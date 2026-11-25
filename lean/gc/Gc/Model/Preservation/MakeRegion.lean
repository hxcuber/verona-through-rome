module

public import Gc.Model.Types
public import Gc.Model.Helpers
public import Gc.Model.Validity
public import Gc.Model.Theorems
public import Gc.Model.Mutation.MakeRegion
public import Gc.Model.Preservation.Common

public import Mathlib.Data.List.Infix

@[expose] public section

-- Inserting at the fresh region id prepends the new entry.
private theorem heap_entries (cfg : RuntimeConfig) (reg : Region) :
    (cfg.heap.insert cfg.freshRegionId reg).entries = ⟨cfg.freshRegionId, reg⟩ :: cfg.heap.entries := by
  rw [AList.entries_insert, List.kerase_of_notMem_keys cfg.freshRegionId_not_mem]

-- Each new frame has an old counterpart with the same index whose refs cover its own, bar the fresh RId.
private theorem swi_down (h : makeRegion x cfg = some cfg') {f' : FrameWithIndex}
    (hf' : f' ∈ cfg'.stackWithIndex) :
    ∃ f ∈ cfg.stackWithIndex, f.index = f'.index ∧ ∀ r ∈ f'.refs, r ∈ f.refs ∨ r = Reference.RId cfg.freshRegionId := by
  obtain ⟨frame, hlast, rfl⟩ := makeRegion_cases h
  rw [stackWithIndex_eq_of_getLast? hlast]
  rw [stackWithIndex_mk_append_singleton] at hf'
  rcases List.mem_append.mp hf' with hd | hl
  · exact ⟨f', List.mem_append_left _ hd, rfl, fun r hr => Or.inl hr⟩
  · obtain rfl := List.mem_singleton.mp hl
    exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, fun r hr => (frame_varMap_insert_refs_mem hr).symm⟩

-- Each old frame has a counterpart after makeRegion with the same index and region.
private theorem swi_up (h : makeRegion x cfg = some cfg') {f : FrameWithIndex} (hf : f ∈ cfg.stackWithIndex) :
    ∃ f' ∈ cfg'.stackWithIndex, f'.index = f.index ∧ f'.regionId = f.regionId := by
  obtain ⟨frame, hlast, rfl⟩ := makeRegion_cases h
  rw [stackWithIndex_eq_of_getLast? hlast] at hf
  rw [stackWithIndex_mk_append_singleton]
  rcases List.mem_append.mp hf with hd | hl
  · exact ⟨f, List.mem_append_left _ hd, rfl, rfl⟩
  · obtain rfl := List.mem_singleton.mp hl
    exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl⟩

-- makeRegion leaves Heap.refs unchanged.
private theorem heap_refs_eq (h : makeRegion x cfg = some cfg') : cfg'.heap.refs = cfg.heap.refs := by
  obtain ⟨frame, hlast, rfl⟩ := makeRegion_cases h
  simp only [Heap.refs, heap_entries]
  simp [Region.refs, Object.refs]

-- cfg'.objectIds is cfg.objectIds with freshObjectId added.
private theorem objectIds_perm (h : makeRegion x cfg = some cfg') :
    cfg'.objectIds.Perm (cfg.freshObjectId :: cfg.objectIds) := by
  obtain ⟨frame, hlast, rfl⟩ := makeRegion_cases h
  unfold RuntimeConfig.objectIds Heap.objectIds
  rw [heap_entries]
  conv_rhs => rw [← List.dropLast_append_getLast? frame hlast]
  simp [Stack.objectIds, Frame.objectIds, Region.objectIds]
  exact (List.perm_middle.append_left _).trans List.perm_middle

-- Every ref stored after makeRegion is the fresh RId or was already stored.
private theorem refs_mem (h : makeRegion x cfg = some cfg') {r : Reference} (hr : r ∈ cfg'.refs) :
    r = Reference.RId cfg.freshRegionId ∨ r ∈ cfg.refs := by
  rw [RuntimeConfig.refs, heap_refs_eq h] at hr
  obtain ⟨frame, hlast, rfl⟩ := makeRegion_cases h
  have hmem : frame ∈ cfg.stack := List.mem_of_getLast? hlast
  simp only [stack_refs_append_singleton, List.mem_append] at hr
  rcases hr with (hd | hn) | hh
  · exact Or.inr (List.mem_append_left _ (by
      rw [← List.dropLast_append_getLast? frame hlast, stack_refs_append_singleton]
      exact List.mem_append_left _ hd))
  · exact (frame_varMap_insert_refs_mem hn).imp_right (List.mem_append_left _ <| stack_refs_mem hmem ·)
  · exact Or.inr (List.mem_append_right _ hh)

-- Locations after makeRegion: the fresh object sits in the fresh region, every other object stays put.
private theorem loc_eq (h : makeRegion x cfg = some cfg') (oid : ObjectId) :
    (Reference.OId oid).loc? cfg' =
      if oid = cfg.freshObjectId then some (Location.Rgn cfg.freshRegionId) else (Reference.OId oid).loc? cfg := by
  obtain ⟨frame, hlast, rfl⟩ := makeRegion_cases h
  simp only [Reference.loc?]
  rw [stackWithIndex_eq_of_getLast? hlast, stackWithIndex_mk_append_singleton, heap_entries]
  simp only [List.findRev?_eq_find?_reverse, List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.find?_cons]
  split_ifs with hne
  · subst hne
    have h1 := freshObjectId_not_mem_frame (List.mem_of_getLast? hlast)
    have h2 : (cfg.stack.dropLast.mapIdx (fun i f => ({ f with index := i } : FrameWithIndex))).reverse.find?
        (fun f => f.objMap.keys.contains cfg.freshObjectId) = none := by
      refine List.find?_eq_none.mpr fun f hf hc => ?_
      obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp (List.mem_reverse.mp hf)
      exact freshObjectId_not_mem_frame (List.mem_of_mem_dropLast (List.getElem_mem hn)) (List.contains_iff_mem.mp hc)
    rw [h2]
    simp [h1]
  · have : ((∅ : ObjMap).insert cfg.freshObjectId ∅).keys.contains oid = false := by
      simp [hne]
    rw [this]
    cases frame.objMap.keys.contains oid <;> cases cfg.heap.entries.find? (fun x => x.2.objMap.keys.contains oid) <;> rfl

-- A stored oid of a new frame is stored in its old counterpart and keeps its location.
private theorem stack_oid_down (vcfg : ValidConfig cfg) (h : makeRegion x cfg = some cfg') {f' : FrameWithIndex}
    {oid : ObjectId} (hf' : f' ∈ cfg'.stackWithIndex) (href : Reference.OId oid ∈ f'.refs) :
    ∃ f ∈ cfg.stackWithIndex, f.index = f'.index ∧ Reference.OId oid ∈ f.refs ∧
      (Reference.OId oid).loc? cfg' = (Reference.OId oid).loc? cfg := by
  obtain ⟨f, hf, hidx, hrefs⟩ := swi_down h hf'
  obtain hr := (hrefs _ href).resolve_right (by simp)
  obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp hf
  have hne := ne_freshObjectId_of_mem_refs vcfg (List.mem_append_left _ (stack_refs_mem (List.getElem_mem hn) hr))
  exact ⟨_, hf, hidx, hr, by simp [loc_eq h, hne]⟩

theorem makeRegion_corollary_loc_eq : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  ∀ oid, oid ≠ cfg.freshObjectId →
    (Reference.OId oid).loc? cfg = (Reference.OId oid).loc? cfg' := fun _ h oid hne => by
  simp [loc_eq h, hne]

theorem makeRegion_L1 : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  L1 cfg' := fun vcfg h =>
  (List.nodup_cons.mpr ⟨cfg.freshObjectId_not_mem, vcfg.l1⟩).perm (objectIds_perm h).symm

theorem makeRegion_L2 : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  L2 cfg' := by
  intro vcfg h f hf
  obtain ⟨frame, hlast, rfl⟩ := makeRegion_cases h
  obtain ⟨reg, hl, ho⟩ : ∃ reg, cfg.heap.lookup f.regionId = some reg ∧ reg.status = .Open := by
    rcases List.mem_append.mp hf with hd | hl
    · exact vcfg.l2 f (List.mem_of_mem_dropLast hd)
    · obtain rfl := List.mem_singleton.mp hl
      exact vcfg.l2 frame (List.mem_of_getLast? hlast)
  have hne : f.regionId ≠ cfg.freshRegionId := fun he =>
    cfg.freshRegionId_not_mem (he ▸ AList.mem_keys_of_lookup_eq_some hl)
  exact ⟨reg, (AList.lookup_insert_ne hne).trans hl, ho⟩

theorem makeRegion_H1 : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  H1 cfg' := by
  intro vcfg h r hr
  obtain ⟨frame, hlast, rfl⟩ := makeRegion_cases h
  simp only [Heap.regions, heap_entries, List.map_cons, List.mem_cons] at hr
  rcases hr with rfl | hr
  · simp [AList.singleton]
  · exact vcfg.h1 r hr

theorem makeRegion_H2 : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  H2 cfg' := by
  intro vcfg h rid
  have hh := heap_refs_eq h
  obtain ⟨frame, hlast, rfl⟩ := makeRegion_cases h
  have hf : (Frame.refs { frame with varMap := frame.varMap.insert x (Reference.RId cfg.freshRegionId) }).count
      (Reference.RId rid) ≤ frame.refs.count (Reference.RId rid) + if rid = cfg.freshRegionId then 1 else 0 := by
    simp only [Frame.refs, AList.entries_insert, List.map_cons, List.count_append, List.count_cons]
    have := ((List.kerase_sublist x frame.varMap.entries).map (·.2)).count_le (Reference.RId rid)
    obtain rfl | hr := eq_or_ne rid cfg.freshRegionId
    · simp
      omega
    · simp [hr, hr.symm]
      omega
  have := vcfg.h2 rid
  rw [← List.dropLast_append_getLast? frame hlast, stack_refs_append_singleton, List.count_append] at this
  dsimp only at hh ⊢
  rw [stack_refs_append_singleton, List.count_append, hh]
  split_ifs at hf with hr
  · subst hr
    have h0 : cfg.refs.count (Reference.RId cfg.freshRegionId) = 0 :=
      List.count_eq_zero.mpr fun hm => cfg.freshRegionId_not_mem (vcfg.hs2 _ hm)
    rw [RuntimeConfig.refs, List.count_append, ← List.dropLast_append_getLast? frame hlast, stack_refs_append_singleton,
      List.count_append] at h0
    omega
  · omega

theorem makeRegion_H3 : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  H3 cfg' := by
  intro vcfg h rid oid reg hreg hoid
  obtain ⟨frame, -, rfl⟩ := makeRegion_cases h
  by_cases hr : rid = cfg.freshRegionId
  · subst hr
    rw [AList.lookup_insert, Option.some_inj] at hreg
    subst hreg
    simp [Region.refs, Object.refs] at hoid
  · rw [AList.lookup_insert_ne hr] at hreg
    simp only [loc_eq h, ne_freshObjectId_of_mem_refs vcfg (List.mem_append_right _ (heap_refs_mem_of_lookup hreg hoid)),
      ↓reduceIte]
    exact vcfg.h3 rid oid reg hreg hoid

theorem makeRegion_S1 : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  S1 cfg' := by
  intro vcfg h
  obtain ⟨frame, hlast, rfl⟩ := makeRegion_cases h
  have := vcfg.s1
  rw [S1, ← List.dropLast_append_getLast? frame hlast] at this
  simpa [S1] using this

theorem makeRegion_S2 : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  S2 cfg' := by
  intro vcfg h f' hf' ref href fid oid hreq hloc
  subst hreq
  obtain ⟨f, hf, hidx, hr, hl⟩ := stack_oid_down vcfg h hf' href
  exact hidx ▸ vcfg.s2 f hf _ hr fid oid rfl (hl ▸ hloc)

theorem makeRegion_S3 : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  S3 cfg' := by
  intro vcfg h f' hf' ref href rid oid hreq hloc
  subst hreq
  obtain ⟨f, hf, hidx, hr, hl⟩ := stack_oid_down vcfg h hf' href
  obtain ⟨g, hg, hgr, hgi⟩ := vcfg.s3 f hf _ hr rid oid rfl (hl ▸ hloc)
  obtain ⟨g', hg', hgi', hgr'⟩ := swi_up h hg
  exact ⟨g', hg', hgr'.trans hgr, hgi'.trans_le (hidx ▸ hgi)⟩

theorem makeRegion_HS1 : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  HS1 cfg' := by
  intro vcfg h oid hmem
  refine (objectIds_perm h).mem_iff.mpr (List.mem_cons_of_mem _ (vcfg.hs1 oid ?_))
  exact (refs_mem h hmem).resolve_left (by simp)

theorem makeRegion_HS2 : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  HS2 cfg' := by
  intro vcfg h rid hmem
  have hk := refs_mem h hmem
  obtain ⟨frame, -, rfl⟩ := makeRegion_cases h
  refine AList.mem_keys.mpr ((AList.mem_insert _).mpr ?_)
  rcases hk with he | hr
  · exact Or.inl (Reference.RId.inj he)
  · exact Or.inr (AList.mem_keys.mp (vcfg.hs2 rid hr))

theorem makeRegion_valid : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  ValidConfig cfg' := by
  intro vcfg h
  exact {
    l1 := makeRegion_L1 vcfg h,
    l2 := makeRegion_L2 vcfg h,
    h1 := makeRegion_H1 vcfg h,
    h2 := makeRegion_H2 vcfg h,
    h3 := makeRegion_H3 vcfg h,
    s1 := makeRegion_S1 vcfg h,
    s2 := makeRegion_S2 vcfg h,
    s3 := makeRegion_S3 vcfg h,
    hs1 := makeRegion_HS1 vcfg h,
    hs2 := makeRegion_HS2 vcfg h
  }
