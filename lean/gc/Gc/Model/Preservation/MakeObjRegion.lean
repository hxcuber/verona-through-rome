module

public import Gc.Model.Types
public import Gc.Model.Helpers
public import Gc.Model.Validity
public import Gc.Model.Theorems
public import Gc.Model.Mutation.MakeObjRegion
public import Gc.Model.Preservation.Common

public import Mathlib.Data.List.Infix

@[expose] public section

-- freshObjectId is not in any region's objMap.
private theorem fresh_not_in_region {cfg : RuntimeConfig} {rid : RegionId} {region : Region}
    (hlookup : cfg.heap.lookup rid = some region) : cfg.freshObjectId ∉ region.objMap.keys := fun hmem =>
  cfg.freshObjectId_not_mem (List.mem_append_right _ (heap_objectIds_of_mem (AList.lookup_mem_entries hlookup) hmem))

-- freshObjectId is not in any stack frame's objMap.
private theorem fresh_not_in_stack {cfg : RuntimeConfig} {f : Frame} (hf : f ∈ cfg.stack) :
    cfg.freshObjectId ∉ f.objMap.keys := fun hmem =>
  cfg.freshObjectId_not_mem (List.mem_append_left _ (by simpa [Stack.objectIds, Frame.objectIds] using ⟨f, hf, hmem⟩))

-- A frame's refs are among its stack's refs.
private theorem stack_refs_mem {s : Stack} {f : Frame} {r : Reference} (hf : f ∈ s) (hr : r ∈ f.refs) :
    r ∈ Stack.refs s := by
  simpa [Stack.refs] using ⟨f, hf, hr⟩

-- Stack.refs of a stack ending in `f`.
private theorem stack_refs_concat (L : List Frame) (f : Frame) : Stack.refs (L ++ [f]) = Stack.refs L ++ f.refs := by
  simp [Stack.refs]

-- Under HS1, a stored oid is never the fresh one.
private theorem ne_fresh_of_refs {cfg : RuntimeConfig} {oid : ObjectId} (vcfg : ValidConfig cfg)
    (hr : Reference.OId oid ∈ cfg.refs) : oid ≠ cfg.freshObjectId := fun he =>
  cfg.freshObjectId_not_mem (he ▸ vcfg.hs1 oid hr)

-- Inserting the fresh empty object leaves a region's refs unchanged.
private theorem newRegion_refs {cfg : RuntimeConfig} {rid : RegionId} {region : Region}
    (hlookup : cfg.heap.lookup rid = some region) :
    Region.refs { region with objMap := region.objMap.insert cfg.freshObjectId ∅ } = region.refs := by
  simp only [Region.refs]
  rw [AList.entries_insert_of_notMem (fresh_not_in_region hlookup)]
  simp [Object.refs]

-- Inserting a region with the same refs at a present heap key permutes `Heap.refs`.
private theorem heap_insert_refs_perm {heap : Heap} {rid : RegionId} {region newRegion : Region}
    (hlookup : heap.lookup rid = some region) (hrefs : newRegion.refs = region.refs) :
    (Heap.refs (heap.insert rid newRegion)).Perm heap.refs := by
  obtain ⟨r2, l1, l2, _, heq, hk⟩ := List.exists_of_kerase (AList.mem_keys_of_lookup_eq_some hlookup)
  obtain rfl : r2 = region := List.NodupKeys.eq_of_mk_mem heap.nodupKeys
    (heq ▸ List.mem_append_right _ List.mem_cons_self) (AList.lookup_mem_entries hlookup)
  unfold Heap.refs
  rw [AList.entries_insert, hk, heq]
  simp [hrefs, List.perm_append_comm_assoc]

-- A ref of a frame after a varMap insert is the inserted value or an old ref of the frame.
private theorem newFrame_refs_mem {frame : Frame} {x : VarName} {r0 r : Reference}
    (hr : r ∈ Frame.refs { frame with varMap := frame.varMap.insert x r0 }) : r = r0 ∨ r ∈ frame.refs := by
  unfold Frame.refs at hr ⊢
  rw [AList.entries_insert, List.map_cons] at hr
  simp only [List.mem_append, List.mem_cons] at hr ⊢
  rcases hr with hr | hr | hr
  · exact Or.inr (Or.inl hr)
  · exact Or.inl hr
  · exact Or.inr (Or.inr (((List.kerase_sublist _ _).map _).subset hr))

-- stackWithIndex of a stack split off at its last frame.
private theorem swi_eq {c : RuntimeConfig} {frame : Frame} (hlast : c.stack.getLast? = some frame) :
    c.stackWithIndex = c.stack.dropLast.mapIdx (fun i f => ({ f with index := i } : FrameWithIndex)) ++
      [{ frame with index := c.stack.dropLast.length }] := by
  rw [RuntimeConfig.stackWithIndex]
  conv_lhs => rw [← List.dropLast_append_getLast? frame hlast]
  rw [List.mapIdx_concat]

-- stackWithIndex of a config whose stack is given as `L ++ [f]`.
private theorem swi_mk (L : List Frame) (f : Frame) (heap : Heap) :
    (RuntimeConfig.mk (L ++ [f]) heap).stackWithIndex =
      L.mapIdx (fun i f => ({ f with index := i } : FrameWithIndex)) ++ [{ f with index := L.length }] :=
  List.mapIdx_concat ..

-- Each frame after makeObjRegion has an old counterpart with the same index, region and objMap whose refs cover its own up to the fresh ref.
private theorem swi_down (h : makeObjRegion x cfg = some cfg') {f' : FrameWithIndex}
    (hf' : f' ∈ cfg'.stackWithIndex) :
    ∃ f ∈ cfg.stackWithIndex, f.index = f'.index ∧ f.regionId = f'.regionId ∧ f.objMap = f'.objMap ∧
      ∀ r ∈ f'.refs, r ∈ f.refs ∨
        (r = Reference.OId cfg.freshObjectId ∧ cfg.stack.getLast?.map Frame.regionId = some f'.regionId) := by
  obtain ⟨frame, region, hlast, -, -, rfl⟩ := makeObjRegion_cases h
  rw [swi_eq hlast]
  rw [swi_mk] at hf'
  rcases List.mem_append.mp hf' with hd | hl
  · exact ⟨f', List.mem_append_left _ hd, rfl, rfl, rfl, fun r hr => Or.inl hr⟩
  · obtain rfl := List.mem_singleton.mp hl
    refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl, rfl, fun r hr => ?_⟩
    rcases newFrame_refs_mem hr with rfl | hr
    · exact Or.inr ⟨rfl, by simp [hlast]⟩
    · exact Or.inl hr

-- Each old frame has a counterpart after makeObjRegion with the same index and region.
private theorem swi_up (h : makeObjRegion x cfg = some cfg') {f : FrameWithIndex} (hf : f ∈ cfg.stackWithIndex) :
    ∃ f' ∈ cfg'.stackWithIndex, f'.index = f.index ∧ f'.regionId = f.regionId := by
  obtain ⟨frame, region, hlast, -, -, rfl⟩ := makeObjRegion_cases h
  rw [swi_eq hlast] at hf
  rw [swi_mk]
  rcases List.mem_append.mp hf with hd | hl
  · exact ⟨f, List.mem_append_left _ hd, rfl, rfl⟩
  · obtain rfl := List.mem_singleton.mp hl
    exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl⟩

-- cfg'.objectIds is cfg.objectIds with freshObjectId added.
private theorem objectIds_perm (h : makeObjRegion x cfg = some cfg') :
    cfg'.objectIds.Perm (cfg.freshObjectId :: cfg.objectIds) := by
  obtain ⟨frame, region, hlast, hlookup, -, rfl⟩ := makeObjRegion_cases h
  have hheap : Heap.objectIds (cfg.heap.insert frame.regionId
      { region with objMap := region.objMap.insert cfg.freshObjectId ∅ }) =
      cfg.freshObjectId :: Heap.objectIds (cfg.heap.insert frame.regionId region) := by
    simp [Heap.objectIds, AList.entries_insert, Region.objectIds,
      List.kerase_of_notMem_keys (fresh_not_in_region hlookup)]
  have hstack : Stack.objectIds (cfg.stack.dropLast ++
      [{ frame with varMap := frame.varMap.insert x (Reference.OId cfg.freshObjectId) }]) = cfg.stack.objectIds := by
    conv_rhs => rw [← List.dropLast_append_getLast? frame hlast]
    simp [Stack.objectIds, Frame.objectIds]
  unfold RuntimeConfig.objectIds
  rw [hstack, hheap]
  exact ((heap_insert_objectIds_perm hlookup (List.Perm.refl _)).cons _ |>.append_left _).trans List.perm_middle

-- Every ref stored after makeObjRegion is the fresh ref or was already stored.
private theorem refs_mem (h : makeObjRegion x cfg = some cfg') {r : Reference} (hr : r ∈ cfg'.refs) :
    r = Reference.OId cfg.freshObjectId ∨ r ∈ cfg.refs := by
  obtain ⟨frame, region, hlast, hlookup, -, rfl⟩ := makeObjRegion_cases h
  have hmem : frame ∈ cfg.stack := List.mem_of_getLast? hlast
  simp only [RuntimeConfig.refs, Stack.refs, List.map_append, List.map_singleton, List.bind_eq_flatMap,
    List.flatMap_id, List.flatten_append, List.flatten_singleton, List.mem_append] at hr
  rcases hr with (hd | hn) | hh
  · exact Or.inr (List.mem_append_left _ (by
      simpa [Stack.refs] using ((List.dropLast_sublist _).map Frame.refs).flatten_sublist.subset hd))
  · exact (newFrame_refs_mem hn).imp_right (List.mem_append_left _ <| stack_refs_mem hmem ·)
  · exact Or.inr (List.mem_append_right _ ((heap_insert_refs_perm hlookup (newRegion_refs hlookup)).subset hh))

theorem makeObjRegion_L1 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  L1 cfg' := fun vcfg h =>
  (List.nodup_cons.mpr ⟨cfg.freshObjectId_not_mem, vcfg.l1⟩).perm (objectIds_perm h).symm

theorem makeObjRegion_L2 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  L2 cfg' := by
  intro vcfg h f hf
  obtain ⟨frame, region, -, hlookup, hopen, rfl⟩ := makeObjRegion_cases h
  by_cases heq : f.regionId = frame.regionId
  · rw [heq, AList.lookup_insert]
    exact ⟨_, rfl, hopen⟩
  · rw [AList.lookup_insert_ne heq]
    rcases List.mem_append.mp hf with hd | hl
    · exact vcfg.l2 f (List.mem_of_mem_dropLast hd)
    · exact absurd (by rw [List.mem_singleton.mp hl]) heq

theorem makeObjRegion_H1 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  H1 cfg' := by
  intro vcfg h r hr
  obtain ⟨frame, region, -, hlookup, -, rfl⟩ := makeObjRegion_cases h
  simp only [Heap.regions, AList.entries_insert, List.map_cons, List.mem_cons] at hr
  rcases hr with rfl | hr
  · exact (AList.mem_insert _).mpr (Or.inr (vcfg.h1 region (List.mem_map_of_mem (AList.lookup_mem_entries hlookup))))
  · exact vcfg.h1 r (((List.kerase_sublist _ _).map _).subset hr)

theorem makeObjRegion_H2 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  H2 cfg' := by
  intro vcfg h rid
  obtain ⟨frame, region, hlast, hlookup, -, rfl⟩ := makeObjRegion_cases h
  have hf : (Frame.refs { frame with varMap := frame.varMap.insert x (Reference.OId cfg.freshObjectId) }).count
      (Reference.RId rid) ≤ frame.refs.count (Reference.RId rid) := by
    simp only [Frame.refs, AList.entries_insert, List.map_cons, List.count_append, List.count_cons]
    simpa using ((List.kerase_sublist _ _).map _).count_le _
  have := vcfg.h2 rid
  rw [← List.dropLast_append_getLast? frame hlast, stack_refs_concat, List.count_append] at this
  dsimp only
  rw [stack_refs_concat, List.count_append, (heap_insert_refs_perm hlookup (newRegion_refs hlookup)).count_eq]
  omega

-- Under L1, `find?` locates an oid in the same region of any heap with the same oid-holding keys.
private theorem heap_find_fst_eq {cfg : RuntimeConfig} {heap : Heap} {oid : ObjectId} (l1 : L1 cfg)
    (hiff : ∀ r, (∃ reg, (⟨r, reg⟩ : Sigma (fun _ : RegionId => Region)) ∈ heap.entries ∧ oid ∈ reg.objMap.keys) ↔
      ∃ reg, (⟨r, reg⟩ : Sigma (fun _ : RegionId => Region)) ∈ cfg.heap.entries ∧ oid ∈ reg.objMap.keys) :
    (heap.entries.find? (fun x => x.2.objMap.keys.contains oid)).map Sigma.fst =
      (cfg.heap.entries.find? (fun x => x.2.objMap.keys.contains oid)).map Sigma.fst := by
  cases ho : cfg.heap.entries.find? (fun x => x.2.objMap.keys.contains oid) with
  | none =>
    rw [Option.map_none, Option.map_eq_none_iff, List.find?_eq_none]
    rintro ⟨r, reg⟩ hm hp
    obtain ⟨reg0, hm0, hp0⟩ := (hiff r).mp ⟨reg, hm, List.contains_iff_mem.mp hp⟩
    exact List.find?_eq_none.mp ho _ hm0 (List.contains_iff_mem.mpr hp0)
  | some e =>
    obtain ⟨r, reg⟩ := e
    have hp := List.find?_some ho
    rw [List.contains_iff_mem] at hp
    obtain ⟨reg', hm', hp'⟩ := (hiff r).mpr ⟨reg, List.mem_of_find?_eq_some ho, hp⟩
    cases hn : heap.entries.find? (fun x => x.2.objMap.keys.contains oid) with
    | none => exact absurd (List.contains_iff_mem.mpr hp') (List.find?_eq_none.mp hn _ hm')
    | some e' =>
      obtain ⟨r', reg''⟩ := e'
      have hp'' := List.find?_some hn
      rw [List.contains_iff_mem] at hp''
      obtain ⟨reg0, hm0, hp0⟩ := (hiff r').mp ⟨reg'', List.mem_of_find?_eq_some hn, hp''⟩
      exact congrArg some (heap_region_unique l1 hm0 hp0 (List.mem_of_find?_eq_some ho) hp)

theorem makeObjRegion_corollary_loc_eq : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  ∀ oid, oid ≠ cfg.freshObjectId →
    (Reference.OId oid).loc? cfg = (Reference.OId oid).loc? cfg' := by
  intro vcfg h oid hne
  obtain ⟨frame, region, hlast, hlookup, -, rfl⟩ := makeObjRegion_cases h
  have hS : (cfg.stackWithIndex.findRev? (fun f => f.objMap.keys.contains oid)).map FrameWithIndex.index =
      ((RuntimeConfig.mk (cfg.stack.dropLast ++
        [{ frame with varMap := frame.varMap.insert x (Reference.OId cfg.freshObjectId) }]) cfg.heap).stackWithIndex.findRev?
        (fun f => f.objMap.keys.contains oid)).map FrameWithIndex.index := by
    rw [swi_eq hlast, swi_mk]
    simp only [List.findRev?_eq_find?_reverse, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.find?_cons]
    cases frame.objMap.keys.contains oid <;> rfl
  have hH := heap_find_fst_eq (heap := cfg.heap.insert frame.regionId
    { region with objMap := region.objMap.insert cfg.freshObjectId ∅ }) (oid := oid) vcfg.l1 fun r => by
    simp only [← AList.mem_lookup_iff, Option.mem_def]
    by_cases hr : r = frame.regionId
    · subst hr
      simp [hlookup, AList.keys_insert, List.mem_erase_of_ne hne, hne]
    · rw [AList.lookup_insert_ne hr]
  simp only [Reference.loc?]
  refine (loc_match_eq _ _).trans ?_
  rw [hS, ← hH]
  exact (loc_match_eq _ _).symm

theorem makeObjRegion_H3 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  H3 cfg' := by
  intro vcfg h rid oid reg hreg hoid
  obtain ⟨frame, region, -, hlookup, -, rfl⟩ := makeObjRegion_cases h
  obtain ⟨reg0, hl0, hr0⟩ : ∃ reg0, cfg.heap.lookup rid = some reg0 ∧ Reference.OId oid ∈ reg0.refs := by
    by_cases hr : rid = frame.regionId
    · subst hr
      rw [AList.lookup_insert, Option.some_inj] at hreg
      subst hreg
      exact ⟨region, hlookup, newRegion_refs hlookup ▸ hoid⟩
    · exact ⟨reg, by rwa [AList.lookup_insert_ne hr] at hreg, hoid⟩
  rw [← makeObjRegion_corollary_loc_eq vcfg h oid
    (ne_fresh_of_refs vcfg (List.mem_append_right _ (heap_refs_mem_of_lookup hl0 hr0)))]
  exact vcfg.h3 rid oid reg0 hl0 hr0

theorem makeObjRegion_S1 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  S1 cfg' := by
  intro vcfg h
  obtain ⟨frame, region, hlast, -, -, rfl⟩ := makeObjRegion_cases h
  have := vcfg.s1
  rw [S1, ← List.dropLast_append_getLast? frame hlast] at this
  simpa [S1] using this

-- The fresh object resolves into the region of the top frame.
theorem makeObjRegion_corollary_loc_fresh : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  ∃ frame, cfg.stack.getLast? = some frame ∧
    (Reference.OId cfg.freshObjectId).loc? cfg' = some (Location.Rgn frame.regionId) := by
  intro vcfg h
  have hS : cfg'.stackWithIndex.findRev? (fun f => f.objMap.keys.contains cfg.freshObjectId) = none := by
    rw [List.findRev?_eq_find?_reverse, List.find?_eq_none]
    intro f hf hc
    obtain ⟨g, hg, -, -, hobj, -⟩ := swi_down h (List.mem_reverse.mp hf)
    obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp hg
    exact fresh_not_in_stack (List.getElem_mem hn) (hobj ▸ List.contains_iff_mem.mp hc)
  obtain ⟨frame, region, hlast, hlookup, -, rfl⟩ := makeObjRegion_cases h
  refine ⟨frame, hlast, ?_⟩
  simp only [Reference.loc?]
  rw [hS]
  simp [AList.entries_insert, AList.keys_insert]

theorem makeObjRegion_S2 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  S2 cfg' := by
  intro vcfg h f' hf' ref href fid oid hreq hloc
  subst hreq
  obtain ⟨f, hf, hidx, -, -, hrefs⟩ := swi_down h hf'
  by_cases hne : oid = cfg.freshObjectId
  · obtain ⟨_, -, hfresh⟩ := makeObjRegion_corollary_loc_fresh vcfg h
    rw [hne, hfresh] at hloc
    cases hloc
  · rcases hrefs _ href with hr | ⟨heq, -⟩
    · exact hidx ▸ vcfg.s2 f hf _ hr fid oid rfl (by rwa [makeObjRegion_corollary_loc_eq vcfg h oid hne])
    · exact absurd (Reference.OId.inj heq) hne

theorem makeObjRegion_S3 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  S3 cfg' := by
  intro vcfg h f' hf' ref href rid oid hreq hloc
  subst hreq
  obtain ⟨f, hf, hidx, -, -, hrefs⟩ := swi_down h hf'
  by_cases hne : oid = cfg.freshObjectId
  · subst hne
    obtain ⟨_, hlast, hfresh⟩ := makeObjRegion_corollary_loc_fresh vcfg h
    rcases hrefs _ href with hr | ⟨-, hreg⟩
    · obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp hf
      exact absurd rfl (ne_fresh_of_refs vcfg (List.mem_append_left _ (stack_refs_mem (List.getElem_mem hn) hr)))
    · rw [hfresh, Option.some_inj, Location.Rgn.injEq] at hloc
      rw [hlast, Option.map_some, Option.some_inj] at hreg
      exact ⟨f', hf', hloc ▸ hreg.symm, le_refl _⟩
  · rcases hrefs _ href with hr | ⟨heq, -⟩
    · obtain ⟨g, hg, hgr, hgi⟩ :=
        vcfg.s3 f hf _ hr rid oid rfl (by rwa [makeObjRegion_corollary_loc_eq vcfg h oid hne])
      obtain ⟨g', hg', hgi', hgr'⟩ := swi_up h hg
      exact ⟨g', hg', hgr'.trans hgr, hgi'.trans_le (hidx ▸ hgi)⟩
    · exact absurd (Reference.OId.inj heq) hne

theorem makeObjRegion_HS1 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  HS1 cfg' := by
  intro vcfg h oid hmem
  refine (objectIds_perm h).mem_iff.mpr ?_
  rcases refs_mem h hmem with he | hr
  · exact Reference.OId.inj he ▸ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (vcfg.hs1 oid hr)

theorem makeObjRegion_HS2 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  HS2 cfg' := by
  intro vcfg h rid hmem
  rcases refs_mem h hmem with he | hr
  · cases he
  · obtain ⟨frame, region, -, hlookup, -, rfl⟩ := makeObjRegion_cases h
    exact (heap_insert_keys_mem (AList.mem_keys_of_lookup_eq_some hlookup) rid).mpr (vcfg.hs2 rid hr)

theorem makeObjRegion_valid : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  ValidConfig cfg' := by
  intro vcfg h
  exact {
    l1 := makeObjRegion_L1 vcfg h,
    l2 := makeObjRegion_L2 vcfg h,
    h1 := makeObjRegion_H1 vcfg h,
    h2 := makeObjRegion_H2 vcfg h,
    h3 := makeObjRegion_H3 vcfg h,
    s1 := makeObjRegion_S1 vcfg h,
    s2 := makeObjRegion_S2 vcfg h,
    s3 := makeObjRegion_S3 vcfg h,
    hs1 := makeObjRegion_HS1 vcfg h,
    hs2 := makeObjRegion_HS2 vcfg h
  }
