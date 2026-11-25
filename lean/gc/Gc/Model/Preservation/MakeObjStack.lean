module

public import Gc.Model.Types
public import Gc.Model.Helpers
public import Gc.Model.Validity
public import Gc.Model.Theorems
public import Gc.Model.Mutation.MakeObjStack
public import Gc.Model.Preservation.Common

public import Mathlib.Data.List.Infix

@[expose] public section

-- No heap region holds freshObjectId.
private theorem fresh_heap_find_none (cfg : RuntimeConfig) :
    cfg.heap.entries.find? (fun x => x.2.objMap.keys.contains cfg.freshObjectId) = none :=
  List.find?_eq_none.mpr fun _ he hc => cfg.freshObjectId_not_mem (List.mem_append_right _
    (heap_objectIds_of_mem he (List.contains_iff_mem.mp hc)))

-- The new top frame's refs are a permutation of the fresh ref plus a sublist of the old frame's refs.
private theorem newFrame_refs_perm {frame : Frame} {x : VarName} {o : ObjectId} (ho : o ∉ frame.objMap.keys) :
    ∃ l, l.Sublist frame.refs ∧ (Frame.refs ({ frame with
      varMap := frame.varMap.insert x (.OId o)
      objMap := frame.objMap.insert o ∅ } : Frame)).Perm (.OId o :: l) := by
  simp only [Frame.refs, AList.entries_insert, List.kerase_of_notMem_keys ho, List.map_cons]
  exact ⟨_, ((List.kerase_sublist x _).map _).append_left _, List.perm_middle⟩

-- A ref of the new top frame is the fresh ref or an old ref of the frame.
private theorem newFrame_refs_mem {frame : Frame} {x : VarName} {o : ObjectId} {r : Reference}
    (ho : o ∉ frame.objMap.keys) (hr : r ∈ Frame.refs ({ frame with
      varMap := frame.varMap.insert x (.OId o)
      objMap := frame.objMap.insert o ∅ } : Frame)) : r = Reference.OId o ∨ r ∈ frame.refs :=
  have ⟨_, hs, hp⟩ := newFrame_refs_perm ho
  (List.mem_cons.mp (hp.mem_iff.mp hr)).imp_right (hs.subset ·)

-- Each new frame has an old counterpart with the same index and region covering its refs, bar the fresh ref on top.
private theorem swi_down (h : makeObjStack x cfg = some cfg') {f' : FrameWithIndex}
    (hf' : f' ∈ cfg'.stackWithIndex) :
    ∃ f ∈ cfg.stackWithIndex, f.index = f'.index ∧ f.regionId = f'.regionId ∧
      ∀ r ∈ f'.refs, r ∈ f.refs ∨ (r = Reference.OId cfg.freshObjectId ∧ f'.index = cfg.stack.dropLast.length) := by
  obtain ⟨frame, hlast, rfl⟩ := makeObjStack_cases h
  rw [stackWithIndex_eq_of_getLast? hlast]
  rw [stackWithIndex_mk_append_singleton] at hf'
  rcases List.mem_append.mp hf' with hd | hl
  · exact ⟨f', List.mem_append_left _ hd, rfl, rfl, fun r hr => Or.inl hr⟩
  · obtain rfl := List.mem_singleton.mp hl
    refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl, fun r hr => ?_⟩
    exact (newFrame_refs_mem (freshObjectId_not_mem_frame (List.mem_of_getLast? hlast)) hr).symm.imp id (⟨·, rfl⟩)

-- Each old frame has a counterpart after makeObjStack with the same index and region.
private theorem swi_up (h : makeObjStack x cfg = some cfg') {f : FrameWithIndex} (hf : f ∈ cfg.stackWithIndex) :
    ∃ f' ∈ cfg'.stackWithIndex, f'.index = f.index ∧ f'.regionId = f.regionId := by
  obtain ⟨frame, hlast, rfl⟩ := makeObjStack_cases h
  rw [stackWithIndex_eq_of_getLast? hlast] at hf
  rw [stackWithIndex_mk_append_singleton]
  rcases List.mem_append.mp hf with hd | hl
  · exact ⟨f, List.mem_append_left _ hd, rfl, rfl⟩
  · obtain rfl := List.mem_singleton.mp hl
    exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl⟩

-- cfg'.objectIds is cfg.objectIds with freshObjectId added.
private theorem objectIds_perm (h : makeObjStack x cfg = some cfg') :
    cfg'.objectIds.Perm (cfg.freshObjectId :: cfg.objectIds) := by
  obtain ⟨frame, hlast, rfl⟩ := makeObjStack_cases h
  have hk := List.erase_of_not_mem (freshObjectId_not_mem_frame (List.mem_of_getLast? hlast))
  unfold RuntimeConfig.objectIds
  conv_rhs => rw [← List.dropLast_append_getLast? frame hlast]
  simp [Stack.objectIds, Frame.objectIds, AList.keys_insert, hk, List.perm_middle]

-- Every ref stored after makeObjStack is the fresh ref or was already stored.
private theorem refs_mem (h : makeObjStack x cfg = some cfg') {r : Reference} (hr : r ∈ cfg'.refs) :
    r = Reference.OId cfg.freshObjectId ∨ r ∈ cfg.refs := by
  obtain ⟨frame, hlast, rfl⟩ := makeObjStack_cases h
  have hmem : frame ∈ cfg.stack := List.mem_of_getLast? hlast
  simp only [RuntimeConfig.refs, stack_refs_append_singleton, List.mem_append] at hr
  rcases hr with (hd | hn) | hh
  · exact Or.inr (List.mem_append_left _ (by
      rw [← List.dropLast_append_getLast? frame hlast, stack_refs_append_singleton]
      exact List.mem_append_left _ hd))
  · exact (newFrame_refs_mem (freshObjectId_not_mem_frame hmem) hn).imp_right (List.mem_append_left _ <| stack_refs_mem hmem ·)
  · exact Or.inr (List.mem_append_right _ hh)

-- Locations after makeObjStack: the fresh object sits in the top frame, every other object stays put.
private theorem loc_eq (h : makeObjStack x cfg = some cfg') (oid : ObjectId) :
    (Reference.OId oid).loc? cfg' =
      if oid = cfg.freshObjectId then some (Location.Stk cfg.stack.dropLast.length) else (Reference.OId oid).loc? cfg := by
  obtain ⟨frame, hlast, rfl⟩ := makeObjStack_cases h
  simp only [Reference.loc?]
  rw [stackWithIndex_eq_of_getLast? hlast, stackWithIndex_mk_append_singleton]
  simp only [List.findRev?_eq_find?_reverse, List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.find?_cons]
  split_ifs with hne
  · subst hne
    rw [fresh_heap_find_none]
    simp [AList.keys_insert]
  · have : (frame.objMap.insert cfg.freshObjectId ∅).keys.contains oid = frame.objMap.keys.contains oid := by
      simp [AList.keys_insert, hne]
    rw [this]
    cases frame.objMap.keys.contains oid <;> cases cfg.heap.entries.find? (fun x => x.2.objMap.keys.contains oid) <;> rfl

theorem makeObjStack_L1 : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  L1 cfg' := fun vcfg h =>
  (List.nodup_cons.mpr ⟨cfg.freshObjectId_not_mem, vcfg.l1⟩).perm (objectIds_perm h).symm

theorem makeObjStack_L2 : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  L2 cfg' := by
  intro vcfg h f hf
  obtain ⟨frame, hlast, rfl⟩ := makeObjStack_cases h
  rcases List.mem_append.mp hf with hd | hl
  · exact vcfg.l2 f (List.mem_of_mem_dropLast hd)
  · obtain rfl := List.mem_singleton.mp hl
    exact vcfg.l2 frame (List.mem_of_getLast? hlast)

theorem makeObjStack_H1 : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  H1 cfg' := by
  intro vcfg h
  obtain ⟨frame, hlast, rfl⟩ := makeObjStack_cases h
  exact vcfg.h1

theorem makeObjStack_H2 : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  H2 cfg' := by
  intro vcfg h rid
  obtain ⟨frame, hlast, rfl⟩ := makeObjStack_cases h
  obtain ⟨l, hs, hp⟩ := newFrame_refs_perm (x := x) (freshObjectId_not_mem_frame (List.mem_of_getLast? hlast))
  have hf := hs.count_le (Reference.RId rid)
  have := vcfg.h2 rid
  rw [← List.dropLast_append_getLast? frame hlast, stack_refs_append_singleton, List.count_append] at this
  dsimp only
  rw [stack_refs_append_singleton, List.count_append, hp.count_eq, List.count_cons]
  simp only [reduceCtorEq, beq_iff_eq, ↓reduceIte] at *
  omega

theorem makeObjStack_H3 : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  H3 cfg' := by
  intro vcfg h rid oid reg hreg hoid
  obtain ⟨frame, -, rfl⟩ := makeObjStack_cases h
  simpa [loc_eq h, ne_freshObjectId_of_mem_refs vcfg (List.mem_append_right _ (heap_refs_mem_of_lookup hreg hoid))] using
    vcfg.h3 rid oid reg hreg hoid

theorem makeObjStack_S1 : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  S1 cfg' := by
  intro vcfg h
  obtain ⟨frame, hlast, rfl⟩ := makeObjStack_cases h
  have := vcfg.s1
  rw [S1, ← List.dropLast_append_getLast? frame hlast] at this
  simpa [S1] using this

theorem makeObjStack_S2 : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  S2 cfg' := by
  intro vcfg h f' hf' ref href fid oid hreq hloc
  subst hreq
  obtain ⟨f, hf, hidx, -, hrefs⟩ := swi_down h hf'
  rw [loc_eq h] at hloc
  split_ifs at hloc with hne
  · rcases hrefs _ href with hr | ⟨-, hi⟩
    · obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp hf
      exact absurd hne (ne_freshObjectId_of_mem_refs vcfg (List.mem_append_left _ (stack_refs_mem (List.getElem_mem hn) hr)))
    · cases hloc
      exact hi.ge
  · rcases hrefs _ href with hr | ⟨heq, -⟩
    · exact hidx ▸ vcfg.s2 f hf _ hr fid oid rfl hloc
    · exact absurd (Reference.OId.inj heq) hne

theorem makeObjStack_S3 : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  S3 cfg' := by
  intro vcfg h f' hf' ref href rid oid hreq hloc
  subst hreq
  obtain ⟨f, hf, hidx, -, hrefs⟩ := swi_down h hf'
  rw [loc_eq h] at hloc
  split_ifs at hloc with hne
  · cases hloc
  · rcases hrefs _ href with hr | ⟨heq, -⟩
    · obtain ⟨g, hg, hgr, hgi⟩ := vcfg.s3 f hf _ hr rid oid rfl hloc
      obtain ⟨g', hg', hgi', hgr'⟩ := swi_up h hg
      exact ⟨g', hg', hgr'.trans hgr, hgi'.trans_le (hidx ▸ hgi)⟩
    · exact absurd (Reference.OId.inj heq) hne

theorem makeObjStack_HS1 : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  HS1 cfg' := by
  intro vcfg h oid hmem
  refine (objectIds_perm h).mem_iff.mpr ?_
  rcases refs_mem h hmem with he | hr
  · exact Reference.OId.inj he ▸ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (vcfg.hs1 oid hr)

theorem makeObjStack_HS2 : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  HS2 cfg' := by
  intro vcfg h rid hmem
  rcases refs_mem h hmem with he | hr
  · cases he
  · obtain ⟨frame, -, rfl⟩ := makeObjStack_cases h
    exact vcfg.hs2 rid hr

theorem makeObjStack_valid : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  ValidConfig cfg' := by
  intro vcfg h
  exact {
    l1 := makeObjStack_L1 vcfg h,
    l2 := makeObjStack_L2 vcfg h,
    h1 := makeObjStack_H1 vcfg h,
    h2 := makeObjStack_H2 vcfg h,
    h3 := makeObjStack_H3 vcfg h,
    s1 := makeObjStack_S1 vcfg h,
    s2 := makeObjStack_S2 vcfg h,
    s3 := makeObjStack_S3 vcfg h,
    hs1 := makeObjStack_HS1 vcfg h,
    hs2 := makeObjStack_HS2 vcfg h
  }
