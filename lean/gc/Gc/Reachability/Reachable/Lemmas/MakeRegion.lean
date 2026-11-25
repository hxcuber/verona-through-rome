module

public import Gc.Model.Types
public import Gc.Model.Helpers
public import Gc.Model.Validity
public import Gc.Model.Mutation.Mutation
public import Gc.Model.Preservation
public import Gc.Reachability.Reachable.Semantics
public import Gc.Reachability.Reachable.Lemmas.Common
public import Gc.Reachability.Reachable.Lemmas.MakeObjStack
public import Gc.Reachability.Reachable.Lemmas.Merge

@[expose] public section

-- An allocated heap key is never the fresh region id.
private theorem ne_freshRegionId_of_lookup {cfg : RuntimeConfig} {rid : RegionId} {region : Region}
    (hl : cfg.heap.lookup rid = some region) : rid ≠ cfg.freshRegionId := fun he =>
  cfg.freshRegionId_not_mem (he ▸ AList.mem_keys_of_lookup_eq_some hl)

-- Every `cfg'.stackWithIndex` member is either an unchanged pre-existing frame or the last frame with `varMap` updated.
theorem makeRegion_frame_cases {cfg cfg' : RuntimeConfig} {x : VarName}
    (h : makeRegion x cfg = some cfg')
    {frame : FrameWithIndex} (hframe : frame ∈ cfg'.stackWithIndex) :
    (frame ∈ cfg.stackWithIndex ∧ frame.index < cfg.stack.length - 1) ∨
    (∃ lastFrame, cfg.stack.getLast? = some lastFrame ∧
      frame.regionId = lastFrame.regionId ∧ frame.bridgeVar = lastFrame.bridgeVar ∧
      frame.objMap = lastFrame.objMap ∧
      frame.varMap = lastFrame.varMap.insert x (Reference.RId cfg.freshRegionId) ∧
      frame.index = cfg.stack.dropLast.length) := by
  obtain ⟨lastFrame, hlast, rfl⟩ := makeRegion_cases h
  rw [stackWithIndex_mk_append_singleton] at hframe
  rcases List.mem_append.mp hframe with hmem | hmem
  · refine .inl ⟨stackWithIndex_eq_of_getLast? hlast ▸ List.mem_append_left _ hmem, ?_⟩
    obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp hmem
    simpa using hn
  · rw [List.mem_singleton.mp hmem]
    exact .inr ⟨lastFrame, hlast, rfl, rfl, rfl, rfl, rfl⟩

-- A pre-existing frame with index strictly below the last one survives `makeRegion` unchanged, at the same index.
theorem makeRegion_frame_mem_up {cfg cfg' : RuntimeConfig} {x : VarName}
    (h : makeRegion x cfg = some cfg')
    {frame : FrameWithIndex} (hframe : frame ∈ cfg.stackWithIndex) (hlt : frame.index < cfg.stack.length - 1) :
    frame ∈ cfg'.stackWithIndex := by
  obtain ⟨lastFrame, hlast, rfl⟩ := makeRegion_cases h
  rw [stackWithIndex_eq_of_getLast? hlast] at hframe
  rw [stackWithIndex_mk_append_singleton]
  rcases List.mem_append.mp hframe with hmem | hmem
  · exact List.mem_append_left _ hmem
  · rw [List.mem_singleton.mp hmem, List.length_dropLast] at hlt
    exact absurd hlt (lt_irrefl _)

-- The freshly-created region's bridge object resolves into the heap at the fresh region id (never onto the stack).
theorem makeRegion_corollary_loc_fresh {cfg cfg' : RuntimeConfig} {x : VarName}
    (h : makeRegion x cfg = some cfg') :
    (Reference.OId cfg.freshObjectId).loc? cfg' = some (Location.Rgn cfg.freshRegionId) := by
  have hs : cfg'.stackWithIndex.findRev? (fun f => f.objMap.keys.contains cfg.freshObjectId) = none := by
    refine List.findRev?_eq_find?_reverse ▸ List.find?_eq_none.mpr fun f hf hc => ?_
    rcases makeRegion_frame_cases h (List.mem_reverse.mp hf) with ⟨hf, -⟩ | ⟨lf, hlf, -, -, ho, -⟩
    · obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp hf
      exact freshObjectId_not_mem_frame (List.getElem_mem hn) (by simpa using hc)
    · exact freshObjectId_not_mem_frame (List.mem_of_getLast? hlf) (by simpa [ho] using hc)
  simp only [Reference.loc?, hs]
  obtain ⟨frame, hlast, rfl⟩ := makeRegion_cases h
  simp [AList.entries_insert, List.kerase_of_notMem_keys cfg.freshRegionId_not_mem]

-- `objAt?` agrees between `cfg`/`cfg'` for `oid ≠ freshObjectId`.
private theorem makeRegion_objAt_eq_of_ne {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeRegion x cfg = some cfg') {oid : ObjectId} (hne : oid ≠ cfg.freshObjectId) :
    (Reference.OId oid).objAt? cfg = (Reference.OId oid).objAt? cfg' := by
  have hlocEq := makeRegion_corollary_loc_eq vcfg h oid hne
  obtain ⟨frame, hlast, rfl⟩ := makeRegion_cases h
  unfold Reference.objAt?
  dsimp only
  rw [hlocEq]
  rcases (Reference.OId oid).loc? _ with _ | rid | fid
  · rfl
  · dsimp only
    by_cases heq : rid = cfg.freshRegionId
    · subst heq
      have hnone : cfg.heap.lookup cfg.freshRegionId = none :=
        AList.lookup_eq_none.mpr fun hm => cfg.freshRegionId_not_mem (AList.mem_keys.mpr hm)
      simp only [hnone, AList.lookup_insert, Option.bind_none, Option.bind_some, AList.lookup_insert_ne hne,
        AList.lookup_empty]
    · rw [AList.lookup_insert_ne heq]
  dsimp only
  rw [stackWithIndex_find_index_eq_getElem, stackWithIndex_find_index_eq_getElem,
    stackWithIndex_eq_of_getLast? hlast, stackWithIndex_mk_append_singleton]
  simp only [List.getElem?_append, List.getElem?_singleton]
  split_ifs <;> simp

-- The freshly-allocated object resolves to its own (empty) content in cfg'.
theorem makeRegion_fresh_objAt_cfg' {cfg cfg' : RuntimeConfig} {x : VarName}
    (h : makeRegion x cfg = some cfg') :
    (Reference.OId cfg.freshObjectId).objAt? cfg' = some (∅ : Object) := by
  have hloc := makeRegion_corollary_loc_fresh h
  obtain ⟨frame, hlast, rfl⟩ := makeRegion_cases h
  unfold Reference.objAt?
  simp only [hloc, AList.lookup_insert, Option.bind_some]

-- `ReachableStep` agrees for every source other than the fresh region reference.
private theorem makeRegion_step_iff_of_ne {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeRegion x cfg = some cfg') {a : Reference} (hane : a ≠ Reference.RId cfg.freshRegionId)
    (b : Reference) : ReachableStep cfg a b ↔ ReachableStep cfg' a b := by
  rcases a with rid | oid
  · obtain ⟨frame, hlast, rfl⟩ := makeRegion_cases h
    rw [ReachableStep_rid_iff, ReachableStep_rid_iff]
    dsimp only
    rw [AList.lookup_insert_ne (by simpa using hane)]
  by_cases hne : oid = cfg.freshObjectId
  · subst hne
    simp [ReachableStep_oid_iff, freshObjectId_objAt_none, makeRegion_fresh_objAt_cfg' h, Object.refs]
  · rw [ReachableStep_oid_iff, ReachableStep_oid_iff, makeRegion_objAt_eq_of_ne vcfg h hne]

-- `RId cfg.freshRegionId` is never a `ReachableStep cfg'` target: by HS2 no pre-existing object stores it.
private theorem makeRegion_freshRid_not_target {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeRegion x cfg = some cfg') {a : Reference} :
    ¬ ReachableStep cfg' a (Reference.RId cfg.freshRegionId) := by
  intro hstep
  rcases a with rid | oid
  · obtain ⟨-, -, -, ⟨⟩⟩ := hstep
  rcases oid_step_container ((makeRegion_step_iff_of_ne vcfg h (by simp) _).mpr hstep) with
    ⟨_, _, -, hlk, hb⟩ | ⟨f, hf, -, hb⟩
  · exact cfg.freshRegionId_not_mem (vcfg.hs2 _ (List.mem_append_right _ (heap_refs_mem_of_lookup hlk hb)))
  · exact cfg.freshRegionId_not_mem (vcfg.hs2 _ (refs_mem_of_stackWithIndex hf hb))

-- A `cfg'`-chain rooted away from the fresh region stays off it and transports back into `cfg`.
theorem makeRegion_reflTransGen_transport_down {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeRegion x cfg = some cfg') {start : Reference} (hstartne : start ≠ Reference.RId cfg.freshRegionId) :
    ∀ {target : Reference}, Relation.ReflTransGen (ReachableStep cfg') start target →
      target ≠ Reference.RId cfg.freshRegionId ∧ Relation.ReflTransGen (ReachableStep cfg) start target := by
  intro target hrtg
  induction hrtg with
  | refl => exact ⟨hstartne, .refl⟩
  | tail _ hstep ih =>
    exact ⟨fun he => makeRegion_freshRid_not_target vcfg h (he ▸ hstep),
      ih.2.tail ((makeRegion_step_iff_of_ne vcfg h ih.1 _).mpr hstep)⟩

-- `FrameRoot` at an index below the last frame agrees, and is never the fresh region reference.
private theorem makeRegion_root_iff {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeRegion x cfg = some cfg') {i : Index} (hi : i < cfg.stack.length - 1) (start : Reference) :
    (FrameRoot cfg i start ↔ FrameRoot cfg' i start) ∧
      (FrameRoot cfg i start → start ≠ Reference.RId cfg.freshRegionId) := by
  have hdown : ∀ {f : FrameWithIndex}, f ∈ cfg'.stackWithIndex → f.index = i → f ∈ cfg.stackWithIndex :=
    fun hf hfi => by
      rcases makeRegion_frame_cases h hf with ⟨hm, -⟩ | ⟨-, -, -, -, -, -, hidx⟩
      · exact hm
      · rw [← hfi, hidx, List.length_dropLast] at hi
        exact absurd hi (lt_irrefl _)
  refine ⟨?_, fun hr he => ?_⟩
  swap
  · subst he
    rcases hr with ⟨f, hf, -, v, hv⟩ | ⟨-, -, -, -, -, ⟨⟩⟩
    exact cfg.freshRegionId_not_mem (vcfg.hs2 _ (refs_mem_of_stackWithIndex hf (mem_frame_refs_of_mem_varMap hv)))
  have hne : ∀ {f : FrameWithIndex}, f ∈ cfg.stackWithIndex → f.regionId ≠ cfg.freshRegionId := fun hf =>
    ne_freshRegionId_of_lookup (l2_of_stackWithIndex vcfg hf).choose_spec.1
  obtain ⟨lastFrame, hlast, rfl⟩ := makeRegion_cases h
  constructor
  · rintro (⟨f, hf, hfi, hv⟩ | ⟨f, hf, hfi, r, hr, hb⟩)
    · exact .inl ⟨f, makeRegion_frame_mem_up h hf (hfi ▸ hi), hfi, hv⟩
    · exact .inr ⟨f, makeRegion_frame_mem_up h hf (hfi ▸ hi), hfi, r, (AList.lookup_insert_ne (hne hf)).trans hr, hb⟩
  · rintro (⟨f, hf, hfi, hv⟩ | ⟨f, hf, hfi, r, hr, hb⟩)
    · exact .inl ⟨f, hdown hf hfi, hfi, hv⟩
    · exact .inr ⟨f, hdown hf hfi, hfi, r, (AList.lookup_insert_ne (hne (hdown hf hfi))).symm.trans hr, hb⟩

-- `FrameReachable` agrees below the last frame: `cfg` never steps out of the fresh `RId`, and `cfg'` never steps into it.
theorem makeRegion_frame_reachable_iff {cfg cfg' : RuntimeConfig} {x : VarName} (vcfg : ValidConfig cfg)
    (h : makeRegion x cfg = some cfg')
    {X : FrameWithIndex} (_hXmem : X ∈ cfg.stackWithIndex) (hXlt : X.index < cfg.stack.length - 1)
    (ref : Reference) : FrameReachable cfg X.index ref ↔ FrameReachable cfg' X.index ref := by
  simp only [FrameReachable_iff_reflTransGen, ← (makeRegion_root_iff vcfg h hXlt _).1]
  refine exists_congr fun s => and_congr_right fun hr => ⟨fun hc => hc.lift id fun a b hs => ?_,
    fun hc => (makeRegion_reflTransGen_transport_down vcfg h ((makeRegion_root_iff vcfg h hXlt s).2 hr) hc).2⟩
  refine (makeRegion_step_iff_of_ne vcfg h ?_ b).mp hs
  rintro rfl
  obtain ⟨region, hl, -⟩ := hs
  exact ne_freshRegionId_of_lookup hl rfl
