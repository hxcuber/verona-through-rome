module

public import Gc.Model.Types
public import Gc.Model.Helpers
public import Gc.Model.Validity
public import Gc.Model.Mutation.Mutation
public import Gc.Model.Preservation
public import Gc.Reachability.Reachable.Semantics
public import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.Def
public import Gc.Reachability.Reachable.Lemmas.Common
public import Gc.Reachability.Reachable.Lemmas.MakeObjStack
public import Gc.Reachability.Reachable.Lemmas.Merge

@[expose] public section

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
  obtain ⟨lastFrame, hlast, rfl⟩ := makeRegion_cases h
  constructor
  · rintro (⟨f, hf, hfi, hv⟩ | ⟨f, hf, hfi, r, hr, hb⟩)
    · exact .inl ⟨f, makeRegion_frame_mem_up h hf (hfi ▸ hi), hfi, hv⟩
    · exact .inr ⟨f, makeRegion_frame_mem_up h hf (hfi ▸ hi), hfi, r, (AList.lookup_insert_ne (frame_regionId_ne_fresh vcfg hf)).trans hr, hb⟩
  · rintro (⟨f, hf, hfi, hv⟩ | ⟨f, hf, hfi, r, hr, hb⟩)
    · exact .inl ⟨f, hdown hf hfi, hfi, hv⟩
    · exact .inr ⟨f, hdown hf hfi, hfi, r, (AList.lookup_insert_ne (frame_regionId_ne_fresh vcfg (hdown hf hfi))).symm.trans hr, hb⟩

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

-- A `cfg'` frame root is either the fresh region (via `x`) or already a `cfg` root.
private theorem makeRegion_root_down {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeRegion x cfg = some cfg') {fid : Index} {start : Reference} (hr : FrameRoot cfg' fid start) :
    start = .RId cfg.freshRegionId ∨ FrameRoot cfg fid start := by
  have hcases := fun {S} (hS : S ∈ cfg'.stackWithIndex) => makeRegion_frame_cases h hS
  obtain ⟨L, hL, rfl⟩ := makeRegion_cases h
  have hLm := stackWithIndex_getLast_mem hL
  rcases hr with ⟨S, hS, rfl, v, hv⟩ | ⟨S, hS, rfl, region, hl, rfl⟩ <;>
    rcases hcases hS with ⟨hS, -⟩ | ⟨L', hL', hrid, -, -, hvm, hi⟩
  · exact .inr (.inl ⟨S, hS, rfl, v, hv⟩)
  · obtain rfl : L' = L := Option.some_inj.mp (hL'.symm.trans hL)
    rw [hvm] at hv
    by_cases hvx : v = x
    · subst hvx
      simp at hv
      exact .inl hv.symm
    · rw [AList.lookup_insert_ne hvx] at hv
      exact .inr (.inl ⟨_, hLm, by simp [hi], v, hv⟩)
  · rw [AList.lookup_insert_ne (frame_regionId_ne_fresh vcfg hS)] at hl
    exact .inr (.inr ⟨S, hS, rfl, region, hl, rfl⟩)
  · obtain rfl : L' = L := Option.some_inj.mp (hL'.symm.trans hL)
    rw [hrid, AList.lookup_insert_ne (frame_regionId_ne_fresh vcfg hLm)] at hl
    exact .inr (.inr ⟨_, hLm, by simp [hi], region, hl, rfl⟩)

-- Reachability of a non-fresh object from any `cfg'` frame is stack-reachability in `cfg`.
private theorem makeRegion_reach_down {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeRegion x cfg = some cfg') {oid : ObjectId} (hne : oid ≠ cfg.freshObjectId) {fid : Index}
    (hr : FrameReachable cfg' fid (.OId oid)) :
    StackReachable cfg (.OId oid) := by
  obtain ⟨start, hs, hc⟩ := (FrameReachable_iff_reflTransGen ..).mp hr
  rcases makeRegion_root_down vcfg h hs with rfl | hs
  · rcases hc.cases_head with he | ⟨c, ⟨region, hl, -, rfl⟩, hc⟩
    · cases he
    obtain ⟨L, hL, hcfg'⟩ := makeRegion_cases h
    rw [hcfg', AList.lookup_insert, Option.some_inj] at hl
    subst hl
    rcases hc.cases_head with he | ⟨c, ⟨obj, ho, hco⟩, -⟩
    · exact absurd (Reference.OId.inj he).symm hne
    · rw [makeRegion_fresh_objAt_cfg' h, Option.some_inj] at ho
      subst ho
      simp [Object.refs] at hco
  · have hsne : start ≠ .RId cfg.freshRegionId := by
      rintro rfl
      rcases hs with ⟨S, hS, -, v, hv⟩ | ⟨_, _, _, _, _, ⟨⟩⟩
      exact cfg.freshRegionId_not_mem (vcfg.hs2 _ (refs_mem_of_stackWithIndex hS (mem_frame_refs_of_mem_varMap hv)))
    exact StackReachable_of_root hs (makeRegion_reflTransGen_transport_down vcfg h hsne hc).2

-- For `oid` in a suspended frame `F`'s region, makeRegion neither creates nor destroys its reachability from `F`.
theorem makeRegion_suspended_reach {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeRegion x cfg = some cfg') (hFR3 : FrameReachable_at_later_frame_implies_FrameReachable_at_frame cfg)
    {F : FrameWithIndex} (hF : F ∈ cfg.stackWithIndex) (hFlt : F.index < cfg.stackWithIndex.length - 1)
    {oid : ObjectId} (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn F.regionId)) :
    F ∈ cfg'.stackWithIndex ∧ (StackReachable cfg (.OId oid) → FrameReachable cfg' F.index (.OId oid)) ∧
    ∀ fid, FrameReachable cfg' fid (.OId oid) → StackReachable cfg (.OId oid) := by
  have hFlt' : F.index < cfg.stack.length - 1 := by simpa [RuntimeConfig.stackWithIndex] using hFlt
  exact ⟨makeRegion_frame_mem_up h hF hFlt', fun hs => (makeRegion_frame_reachable_iff vcfg h hF hFlt' _).mp
    (FrameReachable_of_StackReachable vcfg hFR3 hF hloc hs), fun _ => makeRegion_reach_down vcfg h (fun he => freshObjectId_loc_ne_rgn (he ▸ hloc))⟩
