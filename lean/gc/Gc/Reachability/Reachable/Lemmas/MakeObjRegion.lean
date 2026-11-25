module

public import Gc.Model.Types
public import Gc.Model.Helpers
public import Gc.Model.Validity
public import Gc.Model.Mutation.Mutation
public import Gc.Model.Preservation
public import Gc.Reachability.Reachable.Semantics
public import Gc.Reachability.Reachable.Lemmas.Common
public import Gc.Reachability.Reachable.Lemmas.MakeObjStack

@[expose] public section

-- `objAt?` agrees between `cfg`/`cfg'` for any oid other than the freshly-allocated one.
private theorem makeObjRegion_objAt_eq_of_ne {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeObjRegion x cfg = some cfg') {oid : ObjectId} (hne : oid ≠ cfg.freshObjectId) :
    (Reference.OId oid).objAt? cfg = (Reference.OId oid).objAt? cfg' := by
  have hlocEq := makeObjRegion_corollary_loc_eq vcfg h oid hne
  obtain ⟨frame, region, hlast, hlookup, -, rfl⟩ := makeObjRegion_cases h
  unfold Reference.objAt?
  dsimp only
  rw [hlocEq]
  rcases (Reference.OId oid).loc? _ with _ | rid | fid
  · rfl
  · dsimp only
    by_cases heq : rid = frame.regionId
    · subst heq
      simp [AList.lookup_insert, hlookup, AList.lookup_insert_ne hne]
    · rw [AList.lookup_insert_ne heq]
  dsimp only
  rw [stackWithIndex_find_index_eq_getElem, stackWithIndex_find_index_eq_getElem,
    stackWithIndex_eq_of_getLast? hlast, stackWithIndex_mk_append_singleton]
  simp only [List.getElem?_append, List.getElem?_singleton]
  split_ifs <;> simp

-- The freshly-allocated object resolves to its own (empty) content in cfg'.
private theorem makeObjRegion_fresh_objAt_cfg' {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeObjRegion x cfg = some cfg') :
    (Reference.OId cfg.freshObjectId).objAt? cfg' = some (∅ : Object) := by
  obtain ⟨frame0, hlast0, hlocFresh⟩ := makeObjRegion_corollary_loc_fresh vcfg h
  obtain ⟨frame, region, hlast, hlookup, -, rfl⟩ := makeObjRegion_cases h
  rw [hlast, Option.some_inj] at hlast0
  subst hlast0
  unfold Reference.objAt?
  simp [hlocFresh, AList.lookup_insert]

-- `ReachableStep` agrees unconditionally: the fresh id has no out-edges and the mutated region stays Open (no `RId` step either side).
theorem makeObjRegion_step_eq {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeObjRegion x cfg = some cfg') :
    ReachableStep cfg = ReachableStep cfg' := by
  funext a b
  apply propext
  rcases a with rid | oid
  · obtain ⟨frame, region, hlast, hlookup, hopen, rfl⟩ := makeObjRegion_cases h
    by_cases heq : rid = frame.regionId
    · subst heq
      exact iff_of_false (open_rid_no_step hlookup hopen)
        (open_rid_no_step (region := { region with objMap := region.objMap.insert cfg.freshObjectId ∅ })
          (AList.lookup_insert cfg.heap) hopen)
    · rw [ReachableStep_rid_iff, ReachableStep_rid_iff]
      dsimp only
      rw [AList.lookup_insert_ne heq]
  by_cases hne : oid = cfg.freshObjectId
  · subst hne
    simp [ReachableStep_oid_iff, freshObjectId_objAt_none, makeObjRegion_fresh_objAt_cfg' vcfg h, Object.refs]
  · rw [ReachableStep_oid_iff, ReachableStep_oid_iff, makeObjRegion_objAt_eq_of_ne vcfg h hne]

-- Every `cfg'.stackWithIndex` member is either an unchanged pre-existing frame or the last frame with `varMap` updated.
theorem makeObjRegion_frame_cases {cfg cfg' : RuntimeConfig} {x : VarName}
    (h : makeObjRegion x cfg = some cfg')
    {frame : FrameWithIndex} (hframe : frame ∈ cfg'.stackWithIndex) :
    (frame ∈ cfg.stackWithIndex ∧ frame.index < cfg.stack.length - 1) ∨
    (∃ lastFrame, cfg.stack.getLast? = some lastFrame ∧
      frame.regionId = lastFrame.regionId ∧ frame.bridgeVar = lastFrame.bridgeVar ∧
      frame.objMap = lastFrame.objMap ∧
      frame.varMap = lastFrame.varMap.insert x (Reference.OId cfg.freshObjectId) ∧
      frame.index = cfg.stack.dropLast.length) := by
  obtain ⟨lastFrame, region, hlast, -, -, rfl⟩ := makeObjRegion_cases h
  rw [stackWithIndex_mk_append_singleton] at hframe
  rcases List.mem_append.mp hframe with hmem | hmem
  · refine .inl ⟨stackWithIndex_eq_of_getLast? hlast ▸ List.mem_append_left _ hmem, ?_⟩
    obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp hmem
    simpa using hn
  · rw [List.mem_singleton.mp hmem]
    exact .inr ⟨lastFrame, hlast, rfl, rfl, rfl, rfl, rfl⟩

-- A pre-existing frame with index strictly below the last one survives `makeObjRegion` unchanged, at the same index.
theorem makeObjRegion_frame_mem_up {cfg cfg' : RuntimeConfig} {x : VarName}
    (h : makeObjRegion x cfg = some cfg')
    {frame : FrameWithIndex} (hframe : frame ∈ cfg.stackWithIndex) (hlt : frame.index < cfg.stack.length - 1) :
    frame ∈ cfg'.stackWithIndex := by
  obtain ⟨lastFrame, region, hlast, -, -, rfl⟩ := makeObjRegion_cases h
  rw [stackWithIndex_eq_of_getLast? hlast] at hframe
  rw [stackWithIndex_mk_append_singleton]
  rcases List.mem_append.mp hframe with hmem | hmem
  · exact List.mem_append_left _ hmem
  · rw [List.mem_singleton.mp hmem, List.length_dropLast] at hlt
    exact absurd hlt (lt_irrefl _)

-- `FrameRoot` at an index below the last frame agrees; a suspended frame's region is never the mutated one.
private theorem makeObjRegion_root_iff {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeObjRegion x cfg = some cfg') {i : Index} (hi : i < cfg.stack.length - 1) (start : Reference) :
    FrameRoot cfg i start ↔ FrameRoot cfg' i start := by
  have hdown : ∀ {f : FrameWithIndex}, f ∈ cfg'.stackWithIndex → f.index = i → f ∈ cfg.stackWithIndex :=
    fun hf hfi => by
      rcases makeObjRegion_frame_cases h hf with ⟨hm, -⟩ | ⟨-, -, -, -, -, -, hidx⟩
      · exact hm
      · rw [← hfi, hidx, List.length_dropLast] at hi
        exact absurd hi (lt_irrefl _)
  obtain ⟨lastFrame, region, hlast, -, -, rfl⟩ := makeObjRegion_cases h
  have hlk : ∀ {f : FrameWithIndex}, f ∈ cfg.stackWithIndex → f.index = i →
      (cfg.heap.insert lastFrame.regionId { region with objMap := region.objMap.insert cfg.freshObjectId ∅ }).lookup
        f.regionId = cfg.heap.lookup f.regionId :=
    fun hf hfi => AList.lookup_insert_ne (regionId_ne_last_of_suspended vcfg hf (hfi ▸ hi) hlast)
  constructor
  · rintro (⟨f, hf, hfi, hv⟩ | ⟨f, hf, hfi, r, hr, hb⟩)
    · exact .inl ⟨f, makeObjRegion_frame_mem_up h hf (hfi ▸ hi), hfi, hv⟩
    · exact .inr ⟨f, makeObjRegion_frame_mem_up h hf (hfi ▸ hi), hfi, r, (hlk hf hfi).trans hr, hb⟩
  · rintro (⟨f, hf, hfi, hv⟩ | ⟨f, hf, hfi, r, hr, hb⟩)
    · exact .inl ⟨f, hdown hf hfi, hfi, hv⟩
    · exact .inr ⟨f, hdown hf hfi, hfi, r, (hlk (hdown hf hfi) hfi).symm.trans hr, hb⟩

-- `FrameReachable` agrees below the last frame.
theorem makeObjRegion_frame_reachable_iff {cfg cfg' : RuntimeConfig} {x : VarName} (vcfg : ValidConfig cfg)
    (h : makeObjRegion x cfg = some cfg')
    {X : FrameWithIndex} (_hXmem : X ∈ cfg.stackWithIndex) (hXlt : X.index < cfg.stack.length - 1)
    (ref : Reference) : FrameReachable cfg X.index ref ↔ FrameReachable cfg' X.index ref := by
  simp only [FrameReachable_iff_reflTransGen, makeObjRegion_step_eq vcfg h, makeObjRegion_root_iff vcfg h hXlt]
