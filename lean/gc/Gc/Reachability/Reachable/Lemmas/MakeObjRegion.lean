import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Mutation.Mutation
import Gc.Model.Preservation
import Gc.Reachability.Reachable.Semantics
import Gc.Reachability.Reachable.Basic
import Gc.Reachability.Reachable.Lemmas.Common
import Gc.Reachability.Reachable.Lemmas.MakeObjStack

-- ===== makeObjRegion =====

-- `objAt?` agrees between `cfg`/`cfg'` for `oid ≠ freshObjectId`: heap side via `makeObjRegion_corollary_loc_eq`, stack side unconditional (only `varMap` changes).
theorem makeObjRegion_objAt_eq_of_ne {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeObjRegion x cfg = some cfg') {oid : ObjectId} (hne : oid ≠ cfg.freshObjectId) :
    (Reference.OId oid).objAt? cfg = (Reference.OId oid).objAt? cfg' := by
  obtain ⟨frame, region, hlast, hlookupRid, hopen, hcfg'⟩ := makeObjRegion_cases h
  have hlocEq := makeObjRegion_corollary_loc_eq vcfg h oid hne
  unfold Reference.objAt?
  dsimp only
  rw [hlocEq]
  cases hloc' : (Reference.OId oid).loc? cfg' with
  | none => rfl
  | some loc =>
    cases loc with
    | Rgn rid0 =>
      dsimp only
      by_cases heq : rid0 = frame.regionId
      · subst heq
        have hlookup' : cfg'.heap.lookup frame.regionId =
            some { region with objMap := region.objMap.insert cfg.freshObjectId ∅ } := by
          rw [hcfg']; dsimp only; rw [AList.lookup_insert]
        rw [hlookup', hlookupRid]
        simp [AList.lookup_insert_ne, hne]
      · have hlookup' : cfg'.heap.lookup rid0 = cfg.heap.lookup rid0 := by
          rw [hcfg']; dsimp only; rw [AList.lookup_insert_ne heq]
        rw [hlookup']
    | Stk fid0 =>
      dsimp only
      rw [stackWithIndex_find_index_eq_getElem, stackWithIndex_find_index_eq_getElem]
      have hshape := stackWithIndex_objMap_get_eq_of_last_varMap_update (cfg' := cfg') hlast (by rw [hcfg'])
      have hgetCfg : cfg.stackWithIndex[fid0]? =
          (cfg.stack[fid0]?).map (fun f => ({ toFrame := f, index := fid0 } : FrameWithIndex)) := by
        unfold RuntimeConfig.stackWithIndex; rw [List.getElem?_mapIdx]
      have hgetCfg' : cfg'.stackWithIndex[fid0]? =
          (cfg'.stack[fid0]?).map (fun f => ({ toFrame := f, index := fid0 } : FrameWithIndex)) := by
        unfold RuntimeConfig.stackWithIndex; rw [List.getElem?_mapIdx]
      rw [hgetCfg, hgetCfg']
      cases hc : cfg.stack[fid0]? with
      | none =>
        have hc' : cfg'.stack[fid0]? = none := by
          have hs := hshape fid0; rw [hc] at hs; simpa using hs.symm
        rw [hc']
      | some fA =>
        cases hc' : cfg'.stack[fid0]? with
        | none => have hs := hshape fid0; rw [hc, hc'] at hs; simp at hs
        | some fB =>
          have hobjmapEq : fA.objMap = fB.objMap := by
            have hs := hshape fid0; rw [hc, hc'] at hs; simpa using hs
          simp only [Option.map_some]
          dsimp only [Option.bind]
          rw [hobjmapEq]

-- The freshly-allocated object resolves to its own (empty) content in cfg'.
theorem makeObjRegion_fresh_objAt_cfg' {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeObjRegion x cfg = some cfg') :
    (Reference.OId cfg.freshObjectId).objAt? cfg' = some (∅ : Object) := by
  obtain ⟨frame, region, hlast, hlookupRid, hopen, hcfg'⟩ := makeObjRegion_cases h
  obtain ⟨frame0, hlast0, hlocFresh⟩ := makeObjRegion_corollary_loc_fresh vcfg h
  rw [hlast] at hlast0
  injection hlast0 with hlast0
  subst hlast0
  unfold Reference.objAt?
  dsimp only
  rw [hlocFresh]
  dsimp only
  have hlookup' : cfg'.heap.lookup frame.regionId =
      some { region with objMap := region.objMap.insert cfg.freshObjectId ∅ } := by
    rw [hcfg']; dsimp only; rw [AList.lookup_insert]
  rw [hlookup']
  simp [AList.lookup_insert]

-- `ReachableStep` agrees for every `OId`-sourced step: unconditional for `oid ≠ freshObjectId`, vacuous for the fresh id itself (empty object, no refs).
theorem makeObjRegion_oid_step_iff {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeObjRegion x cfg = some cfg') (oid : ObjectId) (b : Reference) :
    ReachableStep cfg (Reference.OId oid) b ↔ ReachableStep cfg' (Reference.OId oid) b := by
  by_cases hne : oid = cfg.freshObjectId
  · subst hne
    constructor
    · intro hstep
      rw [ReachableStep_oid_iff] at hstep
      obtain ⟨obj, hobjAt, -⟩ := hstep
      rw [freshObjectId_objAt_none] at hobjAt
      exact absurd hobjAt (by simp)
    · intro hstep
      rw [ReachableStep_oid_iff] at hstep
      obtain ⟨obj, hobjAt, hcontains⟩ := hstep
      rw [makeObjRegion_fresh_objAt_cfg' vcfg h] at hobjAt
      injection hobjAt with hobjAt
      rw [← hobjAt] at hcontains
      simp [Object.refs] at hcontains
  · rw [ReachableStep_oid_iff, ReachableStep_oid_iff, makeObjRegion_objAt_eq_of_ne vcfg h hne]

-- `ReachableStep` agrees for every `RId`-sourced step: the mutated region stays Open throughout (`open_rid_no_step` rules out a step either side).
theorem makeObjRegion_rid_step_iff {cfg cfg' : RuntimeConfig}
    (h : makeObjRegion x cfg = some cfg') (rid : RegionId) (b : Reference) :
    ReachableStep cfg (Reference.RId rid) b ↔ ReachableStep cfg' (Reference.RId rid) b := by
  obtain ⟨frame, region, hlast, hlookupRid, hopen, hcfg'⟩ := makeObjRegion_cases h
  by_cases heq : rid = frame.regionId
  · subst heq
    have hlookup' : cfg'.heap.lookup frame.regionId =
        some { region with objMap := region.objMap.insert cfg.freshObjectId ∅ } := by
      rw [hcfg']; dsimp only; rw [AList.lookup_insert]
    constructor
    · intro hstep; exact absurd hstep (open_rid_no_step hlookupRid hopen)
    · intro hstep; exact absurd hstep (open_rid_no_step hlookup' hopen)
  · have hlookup' : cfg'.heap.lookup rid = cfg.heap.lookup rid := by
      rw [hcfg']; dsimp only; rw [AList.lookup_insert_ne heq]
    rw [ReachableStep_rid_iff, ReachableStep_rid_iff, hlookup']

-- `ReachableStep` agrees between `cfg`/`cfg'` as a literal function equality (combines the two cases above).
theorem makeObjRegion_step_eq {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeObjRegion x cfg = some cfg') :
    ReachableStep cfg = ReachableStep cfg' := by
  funext a b
  apply propext
  cases a with
  | OId oid => exact makeObjRegion_oid_step_iff vcfg h oid b
  | RId rid => exact makeObjRegion_rid_step_iff h rid b

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
  obtain ⟨lastFrame, region, hlast, hlookupRid, hopen, hcfg'⟩ := makeObjRegion_cases h
  have hstack' : cfg'.stack = cfg.stack.dropLast ++ [{ lastFrame with
      varMap := lastFrame.varMap.insert x (Reference.OId cfg.freshObjectId) }] := by rw [hcfg']
  have hstackEq : cfg.stack = cfg.stack.dropLast ++ [lastFrame] :=
    (List.dropLast_append_getLast? lastFrame hlast).symm
  unfold RuntimeConfig.stackWithIndex at hframe
  rw [hstack'] at hframe
  rw [List.mapIdx_concat] at hframe
  rcases List.mem_append.mp hframe with hmem | hmem
  · left
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hmem
    have hidx : frame.index = n := by rw [← hfeq]
    have hmem' : frame ∈ cfg.stackWithIndex := by
      unfold RuntimeConfig.stackWithIndex
      conv_lhs => rw [hstackEq]
      rw [List.mapIdx_concat]
      exact List.mem_append_left _ hmem
    refine ⟨hmem', ?_⟩
    rw [hidx, ← List.length_dropLast]
    exact hn
  · right
    rw [List.mem_singleton] at hmem
    subst hmem
    exact ⟨lastFrame, hlast, rfl, rfl, rfl, rfl, rfl⟩

-- A pre-existing frame with index strictly below the last one survives `makeObjRegion` unchanged, at the same index.
theorem makeObjRegion_frame_mem_up {cfg cfg' : RuntimeConfig} {x : VarName}
    (h : makeObjRegion x cfg = some cfg')
    {frame : FrameWithIndex} (hframe : frame ∈ cfg.stackWithIndex) (hlt : frame.index < cfg.stack.length - 1) :
    frame ∈ cfg'.stackWithIndex := by
  obtain ⟨lastFrame, region, hlast, hlookupRid, hopen, hcfg'⟩ := makeObjRegion_cases h
  have hstack' : cfg'.stack = cfg.stack.dropLast ++ [{ lastFrame with
      varMap := lastFrame.varMap.insert x (Reference.OId cfg.freshObjectId) }] := by rw [hcfg']
  unfold RuntimeConfig.stackWithIndex at hframe ⊢
  rw [hstack']
  obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hframe
  have hidx : frame.index = n := by rw [← hfeq]
  have hnlt : n < cfg.stack.dropLast.length := by rw [List.length_dropLast]; rw [hidx] at hlt; exact hlt
  apply List.mem_mapIdx.mpr
  refine ⟨n, ?_, ?_⟩
  · rw [List.length_append]; omega
  · rw [List.getElem_append_left hnlt, List.getElem_dropLast hnlt]
    exact hfeq

-- A frame strictly before the last one has a different regionId from the last frame's own (S1: regionId is injective across the stack).
theorem makeObjRegion_regionId_ne {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {f : FrameWithIndex} (hf : f ∈ cfg.stackWithIndex) (hflt : f.index < cfg.stack.length - 1)
    {lastFrame : Frame} (hlast : cfg.stack.getLast? = some lastFrame) :
    f.regionId ≠ lastFrame.regionId := by
  intro heq
  have hlastMem := stackWithIndex_getLast_mem hlast
  have hidxEq : f.index = ({ lastFrame with index := cfg.stack.length - 1 } : FrameWithIndex).index :=
    merge_corollary_regionId_unique_index vcfg.s1 hf hlastMem heq
  dsimp only at hidxEq
  rw [hidxEq] at hflt
  exact absurd hflt (lt_irrefl _)

-- `FrameReachable` agrees below the last frame; the new wrinkle vs. `makeObjStack` is transporting a `FrameRoot`'s bridge-object heap lookup via the regionId-disjointness fact above.
theorem makeObjRegion_frame_reachable_iff {cfg cfg' : RuntimeConfig} {x : VarName} (vcfg : ValidConfig cfg)
    (h : makeObjRegion x cfg = some cfg')
    {X : FrameWithIndex} (_hXmem : X ∈ cfg.stackWithIndex) (hXlt : X.index < cfg.stack.length - 1)
    (ref : Reference) : FrameReachable cfg X.index ref ↔ FrameReachable cfg' X.index ref := by
  obtain ⟨lastFrame, region, hlast, hlookupRid, hopen, hcfg'⟩ := makeObjRegion_cases h
  rw [FrameReachable_iff_reflTransGen, FrameReachable_iff_reflTransGen, makeObjRegion_step_eq vcfg h]
  constructor
  · rintro ⟨start, hroot, hrtg⟩
    refine ⟨start, ?_, hrtg⟩
    rcases hroot with ⟨Xf, hXfmem, hXfidx, var, hvar⟩ | ⟨Xf, hXfmem, hXfidx, regionX, hlookup, hbridge⟩
    · exact Or.inl ⟨Xf, makeObjRegion_frame_mem_up h hXfmem (hXfidx ▸ hXlt), hXfidx, var, hvar⟩
    · have hXfne : Xf.regionId ≠ lastFrame.regionId :=
        makeObjRegion_regionId_ne vcfg hXfmem (hXfidx ▸ hXlt) hlast
      have hlookup' : cfg'.heap.lookup Xf.regionId = some regionX := by
        rw [hcfg']; dsimp only; rw [AList.lookup_insert_ne hXfne]; exact hlookup
      exact Or.inr ⟨Xf, makeObjRegion_frame_mem_up h hXfmem (hXfidx ▸ hXlt), hXfidx, regionX, hlookup', hbridge⟩
  · rintro ⟨start, hroot, hrtg⟩
    refine ⟨start, ?_, hrtg⟩
    rcases hroot with ⟨Xf, hXfmem, hXfidx, var, hvar⟩ | ⟨Xf, hXfmem, hXfidx, regionX, hlookup, hbridge⟩
    · rcases makeObjRegion_frame_cases h hXfmem with ⟨hXfmemcfg, -⟩ | ⟨lf, hlf, -, -, -, -, hXfidx2⟩
      · exact Or.inl ⟨Xf, hXfmemcfg, hXfidx, var, hvar⟩
      · exfalso
        rw [hlast] at hlf
        injection hlf with hlf
        subst hlf
        have hXeq : X.index = cfg.stack.dropLast.length := by rw [← hXfidx, hXfidx2]
        rw [hXeq, List.length_dropLast] at hXlt
        exact absurd hXlt (lt_irrefl _)
    · rcases makeObjRegion_frame_cases h hXfmem with ⟨hXfmemcfg, hXflt⟩ | ⟨lf, hlf, -, -, -, -, hXfidx2⟩
      · have hXfne : Xf.regionId ≠ lastFrame.regionId :=
          makeObjRegion_regionId_ne vcfg hXfmemcfg hXflt hlast
        have hlookupcfg : cfg.heap.lookup Xf.regionId = some regionX := by
          rw [hcfg'] at hlookup; dsimp only at hlookup
          rw [AList.lookup_insert_ne hXfne] at hlookup; exact hlookup
        exact Or.inr ⟨Xf, hXfmemcfg, hXfidx, regionX, hlookupcfg, hbridge⟩
      · exfalso
        rw [hlast] at hlf
        injection hlf with hlf
        subst hlf
        have hXeq : X.index = cfg.stack.dropLast.length := by rw [← hXfidx, hXfidx2]
        rw [hXeq, List.length_dropLast] at hXlt
        exact absurd hXlt (lt_irrefl _)
