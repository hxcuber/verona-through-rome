import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Mutation.Mutation
import Gc.Model.Preservation
import Gc.Reachability.Reachable.Semantics
import Gc.Reachability.Reachable.Basic
import Gc.Reachability.Reachable.Lemmas.Common
import Gc.Reachability.Reachable.Lemmas.Enter
import Gc.Reachability.Reachable.Lemmas.VarAsgn

-- ===== fieldAsgn =====

-- `objAt?` agrees between `cfg`/`cfg'` for `oid' ≠ oid` (STACK branch): reduces to `AList.lookup_insert_ne` on the mutated frame's `objMap`.
theorem fieldAsgn_stack_objAt_eq_of_ne {cfg cfg' : RuntimeConfig} {frame : FrameWithIndex} {oid : ObjectId}
    {obj : Object} {field : FieldName} {yRef : Reference}
    (hframe : cfg.stackWithIndex.getLast? = some frame) (hobj : frame.objMap.lookup oid = some obj)
    (hcfg' : cfg' = { cfg with stack := cfg.stack.dropLast ++
      [({ frame with objMap := frame.objMap.insert oid (obj.insert field yRef) } : Frame)] })
    {oid' : ObjectId} (hne : oid' ≠ oid) :
    (Reference.OId oid').objAt? cfg = (Reference.OId oid').objAt? cfg' := by
  have hlocEq : (Reference.OId oid').loc? cfg = (Reference.OId oid').loc? cfg' := by
    rw [hcfg']; exact fieldAsgn_corollary_stack_loc_eq hframe hobj oid'
  obtain ⟨stack_eq, hframeidx⟩ := fieldAsgn_corollary_stack_eq hframe
  unfold Reference.objAt?
  dsimp only
  rw [hlocEq]
  cases hloc' : (Reference.OId oid').loc? cfg' with
  | none => rfl
  | some loc =>
    cases loc with
    | Rgn ridX =>
      dsimp only
      have hheapEq : cfg'.heap = cfg.heap := by rw [hcfg']
      rw [hheapEq]
    | Stk fidX =>
      dsimp only
      rw [stackWithIndex_find_index_eq_getElem, stackWithIndex_find_index_eq_getElem]
      have hgetCfg : cfg.stackWithIndex[fidX]? =
          (cfg.stack[fidX]?).map (fun f => ({ toFrame := f, index := fidX } : FrameWithIndex)) := by
        unfold RuntimeConfig.stackWithIndex; rw [List.getElem?_mapIdx]
      have hgetCfg' : cfg'.stackWithIndex[fidX]? =
          (cfg'.stack[fidX]?).map (fun f => ({ toFrame := f, index := fidX } : FrameWithIndex)) := by
        unfold RuntimeConfig.stackWithIndex; rw [List.getElem?_mapIdx]
      rw [hgetCfg, hgetCfg']
      have hstack' : cfg'.stack = cfg.stack.dropLast ++
          [({ frame with objMap := frame.objMap.insert oid (obj.insert field yRef) } : Frame)] := by rw [hcfg']
      have hfidxlt : fidX < cfg'.stack.length := loc_stk_lt hloc'
      have hlen' : cfg'.stack.length = cfg.stack.dropLast.length + 1 := by rw [hstack']; simp
      rw [hlen'] at hfidxlt
      by_cases hfx : fidX = cfg.stack.dropLast.length
      · have h1 : cfg.stack[fidX]? = some frame.toFrame := by
          conv_lhs => rw [stack_eq, hfx]
          simp
        have h2 : cfg'.stack[fidX]? =
            some ({ frame with objMap := frame.objMap.insert oid (obj.insert field yRef) } : Frame) := by
          rw [hstack', hfx]
          simp
        rw [h1, h2]
        simp only [Option.map_some]
        dsimp only [Option.bind]
        rw [AList.lookup_insert_ne hne]
      · have hlt : fidX < cfg.stack.dropLast.length := lt_of_le_of_ne (Nat.lt_succ_iff.mp hfidxlt) hfx
        have h1 : cfg.stack[fidX]? = cfg.stack.dropLast[fidX]? := by
          conv_lhs => rw [stack_eq]
          rw [List.getElem?_append_left hlt]
        have h2 : cfg'.stack[fidX]? = cfg.stack.dropLast[fidX]? := by
          rw [hstack', List.getElem?_append_left hlt]
        rw [h1, h2]

-- `objAt?` agrees between `cfg`/`cfg'` for `oid' ≠ oid` (REGION branch): mirrors the stack version, at the heap level.
theorem fieldAsgn_region_objAt_eq_of_ne {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid oid : ObjectId} {region : Region} {obj : Object} {field : FieldName} {yRef : Reference}
    (hregion : cfg.heap.lookup rid = some region) (hobj : region.objMap.lookup oid = some obj)
    (hcfg' : cfg' = { cfg with heap := cfg.heap.insert rid ({ region with objMap := region.objMap.insert oid (obj.insert field yRef) } : Region) }) :
    ∀ {oid' : ObjectId}, oid' ≠ oid →
    (Reference.OId oid').objAt? cfg = (Reference.OId oid').objAt? cfg' := by
  intro oid' hne
  have hlocEq : (Reference.OId oid').loc? cfg = (Reference.OId oid').loc? cfg' := by
    rw [hcfg']; exact fieldAsgn_corollary_region_loc_eq vcfg hregion hobj oid'
  unfold Reference.objAt?
  dsimp only
  rw [hlocEq]
  cases hloc' : (Reference.OId oid').loc? cfg' with
  | none => rfl
  | some loc =>
    cases loc with
    | Rgn ridX =>
      dsimp only
      by_cases hridx : ridX = rid
      · subst hridx
        have hlookup' : cfg'.heap.lookup ridX = some
            ({ region with objMap := region.objMap.insert oid (obj.insert field yRef) } : Region) := by
          rw [hcfg']; dsimp only; rw [AList.lookup_insert]
        rw [hlookup', hregion]
        dsimp only [Option.bind]
        rw [AList.lookup_insert_ne hne]
      · have hlookup' : cfg'.heap.lookup ridX = cfg.heap.lookup ridX := by
          rw [hcfg']; dsimp only; rw [AList.lookup_insert_ne hridx]
        rw [hlookup']
    | Stk fidX =>
      dsimp only
      rw [stackWithIndex_find_index_eq_getElem, stackWithIndex_find_index_eq_getElem]
      have hstackEq : cfg'.stack = cfg.stack := by rw [hcfg']
      unfold RuntimeConfig.stackWithIndex
      rw [hstackEq]

-- `ReachableStep` agrees between `cfg`/`cfg'` for any source other than the mutated container; returns the container's own id existentially.
theorem fieldAsgn_step_iff_of_ne {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : fieldAsgn xf y cfg = some cfg') :
    ∃ oidC : ObjectId, resolveV xf.root cfg = some (Reference.OId oidC) ∧
      ∀ a : Reference, a ≠ Reference.OId oidC → ∀ b : Reference,
      ReachableStep cfg a b ↔ ReachableStep cfg' a b := by
  obtain ⟨frame, hframe, hcase⟩ := fieldAsgn_cases h
  rcases hcase with
      ⟨oid, oid_y, obj, hxr, hyr, hloc, hobj, hcfg'⟩ |
      ⟨oid, oid_y, rid, region, obj, hxr, hyr, hloc, hregion, hobj, hyloc, hstatus, hfrid, hcfg'⟩
  · refine ⟨oid, hxr, fun a hane b => ?_⟩
    cases a with
    | OId oid' =>
      have hne : oid' ≠ oid := fun heq => hane (heq ▸ rfl)
      rw [ReachableStep_oid_iff, ReachableStep_oid_iff, fieldAsgn_stack_objAt_eq_of_ne hframe hobj hcfg' hne]
    | RId rid' =>
      have hheapEq : cfg'.heap = cfg.heap := by rw [hcfg']
      rw [ReachableStep_rid_iff, ReachableStep_rid_iff, hheapEq]
  · refine ⟨oid, hxr, fun a hane b => ?_⟩
    cases a with
    | OId oid' =>
      have hne : oid' ≠ oid := fun heq => hane (heq ▸ rfl)
      rw [ReachableStep_oid_iff, ReachableStep_oid_iff, fieldAsgn_region_objAt_eq_of_ne vcfg hregion hobj hcfg' hne]
    | RId rid' =>
      by_cases hridEq : rid' = rid
      · subst hridEq
        have hlookup' : cfg'.heap.lookup rid' = some
            ({ region with objMap := region.objMap.insert oid (obj.insert xf.field (Reference.OId oid_y)) } : Region) := by
          rw [hcfg']; dsimp only; rw [AList.lookup_insert]
        constructor
        · intro hstep; exact absurd hstep (open_rid_no_step hregion hstatus)
        · intro hstep; exact absurd hstep (open_rid_no_step hlookup' hstatus)
      · have hlookup' : cfg'.heap.lookup rid' = cfg.heap.lookup rid' := by
          rw [hcfg']; dsimp only; rw [AList.lookup_insert_ne hridEq]
        rw [ReachableStep_rid_iff, ReachableStep_rid_iff, hlookup']

-- Mirror of `stackWithIndex_objMap_get_eq_of_last_varMap_update`: replacing only the last frame's `objMap` leaves `(varMap, bridgeVar, regionId)` unaffected everywhere.
theorem fieldAsgn_stack_shape_eq {cfg cfg' : RuntimeConfig} {frame : Frame}
    {newObjMap : ObjMap} (hframeLast : cfg.stack.getLast? = some frame)
    (hstack' : cfg'.stack = cfg.stack.dropLast ++
      [({ regionId := frame.regionId, bridgeVar := frame.bridgeVar, objMap := newObjMap,
          varMap := frame.varMap } : Frame)]) (n : ℕ) :
    (cfg.stack[n]?).map (fun f : Frame => (f.varMap, f.bridgeVar, f.regionId)) =
    (cfg'.stack[n]?).map (fun f : Frame => (f.varMap, f.bridgeVar, f.regionId)) := by
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
    (List.dropLast_append_getLast? frame hframeLast).symm
  set newFrame : Frame :=
    { regionId := frame.regionId, bridgeVar := frame.bridgeVar, objMap := newObjMap,
      varMap := frame.varMap } with newFrame_def
  by_cases hlp : n = cfg.stack.dropLast.length
  · have e1 : cfg.stack[n]? = some frame := by
      conv_lhs => rw [stack_eq, hlp]
      simp
    have e2 : cfg'.stack[n]? = some newFrame := by
      rw [hstack']; rw [hlp]
      simp
    rw [e1, e2]
    rfl
  · by_cases hlt : n < cfg.stack.dropLast.length
    · have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
        conv_lhs => rw [stack_eq]
        rw [List.getElem?_append_left hlt]
      have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
        rw [hstack']; rw [List.getElem?_append_left hlt]
      rw [e1, e2]
    · have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq]; simp
      have hlen' : cfg'.stack.length = cfg.stack.dropLast.length + 1 := by rw [hstack']; simp
      have e1 : cfg.stack[n]? = none := List.getElem?_eq_none (by omega)
      have e2 : cfg'.stack[n]? = none := List.getElem?_eq_none (by omega)
      rw [e1, e2]

-- `FrameRoot` agrees between `cfg`/`cfg'` unconditionally: fieldAsgn only ever touches an `objMap`, never `varMap`/`bridgeVar`/`bridgeObjectId`.
theorem fieldAsgn_frame_root_iff {cfg cfg' : RuntimeConfig} (h : fieldAsgn xf y cfg = some cfg')
    (fid : Index) (start : Reference) : FrameRoot cfg fid start ↔ FrameRoot cfg' fid start := by
  obtain ⟨frame, hframe, hcase⟩ := fieldAsgn_cases h
  rcases hcase with
      ⟨oid, oid_y, obj, hxr, hyr, hloc, hobj, hcfg'⟩ |
      ⟨oid, oid_y, rid, region, obj, hxr, hyr, hloc, hregion, hobj, hyloc, hstatus, hfrid, hcfg'⟩
  · obtain ⟨stack_eq, hframeidx⟩ := fieldAsgn_corollary_stack_eq hframe
    have hframeLast : cfg.stack.getLast? = some frame.toFrame := by
      rw [stack_eq]; simp
    have hstack' : cfg'.stack = cfg.stack.dropLast ++
        [({ regionId := frame.regionId, bridgeVar := frame.bridgeVar,
            objMap := frame.objMap.insert oid (obj.insert xf.field (Reference.OId oid_y)),
            varMap := frame.varMap } : Frame)] := by rw [hcfg']
    have hshape := fieldAsgn_stack_shape_eq hframeLast hstack'
    have hheapEq : cfg'.heap = cfg.heap := by rw [hcfg']
    constructor
    · rintro (⟨frameV, hVmem, hVidx, var, hvar⟩ | ⟨frameV, hVmem, hVidx, regionV, hVlookup, hVbridge⟩)
      · obtain ⟨frameV0, hVmem0, hVidx0, hproj0⟩ := stackWithIndex_frame_transport_up_of_shape_eq hshape frameV hVmem
        refine Or.inl ⟨frameV0, hVmem0, hVidx0.trans hVidx, var, ?_⟩
        rw [show frameV0.varMap = frameV.varMap from congrArg (·.1) hproj0]
        exact hvar
      · obtain ⟨frameV0, hVmem0, hVidx0, hproj0⟩ := stackWithIndex_frame_transport_up_of_shape_eq hshape frameV hVmem
        refine Or.inr ⟨frameV0, hVmem0, hVidx0.trans hVidx, regionV, ?_, hVbridge⟩
        rw [show frameV0.regionId = frameV.regionId from congrArg (·.2.2) hproj0, hheapEq]
        exact hVlookup
    · rintro (⟨frameV, hVmem, hVidx, var, hvar⟩ | ⟨frameV, hVmem, hVidx, regionV, hVlookup, hVbridge⟩)
      · obtain ⟨frameV0, hVmem0, hVidx0, hproj0⟩ := stackWithIndex_frame_transport_down_of_shape_eq hshape frameV hVmem
        refine Or.inl ⟨frameV0, hVmem0, hVidx0.trans hVidx, var, ?_⟩
        rw [show frameV0.varMap = frameV.varMap from congrArg (·.1) hproj0]
        exact hvar
      · obtain ⟨frameV0, hVmem0, hVidx0, hproj0⟩ := stackWithIndex_frame_transport_down_of_shape_eq hshape frameV hVmem
        refine Or.inr ⟨frameV0, hVmem0, hVidx0.trans hVidx, regionV, ?_, hVbridge⟩
        rw [show frameV0.regionId = frameV.regionId from congrArg (·.2.2) hproj0, ← hheapEq]
        exact hVlookup
  · have hstackEq : cfg'.stack = cfg.stack := by rw [hcfg']
    have hstackWithIndexEq : cfg'.stackWithIndex = cfg.stackWithIndex := by
      unfold RuntimeConfig.stackWithIndex; rw [hstackEq]
    constructor
    · rintro (⟨frameV, hVmem, hVidx, var, hvar⟩ | ⟨frameV, hVmem, hVidx, regionV, hVlookup, hVbridge⟩)
      · exact Or.inl ⟨frameV, hstackWithIndexEq ▸ hVmem, hVidx, var, hvar⟩
      · by_cases hrideq : frameV.regionId = rid
        · have hlookup' : cfg'.heap.lookup frameV.regionId =
              some ({ region with objMap := region.objMap.insert oid (obj.insert xf.field (Reference.OId oid_y)) } : Region) := by
            rw [hrideq, hcfg']; dsimp only; rw [AList.lookup_insert]
          rw [hrideq] at hVlookup
          have hbeq : regionV = region := by
            have hcomb := hVlookup.symm.trans hregion
            injection hcomb
          rw [hbeq] at hVbridge
          exact Or.inr ⟨frameV, hstackWithIndexEq ▸ hVmem, hVidx, _, hlookup', hVbridge⟩
        · have hlookup' : cfg'.heap.lookup frameV.regionId = cfg.heap.lookup frameV.regionId := by
            rw [hcfg']; dsimp only; rw [AList.lookup_insert_ne hrideq]
          exact Or.inr ⟨frameV, hstackWithIndexEq ▸ hVmem, hVidx, regionV, hlookup'.trans hVlookup, hVbridge⟩
    · rintro (⟨frameV, hVmem, hVidx, var, hvar⟩ | ⟨frameV, hVmem, hVidx, regionV, hVlookup, hVbridge⟩)
      · exact Or.inl ⟨frameV, hstackWithIndexEq ▸ hVmem, hVidx, var, hvar⟩
      · by_cases hrideq : frameV.regionId = rid
        · have hlookupcfg' : cfg'.heap.lookup frameV.regionId =
              some ({ region with objMap := region.objMap.insert oid (obj.insert xf.field (Reference.OId oid_y)) } : Region) := by
            rw [hrideq, hcfg']; dsimp only; rw [AList.lookup_insert]
          rw [hlookupcfg'] at hVlookup
          injection hVlookup with hVlookupEq
          rw [← hVlookupEq] at hVbridge
          dsimp only at hVbridge
          exact Or.inr ⟨frameV, hstackWithIndexEq ▸ hVmem, hVidx, region, by rw [hrideq]; exact hregion, hVbridge⟩
        · have hlookup' : cfg'.heap.lookup frameV.regionId = cfg.heap.lookup frameV.regionId := by
            rw [hcfg']; dsimp only; rw [AList.lookup_insert_ne hrideq]
          exact Or.inr ⟨frameV, hstackWithIndexEq ▸ hVmem, hVidx, regionV, hlookup'.symm.trans hVlookup, hVbridge⟩

-- A `FrameReachable cfg G ref` chain confined away from the mutated container `oidC` transports unconditionally to `cfg'`, hop by hop.
theorem fieldAsgn_confined_transport {cfg cfg' : RuntimeConfig}
    {oidC : ObjectId} (hstepIffOfNe : ∀ a : Reference, a ≠ Reference.OId oidC → ∀ b : Reference,
      ReachableStep cfg a b ↔ ReachableStep cfg' a b)
    (hframeRootIff : ∀ fid start, FrameRoot cfg fid start ↔ FrameRoot cfg' fid start)
    {G : Index} (hconfined : ∀ refX, FrameReachable cfg G refX → refX ≠ Reference.OId oidC)
    {ref : Reference} (hreach : FrameReachable cfg G ref) :
    FrameReachable cfg' G ref := by
  rw [FrameReachable_iff_reflTransGen] at hreach
  obtain ⟨start, hroot, hrtg⟩ := hreach
  rw [FrameReachable_iff_reflTransGen]
  refine ⟨start, (hframeRootIff G start).mp hroot, ?_⟩
  induction hrtg with
  | refl => exact Relation.ReflTransGen.refl
  | tail hprev hstep ih =>
    rename_i p c
    have hpReach : FrameReachable cfg G p :=
      (FrameReachable_iff_reflTransGen cfg G p).mpr ⟨start, hroot, hprev⟩
    have hpne : p ≠ Reference.OId oidC := hconfined p hpReach
    exact ih.tail ((hstepIffOfNe p hpne c).mp hstep)

-- Stack membership below the active frame agrees between `cfg`/`cfg'`: fieldAsgn never touches any other frame's record.
theorem fieldAsgn_frame_mem_iff {cfg cfg' : RuntimeConfig} (h : fieldAsgn xf y cfg = some cfg')
    {X : FrameWithIndex} {activeIdx : Index} (hXlt : X.index < activeIdx)
    (hactiveidx : activeIdx = cfg.stack.dropLast.length) :
    X ∈ cfg.stackWithIndex ↔ X ∈ cfg'.stackWithIndex := by
  obtain ⟨frame, hframe, hcase⟩ := fieldAsgn_cases h
  rcases hcase with
      ⟨oid, oid_y, obj, hxr, hyr, hloc, hobj, hcfg'⟩ |
      ⟨oid, oid_y, rid, region, obj, hxr, hyr, hloc, hregion, hobj, hyloc, hstatus, hfrid, hcfg'⟩
  · have hstack' : cfg'.stack = cfg.stack.dropLast ++
        [({ frame with objMap := frame.objMap.insert oid (obj.insert xf.field (Reference.OId oid_y)) } : Frame)] := by
      rw [hcfg']
    constructor
    · intro hXmem
      unfold RuntimeConfig.stackWithIndex
      rw [hstack']
      obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hXmem
      have hidx : X.index = n := by rw [← hfeq]
      have hnlt : n < cfg.stack.dropLast.length := by rw [← hidx, ← hactiveidx]; exact hXlt
      apply List.mem_mapIdx.mpr
      refine ⟨n, ?_, ?_⟩
      · rw [List.length_append]; omega
      · rw [List.getElem_append_left hnlt, List.getElem_dropLast hnlt]; exact hfeq
    · intro hXmem
      unfold RuntimeConfig.stackWithIndex at hXmem
      rw [hstack'] at hXmem
      rw [List.mapIdx_concat] at hXmem
      rcases List.mem_append.mp hXmem with hmem | hmem
      · obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hmem
        have hnlt : n < cfg.stack.length := lt_of_lt_of_le hn (List.length_dropLast .. ▸ Nat.sub_le _ _)
        unfold RuntimeConfig.stackWithIndex
        apply List.mem_mapIdx.mpr
        refine ⟨n, hnlt, ?_⟩
        rw [← List.getElem_dropLast hn]
        exact hfeq
      · exfalso
        rw [List.mem_singleton] at hmem
        have hXeq : X.index = cfg.stack.dropLast.length := by rw [hmem]
        rw [hXeq, ← hactiveidx] at hXlt
        exact absurd hXlt (lt_irrefl _)
  · have hstackEq : cfg'.stack = cfg.stack := by rw [hcfg']
    unfold RuntimeConfig.stackWithIndex
    rw [hstackEq]

-- The mutated container's own step, restricted away from the just-written value `oid_y`, transports backward unconditionally (STACK branch).
theorem fieldAsgn_stack_oidC_step_of_ne_oidY {cfg cfg' : RuntimeConfig} {frame : FrameWithIndex}
    {oid oid_y : ObjectId} {obj : Object} {field : FieldName}
    (hframe : cfg.stackWithIndex.getLast? = some frame)
    (hlocC : (Reference.OId oid).loc? cfg = some (Location.Stk frame.index))
    (hobj : frame.objMap.lookup oid = some obj)
    (hcfg' : cfg' = { cfg with stack := cfg.stack.dropLast ++
      [({ frame with objMap := frame.objMap.insert oid (obj.insert field (Reference.OId oid_y)) } : Frame)] })
    {c : Reference} (hstep : ReachableStep cfg' (Reference.OId oid) c) :
    c = Reference.OId oid_y ∨ ReachableStep cfg (Reference.OId oid) c := by
  have hlocEq : (Reference.OId oid).loc? cfg = (Reference.OId oid).loc? cfg' := by
    rw [hcfg']; exact fieldAsgn_corollary_stack_loc_eq hframe hobj oid
  obtain ⟨stack_eq, hframeidx⟩ := fieldAsgn_corollary_stack_eq hframe
  have hstack' : cfg'.stack = cfg.stack.dropLast ++
      [({ frame with objMap := frame.objMap.insert oid (obj.insert field (Reference.OId oid_y)) } : Frame)] := by
    rw [hcfg']
  have hobjAtC : (Reference.OId oid).objAt? cfg' = some (obj.insert field (Reference.OId oid_y)) := by
    unfold Reference.objAt?
    dsimp only
    rw [← hlocEq, hlocC]
    dsimp only
    rw [stackWithIndex_find_index_eq_getElem]
    have hget : cfg'.stackWithIndex[frame.index]? =
        (cfg'.stack[frame.index]?).map (fun f => ({ toFrame := f, index := frame.index } : FrameWithIndex)) := by
      unfold RuntimeConfig.stackWithIndex; rw [List.getElem?_mapIdx]
    rw [hget]
    have hget2 : cfg'.stack[frame.index]? =
        some ({ frame with objMap := frame.objMap.insert oid (obj.insert field (Reference.OId oid_y)) } : Frame) := by
      rw [hstack', hframeidx]; simp
    rw [hget2]
    simp only [Option.map_some]
    dsimp only [Option.bind]
    rw [AList.lookup_insert]
  have hobjAt : (Reference.OId oid).objAt? cfg = some obj := by
    unfold Reference.objAt?
    dsimp only
    rw [hlocC]
    dsimp only
    rw [stackWithIndex_find_index_eq_getElem]
    have hget : cfg.stackWithIndex[frame.index]? =
        (cfg.stack[frame.index]?).map (fun f => ({ toFrame := f, index := frame.index } : FrameWithIndex)) := by
      unfold RuntimeConfig.stackWithIndex; rw [List.getElem?_mapIdx]
    rw [hget]
    have hget2 : cfg.stack[frame.index]? = some frame.toFrame := by
      conv_lhs => rw [stack_eq, hframeidx]
      simp
    rw [hget2]
    simp only [Option.map_some]
    dsimp only [Option.bind]
    exact hobj
  rw [ReachableStep_oid_iff] at hstep
  obtain ⟨objC, hobjAtC2, hcontainsC⟩ := hstep
  rw [hobjAtC] at hobjAtC2
  injection hobjAtC2 with hobjAtCeq
  rw [← hobjAtCeq] at hcontainsC
  rcases fieldAsgn_corollary_object_insert_refs_mem (List.contains_iff_mem.mp hcontainsC) with heq | hmem
  · left; exact heq
  · right
    rw [ReachableStep_oid_iff]
    exact ⟨obj, hobjAt, List.contains_iff_mem.mpr hmem⟩

-- Mirrors `fieldAsgn_stack_oidC_step_of_ne_oidY` for the FIELD-ASGN-REGION branch.
theorem fieldAsgn_region_oidC_step_of_ne_oidY {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid oid oid_y : ObjectId} {region : Region} {obj : Object} {field : FieldName}
    (hregion : cfg.heap.lookup rid = some region)
    (hlocC : (Reference.OId oid).loc? cfg = some (Location.Rgn rid))
    (hobj : region.objMap.lookup oid = some obj)
    (hcfg' : cfg' = { cfg with heap := cfg.heap.insert rid ({ region with objMap := region.objMap.insert oid (obj.insert field (Reference.OId oid_y)) } : Region) })
    {c : Reference} (hstep : ReachableStep cfg' (Reference.OId oid) c) :
    c = Reference.OId oid_y ∨ ReachableStep cfg (Reference.OId oid) c := by
  have hlocEq : (Reference.OId oid).loc? cfg = (Reference.OId oid).loc? cfg' := by
    rw [hcfg']; exact fieldAsgn_corollary_region_loc_eq vcfg hregion hobj oid
  have hobjAtC : (Reference.OId oid).objAt? cfg' = some (obj.insert field (Reference.OId oid_y)) := by
    unfold Reference.objAt?
    dsimp only
    rw [← hlocEq, hlocC]
    dsimp only
    have hlookup' : cfg'.heap.lookup rid =
        some ({ region with objMap := region.objMap.insert oid (obj.insert field (Reference.OId oid_y)) } : Region) := by
      rw [hcfg']; dsimp only; rw [AList.lookup_insert]
    rw [hlookup']
    dsimp only [Option.bind]
    rw [AList.lookup_insert]
  have hobjAt : (Reference.OId oid).objAt? cfg = some obj := by
    unfold Reference.objAt?
    dsimp only
    rw [hlocC]
    dsimp only
    rw [hregion]
    dsimp only [Option.bind]
    exact hobj
  rw [ReachableStep_oid_iff] at hstep
  obtain ⟨objC, hobjAtC2, hcontainsC⟩ := hstep
  rw [hobjAtC] at hobjAtC2
  injection hobjAtC2 with hobjAtCeq
  rw [← hobjAtCeq] at hcontainsC
  rcases fieldAsgn_corollary_object_insert_refs_mem (List.contains_iff_mem.mp hcontainsC) with heq | hmem
  · left; exact heq
  · right
    rw [ReachableStep_oid_iff]
    exact ⟨obj, hobjAt, List.contains_iff_mem.mpr hmem⟩

-- H3 lifted along a chain rooted at any object confirmed inside region `rid` (generalizes `RegionReachable_oid_confined`'s bridge-only base case).
theorem reflTransGen_region_confined {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid : RegionId} {region : Region} (hlookup : cfg.heap.lookup rid = some region)
    {oidStart : ObjectId} (hlocStart : (Reference.OId oidStart).loc? cfg = some (Location.Rgn rid))
    {target : Reference} (hrtg : Relation.ReflTransGen (ReachableStep cfg) (Reference.OId oidStart) target) :
    (∃ oid ridCur region', target = Reference.OId oid ∧ (Reference.OId oid).loc? cfg = some (Location.Rgn ridCur) ∧
       cfg.heap.lookup ridCur = some region' ∧ (ridCur = rid ∨ region'.status = Status.Closed)) ∨
    (∃ ridR, target = Reference.RId ridR) := by
  induction hrtg with
  | refl => left; exact ⟨oidStart, rid, region, rfl, hlocStart, hlookup, Or.inl rfl⟩
  | tail hprev hstep ih =>
    rename_i b c
    have hmemrefs : ∃ ridCur region', c ∈ region'.refs ∧ cfg.heap.lookup ridCur = some region' ∧
        (ridCur = rid ∨ region'.status = Status.Closed) := by
      rcases ih with ⟨oidB, ridCur, region', heqB, hlocB, hlkB, hcaseB⟩ | ⟨ridB, heqB⟩
      · subst heqB
        rw [ReachableStep_oid_iff] at hstep
        obtain ⟨obj, hobjAt, hcontains⟩ := hstep
        unfold Reference.objAt? at hobjAt
        dsimp only at hobjAt
        rw [hlocB] at hobjAt
        dsimp only at hobjAt
        rw [hlkB] at hobjAt
        exact ⟨ridCur, region', mem_region_refs_of_mem_objMap hobjAt (List.contains_iff_mem.mp hcontains), hlkB, hcaseB⟩
      · subst heqB
        rw [ReachableStep_rid_iff] at hstep
        obtain ⟨regionR, hlkR, hclosedR, obj, hobjlookup, hcontains⟩ := hstep
        exact ⟨ridB, regionR, mem_region_refs_of_mem_objMap hobjlookup (List.contains_iff_mem.mp hcontains),
          hlkR, Or.inr hclosedR⟩
    obtain ⟨ridCur, region', hmemB, hlkCur, hcaseCur⟩ := hmemrefs
    cases c with
    | OId oidB =>
      left
      have hridEq := vcfg.h3 ridCur oidB region' hlkCur hmemB
      exact ⟨oidB, ridCur, region', rfl, hridEq, hlkCur, hcaseCur⟩
    | RId ridB => right; exact ⟨ridB, rfl⟩

-- A chain rooted inside Open region `rid` can never reach an object confirmed to live in a different Open region (mirrors `region_reachable_open_ne_absurd`).
theorem reflTransGen_region_open_ne_absurd {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid : RegionId} {region : Region} (hlookup : cfg.heap.lookup rid = some region)
    {oidStart : ObjectId} (hlocStart : (Reference.OId oidStart).loc? cfg = some (Location.Rgn rid))
    {oidTarget : ObjectId} {ridT : RegionId} {regionT : Region}
    (hlocT : (Reference.OId oidTarget).loc? cfg = some (Location.Rgn ridT))
    (hlkT : cfg.heap.lookup ridT = some regionT) (hopenT : regionT.status = Status.Open) (hne : ridT ≠ rid)
    (hrtg : Relation.ReflTransGen (ReachableStep cfg) (Reference.OId oidStart) (Reference.OId oidTarget)) : False := by
  rcases reflTransGen_region_confined vcfg hlookup hlocStart hrtg with
    ⟨oid', ridCur, region', heq, hloc', hlk', hcase'⟩ | ⟨ridR, heq⟩
  · rw [Reference.OId.injEq] at heq
    subst heq
    rw [hlocT, Option.some_inj, Location.Rgn.injEq] at hloc'
    subst hloc'
    rw [hlkT, Option.some_inj] at hlk'
    subst hlk'
    rcases hcase' with hcaseEq | hcaseClosed
    · exact hne hcaseEq
    · rw [hopenT] at hcaseClosed
      exact absurd hcaseClosed (by decide)
  · exact absurd heq (by simp)
