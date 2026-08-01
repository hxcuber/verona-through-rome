import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Mutation.Mutation
import Gc.Model.Preservation
import Gc.Reachability.Reachable.Semantics
import Gc.Reachability.Reachable.Basic
import Gc.Reachability.Reachable.Lemmas.Common
import Gc.Reachability.Reachable.Lemmas.VarAsgn
import Gc.Reachability.Reachable.Lemmas.FieldAsgn
import Gc.Reachability.Reachable.Lemmas.Merge

-- ===== swap =====

-- A chain from a bare `RId` (Closed region) can never reach an `OId` in a different Open region (first hop forces its own bridge object, via `reflTransGen_region_open_ne_absurd`).
theorem reflTransGen_rid_source_open_absurd {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid0 : RegionId} {oidTarget : ObjectId} {ridT : RegionId} {regionT : Region}
    (hlocT : (Reference.OId oidTarget).loc? cfg = some (Location.Rgn ridT))
    (hlkT : cfg.heap.lookup ridT = some regionT) (hopenT : regionT.status = Status.Open)
    (hrtg : Relation.ReflTransGen (ReachableStep cfg) (Reference.RId rid0) (Reference.OId oidTarget)) : False := by
  rcases hrtg.cases_head with heq | ⟨c, hstep, hrest⟩
  · exact absurd heq (by simp)
  · rw [ReachableStep_rid_iff] at hstep
    obtain ⟨region0, hregion0, hclosed0, hbeq⟩ := hstep
    have hbridgeMem : region0 ∈ cfg.heap.regions := by
      unfold Heap.regions
      exact List.mem_map_of_mem (AList.lookup_mem_entries hregion0)
    have hbridgeIn : region0.bridgeObjectId ∈ region0.objMap := vcfg.h1 region0 hbridgeMem
    have hlocBridge : (Reference.OId region0.bridgeObjectId).loc? cfg = some (Location.Rgn rid0) :=
      (oid_loc_rgn_iff_in_heap vcfg).mpr ⟨region0, hregion0, hbridgeIn⟩
    rw [hbeq] at hrest
    have hne : ridT ≠ rid0 := by
      intro heq
      rw [heq, hregion0] at hlkT
      injection hlkT with hlkTeq
      rw [← hlkTeq, hclosed0] at hopenT
      exact absurd hopenT (by decide)
    exact reflTransGen_region_open_ne_absurd vcfg hregion0 hlocBridge hlocT hlkT hopenT hne hrest

-- Heap `bridgeObjectId` transports across a region-objMap-only mutation (used for `FrameRoot`'s bridge disjunct, which never reads `objMap`).
theorem swap_region_heap_bridge_eq {cfg : RuntimeConfig} {rid : RegionId}
    {region newRegion : Region} (hregion : cfg.heap.lookup rid = some region)
    (hbv : newRegion.bridgeObjectId = region.bridgeObjectId) (rid0 : RegionId) :
    (cfg.heap.lookup rid0).map Region.bridgeObjectId =
      ((cfg.heap.insert rid newRegion).lookup rid0).map Region.bridgeObjectId := by
  by_cases hrideq : rid0 = rid
  · subst hrideq
    rw [hregion, AList.lookup_insert, Option.map_some, Option.map_some, hbv]
  · rw [AList.lookup_insert_ne hrideq]

-- A varMap-only change to the last frame never affects `objAt?` (mirrors `swap_corollary_stack_varmap_loc_eq`).
theorem swap_varmap_objAt_eq {cfg : RuntimeConfig} {frame : FrameWithIndex} {newVarMap : VarMap}
    (hframe : cfg.stackWithIndex.getLast? = some frame) (oid' : ObjectId) :
    (Reference.OId oid').objAt? cfg =
      (Reference.OId oid').objAt? { cfg with stack := cfg.stack.dropLast ++
        [({ frame with varMap := newVarMap } : Frame)] } := by
  have hlocEq := swap_corollary_stack_varmap_loc_eq (frame := frame) (newVarMap := newVarMap) hframe oid'
  set newFrame : Frame := { frame with varMap := newVarMap } with newFrame_def
  set cfg2 : RuntimeConfig := { cfg with stack := cfg.stack.dropLast ++ [newFrame] } with cfg2_def
  cases hloc : (Reference.OId oid').loc? cfg with
  | none =>
    unfold Reference.objAt?
    dsimp only
    rw [hloc, ← hlocEq, hloc]
  | some loc =>
    have hloc2 : (Reference.OId oid').loc? cfg2 = some loc := by rw [← hlocEq]; exact hloc
    cases loc with
    | Rgn rid0 =>
      unfold Reference.objAt?
      dsimp only
      rw [hloc, hloc2]
    | Stk fid0 =>
      obtain ⟨stack_eq, hidxeq⟩ := swap_corollary_stack_eq hframe
      have hframe_mem : frame ∈ cfg.stackWithIndex := List.mem_of_getLast? hframe
      have hL : cfg.stackWithIndex =
          cfg.stack.dropLast.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) ++ [frame] := by
        unfold RuntimeConfig.stackWithIndex
        conv_lhs => rw [stack_eq]
        rw [List.mapIdx_concat, ← hidxeq]
      have hR : cfg2.stackWithIndex =
          cfg.stack.dropLast.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) ++
            [({ newFrame with index := frame.index } : FrameWithIndex)] := by
        rw [cfg2_def]
        unfold RuntimeConfig.stackWithIndex
        dsimp only
        rw [List.mapIdx_concat, ← hidxeq]
      unfold Reference.objAt?
      dsimp only
      rw [hloc, hloc2]
      dsimp only
      by_cases hfid : fid0 = frame.index
      · have hfindL : cfg.stackWithIndex.find? (fun f => f.index == fid0) = some frame := by
          rw [hfid]; exact swap_corollary_stackWithIndex_find_eq hframe_mem
        have hnewFrame_mem : ({ newFrame with index := frame.index } : FrameWithIndex) ∈ cfg2.stackWithIndex := by
          rw [hR]; exact List.mem_append_right _ (List.mem_singleton_self _)
        have hfindR : cfg2.stackWithIndex.find? (fun f => f.index == fid0) =
            some ({ newFrame with index := frame.index } : FrameWithIndex) := by
          rw [hfid]; exact swap_corollary_stackWithIndex_find_eq hnewFrame_mem
        rw [hfindL, hfindR]
        rfl
      · have hnotp : ∀ frR : FrameWithIndex, frR.index = frame.index → (frR.index == fid0) = false := by
          intro frR hfrR
          rw [Bool.eq_false_iff, Ne, beq_iff_eq, hfrR]
          exact fun heq => hfid heq.symm
        have hfindEq : cfg.stackWithIndex.find? (fun f => f.index == fid0) =
            cfg2.stackWithIndex.find? (fun f => f.index == fid0) := by
          rw [hL, hR, List.find?_append, List.find?_append]
          have hLnone : List.find? (fun f => f.index == fid0) [frame] = none := by
            simp only [List.find?_cons, List.find?_nil]
            rw [hnotp frame rfl]
          have hRnone : List.find? (fun f => f.index == fid0)
              [({ newFrame with index := frame.index } : FrameWithIndex)] = none := by
            simp only [List.find?_cons, List.find?_nil]
            rw [hnotp _ rfl]
          rw [hLnone, hRnone]
        rw [hfindEq]

-- The mutated container's new content on REGION branches, generalized over `newBridge` to also cover SWAP-REGION-BRIDGE's simultaneous bridge change.
theorem swap_region_objAt_mutated {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid yoid : ObjectId} {region : Region} {obj : Object} {field : FieldName} {newVal : Reference}
    {newBridge : ObjectId}
    (hregion : cfg.heap.lookup rid = some region) (hobj : region.objMap.lookup yoid = some obj)
    (hlocm : (Reference.OId yoid).loc? cfg = some (Location.Rgn rid))
    (hcfg' : cfg' = { cfg with heap := cfg.heap.insert rid ({ region with bridgeObjectId := newBridge, objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) }) :
    (Reference.OId yoid).objAt? cfg' = some (obj.insert field newVal) := by
  set newRegion : Region :=
    { region with bridgeObjectId := newBridge, objMap := region.objMap.insert yoid (obj.insert field newVal) }
    with newRegion_def
  have hlocEq := swap_corollary_region_loc_eq (rid := rid) (yoid := yoid) (region := region)
    (newRegion := newRegion) (obj := obj) (v := obj.insert field newVal) vcfg hregion hobj
    (by rw [newRegion_def]) yoid
  rw [← hcfg'] at hlocEq
  rw [hlocEq] at hlocm
  unfold Reference.objAt?
  dsimp only
  rw [hlocm]
  dsimp only
  have hlookup2 : cfg'.heap.lookup rid = some newRegion := by
    rw [hcfg']
    exact AList.lookup_insert (a := rid) (b := newRegion) cfg.heap
  rw [hlookup2, newRegion_def]
  exact AList.lookup_insert (a := yoid) (b := obj.insert field newVal) region.objMap

-- REGION-touching branches: for any oid' *other* than the mutated container, `objAt?` is unaffected.
theorem swap_region_objAt_eq_of_ne {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid yoid : ObjectId} {region : Region} {obj : Object} {field : FieldName} {newVal : Reference}
    {newBridge : ObjectId}
    (hregion : cfg.heap.lookup rid = some region) (hobj : region.objMap.lookup yoid = some obj)
    {oid' : ObjectId} (hne : oid' ≠ yoid) :
    (Reference.OId oid').objAt? cfg =
      (Reference.OId oid').objAt? ({ cfg with heap := cfg.heap.insert rid ({ region with bridgeObjectId := newBridge, objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) }) := by
  have hlocEq := swap_corollary_region_loc_eq (rid := rid) (yoid := yoid) (region := region)
    (newRegion := { region with bridgeObjectId := newBridge, objMap := region.objMap.insert yoid (obj.insert field newVal) })
    (obj := obj) (v := obj.insert field newVal) vcfg hregion hobj rfl oid'
  set newRegion : Region :=
    { region with bridgeObjectId := newBridge, objMap := region.objMap.insert yoid (obj.insert field newVal) }
    with newRegion_def
  set cfg2 : RuntimeConfig := { cfg with heap := cfg.heap.insert rid newRegion } with cfg2_def
  cases hloc : (Reference.OId oid').loc? cfg with
  | none =>
    unfold Reference.objAt?
    dsimp only
    rw [hloc, ← hlocEq, hloc]
  | some loc =>
    have hloc2 : (Reference.OId oid').loc? cfg2 = some loc := by rw [← hlocEq]; exact hloc
    cases loc with
    | Stk fid0 =>
      have hswi_eq : cfg2.stackWithIndex = cfg.stackWithIndex := by
        unfold RuntimeConfig.stackWithIndex
        congr 1
      unfold Reference.objAt?
      dsimp only
      rw [hloc, hloc2, hswi_eq]
    | Rgn rid0 =>
      unfold Reference.objAt?
      dsimp only
      rw [hloc, hloc2]
      dsimp only
      by_cases hrideq : rid0 = rid
      · subst hrideq
        have hlookup2 : cfg2.heap.lookup rid0 = some newRegion := by
          rw [cfg2_def]; exact AList.lookup_insert (a := rid0) (b := newRegion) cfg.heap
        rw [hregion, hlookup2, newRegion_def]
        exact (AList.lookup_insert_ne hne).symm
      · have hlookup2 : cfg2.heap.lookup rid0 = cfg.heap.lookup rid0 := by
          rw [cfg2_def]; exact AList.lookup_insert_ne hrideq
        rw [hlookup2]

-- Composes the region `objMap` change with the simultaneous (but `objMap`-irrelevant) stack `varMap` change.
theorem swap_region_stack_loc_eq {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid yoid : ObjectId} {region : Region} {obj : Object} {field : FieldName} {newVal : Reference}
    {frame0 : FrameWithIndex} {newVarMap : VarMap}
    (hframe0 : cfg.stackWithIndex.getLast? = some frame0)
    (hregion : cfg.heap.lookup rid = some region) (hobj : region.objMap.lookup yoid = some obj)
    (oid' : ObjectId) :
    (Reference.OId oid').loc? cfg =
      (Reference.OId oid').loc? ({ stack := cfg.stack.dropLast ++ [({ frame0 with varMap := newVarMap } : Frame)], heap := cfg.heap.insert rid ({ region with objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) } : RuntimeConfig) := by
  have step1 := swap_corollary_region_loc_eq (rid := rid) (yoid := yoid) (region := region)
    (newRegion := { region with objMap := region.objMap.insert yoid (obj.insert field newVal) })
    (obj := obj) (v := obj.insert field newVal) vcfg hregion hobj rfl oid'
  have hframe0' : ({ cfg with heap := cfg.heap.insert rid ({ region with objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) } : RuntimeConfig).stackWithIndex.getLast? = some frame0 :=
    hframe0
  have step2 := swap_corollary_stack_varmap_loc_eq
    (cfg := { cfg with heap := cfg.heap.insert rid ({ region with objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) })
    (frame := frame0) (newVarMap := newVarMap) hframe0' oid'
  exact step1.trans step2

-- `objAt?` analogue of `swap_region_stack_loc_eq`, for oid' *other* than the mutated container.
theorem swap_region_stack_objAt_eq_of_ne {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid yoid : ObjectId} {region : Region} {obj : Object} {field : FieldName} {newVal : Reference}
    {frame0 : FrameWithIndex} {newVarMap : VarMap}
    (hframe0 : cfg.stackWithIndex.getLast? = some frame0)
    (hregion : cfg.heap.lookup rid = some region) (hobj : region.objMap.lookup yoid = some obj)
    {oid' : ObjectId} (hne : oid' ≠ yoid) :
    (Reference.OId oid').objAt? cfg =
      (Reference.OId oid').objAt? ({ stack := cfg.stack.dropLast ++ [({ frame0 with varMap := newVarMap } : Frame)], heap := cfg.heap.insert rid ({ region with objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) } : RuntimeConfig) := by
  have step1 := swap_region_objAt_eq_of_ne vcfg (rid := rid) (yoid := yoid) (region := region)
    (obj := obj) (field := field) (newVal := newVal) (newBridge := region.bridgeObjectId) hregion hobj hne
  have hframe0' : ({ cfg with heap := cfg.heap.insert rid ({ region with objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) } : RuntimeConfig).stackWithIndex.getLast? = some frame0 :=
    hframe0
  have step2 := swap_varmap_objAt_eq
    (cfg := { cfg with heap := cfg.heap.insert rid ({ region with objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) })
    (frame := frame0) (newVarMap := newVarMap) hframe0' oid'
  exact step1.trans step2

-- The mutated container's own new content combined with the simultaneous stack varMap change.
theorem swap_region_stack_objAt_mutated {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid yoid : ObjectId} {region : Region} {obj : Object} {field : FieldName} {newVal : Reference}
    {frame0 : FrameWithIndex} {newVarMap : VarMap}
    (hframe0 : cfg.stackWithIndex.getLast? = some frame0)
    (hregion : cfg.heap.lookup rid = some region) (hobj : region.objMap.lookup yoid = some obj)
    (hlocm : (Reference.OId yoid).loc? cfg = some (Location.Rgn rid)) :
    (Reference.OId yoid).objAt? ({ stack := cfg.stack.dropLast ++ [({ frame0 with varMap := newVarMap } : Frame)], heap := cfg.heap.insert rid ({ region with objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) } : RuntimeConfig) =
      some (obj.insert field newVal) := by
  have hstep : (Reference.OId yoid).objAt? ({ cfg with heap := cfg.heap.insert rid ({ region with objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) } : RuntimeConfig) = some (obj.insert field newVal) :=
    swap_region_objAt_mutated vcfg (newBridge := region.bridgeObjectId) hregion hobj hlocm rfl
  have hframe0' : ({ cfg with heap := cfg.heap.insert rid ({ region with objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) } : RuntimeConfig).stackWithIndex.getLast? = some frame0 :=
    hframe0
  have step2 := swap_varmap_objAt_eq
    (cfg := { cfg with heap := cfg.heap.insert rid ({ region with objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) })
    (frame := frame0) (newVarMap := newVarMap) hframe0' yoid
  rw [← step2]; exact hstep

-- swap's stack-mutating branches all replace the last frame via `{ frame with varMap := ..., objMap := ... }`, so `regionId`/`bridgeVar` are unchanged; packages the shared index-case-split.
theorem swap_stack_shape_eq_of_last_update
    {cfg cfg' : RuntimeConfig} {frame : FrameWithIndex} (newFrame : Frame)
    (hframe : cfg.stackWithIndex.getLast? = some frame)
    (hstack' : cfg'.stack = cfg.stack.dropLast ++ [newFrame])
    (hrid : newFrame.regionId = frame.regionId) (hbv : newFrame.bridgeVar = frame.bridgeVar)
    (n : ℕ) :
    (cfg.stack[n]?).map (fun f => (f.regionId, f.bridgeVar)) =
    (cfg'.stack[n]?).map (fun f => (f.regionId, f.bridgeVar)) := by
  obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
  by_cases hlp : n = cfg.stack.dropLast.length
  · have e1 : cfg.stack[n]? = some frame.toFrame := by conv_lhs => rw [stack_eq, hlp]; simp
    have e2 : cfg'.stack[n]? = some newFrame := by rw [hstack', hlp]; simp
    rw [e1, e2]
    simp [hrid, hbv]
  · by_cases hlt : n < cfg.stack.dropLast.length
    · have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
        conv_lhs => rw [stack_eq]
        rw [List.getElem?_append_left hlt]
      have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
        rw [hstack', List.getElem?_append_left hlt]
      rw [e1, e2]
    · have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq]; simp
      have hlen' : cfg'.stack.length = cfg.stack.dropLast.length + 1 := by rw [hstack']; simp
      have e1 : cfg.stack[n]? = none := List.getElem?_eq_none (by omega)
      have e2 : cfg'.stack[n]? = none := List.getElem?_eq_none (by omega)
      rw [e1, e2]

-- swap never touches a frame's `regionId`/`bridgeVar` anywhere.
theorem swap_stack_shape_eq (h : swap x yf cfg = some cfg') (n : ℕ) :
    (cfg.stack[n]?).map (fun f => (f.regionId, f.bridgeVar)) =
    (cfg'.stack[n]?).map (fun f => (f.regionId, f.bridgeVar)) := by
  obtain ⟨frame, hframe, yRef, hyr, yRefLoc, hyrl, yfRef, hyf, yfRefLoc, hyfl, hcase⟩ := swap_cases h
  rcases hcase with
    ⟨yoid, xRef, obj, hxb, hyoid, hyrloc, hxr, hobj, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xoid, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hxrl, hxrid, hstatus, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hstatus, hcfg'⟩ |
    ⟨yoid, yrid, yfoid, yfrid, region, obj, hxb, hyoid, hyrloc, hyfoid, hyfrloc, hyrid, hyfrid, hregion, hobj, hcfg'⟩
  · exact swap_stack_shape_eq_of_last_update
      { frame with varMap := frame.varMap.insert x yfRef, objMap := frame.objMap.insert yoid (obj.insert yf.field xRef) }
      hframe (by rw [hcfg']) rfl rfl n
  · exact swap_stack_shape_eq_of_last_update
      { frame with varMap := frame.varMap.insert x yfRef } hframe (by rw [hcfg']) rfl rfl n
  · exact swap_stack_shape_eq_of_last_update
      { frame with varMap := frame.varMap.insert x yfRef } hframe (by rw [hcfg']) rfl rfl n
  · rw [hcfg']

-- Frame membership in `cfg'.stackWithIndex` transports down to `cfg`, same index/regionId/bridgeVar.
theorem swap_frame_transport_down (h : swap x yf cfg = some cfg')
    (fr : FrameWithIndex) (hfr : fr ∈ cfg'.stackWithIndex) :
    ∃ fr0 : FrameWithIndex, fr0 ∈ cfg.stackWithIndex ∧ fr0.index = fr.index ∧
      fr0.regionId = fr.regionId ∧ fr0.bridgeVar = fr.bridgeVar := by
  obtain ⟨fr0, hmem, hidx, hproj⟩ :=
    stackWithIndex_frame_transport_down_of_shape_eq (proj := fun f => (f.regionId, f.bridgeVar))
      (swap_stack_shape_eq h) fr hfr
  injection hproj with hrid hbv
  exact ⟨fr0, hmem, hidx, hrid, hbv⟩

-- Mirrors `swap_frame_transport_down`, transporting membership the other way.
theorem swap_frame_transport_up (h : swap x yf cfg = some cfg')
    (fr : FrameWithIndex) (hfr : fr ∈ cfg.stackWithIndex) :
    ∃ fr0 : FrameWithIndex, fr0 ∈ cfg'.stackWithIndex ∧ fr0.index = fr.index ∧
      fr0.regionId = fr.regionId ∧ fr0.bridgeVar = fr.bridgeVar := by
  obtain ⟨fr0, hmem, hidx, hproj⟩ :=
    stackWithIndex_frame_transport_up_of_shape_eq (proj := fun f => (f.regionId, f.bridgeVar))
      (swap_stack_shape_eq h) fr hfr
  injection hproj with hrid hbv
  exact ⟨fr0, hmem, hidx, hrid, hbv⟩

-- The mutated container's own new content on the STACK branch.
theorem swap_stack_objAt_mutated {cfg cfg' : RuntimeConfig} {frame0 : FrameWithIndex}
    {yoid : ObjectId} {obj : Object} {field : FieldName} {newVal : Reference} {newVarMap : VarMap}
    (hframe0 : cfg.stackWithIndex.getLast? = some frame0) (hobjm : frame0.objMap.lookup yoid = some obj)
    (hlocm : (Reference.OId yoid).loc? cfg = some (Location.Stk frame0.index))
    (hcfg' : cfg' = { cfg with stack := cfg.stack.dropLast ++
      [({ frame0 with varMap := newVarMap, objMap := frame0.objMap.insert yoid (obj.insert field newVal) } :
        Frame)] }) :
    (Reference.OId yoid).objAt? cfg' = some (obj.insert field newVal) := by
  set newFrame : Frame :=
    { frame0 with varMap := newVarMap, objMap := frame0.objMap.insert yoid (obj.insert field newVal) }
    with newFrame_def
  have hlocEqM := swap_corollary_stack_loc_eq (field := field) (newVal := newVal) (newVarMap := newVarMap)
    hframe0 hobjm yoid
  rw [← hcfg'] at hlocEqM
  rw [hlocEqM] at hlocm
  unfold Reference.objAt?
  dsimp only
  rw [hlocm]
  dsimp only
  have hnewFrame_mem : ({ newFrame with index := frame0.index } : FrameWithIndex) ∈ cfg'.stackWithIndex := by
    rw [hcfg']
    unfold RuntimeConfig.stackWithIndex
    dsimp only
    obtain ⟨stack_eq, hidxeq⟩ := swap_corollary_stack_eq hframe0
    rw [List.mapIdx_concat, ← hidxeq]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  rw [swap_corollary_stackWithIndex_find_eq hnewFrame_mem]
  rw [newFrame_def]
  exact AList.lookup_insert (a := yoid) (b := obj.insert field newVal) frame0.objMap

-- STACK branch: for any oid' *other* than the mutated container, `objAt?` is unaffected.
theorem swap_stack_objAt_eq_of_ne {cfg : RuntimeConfig} {frame0 : FrameWithIndex}
    {yoid : ObjectId} {obj : Object} {field : FieldName} {newVal : Reference} {newVarMap : VarMap}
    (hframe0 : cfg.stackWithIndex.getLast? = some frame0) (hobj : frame0.objMap.lookup yoid = some obj)
    {oid' : ObjectId} (hne : oid' ≠ yoid) :
    (Reference.OId oid').objAt? cfg =
      (Reference.OId oid').objAt? { cfg with stack := cfg.stack.dropLast ++
        [({ frame0 with varMap := newVarMap, objMap := frame0.objMap.insert yoid (obj.insert field newVal) } :
          Frame)] } := by
  have hlocEq := swap_corollary_stack_loc_eq (field := field) (newVal := newVal) (newVarMap := newVarMap)
    hframe0 hobj oid'
  set newFrame : Frame :=
    { frame0 with varMap := newVarMap, objMap := frame0.objMap.insert yoid (obj.insert field newVal) }
    with newFrame_def
  set cfg2 : RuntimeConfig := { cfg with stack := cfg.stack.dropLast ++ [newFrame] } with cfg2_def
  cases hloc : (Reference.OId oid').loc? cfg with
  | none =>
    unfold Reference.objAt?
    dsimp only
    rw [hloc, ← hlocEq, hloc]
  | some loc =>
    have hloc2 : (Reference.OId oid').loc? cfg2 = some loc := by rw [← hlocEq]; exact hloc
    cases loc with
    | Rgn rid0 =>
      unfold Reference.objAt?
      dsimp only
      rw [hloc, hloc2]
    | Stk fid0 =>
      obtain ⟨stack_eq, hidxeq⟩ := swap_corollary_stack_eq hframe0
      have hframe0_mem : frame0 ∈ cfg.stackWithIndex := List.mem_of_getLast? hframe0
      have hL : cfg.stackWithIndex =
          cfg.stack.dropLast.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) ++ [frame0] := by
        unfold RuntimeConfig.stackWithIndex
        conv_lhs => rw [stack_eq]
        rw [List.mapIdx_concat, ← hidxeq]
      have hR : cfg2.stackWithIndex =
          cfg.stack.dropLast.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) ++
            [({ newFrame with index := frame0.index } : FrameWithIndex)] := by
        rw [cfg2_def]
        unfold RuntimeConfig.stackWithIndex
        dsimp only
        rw [List.mapIdx_concat, ← hidxeq]
      unfold Reference.objAt?
      dsimp only
      rw [hloc, hloc2]
      dsimp only
      by_cases hfid : fid0 = frame0.index
      · have hfindL : cfg.stackWithIndex.find? (fun f => f.index == fid0) = some frame0 := by
          rw [hfid]; exact swap_corollary_stackWithIndex_find_eq hframe0_mem
        have hnewFrame_mem : ({ newFrame with index := frame0.index } : FrameWithIndex) ∈ cfg2.stackWithIndex := by
          rw [hR]; exact List.mem_append_right _ (List.mem_singleton_self _)
        have hfindR : cfg2.stackWithIndex.find? (fun f => f.index == fid0) =
            some ({ newFrame with index := frame0.index } : FrameWithIndex) := by
          rw [hfid]; exact swap_corollary_stackWithIndex_find_eq hnewFrame_mem
        rw [hfindL, hfindR]
        rw [newFrame_def]
        exact (AList.lookup_insert_ne hne).symm
      · have hnotp : ∀ frR : FrameWithIndex, frR.index = frame0.index → (frR.index == fid0) = false := by
          intro frR hfrR
          rw [Bool.eq_false_iff, Ne, beq_iff_eq, hfrR]
          exact fun heq => hfid heq.symm
        have hfindEq : cfg.stackWithIndex.find? (fun f => f.index == fid0) =
            cfg2.stackWithIndex.find? (fun f => f.index == fid0) := by
          rw [hL, hR, List.find?_append, List.find?_append]
          have hLnone : List.find? (fun f => f.index == fid0) [frame0] = none := by
            simp only [List.find?_cons, List.find?_nil]
            rw [hnotp frame0 rfl]
          have hRnone : List.find? (fun f => f.index == fid0)
              [({ newFrame with index := frame0.index } : FrameWithIndex)] = none := by
            simp only [List.find?_cons, List.find?_nil]
            rw [hnotp _ rfl]
          rw [hLnone, hRnone]
        rw [hfindEq]

-- `FrameReachable` is unaffected below the mutated frame across all four branches: a suspended chain can never reach `yoid` (owner-index bound), so no escape machinery is needed.
theorem swap_frame_reachable_iff_of_lt {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg) (vcfg' : ValidConfig cfg')
    (h : swap x yf cfg = some cfg')
    (frame : FrameWithIndex) (hlt : frame.index < cfg.stack.dropLast.length) (ref : Reference) :
    FrameReachable cfg frame.index ref ↔ FrameReachable cfg' frame.index ref := by
  obtain ⟨frame0, hframe0, yRef, hyr, yRefLoc, hyrl, yfRef, hyf, yfRefLoc, hyfl, hcase⟩ := swap_cases h
  have hframe0_mem : frame0 ∈ cfg.stackWithIndex := List.mem_of_getLast? hframe0
  obtain ⟨stack_eq0, hidx00⟩ := swap_corollary_stack_eq hframe0
  have hltd : frame.index < frame0.index := by rw [hidx00]; exact hlt
  rw [FrameReachable_iff_reflTransGen, FrameReachable_iff_reflTransGen]
  rcases hcase with
    ⟨yoid, xRef, obj, hxb, hyoid, hyrloc, hxr, hobj, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xoid, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hxrl, hxridEq, hstatus, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hstatus, hcfg'⟩ |
    ⟨yoid, yrid, yfoid, yfrid, region, obj, hxb, hyoid, hyrloc, hyfoid, hyfrloc, hyridEq, hyfridEq, hregion, hobj,
      hcfg'⟩
  · -- SWAP-STACK
    have hyloc0 : (Reference.OId yoid).loc? cfg = some (Location.Stk frame0.index) := by
      rw [← hyoid, ← hyrloc]; exact hyrl
    have frame_transport_down : ∀ fr : FrameWithIndex, fr ∈ cfg'.stackWithIndex →
        fr.index < cfg.stack.dropLast.length → fr ∈ cfg.stackWithIndex := by
      intro fr hfr hltfr
      obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr
      have hidx_n : fr.index = n := by rw [← hfeq]
      have hltn : n < cfg.stack.dropLast.length := by rw [← hidx_n]; exact hltfr
      have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
        conv_lhs => rw [stack_eq0]; rw [List.getElem?_append_left hltn]
      have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
        rw [hcfg']; dsimp only; rw [List.getElem?_append_left hltn]
      have hfr_get? : cfg'.stack[n]? = some fr.toFrame := by
        rw [show fr.toFrame = cfg'.stack[n] from by rw [← hfeq]]
        exact List.getElem?_eq_getElem hn
      have hcfgn : cfg.stack[n]? = some fr.toFrame := by rw [e1, ← e2, hfr_get?]
      obtain ⟨h1, heq⟩ := List.getElem?_eq_some_iff.mp hcfgn
      unfold RuntimeConfig.stackWithIndex
      exact List.mem_mapIdx.mpr ⟨n, h1, by rw [heq, ← hidx_n]⟩
    have frame_transport_up : ∀ fr : FrameWithIndex, fr ∈ cfg.stackWithIndex →
        fr.index < cfg.stack.dropLast.length → fr ∈ cfg'.stackWithIndex := by
      intro fr hfr hltfr
      obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr
      have hidx_n : fr.index = n := by rw [← hfeq]
      have hltn : n < cfg.stack.dropLast.length := by rw [← hidx_n]; exact hltfr
      have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
        conv_lhs => rw [stack_eq0]; rw [List.getElem?_append_left hltn]
      have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
        rw [hcfg']; dsimp only; rw [List.getElem?_append_left hltn]
      have hfr_get? : cfg.stack[n]? = some fr.toFrame := by
        rw [show fr.toFrame = cfg.stack[n] from by rw [← hfeq]]
        exact List.getElem?_eq_getElem hn
      have hcfg'n : cfg'.stack[n]? = some fr.toFrame := by rw [e2, ← e1, hfr_get?]
      obtain ⟨h1, heq⟩ := List.getElem?_eq_some_iff.mp hcfg'n
      unfold RuntimeConfig.stackWithIndex
      exact List.mem_mapIdx.mpr ⟨n, h1, by rw [heq, ← hidx_n]⟩
    have hheap_eq : cfg'.heap = cfg.heap := by rw [hcfg']
    have hfrRootIff : ∀ start, FrameRoot cfg frame.index start ↔ FrameRoot cfg' frame.index start := by
      intro start
      unfold FrameRoot
      constructor
      · rintro (⟨fr, hfr, hidx, var, hlookup⟩ | ⟨fr, hfr, hidx, region1, hlookup, hstart⟩)
        · exact Or.inl ⟨fr, frame_transport_up fr hfr (hidx ▸ hlt), hidx, var, hlookup⟩
        · exact Or.inr ⟨fr, frame_transport_up fr hfr (hidx ▸ hlt), hidx, region1, by rw [hheap_eq]; exact hlookup, hstart⟩
      · rintro (⟨fr, hfr, hidx, var, hlookup⟩ | ⟨fr, hfr, hidx, region1, hlookup, hstart⟩)
        · exact Or.inl ⟨fr, frame_transport_down fr hfr (hidx ▸ hlt), hidx, var, hlookup⟩
        · exact Or.inr ⟨fr, frame_transport_down fr hfr (hidx ▸ hlt), hidx, region1, by rw [← hheap_eq]; exact hlookup, hstart⟩
    have hoidm_ne : ∀ oidx, FrameReachable cfg frame.index (Reference.OId oidx) → oidx ≠ yoid := by
      intro oidx hreachx heq
      rw [heq] at hreachx
      have := stack_container_confined vcfg hyloc0 hreachx
      exact absurd this (Nat.not_le.mpr hltd)
    have hoidm_ne' : ∀ oidx, FrameReachable cfg' frame.index (Reference.OId oidx) → oidx ≠ yoid := by
      intro oidx hreachx heq
      rw [heq] at hreachx
      have hyloc0' : (Reference.OId yoid).loc? cfg' = some (Location.Stk frame0.index) := by
        have e := swap_corollary_stack_loc_eq (field := yf.field) (newVal := xRef)
          (newVarMap := frame0.varMap.insert x yfRef) hframe0 hobj yoid
        rw [← hcfg'] at e; rw [← e]; exact hyloc0
      have := stack_container_confined vcfg' hyloc0' hreachx
      exact absurd this (Nat.not_le.mpr hltd)
    have hobjAtEq : ∀ oid', oid' ≠ yoid →
        (Reference.OId oid').objAt? cfg = (Reference.OId oid').objAt? cfg' := by
      intro oid' hne
      have e := swap_stack_objAt_eq_of_ne (yoid := yoid) (obj := obj) (field := yf.field)
        (newVal := xRef) (newVarMap := frame0.varMap.insert x yfRef) (oid' := oid') hframe0 hobj hne
      rw [← hcfg'] at e; exact e
    have hridstepIff : ∀ rid0 b, ReachableStep cfg (Reference.RId rid0) b ↔ ReachableStep cfg' (Reference.RId rid0) b := by
      intro rid0 b
      rw [ReachableStep_rid_iff, ReachableStep_rid_iff, hheap_eq]
    constructor
    · rintro ⟨start, hroot, hrtg⟩
      have main_up : ∀ target : Reference, Relation.ReflTransGen (ReachableStep cfg) start target →
          FrameReachable cfg frame.index target ∧ Relation.ReflTransGen (ReachableStep cfg') start target := by
        intro target htrg
        induction htrg with
        | refl =>
          exact ⟨(FrameReachable_iff_reflTransGen cfg frame.index start).mpr
            ⟨start, hroot, Relation.ReflTransGen.refl⟩, Relation.ReflTransGen.refl⟩
        | tail hprev hstep ih =>
          rename_i p c
          obtain ⟨ihreach, ihrtg⟩ := ih
          cases p with
          | RId rid0 => exact ⟨FrameReachable.step hstep ihreach, ihrtg.tail ((hridstepIff rid0 c).mp hstep)⟩
          | OId oidb =>
            have hbne : oidb ≠ yoid := hoidm_ne oidb ihreach
            have heqB := hobjAtEq oidb hbne
            obtain ⟨objv, hobjAt, hcontains⟩ := (ReachableStep_oid_iff cfg oidb c).mp hstep
            exact ⟨FrameReachable.step hstep ihreach,
              ihrtg.tail ((ReachableStep_oid_iff cfg' oidb c).mpr ⟨objv, by rw [← heqB]; exact hobjAt, hcontains⟩)⟩
      obtain ⟨_, hup⟩ := main_up ref hrtg
      exact ⟨start, (hfrRootIff start).mp hroot, hup⟩
    · rintro ⟨start, hroot, hrtg⟩
      have hroot_down := (hfrRootIff start).mpr hroot
      have main_down : ∀ target : Reference, Relation.ReflTransGen (ReachableStep cfg') start target →
          FrameReachable cfg' frame.index target ∧ Relation.ReflTransGen (ReachableStep cfg) start target := by
        intro target htrg
        induction htrg with
        | refl =>
          exact ⟨(FrameReachable_iff_reflTransGen cfg' frame.index start).mpr
            ⟨start, hroot, Relation.ReflTransGen.refl⟩, Relation.ReflTransGen.refl⟩
        | tail hprev hstep ih =>
          rename_i p c
          obtain ⟨ihreach, ihrtg⟩ := ih
          cases p with
          | RId rid0 => exact ⟨FrameReachable.step hstep ihreach, ihrtg.tail ((hridstepIff rid0 c).mpr hstep)⟩
          | OId oidb =>
            have hbne : oidb ≠ yoid := hoidm_ne' oidb ihreach
            have heqB := hobjAtEq oidb hbne
            obtain ⟨objv, hobjAt, hcontains⟩ := (ReachableStep_oid_iff cfg' oidb c).mp hstep
            exact ⟨FrameReachable.step hstep ihreach,
              ihrtg.tail ((ReachableStep_oid_iff cfg oidb c).mpr ⟨objv, by rw [heqB]; exact hobjAt, hcontains⟩)⟩
      obtain ⟨_, hdown⟩ := main_down ref hrtg
      exact ⟨start, hroot_down, hdown⟩
  · -- SWAP-REGION-OBJECT
    have hyloc0 : (Reference.OId yoid).loc? cfg = some (Location.Rgn rid) := by
      rw [← hyoid, ← hyrloc]; exact hyrl
    have frame_transport_down : ∀ fr : FrameWithIndex, fr ∈ cfg'.stackWithIndex →
        fr.index < cfg.stack.dropLast.length → fr ∈ cfg.stackWithIndex := by
      intro fr hfr hltfr
      obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr
      have hidx_n : fr.index = n := by rw [← hfeq]
      have hltn : n < cfg.stack.dropLast.length := by rw [← hidx_n]; exact hltfr
      have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
        conv_lhs => rw [stack_eq0]; rw [List.getElem?_append_left hltn]
      have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
        rw [hcfg']; dsimp only; rw [List.getElem?_append_left hltn]
      have hfr_get? : cfg'.stack[n]? = some fr.toFrame := by
        rw [show fr.toFrame = cfg'.stack[n] from by rw [← hfeq]]
        exact List.getElem?_eq_getElem hn
      have hcfgn : cfg.stack[n]? = some fr.toFrame := by rw [e1, ← e2, hfr_get?]
      obtain ⟨h1, heq⟩ := List.getElem?_eq_some_iff.mp hcfgn
      unfold RuntimeConfig.stackWithIndex
      exact List.mem_mapIdx.mpr ⟨n, h1, by rw [heq, ← hidx_n]⟩
    have frame_transport_up : ∀ fr : FrameWithIndex, fr ∈ cfg.stackWithIndex →
        fr.index < cfg.stack.dropLast.length → fr ∈ cfg'.stackWithIndex := by
      intro fr hfr hltfr
      obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr
      have hidx_n : fr.index = n := by rw [← hfeq]
      have hltn : n < cfg.stack.dropLast.length := by rw [← hidx_n]; exact hltfr
      have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
        conv_lhs => rw [stack_eq0]; rw [List.getElem?_append_left hltn]
      have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
        rw [hcfg']; dsimp only; rw [List.getElem?_append_left hltn]
      have hfr_get? : cfg.stack[n]? = some fr.toFrame := by
        rw [show fr.toFrame = cfg.stack[n] from by rw [← hfeq]]
        exact List.getElem?_eq_getElem hn
      have hcfg'n : cfg'.stack[n]? = some fr.toFrame := by rw [e2, ← e1, hfr_get?]
      obtain ⟨h1, heq⟩ := List.getElem?_eq_some_iff.mp hcfg'n
      unfold RuntimeConfig.stackWithIndex
      exact List.mem_mapIdx.mpr ⟨n, h1, by rw [heq, ← hidx_n]⟩
    have hridne : ∀ fr : FrameWithIndex, fr ∈ cfg.stackWithIndex → fr.index < frame0.index →
        fr.regionId ≠ rid := by
      intro fr hfr hfrlt hc
      have hidxeq := merge_corollary_regionId_unique_index vcfg.s1 hfr hframe0_mem (by rw [hc, hrid])
      exact absurd hidxeq (Nat.ne_of_lt hfrlt)
    have hheap_eq_at : ∀ fr : FrameWithIndex, fr ∈ cfg.stackWithIndex → fr.index < frame0.index →
        cfg'.heap.lookup fr.regionId = cfg.heap.lookup fr.regionId := by
      intro fr hfr hfrlt
      rw [hcfg']; dsimp only
      exact AList.lookup_insert_ne (hridne fr hfr hfrlt)
    have hfrRootIff : ∀ start, FrameRoot cfg frame.index start ↔ FrameRoot cfg' frame.index start := by
      intro start
      unfold FrameRoot
      constructor
      · rintro (⟨fr, hfr, hidx, var, hlookup⟩ | ⟨fr, hfr, hidx, region1, hlookup, hstart⟩)
        · exact Or.inl ⟨fr, frame_transport_up fr hfr (hidx ▸ hlt), hidx, var, hlookup⟩
        · exact Or.inr ⟨fr, frame_transport_up fr hfr (hidx ▸ hlt), hidx, region1,
            by rw [hheap_eq_at fr hfr (hidx ▸ hltd)]; exact hlookup, hstart⟩
      · rintro (⟨fr, hfr, hidx, var, hlookup⟩ | ⟨fr, hfr, hidx, region1, hlookup, hstart⟩)
        · exact Or.inl ⟨fr, frame_transport_down fr hfr (hidx ▸ hlt), hidx, var, hlookup⟩
        · have hfrCfg : fr ∈ cfg.stackWithIndex := frame_transport_down fr hfr (hidx ▸ hlt)
          exact Or.inr ⟨fr, hfrCfg, hidx, region1,
            by rw [← hheap_eq_at fr hfrCfg (hidx ▸ hltd)]; exact hlookup, hstart⟩
    have hoidm_ne : ∀ oidx, FrameReachable cfg frame.index (Reference.OId oidx) → oidx ≠ yoid := by
      intro oidx hreachx heq
      rw [heq] at hreachx
      have := region_container_confined vcfg hregion hstatus hframe0_mem hrid.symm hyloc0 hreachx
      exact absurd this (Nat.not_le.mpr hltd)
    have hoidm_ne' : ∀ oidx, FrameReachable cfg' frame.index (Reference.OId oidx) → oidx ≠ yoid := by
      intro oidx hreachx heq
      rw [heq] at hreachx
      have hyloc0' : (Reference.OId yoid).loc? cfg' = some (Location.Rgn rid) := by
        have e := swap_region_stack_loc_eq vcfg (rid := rid) (yoid := yoid) (region := region)
          (obj := obj) (field := yf.field) (newVal := Reference.OId xoid) (frame0 := frame0)
          (newVarMap := frame0.varMap.insert x yfRef) hframe0 hregion hobj yoid
        rw [← hcfg'] at e
        rw [← e]; exact hyloc0
      obtain ⟨fr0, hfr0, hidx0, hrid0, _⟩ := swap_frame_transport_up h frame0 hframe0_mem
      have hfr0rid : fr0.regionId = rid := hrid0.trans hrid.symm
      have hlookup' : cfg'.heap.lookup rid =
          some ({ region with objMap := region.objMap.insert yoid (obj.insert yf.field (Reference.OId xoid)) } :
            Region) := by
        rw [hcfg']; dsimp only; exact AList.lookup_insert cfg.heap
      have hownerbound := region_container_confined vcfg' hlookup' hstatus hfr0 hfr0rid hyloc0' hreachx
      rw [hidx0] at hownerbound
      exact absurd hownerbound (Nat.not_le.mpr hltd)
    have hobjAtEq : ∀ oid', oid' ≠ yoid →
        (Reference.OId oid').objAt? cfg = (Reference.OId oid').objAt? cfg' := by
      intro oid' hne
      have e := swap_region_stack_objAt_eq_of_ne vcfg (rid := rid) (yoid := yoid) (region := region)
        (obj := obj) (field := yf.field) (newVal := Reference.OId xoid) (frame0 := frame0)
        (newVarMap := frame0.varMap.insert x yfRef) hframe0 hregion hobj (oid' := oid') hne
      rw [← hcfg'] at e; exact e
    have hridstepIff : ∀ rid0 b, ReachableStep cfg (Reference.RId rid0) b ↔ ReachableStep cfg' (Reference.RId rid0) b := by
      intro rid0 b
      by_cases hrideq : rid0 = rid
      · subst hrideq
        have hlookup' : cfg'.heap.lookup rid0 =
            some ({ region with objMap := region.objMap.insert yoid (obj.insert yf.field (Reference.OId xoid)) } :
              Region) := by
          rw [hcfg']; dsimp only; exact AList.lookup_insert cfg.heap
        exact iff_of_false (open_rid_no_step hregion hstatus) (open_rid_no_step hlookup' hstatus)
      · have hlookup' : cfg'.heap.lookup rid0 = cfg.heap.lookup rid0 := by
          rw [hcfg']; dsimp only; exact AList.lookup_insert_ne hrideq
        rw [ReachableStep_rid_iff, ReachableStep_rid_iff, hlookup']
    constructor
    · rintro ⟨start, hroot, hrtg⟩
      have main_up : ∀ target : Reference, Relation.ReflTransGen (ReachableStep cfg) start target →
          FrameReachable cfg frame.index target ∧ Relation.ReflTransGen (ReachableStep cfg') start target := by
        intro target htrg
        induction htrg with
        | refl =>
          exact ⟨(FrameReachable_iff_reflTransGen cfg frame.index start).mpr
            ⟨start, hroot, Relation.ReflTransGen.refl⟩, Relation.ReflTransGen.refl⟩
        | tail hprev hstep ih =>
          rename_i p c
          obtain ⟨ihreach, ihrtg⟩ := ih
          cases p with
          | RId rid0 => exact ⟨FrameReachable.step hstep ihreach, ihrtg.tail ((hridstepIff rid0 c).mp hstep)⟩
          | OId oidb =>
            have hbne : oidb ≠ yoid := hoidm_ne oidb ihreach
            have heqB := hobjAtEq oidb hbne
            obtain ⟨objv, hobjAt, hcontains⟩ := (ReachableStep_oid_iff cfg oidb c).mp hstep
            exact ⟨FrameReachable.step hstep ihreach,
              ihrtg.tail ((ReachableStep_oid_iff cfg' oidb c).mpr ⟨objv, by rw [← heqB]; exact hobjAt, hcontains⟩)⟩
      obtain ⟨_, hup⟩ := main_up ref hrtg
      exact ⟨start, (hfrRootIff start).mp hroot, hup⟩
    · rintro ⟨start, hroot, hrtg⟩
      have hroot_down := (hfrRootIff start).mpr hroot
      have main_down : ∀ target : Reference, Relation.ReflTransGen (ReachableStep cfg') start target →
          FrameReachable cfg' frame.index target ∧ Relation.ReflTransGen (ReachableStep cfg) start target := by
        intro target htrg
        induction htrg with
        | refl =>
          exact ⟨(FrameReachable_iff_reflTransGen cfg' frame.index start).mpr
            ⟨start, hroot, Relation.ReflTransGen.refl⟩, Relation.ReflTransGen.refl⟩
        | tail hprev hstep ih =>
          rename_i p c
          obtain ⟨ihreach, ihrtg⟩ := ih
          cases p with
          | RId rid0 => exact ⟨FrameReachable.step hstep ihreach, ihrtg.tail ((hridstepIff rid0 c).mpr hstep)⟩
          | OId oidb =>
            have hbne : oidb ≠ yoid := hoidm_ne' oidb ihreach
            have heqB := hobjAtEq oidb hbne
            obtain ⟨objv, hobjAt, hcontains⟩ := (ReachableStep_oid_iff cfg' oidb c).mp hstep
            exact ⟨FrameReachable.step hstep ihreach,
              ihrtg.tail ((ReachableStep_oid_iff cfg oidb c).mpr ⟨objv, by rw [heqB]; exact hobjAt, hcontains⟩)⟩
      obtain ⟨_, hdown⟩ := main_down ref hrtg
      exact ⟨start, hroot_down, hdown⟩
  · -- SWAP-REGION-REGION
    have hyloc0 : (Reference.OId yoid).loc? cfg = some (Location.Rgn rid) := by
      rw [← hyoid, ← hyrloc]; exact hyrl
    have frame_transport_down : ∀ fr : FrameWithIndex, fr ∈ cfg'.stackWithIndex →
        fr.index < cfg.stack.dropLast.length → fr ∈ cfg.stackWithIndex := by
      intro fr hfr hltfr
      obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr
      have hidx_n : fr.index = n := by rw [← hfeq]
      have hltn : n < cfg.stack.dropLast.length := by rw [← hidx_n]; exact hltfr
      have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
        conv_lhs => rw [stack_eq0]; rw [List.getElem?_append_left hltn]
      have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
        rw [hcfg']; dsimp only; rw [List.getElem?_append_left hltn]
      have hfr_get? : cfg'.stack[n]? = some fr.toFrame := by
        rw [show fr.toFrame = cfg'.stack[n] from by rw [← hfeq]]
        exact List.getElem?_eq_getElem hn
      have hcfgn : cfg.stack[n]? = some fr.toFrame := by rw [e1, ← e2, hfr_get?]
      obtain ⟨h1, heq⟩ := List.getElem?_eq_some_iff.mp hcfgn
      unfold RuntimeConfig.stackWithIndex
      exact List.mem_mapIdx.mpr ⟨n, h1, by rw [heq, ← hidx_n]⟩
    have frame_transport_up : ∀ fr : FrameWithIndex, fr ∈ cfg.stackWithIndex →
        fr.index < cfg.stack.dropLast.length → fr ∈ cfg'.stackWithIndex := by
      intro fr hfr hltfr
      obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr
      have hidx_n : fr.index = n := by rw [← hfeq]
      have hltn : n < cfg.stack.dropLast.length := by rw [← hidx_n]; exact hltfr
      have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
        conv_lhs => rw [stack_eq0]; rw [List.getElem?_append_left hltn]
      have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
        rw [hcfg']; dsimp only; rw [List.getElem?_append_left hltn]
      have hfr_get? : cfg.stack[n]? = some fr.toFrame := by
        rw [show fr.toFrame = cfg.stack[n] from by rw [← hfeq]]
        exact List.getElem?_eq_getElem hn
      have hcfg'n : cfg'.stack[n]? = some fr.toFrame := by rw [e2, ← e1, hfr_get?]
      obtain ⟨h1, heq⟩ := List.getElem?_eq_some_iff.mp hcfg'n
      unfold RuntimeConfig.stackWithIndex
      exact List.mem_mapIdx.mpr ⟨n, h1, by rw [heq, ← hidx_n]⟩
    have hridne : ∀ fr : FrameWithIndex, fr ∈ cfg.stackWithIndex → fr.index < frame0.index →
        fr.regionId ≠ rid := by
      intro fr hfr hfrlt hc
      have hidxeq := merge_corollary_regionId_unique_index vcfg.s1 hfr hframe0_mem (by rw [hc, hrid])
      exact absurd hidxeq (Nat.ne_of_lt hfrlt)
    have hheap_eq_at : ∀ fr : FrameWithIndex, fr ∈ cfg.stackWithIndex → fr.index < frame0.index →
        cfg'.heap.lookup fr.regionId = cfg.heap.lookup fr.regionId := by
      intro fr hfr hfrlt
      rw [hcfg']; dsimp only
      exact AList.lookup_insert_ne (hridne fr hfr hfrlt)
    have hfrRootIff : ∀ start, FrameRoot cfg frame.index start ↔ FrameRoot cfg' frame.index start := by
      intro start
      unfold FrameRoot
      constructor
      · rintro (⟨fr, hfr, hidx, var, hlookup⟩ | ⟨fr, hfr, hidx, region1, hlookup, hstart⟩)
        · exact Or.inl ⟨fr, frame_transport_up fr hfr (hidx ▸ hlt), hidx, var, hlookup⟩
        · exact Or.inr ⟨fr, frame_transport_up fr hfr (hidx ▸ hlt), hidx, region1,
            by rw [hheap_eq_at fr hfr (hidx ▸ hltd)]; exact hlookup, hstart⟩
      · rintro (⟨fr, hfr, hidx, var, hlookup⟩ | ⟨fr, hfr, hidx, region1, hlookup, hstart⟩)
        · exact Or.inl ⟨fr, frame_transport_down fr hfr (hidx ▸ hlt), hidx, var, hlookup⟩
        · have hfrCfg : fr ∈ cfg.stackWithIndex := frame_transport_down fr hfr (hidx ▸ hlt)
          exact Or.inr ⟨fr, hfrCfg, hidx, region1,
            by rw [← hheap_eq_at fr hfrCfg (hidx ▸ hltd)]; exact hlookup, hstart⟩
    have hoidm_ne : ∀ oidx, FrameReachable cfg frame.index (Reference.OId oidx) → oidx ≠ yoid := by
      intro oidx hreachx heq
      rw [heq] at hreachx
      have := region_container_confined vcfg hregion hstatus hframe0_mem hrid.symm hyloc0 hreachx
      exact absurd this (Nat.not_le.mpr hltd)
    have hoidm_ne' : ∀ oidx, FrameReachable cfg' frame.index (Reference.OId oidx) → oidx ≠ yoid := by
      intro oidx hreachx heq
      rw [heq] at hreachx
      have hyloc0' : (Reference.OId yoid).loc? cfg' = some (Location.Rgn rid) := by
        have e := swap_region_stack_loc_eq vcfg (rid := rid) (yoid := yoid) (region := region)
          (obj := obj) (field := yf.field) (newVal := Reference.RId xrid) (frame0 := frame0)
          (newVarMap := frame0.varMap.insert x yfRef) hframe0 hregion hobj yoid
        rw [← hcfg'] at e
        rw [← e]; exact hyloc0
      obtain ⟨fr0, hfr0, hidx0, hrid0, _⟩ := swap_frame_transport_up h frame0 hframe0_mem
      have hfr0rid : fr0.regionId = rid := hrid0.trans hrid.symm
      have hlookup' : cfg'.heap.lookup rid =
          some ({ region with objMap := region.objMap.insert yoid (obj.insert yf.field (Reference.RId xrid)) } :
            Region) := by
        rw [hcfg']; dsimp only; exact AList.lookup_insert cfg.heap
      have hownerbound := region_container_confined vcfg' hlookup' hstatus hfr0 hfr0rid hyloc0' hreachx
      rw [hidx0] at hownerbound
      exact absurd hownerbound (Nat.not_le.mpr hltd)
    have hobjAtEq : ∀ oid', oid' ≠ yoid →
        (Reference.OId oid').objAt? cfg = (Reference.OId oid').objAt? cfg' := by
      intro oid' hne
      have e := swap_region_stack_objAt_eq_of_ne vcfg (rid := rid) (yoid := yoid) (region := region)
        (obj := obj) (field := yf.field) (newVal := Reference.RId xrid) (frame0 := frame0)
        (newVarMap := frame0.varMap.insert x yfRef) hframe0 hregion hobj (oid' := oid') hne
      rw [← hcfg'] at e; exact e
    have hridstepIff : ∀ rid0 b, ReachableStep cfg (Reference.RId rid0) b ↔ ReachableStep cfg' (Reference.RId rid0) b := by
      intro rid0 b
      by_cases hrideq : rid0 = rid
      · subst hrideq
        have hlookup' : cfg'.heap.lookup rid0 =
            some ({ region with objMap := region.objMap.insert yoid (obj.insert yf.field (Reference.RId xrid)) } :
              Region) := by
          rw [hcfg']; dsimp only; exact AList.lookup_insert cfg.heap
        exact iff_of_false (open_rid_no_step hregion hstatus) (open_rid_no_step hlookup' hstatus)
      · have hlookup' : cfg'.heap.lookup rid0 = cfg.heap.lookup rid0 := by
          rw [hcfg']; dsimp only; exact AList.lookup_insert_ne hrideq
        rw [ReachableStep_rid_iff, ReachableStep_rid_iff, hlookup']
    constructor
    · rintro ⟨start, hroot, hrtg⟩
      have main_up : ∀ target : Reference, Relation.ReflTransGen (ReachableStep cfg) start target →
          FrameReachable cfg frame.index target ∧ Relation.ReflTransGen (ReachableStep cfg') start target := by
        intro target htrg
        induction htrg with
        | refl =>
          exact ⟨(FrameReachable_iff_reflTransGen cfg frame.index start).mpr
            ⟨start, hroot, Relation.ReflTransGen.refl⟩, Relation.ReflTransGen.refl⟩
        | tail hprev hstep ih =>
          rename_i p c
          obtain ⟨ihreach, ihrtg⟩ := ih
          cases p with
          | RId rid0 => exact ⟨FrameReachable.step hstep ihreach, ihrtg.tail ((hridstepIff rid0 c).mp hstep)⟩
          | OId oidb =>
            have hbne : oidb ≠ yoid := hoidm_ne oidb ihreach
            have heqB := hobjAtEq oidb hbne
            obtain ⟨objv, hobjAt, hcontains⟩ := (ReachableStep_oid_iff cfg oidb c).mp hstep
            exact ⟨FrameReachable.step hstep ihreach,
              ihrtg.tail ((ReachableStep_oid_iff cfg' oidb c).mpr ⟨objv, by rw [← heqB]; exact hobjAt, hcontains⟩)⟩
      obtain ⟨_, hup⟩ := main_up ref hrtg
      exact ⟨start, (hfrRootIff start).mp hroot, hup⟩
    · rintro ⟨start, hroot, hrtg⟩
      have hroot_down := (hfrRootIff start).mpr hroot
      have main_down : ∀ target : Reference, Relation.ReflTransGen (ReachableStep cfg') start target →
          FrameReachable cfg' frame.index target ∧ Relation.ReflTransGen (ReachableStep cfg) start target := by
        intro target htrg
        induction htrg with
        | refl =>
          exact ⟨(FrameReachable_iff_reflTransGen cfg' frame.index start).mpr
            ⟨start, hroot, Relation.ReflTransGen.refl⟩, Relation.ReflTransGen.refl⟩
        | tail hprev hstep ih =>
          rename_i p c
          obtain ⟨ihreach, ihrtg⟩ := ih
          cases p with
          | RId rid0 => exact ⟨FrameReachable.step hstep ihreach, ihrtg.tail ((hridstepIff rid0 c).mpr hstep)⟩
          | OId oidb =>
            have hbne : oidb ≠ yoid := hoidm_ne' oidb ihreach
            have heqB := hobjAtEq oidb hbne
            obtain ⟨objv, hobjAt, hcontains⟩ := (ReachableStep_oid_iff cfg' oidb c).mp hstep
            exact ⟨FrameReachable.step hstep ihreach,
              ihrtg.tail ((ReachableStep_oid_iff cfg oidb c).mpr ⟨objv, by rw [heqB]; exact hobjAt, hcontains⟩)⟩
      obtain ⟨_, hdown⟩ := main_down ref hrtg
      exact ⟨start, hroot_down, hdown⟩
  · -- SWAP-REGION-BRIDGE
    have hyloc0 : (Reference.OId yoid).loc? cfg = some (Location.Rgn yrid) := by
      rw [← hyoid, ← hyrloc]; exact hyrl
    have hswi_eq : cfg'.stackWithIndex = cfg.stackWithIndex := by
      unfold RuntimeConfig.stackWithIndex
      rw [show cfg'.stack = cfg.stack from by rw [hcfg']]
    obtain ⟨region0, hlkFrame0, hopenFrame0⟩ := l2_of_stackWithIndex vcfg hframe0_mem
    have hregionEq : region0 = region := by
      rw [← hyridEq] at hlkFrame0; rw [hregion] at hlkFrame0; injection hlkFrame0 with heq; exact heq.symm
    have hopenReg : region.status = Status.Open := hregionEq ▸ hopenFrame0
    set newRegionB : Region := { region with bridgeObjectId := yfoid, objMap := region.objMap.insert yoid (obj.insert yf.field (Reference.OId region.bridgeObjectId)) } with newRegionB_def
    have hridne : ∀ fr : FrameWithIndex, fr ∈ cfg.stackWithIndex → fr.index < frame0.index →
        fr.regionId ≠ yrid := by
      intro fr hfr hfrlt hc
      have hidxeq := merge_corollary_regionId_unique_index vcfg.s1 hfr hframe0_mem (by rw [hc, hyridEq])
      exact absurd hidxeq (Nat.ne_of_lt hfrlt)
    have hheap_eq_at : ∀ fr : FrameWithIndex, fr ∈ cfg.stackWithIndex → fr.index < frame0.index →
        cfg'.heap.lookup fr.regionId = cfg.heap.lookup fr.regionId := by
      intro fr hfr hfrlt
      rw [hcfg']; dsimp only
      exact AList.lookup_insert_ne (hridne fr hfr hfrlt)
    have hfrRootIff : ∀ start, FrameRoot cfg frame.index start ↔ FrameRoot cfg' frame.index start := by
      intro start
      unfold FrameRoot
      constructor
      · rintro (⟨fr, hfr, hidx, var, hlookup⟩ | ⟨fr, hfr, hidx, region1, hlookup, hstart⟩)
        · exact Or.inl ⟨fr, hswi_eq ▸ hfr, hidx, var, hlookup⟩
        · exact Or.inr ⟨fr, hswi_eq ▸ hfr, hidx, region1,
            by rw [hheap_eq_at fr hfr (hidx ▸ hltd)]; exact hlookup, hstart⟩
      · rintro (⟨fr, hfr, hidx, var, hlookup⟩ | ⟨fr, hfr, hidx, region1, hlookup, hstart⟩)
        · exact Or.inl ⟨fr, hswi_eq ▸ hfr, hidx, var, hlookup⟩
        · have hfrCfg : fr ∈ cfg.stackWithIndex := hswi_eq ▸ hfr
          exact Or.inr ⟨fr, hfrCfg, hidx, region1,
            by rw [← hheap_eq_at fr hfrCfg (hidx ▸ hltd)]; exact hlookup, hstart⟩
    have hoidm_ne : ∀ oidx, FrameReachable cfg frame.index (Reference.OId oidx) → oidx ≠ yoid := by
      intro oidx hreachx heq
      rw [heq] at hreachx
      have := region_container_confined vcfg hregion hopenReg hframe0_mem hyridEq.symm hyloc0 hreachx
      exact absurd this (Nat.not_le.mpr hltd)
    have hoidm_ne' : ∀ oidx, FrameReachable cfg' frame.index (Reference.OId oidx) → oidx ≠ yoid := by
      intro oidx hreachx heq
      rw [heq] at hreachx
      have hyloc0' : (Reference.OId yoid).loc? cfg' = some (Location.Rgn yrid) := by
        have e := swap_corollary_region_loc_eq (rid := yrid) (yoid := yoid) (region := region)
          (newRegion := newRegionB) (obj := obj) (v := obj.insert yf.field (Reference.OId region.bridgeObjectId))
          vcfg hregion hobj (by rw [newRegionB_def]) yoid
        rw [← hcfg'] at e
        rw [← e]; exact hyloc0
      have hframe0_mem' : frame0 ∈ cfg'.stackWithIndex := hswi_eq ▸ hframe0_mem
      have hlookup' : cfg'.heap.lookup yrid = some newRegionB := by
        rw [hcfg']; dsimp only; exact AList.lookup_insert cfg.heap
      have hownerbound := region_container_confined vcfg' hlookup' hopenReg hframe0_mem' hyridEq.symm
        hyloc0' hreachx
      exact absurd hownerbound (Nat.not_le.mpr hltd)
    have hobjAtEq : ∀ oid', oid' ≠ yoid →
        (Reference.OId oid').objAt? cfg = (Reference.OId oid').objAt? cfg' := by
      intro oid' hne
      have e := swap_region_objAt_eq_of_ne vcfg (rid := yrid) (yoid := yoid) (region := region)
        (obj := obj) (field := yf.field) (newVal := Reference.OId region.bridgeObjectId) (newBridge := yfoid)
        hregion hobj (oid' := oid') hne
      rw [← hcfg'] at e; exact e
    have hridstepIff : ∀ rid0 b, ReachableStep cfg (Reference.RId rid0) b ↔ ReachableStep cfg' (Reference.RId rid0) b := by
      intro rid0 b
      by_cases hrideq : rid0 = yrid
      · subst hrideq
        have hlookup' : cfg'.heap.lookup rid0 = some newRegionB := by
          rw [hcfg']; dsimp only; exact AList.lookup_insert cfg.heap
        exact iff_of_false (open_rid_no_step hregion hopenReg) (open_rid_no_step hlookup' hopenReg)
      · have hlookup' : cfg'.heap.lookup rid0 = cfg.heap.lookup rid0 := by
          rw [hcfg']; dsimp only; exact AList.lookup_insert_ne hrideq
        rw [ReachableStep_rid_iff, ReachableStep_rid_iff, hlookup']
    constructor
    · rintro ⟨start, hroot, hrtg⟩
      have main_up : ∀ target : Reference, Relation.ReflTransGen (ReachableStep cfg) start target →
          FrameReachable cfg frame.index target ∧ Relation.ReflTransGen (ReachableStep cfg') start target := by
        intro target htrg
        induction htrg with
        | refl =>
          exact ⟨(FrameReachable_iff_reflTransGen cfg frame.index start).mpr
            ⟨start, hroot, Relation.ReflTransGen.refl⟩, Relation.ReflTransGen.refl⟩
        | tail hprev hstep ih =>
          rename_i p c
          obtain ⟨ihreach, ihrtg⟩ := ih
          cases p with
          | RId rid0 => exact ⟨FrameReachable.step hstep ihreach, ihrtg.tail ((hridstepIff rid0 c).mp hstep)⟩
          | OId oidb =>
            have hbne : oidb ≠ yoid := hoidm_ne oidb ihreach
            have heqB := hobjAtEq oidb hbne
            obtain ⟨objv, hobjAt, hcontains⟩ := (ReachableStep_oid_iff cfg oidb c).mp hstep
            exact ⟨FrameReachable.step hstep ihreach,
              ihrtg.tail ((ReachableStep_oid_iff cfg' oidb c).mpr ⟨objv, by rw [← heqB]; exact hobjAt, hcontains⟩)⟩
      obtain ⟨_, hup⟩ := main_up ref hrtg
      exact ⟨start, (hfrRootIff start).mp hroot, hup⟩
    · rintro ⟨start, hroot, hrtg⟩
      have hroot_down := (hfrRootIff start).mpr hroot
      have main_down : ∀ target : Reference, Relation.ReflTransGen (ReachableStep cfg') start target →
          FrameReachable cfg' frame.index target ∧ Relation.ReflTransGen (ReachableStep cfg) start target := by
        intro target htrg
        induction htrg with
        | refl =>
          exact ⟨(FrameReachable_iff_reflTransGen cfg' frame.index start).mpr
            ⟨start, hroot, Relation.ReflTransGen.refl⟩, Relation.ReflTransGen.refl⟩
        | tail hprev hstep ih =>
          rename_i p c
          obtain ⟨ihreach, ihrtg⟩ := ih
          cases p with
          | RId rid0 => exact ⟨FrameReachable.step hstep ihreach, ihrtg.tail ((hridstepIff rid0 c).mpr hstep)⟩
          | OId oidb =>
            have hbne : oidb ≠ yoid := hoidm_ne' oidb ihreach
            have heqB := hobjAtEq oidb hbne
            obtain ⟨objv, hobjAt, hcontains⟩ := (ReachableStep_oid_iff cfg' oidb c).mp hstep
            exact ⟨FrameReachable.step hstep ihreach,
              ihrtg.tail ((ReachableStep_oid_iff cfg oidb c).mpr ⟨objv, by rw [heqB]; exact hobjAt, hcontains⟩)⟩
      obtain ⟨_, hdown⟩ := main_down ref hrtg
      exact ⟨start, hroot_down, hdown⟩

-- ROOT escape, shared by all four branches: `yfRef` (the field's OLD value) was already resolvable pre-mutation via `resolveFA`, giving a natural root `frameY` reaching `frameD` via `hcr3`.
theorem swap_escape {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    (hcr3 : FrameReachable_at_later_frame_implies_FrameReachable_at_frame cfg)
    {oid : ObjectId} {yf : FieldAccess} {yfRef : Reference}
    (hyf : resolveFA yf cfg = some yfRef) {frameD : FrameWithIndex}
    (hframeDMem : frameD ∈ cfg.stackWithIndex)
    (hlocDown : (Reference.OId oid).loc? cfg = some (Location.Rgn frameD.regionId)) :
    ∀ start : Reference, start = yfRef →
      Relation.ReflTransGen (ReachableStep cfg) start (Reference.OId oid) →
      FrameReachable cfg frameD.index (Reference.OId oid) := by
  obtain ⟨regionD, hlkD, hopenD⟩ := l2_of_stackWithIndex vcfg hframeDMem
  intro start hstarteq hrtgS
  cases yfRef with
  | RId ridw =>
    exfalso
    rw [hstarteq] at hrtgS
    exact reflTransGen_rid_source_open_absurd vcfg hlocDown hlkD hopenD hrtgS
  | OId oidw =>
    obtain ⟨frameY, hframeYMem, hreachYw⟩ := resolveFA_frameReach hyf
    have hreachY : FrameReachable cfg frameY.index (Reference.OId oid) := by
      rw [FrameReachable_iff_reflTransGen] at hreachYw ⊢
      obtain ⟨startY, hrootY, hrtgY⟩ := hreachYw
      exact ⟨startY, hrootY, hrtgY.trans (hstarteq ▸ hrtgS)⟩
    have hownerbound := region_container_confined vcfg hlkD hopenD hframeDMem rfl hlocDown hreachY
    by_cases heqidx : frameD.index = frameY.index
    · have hFYeq : frameY = frameD := swap_corollary_stackWithIndex_index_inj hframeYMem hframeDMem heqidx.symm
      rw [← hFYeq]; exact hreachY
    · have hltidx : frameD.index < frameY.index := lt_of_le_of_ne hownerbound heqidx
      exact hcr3 frameD hframeDMem frameY hframeYMem hltidx oid hlocDown hreachY

-- Shared by the `OId`-shaped mutated-container-content branches: a mid-chain hop using `newVal` has `frame0` as a valid root (`hxRoot`), reaching `frameD` via `hcr3`.
theorem swap_root_escape {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    (hcr3 : FrameReachable_at_later_frame_implies_FrameReachable_at_frame cfg)
    {oid oidc : ObjectId} {newVal : Reference}
    {frame0 frameD : FrameWithIndex} (hxRoot : FrameRoot cfg frame0.index newVal)
    (hframe0_mem : frame0 ∈ cfg.stackWithIndex) (hframeDMem : frameD ∈ cfg.stackWithIndex)
    (hlocDown : (Reference.OId oid).loc? cfg = some (Location.Rgn frameD.regionId))
    (heqv : Reference.OId oidc = newVal)
    (ihchain : Relation.ReflTransGen (ReachableStep cfg) (Reference.OId oidc) (Reference.OId oid)) :
    FrameReachable cfg frameD.index (Reference.OId oid) := by
  have hichainX : Relation.ReflTransGen (ReachableStep cfg) newVal (Reference.OId oid) := by
    rw [← heqv]; exact ihchain
  have hreachY : FrameReachable cfg frame0.index (Reference.OId oid) := by
    rw [FrameReachable_iff_reflTransGen]
    exact ⟨newVal, hxRoot, hichainX⟩
  obtain ⟨regionD, hlkD, hopenD⟩ := l2_of_stackWithIndex vcfg hframeDMem
  have hownerbound := region_container_confined vcfg hlkD hopenD hframeDMem rfl hlocDown hreachY
  by_cases heqidx : frameD.index = frame0.index
  · have hFYeq : frame0 = frameD := swap_corollary_stackWithIndex_index_inj hframe0_mem hframeDMem heqidx.symm
    rw [← hFYeq]; exact hreachY
  · have hltidx : frameD.index < frame0.index := lt_of_le_of_ne hownerbound heqidx
    exact hcr3 frameD hframeDMem frame0 hframe0_mem hltidx oid hlocDown hreachY

-- New vs. `Referencable`: `ReachableStep` can continue from an `RId` source, but reaching `oid` (in `frameD`'s Open region) from one is still impossible, via `reflTransGen_rid_source_open_absurd`.
theorem swap_root_escape_rid {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {oid : ObjectId} {xrid0 : RegionId} {frameD : FrameWithIndex}
    (hframeDMem : frameD ∈ cfg.stackWithIndex)
    (hlocDown : (Reference.OId oid).loc? cfg = some (Location.Rgn frameD.regionId))
    (ihchainX : Relation.ReflTransGen (ReachableStep cfg) (Reference.RId xrid0) (Reference.OId oid)) :
    FrameReachable cfg frameD.index (Reference.OId oid) := by
  obtain ⟨regionD, hlkD, hopenD⟩ := l2_of_stackWithIndex vcfg hframeDMem
  exact (reflTransGen_rid_source_open_absurd vcfg hlocDown hlkD hopenD ihchainX).elim

-- The mutated container's own step, restricted to `c ≠ newVal` (STACK branch): new refs are old refs plus possibly `newVal`.
theorem swap_stack_yoid_step_of_ne {cfg cfg' : RuntimeConfig} {frame0 : FrameWithIndex}
    {yoid : ObjectId} {obj : Object} {field : FieldName} {newVal : Reference} {newVarMap : VarMap}
    (hframe0 : cfg.stackWithIndex.getLast? = some frame0)
    (hlocm : (Reference.OId yoid).loc? cfg = some (Location.Stk frame0.index))
    (hobj : frame0.objMap.lookup yoid = some obj)
    (hcfg' : cfg' = { cfg with stack := cfg.stack.dropLast ++
      [({ frame0 with varMap := newVarMap, objMap := frame0.objMap.insert yoid (obj.insert field newVal) } :
        Frame)] })
    {c : Reference} (hstep : ReachableStep cfg' (Reference.OId yoid) c) :
    c = newVal ∨ ReachableStep cfg (Reference.OId yoid) c := by
  have hobjAtC : (Reference.OId yoid).objAt? cfg' = some (obj.insert field newVal) :=
    swap_stack_objAt_mutated hframe0 hobj hlocm hcfg'
  have hobjAt : (Reference.OId yoid).objAt? cfg = some obj := by
    unfold Reference.objAt?
    dsimp only
    rw [hlocm]
    dsimp only
    rw [stackWithIndex_find_index_eq_getElem]
    have hget : cfg.stackWithIndex[frame0.index]? =
        (cfg.stack[frame0.index]?).map (fun f => ({ toFrame := f, index := frame0.index } : FrameWithIndex)) := by
      unfold RuntimeConfig.stackWithIndex; rw [List.getElem?_mapIdx]
    rw [hget]
    obtain ⟨stack_eq, hidxeq⟩ := swap_corollary_stack_eq hframe0
    have hget2 : cfg.stack[frame0.index]? = some frame0.toFrame := by
      conv_lhs => rw [stack_eq, hidxeq]
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

-- Mirrors `swap_stack_yoid_step_of_ne` for the REGION-touching branches (mutated container in a region, plus an irrelevant stack `varMap` change).
theorem swap_region_stack_yoid_step_of_ne {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid yoid : ObjectId} {region : Region} {obj : Object} {field : FieldName} {newVal : Reference}
    {frame0 : FrameWithIndex} {newVarMap : VarMap}
    (hframe0 : cfg.stackWithIndex.getLast? = some frame0)
    (hregion : cfg.heap.lookup rid = some region) (hobj : region.objMap.lookup yoid = some obj)
    (hlocm : (Reference.OId yoid).loc? cfg = some (Location.Rgn rid))
    {c : Reference} (hstep : ReachableStep ({ stack := cfg.stack.dropLast ++ [({ frame0 with varMap := newVarMap } : Frame)], heap := cfg.heap.insert rid ({ region with objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) } : RuntimeConfig) (Reference.OId yoid) c) :
    c = newVal ∨ ReachableStep cfg (Reference.OId yoid) c := by
  have hobjAtC : (Reference.OId yoid).objAt? ({ stack := cfg.stack.dropLast ++ [({ frame0 with varMap := newVarMap } : Frame)], heap := cfg.heap.insert rid ({ region with objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) } : RuntimeConfig) = some (obj.insert field newVal) :=
    swap_region_stack_objAt_mutated vcfg hframe0 hregion hobj hlocm
  have hobjAt : (Reference.OId yoid).objAt? cfg = some obj := by
    unfold Reference.objAt?
    dsimp only
    rw [hlocm]
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

-- Mirrors `swap_stack_yoid_step_of_ne` for the SWAP-REGION-BRIDGE branch (heap-only, `newBridge` generalized).
theorem swap_bridge_yoid_step_of_ne {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid yoid : ObjectId} {region : Region} {obj : Object} {field : FieldName} {newVal : Reference}
    {newBridge : ObjectId}
    (hregion : cfg.heap.lookup rid = some region) (hobj : region.objMap.lookup yoid = some obj)
    (hlocm : (Reference.OId yoid).loc? cfg = some (Location.Rgn rid))
    {c : Reference} (hstep : ReachableStep ({ cfg with heap := cfg.heap.insert rid ({ region with bridgeObjectId := newBridge, objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) }) (Reference.OId yoid) c) :
    c = newVal ∨ ReachableStep cfg (Reference.OId yoid) c := by
  have hobjAtC : (Reference.OId yoid).objAt? ({ cfg with heap := cfg.heap.insert rid ({ region with bridgeObjectId := newBridge, objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) }) = some (obj.insert field newVal) :=
    swap_region_objAt_mutated vcfg (newBridge := newBridge) hregion hobj hlocm rfl
  have hobjAt : (Reference.OId yoid).objAt? cfg = some obj := by
    unfold Reference.objAt?
    dsimp only
    rw [hlocm]
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

-- `ReachableStep` agrees for any source other than the mutated container (STACK branch): heap untouched, so `RId` hops are trivial.
theorem swap_stack_step_iff_of_ne {cfg cfg' : RuntimeConfig} {frame0 : FrameWithIndex}
    {yoid : ObjectId} {obj : Object} {field : FieldName} {newVal : Reference} {newVarMap : VarMap}
    (hframe0 : cfg.stackWithIndex.getLast? = some frame0) (hobj : frame0.objMap.lookup yoid = some obj)
    (hcfg' : cfg' = { cfg with stack := cfg.stack.dropLast ++
      [({ frame0 with varMap := newVarMap, objMap := frame0.objMap.insert yoid (obj.insert field newVal) } :
        Frame)] }) :
    ∀ a : Reference, a ≠ Reference.OId yoid → ∀ b : Reference, ReachableStep cfg a b ↔ ReachableStep cfg' a b := by
  intro a hane b
  cases a with
  | OId oid' =>
    have hne : oid' ≠ yoid := fun heq => hane (heq ▸ rfl)
    have e := swap_stack_objAt_eq_of_ne (field := field) (newVal := newVal) (newVarMap := newVarMap)
      hframe0 hobj hne
    rw [← hcfg'] at e
    rw [ReachableStep_oid_iff, ReachableStep_oid_iff, e]
  | RId rid' =>
    have hheapEq : cfg'.heap = cfg.heap := by rw [hcfg']
    rw [ReachableStep_rid_iff, ReachableStep_rid_iff, hheapEq]

-- Mirrors `swap_stack_step_iff_of_ne` for the REGION-touching branches: the touched region is always Open (L2), so no `RId` hop is possible.
theorem swap_region_stack_step_iff_of_ne {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid yoid : ObjectId} {region : Region} {obj : Object} {field : FieldName} {newVal : Reference}
    {frame0 : FrameWithIndex} {newVarMap : VarMap}
    (hframe0 : cfg.stackWithIndex.getLast? = some frame0)
    (hregion : cfg.heap.lookup rid = some region) (hobj : region.objMap.lookup yoid = some obj)
    (hstatus : region.status = Status.Open)
    (hcfg' : cfg' = { stack := cfg.stack.dropLast ++ [({ frame0 with varMap := newVarMap } : Frame)], heap := cfg.heap.insert rid ({ region with objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) }) :
    ∀ a : Reference, a ≠ Reference.OId yoid → ∀ b : Reference, ReachableStep cfg a b ↔ ReachableStep cfg' a b := by
  intro a hane b
  cases a with
  | OId oid' =>
    have hne : oid' ≠ yoid := fun heq => hane (heq ▸ rfl)
    have e := swap_region_stack_objAt_eq_of_ne vcfg (field := field) (newVal := newVal) (newVarMap := newVarMap) hframe0 hregion hobj hne
    rw [← hcfg'] at e
    rw [ReachableStep_oid_iff, ReachableStep_oid_iff, e]
  | RId rid' =>
    by_cases hrideq : rid' = rid
    · subst hrideq
      have hlookup' : cfg'.heap.lookup rid' = some ({ region with objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) := by
        rw [hcfg']; dsimp only; exact AList.lookup_insert cfg.heap
      exact iff_of_false (open_rid_no_step hregion hstatus) (open_rid_no_step hlookup' hstatus)
    · have hlookup' : cfg'.heap.lookup rid' = cfg.heap.lookup rid' := by
        rw [hcfg']; dsimp only; exact AList.lookup_insert_ne hrideq
      rw [ReachableStep_rid_iff, ReachableStep_rid_iff, hlookup']

-- Mirrors `swap_stack_step_iff_of_ne` for the SWAP-REGION-BRIDGE branch (heap-only, `newBridge` generalized).
theorem swap_bridge_step_iff_of_ne {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid yoid : ObjectId} {region : Region} {obj : Object} {field : FieldName} {newVal : Reference}
    {newBridge : ObjectId} (hregion : cfg.heap.lookup rid = some region) (hobj : region.objMap.lookup yoid = some obj)
    (hstatus : region.status = Status.Open)
    (hcfg' : cfg' = { cfg with heap := cfg.heap.insert rid ({ region with bridgeObjectId := newBridge, objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) }) :
    ∀ a : Reference, a ≠ Reference.OId yoid → ∀ b : Reference, ReachableStep cfg a b ↔ ReachableStep cfg' a b := by
  intro a hane b
  cases a with
  | OId oid' =>
    have hne : oid' ≠ yoid := fun heq => hane (heq ▸ rfl)
    have e := swap_region_objAt_eq_of_ne vcfg (field := field) (newVal := newVal) (newBridge := newBridge) hregion hobj hne
    rw [← hcfg'] at e
    rw [ReachableStep_oid_iff, ReachableStep_oid_iff, e]
  | RId rid' =>
    by_cases hrideq : rid' = rid
    · subst hrideq
      have hlookup' : cfg'.heap.lookup rid' = some ({ region with bridgeObjectId := newBridge, objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) := by
        rw [hcfg']; dsimp only; exact AList.lookup_insert cfg.heap
      exact iff_of_false (open_rid_no_step hregion hstatus) (open_rid_no_step hlookup' hstatus)
    · have hlookup' : cfg'.heap.lookup rid' = cfg.heap.lookup rid' := by
        rw [hcfg']; dsimp only; exact AList.lookup_insert_ne hrideq
      rw [ReachableStep_rid_iff, ReachableStep_rid_iff, hlookup']
