import Gc.Model.Mutation.Swap
import Gc.Model.Preservation.Swap
import Gc.Model.Preservation.Common
import Gc.Reachability.Referencable.Basic
import Gc.Reachability.Referencable.Lemmas.Common

-- swap's stack-mutating branches (SWAP-STACK/SWAP-REGION-OBJECT/SWAP-REGION-REGION) all replace
-- the last frame with some `newFrame` built via `{ frame with varMap := ..., objMap := ... }`
-- (varying which fields actually change), so `newFrame.regionId`/`newFrame.bridgeVar` always
-- literally equal `frame.regionId`/`frame.bridgeVar` -- this packages the common index-case-split
-- argument once (mirrors varAsgn/fieldAsgn's own `stack_shape_eq`, generalized over the replacement
-- frame instead of hardcoding it), for reuse across those three branches.
theorem swap_corollary_stack_shape_eq_of_last_update
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

-- swap never touches a frame's `regionId`/`bridgeVar` anywhere: SWAP-STACK/SWAP-REGION-OBJECT/
-- SWAP-REGION-REGION only ever replace the last frame's `varMap`/`objMap`, and SWAP-REGION-BRIDGE
-- doesn't touch `cfg.stack` at all. Mirrors varAsgn_corollary_stack_shape_eq's role.
theorem swap_corollary_stack_shape_eq (h : swap x yf cfg = some cfg') (n : ℕ) :
    (cfg.stack[n]?).map (fun f => (f.regionId, f.bridgeVar)) =
    (cfg'.stack[n]?).map (fun f => (f.regionId, f.bridgeVar)) := by
  obtain ⟨frame, hframe, yRef, hyr, yRefLoc, hyrl, yfRef, hyf, yfRefLoc, hyfl, hcase⟩ := swap_cases h
  rcases hcase with
    ⟨yoid, xRef, obj, hxb, hyoid, hyrloc, hxr, hobj, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xoid, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hxrl, hxrid, hstatus, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hstatus, hcfg'⟩ |
    ⟨yoid, yrid, yfoid, yfrid, region, obj, hxb, hyoid, hyrloc, hyfoid, hyfrloc, hyrid, hyfrid, hregion, hobj, hcfg'⟩
  · exact swap_corollary_stack_shape_eq_of_last_update
      { frame with varMap := frame.varMap.insert x yfRef, objMap := frame.objMap.insert yoid (obj.insert yf.field xRef) }
      hframe (by rw [hcfg']) rfl rfl n
  · exact swap_corollary_stack_shape_eq_of_last_update
      { frame with varMap := frame.varMap.insert x yfRef } hframe (by rw [hcfg']) rfl rfl n
  · exact swap_corollary_stack_shape_eq_of_last_update
      { frame with varMap := frame.varMap.insert x yfRef } hframe (by rw [hcfg']) rfl rfl n
  · rw [hcfg']

-- Any frame membership in cfg'.stackWithIndex transports down to cfg with the SAME index,
-- regionId and bridgeVar (though possibly a different varMap/objMap) -- everything CR3/FrameRoot
-- ever read off a frame (never its varMap/objMap directly; those are read only via `.lookup`,
-- transported separately per branch below). Thin wrapper around `Gc.Model.Preservation.Common`'s
-- generic `stackWithIndex_frame_transport_down_of_shape_eq` (same `proj` as
-- `varAsgn_corollary_frame_transport_down`, since both operations leave `regionId`/`bridgeVar`
-- untouched everywhere).
theorem swap_corollary_frame_transport_down (h : swap x yf cfg = some cfg')
    (fr : FrameWithIndex) (hfr : fr ∈ cfg'.stackWithIndex) :
    ∃ fr0 : FrameWithIndex, fr0 ∈ cfg.stackWithIndex ∧ fr0.index = fr.index ∧
      fr0.regionId = fr.regionId ∧ fr0.bridgeVar = fr.bridgeVar := by
  obtain ⟨fr0, hmem, hidx, hproj⟩ :=
    stackWithIndex_frame_transport_down_of_shape_eq (proj := fun f => (f.regionId, f.bridgeVar))
      (swap_corollary_stack_shape_eq h) fr hfr
  injection hproj with hrid hbv
  exact ⟨fr0, hmem, hidx, hrid, hbv⟩

-- Mirrors swap_corollary_frame_transport_down, transporting membership the other way (also a thin
-- wrapper, around `stackWithIndex_frame_transport_up_of_shape_eq`).
theorem swap_corollary_frame_transport_up (h : swap x yf cfg = some cfg')
    (fr : FrameWithIndex) (hfr : fr ∈ cfg.stackWithIndex) :
    ∃ fr0 : FrameWithIndex, fr0 ∈ cfg'.stackWithIndex ∧ fr0.index = fr.index ∧
      fr0.regionId = fr.regionId ∧ fr0.bridgeVar = fr.bridgeVar := by
  obtain ⟨fr0, hmem, hidx, hproj⟩ :=
    stackWithIndex_frame_transport_up_of_shape_eq (proj := fun f => (f.regionId, f.bridgeVar))
      (swap_corollary_stack_shape_eq h) fr hfr
  injection hproj with hrid hbv
  exact ⟨fr0, hmem, hidx, hrid, hbv⟩

-- Generic AList fact (Reference-valued): membership after inserting at a key is either the
-- newly-written value or a pre-existing one. Copy of Model.Preservation.Swap's
-- `swap_corollary_alist_insert_refs_mem`, restated at the `Object.refs` level (mirrors
-- fieldAsgn_corollary_object_insert_refs_mem).
theorem swap_corollary_object_insert_refs_mem {obj : Object} {field : FieldName} {v r : Reference}
    (hr : r ∈ Object.refs (obj.insert field v)) : r = v ∨ r ∈ Object.refs obj := by
  unfold Object.refs at hr ⊢
  exact swap_corollary_alist_insert_refs_mem hr

-- The mutated container's own new content on the REGION-touching branches (mirrors
-- fieldAsgn_corollary_region_objAt_mutated): computed directly from the region-level insert at the
-- already-present key `yoid` (the container). Generalized over `newBridge : ObjectId` so the same
-- proof covers both an untouched `bridgeObjectId` (non-bridge callers pass `region.bridgeObjectId`)
-- and SWAP-REGION-BRIDGE's simultaneous bridge change (`Reference.objAt?`/
-- `swap_corollary_region_loc_eq` never read `bridgeObjectId` at all, so folding it into `newRegion`
-- doesn't change the proof shape).
theorem swap_corollary_region_objAt_mutated {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
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

-- REGION-touching branches: for any oid' *other* than the mutated container, `objAt?` is
-- unaffected. Mirrors fieldAsgn_corollary_region_objAt_eq_of_ne, using swap's own (already
-- unconditional-in-oid') `swap_corollary_region_loc_eq`. Generalized over `newBridge` for the same
-- reason as `swap_corollary_region_objAt_mutated` above.
theorem swap_corollary_region_objAt_eq_of_ne {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
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

-- Heap `bridgeObjectId` at any key transports across a region-object-map-only mutation
-- (`hbv` witnesses the touched region's own `bridgeObjectId` is literally unaffected) -- used for
-- FrameRoot's bridge disjunct, which never reads `objMap`. Mirrors
-- fieldAsgn_corollary_heap_bridge_eq, generalized to a bare `Heap`-level statement (no
-- `RuntimeConfig` wrapper) so it applies uniformly whether or not the *stack* also changed.
theorem swap_corollary_region_heap_bridge_eq {cfg : RuntimeConfig} {rid : RegionId}
    {region newRegion : Region} (hregion : cfg.heap.lookup rid = some region)
    (hbv : newRegion.bridgeObjectId = region.bridgeObjectId) (rid0 : RegionId) :
    (cfg.heap.lookup rid0).map Region.bridgeObjectId =
      ((cfg.heap.insert rid newRegion).lookup rid0).map Region.bridgeObjectId := by
  by_cases hrideq : rid0 = rid
  · subst hrideq
    rw [hregion, AList.lookup_insert, Option.map_some, Option.map_some, hbv]
  · rw [AList.lookup_insert_ne hrideq]

-- A varMap-only change to the last frame never affects `objAt?` either -- mirrors
-- swap_corollary_stack_varmap_loc_eq at the objAt? level (needed since the REGION-touching
-- branches change the stack varMap *and* the heap objMap simultaneously, so the loc?-level fact
-- alone isn't enough once we need to reason about actual object *content*).
theorem swap_corollary_varmap_objAt_eq {cfg : RuntimeConfig} {frame : FrameWithIndex} {newVarMap : VarMap}
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

-- Composes `swap_corollary_region_loc_eq` (heap objMap change) with
-- `swap_corollary_stack_varmap_loc_eq` (stack varMap change) -- needed because
-- SWAP-REGION-OBJECT/SWAP-REGION-REGION change BOTH simultaneously, unlike any single
-- Model.Preservation.Swap corollary (which each cover only one side at a time).
theorem swap_corollary_region_stack_loc_eq {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
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

-- objAt? analogue of swap_corollary_region_stack_loc_eq, for oid' *other* than the mutated
-- container.
theorem swap_corollary_region_stack_objAt_eq_of_ne {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid yoid : ObjectId} {region : Region} {obj : Object} {field : FieldName} {newVal : Reference}
    {frame0 : FrameWithIndex} {newVarMap : VarMap}
    (hframe0 : cfg.stackWithIndex.getLast? = some frame0)
    (hregion : cfg.heap.lookup rid = some region) (hobj : region.objMap.lookup yoid = some obj)
    {oid' : ObjectId} (hne : oid' ≠ yoid) :
    (Reference.OId oid').objAt? cfg =
      (Reference.OId oid').objAt? ({ stack := cfg.stack.dropLast ++ [({ frame0 with varMap := newVarMap } : Frame)], heap := cfg.heap.insert rid ({ region with objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) } : RuntimeConfig) := by
  have step1 := swap_corollary_region_objAt_eq_of_ne vcfg (rid := rid) (yoid := yoid) (region := region)
    (obj := obj) (field := field) (newVal := newVal) (newBridge := region.bridgeObjectId) hregion hobj hne
  have hframe0' : ({ cfg with heap := cfg.heap.insert rid ({ region with objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) } : RuntimeConfig).stackWithIndex.getLast? = some frame0 :=
    hframe0
  have step2 := swap_corollary_varmap_objAt_eq
    (cfg := { cfg with heap := cfg.heap.insert rid ({ region with objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) })
    (frame := frame0) (newVarMap := newVarMap) hframe0' oid'
  exact step1.trans step2

-- The mutated container's own new content combined with the (irrelevant, since it never touches
-- objMap) simultaneous stack varMap change.
theorem swap_corollary_region_stack_objAt_mutated {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid yoid : ObjectId} {region : Region} {obj : Object} {field : FieldName} {newVal : Reference}
    {frame0 : FrameWithIndex} {newVarMap : VarMap}
    (hframe0 : cfg.stackWithIndex.getLast? = some frame0)
    (hregion : cfg.heap.lookup rid = some region) (hobj : region.objMap.lookup yoid = some obj)
    (hlocm : (Reference.OId yoid).loc? cfg = some (Location.Rgn rid)) :
    (Reference.OId yoid).objAt? ({ stack := cfg.stack.dropLast ++ [({ frame0 with varMap := newVarMap } : Frame)], heap := cfg.heap.insert rid ({ region with objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) } : RuntimeConfig) =
      some (obj.insert field newVal) := by
  have hstep : (Reference.OId yoid).objAt? ({ cfg with heap := cfg.heap.insert rid ({ region with objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) } : RuntimeConfig) = some (obj.insert field newVal) :=
    swap_corollary_region_objAt_mutated vcfg (newBridge := region.bridgeObjectId) hregion hobj hlocm rfl
  have hframe0' : ({ cfg with heap := cfg.heap.insert rid ({ region with objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) } : RuntimeConfig).stackWithIndex.getLast? = some frame0 :=
    hframe0
  have step2 := swap_corollary_varmap_objAt_eq
    (cfg := { cfg with heap := cfg.heap.insert rid ({ region with objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) })
    (frame := frame0) (newVarMap := newVarMap) hframe0' yoid
  rw [← step2]; exact hstep

-- The mutated container's own new content on the STACK branch: computed directly from the
-- `hcfg'` construction (frame0's position is found via index-uniqueness, and the new object's
-- value is inserted at the already-present key `yoid`). Mirrors
-- fieldAsgn_corollary_stack_objAt_mutated.
theorem swap_corollary_stack_objAt_mutated {cfg cfg' : RuntimeConfig} {frame0 : FrameWithIndex}
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

-- STACK branch: for any oid' *other* than the mutated container, `objAt?` (not just `loc?`) is
-- unaffected. Mirrors fieldAsgn_corollary_stack_objAt_eq_of_ne, using swap's own (already
-- unconditional-in-oid') `swap_corollary_stack_loc_eq` in place of fieldAsgn's version.
theorem swap_corollary_stack_objAt_eq_of_ne {cfg : RuntimeConfig} {frame0 : FrameWithIndex}
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

-- ROOT escape, shared verbatim by all four `swap_cr3` branches: whatever the mutation places at
-- the var/bridge root (`yfRef`, the field access `yf`'s OLD value) was already resolvable
-- pre-mutation via `resolveFA`, exactly like `varAsgn`'s fresh-var escape -- so a chain starting
-- there already has a natural pre-mutation root `frameY`, from which `frameD` (the region owner
-- CR3 is being checked against) is reached either directly (if `frameY = frameD`) or by recursing
-- into `vrcfg.cr3` itself. Nothing here depends on *where* the mutated container lives
-- (`Stk`/`Rgn`), which is why the same proof serves SWAP-STACK/SWAP-REGION-OBJECT/
-- SWAP-REGION-REGION/SWAP-REGION-BRIDGE unchanged.
theorem swap_corollary_escape {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    (vrcfg : ValidReachableConfig cfg) {oid : ObjectId} {yf : FieldAccess} {yfRef : Reference}
    (hyf : resolveFA yf cfg = some yfRef) {frameD : FrameWithIndex}
    (hframeDMem : frameD ∈ cfg.stackWithIndex)
    (hlocDown : (Reference.OId oid).loc? cfg = some (Location.Rgn frameD.regionId)) :
    ∀ start : Reference, start = yfRef →
      Relation.ReflTransGen (RefStep cfg) start (Reference.OId oid) →
      FrameReferencable cfg frameD.index (Reference.OId oid) := by
  intro start hstarteq hrtgS
  cases yfRef with
  | RId ridw =>
    exfalso
    rw [hstarteq] at hrtgS
    rcases hrtgS.cases_head with heq | ⟨d, hstep, _⟩
    · exact absurd heq (by simp)
    · obtain ⟨oid0, hoid0⟩ := hstep.exists_oid_left
      exact absurd hoid0 (by simp)
  | OId oidw =>
    obtain ⟨frameY, hframeYMem, hreachYw⟩ := resolveFA_frameReach hyf
    have hreachY : FrameReferencable cfg frameY.index (Reference.OId oid) := by
      rw [FrameReferencable_iff_reflTransGen] at hreachYw ⊢
      obtain ⟨startY, hrootY, hrtgY⟩ := hreachYw
      exact ⟨startY, hrootY, hrtgY.trans (hstarteq ▸ hrtgS)⟩
    have hownerbound := FrameReferencable_owner_index_le cfg vcfg frameY hreachY frameD.regionId
      hlocDown frameD hframeDMem rfl
    by_cases heqidx : frameD.index = frameY.index
    · have hFYeq : frameY = frameD := swap_corollary_stackWithIndex_index_inj hframeYMem hframeDMem heqidx.symm
      rw [← hFYeq]; exact hreachY
    · have hltidx : frameD.index < frameY.index := lt_of_le_of_ne hownerbound heqidx
      exact vrcfg.cr3 frameD hframeDMem frameY hframeYMem hltidx oid hlocDown hreachY

-- Shared by `main_claim`'s SWAP-STACK/SWAP-REGION-OBJECT/SWAP-REGION-BRIDGE branches (the ones
-- where the newly-written value `newVal` is `OId`-shaped, so `heqv : Reference.OId oidc = newVal`
-- is satisfiable -- SWAP-REGION-REGION's `newVal = Reference.RId xrid` makes this case vacuous
-- instead, via a direct constructor mismatch, so it never calls this lemma): a mid-chain hop using
-- `newVal` already has `frame0` itself as a valid root (`hxRoot`), so it reaches `frameD` either
-- directly or by recursing into `vrcfg.cr3`, exactly like `swap_corollary_escape`'s own argument.
theorem swap_corollary_root_escape {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    (vrcfg : ValidReachableConfig cfg) {oid oidc : ObjectId} {newVal : Reference}
    {frame0 frameD : FrameWithIndex} (hxRoot : FrameRoot cfg frame0.index newVal)
    (hframe0_mem : frame0 ∈ cfg.stackWithIndex) (hframeDMem : frameD ∈ cfg.stackWithIndex)
    (hlocDown : (Reference.OId oid).loc? cfg = some (Location.Rgn frameD.regionId))
    (heqv : Reference.OId oidc = newVal)
    (ihchain : Relation.ReflTransGen (RefStep cfg) (Reference.OId oidc) (Reference.OId oid)) :
    FrameReferencable cfg frameD.index (Reference.OId oid) := by
  have hichainX : Relation.ReflTransGen (RefStep cfg) newVal (Reference.OId oid) := by
    rw [← heqv]; exact ihchain
  have hreachY : FrameReferencable cfg frame0.index (Reference.OId oid) := by
    rw [FrameReferencable_iff_reflTransGen]
    exact ⟨newVal, hxRoot, hichainX⟩
  have hownerbound := FrameReferencable_owner_index_le cfg vcfg frame0 hreachY frameD.regionId
    hlocDown frameD hframeDMem rfl
  by_cases heqidx : frameD.index = frame0.index
  · have hFYeq : frame0 = frameD := swap_corollary_stackWithIndex_index_inj hframe0_mem hframeDMem heqidx.symm
    rw [← hFYeq]; exact hreachY
  · have hltidx : frameD.index < frame0.index := lt_of_le_of_ne hownerbound heqidx
    exact vrcfg.cr3 frameD hframeDMem frame0 hframe0_mem hltidx oid hlocDown hreachY

-- `FrameReferencable` is completely unaffected at any position strictly before the mutated (last)
-- one, across all four swap branches. Simpler than `swap_cr3` itself in the same way
-- `fieldAsgn_corollary_frameReferencable_iff_of_lt` is simpler than `fieldAsgn_cr3`: a chain rooted
-- at a suspended frame can never reach the mutated container `yoid` at all (owner-index bound), so
-- neither `swap_corollary_escape` nor `swap_corollary_root_escape` (CR3's mid-chain/root escape
-- machinery) is ever needed here -- just a per-branch FrameRoot-iff (frame identity is preserved
-- outside the mutated position) plus a straightforward tail-induction transport in each direction.
theorem swap_corollary_frameReferencable_iff_of_lt (vcfg : ValidConfig cfg) (vcfg' : ValidConfig cfg')
    (h : swap x yf cfg = some cfg')
    (frame : FrameWithIndex) (hlt : frame.index < cfg.stack.dropLast.length) (ref : Reference) :
    FrameReferencable cfg frame.index ref ↔ FrameReferencable cfg' frame.index ref := by
  obtain ⟨frame0, hframe0, yRef, hyr, yRefLoc, hyrl, yfRef, hyf, yfRefLoc, hyfl, hcase⟩ := swap_cases h
  have hframe0_mem : frame0 ∈ cfg.stackWithIndex := List.mem_of_getLast? hframe0
  obtain ⟨stack_eq0, hidx00⟩ := swap_corollary_stack_eq hframe0
  have hltd : frame.index < frame0.index := by rw [hidx00]; exact hlt
  rw [FrameReferencable_iff_reflTransGen, FrameReferencable_iff_reflTransGen]
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
    have hoidm_ne : ∀ oidx, FrameReferencable cfg frame.index (Reference.OId oidx) → oidx ≠ yoid := by
      intro oidx hreachx heq
      rw [heq] at hreachx
      have := FrameReferencable_stk_index_le cfg vcfg frame hreachx frame0.index hyloc0
      exact absurd this (Nat.not_le.mpr hltd)
    have hoidm_ne' : ∀ oidx, FrameReferencable cfg' frame.index (Reference.OId oidx) → oidx ≠ yoid := by
      intro oidx hreachx heq
      rw [heq] at hreachx
      have hyloc0' : (Reference.OId yoid).loc? cfg' = some (Location.Stk frame0.index) := by
        have e := swap_corollary_stack_loc_eq (field := yf.field) (newVal := xRef)
          (newVarMap := frame0.varMap.insert x yfRef) hframe0 hobj yoid
        rw [← hcfg'] at e; rw [← e]; exact hyloc0
      have := FrameReferencable_stk_index_le cfg' vcfg' frame hreachx frame0.index hyloc0'
      exact absurd this (Nat.not_le.mpr hltd)
    have hobjAtEq : ∀ oid', oid' ≠ yoid →
        (Reference.OId oid').objAt? cfg = (Reference.OId oid').objAt? cfg' := by
      intro oid' hne
      have e := swap_corollary_stack_objAt_eq_of_ne (yoid := yoid) (obj := obj) (field := yf.field)
        (newVal := xRef) (newVarMap := frame0.varMap.insert x yfRef) (oid' := oid') hframe0 hobj hne
      rw [← hcfg'] at e; exact e
    constructor
    · rintro ⟨start, hroot, hrtg⟩
      have main_up : ∀ target : Reference, Relation.ReflTransGen (RefStep cfg) start target →
          FrameReferencable cfg frame.index target ∧ Relation.ReflTransGen (RefStep cfg') start target := by
        intro target htrg
        induction htrg with
        | refl =>
          exact ⟨(FrameReferencable_iff_reflTransGen cfg frame.index start).mpr
            ⟨start, hroot, Relation.ReflTransGen.refl⟩, Relation.ReflTransGen.refl⟩
        | tail hprev hstep ih =>
          obtain ⟨ihreach, ihrtg⟩ := ih
          obtain ⟨oidb, hbeq⟩ := hstep.exists_oid_left
          subst hbeq
          have hbne : oidb ≠ yoid := hoidm_ne oidb ihreach
          have heqB := hobjAtEq oidb hbne
          obtain ⟨objv, hobjAt, hcontains⟩ := hstep
          refine ⟨FrameReferencable.step hobjAt hcontains ihreach, ihrtg.tail ⟨objv, ?_, hcontains⟩⟩
          rw [← heqB]; exact hobjAt
      obtain ⟨_, hup⟩ := main_up ref hrtg
      exact ⟨start, (hfrRootIff start).mp hroot, hup⟩
    · rintro ⟨start, hroot, hrtg⟩
      have hroot_down := (hfrRootIff start).mpr hroot
      have main_down : ∀ target : Reference, Relation.ReflTransGen (RefStep cfg') start target →
          FrameReferencable cfg' frame.index target ∧ Relation.ReflTransGen (RefStep cfg) start target := by
        intro target htrg
        induction htrg with
        | refl =>
          exact ⟨(FrameReferencable_iff_reflTransGen cfg' frame.index start).mpr
            ⟨start, hroot, Relation.ReflTransGen.refl⟩, Relation.ReflTransGen.refl⟩
        | tail hprev hstep ih =>
          obtain ⟨ihreach, ihrtg⟩ := ih
          obtain ⟨oidb, hbeq⟩ := hstep.exists_oid_left
          subst hbeq
          have hbne : oidb ≠ yoid := hoidm_ne' oidb ihreach
          have heqB := hobjAtEq oidb hbne
          obtain ⟨objv, hobjAt, hcontains⟩ := hstep
          refine ⟨FrameReferencable.step hobjAt hcontains ihreach, ihrtg.tail ⟨objv, ?_, hcontains⟩⟩
          rw [heqB]; exact hobjAt
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
    have hoidm_ne : ∀ oidx, FrameReferencable cfg frame.index (Reference.OId oidx) → oidx ≠ yoid := by
      intro oidx hreachx heq
      rw [heq] at hreachx
      have := FrameReferencable_owner_index_le cfg vcfg frame hreachx rid hyloc0 frame0 hframe0_mem hrid.symm
      exact absurd this (Nat.not_le.mpr hltd)
    have hoidm_ne' : ∀ oidx, FrameReferencable cfg' frame.index (Reference.OId oidx) → oidx ≠ yoid := by
      intro oidx hreachx heq
      rw [heq] at hreachx
      have hyloc0' : (Reference.OId yoid).loc? cfg' = some (Location.Rgn rid) := by
        have e := swap_corollary_region_stack_loc_eq vcfg (rid := rid) (yoid := yoid) (region := region)
          (obj := obj) (field := yf.field) (newVal := Reference.OId xoid) (frame0 := frame0)
          (newVarMap := frame0.varMap.insert x yfRef) hframe0 hregion hobj yoid
        rw [← hcfg'] at e
        rw [← e]; exact hyloc0
      obtain ⟨fr0, hfr0, hidx0, hrid0, _⟩ := swap_corollary_frame_transport_up h frame0 hframe0_mem
      have hfr0rid : fr0.regionId = rid := by rw [hrid0, ← hrid]
      have hownerbound := FrameReferencable_owner_index_le cfg' vcfg' frame hreachx rid hyloc0' fr0 hfr0 hfr0rid
      rw [hidx0] at hownerbound
      exact absurd hownerbound (Nat.not_le.mpr hltd)
    have hobjAtEq : ∀ oid', oid' ≠ yoid →
        (Reference.OId oid').objAt? cfg = (Reference.OId oid').objAt? cfg' := by
      intro oid' hne
      have e := swap_corollary_region_stack_objAt_eq_of_ne vcfg (rid := rid) (yoid := yoid) (region := region)
        (obj := obj) (field := yf.field) (newVal := Reference.OId xoid) (frame0 := frame0)
        (newVarMap := frame0.varMap.insert x yfRef) hframe0 hregion hobj (oid' := oid') hne
      rw [← hcfg'] at e; exact e
    constructor
    · rintro ⟨start, hroot, hrtg⟩
      have main_up : ∀ target : Reference, Relation.ReflTransGen (RefStep cfg) start target →
          FrameReferencable cfg frame.index target ∧ Relation.ReflTransGen (RefStep cfg') start target := by
        intro target htrg
        induction htrg with
        | refl =>
          exact ⟨(FrameReferencable_iff_reflTransGen cfg frame.index start).mpr
            ⟨start, hroot, Relation.ReflTransGen.refl⟩, Relation.ReflTransGen.refl⟩
        | tail hprev hstep ih =>
          obtain ⟨ihreach, ihrtg⟩ := ih
          obtain ⟨oidb, hbeq⟩ := hstep.exists_oid_left
          subst hbeq
          have hbne : oidb ≠ yoid := hoidm_ne oidb ihreach
          have heqB := hobjAtEq oidb hbne
          obtain ⟨objv, hobjAt, hcontains⟩ := hstep
          refine ⟨FrameReferencable.step hobjAt hcontains ihreach, ihrtg.tail ⟨objv, ?_, hcontains⟩⟩
          rw [← heqB]; exact hobjAt
      obtain ⟨_, hup⟩ := main_up ref hrtg
      exact ⟨start, (hfrRootIff start).mp hroot, hup⟩
    · rintro ⟨start, hroot, hrtg⟩
      have hroot_down := (hfrRootIff start).mpr hroot
      have main_down : ∀ target : Reference, Relation.ReflTransGen (RefStep cfg') start target →
          FrameReferencable cfg' frame.index target ∧ Relation.ReflTransGen (RefStep cfg) start target := by
        intro target htrg
        induction htrg with
        | refl =>
          exact ⟨(FrameReferencable_iff_reflTransGen cfg' frame.index start).mpr
            ⟨start, hroot, Relation.ReflTransGen.refl⟩, Relation.ReflTransGen.refl⟩
        | tail hprev hstep ih =>
          obtain ⟨ihreach, ihrtg⟩ := ih
          obtain ⟨oidb, hbeq⟩ := hstep.exists_oid_left
          subst hbeq
          have hbne : oidb ≠ yoid := hoidm_ne' oidb ihreach
          have heqB := hobjAtEq oidb hbne
          obtain ⟨objv, hobjAt, hcontains⟩ := hstep
          refine ⟨FrameReferencable.step hobjAt hcontains ihreach, ihrtg.tail ⟨objv, ?_, hcontains⟩⟩
          rw [heqB]; exact hobjAt
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
    have hoidm_ne : ∀ oidx, FrameReferencable cfg frame.index (Reference.OId oidx) → oidx ≠ yoid := by
      intro oidx hreachx heq
      rw [heq] at hreachx
      have := FrameReferencable_owner_index_le cfg vcfg frame hreachx rid hyloc0 frame0 hframe0_mem hrid.symm
      exact absurd this (Nat.not_le.mpr hltd)
    have hoidm_ne' : ∀ oidx, FrameReferencable cfg' frame.index (Reference.OId oidx) → oidx ≠ yoid := by
      intro oidx hreachx heq
      rw [heq] at hreachx
      have hyloc0' : (Reference.OId yoid).loc? cfg' = some (Location.Rgn rid) := by
        have e := swap_corollary_region_stack_loc_eq vcfg (rid := rid) (yoid := yoid) (region := region)
          (obj := obj) (field := yf.field) (newVal := Reference.RId xrid) (frame0 := frame0)
          (newVarMap := frame0.varMap.insert x yfRef) hframe0 hregion hobj yoid
        rw [← hcfg'] at e
        rw [← e]; exact hyloc0
      obtain ⟨fr0, hfr0, hidx0, hrid0, _⟩ := swap_corollary_frame_transport_up h frame0 hframe0_mem
      have hfr0rid : fr0.regionId = rid := by rw [hrid0, ← hrid]
      have hownerbound := FrameReferencable_owner_index_le cfg' vcfg' frame hreachx rid hyloc0' fr0 hfr0 hfr0rid
      rw [hidx0] at hownerbound
      exact absurd hownerbound (Nat.not_le.mpr hltd)
    have hobjAtEq : ∀ oid', oid' ≠ yoid →
        (Reference.OId oid').objAt? cfg = (Reference.OId oid').objAt? cfg' := by
      intro oid' hne
      have e := swap_corollary_region_stack_objAt_eq_of_ne vcfg (rid := rid) (yoid := yoid) (region := region)
        (obj := obj) (field := yf.field) (newVal := Reference.RId xrid) (frame0 := frame0)
        (newVarMap := frame0.varMap.insert x yfRef) hframe0 hregion hobj (oid' := oid') hne
      rw [← hcfg'] at e; exact e
    constructor
    · rintro ⟨start, hroot, hrtg⟩
      have main_up : ∀ target : Reference, Relation.ReflTransGen (RefStep cfg) start target →
          FrameReferencable cfg frame.index target ∧ Relation.ReflTransGen (RefStep cfg') start target := by
        intro target htrg
        induction htrg with
        | refl =>
          exact ⟨(FrameReferencable_iff_reflTransGen cfg frame.index start).mpr
            ⟨start, hroot, Relation.ReflTransGen.refl⟩, Relation.ReflTransGen.refl⟩
        | tail hprev hstep ih =>
          obtain ⟨ihreach, ihrtg⟩ := ih
          obtain ⟨oidb, hbeq⟩ := hstep.exists_oid_left
          subst hbeq
          have hbne : oidb ≠ yoid := hoidm_ne oidb ihreach
          have heqB := hobjAtEq oidb hbne
          obtain ⟨objv, hobjAt, hcontains⟩ := hstep
          refine ⟨FrameReferencable.step hobjAt hcontains ihreach, ihrtg.tail ⟨objv, ?_, hcontains⟩⟩
          rw [← heqB]; exact hobjAt
      obtain ⟨_, hup⟩ := main_up ref hrtg
      exact ⟨start, (hfrRootIff start).mp hroot, hup⟩
    · rintro ⟨start, hroot, hrtg⟩
      have hroot_down := (hfrRootIff start).mpr hroot
      have main_down : ∀ target : Reference, Relation.ReflTransGen (RefStep cfg') start target →
          FrameReferencable cfg' frame.index target ∧ Relation.ReflTransGen (RefStep cfg) start target := by
        intro target htrg
        induction htrg with
        | refl =>
          exact ⟨(FrameReferencable_iff_reflTransGen cfg' frame.index start).mpr
            ⟨start, hroot, Relation.ReflTransGen.refl⟩, Relation.ReflTransGen.refl⟩
        | tail hprev hstep ih =>
          obtain ⟨ihreach, ihrtg⟩ := ih
          obtain ⟨oidb, hbeq⟩ := hstep.exists_oid_left
          subst hbeq
          have hbne : oidb ≠ yoid := hoidm_ne' oidb ihreach
          have heqB := hobjAtEq oidb hbne
          obtain ⟨objv, hobjAt, hcontains⟩ := hstep
          refine ⟨FrameReferencable.step hobjAt hcontains ihreach, ihrtg.tail ⟨objv, ?_, hcontains⟩⟩
          rw [heqB]; exact hobjAt
      obtain ⟨_, hdown⟩ := main_down ref hrtg
      exact ⟨start, hroot_down, hdown⟩
  · -- SWAP-REGION-BRIDGE
    have hyloc0 : (Reference.OId yoid).loc? cfg = some (Location.Rgn yrid) := by
      rw [← hyoid, ← hyrloc]; exact hyrl
    have hswi_eq : cfg'.stackWithIndex = cfg.stackWithIndex := by
      unfold RuntimeConfig.stackWithIndex
      rw [show cfg'.stack = cfg.stack from by rw [hcfg']]
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
    have hoidm_ne : ∀ oidx, FrameReferencable cfg frame.index (Reference.OId oidx) → oidx ≠ yoid := by
      intro oidx hreachx heq
      rw [heq] at hreachx
      have := FrameReferencable_owner_index_le cfg vcfg frame hreachx yrid hyloc0 frame0 hframe0_mem hyridEq.symm
      exact absurd this (Nat.not_le.mpr hltd)
    have hoidm_ne' : ∀ oidx, FrameReferencable cfg' frame.index (Reference.OId oidx) → oidx ≠ yoid := by
      intro oidx hreachx heq
      rw [heq] at hreachx
      have hyloc0' : (Reference.OId yoid).loc? cfg' = some (Location.Rgn yrid) := by
        have e := swap_corollary_region_loc_eq (rid := yrid) (yoid := yoid) (region := region)
          (newRegion := ({ region with bridgeObjectId := yfoid, objMap := region.objMap.insert yoid (obj.insert yf.field (Reference.OId region.bridgeObjectId)) } : Region))
          (obj := obj) (v := obj.insert yf.field (Reference.OId region.bridgeObjectId)) vcfg hregion hobj rfl yoid
        rw [← hcfg'] at e
        rw [← e]; exact hyloc0
      have hframe0_mem' : frame0 ∈ cfg'.stackWithIndex := hswi_eq ▸ hframe0_mem
      have := FrameReferencable_owner_index_le cfg' vcfg' frame hreachx yrid hyloc0' frame0 hframe0_mem' hyridEq.symm
      exact absurd this (Nat.not_le.mpr hltd)
    have hobjAtEq : ∀ oid', oid' ≠ yoid →
        (Reference.OId oid').objAt? cfg = (Reference.OId oid').objAt? cfg' := by
      intro oid' hne
      have e := swap_corollary_region_objAt_eq_of_ne vcfg (rid := yrid) (yoid := yoid) (region := region)
        (obj := obj) (field := yf.field) (newVal := Reference.OId region.bridgeObjectId) (newBridge := yfoid)
        hregion hobj (oid' := oid') hne
      rw [← hcfg'] at e; exact e
    constructor
    · rintro ⟨start, hroot, hrtg⟩
      have main_up : ∀ target : Reference, Relation.ReflTransGen (RefStep cfg) start target →
          FrameReferencable cfg frame.index target ∧ Relation.ReflTransGen (RefStep cfg') start target := by
        intro target htrg
        induction htrg with
        | refl =>
          exact ⟨(FrameReferencable_iff_reflTransGen cfg frame.index start).mpr
            ⟨start, hroot, Relation.ReflTransGen.refl⟩, Relation.ReflTransGen.refl⟩
        | tail hprev hstep ih =>
          obtain ⟨ihreach, ihrtg⟩ := ih
          obtain ⟨oidb, hbeq⟩ := hstep.exists_oid_left
          subst hbeq
          have hbne : oidb ≠ yoid := hoidm_ne oidb ihreach
          have heqB := hobjAtEq oidb hbne
          obtain ⟨objv, hobjAt, hcontains⟩ := hstep
          refine ⟨FrameReferencable.step hobjAt hcontains ihreach, ihrtg.tail ⟨objv, ?_, hcontains⟩⟩
          rw [← heqB]; exact hobjAt
      obtain ⟨_, hup⟩ := main_up ref hrtg
      exact ⟨start, (hfrRootIff start).mp hroot, hup⟩
    · rintro ⟨start, hroot, hrtg⟩
      have hroot_down := (hfrRootIff start).mpr hroot
      have main_down : ∀ target : Reference, Relation.ReflTransGen (RefStep cfg') start target →
          FrameReferencable cfg' frame.index target ∧ Relation.ReflTransGen (RefStep cfg) start target := by
        intro target htrg
        induction htrg with
        | refl =>
          exact ⟨(FrameReferencable_iff_reflTransGen cfg' frame.index start).mpr
            ⟨start, hroot, Relation.ReflTransGen.refl⟩, Relation.ReflTransGen.refl⟩
        | tail hprev hstep ih =>
          obtain ⟨ihreach, ihrtg⟩ := ih
          obtain ⟨oidb, hbeq⟩ := hstep.exists_oid_left
          subst hbeq
          have hbne : oidb ≠ yoid := hoidm_ne' oidb ihreach
          have heqB := hobjAtEq oidb hbne
          obtain ⟨objv, hobjAt, hcontains⟩ := hstep
          refine ⟨FrameReferencable.step hobjAt hcontains ihreach, ihrtg.tail ⟨objv, ?_, hcontains⟩⟩
          rw [heqB]; exact hobjAt
      obtain ⟨_, hdown⟩ := main_down ref hrtg
      exact ⟨start, hroot_down, hdown⟩

