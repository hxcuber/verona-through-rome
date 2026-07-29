import Gc.Model.Mutation.FieldAsgn
import Gc.Model.Preservation.FieldAsgn
import Gc.Model.Preservation.Common
import Gc.Reachability.Validity.Reachable
import Gc.Reachability.Corollaries.Common

-- fieldAsgn never touches a frame's `regionId`/`bridgeVar`/`varMap` anywhere: the STACK branch
-- only replaces a value inside the last frame's own `objMap`, and the REGION branch doesn't touch
-- `cfg.stack` at all. So at every stack position, this whole triple is literally unchanged between
-- cfg and cfg' (only `objMap`, projected away here, can ever differ).
private theorem fieldAsgn_corollary_stack_shape_eq (h : fieldAsgn x yf cfg = some cfg') (n : ℕ) :
    (cfg.stack[n]?).map (fun f => (f.regionId, f.bridgeVar, f.varMap)) =
    (cfg'.stack[n]?).map (fun f => (f.regionId, f.bridgeVar, f.varMap)) := by
  obtain ⟨frame0, hframe0, hcase⟩ := fieldAsgn_cases h
  rcases hcase with
    ⟨oid, oid_y, obj, hxr, hyr, hloc, hobj, hcfg'⟩ |
    ⟨oid, oid_y, rid, region, obj, hxr, hyr, hloc, hregion, hobj, hyloc, hstatus, hfrid, hcfg'⟩
  · obtain ⟨stack_eq, _⟩ := fieldAsgn_corollary_stack_eq hframe0
    set newFrame : Frame :=
      { frame0.toFrame with objMap := frame0.objMap.insert oid (obj.insert x.field (Reference.OId oid_y)) }
      with newFrame_def
    have hcfg'2 : cfg' = { cfg with stack := cfg.stack.dropLast ++ [newFrame] } := by
      rw [hcfg', newFrame_def]
    by_cases hlp : n = cfg.stack.dropLast.length
    · have e1 : cfg.stack[n]? = some frame0.toFrame := by
        conv_lhs => rw [stack_eq, hlp]
        simp
      have e2 : cfg'.stack[n]? = some newFrame := by
        rw [hcfg'2]; dsimp only; rw [hlp]; simp
      rw [e1, e2]; rfl
    · by_cases hlt : n < cfg.stack.dropLast.length
      · have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
          conv_lhs => rw [stack_eq]
          rw [List.getElem?_append_left hlt]
        have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
          rw [hcfg'2]; dsimp only; rw [List.getElem?_append_left hlt]
        rw [e1, e2]
      · have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq]; simp
        have hlen' : cfg'.stack.length = cfg.stack.dropLast.length + 1 := by rw [hcfg'2]; simp
        have e1 : cfg.stack[n]? = none := List.getElem?_eq_none (by omega)
        have e2 : cfg'.stack[n]? = none := List.getElem?_eq_none (by omega)
        rw [e1, e2]
  · rw [hcfg']

private theorem fieldAsgn_corollary_stack_length_eq (h : fieldAsgn x yf cfg = some cfg') :
    cfg'.stack.length = cfg.stack.length := by
  obtain ⟨frame0, hframe0, hcase⟩ := fieldAsgn_cases h
  rcases hcase with
    ⟨oid, oid_y, obj, hxr, hyr, hloc, hobj, hcfg'⟩ |
    ⟨oid, oid_y, rid, region, obj, hxr, hyr, hloc, hregion, hobj, hyloc, hstatus, hfrid, hcfg'⟩
  · obtain ⟨stack_eq, _⟩ := fieldAsgn_corollary_stack_eq hframe0
    rw [hcfg']; dsimp only; rw [stack_eq]; simp
  · rw [hcfg']

-- Any frame membership in cfg'.stackWithIndex transports down to cfg with the SAME index,
-- regionId, bridgeVar and varMap (though possibly a different record, if fieldAsgn's STACK branch
-- mutated exactly that position's own objMap) -- which is everything FrameRoot/CR3 ever read off a
-- frame (never its objMap). Thin wrapper around `Gc.Model.Preservation.Common`'s generic
-- `stackWithIndex_frame_transport_down_of_shape_eq`, instantiated at `proj := fun f => (f.regionId,
-- f.bridgeVar, f.varMap)` -- one field wider than `varAsgn`/`swap`'s own instantiation, since here
-- it's `objMap` (not `varMap`) that's left out.
private theorem fieldAsgn_corollary_frame_transport_down (h : fieldAsgn x yf cfg = some cfg')
    (fr : FrameWithIndex) (hfr : fr ∈ cfg'.stackWithIndex) :
    ∃ fr0 : FrameWithIndex, fr0 ∈ cfg.stackWithIndex ∧ fr0.index = fr.index ∧
      fr0.regionId = fr.regionId ∧ fr0.bridgeVar = fr.bridgeVar ∧ fr0.varMap = fr.varMap := by
  obtain ⟨fr0, hmem, hidx, hproj⟩ :=
    stackWithIndex_frame_transport_down_of_shape_eq
      (proj := fun f => (f.regionId, f.bridgeVar, f.varMap)) (fieldAsgn_corollary_stack_shape_eq h) fr hfr
  injection hproj with hrid heq23
  injection heq23 with hbv hvm
  exact ⟨fr0, hmem, hidx, hrid, hbv, hvm⟩

-- Mirrors fieldAsgn_corollary_frame_transport_down, transporting membership the other way (also a
-- thin wrapper, around `stackWithIndex_frame_transport_up_of_shape_eq`).
private theorem fieldAsgn_corollary_frame_transport_up (h : fieldAsgn x yf cfg = some cfg')
    (fr : FrameWithIndex) (hfr : fr ∈ cfg.stackWithIndex) :
    ∃ fr0 : FrameWithIndex, fr0 ∈ cfg'.stackWithIndex ∧ fr0.index = fr.index ∧
      fr0.regionId = fr.regionId ∧ fr0.bridgeVar = fr.bridgeVar ∧ fr0.varMap = fr.varMap := by
  obtain ⟨fr0, hmem, hidx, hproj⟩ :=
    stackWithIndex_frame_transport_up_of_shape_eq
      (proj := fun f => (f.regionId, f.bridgeVar, f.varMap)) (fieldAsgn_corollary_stack_shape_eq h) fr hfr
  injection hproj with hrid heq23
  injection heq23 with hbv hvm
  exact ⟨fr0, hmem, hidx, hrid, hbv, hvm⟩

-- fieldAsgn's REGION branch also literally leaves cfg.heap's `bridgeObjectId` untouched at every
-- key (only the mutated region's `objMap` changes) -- so a `FrameRoot` bridge witness transports
-- unconditionally regardless of whether the witness frame's own region happens to be the mutated
-- one.
private theorem fieldAsgn_corollary_heap_bridge_eq (h : fieldAsgn x yf cfg = some cfg') (rid0 : RegionId) :
    (cfg.heap.lookup rid0).map Region.bridgeObjectId = (cfg'.heap.lookup rid0).map Region.bridgeObjectId := by
  obtain ⟨frame0, hframe0, hcase⟩ := fieldAsgn_cases h
  rcases hcase with
    ⟨oid, oid_y, obj, hxr, hyr, hloc, hobj, hcfg'⟩ |
    ⟨oid, oid_y, rid, region, obj, hxr, hyr, hloc, hregion, hobj, hyloc, hstatus, hfrid, hcfg'⟩
  · rw [hcfg']
  · rw [hcfg']
    dsimp only
    by_cases hrideq : rid0 = rid
    · subst hrideq
      rw [hregion, AList.lookup_insert]
      rfl
    · rw [AList.lookup_insert_ne hrideq]

-- FrameRoot is completely invariant under fieldAsgn (both branches), for every fid: the STACK
-- branch never touches any varMap/bridgeVar/regionId (only objMap, which FrameRoot never reads),
-- and the REGION branch never touches the stack at all and never touches any bridgeObjectId
-- (only the mutated region's own objMap). Since fieldAsgn's own "frame0" (the last frame) is never
-- structurally special-cased by FrameRoot's definition, no last-position exception is needed here
-- at all (contrast MakeObjStack/MakeObjRegion, which genuinely do change a frame's varMap/heap
-- bridgeObjectId at the last position).
private theorem fieldAsgn_corollary_frameRoot_iff (h : fieldAsgn x yf cfg = some cfg')
    (fid : Index) (start : Reference) : FrameRoot cfg fid start ↔ FrameRoot cfg' fid start := by
  unfold FrameRoot
  constructor
  · rintro (⟨fr, hfr, hidx, var, hlookup⟩ | ⟨fr, hfr, hidx, region1, hlookup, hstart⟩)
    · obtain ⟨fr0, hfr0, hidx0, _, _, hvm⟩ := fieldAsgn_corollary_frame_transport_up h fr hfr
      exact Or.inl ⟨fr0, hfr0, hidx0 ▸ hidx, var, hvm ▸ hlookup⟩
    · obtain ⟨fr0, hfr0, hidx0, hrid0, _, _⟩ := fieldAsgn_corollary_frame_transport_up h fr hfr
      have hheap_eq := fieldAsgn_corollary_heap_bridge_eq h fr.regionId
      rw [hlookup, Option.map_some] at hheap_eq
      obtain ⟨region0, hregion0, hbridge0⟩ := Option.map_eq_some_iff.mp hheap_eq.symm
      refine Or.inr ⟨fr0, hfr0, hidx0 ▸ hidx, region0, ?_, ?_⟩
      · rw [hrid0]; exact hregion0
      · rw [hstart, hbridge0]
  · rintro (⟨fr, hfr, hidx, var, hlookup⟩ | ⟨fr, hfr, hidx, region1, hlookup, hstart⟩)
    · obtain ⟨fr0, hfr0, hidx0, _, _, hvm⟩ := fieldAsgn_corollary_frame_transport_down h fr hfr
      exact Or.inl ⟨fr0, hfr0, hidx0 ▸ hidx, var, hvm ▸ hlookup⟩
    · obtain ⟨fr0, hfr0, hidx0, hrid0, _, _⟩ := fieldAsgn_corollary_frame_transport_down h fr hfr
      have hheap_eq := fieldAsgn_corollary_heap_bridge_eq h fr.regionId
      rw [hlookup, Option.map_some] at hheap_eq
      obtain ⟨region0, hregion0, hbridge0⟩ := Option.map_eq_some_iff.mp hheap_eq
      refine Or.inr ⟨fr0, hfr0, hidx0 ▸ hidx, region0, ?_, ?_⟩
      · rw [hrid0]; exact hregion0
      · rw [hstart, hbridge0]

-- The mutated container's *own* new content on the STACK branch: computed directly from the
-- `hcfg'` construction (frame0's position is found via index-uniqueness, and the new object's
-- value is inserted at the already-present key `oidm`).
private theorem fieldAsgn_corollary_stack_objAt_mutated {cfg cfg' : RuntimeConfig} {frame0 : FrameWithIndex}
    {oidm oidy : ObjectId} {obj : Object} {field : FieldName}
    (hframe0 : cfg.stackWithIndex.getLast? = some frame0) (hobjm : frame0.objMap.lookup oidm = some obj)
    (hlocm : (Reference.OId oidm).loc? cfg = some (Location.Stk frame0.index))
    (hcfg' : cfg' = { cfg with stack := cfg.stack.dropLast ++
      [({ frame0 with objMap := frame0.objMap.insert oidm (obj.insert field (Reference.OId oidy)) } : Frame)] }) :
    (Reference.OId oidm).objAt? cfg' = some (obj.insert field (Reference.OId oidy)) := by
  set newFrame : Frame :=
    { frame0 with objMap := frame0.objMap.insert oidm (obj.insert field (Reference.OId oidy)) } with newFrame_def
  have hlocEqM := fieldAsgn_corollary_stack_loc_eq (field := field) (yRef := Reference.OId oidy) hframe0 hobjm oidm
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
    obtain ⟨stack_eq, hidxeq⟩ := fieldAsgn_corollary_stack_eq hframe0
    rw [List.mapIdx_concat, ← hidxeq]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  rw [swap_corollary_stackWithIndex_find_eq hnewFrame_mem]
  rw [newFrame_def]
  exact AList.lookup_insert (a := oidm) (b := obj.insert field (Reference.OId oidy)) frame0.objMap

-- STACK branch: for any oid' *other* than the mutated container, `objAt?` (not just `loc?`) is
-- unaffected. `loc?` transports via the already-established (unconditional-in-oid')
-- `fieldAsgn_corollary_stack_loc_eq`; the Rgn case is then trivial (heap untouched by the STACK
-- branch), and the Stk case needs one extra step: at the mutated (last) position, the *found*
-- frame's objMap only differs at key `oid` (the container), so lookup at any *other* key is
-- unaffected via `AList.lookup_insert_ne`.
private theorem fieldAsgn_corollary_stack_objAt_eq_of_ne {cfg : RuntimeConfig} {frame : FrameWithIndex}
    {oid : ObjectId} {obj : Object} {field : FieldName} {yRef : Reference}
    (hframe : cfg.stackWithIndex.getLast? = some frame) (hobj : frame.objMap.lookup oid = some obj)
    {oid' : ObjectId} (hne : oid' ≠ oid) :
    (Reference.OId oid').objAt? cfg =
      (Reference.OId oid').objAt? { cfg with stack := cfg.stack.dropLast ++
        [({ frame with objMap := frame.objMap.insert oid (obj.insert field yRef) } : Frame)] } := by
  have hlocEq := fieldAsgn_corollary_stack_loc_eq (field := field) (yRef := yRef) hframe hobj oid'
  set newFrame : Frame := { frame with objMap := frame.objMap.insert oid (obj.insert field yRef) } with newFrame_def
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
      obtain ⟨stack_eq, hidxeq⟩ := fieldAsgn_corollary_stack_eq hframe
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
        rw [newFrame_def]
        exact (AList.lookup_insert_ne hne).symm
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
          have hRnone : List.find? (fun f => f.index == fid0) [({ newFrame with index := frame.index } : FrameWithIndex)]
              = none := by
            simp only [List.find?_cons, List.find?_nil]
            rw [hnotp _ rfl]
          rw [hLnone, hRnone]
        rw [hfindEq]

-- REGION branch: for any oid' *other* than the mutated container, `objAt?` is unaffected. Mirrors
-- the STACK-branch corollary above: `loc?` transports via the unconditional
-- `fieldAsgn_corollary_region_loc_eq`; the Stk case is trivial (stack untouched by the REGION
-- branch), and the Rgn case is simpler than `loc?`'s own proof needed to be -- `AList.lookup` is
-- well-defined regardless of the `entries`-level reordering an already-present-key `insert`
-- causes, so `AList.lookup_insert`/`_insert_ne` suffice directly, no `region_unique` argument
-- needed at this level.
private theorem fieldAsgn_corollary_region_objAt_eq_of_ne {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid oid : ObjectId} {region : Region} {obj : Object} {field : FieldName} {yRef : Reference}
    (hregion : cfg.heap.lookup rid = some region) (hobj : region.objMap.lookup oid = some obj)
    {oid' : ObjectId} (hne : oid' ≠ oid) :
    (Reference.OId oid').objAt? cfg =
      (Reference.OId oid').objAt?
        ({ cfg with heap := cfg.heap.insert rid ({ region with objMap := region.objMap.insert oid (obj.insert field yRef) } : Region) }) := by
  have hlocEq := fieldAsgn_corollary_region_loc_eq (field := field) (yRef := yRef) vcfg hregion hobj oid'
  set newRegion : Region := { region with objMap := region.objMap.insert oid (obj.insert field yRef) }
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

-- The mutated container's own new content on the REGION branch (mirrors
-- fieldAsgn_corollary_stack_objAt_mutated): computed directly from the region-level insert at the
-- already-present key `oid` (the container).
private theorem fieldAsgn_corollary_region_objAt_mutated {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid oid oidy : ObjectId} {region : Region} {obj : Object} {field : FieldName}
    (hregion : cfg.heap.lookup rid = some region) (hobj : region.objMap.lookup oid = some obj)
    (hlocm : (Reference.OId oid).loc? cfg = some (Location.Rgn rid))
    (hcfg' : cfg' = { cfg with heap := cfg.heap.insert rid ({ region with objMap := region.objMap.insert oid (obj.insert field (Reference.OId oidy)) } : Region) }) :
    (Reference.OId oid).objAt? cfg' = some (obj.insert field (Reference.OId oidy)) := by
  set newRegion : Region := { region with objMap := region.objMap.insert oid (obj.insert field (Reference.OId oidy)) }
    with newRegion_def
  have hlocEq := fieldAsgn_corollary_region_loc_eq (field := field) (yRef := Reference.OId oidy) vcfg hregion hobj oid
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
  exact AList.lookup_insert (a := oid) (b := obj.insert field (Reference.OId oidy)) region.objMap

-- `FrameReferencable` is completely unaffected at any position strictly before the mutated (last)
-- one: `fieldAsgn_corollary_frameRoot_iff` already shows `FrameRoot` is unconditional (fieldAsgn
-- only ever touches `objMap`, never `varMap`/`bridgeObjectId`), so the only remaining work is the
-- `RefStep`-chain itself -- which, unlike `fieldAsgn_cr3`'s own `main_claim`, needs NO escape case
-- here: a chain rooted at a suspended frame can never even reach the mutated container in the
-- first place (`FrameReferencable_stk_index_le`/`_owner_index_le` bound any object reachable from a
-- suspended frame's own index, which is strictly below the mutated container's owner index).
-- Packaged here as its own reusable theorem since CR5 (`Gc/Reachability/Validity/CR5.lean`) needs
-- exactly this fact, not CR3's later-frame-implies-earlier-frame shape.
theorem fieldAsgn_corollary_frameReferencable_iff_of_lt (vcfg : ValidConfig cfg) (vcfg' : ValidConfig cfg')
    (h : fieldAsgn xf y cfg = some cfg')
    (frame : FrameWithIndex) (hlt : frame.index < cfg.stack.dropLast.length) (ref : Reference) :
    FrameReferencable cfg frame.index ref ↔ FrameReferencable cfg' frame.index ref := by
  obtain ⟨frame0, hframe0, hcase⟩ := fieldAsgn_cases h
  obtain ⟨stack_eq0, hidx00⟩ := fieldAsgn_corollary_stack_eq hframe0
  rw [← hidx00] at hlt
  have hframeRootIff := fieldAsgn_corollary_frameRoot_iff h frame.index
  rw [FrameReferencable_iff_reflTransGen, FrameReferencable_iff_reflTransGen]
  rcases hcase with
    ⟨oidm, oidy, obj, hxr, hyr, hlocm, hobjm, hcfg'⟩ |
    ⟨oidm, oidy, rid, region, obj, hxr, hyr, hlocm, hregion, hobjm, hyloc, hstatus, hfrid, hcfg'⟩
  · -- STACK branch
    have hlocm' : (Reference.OId oidm).loc? cfg' = some (Location.Stk frame0.index) := by
      have e := fieldAsgn_corollary_stack_loc_eq (field := xf.field) (yRef := Reference.OId oidy) hframe0 hobjm oidm
      rw [← hcfg'] at e
      rw [← e]; exact hlocm
    have hoidm_ne : ∀ oidx, FrameReferencable cfg frame.index (Reference.OId oidx) → oidx ≠ oidm := by
      intro oidx hreachx heq
      subst heq
      have := FrameReferencable_stk_index_le cfg vcfg frame hreachx frame0.index hlocm
      exact absurd this (Nat.not_le.mpr hlt)
    have hoidm_ne' : ∀ oidx, FrameReferencable cfg' frame.index (Reference.OId oidx) → oidx ≠ oidm := by
      intro oidx hreachx heq
      subst heq
      have := FrameReferencable_stk_index_le cfg' vcfg' frame hreachx frame0.index hlocm'
      exact absurd this (Nat.not_le.mpr hlt)
    have hobjAtEq : ∀ oid', oid' ≠ oidm →
        (Reference.OId oid').objAt? cfg = (Reference.OId oid').objAt? cfg' := by
      intro oid' hne
      have e := fieldAsgn_corollary_stack_objAt_eq_of_ne
        (field := xf.field) (yRef := Reference.OId oidy) hframe0 hobjm hne
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
          have hbne : oidb ≠ oidm := hoidm_ne oidb ihreach
          have heqB := hobjAtEq oidb hbne
          obtain ⟨objv, hobjAt, hcontains⟩ := hstep
          refine ⟨FrameReferencable.step hobjAt hcontains ihreach, ihrtg.tail ⟨objv, ?_, hcontains⟩⟩
          rw [← heqB]; exact hobjAt
      obtain ⟨_, hup⟩ := main_up ref hrtg
      exact ⟨start, (hframeRootIff start).mp hroot, hup⟩
    · rintro ⟨start, hroot, hrtg⟩
      have hroot_down := (hframeRootIff start).mpr hroot
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
          have hbne : oidb ≠ oidm := hoidm_ne' oidb ihreach
          have heqB := hobjAtEq oidb hbne
          obtain ⟨objv, hobjAt, hcontains⟩ := hstep
          refine ⟨FrameReferencable.step hobjAt hcontains ihreach, ihrtg.tail ⟨objv, ?_, hcontains⟩⟩
          rw [heqB]; exact hobjAt
      obtain ⟨_, hdown⟩ := main_down ref hrtg
      exact ⟨start, hroot_down, hdown⟩
  · -- REGION branch
    have hlocm' : (Reference.OId oidm).loc? cfg' = some (Location.Rgn rid) := by
      have e := fieldAsgn_corollary_region_loc_eq (field := xf.field) (yRef := Reference.OId oidy) vcfg hregion hobjm oidm
      rw [← hcfg'] at e
      rw [← e]; exact hlocm
    have hframe0_mem : frame0 ∈ cfg.stackWithIndex := List.mem_of_getLast? hframe0
    have hswi_eq : cfg'.stackWithIndex = cfg.stackWithIndex := by
      unfold RuntimeConfig.stackWithIndex
      rw [show cfg'.stack = cfg.stack from by rw [hcfg']]
    have hframe0_mem' : frame0 ∈ cfg'.stackWithIndex := by rw [hswi_eq]; exact hframe0_mem
    have hoidm_ne : ∀ oidx, FrameReferencable cfg frame.index (Reference.OId oidx) → oidx ≠ oidm := by
      intro oidx hreachx heq
      subst heq
      have := FrameReferencable_owner_index_le cfg vcfg frame hreachx rid hlocm frame0 hframe0_mem hfrid.symm
      exact absurd this (Nat.not_le.mpr hlt)
    have hoidm_ne' : ∀ oidx, FrameReferencable cfg' frame.index (Reference.OId oidx) → oidx ≠ oidm := by
      intro oidx hreachx heq
      subst heq
      have := FrameReferencable_owner_index_le cfg' vcfg' frame hreachx rid hlocm' frame0 hframe0_mem' hfrid.symm
      exact absurd this (Nat.not_le.mpr hlt)
    have hobjAtEq : ∀ oid', oid' ≠ oidm →
        (Reference.OId oid').objAt? cfg = (Reference.OId oid').objAt? cfg' := by
      intro oid' hne
      have e := fieldAsgn_corollary_region_objAt_eq_of_ne vcfg
        (field := xf.field) (yRef := Reference.OId oidy) hregion hobjm hne
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
          have hbne : oidb ≠ oidm := hoidm_ne oidb ihreach
          have heqB := hobjAtEq oidb hbne
          obtain ⟨objv, hobjAt, hcontains⟩ := hstep
          refine ⟨FrameReferencable.step hobjAt hcontains ihreach, ihrtg.tail ⟨objv, ?_, hcontains⟩⟩
          rw [← heqB]; exact hobjAt
      obtain ⟨_, hup⟩ := main_up ref hrtg
      exact ⟨start, (hframeRootIff start).mp hroot, hup⟩
    · rintro ⟨start, hroot, hrtg⟩
      have hroot_down := (hframeRootIff start).mpr hroot
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
          have hbne : oidb ≠ oidm := hoidm_ne' oidb ihreach
          have heqB := hobjAtEq oidb hbne
          obtain ⟨objv, hobjAt, hcontains⟩ := hstep
          refine ⟨FrameReferencable.step hobjAt hcontains ihreach, ihrtg.tail ⟨objv, ?_, hcontains⟩⟩
          rw [heqB]; exact hobjAt
      obtain ⟨_, hdown⟩ := main_down ref hrtg
      exact ⟨start, hroot_down, hdown⟩

theorem fieldAsgn_cr3 : ValidReachableConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  CR3 cfg' := by
  intro vrcfg h
  have vcfg := vrcfg.toValidConfig
  have vcfg' := fieldAsgn_valid vcfg h
  obtain ⟨frame0, hframe0, hcase⟩ := fieldAsgn_cases h
  obtain ⟨stack_eq0, hidx00⟩ := fieldAsgn_corollary_stack_eq hframe0
  have hframe0_max : ∀ fr : FrameWithIndex, fr ∈ cfg.stackWithIndex → fr.index ≤ frame0.index := by
    intro fr hfr
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr
    have hidxfr : fr.index = n := by rw [← hfeq]
    have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq0]; simp
    rw [hlen] at hn
    rw [hidxfr, hidx00]
    exact Nat.le_of_lt_succ hn
  unfold CR3
  intro frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  obtain ⟨frameD, hframeDMem, hidxD, hridD, _, _⟩ := fieldAsgn_corollary_frame_transport_down h frame hframeMem
  obtain ⟨frameD', hframeD'Mem, hidxD', hridD', _, _⟩ := fieldAsgn_corollary_frame_transport_down h frame' hframe'Mem
  have hltD : frameD.index < frameD'.index := by rw [hidxD, hidxD']; exact hlt
  have hD'_le_frame0 : frameD'.index ≤ frame0.index := hframe0_max frameD' hframeD'Mem
  have hD_lt_frame0 : frameD.index < frame0.index := lt_of_lt_of_le hltD hD'_le_frame0
  have hframe_lt_frame0 : frame.index < frame0.index := by rw [← hidxD]; exact hD_lt_frame0
  rcases hcase with
    ⟨oidm, oidy, obj, hxr, hyr, hlocm, hobjm, hcfg'⟩ |
    ⟨oidm, oidy, rid, region, obj, hxr, hyr, hlocm, hregion, hobjm, hyloc, hstatus, hfrid, hcfg'⟩
  · -- STACK branch
    have hlocEq0 :=
      fieldAsgn_corollary_stack_loc_eq (field := x.field) (yRef := Reference.OId oidy) hframe0 hobjm oid
    rw [← hcfg'] at hlocEq0
    have hlocDown : (Reference.OId oid).loc? cfg = some (Location.Rgn frameD.regionId) := by
      rw [hridD, hlocEq0]; exact hloc
    have hoidAtM := fieldAsgn_corollary_stack_objAt_mutated hframe0 hobjm hlocm hcfg'
    have hoidAtM_cfg : (Reference.OId oidm).objAt? cfg = some obj := by
      unfold Reference.objAt?
      dsimp only
      rw [hlocm]
      dsimp only
      have hframe0_mem : frame0 ∈ cfg.stackWithIndex := List.mem_of_getLast? hframe0
      rw [swap_corollary_stackWithIndex_find_eq hframe0_mem]
      exact hobjm
    have hoidm_ne : ∀ oidx, FrameReferencable cfg frame.index (Reference.OId oidx) → oidx ≠ oidm := by
      intro oidx hreachx heq
      subst heq
      have := FrameReferencable_stk_index_le cfg vcfg frame hreachx frame0.index hlocm
      exact absurd this (Nat.not_le.mpr hframe_lt_frame0)
    have main_claim : ∀ start', Relation.ReflTransGen (RefStep cfg') start' (Reference.OId oid) →
        Relation.ReflTransGen (RefStep cfg) start' (Reference.OId oid) ∨
          FrameReferencable cfg frameD.index (Reference.OId oid) := by
      intro start' hrtg'
      induction hrtg' using Relation.ReflTransGen.head_induction_on with
      | refl => left; exact Relation.ReflTransGen.refl
      | head hstep hrest ih =>
        rename_i a c
        rcases ih with ihchain | ihgoal
        · obtain ⟨oida, ha_eq⟩ := hstep.exists_oid_left
          subst ha_eq
          have hc_oid : ∃ oidc, c = Reference.OId oidc := by
            rcases hrest.cases_head with heq | ⟨d, hcd, _⟩
            · exact ⟨oid, heq⟩
            · exact hcd.exists_oid_left
          obtain ⟨oidc, hc_eq⟩ := hc_oid
          subst hc_eq
          by_cases haeq : oida = oidm
          · by_cases hceq : oidc = oidy
            · -- ESCAPE: the mutated container's *new* field write is exactly the value read out
              -- of `yf` -- since that value was already resolvable pre-mutation, its own natural
              -- root gives an independent path to `oid` that doesn't depend on this hop at all.
              obtain ⟨frameY, hframeYMem, hrootY⟩ := resolveV_frameRoot hyr
              rw [hceq] at ihchain
              have hreachY : FrameReferencable cfg frameY.index (Reference.OId oid) := by
                rw [FrameReferencable_iff_reflTransGen]
                exact ⟨Reference.OId oidy, hrootY, ihchain⟩
              have hownerbound := FrameReferencable_owner_index_le cfg vcfg frameY hreachY frameD.regionId
                hlocDown frameD hframeDMem rfl
              by_cases heqidx : frameD.index = frameY.index
              · right
                have hFYeq : frameY = frameD :=
                  swap_corollary_stackWithIndex_index_inj hframeYMem hframeDMem heqidx.symm
                rw [← hFYeq]; exact hreachY
              · right
                have hltidx : frameD.index < frameY.index := lt_of_le_of_ne hownerbound heqidx
                exact vrcfg.cr3 frameD hframeDMem frameY hframeYMem hltidx oid hlocDown hreachY
            · left
              have hstep_cfg : RefStep cfg (Reference.OId oida) (Reference.OId oidc) := by
                rw [haeq]
                refine ⟨obj, hoidAtM_cfg, ?_⟩
                obtain ⟨objv, hobjAt, hcontains⟩ := hstep
                rw [haeq, hoidAtM] at hobjAt
                injection hobjAt with hobjAt_eq
                rw [← hobjAt_eq] at hcontains
                have hmem := List.contains_iff_mem.mp hcontains
                rcases fieldAsgn_corollary_object_insert_refs_mem hmem with heq | hmem'
                · injection heq with heq'; exact absurd heq' hceq
                · exact List.contains_iff_mem.mpr hmem'
              exact ihchain.head hstep_cfg
          · left
            have hstep_cfg : RefStep cfg (Reference.OId oida) (Reference.OId oidc) := by
              obtain ⟨objv, hobjAt, hcontains⟩ := hstep
              have heqA := fieldAsgn_corollary_stack_objAt_eq_of_ne
                (field := x.field) (yRef := Reference.OId oidy) (oid' := oida) hframe0 hobjm haeq
              rw [← hcfg'] at heqA
              exact ⟨objv, heqA ▸ hobjAt, hcontains⟩
            exact ihchain.head hstep_cfg
        · right; exact ihgoal
    have hconcDown : FrameReferencable cfg frame.index (Reference.OId oid) := by
      rw [FrameReferencable_iff_reflTransGen] at hreach
      obtain ⟨start, hroot, hrtg⟩ := hreach
      rcases main_claim start hrtg with hchain | hgoal
      · have hrootDown : FrameRoot cfg frame'.index start :=
          (fieldAsgn_corollary_frameRoot_iff h frame'.index start).mpr hroot
        have hreachD' : FrameReferencable cfg frameD'.index (Reference.OId oid) := by
          rw [hidxD']
          exact (FrameReferencable_iff_reflTransGen cfg frame'.index (Reference.OId oid)).mpr ⟨start, hrootDown, hchain⟩
        have hres := vrcfg.cr3 frameD hframeDMem frameD' hframeD'Mem hltD oid hlocDown hreachD'
        rwa [hidxD] at hres
      · rwa [hidxD] at hgoal
    rw [FrameReferencable_iff_reflTransGen] at hconcDown
    obtain ⟨start2, hroot2, hrtg2⟩ := hconcDown
    have main_claim_up : ∀ target3 : Reference, Relation.ReflTransGen (RefStep cfg) start2 target3 →
        ∀ oid3, target3 = Reference.OId oid3 →
          FrameReferencable cfg frame.index (Reference.OId oid3) ∧
            Relation.ReflTransGen (RefStep cfg') start2 (Reference.OId oid3) := by
      intro target3 hrtg3
      induction hrtg3 with
      | refl =>
        intro oid3 heq3
        refine ⟨?_, by rw [← heq3]⟩
        rw [FrameReferencable_iff_reflTransGen, ← heq3]
        exact ⟨start2, hroot2, Relation.ReflTransGen.refl⟩
      | tail hprev hstep ih =>
        intro oid3 heq3
        obtain ⟨oidb, hb_eq⟩ := hstep.exists_oid_left
        obtain ⟨ihreach, ihrtg⟩ := ih oidb hb_eq
        have hbne : oidb ≠ oidm := hoidm_ne oidb ihreach
        have heqB := fieldAsgn_corollary_stack_objAt_eq_of_ne
          (field := x.field) (yRef := Reference.OId oidy) (oid' := oidb) hframe0 hobjm hbne
        rw [← hcfg'] at heqB
        obtain ⟨objv, hobjAt, hcontains⟩ := hstep
        rw [hb_eq] at hobjAt
        rw [heq3] at hcontains
        refine ⟨FrameReferencable.step hobjAt hcontains ihreach, ihrtg.tail ⟨objv, ?_, hcontains⟩⟩
        rw [← heqB]; exact hobjAt
    have hup := main_claim_up (Reference.OId oid) hrtg2 oid rfl
    rw [FrameReferencable_iff_reflTransGen]
    exact ⟨start2, (fieldAsgn_corollary_frameRoot_iff h frame.index start2).mp hroot2, hup.2⟩
  · -- REGION branch
    have hlocEq0 :=
      fieldAsgn_corollary_region_loc_eq (field := x.field) (yRef := Reference.OId oidy) vcfg hregion hobjm oid
    rw [← hcfg'] at hlocEq0
    have hlocDown : (Reference.OId oid).loc? cfg = some (Location.Rgn frameD.regionId) := by
      rw [hridD, hlocEq0]; exact hloc
    have hoidAtM := fieldAsgn_corollary_region_objAt_mutated vcfg hregion hobjm hlocm hcfg'
    have hoidAtM_cfg : (Reference.OId oidm).objAt? cfg = some obj := by
      unfold Reference.objAt?
      dsimp only
      rw [hlocm]
      dsimp only
      rw [hregion]
      exact hobjm
    have hframe0_mem : frame0 ∈ cfg.stackWithIndex := List.mem_of_getLast? hframe0
    have hoidm_ne : ∀ oidx, FrameReferencable cfg frame.index (Reference.OId oidx) → oidx ≠ oidm := by
      intro oidx hreachx heq
      subst heq
      have := FrameReferencable_owner_index_le cfg vcfg frame hreachx rid hlocm frame0 hframe0_mem hfrid.symm
      exact absurd this (Nat.not_le.mpr hframe_lt_frame0)
    have main_claim : ∀ start', Relation.ReflTransGen (RefStep cfg') start' (Reference.OId oid) →
        Relation.ReflTransGen (RefStep cfg) start' (Reference.OId oid) ∨
          FrameReferencable cfg frameD.index (Reference.OId oid) := by
      intro start' hrtg'
      induction hrtg' using Relation.ReflTransGen.head_induction_on with
      | refl => left; exact Relation.ReflTransGen.refl
      | head hstep hrest ih =>
        rename_i a c
        rcases ih with ihchain | ihgoal
        · obtain ⟨oida, ha_eq⟩ := hstep.exists_oid_left
          subst ha_eq
          have hc_oid : ∃ oidc, c = Reference.OId oidc := by
            rcases hrest.cases_head with heq | ⟨d, hcd, _⟩
            · exact ⟨oid, heq⟩
            · exact hcd.exists_oid_left
          obtain ⟨oidc, hc_eq⟩ := hc_oid
          subst hc_eq
          by_cases haeq : oida = oidm
          · by_cases hceq : oidc = oidy
            · -- ESCAPE
              obtain ⟨frameY, hframeYMem, hrootY⟩ := resolveV_frameRoot hyr
              rw [hceq] at ihchain
              have hreachY : FrameReferencable cfg frameY.index (Reference.OId oid) := by
                rw [FrameReferencable_iff_reflTransGen]
                exact ⟨Reference.OId oidy, hrootY, ihchain⟩
              have hownerbound := FrameReferencable_owner_index_le cfg vcfg frameY hreachY frameD.regionId
                hlocDown frameD hframeDMem rfl
              by_cases heqidx : frameD.index = frameY.index
              · right
                have hFYeq : frameY = frameD :=
                  swap_corollary_stackWithIndex_index_inj hframeYMem hframeDMem heqidx.symm
                rw [← hFYeq]; exact hreachY
              · right
                have hltidx : frameD.index < frameY.index := lt_of_le_of_ne hownerbound heqidx
                exact vrcfg.cr3 frameD hframeDMem frameY hframeYMem hltidx oid hlocDown hreachY
            · left
              have hstep_cfg : RefStep cfg (Reference.OId oida) (Reference.OId oidc) := by
                rw [haeq]
                refine ⟨obj, hoidAtM_cfg, ?_⟩
                obtain ⟨objv, hobjAt, hcontains⟩ := hstep
                rw [haeq, hoidAtM] at hobjAt
                injection hobjAt with hobjAt_eq
                rw [← hobjAt_eq] at hcontains
                have hmem := List.contains_iff_mem.mp hcontains
                rcases fieldAsgn_corollary_object_insert_refs_mem hmem with heq | hmem'
                · injection heq with heq'; exact absurd heq' hceq
                · exact List.contains_iff_mem.mpr hmem'
              exact ihchain.head hstep_cfg
          · left
            have hstep_cfg : RefStep cfg (Reference.OId oida) (Reference.OId oidc) := by
              obtain ⟨objv, hobjAt, hcontains⟩ := hstep
              have heqA := fieldAsgn_corollary_region_objAt_eq_of_ne vcfg
                (field := x.field) (yRef := Reference.OId oidy) (oid' := oida) hregion hobjm haeq
              rw [← hcfg'] at heqA
              exact ⟨objv, heqA ▸ hobjAt, hcontains⟩
            exact ihchain.head hstep_cfg
        · right; exact ihgoal
    have hconcDown : FrameReferencable cfg frame.index (Reference.OId oid) := by
      rw [FrameReferencable_iff_reflTransGen] at hreach
      obtain ⟨start, hroot, hrtg⟩ := hreach
      rcases main_claim start hrtg with hchain | hgoal
      · have hrootDown : FrameRoot cfg frame'.index start :=
          (fieldAsgn_corollary_frameRoot_iff h frame'.index start).mpr hroot
        have hreachD' : FrameReferencable cfg frameD'.index (Reference.OId oid) := by
          rw [hidxD']
          exact (FrameReferencable_iff_reflTransGen cfg frame'.index (Reference.OId oid)).mpr ⟨start, hrootDown, hchain⟩
        have hres := vrcfg.cr3 frameD hframeDMem frameD' hframeD'Mem hltD oid hlocDown hreachD'
        rwa [hidxD] at hres
      · rwa [hidxD] at hgoal
    rw [FrameReferencable_iff_reflTransGen] at hconcDown
    obtain ⟨start2, hroot2, hrtg2⟩ := hconcDown
    have main_claim_up : ∀ target3 : Reference, Relation.ReflTransGen (RefStep cfg) start2 target3 →
        ∀ oid3, target3 = Reference.OId oid3 →
          FrameReferencable cfg frame.index (Reference.OId oid3) ∧
            Relation.ReflTransGen (RefStep cfg') start2 (Reference.OId oid3) := by
      intro target3 hrtg3
      induction hrtg3 with
      | refl =>
        intro oid3 heq3
        refine ⟨?_, by rw [← heq3]⟩
        rw [FrameReferencable_iff_reflTransGen, ← heq3]
        exact ⟨start2, hroot2, Relation.ReflTransGen.refl⟩
      | tail hprev hstep ih =>
        intro oid3 heq3
        obtain ⟨oidb, hb_eq⟩ := hstep.exists_oid_left
        obtain ⟨ihreach, ihrtg⟩ := ih oidb hb_eq
        have hbne : oidb ≠ oidm := hoidm_ne oidb ihreach
        have heqB := fieldAsgn_corollary_region_objAt_eq_of_ne vcfg
          (field := x.field) (yRef := Reference.OId oidy) (oid' := oidb) hregion hobjm hbne
        rw [← hcfg'] at heqB
        obtain ⟨objv, hobjAt, hcontains⟩ := hstep
        rw [hb_eq] at hobjAt
        rw [heq3] at hcontains
        refine ⟨FrameReferencable.step hobjAt hcontains ihreach, ihrtg.tail ⟨objv, ?_, hcontains⟩⟩
        rw [← heqB]; exact hobjAt
    have hup := main_claim_up (Reference.OId oid) hrtg2 oid rfl
    rw [FrameReferencable_iff_reflTransGen]
    exact ⟨start2, (fieldAsgn_corollary_frameRoot_iff h frame.index start2).mp hroot2, hup.2⟩

theorem fieldAsgn_reachable_valid : ValidReachableConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  ValidReachableConfig cfg' := by
  intro vrcfg h
  exact { fieldAsgn_valid vrcfg.toValidConfig h with cr3 := fieldAsgn_cr3 vrcfg h }
