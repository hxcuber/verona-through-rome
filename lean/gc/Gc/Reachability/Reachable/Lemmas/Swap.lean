module

public import Gc.Model.Types
public import Gc.Model.Helpers
public import Gc.Model.Validity
public import Gc.Model.Mutation.Mutation
public import Gc.Model.Preservation
public import Gc.Reachability.Reachable.Semantics
public import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.Def
public import Gc.Reachability.Reachable.Lemmas.Common
public import Gc.Reachability.Reachable.Lemmas.VarAsgn
public import Gc.Reachability.Reachable.Lemmas.FieldAsgn
public import Gc.Reachability.Reachable.Lemmas.Merge

@[expose] public section

-- Replacing the last frame by `g` leaves `objAt? o` unchanged when `loc? o` and `g`'s entry at `o` agree.
private theorem objAt_last_frame_eq {cfg : RuntimeConfig} {frame : FrameWithIndex} {g : Frame} {o : ObjectId}
    (hframe : cfg.stackWithIndex.getLast? = some frame)
    (hloc : (Reference.OId o).loc? cfg = (Reference.OId o).loc? { cfg with stack := cfg.stack.dropLast ++ [g] })
    (hlk : g.objMap.lookup o = frame.objMap.lookup o) :
    (Reference.OId o).objAt? cfg = (Reference.OId o).objAt? { cfg with stack := cfg.stack.dropLast ++ [g] } := by
  simp only [Reference.objAt?, ← hloc]
  rcases (Reference.OId o).loc? cfg with _ | _ | fid
  · rfl
  · rfl
  dsimp only
  rw [stackWithIndex_find_index_eq_getElem, stackWithIndex_find_index_eq_getElem,
    stackWithIndex_eq_of_getLast? (stack_getLast?_of_stackWithIndex_getLast? hframe), stackWithIndex_mk_append_singleton]
  simp only [List.getElem?_append, List.getElem?_singleton]
  split_ifs <;> simp [hlk]

-- Inserting `newRegion` at `rid` leaves `objAt? o` unchanged when `loc? o` and the new entry at `o` agree.
private theorem objAt_heap_insert_eq {cfg : RuntimeConfig} {rid : RegionId} {region newRegion : Region}
    {o : ObjectId} (hregion : cfg.heap.lookup rid = some region)
    (hloc : (Reference.OId o).loc? cfg = (Reference.OId o).loc? { cfg with heap := cfg.heap.insert rid newRegion })
    (hlk : newRegion.objMap.lookup o = region.objMap.lookup o) :
    (Reference.OId o).objAt? cfg = (Reference.OId o).objAt? { cfg with heap := cfg.heap.insert rid newRegion } := by
  simp only [Reference.objAt?, ← hloc]
  rcases (Reference.OId o).loc? cfg with _ | ridX | _
  · rfl
  · by_cases hridx : ridX = rid
    · subst hridx
      simp [hregion, hlk]
    · simp [AList.lookup_insert_ne hridx]
  · rfl

-- A varMap-only change to the last frame never affects `objAt?`.
private theorem swap_varmap_objAt_eq {cfg : RuntimeConfig} {frame : FrameWithIndex} {newVarMap : VarMap}
    (hframe : cfg.stackWithIndex.getLast? = some frame) (oid' : ObjectId) :
    (Reference.OId oid').objAt? cfg =
      (Reference.OId oid').objAt? { cfg with stack := cfg.stack.dropLast ++
        [({ frame with varMap := newVarMap } : Frame)] } :=
  objAt_last_frame_eq hframe (swap_corollary_stack_varmap_loc_eq hframe oid') rfl

-- The mutated container's new content on REGION branches, generalized over `newBridge`.
private theorem swap_region_objAt_mutated {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid yoid : ObjectId} {region : Region} {obj : Object} {field : FieldName} {newVal : Reference}
    {newBridge : ObjectId}
    (hregion : cfg.heap.lookup rid = some region) (hobj : region.objMap.lookup yoid = some obj)
    (hlocm : (Reference.OId yoid).loc? cfg = some (Location.Rgn rid)) :
    (Reference.OId yoid).objAt? { cfg with heap := cfg.heap.insert rid ({ region with bridgeObjectId := newBridge, objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) } = some (obj.insert field newVal) := by
  simp [Reference.objAt?, ← swap_corollary_region_loc_eq (newRegion := { region with bridgeObjectId := newBridge, objMap := region.objMap.insert yoid (obj.insert field newVal) })
    vcfg hregion hobj rfl, hlocm]

-- REGION-touching branches: for any oid' other than the mutated container, `objAt?` is unaffected.
private theorem swap_region_objAt_eq_of_ne {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid yoid : ObjectId} {region : Region} {obj : Object} {field : FieldName} {newVal : Reference}
    {newBridge : ObjectId}
    (hregion : cfg.heap.lookup rid = some region) (hobj : region.objMap.lookup yoid = some obj)
    {oid' : ObjectId} (hne : oid' ≠ yoid) :
    (Reference.OId oid').objAt? cfg =
      (Reference.OId oid').objAt? ({ cfg with heap := cfg.heap.insert rid ({ region with bridgeObjectId := newBridge, objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) }) :=
  objAt_heap_insert_eq hregion (swap_corollary_region_loc_eq vcfg hregion hobj rfl oid') (AList.lookup_insert_ne hne)

-- Composes the region `objMap` change with the simultaneous (but `objMap`-irrelevant) stack `varMap` change.
theorem swap_region_stack_loc_eq {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid yoid : ObjectId} {region : Region} {obj : Object} {field : FieldName} {newVal : Reference}
    {frame0 : FrameWithIndex} {newVarMap : VarMap}
    (hframe0 : cfg.stackWithIndex.getLast? = some frame0)
    (hregion : cfg.heap.lookup rid = some region) (hobj : region.objMap.lookup yoid = some obj)
    (oid' : ObjectId) :
    (Reference.OId oid').loc? cfg =
      (Reference.OId oid').loc? ({ stack := cfg.stack.dropLast ++ [({ frame0 with varMap := newVarMap } : Frame)], heap := cfg.heap.insert rid ({ region with objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) } : RuntimeConfig) :=
  (swap_corollary_region_loc_eq (newRegion := { region with objMap := region.objMap.insert yoid (obj.insert field newVal) })
    vcfg hregion hobj rfl oid').trans
    (swap_corollary_stack_varmap_loc_eq (cfg := { cfg with heap := cfg.heap.insert rid _ }) hframe0 oid')

-- swap never touches a frame's `regionId`/`bridgeVar` anywhere.
private theorem swap_stack_shape_eq (h : swap x yf cfg = some cfg') (n : ℕ) :
    (cfg.stack[n]?).map (fun f => (f.regionId, f.bridgeVar)) =
    (cfg'.stack[n]?).map (fun f => (f.regionId, f.bridgeVar)) := by
  obtain ⟨frame, hframe, -, -, -, -, -, -, -, -, ⟨-, -, -, -, -, -, -, -, rfl⟩ |
    ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, rfl⟩ | ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, rfl⟩ |
    ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, rfl⟩⟩ := swap_cases h
  all_goals try rfl
  all_goals
    conv_lhs => rw [(stack_eq_of_stackWithIndex_getLast? hframe).1]
    simp only [List.getElem?_append, List.getElem?_singleton]
    split_ifs <;> simp

-- Frame membership in `cfg'.stackWithIndex` transports down to `cfg`, same index/regionId/bridgeVar.
theorem swap_frame_transport_down (h : swap x yf cfg = some cfg')
    (fr : FrameWithIndex) (hfr : fr ∈ cfg'.stackWithIndex) :
    ∃ fr0 : FrameWithIndex, fr0 ∈ cfg.stackWithIndex ∧ fr0.index = fr.index ∧
      fr0.regionId = fr.regionId ∧ fr0.bridgeVar = fr.bridgeVar := by
  obtain ⟨fr0, hmem, hidx, hproj⟩ :=
    stackWithIndex_frame_transport_down_of_shape_eq (proj := fun f => (f.regionId, f.bridgeVar))
      (swap_stack_shape_eq h) fr hfr
  exact ⟨fr0, hmem, hidx, Prod.ext_iff.mp hproj⟩

-- Frame membership in `cfg.stackWithIndex` transports up to `cfg'`, same index/regionId/bridgeVar.
theorem swap_frame_transport_up (h : swap x yf cfg = some cfg')
    (fr : FrameWithIndex) (hfr : fr ∈ cfg.stackWithIndex) :
    ∃ fr0 : FrameWithIndex, fr0 ∈ cfg'.stackWithIndex ∧ fr0.index = fr.index ∧
      fr0.regionId = fr.regionId ∧ fr0.bridgeVar = fr.bridgeVar := by
  obtain ⟨fr0, hmem, hidx, hproj⟩ :=
    stackWithIndex_frame_transport_up_of_shape_eq (proj := fun f => (f.regionId, f.bridgeVar))
      (swap_stack_shape_eq h) fr hfr
  exact ⟨fr0, hmem, hidx, Prod.ext_iff.mp hproj⟩


-- STACK branch: for any oid' other than the mutated container, `objAt?` is unaffected.
private theorem swap_stack_objAt_eq_of_ne {cfg : RuntimeConfig} {frame0 : FrameWithIndex}
    {yoid : ObjectId} {obj : Object} {field : FieldName} {newVal : Reference} {newVarMap : VarMap}
    (hframe0 : cfg.stackWithIndex.getLast? = some frame0) (hobj : frame0.objMap.lookup yoid = some obj)
    {oid' : ObjectId} (hne : oid' ≠ yoid) :
    (Reference.OId oid').objAt? cfg =
      (Reference.OId oid').objAt? { cfg with stack := cfg.stack.dropLast ++
        [({ frame0 with varMap := newVarMap, objMap := frame0.objMap.insert yoid (obj.insert field newVal) } :
          Frame)] } :=
  objAt_last_frame_eq hframe0 (swap_corollary_stack_loc_eq hframe0 hobj oid') (AList.lookup_insert_ne hne)

-- `ReachableStep` agrees for every source other than `OId yoid` once `objAt?` (off `yoid`) and `RId` steps agree.
private theorem step_iff_of_ne_of_objAt {cfg cfg' : RuntimeConfig} {yoid : ObjectId}
    (hobjAt : ∀ o, o ≠ yoid → (Reference.OId o).objAt? cfg = (Reference.OId o).objAt? cfg')
    (hrid : ∀ r b, ReachableStep cfg (Reference.RId r) b ↔ ReachableStep cfg' (Reference.RId r) b) :
    ∀ a : Reference, a ≠ Reference.OId yoid → ∀ b : Reference, ReachableStep cfg a b ↔ ReachableStep cfg' a b := by
  rintro (r | o) hane b
  · exact hrid r b
  · rw [ReachableStep_oid_iff, ReachableStep_oid_iff, hobjAt o (by rintro rfl; exact hane rfl)]

-- `RId` steps agree after replacing an Open region by another Open region (neither ever steps).
private theorem rid_step_iff_of_insert_open {cfg cfg' : RuntimeConfig} {rid : RegionId} {region newRegion : Region}
    (hregion : cfg.heap.lookup rid = some region) (hstatus : region.status = Status.Open)
    (hheap : cfg'.heap = cfg.heap.insert rid newRegion) (hnew : newRegion.status = Status.Open)
    (r : RegionId) (b : Reference) : ReachableStep cfg (Reference.RId r) b ↔ ReachableStep cfg' (Reference.RId r) b := by
  by_cases hr : r = rid
  · subst hr
    exact iff_of_false (open_rid_no_step hregion hstatus) (open_rid_no_step (hheap ▸ AList.lookup_insert cfg.heap) hnew)
  · simp only [ReachableStep_rid_iff, hheap, AList.lookup_insert_ne hr]

-- `ReachableStep` agrees for any source other than the mutated container (STACK branch): heap untouched, so `RId` hops are trivial.
theorem swap_stack_step_iff_of_ne {cfg cfg' : RuntimeConfig} {frame0 : FrameWithIndex}
    {yoid : ObjectId} {obj : Object} {field : FieldName} {newVal : Reference} {newVarMap : VarMap}
    (hframe0 : cfg.stackWithIndex.getLast? = some frame0) (hobj : frame0.objMap.lookup yoid = some obj)
    (hcfg' : cfg' = { cfg with stack := cfg.stack.dropLast ++
      [({ frame0 with varMap := newVarMap, objMap := frame0.objMap.insert yoid (obj.insert field newVal) } :
        Frame)] }) :
    ∀ a : Reference, a ≠ Reference.OId yoid → ∀ b : Reference, ReachableStep cfg a b ↔ ReachableStep cfg' a b := by
  subst hcfg'
  exact step_iff_of_ne_of_objAt (fun _ hne => swap_stack_objAt_eq_of_ne hframe0 hobj hne) fun _ _ => Iff.rfl

-- REGION-touching branches: the touched region is always Open (L2), so no `RId` hop is possible.
theorem swap_region_stack_step_iff_of_ne {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid yoid : ObjectId} {region : Region} {obj : Object} {field : FieldName} {newVal : Reference}
    {frame0 : FrameWithIndex} {newVarMap : VarMap}
    (hframe0 : cfg.stackWithIndex.getLast? = some frame0)
    (hregion : cfg.heap.lookup rid = some region) (hobj : region.objMap.lookup yoid = some obj)
    (hstatus : region.status = Status.Open)
    (hcfg' : cfg' = { stack := cfg.stack.dropLast ++ [({ frame0 with varMap := newVarMap } : Frame)], heap := cfg.heap.insert rid ({ region with objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) }) :
    ∀ a : Reference, a ≠ Reference.OId yoid → ∀ b : Reference, ReachableStep cfg a b ↔ ReachableStep cfg' a b := by
  subst hcfg'
  exact step_iff_of_ne_of_objAt (fun _ hne => (swap_region_objAt_eq_of_ne (newBridge := region.bridgeObjectId) vcfg
    hregion hobj hne).trans (swap_varmap_objAt_eq (cfg := { cfg with heap := cfg.heap.insert rid { region with objMap := region.objMap.insert yoid (obj.insert field newVal) } }) hframe0 _))
    (rid_step_iff_of_insert_open hregion hstatus rfl hstatus)

-- SWAP-REGION-BRIDGE branch (heap-only, `newBridge` generalized).
theorem swap_bridge_step_iff_of_ne {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid yoid : ObjectId} {region : Region} {obj : Object} {field : FieldName} {newVal : Reference}
    {newBridge : ObjectId} (hregion : cfg.heap.lookup rid = some region) (hobj : region.objMap.lookup yoid = some obj)
    (hstatus : region.status = Status.Open)
    (hcfg' : cfg' = { cfg with heap := cfg.heap.insert rid ({ region with bridgeObjectId := newBridge, objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) }) :
    ∀ a : Reference, a ≠ Reference.OId yoid → ∀ b : Reference, ReachableStep cfg a b ↔ ReachableStep cfg' a b := by
  subst hcfg'
  exact step_iff_of_ne_of_objAt (fun _ hne => swap_region_objAt_eq_of_ne vcfg hregion hobj hne)
    (rid_step_iff_of_insert_open hregion hstatus rfl hstatus)

-- `FrameRoot` below the last frame agrees when only the last frame and its own region's heap entry change.
private theorem frame_root_iff_of_lt {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg) {frame0 : FrameWithIndex}
    (hframe0 : cfg.stackWithIndex.getLast? = some frame0) (hstack : ∃ g, cfg'.stack = cfg.stack.dropLast ++ [g])
    (hheap : ∀ r, r ≠ frame0.regionId → cfg'.heap.lookup r = cfg.heap.lookup r)
    {G : Index} (hG : G < frame0.index) (s : Reference) : FrameRoot cfg G s ↔ FrameRoot cfg' G s := by
  have hidx := (stack_eq_of_stackWithIndex_getLast? hframe0).2
  obtain ⟨g, hstack⟩ := hstack
  have hmem : ∀ fr : FrameWithIndex, fr.index = G → (fr ∈ cfg.stackWithIndex ↔ fr ∈ cfg'.stackWithIndex) := by
    intro fr hfr
    have hne : ∀ f : Frame, fr ≠ { f with index := cfg.stack.dropLast.length } := by
      rintro f rfl
      dsimp only at hfr
      exact hG.ne (hfr ▸ hidx).symm
    rw [stackWithIndex_eq_of_getLast? (stack_getLast?_of_stackWithIndex_getLast? hframe0), RuntimeConfig.stackWithIndex, hstack,
      List.mapIdx_concat]
    simp only [List.mem_append, List.mem_singleton, or_iff_left (hne _)]
  have hlk : ∀ fr ∈ cfg.stackWithIndex, fr.index = G → cfg'.heap.lookup fr.regionId = cfg.heap.lookup fr.regionId :=
    fun fr hfr hfrG => hheap _ fun hc =>
      hG.ne (hfrG ▸ merge_corollary_regionId_unique_index vcfg.s1 hfr (List.mem_of_getLast? hframe0) hc)
  constructor
  · rintro (⟨fr, hfr, hfrG, h⟩ | ⟨fr, hfr, hfrG, h⟩)
    · exact .inl ⟨fr, (hmem fr hfrG).mp hfr, hfrG, h⟩
    · exact .inr ⟨fr, (hmem fr hfrG).mp hfr, hfrG, by rwa [hlk fr hfr hfrG]⟩
  · rintro (⟨fr, hfr, hfrG, h⟩ | ⟨fr, hfr, hfrG, h⟩)
    · exact .inl ⟨fr, (hmem fr hfrG).mpr hfr, hfrG, h⟩
    · have hfr0 := (hmem fr hfrG).mpr hfr
      exact .inr ⟨fr, hfr0, hfrG, by rwa [← hlk fr hfr0 hfrG]⟩

-- `FrameReachable cfg G` transports both ways when it never reaches the only source `OId oidC` whose steps differ.
private theorem confined_iff {cfg cfg' : RuntimeConfig} {oidC : ObjectId}
    (hS : ∀ a : Reference, a ≠ Reference.OId oidC → ∀ b, ReachableStep cfg a b ↔ ReachableStep cfg' a b)
    {G : Index} (hR : ∀ s, FrameRoot cfg G s ↔ FrameRoot cfg' G s)
    (hC : ∀ r, FrameReachable cfg G r → r ≠ Reference.OId oidC) (ref : Reference) :
    FrameReachable cfg G ref ↔ FrameReachable cfg' G ref := by
  rw [FrameReachable_iff_reflTransGen, FrameReachable_iff_reflTransGen]
  constructor
  · rintro ⟨s, hs, hrtg⟩
    refine ⟨s, (hR s).mp hs, ?_⟩
    induction hrtg with
    | refl => exact .refl
    | tail hprev hstep ih =>
      exact ih.tail ((hS _ (hC _ ((FrameReachable_iff_reflTransGen ..).mpr ⟨s, hs, hprev⟩)) _).mp hstep)
  · rintro ⟨s, hs, hrtg⟩
    have hs' := (hR s).mpr hs
    refine ⟨s, hs', ?_⟩
    induction hrtg with
    | refl => exact .refl
    | tail _ hstep ih =>
      exact ih.tail ((hS _ (hC _ ((FrameReachable_iff_reflTransGen ..).mpr ⟨s, hs', ih⟩)) _).mpr hstep)

-- `FrameReachable` is unaffected below the mutated frame across all four branches: a suspended chain can never reach `yoid` (owner-index bound).
theorem swap_frame_reachable_iff_of_lt {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg) (vcfg' : ValidConfig cfg')
    (h : swap x yf cfg = some cfg')
    (frame : FrameWithIndex) (hlt : frame.index < cfg.stack.dropLast.length) (ref : Reference) :
    FrameReachable cfg frame.index ref ↔ FrameReachable cfg' frame.index ref := by
  obtain ⟨frame0, hframe0, yRef, -, yRefLoc, hyrl, yfRef, -, yfRefLoc, -, hcase⟩ := swap_cases h
  have hmem0 := List.mem_of_getLast? hframe0
  have hlt0 : frame.index < frame0.index := by rw [(stack_eq_of_stackWithIndex_getLast? hframe0).2]; exact hlt
  rcases hcase with ⟨yoid, xRef, obj, -, rfl, rfl, -, hobj, rfl⟩ |
    ⟨yoid, rid, region, obj, xoid, xrid, -, rfl, rfl, rfl, hregion, hobj, -, -, -, hstatus, rfl⟩ |
    ⟨yoid, rid, region, obj, xrid, -, rfl, rfl, rfl, hregion, hobj, -, hstatus, rfl⟩ |
    ⟨yoid, yrid, yfoid, yfrid, region, obj, -, rfl, rfl, -, -, rfl, -, hregion, hobj, rfl⟩
  · exact confined_iff (swap_stack_step_iff_of_ne hframe0 hobj rfl)
      (frame_root_iff_of_lt vcfg hframe0 ⟨_, rfl⟩ (fun _ _ => by rfl) hlt0)
      (by rintro _ hr rfl; exact absurd (stack_container_confined vcfg hyrl hr) (Nat.not_le.mpr hlt0)) ref
  all_goals first
    | have hstatus : region.status = Status.Open := hstatus
    | obtain ⟨_, hlk0, hstatus⟩ := l2_of_stackWithIndex vcfg hmem0
      rw [hregion, Option.some_inj] at hlk0
      subst hlk0
  all_goals
    refine confined_iff ?_ (frame_root_iff_of_lt vcfg hframe0 ?_ (fun _ hr => AList.lookup_insert_ne hr) hlt0)
      (by rintro _ hr rfl; exact absurd (region_container_confined vcfg hregion hstatus hmem0 rfl hyrl hr) (Nat.not_le.mpr hlt0)) ref
  · exact swap_region_stack_step_iff_of_ne vcfg hframe0 hregion hobj hstatus rfl
  · exact ⟨_, rfl⟩
  · exact swap_region_stack_step_iff_of_ne vcfg hframe0 hregion hobj hstatus rfl
  · exact ⟨_, rfl⟩
  · exact swap_bridge_step_iff_of_ne vcfg hregion hobj hstatus rfl
  · exact ⟨_, (stack_eq_of_stackWithIndex_getLast? hframe0).1⟩

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
  rw [(stack_eq_of_stackWithIndex_getLast? hframe0).2] at hlocm
  refine objAt_insert_step (field := field) ((objAt_of_loc_last (stack_getLast?_of_stackWithIndex_getLast? hframe0) hlocm).trans hobj) ?_ hstep
  subst hcfg'
  simp [objAt_of_loc_last List.getLast?_concat
    ((swap_corollary_stack_loc_eq hframe0 hobj yoid).symm.trans (hlocm.trans (by simp)))]

-- REGION-touching branches (mutated container in a region, plus an irrelevant stack `varMap` change).
theorem swap_region_stack_yoid_step_of_ne {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid yoid : ObjectId} {region : Region} {obj : Object} {field : FieldName} {newVal : Reference}
    {frame0 : FrameWithIndex} {newVarMap : VarMap}
    (hframe0 : cfg.stackWithIndex.getLast? = some frame0)
    (hregion : cfg.heap.lookup rid = some region) (hobj : region.objMap.lookup yoid = some obj)
    (hlocm : (Reference.OId yoid).loc? cfg = some (Location.Rgn rid))
    {c : Reference} (hstep : ReachableStep ({ stack := cfg.stack.dropLast ++ [({ frame0 with varMap := newVarMap } : Frame)], heap := cfg.heap.insert rid ({ region with objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) } : RuntimeConfig) (Reference.OId yoid) c) :
    c = newVal ∨ ReachableStep cfg (Reference.OId yoid) c :=
  objAt_insert_step (by simp [Reference.objAt?, hlocm, hregion, hobj])
    ((swap_varmap_objAt_eq (cfg := { cfg with heap := cfg.heap.insert rid { region with objMap := region.objMap.insert yoid (obj.insert field newVal) } }) hframe0 yoid).symm.trans
      (swap_region_objAt_mutated (newBridge := region.bridgeObjectId) vcfg hregion hobj hlocm)) hstep

-- SWAP-REGION-BRIDGE branch (heap-only, `newBridge` generalized).
theorem swap_bridge_yoid_step_of_ne {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid yoid : ObjectId} {region : Region} {obj : Object} {field : FieldName} {newVal : Reference}
    {newBridge : ObjectId}
    (hregion : cfg.heap.lookup rid = some region) (hobj : region.objMap.lookup yoid = some obj)
    (hlocm : (Reference.OId yoid).loc? cfg = some (Location.Rgn rid))
    {c : Reference} (hstep : ReachableStep ({ cfg with heap := cfg.heap.insert rid ({ region with bridgeObjectId := newBridge, objMap := region.objMap.insert yoid (obj.insert field newVal) } : Region) }) (Reference.OId yoid) c) :
    c = newVal ∨ ReachableStep cfg (Reference.OId yoid) c :=
  objAt_insert_step (by simp [Reference.objAt?, hlocm, hregion, hobj]) (swap_region_objAt_mutated vcfg hregion hobj hlocm) hstep
