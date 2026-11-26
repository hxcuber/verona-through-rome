module

public import Gc.Reachability.Reachable.Lemmas.Enter
public import Gc.Reachability.Reachable.Lemmas.VarAsgn

@[expose] public section

-- `objAt?` agrees for `o ≠ oid` (STACK branch): only the last frame's entry at `oid` changes.
private theorem fieldAsgn_stack_objAt_eq_of_ne {cfg : RuntimeConfig} {frame : FrameWithIndex} {oid : ObjectId}
    {obj : Object} {field : FieldName} {yRef : Reference}
    (hframe : cfg.stackWithIndex.getLast? = some frame) (hobj : frame.objMap.lookup oid = some obj)
    {o : ObjectId} (hne : o ≠ oid) :
    (Reference.OId o).objAt? cfg = (Reference.OId o).objAt? { cfg with stack := cfg.stack.dropLast ++
      [({ frame with objMap := frame.objMap.insert oid (obj.insert field yRef) } : Frame)] } :=
  objAt_last_frame_eq hframe (fieldAsgn_corollary_stack_loc_eq hframe hobj o) (AList.lookup_insert_ne hne)

-- `objAt?` agrees for `o ≠ oid` (REGION branch): only region `rid`'s entry at `oid` changes.
private theorem fieldAsgn_region_objAt_eq_of_ne {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid oid : ObjectId} {region : Region} {obj : Object} {field : FieldName} {yRef : Reference}
    (hregion : cfg.heap.lookup rid = some region) (hobj : region.objMap.lookup oid = some obj)
    {o : ObjectId} (hne : o ≠ oid) :
    (Reference.OId o).objAt? cfg = (Reference.OId o).objAt?
      { cfg with heap := cfg.heap.insert rid { region with objMap := region.objMap.insert oid (obj.insert field yRef) } } :=
  objAt_heap_insert_eq hregion (fieldAsgn_corollary_region_loc_eq vcfg hregion hobj o) (AList.lookup_insert_ne hne)

-- `ReachableStep` agrees between `cfg`/`cfg'` for any source other than the mutated container; returns the container's own id existentially.
theorem fieldAsgn_step_iff_of_ne {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : fieldAsgn xf y cfg = some cfg') :
    ∃ oidC : ObjectId, resolveV xf.root cfg = some (Reference.OId oidC) ∧
      ∀ a : Reference, a ≠ Reference.OId oidC → ∀ b : Reference,
      ReachableStep cfg a b ↔ ReachableStep cfg' a b := by
  obtain ⟨frame, hframe, ⟨oid, -, obj, hxr, -, -, hobj, rfl⟩ |
    ⟨oid, oid_y, rid, region, obj, hxr, -, -, hregion, hobj, -, hstatus, -, rfl⟩⟩ := fieldAsgn_cases h
  · exact ⟨oid, hxr, step_iff_of_ne_of_objAt (fun _ hne => fieldAsgn_stack_objAt_eq_of_ne hframe hobj hne)
      fun _ _ => Iff.rfl⟩
  · exact ⟨oid, hxr, step_iff_of_ne_of_objAt (fun _ hne => fieldAsgn_region_objAt_eq_of_ne vcfg hregion hobj hne)
      (rid_step_iff_of_insert_open hregion hstatus rfl hstatus)⟩

-- `FrameRoot` agrees between `cfg`/`cfg'` unconditionally: fieldAsgn only ever touches an `objMap`, never `varMap`/`regionId`/`bridgeObjectId`.
theorem fieldAsgn_frame_root_iff {cfg cfg' : RuntimeConfig} (h : fieldAsgn xf y cfg = some cfg')
    (fid : Index) (start : Reference) : FrameRoot cfg fid start ↔ FrameRoot cfg' fid start := by
  obtain ⟨frame, hframe, ⟨-, -, -, -, -, -, -, rfl⟩ | ⟨oid, oid_y, rid, region, obj, -, -, -, hregion, -, -, -, -, rfl⟩⟩ :=
    fieldAsgn_cases h
  · simp only [FrameRoot, stackWithIndex_eq_of_getLast? (stack_getLast?_of_stackWithIndex_getLast? hframe),
      stackWithIndex_mk_append_singleton, List.mem_append, List.mem_singleton, or_and_right, exists_or,
      exists_eq_left]
  · have hbr : ∀ r, (∃ g, cfg.heap.lookup r = some g ∧ start = Reference.OId g.bridgeObjectId) ↔
        ∃ g, (cfg.heap.insert rid { region with objMap := region.objMap.insert oid (obj.insert xf.field (Reference.OId oid_y)) }).lookup r = some g ∧ start = Reference.OId g.bridgeObjectId := by
      intro r
      by_cases hr : r = rid
      · subst hr
        simp [hregion]
      · simp [AList.lookup_insert_ne hr]
    simp only [FrameRoot, hbr]
    rfl

-- A `FrameReachable cfg G ref` chain confined away from the mutated container `oidC` transports unconditionally to `cfg'`, hop by hop.
theorem fieldAsgn_confined_transport {cfg cfg' : RuntimeConfig}
    {oidC : ObjectId} (hstepIffOfNe : ∀ a : Reference, a ≠ Reference.OId oidC → ∀ b : Reference,
      ReachableStep cfg a b ↔ ReachableStep cfg' a b)
    (hframeRootIff : ∀ fid start, FrameRoot cfg fid start ↔ FrameRoot cfg' fid start)
    {G : Index} (hconfined : ∀ refX, FrameReachable cfg G refX → refX ≠ Reference.OId oidC)
    {ref : Reference} (hreach : FrameReachable cfg G ref) :
    FrameReachable cfg' G ref := by
  obtain ⟨start, hroot, hrtg⟩ := (FrameReachable_iff_reflTransGen ..).mp hreach
  refine (FrameReachable_iff_reflTransGen ..).mpr ⟨start, (hframeRootIff G start).mp hroot, ?_⟩
  clear hreach
  induction hrtg with
  | refl => exact .refl
  | tail hprev hstep ih =>
    exact ih.tail ((hstepIffOfNe _ (hconfined _ ((FrameReachable_iff_reflTransGen ..).mpr ⟨_, hroot, hprev⟩)) _).mp hstep)

-- Stack membership below the active frame agrees between `cfg`/`cfg'`: fieldAsgn never touches any other frame's record.
theorem fieldAsgn_frame_mem_iff {cfg cfg' : RuntimeConfig} (h : fieldAsgn xf y cfg = some cfg')
    {X : FrameWithIndex} {activeIdx : Index} (hXlt : X.index < activeIdx)
    (hactiveidx : activeIdx = cfg.stack.dropLast.length) :
    X ∈ cfg.stackWithIndex ↔ X ∈ cfg'.stackWithIndex := by
  obtain ⟨frame, hframe, ⟨-, -, -, -, -, -, -, rfl⟩ | ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, rfl⟩⟩ := fieldAsgn_cases h
  · rw [stackWithIndex_eq_of_getLast? (stack_getLast?_of_stackWithIndex_getLast? hframe), stackWithIndex_mk_append_singleton]
    have hne : ∀ f : Frame, X ≠ { f with index := cfg.stack.dropLast.length } := by
      rintro f rfl
      exact lt_irrefl _ (hactiveidx ▸ hXlt)
    simp only [List.mem_append, List.mem_singleton, or_iff_left (hne _)]
  · rfl

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
  have hlast := stack_getLast?_of_stackWithIndex_getLast? hframe
  rw [(stack_eq_of_stackWithIndex_getLast? hframe).2] at hlocC
  refine objAt_insert_step (obj := obj) (field := field) ((objAt_of_loc_last hlast hlocC).trans hobj) ?_ hstep
  subst hcfg'
  simp [objAt_of_loc_last List.getLast?_concat
    ((fieldAsgn_corollary_stack_loc_eq hframe hobj oid).symm.trans (hlocC.trans (by simp)))]

-- The REGION-branch counterpart of `fieldAsgn_stack_oidC_step_of_ne_oidY`.
theorem fieldAsgn_region_oidC_step_of_ne_oidY {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid oid oid_y : ObjectId} {region : Region} {obj : Object} {field : FieldName}
    (hregion : cfg.heap.lookup rid = some region)
    (hlocC : (Reference.OId oid).loc? cfg = some (Location.Rgn rid))
    (hobj : region.objMap.lookup oid = some obj)
    (hcfg' : cfg' = { cfg with heap := cfg.heap.insert rid ({ region with objMap := region.objMap.insert oid (obj.insert field (Reference.OId oid_y)) } : Region) })
    {c : Reference} (hstep : ReachableStep cfg' (Reference.OId oid) c) :
    c = Reference.OId oid_y ∨ ReachableStep cfg (Reference.OId oid) c := by
  refine objAt_insert_step (obj := obj) (field := field) (by simp [Reference.objAt?, hlocC, hregion, hobj]) ?_ hstep
  subst hcfg'
  simp [Reference.objAt?, ← fieldAsgn_corollary_region_loc_eq vcfg hregion hobj, hlocC]

-- H3 lifted along a chain rooted at any object inside region `rid`: an `OId` reached stays in `rid` or enters via a Closed-region hop.
private theorem reflTransGen_region_confined {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid : RegionId} {region : Region} (hlookup : cfg.heap.lookup rid = some region)
    {oidStart : ObjectId} (hlocStart : (Reference.OId oidStart).loc? cfg = some (Location.Rgn rid))
    {target : Reference} (hrtg : Relation.ReflTransGen (ReachableStep cfg) (Reference.OId oidStart) target) :
    (∃ oid ridCur region', target = Reference.OId oid ∧ (Reference.OId oid).loc? cfg = some (Location.Rgn ridCur) ∧
       cfg.heap.lookup ridCur = some region' ∧ (ridCur = rid ∨ region'.status = Status.Closed)) ∨
    (∃ ridR, target = Reference.RId ridR) := by
  induction hrtg with
  | refl => exact .inl ⟨oidStart, rid, region, rfl, hlocStart, hlookup, .inl rfl⟩
  | tail _ hstep ih =>
    rcases ih with ⟨oidB, ridCur, region', rfl, hlocB, hlkB, hcaseB⟩ | ⟨ridB, rfl⟩
    · obtain ⟨obj, hobjAt, hcontains⟩ := hstep
      simp only [Reference.objAt?, hlocB, hlkB, Option.bind_some] at hobjAt
      have hmemB := mem_region_refs_of_mem_objMap hobjAt (List.contains_iff_mem.mp hcontains)
      rename_i c _
      rcases c with ridC | oidC
      · exact .inr ⟨ridC, rfl⟩
      · exact .inl ⟨oidC, ridCur, region', rfl, vcfg.h3 ridCur oidC region' hlkB hmemB, hlkB, hcaseB⟩
    · obtain ⟨regionR, hlkR, hclosedR, rfl⟩ := hstep
      exact .inl ⟨_, ridB, regionR, rfl, (oid_loc_rgn_iff_in_heap vcfg).mpr
        ⟨regionR, hlkR, vcfg.h1 _ (List.mem_map_of_mem (AList.lookup_mem_entries hlkR))⟩, hlkR, .inr hclosedR⟩

-- A chain rooted inside region `rid` can never reach an object in a different Open region.
theorem reflTransGen_region_open_ne_absurd {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid : RegionId} {region : Region} (hlookup : cfg.heap.lookup rid = some region)
    {oidStart : ObjectId} (hlocStart : (Reference.OId oidStart).loc? cfg = some (Location.Rgn rid))
    {oidTarget : ObjectId} {ridT : RegionId} {regionT : Region}
    (hlocT : (Reference.OId oidTarget).loc? cfg = some (Location.Rgn ridT))
    (hlkT : cfg.heap.lookup ridT = some regionT) (hopenT : regionT.status = Status.Open) (hne : ridT ≠ rid)
    (hrtg : Relation.ReflTransGen (ReachableStep cfg) (Reference.OId oidStart) (Reference.OId oidTarget)) : False := by
  rcases reflTransGen_region_confined vcfg hlookup hlocStart hrtg with ⟨_, ridCur, region', heq, hloc', hlk', hcase'⟩ | ⟨_, heq⟩
  · cases heq
    obtain rfl : ridT = ridCur := by simpa using hlocT.symm.trans hloc'
    obtain rfl : regionT = region' := by simpa using hlkT.symm.trans hlk'
    rcases hcase' with rfl | hc
    · exact hne rfl
    · simp [hopenT] at hc
  · cases heq

-- fieldAsgn preserves the stack length, every object's `loc?`, and every frame below the active one.
theorem fieldAsgn_shape {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : fieldAsgn xf y cfg = some cfg') :
    cfg'.stackWithIndex.length = cfg.stackWithIndex.length ∧
    (∀ o, (Reference.OId o).loc? cfg' = (Reference.OId o).loc? cfg) ∧
    ∀ X : FrameWithIndex, X.index < cfg.stackWithIndex.length - 1 →
      (X ∈ cfg.stackWithIndex ↔ X ∈ cfg'.stackWithIndex) := by
  have hmem := fun X (hX : X.index < cfg.stackWithIndex.length - 1) => fieldAsgn_frame_mem_iff h
    (X := X) (activeIdx := cfg.stack.dropLast.length) (by simpa [RuntimeConfig.stackWithIndex] using hX) rfl
  obtain ⟨A, hA, ⟨_, _, _, _, _, _, hobj, rfl⟩ | ⟨_, _, _, _, _, _, _, _, hregion, hobj, _, _, _, rfl⟩⟩ :=
    fieldAsgn_cases h
  · exact ⟨stackWithIndex_length_of_replace_last (stack_getLast?_of_stackWithIndex_getLast? hA) rfl,
      fun o => (fieldAsgn_corollary_stack_loc_eq hA hobj o).symm, hmem⟩
  · exact ⟨rfl, fun o => (fieldAsgn_corollary_region_loc_eq vcfg hregion hobj o).symm, hmem⟩

-- For `oid` in a suspended frame `F`'s region, fieldAsgn neither creates nor destroys its reachability from `F`.
theorem fieldAsgn_suspended_reach {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : fieldAsgn xf y cfg = some cfg') (hFR3 : FrameReachable_at_later_frame_implies_FrameReachable_at_frame cfg)
    {F : FrameWithIndex} (hF : F ∈ cfg.stackWithIndex) (hFlt : F.index < cfg.stackWithIndex.length - 1)
    {oid : ObjectId} (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn F.regionId)) :
    F ∈ cfg'.stackWithIndex ∧ (StackReachable cfg (.OId oid) → FrameReachable cfg' F.index (.OId oid)) ∧
    ∀ fid, FrameReachable cfg' fid (.OId oid) → StackReachable cfg (.OId oid) := by
  obtain ⟨oidC, hxrC, hne⟩ := fieldAsgn_step_iff_of_ne vcfg h
  have hroot := fieldAsgn_frame_root_iff h
  obtain ⟨regionF, hlkF, hopenF⟩ := l2_of_stackWithIndex vcfg hF
  obtain ⟨A, hA, hcase⟩ := fieldAsgn_cases h
  have hAmem := List.mem_of_getLast? hA
  have hFA : F.index < A.index := by
    have := (stack_eq_of_stackWithIndex_getLast? hA).2
    simp [RuntimeConfig.stackWithIndex] at hFlt
    rw [this, List.length_dropLast]
    omega
  obtain ⟨hbound, oid_y, hstepC, hesc⟩ : (∀ fid, FrameReachable cfg fid (.OId oidC) → A.index ≤ fid) ∧
      ∃ oid_y, (∀ c, ReachableStep cfg' (.OId oidC) c → c = .OId oid_y ∨ ReachableStep cfg (.OId oidC) c) ∧
      (Relation.ReflTransGen (ReachableStep cfg) (.OId oid_y) (.OId oid) → StackReachable cfg (.OId oid)) := by
    rcases hcase with ⟨oid0, oid_y, obj, hxr0, hyr, hlocC, hobj, hcfg'⟩ |
        ⟨oid0, oid_y, rid, region, obj, hxr0, hyr, hlocC, hregion, hobj, hyloc, hstatus, hfrid, hcfg'⟩
    · obtain rfl : oidC = oid0 := by simpa using hxrC.symm.trans hxr0
      refine ⟨fun _ => stack_container_confined vcfg hlocC, oid_y,
        fun _ => fieldAsgn_stack_oidC_step_of_ne_oidY hA hlocC hobj hcfg', fun hc => ?_⟩
      obtain ⟨Y, hY, hrootY⟩ := resolveV_frameRoot hyr
      exact ⟨Y, hY, (FrameReachable_iff_reflTransGen ..).mpr ⟨_, hrootY, hc⟩⟩
    · obtain rfl : oidC = oid0 := by simpa using hxrC.symm.trans hxr0
      refine ⟨fun _ => region_container_confined vcfg hregion hstatus hAmem hfrid.symm hlocC, oid_y,
        fun _ => fieldAsgn_region_oidC_step_of_ne_oidY vcfg hregion hlocC hobj hcfg', fun hc => ?_⟩
      exact (reflTransGen_region_open_ne_absurd vcfg hregion hyloc hloc hlkF hopenF (fun he => Nat.ne_of_lt hFA
        (merge_corollary_regionId_unique_index vcfg.s1 hF hAmem (he.trans hfrid))) hc).elim
  refine ⟨((fieldAsgn_shape vcfg h).2.2 F hFlt).mp hF, fun hs => ?_, fun fid hr => ?_⟩
  · exact fieldAsgn_confined_transport hne hroot (fun r hr he => absurd (hbound _ (he ▸ hr)) (Nat.not_le.mpr hFA))
      (FrameReachable_of_StackReachable vcfg hFR3 hF hloc hs)
  · obtain ⟨start, hs, hc⟩ := (FrameReachable_iff_reflTransGen ..).mp hr
    rcases reflTransGen_split (fun a ha b => (hne a ha b).mpr) hstepC hc with hc | hc
    · exact StackReachable_of_root ((hroot fid start).mpr hs) hc
    · exact hesc hc
