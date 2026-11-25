module

public import Gc.Model.Types
public import Gc.Model.Helpers
public import Gc.Model.Validity
public import Gc.Model.Mutation.Mutation
public import Gc.Model.Preservation
public import Gc.Reachability.Reachable.Semantics
public import Gc.Reachability.Reachable.Lemmas.Common
public import Gc.Reachability.Reachable.Lemmas.Enter
public import Gc.Reachability.Reachable.Lemmas.VarAsgn

@[expose] public section

-- The last stack frame of a fieldAsgn-STACK config, written as a `getLast?` fact on the underlying stack.
private theorem fieldAsgn_stack_last {cfg : RuntimeConfig} {frame : FrameWithIndex}
    (hframe : cfg.stackWithIndex.getLast? = some frame) : cfg.stack.getLast? = some frame.toFrame := by
  rw [(stack_eq_of_stackWithIndex_getLast? hframe).1]; simp

-- `objAt?` of an object located in the last stack frame is that frame's own `objMap` lookup.
private theorem objAt_of_loc_last {cfg : RuntimeConfig} {frame : Frame} {o : ObjectId}
    (hlast : cfg.stack.getLast? = some frame)
    (hloc : (Reference.OId o).loc? cfg = some (Location.Stk cfg.stack.dropLast.length)) :
    (Reference.OId o).objAt? cfg = frame.objMap.lookup o := by
  simp only [Reference.objAt?, hloc]
  rw [stackWithIndex_find_index_eq_getElem, stackWithIndex_eq_of_getLast? hlast]
  simp

-- `objAt?` agrees for `o ≠ oid` (STACK branch): only the last frame's entry at `oid` changes.
private theorem fieldAsgn_stack_objAt_eq_of_ne {cfg : RuntimeConfig} {frame : FrameWithIndex} {oid : ObjectId}
    {obj : Object} {field : FieldName} {yRef : Reference}
    (hframe : cfg.stackWithIndex.getLast? = some frame) (hobj : frame.objMap.lookup oid = some obj)
    {o : ObjectId} (hne : o ≠ oid) :
    (Reference.OId o).objAt? cfg = (Reference.OId o).objAt? { cfg with stack := cfg.stack.dropLast ++
      [({ frame with objMap := frame.objMap.insert oid (obj.insert field yRef) } : Frame)] } := by
  simp only [Reference.objAt?, ← fieldAsgn_corollary_stack_loc_eq hframe hobj o]
  rcases (Reference.OId o).loc? cfg with _ | _ | fid
  · rfl
  · rfl
  dsimp only
  rw [stackWithIndex_find_index_eq_getElem, stackWithIndex_find_index_eq_getElem,
    stackWithIndex_eq_of_getLast? (fieldAsgn_stack_last hframe), stackWithIndex_mk_append_singleton]
  simp only [List.getElem?_append, List.getElem?_singleton]
  split_ifs <;> simp [AList.lookup_insert_ne hne]

-- `objAt?` agrees for `o ≠ oid` (REGION branch): only region `rid`'s entry at `oid` changes.
private theorem fieldAsgn_region_objAt_eq_of_ne {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid oid : ObjectId} {region : Region} {obj : Object} {field : FieldName} {yRef : Reference}
    (hregion : cfg.heap.lookup rid = some region) (hobj : region.objMap.lookup oid = some obj)
    {o : ObjectId} (hne : o ≠ oid) :
    (Reference.OId o).objAt? cfg = (Reference.OId o).objAt?
      { cfg with heap := cfg.heap.insert rid { region with objMap := region.objMap.insert oid (obj.insert field yRef) } } := by
  simp only [Reference.objAt?, ← fieldAsgn_corollary_region_loc_eq vcfg hregion hobj o]
  rcases (Reference.OId o).loc? cfg with _ | ridX | _
  · rfl
  · by_cases hridx : ridX = rid
    · subst hridx
      simp [hregion, AList.lookup_insert_ne hne]
    · simp [AList.lookup_insert_ne hridx]
  · rfl

-- `ReachableStep` agrees between `cfg`/`cfg'` for any source other than the mutated container; returns the container's own id existentially.
theorem fieldAsgn_step_iff_of_ne {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : fieldAsgn xf y cfg = some cfg') :
    ∃ oidC : ObjectId, resolveV xf.root cfg = some (Reference.OId oidC) ∧
      ∀ a : Reference, a ≠ Reference.OId oidC → ∀ b : Reference,
      ReachableStep cfg a b ↔ ReachableStep cfg' a b := by
  obtain ⟨frame, hframe, ⟨oid, -, obj, hxr, -, -, hobj, rfl⟩ |
    ⟨oid, oid_y, rid, region, obj, hxr, -, -, hregion, hobj, -, hstatus, -, rfl⟩⟩ := fieldAsgn_cases h
  · refine ⟨oid, hxr, fun a hane b => ?_⟩
    rcases a with _ | o
    · rfl
    · rw [ReachableStep_oid_iff, ReachableStep_oid_iff,
        fieldAsgn_stack_objAt_eq_of_ne hframe hobj (by rintro rfl; exact hane rfl)]
  · refine ⟨oid, hxr, fun a hane b => ?_⟩
    rcases a with r | o
    · set newRegion : Region := { region with objMap := region.objMap.insert oid (obj.insert xf.field (Reference.OId oid_y)) }
      by_cases hr : r = rid
      · subst hr
        exact iff_of_false (open_rid_no_step hregion hstatus)
          (open_rid_no_step (region := newRegion) (AList.lookup_insert cfg.heap) hstatus)
      · simp only [ReachableStep_rid_iff, AList.lookup_insert_ne hr]
    · rw [ReachableStep_oid_iff, ReachableStep_oid_iff,
        fieldAsgn_region_objAt_eq_of_ne vcfg hregion hobj (by rintro rfl; exact hane rfl)]
-- `FrameRoot` agrees between `cfg`/`cfg'` unconditionally: fieldAsgn only ever touches an `objMap`, never `varMap`/`regionId`/`bridgeObjectId`.
theorem fieldAsgn_frame_root_iff {cfg cfg' : RuntimeConfig} (h : fieldAsgn xf y cfg = some cfg')
    (fid : Index) (start : Reference) : FrameRoot cfg fid start ↔ FrameRoot cfg' fid start := by
  obtain ⟨frame, hframe, ⟨-, -, -, -, -, -, -, rfl⟩ | ⟨oid, oid_y, rid, region, obj, -, -, -, hregion, -, -, -, -, rfl⟩⟩ :=
    fieldAsgn_cases h
  · simp only [FrameRoot, stackWithIndex_eq_of_getLast? (fieldAsgn_stack_last hframe),
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
  · rw [stackWithIndex_eq_of_getLast? (fieldAsgn_stack_last hframe), stackWithIndex_mk_append_singleton]
    have hne : ∀ f : Frame, X ≠ { f with index := cfg.stack.dropLast.length } := by
      rintro f rfl
      exact lt_irrefl _ (hactiveidx ▸ hXlt)
    simp only [List.mem_append, List.mem_singleton, or_iff_left (hne _)]
  · rfl

-- A step out of the mutated container in `cfg'` either follows the newly-written field or an edge it already had in `cfg`.
private theorem fieldAsgn_oidC_step {cfg cfg' : RuntimeConfig} {oid oid_y : ObjectId} {obj : Object}
    {field : FieldName} (hobjAt : (Reference.OId oid).objAt? cfg = some obj)
    (hobjAtC : (Reference.OId oid).objAt? cfg' = some (obj.insert field (Reference.OId oid_y)))
    {c : Reference} (hstep : ReachableStep cfg' (Reference.OId oid) c) :
    c = Reference.OId oid_y ∨ ReachableStep cfg (Reference.OId oid) c := by
  obtain ⟨_, h1, h2⟩ := hstep
  rw [hobjAtC, Option.some_inj] at h1
  subst h1
  exact (object_insert_refs_mem (List.contains_iff_mem.mp h2)).imp_right
    fun hm => ⟨obj, hobjAt, List.contains_iff_mem.mpr hm⟩

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
  have hlast := fieldAsgn_stack_last hframe
  rw [(stack_eq_of_stackWithIndex_getLast? hframe).2] at hlocC
  refine fieldAsgn_oidC_step (obj := obj) (field := field) ((objAt_of_loc_last hlast hlocC).trans hobj) ?_ hstep
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
  refine fieldAsgn_oidC_step (obj := obj) (field := field) (by simp [Reference.objAt?, hlocC, hregion, hobj]) ?_ hstep
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
