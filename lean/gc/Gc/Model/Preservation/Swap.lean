module

public import Gc.Model.Types
public import Gc.Model.Helpers
public import Gc.Model.Validity
public import Gc.Model.Theorems
public import Gc.Model.Mutation.Swap
public import Gc.Model.Preservation.Common

public import Mathlib.Data.List.Infix

@[expose] public section

-- `swap_cases` with the two region branches merged, `rid` substituted and the overwritten field value recorded.
theorem swap_cases_norm (h : swap x yf cfg = some cfg') :
    ∃ frame : FrameWithIndex, cfg.stackWithIndex.getLast? = some frame ∧ ∃ yfRef yoid obj,
    ((∃ xRef, frame.varMap.lookup x = some xRef ∧ frame.objMap.lookup yoid = some obj ∧
        obj.lookup yf.field = some yfRef ∧
        cfg' = { cfg with stack := cfg.stack.dropLast ++ [ { frame with
          varMap := frame.varMap.insert x yfRef,
          objMap := frame.objMap.insert yoid (obj.insert yf.field xRef) } ] }) ∨
     (∃ region xRef, cfg.heap.lookup frame.regionId = some region ∧ region.objMap.lookup yoid = some obj ∧
        obj.lookup yf.field = some yfRef ∧ frame.varMap.lookup x = some xRef ∧ region.status = Status.Open ∧
        (∀ xoid, xRef = Reference.OId xoid → (Reference.OId xoid).loc? cfg = some (Location.Rgn frame.regionId)) ∧
        cfg' = { cfg with
          stack := cfg.stack.dropLast ++ [ { frame with varMap := frame.varMap.insert x yfRef } ],
          heap := cfg.heap.insert frame.regionId { region with
            objMap := region.objMap.insert yoid (obj.insert yf.field xRef) } }) ∨
     (∃ region yfoid, cfg.heap.lookup frame.regionId = some region ∧ region.objMap.lookup yoid = some obj ∧
        obj.lookup yf.field = some yfRef ∧ yfRef = Reference.OId yfoid ∧
        (Reference.OId yfoid).loc? cfg = some (Location.Rgn frame.regionId) ∧
        cfg' = { cfg with
          heap := cfg.heap.insert frame.regionId { region with
            bridgeObjectId := yfoid,
            objMap := region.objMap.insert yoid (obj.insert yf.field (Reference.OId region.bridgeObjectId)) } })) := by
  obtain ⟨frame, hframe, yRef, hyr, yRefLoc, hyrl, yfRef, hyf, yfRefLoc, hyfl, hcase⟩ := swap_cases h
  refine ⟨frame, hframe, yfRef, ?_⟩
  rcases hcase with
    ⟨yoid, xRef, obj, -, rfl, rfl, hxr, hobj, rfl⟩ |
    ⟨yoid, rid, region, obj, xoid, xrid, -, rfl, rfl, rfl, hregion, hobj, hxr, hxrl, rfl, hstatus, rfl⟩ |
    ⟨yoid, rid, region, obj, xrid, -, rfl, rfl, rfl, hregion, hobj, hxr, hstatus, rfl⟩ |
    ⟨yoid, yrid, yfoid, yfrid, region, obj, -, rfl, rfl, rfl, rfl, rfl, rfl, hregion, hobj, rfl⟩
  · refine ⟨yoid, obj, Or.inl ⟨xRef, hxr, hobj, ?_, rfl⟩⟩
    simpa [resolveFA, hyr, hyrl, swap_corollary_stackWithIndex_find_eq (List.mem_of_getLast? hframe), hobj]
      using hyf
  · refine ⟨yoid, obj, Or.inr (Or.inl ⟨region, _, hregion, hobj, ?_, hxr, hstatus,
      by rintro _ ⟨⟩; exact hxrl, rfl⟩)⟩
    simpa [resolveFA, hyr, hyrl, hregion, hobj] using hyf
  · refine ⟨yoid, obj, Or.inr (Or.inl ⟨region, _, hregion, hobj, ?_, hxr, hstatus, by simp, rfl⟩)⟩
    simpa [resolveFA, hyr, hyrl, hregion, hobj] using hyf
  · refine ⟨yoid, obj, Or.inr (Or.inr ⟨region, yfoid, hregion, hobj, ?_, rfl, hyfl, rfl⟩)⟩
    simpa [resolveFA, hyr, hyrl, hregion, hobj] using hyf

-- A value stored at an AList key is among the AList's values.
theorem alist_lookup_mem_values {α β : Type*} [DecidableEq α] {l : AList (fun _ : α => β)} {k : α} {v : β}
    (h : l.lookup k = some v) : v ∈ l.entries.map (·.2) :=
  List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries h)

-- SWAP-STACK only exchanges two values already stored in the frame, so the frame's refs can only shrink.
theorem swap_stack_frame_refs_mem {f : Frame} {x : VarName} {yoid : ObjectId} {obj : Object} {k : FieldName}
    {xRef yfRef r : Reference} (hxr : f.varMap.lookup x = some xRef) (hobj : f.objMap.lookup yoid = some obj)
    (hfield : obj.lookup k = some yfRef)
    (hr : r ∈ Frame.refs ⟨f.regionId, f.bridgeVar, f.objMap.insert yoid (obj.insert k xRef),
      f.varMap.insert x yfRef⟩) : r ∈ f.refs := by
  simp only [Frame.refs, List.mem_append] at hr ⊢
  rcases hr with hr | hr
  · rcases objMap_insert_field_refs_mem hobj hr with rfl | hr
    · exact Or.inr (alist_lookup_mem_values hxr)
    · exact Or.inl hr
  · rcases alist_insert_refs_mem hr with rfl | hr
    · exact Or.inl (objMap_bind_refs_mem_of_lookup hobj (alist_lookup_mem_values hfield))
    · exact Or.inr hr

-- Regions of a heap after an insert are the inserted region or pre-existing ones.
theorem heap_insert_regions_mem {heap : Heap} {rid : RegionId} {newRegion r : Region}
    (hr : r ∈ Heap.regions (heap.insert rid newRegion)) : r = newRegion ∨ r ∈ heap.regions := by
  unfold Heap.regions at hr ⊢
  rw [AList.entries_insert, List.map_cons, List.mem_cons] at hr
  exact hr.imp_right ((List.kerase_sublist rid heap.entries).map _).mem

-- Overwriting one field of a stored object changes the ObjMap's bind-refs count by the two `==` indicators.
theorem objMap_insert_field_count_eq {m : ObjMap} {oid : ObjectId} {obj : Object} {k : FieldName}
    {v_old v_new : Reference} (hobj : m.lookup oid = some obj) (hfield : obj.lookup k = some v_old) (t : Reference) :
    ((m.insert oid (obj.insert k v_new)).entries.map (·.2) >>= Object.refs).count t +
      (if (v_old == t) = true then 1 else 0) =
    (m.entries.map (·.2) >>= Object.refs).count t + (if (v_new == t) = true then 1 else 0) := by
  have h1 : (Object.refs (obj.insert k v_new)).count t + _ = (Object.refs obj).count t + _ :=
    alist_insert_count_eq (v_new := v_new) (t := t) hfield
  have h2 : ((m.insert oid (obj.insert k v_new)).entries.map (·.2) >>= Object.refs).count t +
      (Object.refs obj).count t =
      (m.entries.map (·.2) >>= Object.refs).count t + (Object.refs (obj.insert k v_new)).count t :=
    alist_insert_bind_count_eq Object.refs t hobj
  omega

-- Replacing the last frame by one with a permuted objMap key set leaves every object's `Reference.loc?` unchanged.
theorem last_frame_loc_eq {cfg : RuntimeConfig} {frame : FrameWithIndex} {g : Frame}
    (hframe : cfg.stackWithIndex.getLast? = some frame) (hkeys : g.objMap.keys.Perm frame.objMap.keys)
    (oid' : ObjectId) :
    (Reference.OId oid').loc? cfg = (Reference.OId oid').loc? { cfg with stack := cfg.stack.dropLast ++ [g] } := by
  obtain ⟨stack_eq, _⟩ := stack_eq_of_stackWithIndex_getLast? hframe
  refine loc_eq_of_find_map_eq ?_ rfl
  unfold RuntimeConfig.stackWithIndex
  conv_lhs => rw [stack_eq]
  simp only [List.mapIdx_concat, List.findRev?_eq_find?_reverse, List.reverse_append, List.reverse_singleton,
    List.singleton_append, List.find?_cons, hkeys.contains_eq]
  cases frame.objMap.keys.contains oid' <;> rfl

-- SWAP-STACK never changes the last frame's objMap key set, so `Reference.loc?` transports for every object id.
theorem swap_corollary_stack_loc_eq {cfg : RuntimeConfig} {frame : FrameWithIndex} {yoid : ObjectId}
    {obj : Object} {field : FieldName} {newVal : Reference} {newVarMap : VarMap}
    (hframe : cfg.stackWithIndex.getLast? = some frame) (hobj : frame.objMap.lookup yoid = some obj)
    (oid' : ObjectId) :
    (Reference.OId oid').loc? cfg =
      (Reference.OId oid').loc? { cfg with stack := cfg.stack.dropLast ++
        [({ frame with varMap := newVarMap, objMap := frame.objMap.insert yoid (obj.insert field newVal) } :
          Frame)] } :=
  last_frame_loc_eq hframe (AList.keys_insert_perm_of_mem (AList.mem_keys_of_lookup_eq_some hobj)) oid'

-- A region-side swap only inserts at present keys, so `Reference.loc?` transports for every object id.
theorem swap_corollary_region_loc_eq {cfg : RuntimeConfig} {rid yoid : ObjectId} {region newRegion : Region}
    {obj v : Object} (vcfg : ValidConfig cfg)
    (hregion : cfg.heap.lookup rid = some region) (hobj : region.objMap.lookup yoid = some obj)
    (hnewRegion : newRegion.objMap = region.objMap.insert yoid v)
    (oid' : ObjectId) :
    (Reference.OId oid').loc? cfg =
      (Reference.OId oid').loc? { cfg with heap := cfg.heap.insert rid newRegion } := by
  have keys_perm : newRegion.objMap.keys.Perm region.objMap.keys := by
    rw [hnewRegion]
    exact AList.keys_insert_perm_of_mem (AList.mem_keys_of_lookup_eq_some hobj)
  refine loc_eq_of_find_map_eq rfl ?_
  obtain ⟨region2, l1e, l2e, hnotmem, heq, hkerase⟩ :=
    List.exists_of_kerase (AList.mem_keys_of_lookup_eq_some hregion)
  have region_mem_cfg : (⟨rid, region⟩ : Sigma (fun _ : RegionId => Region)) ∈ cfg.heap.entries :=
    AList.mem_lookup_iff.mp (by rw [hregion]; rfl)
  obtain rfl : region2 = region := List.NodupKeys.eq_of_mk_mem cfg.heap.nodupKeys
    (heq ▸ List.mem_append_right _ List.mem_cons_self) region_mem_cfg
  dsimp only
  rw [AList.entries_insert, hkerase, List.find?_cons, keys_perm.contains_eq]
  by_cases hb2 : region2.objMap.keys.contains oid'
  · rw [hb2, List.find?_eq_some_of_unique region_mem_cfg hb2 fun ⟨rid_y, region_y⟩ hy hpy => by
      obtain rfl := heap_region_unique vcfg.l1 hy (List.contains_iff_mem.mp hpy)
        region_mem_cfg (List.contains_iff_mem.mp hb2)
      rw [List.NodupKeys.eq_of_mk_mem cfg.heap.nodupKeys hy region_mem_cfg]]
    rfl
  · rw [Bool.not_eq_true] at hb2
    simp only [hb2, heq, List.find?_append, List.find?_cons]

-- A varMap-only change to the last frame never affects `Reference.loc?`.
theorem swap_corollary_stack_varmap_loc_eq {cfg : RuntimeConfig} {frame : FrameWithIndex} {newVarMap : VarMap}
    (hframe : cfg.stackWithIndex.getLast? = some frame) (oid' : ObjectId) :
    (Reference.OId oid').loc? cfg =
      (Reference.OId oid').loc? { cfg with stack := cfg.stack.dropLast ++
        [({ frame with varMap := newVarMap } : Frame)] } :=
  last_frame_loc_eq (g := { frame with varMap := newVarMap }) hframe (List.Perm.refl _) oid'

-- Frames of a config whose last frame was replaced by `g` are either old frames or `g` at the old last index.
theorem stackWithIndex_mem_of_last_replace {cfg cfg' : RuntimeConfig} {frame : FrameWithIndex} {g : Frame}
    (hframe : cfg.stackWithIndex.getLast? = some frame) (hstack : cfg'.stack = cfg.stack.dropLast ++ [g])
    {f' : FrameWithIndex} (hf' : f' ∈ cfg'.stackWithIndex) :
    f' ∈ cfg.stackWithIndex ∨ (f'.toFrame = g ∧ f'.index = frame.index) := by
  obtain ⟨stack_eq, hidx⟩ := stack_eq_of_stackWithIndex_getLast? hframe
  unfold RuntimeConfig.stackWithIndex at hf' ⊢
  rw [hstack, List.mapIdx_concat, List.mem_append, List.mem_singleton] at hf'
  rcases hf' with hf' | rfl
  · rw [stack_eq, List.mapIdx_concat]
    exact Or.inl (List.mem_append_left _ hf')
  · exact Or.inr ⟨rfl, hidx.symm⟩

-- swap never changes the stack's sequence of region ids.
theorem swap_stack_regionIds (h : swap x yf cfg = some cfg') :
    cfg'.stack.map Frame.regionId = cfg.stack.map Frame.regionId := by
  obtain ⟨frame, hframe, _, _, _, ⟨_, -, -, -, rfl⟩ | ⟨_, _, -, -, -, -, -, -, rfl⟩ |
    ⟨_, _, -, -, -, -, -, rfl⟩⟩ :=
    swap_cases_norm h
  case inr.inr => rfl
  all_goals
    conv_rhs => rw [(stack_eq_of_stackWithIndex_getLast? hframe).1]
    simp

-- swap only permutes the config's object ids.
theorem swap_objectIds_perm (h : swap x yf cfg = some cfg') : cfg'.objectIds.Perm cfg.objectIds := by
  obtain ⟨frame, hframe, _, yoid, obj, ⟨_, -, hobj, -, rfl⟩ | ⟨region, _, hregion, hobj, -, -, -, -, rfl⟩ |
    ⟨region, _, hregion, hobj, -, -, -, rfl⟩⟩ := swap_cases_norm h
  all_goals
    have stack_eq := (stack_eq_of_stackWithIndex_getLast? hframe).1
    have keys_perm := fun v => AList.keys_insert_perm_of_mem (v := v) (AList.mem_keys_of_lookup_eq_some hobj)
    unfold RuntimeConfig.objectIds
  · conv_rhs => rw [stack_eq]
    rw [stack_objectIds_append_singleton, stack_objectIds_append_singleton]
    exact ((keys_perm _).append_left _).append_right _
  · refine List.Perm.append (List.Perm.of_eq ?_) (heap_insert_objectIds_perm hregion (keys_perm _))
    conv_rhs => rw [stack_eq]
    rw [stack_objectIds_append_singleton, stack_objectIds_append_singleton]
    rfl
  · exact (heap_insert_objectIds_perm hregion (keys_perm _)).append_left _

-- swap never changes the heap's key set.
theorem swap_heap_keys (h : swap x yf cfg = some cfg') (rid : RegionId) :
    rid ∈ cfg'.heap.keys ↔ rid ∈ cfg.heap.keys := by
  obtain ⟨frame, -, _, _, _, ⟨-, -, -, -, rfl⟩ | ⟨_, _, hregion, -, -, -, -, -, rfl⟩ |
    ⟨_, _, hregion, -, -, -, -, rfl⟩⟩ := swap_cases_norm h
  · rfl
  all_goals exact heap_insert_keys_mem (AList.mem_keys_of_lookup_eq_some hregion) rid

-- swap never changes any region's status.
theorem swap_heap_status (h : swap x yf cfg = some cfg') {rid : RegionId} {region : Region}
    (hr : cfg.heap.lookup rid = some region) :
    ∃ region', cfg'.heap.lookup rid = some region' ∧ region'.status = region.status := by
  obtain ⟨frame, -, _, _, _, ⟨-, -, -, -, rfl⟩ | ⟨_, _, hregion, -, -, -, -, -, rfl⟩ |
    ⟨_, _, hregion, -, -, -, -, rfl⟩⟩ := swap_cases_norm h
  · exact ⟨region, hr, rfl⟩
  all_goals
    by_cases heq : rid = frame.regionId
    · subst heq
      rw [hregion, Option.some_inj] at hr
      exact ⟨_, AList.lookup_insert cfg.heap, hr ▸ rfl⟩
    · exact ⟨region, by rw [AList.lookup_insert_ne heq]; exact hr, rfl⟩

-- swap never changes any object's location.
theorem swap_loc_eq (vcfg : ValidConfig cfg) (h : swap x yf cfg = some cfg') (oid : ObjectId) :
    (Reference.OId oid).loc? cfg' = (Reference.OId oid).loc? cfg := by
  obtain ⟨frame, hframe, _, yoid, obj, ⟨_, -, hobj, -, rfl⟩ | ⟨region, xRef, hregion, hobj, -, -, -, -, rfl⟩ |
    ⟨_, _, hregion, hobj, -, -, -, rfl⟩⟩ := swap_cases_norm h
  · exact (swap_corollary_stack_loc_eq hframe hobj oid).symm
  · rw [eq_comm, swap_corollary_region_loc_eq
      (newRegion := { region with objMap := region.objMap.insert yoid (obj.insert yf.field xRef) })
      vcfg hregion hobj rfl oid]
    exact swap_corollary_stack_varmap_loc_eq (by exact hframe) oid
  · exact (swap_corollary_region_loc_eq vcfg hregion hobj rfl oid).symm

-- Every post-swap ref was already a ref, or (SWAP-REGION-BRIDGE) wraps an existing object id.
theorem swap_refs_mem (vcfg : ValidConfig cfg) (h : swap x yf cfg = some cfg') {r : Reference}
    (hr : r ∈ cfg'.refs) : r ∈ cfg.refs ∨ ∃ oid ∈ cfg.objectIds, r = Reference.OId oid := by
  obtain ⟨frame, hframe, yfRef, yoid, obj, ⟨xRef, hxr, hobj, hfield, rfl⟩ |
    ⟨region, xRef, hregion, hobj, hfield, hxr, -, -, rfl⟩ | ⟨region, yfoid, hregion, hobj, -, -, -, rfl⟩⟩ :=
    swap_cases_norm h
  all_goals
    have stack_eq := (stack_eq_of_stackWithIndex_getLast? hframe).1
    have hF : ∀ r ∈ frame.refs, r ∈ cfg.refs := fun r h =>
      (mem_refs_of_stack_eq stack_eq).mpr (Or.inl (Or.inr h))
    have hH : ∀ r ∈ Heap.refs cfg.heap, r ∈ cfg.refs := fun r h => List.mem_append_right _ h
  · left
    rw [mem_refs_of_stack_eq rfl] at hr
    rw [mem_refs_of_stack_eq stack_eq]
    rcases hr with (hr | hr) | hr
    · exact Or.inl (Or.inl hr)
    · exact Or.inl (Or.inr (swap_stack_frame_refs_mem hxr hobj hfield hr))
    · exact Or.inr hr
  · left
    rw [mem_refs_of_stack_eq rfl] at hr
    rcases hr with (hr | hr) | hr
    · exact (mem_refs_of_stack_eq stack_eq).mpr (Or.inl (Or.inl hr))
    · rcases frame_varMap_insert_refs_mem hr with rfl | hr
      · exact hH _ (heap_refs_mem_of_lookup hregion
          (objMap_bind_refs_mem_of_lookup hobj (alist_lookup_mem_values hfield)))
      · exact hF _ hr
    · rcases heap_insert_refs_mem (AList.mem_keys_of_lookup_eq_some hregion) hr with hr | hr
      · rcases objMap_insert_field_refs_mem hobj hr with rfl | hr
        · exact hF _ (List.mem_append_right _ (alist_lookup_mem_values hxr))
        · exact hH _ (heap_refs_mem_of_lookup hregion hr)
      · exact hH _ hr
  · rcases List.mem_append.mp hr with hr | hr
    · exact Or.inl (List.mem_append_left _ hr)
    rcases heap_insert_refs_mem (AList.mem_keys_of_lookup_eq_some hregion) hr with hr | hr
    · rcases objMap_insert_field_refs_mem hobj hr with rfl | hr
      · have hmem := AList.lookup_mem_entries hregion
        exact Or.inr ⟨_, List.mem_append_right _ (heap_objectIds_of_mem hmem
          (AList.mem_keys.mp (vcfg.h1 region (List.mem_map_of_mem (f := (·.2)) hmem)))), rfl⟩
      · exact Or.inl (hH _ (heap_refs_mem_of_lookup hregion hr))
    · exact Or.inl (hH _ hr)

-- Every post-swap frame is an old frame, or sits at the old last frame's index with refs from that frame or its region.
theorem swap_stackWithIndex_mem (h : swap x yf cfg = some cfg') {f' : FrameWithIndex}
    (hf' : f' ∈ cfg'.stackWithIndex) :
    f' ∈ cfg.stackWithIndex ∨ ∃ frame ∈ cfg.stackWithIndex, f'.index = frame.index ∧
      ∀ r ∈ f'.refs, r ∈ frame.refs ∨
        ∃ region, cfg.heap.lookup frame.regionId = some region ∧ r ∈ region.refs := by
  obtain ⟨frame, hframe, yfRef, yoid, obj, ⟨xRef, hxr, hobj, hfield, rfl⟩ |
    ⟨region, xRef, hregion, hobj, hfield, -, -, -, rfl⟩ | ⟨_, _, -, -, -, -, -, rfl⟩⟩ := swap_cases_norm h
  case inr.inr => exact Or.inl hf'
  all_goals
    refine (stackWithIndex_mem_of_last_replace hframe rfl hf').imp_right fun ⟨hg, hidx⟩ =>
      ⟨frame, List.mem_of_getLast? hframe, hidx, fun r hr => ?_⟩
    rw [hg] at hr
  · exact Or.inl (swap_stack_frame_refs_mem hxr hobj hfield hr)
  · rcases frame_varMap_insert_refs_mem hr with rfl | hr
    · exact Or.inr ⟨region, hregion, objMap_bind_refs_mem_of_lookup hobj (alist_lookup_mem_values hfield)⟩
    · exact Or.inl hr

-- Every pre-swap frame has a post-swap counterpart with the same region id and index.
theorem swap_stackWithIndex_transport (h : swap x yf cfg = some cfg') {f : FrameWithIndex}
    (hf : f ∈ cfg.stackWithIndex) : ∃ g ∈ cfg'.stackWithIndex, g.regionId = f.regionId ∧ g.index = f.index := by
  obtain ⟨g, hg, hidx, hrid⟩ := stackWithIndex_frame_transport_up_of_shape_eq (cfg' := cfg')
    (proj := Frame.regionId) (fun n => by rw [← List.getElem?_map, ← List.getElem?_map, swap_stack_regionIds h])
    f hf
  exact ⟨g, hg, hrid, hidx⟩

-- swap preserves the total number of stored references to each region.
theorem swap_rid_count (h : swap x yf cfg = some cfg') (rid : RegionId) :
    cfg'.stack.refs.count (Reference.RId rid) + cfg'.heap.refs.count (Reference.RId rid) =
    cfg.stack.refs.count (Reference.RId rid) + cfg.heap.refs.count (Reference.RId rid) := by
  obtain ⟨frame, hframe, yfRef, yoid, obj, ⟨xRef, hxr, hobj, hfield, rfl⟩ |
    ⟨region, xRef, hregion, hobj, hfield, hxr, -, -, rfl⟩ |
    ⟨region, yfoid, hregion, hobj, hfield, rfl, -, rfl⟩⟩ :=
    swap_cases_norm h
  · have h1 := objMap_insert_field_count_eq (v_new := xRef) hobj hfield (Reference.RId rid)
    have h2 := alist_insert_count_eq (v_new := yfRef) (t := Reference.RId rid) hxr
    conv_rhs => rw [(stack_eq_of_stackWithIndex_getLast? hframe).1]
    simp only [stack_refs_append_singleton, List.count_append, Frame.refs]
    omega
  · have h1 := objMap_insert_field_count_eq (v_new := xRef) hobj hfield (Reference.RId rid)
    have h2 := alist_insert_count_eq (v_new := yfRef) (t := Reference.RId rid) hxr
    have h3 := alist_insert_bind_count_eq Region.refs (Reference.RId rid)
      (new := { region with objMap := region.objMap.insert yoid (obj.insert yf.field xRef) }) hregion
    conv_rhs => rw [(stack_eq_of_stackWithIndex_getLast? hframe).1]
    simp only [stack_refs_append_singleton, List.count_append, Frame.refs, Heap.refs, Region.refs] at h3 ⊢
    omega
  · have h1 := objMap_insert_field_count_eq (v_new := Reference.OId region.bridgeObjectId) hobj hfield
      (Reference.RId rid)
    have h3 := alist_insert_bind_count_eq Region.refs (Reference.RId rid) (new := { region with
      bridgeObjectId := yfoid,
      objMap := region.objMap.insert yoid (obj.insert yf.field (Reference.OId region.bridgeObjectId)) }) hregion
    simp only [Heap.refs, Region.refs] at h3 ⊢
    simp only [show ∀ o, (Reference.OId o == Reference.RId rid) = false from fun _ => rfl, Bool.false_eq_true,
      ite_false] at h1
    omega

theorem swap_S1 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  S1 cfg' := by
  intro vcfg h
  unfold S1
  rw [swap_stack_regionIds h]
  exact vcfg.s1

theorem swap_L1 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  L1 cfg' := fun vcfg h => vcfg.l1.perm (swap_objectIds_perm h).symm

theorem swap_L2 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  L2 cfg' := by
  intro vcfg h f hf
  obtain ⟨g, hg, hrid⟩ := List.mem_map.mp (swap_stack_regionIds h ▸ List.mem_map_of_mem (f := Frame.regionId) hf)
  obtain ⟨region, hregion, hopen⟩ := vcfg.l2 g hg
  obtain ⟨region', h', hs⟩ := swap_heap_status h hregion
  exact ⟨region', hrid ▸ h', hs.trans hopen⟩

theorem swap_H1 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  H1 cfg' := by
  intro vcfg h
  obtain ⟨frame, -, yfRef, yoid, obj, ⟨_, -, -, -, rfl⟩ | ⟨region, xRef, hregion, -, -, -, -, -, rfl⟩ |
    ⟨region, yfoid, hregion, -, -, -, hyfl, rfl⟩⟩ := swap_cases_norm h
  · exact vcfg.h1
  all_goals
    intro r hr
    rcases heap_insert_regions_mem hr with rfl | hr
    on_goal 2 => exact vcfg.h1 r hr
    refine (AList.mem_insert _).mpr (Or.inr ?_)
  · exact vcfg.h1 region (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hregion))
  · obtain ⟨region', hregion', hmem⟩ := (oid_loc_rgn_iff_in_heap vcfg).mp hyfl
    rw [hregion, Option.some_inj] at hregion'
    exact hregion' ▸ hmem

theorem swap_H2 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  H2 cfg' := fun vcfg h rid => (swap_rid_count h rid).trans_le (vcfg.h2 rid)

theorem swap_H3 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  H3 cfg' := by
  intro vcfg h rid0 oid0 region0 hlookup0 href0
  rw [swap_loc_eq vcfg h]
  obtain ⟨frame, -, yfRef, yoid, obj, ⟨_, -, -, -, rfl⟩ | ⟨region, xRef, hregion, hobj, -, -, -, hxloc, rfl⟩ |
    ⟨region, yfoid, hregion, hobj, -, -, -, rfl⟩⟩ := swap_cases_norm h
  · exact vcfg.h3 rid0 oid0 region0 hlookup0 href0
  all_goals
    by_cases hrid : rid0 = frame.regionId
    on_goal 2 => exact vcfg.h3 rid0 oid0 region0 (by rwa [AList.lookup_insert_ne hrid] at hlookup0) href0
    subst hrid
    rw [AList.lookup_insert, Option.some_inj] at hlookup0
    subst hlookup0
    rcases objMap_insert_field_refs_mem hobj href0 with heq | horig
    on_goal 2 => exact vcfg.h3 _ _ region hregion horig
  · exact hxloc oid0 heq.symm
  · cases heq
    exact (oid_loc_rgn_iff_in_heap vcfg).mpr ⟨region, hregion,
      vcfg.h1 region (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hregion))⟩

theorem swap_S2 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  S2 cfg' := by
  intro vcfg h f' hf' ref href fid' oid hrefeq hloc
  subst hrefeq
  rw [swap_loc_eq vcfg h] at hloc
  rcases swap_stackWithIndex_mem h hf' with hold | ⟨frame, hframe, hidx, hrefs⟩
  · exact vcfg.s2 f' hold _ href fid' oid rfl hloc
  · rcases hrefs _ href with hr | ⟨region, hregion, hr⟩
    · exact hidx ▸ vcfg.s2 frame hframe _ hr fid' oid rfl hloc
    · rw [vcfg.h3 _ _ region hregion hr] at hloc
      cases hloc

theorem swap_S3 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  S3 cfg' := by
  intro vcfg h f' hf' ref href rid' oid hrefeq hloc
  subst hrefeq
  rw [swap_loc_eq vcfg h] at hloc
  have transport : ∀ f ∈ cfg.stackWithIndex, f.regionId = rid' → f.index ≤ f'.index →
      ∃ g ∈ cfg'.stackWithIndex, g.regionId = rid' ∧ g.index ≤ f'.index := fun f hf hrid hidx => by
    obtain ⟨g, hg, hgrid, hgidx⟩ := swap_stackWithIndex_transport h hf
    exact ⟨g, hg, hgrid.trans hrid, hgidx ▸ hidx⟩
  rcases swap_stackWithIndex_mem h hf' with hold | ⟨frame, hframe, hidx, hrefs⟩
  · obtain ⟨anc, hanc, hrid, hle⟩ := vcfg.s3 f' hold _ href rid' oid rfl hloc
    exact transport anc hanc hrid hle
  · rcases hrefs _ href with hr | ⟨region, hregion, hr⟩
    · obtain ⟨anc, hanc, hrid, hle⟩ := vcfg.s3 frame hframe _ hr rid' oid rfl hloc
      exact transport anc hanc hrid (hidx ▸ hle)
    · rw [vcfg.h3 _ _ region hregion hr, Option.some_inj, Location.Rgn.injEq] at hloc
      exact transport frame hframe hloc hidx.ge

theorem swap_HS1 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  HS1 cfg' := by
  intro vcfg h oid hr
  apply (swap_objectIds_perm h).mem_iff.mpr
  rcases swap_refs_mem vcfg h hr with hr | ⟨oid', hoid', heq⟩
  · exact vcfg.hs1 oid hr
  · cases heq
    exact hoid'

theorem swap_HS2 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  HS2 cfg' := by
  intro vcfg h rid hr
  rw [swap_heap_keys h]
  rcases swap_refs_mem vcfg h hr with hr | ⟨_, _, ⟨⟩⟩
  exact vcfg.hs2 rid hr

theorem swap_valid : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  ValidConfig cfg' := fun vcfg h =>
  { l1 := swap_L1 vcfg h, l2 := swap_L2 vcfg h, h1 := swap_H1 vcfg h, h2 := swap_H2 vcfg h,
    h3 := swap_H3 vcfg h, s1 := swap_S1 vcfg h, s2 := swap_S2 vcfg h, s3 := swap_S3 vcfg h,
    hs1 := swap_HS1 vcfg h, hs2 := swap_HS2 vcfg h }
