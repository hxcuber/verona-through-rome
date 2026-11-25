module

public import Gc.Model.Mutation.FieldAsgn
public import Gc.Model.Preservation.Common

@[expose] public section

-- Membership in the refs of a frame with one object field overwritten.
private theorem frame_insert_field_refs_mem {f : Frame} {oid : ObjectId} {obj : Object} {k : FieldName}
    {v r : Reference} (hobj : f.objMap.lookup oid = some obj)
    (hr : r ∈ Frame.refs { f with objMap := f.objMap.insert oid (obj.insert k v) }) : r = v ∨ r ∈ f.refs := by
  simp only [Frame.refs, List.mem_append] at hr ⊢
  rcases hr with hr | hr
  · exact (objMap_insert_field_refs_mem hobj hr).imp_right Or.inl
  · exact Or.inr (Or.inr hr)

-- Writing a non-`t` value into one field never increases an ObjMap's bind-refs count of `t`.
private theorem objMap_insert_field_count_le {m : ObjMap} {oid : ObjectId} {obj : Object} {k : FieldName}
    {v t : Reference} (hobj : m.lookup oid = some obj) (hne : (v == t) = false) :
    ((m.insert oid (obj.insert k v)).entries.map (·.2) >>= Object.refs).count t ≤
      (m.entries.map (·.2) >>= Object.refs).count t := by
  have h1 : ((m.insert oid (obj.insert k v)).entries.map (·.2) >>= Object.refs).count t + (Object.refs obj).count t =
      (m.entries.map (·.2) >>= Object.refs).count t + (Object.refs (obj.insert k v)).count t :=
    alist_insert_bind_count_eq Object.refs t hobj
  have h2 : (Object.refs (obj.insert k v)).count t ≤ (Object.refs obj).count t := by
    unfold Object.refs
    rw [AList.entries_insert, List.map_cons, List.count_cons, hne]
    simpa using ((List.kerase_sublist k obj.entries).map (·.2)).count_le t
  omega

-- FIELD-ASGN-STACK keeps the last frame's objMap key set (up to perm), so `Reference.loc?` transports.
theorem fieldAsgn_corollary_stack_loc_eq {cfg : RuntimeConfig} {frame : FrameWithIndex} {oid : ObjectId}
    {obj : Object} {field : FieldName} {yRef : Reference}
    (hframe : cfg.stackWithIndex.getLast? = some frame) (hobj : frame.objMap.lookup oid = some obj)
    (oid' : ObjectId) :
    (Reference.OId oid').loc? cfg =
      (Reference.OId oid').loc? { cfg with stack := cfg.stack.dropLast ++
        [({ frame with objMap := frame.objMap.insert oid (obj.insert field yRef) } : Frame)] } := by
  have hkeys : (frame.objMap.insert oid (obj.insert field yRef)).keys.Perm frame.objMap.keys :=
    AList.keys_insert_perm_of_mem (AList.mem_keys_of_lookup_eq_some hobj)
  obtain ⟨stack_eq, _⟩ := stack_eq_of_stackWithIndex_getLast? hframe
  refine loc_eq_of_find_map_eq ?_ rfl
  unfold RuntimeConfig.stackWithIndex
  conv_lhs => rw [stack_eq]
  simp only [List.mapIdx_concat, List.findRev?_eq_find?_reverse, List.reverse_append, List.reverse_singleton,
    List.singleton_append, List.find?_cons, hkeys.contains_eq]
  cases frame.objMap.keys.contains oid' <;> rfl

-- FIELD-ASGN-REGION only inserts at present keys, so `Reference.loc?` transports for every object id.
theorem fieldAsgn_corollary_region_loc_eq {cfg : RuntimeConfig} {rid oid : ObjectId} {region : Region}
    {obj : Object} {field : FieldName} {yRef : Reference} (vcfg : ValidConfig cfg)
    (hregion : cfg.heap.lookup rid = some region) (hobj : region.objMap.lookup oid = some obj)
    (oid' : ObjectId) :
    (Reference.OId oid').loc? cfg =
      (Reference.OId oid').loc? { cfg with heap := cfg.heap.insert rid { region with objMap := region.objMap.insert oid (obj.insert field yRef) } } := by
  have keys_perm : (region.objMap.insert oid (obj.insert field yRef)).keys.Perm region.objMap.keys :=
    AList.keys_insert_perm_of_mem (AList.mem_keys_of_lookup_eq_some hobj)
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

-- A resolved object reference is stored in some frame, or is the bridge object of some frame's region.
private theorem resolveV_oid_source {cfg : RuntimeConfig} {var : VarName} {oid : ObjectId}
    (hrv : resolveV var cfg = some (Reference.OId oid)) : ∃ f ∈ cfg.stackWithIndex,
      Reference.OId oid ∈ f.refs ∨
        ∃ region, cfg.heap.lookup f.regionId = some region ∧ region.bridgeObjectId = oid := by
  unfold resolveV at hrv
  rcases hf : cfg.stackWithIndex.findRev? (fun frame => frame.varMap.keys.contains var ∨ frame.bridgeVar == var)
    with _ | f
  · rw [hf] at hrv
    contradiction
  rw [hf] at hrv
  dsimp at hrv
  refine ⟨f, ?_, ?_⟩
  · rw [List.findRev?_eq_find?_reverse] at hf
    exact List.mem_reverse.mp (List.mem_of_find?_eq_some hf)
  rcases hl : f.varMap.lookup var with _ | r
  · rw [hl] at hrv
    rcases hreg : cfg.heap.lookup f.regionId with _ | region <;> split_ifs at hrv <;> simp_all
  · rw [hl] at hrv
    cases hrv
    exact Or.inl (List.mem_append_right _ (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hl)))

-- A resolved object reference names a live object.
private theorem resolveV_oid_mem_objectIds {cfg : RuntimeConfig} (vcfg : ValidConfig cfg) {var : VarName}
    {oid : ObjectId} (hrv : resolveV var cfg = some (Reference.OId oid)) : oid ∈ cfg.objectIds := by
  obtain ⟨f, hf, hr | ⟨region, hregion, rfl⟩⟩ := resolveV_oid_source hrv
  · exact vcfg.hs1 oid (refs_mem_of_stackWithIndex hf hr)
  · have hmem := AList.lookup_mem_entries hregion
    exact List.mem_append_right _ (heap_objectIds_of_mem hmem
      (AList.mem_keys.mp (vcfg.h1 region (List.mem_map_of_mem (f := (·.2)) hmem))))

-- A resolved object reference living in a region has that region owned by some on-stack frame.
private theorem resolveV_loc_ancestor {cfg : RuntimeConfig} (vcfg : ValidConfig cfg) {var : VarName}
    {oid : ObjectId} {rid : RegionId} (hrv : resolveV var cfg = some (Reference.OId oid))
    (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn rid)) :
    ∃ g ∈ cfg.stackWithIndex, g.regionId = rid ∧ g.index < cfg.stack.length := by
  obtain ⟨f, hf, hsrc⟩ := resolveV_oid_source hrv
  have hlt : f.index < cfg.stack.length := by
    obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp hf
    exact hn
  rcases hsrc with hr | ⟨region, hregion, rfl⟩
  · obtain ⟨g, hg, hrid, hle⟩ := vcfg.s3 f hf _ hr rid _ rfl hloc
    exact ⟨g, hg, hrid, hle.trans_lt hlt⟩
  · have hb := (oid_loc_rgn_iff_in_heap vcfg).mpr ⟨region, hregion,
      vcfg.h1 region (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hregion))⟩
    rw [hloc, Option.some_inj, Location.Rgn.injEq] at hb
    exact ⟨f, hf, hb.symm, hlt⟩

-- fieldAsgn never changes the stack's sequence of region ids.
private theorem fieldAsgn_stack_regionIds (h : fieldAsgn x yf cfg = some cfg') :
    cfg'.stack.map Frame.regionId = cfg.stack.map Frame.regionId := by
  obtain ⟨frame, hframe, ⟨_, _, _, -, -, -, -, rfl⟩ | ⟨_, _, _, _, _, -, -, -, -, -, -, -, -, rfl⟩⟩ :=
    fieldAsgn_cases h
  · conv_rhs => rw [(stack_eq_of_stackWithIndex_getLast? hframe).1]
    simp
  · rfl

-- fieldAsgn only permutes the config's object ids.
private theorem fieldAsgn_objectIds_perm (h : fieldAsgn x yf cfg = some cfg') :
    cfg'.objectIds.Perm cfg.objectIds := by
  obtain ⟨frame, hframe, ⟨_, _, _, -, -, -, hobj, rfl⟩ |
    ⟨_, _, _, _, _, -, -, -, hregion, hobj, -, -, -, rfl⟩⟩ :=
    fieldAsgn_cases h
  all_goals
    have keys_perm := fun v => AList.keys_insert_perm_of_mem (v := v) (AList.mem_keys_of_lookup_eq_some hobj)
    unfold RuntimeConfig.objectIds
  · conv_rhs => rw [(stack_eq_of_stackWithIndex_getLast? hframe).1]
    simp only [Stack.objectIds, List.map_append, List.bind_eq_flatMap, List.flatMap_id, List.flatten_append,
      List.map_singleton, List.flatten_singleton]
    exact ((keys_perm _).append_left _).append_right _
  · exact (heap_insert_objectIds_perm hregion (keys_perm _)).append_left _

-- fieldAsgn never changes the heap's key set.
private theorem fieldAsgn_heap_keys (h : fieldAsgn x yf cfg = some cfg') (rid : RegionId) :
    rid ∈ cfg'.heap.keys ↔ rid ∈ cfg.heap.keys := by
  obtain ⟨_, -, ⟨_, _, _, -, -, -, -, rfl⟩ | ⟨_, _, _, _, _, -, -, -, hregion, -, -, -, -, rfl⟩⟩ :=
    fieldAsgn_cases h
  · rfl
  · exact heap_insert_keys_mem (AList.mem_keys_of_lookup_eq_some hregion) rid

-- fieldAsgn never changes any region's status.
private theorem fieldAsgn_heap_status (h : fieldAsgn x yf cfg = some cfg') {rid : RegionId} {region : Region}
    (hr : cfg.heap.lookup rid = some region) :
    ∃ region', cfg'.heap.lookup rid = some region' ∧ region'.status = region.status := by
  obtain ⟨_, -, ⟨_, _, _, -, -, -, -, rfl⟩ | ⟨_, _, rid0, _, _, -, -, -, hregion, -, -, -, -, rfl⟩⟩ :=
    fieldAsgn_cases h
  · exact ⟨region, hr, rfl⟩
  by_cases heq : rid = rid0
  · subst heq
    rw [hregion, Option.some_inj] at hr
    exact ⟨_, AList.lookup_insert cfg.heap, hr ▸ rfl⟩
  · exact ⟨region, by rw [AList.lookup_insert_ne heq]; exact hr, rfl⟩

-- fieldAsgn never changes any object's location.
private theorem fieldAsgn_loc_eq (vcfg : ValidConfig cfg) (h : fieldAsgn x yf cfg = some cfg') (oid : ObjectId) :
    (Reference.OId oid).loc? cfg' = (Reference.OId oid).loc? cfg := by
  obtain ⟨_, hframe, ⟨_, _, _, -, -, -, hobj, rfl⟩ |
    ⟨_, _, _, _, _, -, -, -, hregion, hobj, -, -, -, rfl⟩⟩ :=
    fieldAsgn_cases h
  · exact (fieldAsgn_corollary_stack_loc_eq hframe hobj oid).symm
  · exact (fieldAsgn_corollary_region_loc_eq vcfg hregion hobj oid).symm

-- Every post-fieldAsgn ref was already a ref, or is the newly-written (live) object reference.
private theorem fieldAsgn_refs_mem (vcfg : ValidConfig cfg) (h : fieldAsgn x yf cfg = some cfg') {r : Reference}
    (hr : r ∈ cfg'.refs) : r ∈ cfg.refs ∨ ∃ oid ∈ cfg.objectIds, r = Reference.OId oid := by
  obtain ⟨frame, hframe, ⟨_, _, _, -, hyr, -, hobj, rfl⟩ |
    ⟨_, _, _, region, _, -, hyr, -, hregion, hobj, -, -, -, rfl⟩⟩ :=
    fieldAsgn_cases h
  · have stack_eq := (stack_eq_of_stackWithIndex_getLast? hframe).1
    rw [mem_refs_of_stack_eq rfl] at hr
    rcases hr with (hr | hr) | hr
    · exact Or.inl ((mem_refs_of_stack_eq stack_eq).mpr (Or.inl (Or.inl hr)))
    · rcases frame_insert_field_refs_mem hobj hr with rfl | hr
      · exact Or.inr ⟨_, resolveV_oid_mem_objectIds vcfg hyr, rfl⟩
      · exact Or.inl ((mem_refs_of_stack_eq stack_eq).mpr (Or.inl (Or.inr hr)))
    · exact Or.inl ((mem_refs_of_stack_eq stack_eq).mpr (Or.inr hr))
  · rcases List.mem_append.mp hr with hr | hr
    · exact Or.inl (List.mem_append_left _ hr)
    rcases heap_insert_refs_mem (AList.mem_keys_of_lookup_eq_some hregion) hr with hr | hr
    · rcases objMap_insert_field_refs_mem hobj hr with rfl | hr
      · exact Or.inr ⟨_, resolveV_oid_mem_objectIds vcfg hyr, rfl⟩
      · exact Or.inl (List.mem_append_right _ (heap_refs_mem_of_lookup hregion hr))
    · exact Or.inl (List.mem_append_right _ hr)

-- Every post-fieldAsgn frame is an old frame, or replaces the last frame with refs from it or the written value.
private theorem fieldAsgn_stackWithIndex_mem (h : fieldAsgn x y cfg = some cfg') {f' : FrameWithIndex}
    (hf' : f' ∈ cfg'.stackWithIndex) :
    f' ∈ cfg.stackWithIndex ∨ ∃ frame, cfg.stackWithIndex.getLast? = some frame ∧ f'.index = frame.index ∧
      ∀ r ∈ f'.refs, r ∈ frame.refs ∨
        ∃ oid, resolveV y cfg = some (Reference.OId oid) ∧ r = Reference.OId oid := by
  obtain ⟨frame, hframe, ⟨_, _, _, -, hyr, -, hobj, rfl⟩ | ⟨_, _, _, _, _, -, -, -, -, -, -, -, -, rfl⟩⟩ :=
    fieldAsgn_cases h
  · obtain ⟨stack_eq, hidx⟩ := stack_eq_of_stackWithIndex_getLast? hframe
    unfold RuntimeConfig.stackWithIndex at hf'
    rw [List.mapIdx_concat, List.mem_append, List.mem_singleton] at hf'
    rcases hf' with hf' | rfl
    · left
      unfold RuntimeConfig.stackWithIndex
      rw [stack_eq, List.mapIdx_concat]
      exact List.mem_append_left _ hf'
    · refine Or.inr ⟨frame, hframe, hidx.symm, fun r hr => ?_⟩
      rcases frame_insert_field_refs_mem hobj hr with rfl | hr
      · exact Or.inr ⟨_, hyr, rfl⟩
      · exact Or.inl hr
  · exact Or.inl hf'

theorem fieldAsgn_L1 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  L1 cfg' := fun vcfg h => vcfg.l1.perm (fieldAsgn_objectIds_perm h).symm

theorem fieldAsgn_L2 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  L2 cfg' := by
  intro vcfg h f hf
  obtain ⟨g, hg, hrid⟩ :=
    List.mem_map.mp (fieldAsgn_stack_regionIds h ▸ List.mem_map_of_mem (f := Frame.regionId) hf)
  obtain ⟨region, hregion, hopen⟩ := vcfg.l2 g hg
  obtain ⟨region', h', hs⟩ := fieldAsgn_heap_status h hregion
  exact ⟨region', hrid ▸ h', hs.trans hopen⟩

theorem fieldAsgn_S1 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  S1 cfg' := fun vcfg h => by
  unfold S1
  rw [fieldAsgn_stack_regionIds h]
  exact vcfg.s1

theorem fieldAsgn_H1 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  H1 cfg' := by
  intro vcfg h
  obtain ⟨_, -, ⟨_, _, _, -, -, -, -, rfl⟩ | ⟨_, _, _, region, _, -, -, -, hregion, -, -, -, -, rfl⟩⟩ :=
    fieldAsgn_cases h
  · exact vcfg.h1
  intro r hr
  unfold Heap.regions at hr
  rw [AList.entries_insert, List.map_cons, List.mem_cons] at hr
  rcases hr with rfl | hr
  · exact (AList.mem_insert _).mpr
      (Or.inr (vcfg.h1 region (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hregion))))
  · exact vcfg.h1 r (((List.kerase_sublist _ cfg.heap.entries).map _).mem hr)

theorem fieldAsgn_H2 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  H2 cfg' := by
  intro vcfg h rid
  refine le_trans ?_ (vcfg.h2 rid)
  obtain ⟨frame, hframe, ⟨_, oid_y, _, -, -, -, hobj, rfl⟩ |
    ⟨oid, oid_y, _, region, obj, -, -, -, hregion, hobj, -, -, -, rfl⟩⟩ := fieldAsgn_cases h
  · have h1 := objMap_insert_field_count_le (k := x.field) (v := Reference.OId oid_y) hobj (t := Reference.RId rid) rfl
    conv_rhs => rw [(stack_eq_of_stackWithIndex_getLast? hframe).1]
    simp only [Stack.refs, List.map_append, List.bind_eq_flatMap, List.flatMap_id, List.flatten_append,
      List.map_singleton, List.flatten_singleton, List.count_append, Frame.refs] at h1 ⊢
    omega
  · have h1 := objMap_insert_field_count_le (k := x.field) (v := Reference.OId oid_y) hobj (t := Reference.RId rid) rfl
    have h3 := alist_insert_bind_count_eq Region.refs (Reference.RId rid) hregion
      (new := { region with objMap := region.objMap.insert oid (obj.insert x.field (Reference.OId oid_y)) })
    simp only [Heap.refs, Region.refs] at h3 ⊢
    omega

theorem fieldAsgn_H3 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  H3 cfg' := by
  intro vcfg h rid0 oid0 region0 hlookup0 href0
  rw [fieldAsgn_loc_eq vcfg h]
  obtain ⟨_, -, ⟨_, _, _, -, -, -, -, rfl⟩ |
    ⟨_, _, rid, region, _, -, -, -, hregion, hobj, hyloc, -, -, rfl⟩⟩ :=
    fieldAsgn_cases h
  · exact vcfg.h3 rid0 oid0 region0 hlookup0 href0
  by_cases hrid : rid0 = rid
  · subst hrid
    rw [AList.lookup_insert, Option.some_inj] at hlookup0
    subst hlookup0
    rcases objMap_insert_field_refs_mem hobj href0 with heq | horig
    · exact Reference.OId.inj heq ▸ hyloc
    · exact vcfg.h3 _ _ region hregion horig
  · exact vcfg.h3 rid0 oid0 region0 (by rwa [AList.lookup_insert_ne hrid] at hlookup0) href0

theorem fieldAsgn_S2 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  S2 cfg' := by
  intro vcfg h f' hf' ref href fid' oid hrefeq hloc
  subst hrefeq
  rw [fieldAsgn_loc_eq vcfg h] at hloc
  rcases fieldAsgn_stackWithIndex_mem h hf' with hold | ⟨frame, hframe, hidx, hrefs⟩
  · exact vcfg.s2 f' hold _ href fid' oid rfl hloc
  rcases hrefs _ href with hr | ⟨_, -, ⟨⟩⟩
  · exact hidx ▸ vcfg.s2 frame (List.mem_of_getLast? hframe) _ hr fid' oid rfl hloc
  · obtain ⟨_, hw, -⟩ := (oid_loc_stk_iff_in_stack vcfg).mp hloc
    obtain ⟨stack_eq, hfidx⟩ := stack_eq_of_stackWithIndex_getLast? hframe
    have hlt := (List.getElem?_eq_some_iff.mp hw).1
    have hlen := congrArg List.length stack_eq
    simp only [RuntimeConfig.stackWithIndex, List.length_mapIdx, List.length_append, List.length_singleton] at hlt hlen
    rw [hidx, hfidx]
    exact Nat.le_of_lt_succ (by omega)

theorem fieldAsgn_S3 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  S3 cfg' := by
  intro vcfg h f' hf' ref href rid' oid hrefeq hloc
  subst hrefeq
  rw [fieldAsgn_loc_eq vcfg h] at hloc
  have transport : ∀ f ∈ cfg.stackWithIndex, f.regionId = rid' → f.index ≤ f'.index →
      ∃ g ∈ cfg'.stackWithIndex, g.regionId = rid' ∧ g.index ≤ f'.index := fun f hf hrid hidx => by
    obtain ⟨g, hg, hgidx, hgrid⟩ := stackWithIndex_frame_transport_up_of_shape_eq (cfg' := cfg')
      (proj := Frame.regionId)
      (fun n => by rw [← List.getElem?_map, ← List.getElem?_map, fieldAsgn_stack_regionIds h]) f hf
    exact ⟨g, hg, hgrid.trans hrid, hgidx ▸ hidx⟩
  rcases fieldAsgn_stackWithIndex_mem h hf' with hold | ⟨frame, hframe, hidx, hrefs⟩
  · obtain ⟨anc, hanc, hrid, hle⟩ := vcfg.s3 f' hold _ href rid' oid rfl hloc
    exact transport anc hanc hrid hle
  rcases hrefs _ href with hr | ⟨_, hyr, ⟨⟩⟩
  · obtain ⟨anc, hanc, hrid, hle⟩ := vcfg.s3 frame (List.mem_of_getLast? hframe) _ hr rid' oid rfl hloc
    exact transport anc hanc hrid (hidx ▸ hle)
  · obtain ⟨anc, hanc, hrid, hlt⟩ := resolveV_loc_ancestor vcfg hyr hloc
    obtain ⟨stack_eq, hfidx⟩ := stack_eq_of_stackWithIndex_getLast? hframe
    have hlen := congrArg List.length stack_eq
    simp only [List.length_append, List.length_singleton] at hlen
    rw [hlen] at hlt
    exact transport anc hanc hrid (by rw [hidx, hfidx]; exact Nat.le_of_lt_succ hlt)

theorem fieldAsgn_HS1 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  HS1 cfg' := by
  intro vcfg h oid hr
  apply (fieldAsgn_objectIds_perm h).mem_iff.mpr
  rcases fieldAsgn_refs_mem vcfg h hr with hr | ⟨oid', hoid', ⟨⟩⟩
  · exact vcfg.hs1 oid hr
  · exact hoid'

theorem fieldAsgn_HS2 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  HS2 cfg' := by
  intro vcfg h rid hr
  rw [fieldAsgn_heap_keys h]
  rcases fieldAsgn_refs_mem vcfg h hr with hr | ⟨_, _, ⟨⟩⟩
  exact vcfg.hs2 rid hr

theorem fieldAsgn_valid : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  ValidConfig cfg' := fun vcfg h =>
  { l1 := fieldAsgn_L1 vcfg h, l2 := fieldAsgn_L2 vcfg h, h1 := fieldAsgn_H1 vcfg h, h2 := fieldAsgn_H2 vcfg h,
    h3 := fieldAsgn_H3 vcfg h, s1 := fieldAsgn_S1 vcfg h, s2 := fieldAsgn_S2 vcfg h, s3 := fieldAsgn_S3 vcfg h,
    hs1 := fieldAsgn_HS1 vcfg h, hs2 := fieldAsgn_HS2 vcfg h }
