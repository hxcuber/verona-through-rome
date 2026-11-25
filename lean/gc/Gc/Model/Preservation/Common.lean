module

public import Gc.Model.Types
public import Gc.Model.Helpers
public import Gc.Model.Validity
public import Gc.Model.Theorems

public import Mathlib.Data.List.Infix

@[expose] public section

-- Generic, non-operation-specific facts shared by several `Preservation`/`Reachability` files.

-- A `heap.entries` membership witnessing `oid` inside some region's `objMap` puts `oid` in the
-- heap's own flattened `objectIds`.
theorem heap_objectIds_of_mem {heap : Heap} :
  (⟨rid, region⟩ : Sigma (fun _ : RegionId => Region)) ∈ heap.entries → oid ∈ region.objMap.keys →
  oid ∈ heap.objectIds := by
  intro mem in_region
  unfold Heap.objectIds
  apply List.mem_flatten.mpr
  refine ⟨region.objectIds, List.mem_map_of_mem (f := λ e => e.2.objectIds) mem, ?_⟩
  unfold Region.objectIds
  exact in_region

-- Two elements of `cfg.stackWithIndex` with the same `.index` are the same element -- `.index` is
-- assigned to be the element's own position by `mapIdx`, so equal indices means equal positions.
theorem swap_corollary_stackWithIndex_index_inj {cfg : RuntimeConfig} {f1 f2 : FrameWithIndex}
    (h1 : f1 ∈ cfg.stackWithIndex) (h2 : f2 ∈ cfg.stackWithIndex) (heq : f1.index = f2.index) :
    f1 = f2 := by
  unfold RuntimeConfig.stackWithIndex at h1 h2
  obtain ⟨n1, hn1, e1⟩ := List.mem_mapIdx.mp h1
  obtain ⟨n2, hn2, e2⟩ := List.mem_mapIdx.mp h2
  have hi1 : f1.index = n1 := by rw [← e1]
  have hi2 : f2.index = n2 := by rw [← e2]
  have hn : n1 = n2 := by rw [hi1, hi2] at heq; exact heq
  subst hn
  rw [← e1, ← e2]

-- resolveFA's own `.find? (index==fid)` step recovers exactly the frame already known to have
-- that index, via the index-injectivity fact above plus the generic find?-uniqueness lemma.
theorem swap_corollary_stackWithIndex_find_eq {cfg : RuntimeConfig} {frame : FrameWithIndex}
    (hmem : frame ∈ cfg.stackWithIndex) :
    cfg.stackWithIndex.find? (fun f => f.index == frame.index) = some frame := by
  apply List.find?_eq_some_of_unique hmem (by simp)
  intro f' hf'_mem hf'_pred
  rw [beq_iff_eq] at hf'_pred
  exact swap_corollary_stackWithIndex_index_inj hf'_mem hmem hf'_pred

-- `S1`'s regionId-uniqueness at the `FrameWithIndex` level: two stack frames sharing a `regionId`
-- must be the *same* frame (same index).
theorem merge_corollary_regionId_unique_index {cfg : RuntimeConfig} (s1 : S1 cfg)
    {frameZ frameW : FrameWithIndex} (hZ : frameZ ∈ cfg.stackWithIndex) (hW : frameW ∈ cfg.stackWithIndex)
    (heq : frameZ.regionId = frameW.regionId) : frameZ.index = frameW.index := by
  unfold RuntimeConfig.stackWithIndex at hZ hW
  obtain ⟨nZ, hnZ, hZeq⟩ := List.mem_mapIdx.mp hZ
  obtain ⟨nW, hnW, hWeq⟩ := List.mem_mapIdx.mp hW
  have hZidx : frameZ.index = nZ := by rw [← hZeq]
  have hWidx : frameW.index = nW := by rw [← hWeq]
  have hZregion : frameZ.regionId = cfg.stack[nZ].regionId := by rw [← hZeq]
  have hWregion : frameW.regionId = cfg.stack[nW].regionId := by rw [← hWeq]
  unfold S1 at s1
  have hnZ' : nZ < (cfg.stack.map (fun f => f.regionId)).length := by rwa [List.length_map]
  have hnW' : nW < (cfg.stack.map (fun f => f.regionId)).length := by rwa [List.length_map]
  have hgetZ : (cfg.stack.map (fun f => f.regionId))[nZ] = frameZ.regionId := by
    rw [List.getElem_map]; rw [hZregion]
  have hgetW : (cfg.stack.map (fun f => f.regionId))[nW] = frameW.regionId := by
    rw [List.getElem_map]; rw [hWregion]
  have : nZ = nW := by
    apply (List.Nodup.getElem_inj_iff s1 (hi := hnZ') (hj := hnW')).mp
    rw [hgetZ, hgetW, heq]
  rw [hZidx, hWidx, this]

-- The `.index` field of an element found by direct `stackWithIndex[fid]?` lookup always equals
-- the lookup index itself -- `.index` is assigned to be the element's own `mapIdx` position, so an
-- `[fid]?`-indexed lookup and the element's own `.index` necessarily agree. Fully generic (no
-- mutation/`ValidConfig` involved at all) -- previously three byte-for-byte-identical private
-- copies (`enter`/`exit`/`makeObjStack_corollary_getElem_index_eq`).
theorem stackWithIndex_getElem_index_eq {cfg : RuntimeConfig} {fid : Index} {frame : FrameWithIndex}
    (h : cfg.stackWithIndex[fid]? = some frame) : frame.index = fid := by
  unfold RuntimeConfig.stackWithIndex at h
  rw [List.getElem?_mapIdx, Option.map_eq_some_iff] at h
  obtain ⟨stackFrame, hfid, hframe_eq⟩ := h
  obtain ⟨fid_lt_length, stackFrame_eq⟩ := List.getElem?_eq_some_iff.mp hfid
  have frame_eq : ({cfg.stack[fid] with index := fid} : FrameWithIndex) = frame :=
    stackFrame_eq ▸ hframe_eq
  rw [← frame_eq]

-- If cfg/cfg' agree (as an `Option`-valued `Frame`-projection `proj`) at every stack position, any
-- `cfg'.stackWithIndex` membership transports down to a `cfg.stackWithIndex` member with the same
-- `.index` and the same `proj`-value. Fully generic over `proj` (e.g. `fun f => (f.regionId,
-- f.bridgeVar)`, or with `Frame.objMap`/`Frame.varMap` projected away entirely) -- previously
-- reconstructed per-operation as `varAsgn_corollary_frame_transport_down`/
-- `fieldAsgn_corollary_frame_transport_down`/`swap_corollary_frame_transport_down` (the `varAsgn`/
-- `swap` versions were byte-for-byte identical; `fieldAsgn`'s differed only in `proj`'s arity).
theorem stackWithIndex_frame_transport_down_of_shape_eq {cfg cfg' : RuntimeConfig} {α : Type*}
    {proj : Frame → α} (hshape : ∀ n : ℕ, (cfg.stack[n]?).map proj = (cfg'.stack[n]?).map proj)
    (fr : FrameWithIndex) (hfr : fr ∈ cfg'.stackWithIndex) :
    ∃ fr0 : FrameWithIndex, fr0 ∈ cfg.stackWithIndex ∧ fr0.index = fr.index ∧
      proj fr0.toFrame = proj fr.toFrame := by
  obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr
  have hidx_n : fr.index = n := by rw [← hfeq]
  have hget' : cfg'.stack[n]? = some fr.toFrame := by
    rw [show fr.toFrame = cfg'.stack[n] from by rw [← hfeq]]
    exact List.getElem?_eq_getElem hn
  have hmap_eq := hshape n
  rw [hget', Option.map_some] at hmap_eq
  obtain ⟨frameX, hframeX, hridX⟩ := Option.map_eq_some_iff.mp hmap_eq
  obtain ⟨hh1, heq⟩ := List.getElem?_eq_some_iff.mp hframeX
  refine ⟨{ frameX with index := n }, ?_, ?_, ?_⟩
  · unfold RuntimeConfig.stackWithIndex
    exact List.mem_mapIdx.mpr ⟨n, hh1, by rw [heq]⟩
  · rw [hidx_n]
  · exact hridX

-- Mirrors `stackWithIndex_frame_transport_down_of_shape_eq`, transporting membership the other way
-- (`cfg.stackWithIndex` member down to `cfg'.stackWithIndex`).
theorem stackWithIndex_frame_transport_up_of_shape_eq {cfg cfg' : RuntimeConfig} {α : Type*}
    {proj : Frame → α} (hshape : ∀ n : ℕ, (cfg.stack[n]?).map proj = (cfg'.stack[n]?).map proj)
    (fr : FrameWithIndex) (hfr : fr ∈ cfg.stackWithIndex) :
    ∃ fr0 : FrameWithIndex, fr0 ∈ cfg'.stackWithIndex ∧ fr0.index = fr.index ∧
      proj fr0.toFrame = proj fr.toFrame := by
  obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr
  have hidx_n : fr.index = n := by rw [← hfeq]
  have hget : cfg.stack[n]? = some fr.toFrame := by
    rw [show fr.toFrame = cfg.stack[n] from by rw [← hfeq]]
    exact List.getElem?_eq_getElem hn
  have hmap_eq := hshape n
  rw [hget, Option.map_some] at hmap_eq
  obtain ⟨frameX, hframeX, hridX⟩ := Option.map_eq_some_iff.mp hmap_eq.symm
  obtain ⟨hh1, heq⟩ := List.getElem?_eq_some_iff.mp hframeX
  refine ⟨{ frameX with index := n }, ?_, ?_, ?_⟩
  · unfold RuntimeConfig.stackWithIndex
    exact List.mem_mapIdx.mpr ⟨n, hh1, by rw [heq]⟩
  · rw [hidx_n]
  · exact hridX

-- If `cfg'` is `cfg` with its **last** frame's `varMap` replaced (everything else about that frame
-- -- `regionId`/`bridgeVar`/`objMap` -- untouched, and every other frame untouched), then `objMap`
-- is unaffected at every stack position. Fully generic over the new `varMap` value -- previously
-- reconstructed identically three times (`merge`/`makeObjRegion`/`makeRegion_corollary_
-- objMap_get_eq`), differing only in *which* reference got inserted (a fact this lemma's conclusion
-- never even mentions).
theorem stackWithIndex_objMap_get_eq_of_last_varMap_update {cfg cfg' : RuntimeConfig} {frame : Frame}
    {newVarMap : VarMap} (hframeLast : cfg.stack.getLast? = some frame)
    (hstack' : cfg'.stack = cfg.stack.dropLast ++
      [({ regionId := frame.regionId, bridgeVar := frame.bridgeVar, objMap := frame.objMap,
          varMap := newVarMap } : Frame)]) (n : ℕ) :
    (cfg.stack[n]?).map Frame.objMap = (cfg'.stack[n]?).map Frame.objMap := by
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
    (List.dropLast_append_getLast? frame hframeLast).symm
  set newFrame : Frame :=
    { regionId := frame.regionId, bridgeVar := frame.bridgeVar, objMap := frame.objMap,
      varMap := newVarMap } with newFrame_def
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

-- An oid can be found in at most one region's objMap (stated over bare L1, so it's usable on cfg
-- before cfg''s own validity is established). Mirrors heap_region_unique/heap_region_unique.
theorem heap_region_unique
    {cfg : RuntimeConfig} {rid1 rid2 : RegionId} {region1 region2 : Region} {oid : ObjectId} :
  L1 cfg →
  (⟨rid1, region1⟩ : Sigma (fun _ : RegionId => Region)) ∈ cfg.heap.entries → oid ∈ region1.objMap.keys →
  (⟨rid2, region2⟩ : Sigma (fun _ : RegionId => Region)) ∈ cfg.heap.entries → oid ∈ region2.objMap.keys →
  rid1 = rid2 := by
  intro l1 mem1 in1 mem2 in2
  by_contra hne
  unfold L1 RuntimeConfig.objectIds at l1
  obtain ⟨_, heap_nodup, _⟩ := List.nodup_append.mp l1
  unfold Heap.objectIds at heap_nodup
  rw [List.nodup_flatten, List.pairwise_map] at heap_nodup
  obtain ⟨_, pairwise_disjoint⟩ := heap_nodup
  have hneq : (⟨rid1, region1⟩ : Sigma (fun _ : RegionId => Region)) ≠ ⟨rid2, region2⟩ := by
    intro heq
    exact hne (congrArg Sigma.fst heq)
  have : Std.Symm (fun (e1 e2 : Sigma (fun _ : RegionId => Region)) => List.Disjoint e1.2.objectIds e2.2.objectIds) := ⟨fun _ _ hd => List.disjoint_symm hd⟩
  have disj := List.Pairwise.forall
    (R := fun (e1 e2 : Sigma (fun _ : RegionId => Region)) => List.Disjoint e1.2.objectIds e2.2.objectIds)
    pairwise_disjoint mem1 mem2 hneq
  unfold Region.objectIds at disj
  exact disj in1 in2

-- Reference.loc?'s (h1, h2)-match for OId factors through Option.map, so equal cfg's need only
-- agree on the *projected* index/rid, not the full FrameWithIndex/heap-entry value.
theorem loc_match_eq (o1 : Option FrameWithIndex)
    (o2 : Option (Sigma (fun _ : RegionId => Region))) :
    (match o1, o2 with
      | some f, none => some (Location.Stk f.index)
      | none, some ⟨rid, _⟩ => some (Location.Rgn rid)
      | _, _ => none) =
    (match o1.map FrameWithIndex.index, o2.map Sigma.fst with
      | some n, none => some (Location.Stk n)
      | none, some r => some (Location.Rgn r)
      | _, _ => none) := by
  cases o1 <;> cases o2 <;> rfl

-- Relates the `stackWithIndex.getLast?` frame used by `swap_cases` back to `cfg.stack`'s own
-- decomposition, mirroring stack_eq_of_stackWithIndex_getLast?/VarAsgn.lean's stack_eq construction.
theorem stack_eq_of_stackWithIndex_getLast? {cfg : RuntimeConfig} {frame : FrameWithIndex}
    (hframe : cfg.stackWithIndex.getLast? = some frame) :
    cfg.stack = cfg.stack.dropLast ++ [frame.toFrame] ∧ frame.index = cfg.stack.dropLast.length := by
  cases hlast : cfg.stack.getLast? with
  | none =>
    exfalso
    have hnil : cfg.stack = [] := List.getLast?_eq_none_iff.mp hlast
    unfold RuntimeConfig.stackWithIndex at hframe
    rw [hnil] at hframe
    simp at hframe
  | some lastF =>
    have stack_eq : cfg.stack = cfg.stack.dropLast ++ [lastF] :=
      (List.dropLast_append_getLast? lastF hlast).symm
    have stackWithIndex_eq :
        cfg.stackWithIndex =
          cfg.stack.dropLast.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) ++
            [({ lastF with index := cfg.stack.dropLast.length } : FrameWithIndex)] := by
      unfold RuntimeConfig.stackWithIndex
      conv_lhs => rw [stack_eq]
      rw [List.mapIdx_concat]
    rw [stackWithIndex_eq, List.getLast?_concat, Option.some_inj] at hframe
    subst hframe
    exact ⟨stack_eq, rfl⟩

-- Once an object is already stored at some key of an ObjMap, its own refs already contribute to
-- the ObjMap-level bind-refs.
theorem objMap_bind_refs_mem_of_lookup {m : ObjMap} {oid : ObjectId} {obj : Object}
    {r : Reference} (hobj : m.lookup oid = some obj) (hr : r ∈ Object.refs obj) :
    r ∈ (m.entries.map (·.2) >>= Object.refs) := by
  have hmem : (⟨oid, obj⟩ : Sigma (fun _ : ObjectId => Object)) ∈ m.entries :=
    AList.mem_lookup_iff.mp (by rw [hobj]; rfl)
  rw [List.bind_eq_flatMap, List.mem_flatMap]
  exact ⟨obj, List.mem_map_of_mem (f := (·.2)) hmem, hr⟩

-- Membership after inserting at an ObjMap key: either from the newly-written object, or already present.
theorem objMap_insert_bind_refs_mem {m : ObjMap} {oid : ObjectId} {v : Object} {r : Reference}
    (hr : r ∈ ((m.insert oid v).entries.map (·.2) >>= Object.refs)) :
    r ∈ Object.refs v ∨ r ∈ (m.entries.map (·.2) >>= Object.refs) := by
  by_cases hoid : oid ∈ m
  · obtain ⟨v0, l1e, l2e, hnotmem, heq, hkerase⟩ := List.exists_of_kerase (AList.mem_keys.mp hoid)
    rw [AList.entries_insert, hkerase, List.map_cons, List.bind_eq_flatMap, List.flatMap_cons,
      ← List.bind_eq_flatMap, List.mem_append, List.map_append, List.bind_eq_flatMap, List.flatMap_append,
      ← List.bind_eq_flatMap, List.mem_append] at hr
    rw [heq, List.map_append, List.map_cons, List.bind_eq_flatMap, List.flatMap_append, List.flatMap_cons,
      ← List.bind_eq_flatMap, ← List.bind_eq_flatMap, List.mem_append, List.mem_append]
    tauto
  · rw [AList.entries_insert_of_notMem hoid, List.map_cons, List.bind_eq_flatMap, List.flatMap_cons,
      ← List.bind_eq_flatMap, List.mem_append] at hr
    tauto

-- Once a region is already stored at some key of a heap, its own refs already contribute to Heap.refs.
theorem heap_refs_mem_of_lookup {cfg : RuntimeConfig} {rid : RegionId} {region : Region}
    {r : Reference} (hregion : cfg.heap.lookup rid = some region) (hr : r ∈ Region.refs region) :
    r ∈ Heap.refs cfg.heap := by
  have hmem : (⟨rid, region⟩ : Sigma (fun _ : RegionId => Region)) ∈ cfg.heap.entries :=
    AList.mem_lookup_iff.mp (by rw [hregion]; rfl)
  unfold Heap.refs
  rw [List.bind_eq_flatMap, List.mem_flatMap]
  exact ⟨region, List.mem_map_of_mem (f := (·.2)) hmem, hr⟩

-- Membership after inserting at a heap key: either from the newly-written region, or already present.
theorem heap_insert_refs_mem {cfg : RuntimeConfig} {rid : RegionId} {newRegion : Region}
    {r : Reference} (hrid : rid ∈ cfg.heap.keys) (hr : r ∈ Heap.refs (cfg.heap.insert rid newRegion)) :
    r ∈ Region.refs newRegion ∨ r ∈ Heap.refs cfg.heap := by
  unfold Heap.refs at hr ⊢
  obtain ⟨v0, l1e, l2e, hnotmem, heq, hkerase⟩ := List.exists_of_kerase hrid
  rw [AList.entries_insert, hkerase, List.map_cons, List.bind_eq_flatMap, List.flatMap_cons,
    ← List.bind_eq_flatMap, List.mem_append, List.map_append, List.bind_eq_flatMap, List.flatMap_append,
    ← List.bind_eq_flatMap, List.mem_append] at hr
  rw [heq, List.map_append, List.map_cons, List.bind_eq_flatMap, List.flatMap_append, List.flatMap_cons,
    ← List.bind_eq_flatMap, ← List.bind_eq_flatMap, List.mem_append, List.mem_append]
  tauto

-- Heap key set is unchanged by inserting at an already-present key.
theorem heap_insert_keys_mem {cfg : RuntimeConfig} {rid : RegionId} {newRegion : Region}
    (hridmem : rid ∈ cfg.heap.keys) (rid' : RegionId) :
    rid' ∈ (cfg.heap.insert rid newRegion).keys ↔ rid' ∈ cfg.heap.keys := by
  rw [← AList.mem_keys, AList.mem_insert, AList.mem_keys]
  exact or_iff_right_of_imp (fun heq => heq ▸ hridmem)

-- The region-touching branches' `heap.insert` at an already-present key, where the newly-inserted
-- region's objMap key set is only known up to a `Perm` of the old region's (the region's objMap
-- genuinely changes, not just a scalar field) -- composes the outer heap-entries reorder with the
-- inner region-level permutation. Mirrors heap_insert_objectIds_perm.
theorem heap_insert_objectIds_perm {cfg : RuntimeConfig} {rid : RegionId}
    {region newRegion : Region} (hregion : cfg.heap.lookup rid = some region)
    (hperm : newRegion.objMap.keys.Perm region.objMap.keys) :
    (Heap.objectIds (cfg.heap.insert rid newRegion)).Perm cfg.heap.objectIds := by
  obtain ⟨region2, l1e, l2e, hnotmem, heq, hkerase⟩ :=
    List.exists_of_kerase (AList.mem_keys_of_lookup_eq_some hregion)
  have region2_eq : region2 = region :=
    List.NodupKeys.eq_of_mk_mem cfg.heap.nodupKeys
      (heq ▸ List.mem_append_right _ List.mem_cons_self) (AList.mem_lookup_iff.mp (by rw [hregion]; rfl))
  have cfg_eq : Heap.objectIds cfg.heap =
      List.flatten (l1e.map (fun e => e.2.objectIds)) ++
        (region.objectIds ++ List.flatten (l2e.map (fun e => e.2.objectIds))) := by
    unfold Heap.objectIds
    rw [heq, ← region2_eq, List.map_append, List.map_cons, List.flatten_append, List.flatten_cons]
  have cfg'_eq : Heap.objectIds (cfg.heap.insert rid newRegion) =
      newRegion.objectIds ++
        (List.flatten (l1e.map (fun e => e.2.objectIds)) ++ List.flatten (l2e.map (fun e => e.2.objectIds))) := by
    unfold Heap.objectIds
    rw [AList.entries_insert, hkerase, List.map_cons, List.flatten_cons, List.map_append, List.flatten_append]
  rw [cfg_eq, cfg'_eq]
  set LA := List.flatten (l1e.map (fun e => e.2.objectIds))
  set LB := List.flatten (l2e.map (fun e => e.2.objectIds))
  have swap_perm : (region.objectIds ++ (LA ++ LB)).Perm (LA ++ (region.objectIds ++ LB)) := by
    rw [← List.append_assoc, ← List.append_assoc]
    exact (List.perm_append_comm).append_right LB
  exact (hperm.append_right (LA ++ LB)).trans swap_perm

-- Generic AList fact (Reference-valued): replacing the value at an already-present key changes
-- the count of any target `t` by exactly (v_new==t?1:0) - (v_old==t?1:0), captured additively (to
-- avoid Nat subtraction) as an equation relating the two counts via the two `==` conditions. This
-- is what makes `swap` provably an *exchange* rather than a plain overwrite: applying this once
-- for each of the two slots being swapped, the two `if`-terms cancel out exactly when combined.
theorem alist_insert_count_eq {α : Type*} [DecidableEq α] {l : AList (fun _ : α => Reference)}
    {k : α} {v_old v_new t : Reference} (hlookup : l.lookup k = some v_old) :
    ((l.insert k v_new).entries.map (·.2)).count t + (if (v_old == t) = true then 1 else 0) =
    (l.entries.map (·.2)).count t + (if (v_new == t) = true then 1 else 0) := by
  obtain ⟨v0, l1e, l2e, hnotmem, heq, hkerase⟩ := List.exists_of_kerase (AList.mem_keys_of_lookup_eq_some hlookup)
  have v0_eq : v0 = v_old := by
    have hmem_v0 : (⟨k, v0⟩ : Sigma (fun _ : α => Reference)) ∈ l.entries :=
      heq ▸ List.mem_append_right _ List.mem_cons_self
    have hmem_vold : (⟨k, v_old⟩ : Sigma (fun _ : α => Reference)) ∈ l.entries :=
      AList.mem_lookup_iff.mp (by rw [hlookup]; rfl)
    exact List.NodupKeys.eq_of_mk_mem (β := fun _ : α => Reference) l.nodupKeys hmem_v0 hmem_vold
  have hnew : (l.insert k v_new).entries.map (·.2) = v_new :: (l1e ++ l2e).map (·.2) := by
    rw [AList.entries_insert, hkerase, List.map_cons]
  have hold : l.entries.map (·.2) = l1e.map (·.2) ++ v_old :: l2e.map (·.2) := by
    rw [heq, v0_eq, List.map_append, List.map_cons]
  rw [hnew, hold, List.count_cons, List.map_append, List.count_append, List.count_append, List.count_cons]
  omega
