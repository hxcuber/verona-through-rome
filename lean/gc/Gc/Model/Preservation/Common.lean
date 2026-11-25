module

public import Gc.Model.Types
public import Gc.Model.Helpers
public import Gc.Model.Validity
public import Gc.Model.Theorems

public import Mathlib.Data.List.Infix

@[expose] public section

-- Generic, non-operation-specific facts shared by several `Preservation`/`Reachability` files.

-- A `heap.entries` membership witnessing `oid` inside some region's `objMap` puts `oid` in the heap's `objectIds`.
theorem heap_objectIds_of_mem {heap : Heap} :
  (⟨rid, region⟩ : Sigma (fun _ : RegionId => Region)) ∈ heap.entries → oid ∈ region.objMap.keys →
  oid ∈ heap.objectIds := fun mem in_region =>
  List.mem_flatten.mpr ⟨region.objectIds, List.mem_map_of_mem (f := λ e => e.2.objectIds) mem, in_region⟩

-- Two elements of `cfg.stackWithIndex` with the same `.index` are equal, since `.index` is the element's own position.
theorem swap_corollary_stackWithIndex_index_inj {cfg : RuntimeConfig} {f1 f2 : FrameWithIndex}
    (h1 : f1 ∈ cfg.stackWithIndex) (h2 : f2 ∈ cfg.stackWithIndex) (heq : f1.index = f2.index) :
    f1 = f2 := by
  obtain ⟨n1, hn1, rfl⟩ := List.mem_mapIdx.mp h1
  obtain ⟨n2, hn2, rfl⟩ := List.mem_mapIdx.mp h2
  cases heq
  rfl

-- `find?` on the index recovers exactly the frame already known to have that index.
theorem swap_corollary_stackWithIndex_find_eq {cfg : RuntimeConfig} {frame : FrameWithIndex}
    (hmem : frame ∈ cfg.stackWithIndex) :
    cfg.stackWithIndex.find? (fun f => f.index == frame.index) = some frame :=
  List.find?_eq_some_of_unique hmem (by simp) fun _ hf' hp =>
    swap_corollary_stackWithIndex_index_inj hf' hmem (beq_iff_eq.mp hp)

-- Two stack frames sharing a `regionId` have the same index (from `S1`).
theorem merge_corollary_regionId_unique_index {cfg : RuntimeConfig} (s1 : S1 cfg)
    {frameZ frameW : FrameWithIndex} (hZ : frameZ ∈ cfg.stackWithIndex) (hW : frameW ∈ cfg.stackWithIndex)
    (heq : frameZ.regionId = frameW.regionId) : frameZ.index = frameW.index := by
  obtain ⟨nZ, hnZ, rfl⟩ := List.mem_mapIdx.mp hZ
  obtain ⟨nW, hnW, rfl⟩ := List.mem_mapIdx.mp hW
  have := (List.Nodup.getElem_inj_iff (hi := by simpa using hnZ) (hj := by simpa using hnW) s1).mp (by simpa using heq)
  exact this

-- The `.index` of a frame found by `stackWithIndex[fid]?` is `fid` itself.
theorem stackWithIndex_getElem_index_eq {cfg : RuntimeConfig} {fid : Index} {frame : FrameWithIndex}
    (h : cfg.stackWithIndex[fid]? = some frame) : frame.index = fid := by
  simp only [RuntimeConfig.stackWithIndex, List.getElem?_mapIdx, Option.map_eq_some_iff] at h
  obtain ⟨_, hfid, rfl⟩ := h
  rfl

-- If cfg/cfg' agree on a frame projection `proj` at every stack position, membership in `cfg'.stackWithIndex` transports down to `cfg.stackWithIndex` with the same index and `proj`-value.
theorem stackWithIndex_frame_transport_down_of_shape_eq {cfg cfg' : RuntimeConfig} {α : Type*}
    {proj : Frame → α} (hshape : ∀ n : ℕ, (cfg.stack[n]?).map proj = (cfg'.stack[n]?).map proj)
    (fr : FrameWithIndex) (hfr : fr ∈ cfg'.stackWithIndex) :
    ∃ fr0 : FrameWithIndex, fr0 ∈ cfg.stackWithIndex ∧ fr0.index = fr.index ∧
      proj fr0.toFrame = proj fr.toFrame := by
  obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp hfr
  obtain ⟨frameX, hframeX, hridX⟩ := Option.map_eq_some_iff.mp
    (by simpa [List.getElem?_eq_getElem hn] using hshape n)
  obtain ⟨hh1, heq⟩ := List.getElem?_eq_some_iff.mp hframeX
  exact ⟨{ frameX with index := n }, List.mem_mapIdx.mpr ⟨n, hh1, by rw [heq]⟩, rfl, hridX⟩

-- The same transport in the other direction.
theorem stackWithIndex_frame_transport_up_of_shape_eq {cfg cfg' : RuntimeConfig} {α : Type*}
    {proj : Frame → α} (hshape : ∀ n : ℕ, (cfg.stack[n]?).map proj = (cfg'.stack[n]?).map proj)
    (fr : FrameWithIndex) (hfr : fr ∈ cfg.stackWithIndex) :
    ∃ fr0 : FrameWithIndex, fr0 ∈ cfg'.stackWithIndex ∧ fr0.index = fr.index ∧
      proj fr0.toFrame = proj fr.toFrame :=
  stackWithIndex_frame_transport_down_of_shape_eq (fun n => (hshape n).symm) fr hfr

-- If `cfg'` is `cfg` with only its last frame's `varMap` replaced, `objMap` is unchanged at every stack position.
theorem stackWithIndex_objMap_get_eq_of_last_varMap_update {cfg cfg' : RuntimeConfig} {frame : Frame}
    {newVarMap : VarMap} (hframeLast : cfg.stack.getLast? = some frame)
    (hstack' : cfg'.stack = cfg.stack.dropLast ++
      [({ regionId := frame.regionId, bridgeVar := frame.bridgeVar, objMap := frame.objMap,
          varMap := newVarMap } : Frame)]) (n : ℕ) :
    (cfg.stack[n]?).map Frame.objMap = (cfg'.stack[n]?).map Frame.objMap := by
  rw [hstack']
  conv_lhs => rw [← List.dropLast_append_getLast? frame hframeLast]
  generalize cfg.stack.dropLast = L
  by_cases hlt : n < L.length
  · simp [List.getElem?_append_left hlt]
  · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    rcases n - L.length with _ | _ <;> simp

-- An oid can be found in at most one region's objMap (stated over bare L1).
theorem heap_region_unique
    {cfg : RuntimeConfig} {rid1 rid2 : RegionId} {region1 region2 : Region} {oid : ObjectId} :
  L1 cfg →
  (⟨rid1, region1⟩ : Sigma (fun _ : RegionId => Region)) ∈ cfg.heap.entries → oid ∈ region1.objMap.keys →
  (⟨rid2, region2⟩ : Sigma (fun _ : RegionId => Region)) ∈ cfg.heap.entries → oid ∈ region2.objMap.keys →
  rid1 = rid2 := fun l1 mem1 in1 mem2 in2 =>
  congrArg Sigma.fst (List.eq_of_mem_flatten_map_nodup (l := cfg.heap.entries) (f := fun e => e.2.objectIds)
    (List.nodup_append.mp l1).2.1 mem1 mem2 in1 in2)

-- `Reference.loc?`'s match for OId factors through `Option.map`, so only the projected index/rid matters.
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

-- The last `stackWithIndex` frame is the last `stack` frame, indexed by the length of the rest of the stack.
theorem stack_eq_of_stackWithIndex_getLast? {cfg : RuntimeConfig} {frame : FrameWithIndex}
    (hframe : cfg.stackWithIndex.getLast? = some frame) :
    cfg.stack = cfg.stack.dropLast ++ [frame.toFrame] ∧ frame.index = cfg.stack.dropLast.length := by
  cases hlast : cfg.stack.getLast? with
  | none =>
    simp [RuntimeConfig.stackWithIndex, List.getLast?_eq_none_iff.mp hlast] at hframe
  | some lastF =>
    have stack_eq : cfg.stack = cfg.stack.dropLast ++ [lastF] :=
      (List.dropLast_append_getLast? lastF hlast).symm
    have : cfg.stackWithIndex =
        cfg.stack.dropLast.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) ++
          [({ lastF with index := cfg.stack.dropLast.length } : FrameWithIndex)] := by
      unfold RuntimeConfig.stackWithIndex
      conv_lhs => rw [stack_eq]
      rw [List.mapIdx_concat]
    rw [this, List.getLast?_concat, Option.some_inj] at hframe
    subst hframe
    exact ⟨stack_eq, rfl⟩

-- An object already stored in an ObjMap contributes its refs to the ObjMap-level bind-refs.
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

-- A region already stored in a heap contributes its refs to `Heap.refs`.
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

-- Inserting a region at an already-present heap key permutes `Heap.objectIds` when the region's objMap keys are permuted.
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

-- Replacing the value at a present key changes the count of `t` by the difference of the two `==` indicators (stated additively).
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
