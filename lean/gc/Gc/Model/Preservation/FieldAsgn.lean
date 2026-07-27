import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Theorems
import Gc.Model.Mutation.FieldAsgn

import Mathlib.Data.List.Infix

-- Relates the `stackWithIndex.getLast?` frame used by `fieldAsgn_cases` back to `cfg.stack`'s own
-- decomposition, mirroring the `stack_eq`/`stackWithIndex_eq` construction used throughout
-- VarAsgn.lean/MakeObjStack.lean, just starting from `stackWithIndex.getLast?` instead of `stack.getLast?`.
theorem fieldAsgn_corollary_stack_eq {cfg : RuntimeConfig} {frame : FrameWithIndex}
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

-- Generic AList fact (no domain dependency): replacing the value at an already-present key
-- reorders `entries` (moves it to the front via kerase+cons) but only *permutes* `.keys`, never
-- changes the key set. Used at both nesting levels in this file (frame.objMap/region.objMap
-- insert at the already-present `oid`, and cfg.heap insert at the already-present `rid`).
theorem fieldAsgn_corollary_insert_keys_perm {α : Type*} {β : α → Type*} [DecidableEq α]
    {l : AList β} {k : α} {v : β k} (hk : k ∈ l.keys) :
    (l.insert k v).keys.Perm l.keys := by
  obtain ⟨v0, l1e, l2e, hnotmem, heq, hkerase⟩ := List.exists_of_kerase hk
  unfold AList.keys
  rw [AList.entries_insert, hkerase]
  conv_rhs => rw [heq]
  rw [List.keys_cons, List.keys_append, List.keys_append, List.keys_cons]
  exact List.perm_middle.symm

-- Generic AList fact: a successful `lookup` means the key is already present.
theorem fieldAsgn_corollary_mem_keys_of_lookup {α : Type*} {β : α → Type*} [DecidableEq α]
    {l : AList β} {k : α} {v : β k} (hv : l.lookup k = some v) : k ∈ l.keys :=
  AList.mem_keys.mp (AList.lookup_isSome.mp (by rw [hv]; rfl))

-- FIELD-ASGN-REGION's heap.insert at an already-present key `rid`, where the newly-inserted region's
-- objMap key set is only known up to a `Perm` of the old region's (rather than literal equality, as in
-- VarAsgn.lean's bridge branch, since here the region's `objMap` genuinely changes, not just a scalar
-- field), still only permutes `Heap.objectIds` overall -- composes the outer heap-entries reorder
-- (mirroring varAsgn_corollary_bridge_heap_objectIds_perm) with the inner region-level permutation.
theorem fieldAsgn_corollary_region_heap_objectIds_perm {cfg : RuntimeConfig} {rid : RegionId}
    {region newRegion : Region} (hregion : cfg.heap.lookup rid = some region)
    (hperm : newRegion.objMap.keys.Perm region.objMap.keys) :
    (Heap.objectIds (cfg.heap.insert rid newRegion)).Perm cfg.heap.objectIds := by
  obtain ⟨region2, l1e, l2e, hnotmem, heq, hkerase⟩ :=
    List.exists_of_kerase (fieldAsgn_corollary_mem_keys_of_lookup hregion)
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

theorem fieldAsgn_L1 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  L1 cfg' := by
  intro vcfg h
  have l1 := vcfg.l1
  obtain ⟨frame, hframe, hcase⟩ := fieldAsgn_cases h
  unfold L1
  rcases hcase with
    ⟨oid, oid_y, obj, hxr, hyr, hloc, hobj, hcfg'⟩ |
    ⟨oid, oid_y, rid, region, obj, hxr, hyr, hloc, hregion, hobj, hyloc, hstatus, hfrid, hcfg'⟩
  · subst hcfg'
    obtain ⟨stack_eq, _⟩ := fieldAsgn_corollary_stack_eq hframe
    have hoidmem : oid ∈ frame.objMap.keys := fieldAsgn_corollary_mem_keys_of_lookup hobj
    have frame_perm := fieldAsgn_corollary_insert_keys_perm
      (l := frame.objMap) (v := obj.insert x.field (Reference.OId oid_y)) hoidmem
    have stack_objectIds_append : ∀ (l : Stack) (f : Frame),
        Stack.objectIds (l ++ [f]) = Stack.objectIds l ++ f.objectIds := by
      intro l f
      unfold Stack.objectIds
      rw [List.bind_eq_flatMap, List.bind_eq_flatMap, List.flatMap_id, List.flatMap_id,
        List.map_append, List.flatten_append]
      simp
    unfold RuntimeConfig.objectIds
    dsimp
    rw [stack_objectIds_append]
    have cfg_stack_eq : Stack.objectIds cfg.stack = Stack.objectIds cfg.stack.dropLast ++ frame.objMap.keys := by
      conv_lhs => rw [stack_eq]
      rw [stack_objectIds_append]
      rfl
    have perm2 :=
      (List.Perm.append_left (Stack.objectIds cfg.stack.dropLast) frame_perm).append_right cfg.heap.objectIds
    rw [← cfg_stack_eq] at perm2
    exact l1.perm perm2.symm
  · subst hcfg'
    have hoidmem : oid ∈ region.objMap.keys := fieldAsgn_corollary_mem_keys_of_lookup hobj
    have region_perm := fieldAsgn_corollary_insert_keys_perm
      (l := region.objMap) (v := obj.insert x.field (Reference.OId oid_y)) hoidmem
    have heap_perm := fieldAsgn_corollary_region_heap_objectIds_perm
      (newRegion := { region with objMap := AList.insert oid (obj.insert x.field (Reference.OId oid_y)) region.objMap })
      hregion region_perm
    unfold RuntimeConfig.objectIds
    dsimp
    exact l1.perm (List.Perm.append_left cfg.stack.objectIds heap_perm).symm

theorem fieldAsgn_L2 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  L2 cfg' := by
  intro vcfg h
  have l2 := vcfg.l2
  obtain ⟨frame, hframe, hcase⟩ := fieldAsgn_cases h
  unfold L2
  rcases hcase with
    ⟨oid, oid_y, obj, hxr, hyr, hloc, hobj, hcfg'⟩ |
    ⟨oid, oid_y, rid, region, obj, hxr, hyr, hloc, hregion, hobj, hyloc, hstatus, hfrid, hcfg'⟩
  · subst hcfg'
    obtain ⟨stack_eq, _⟩ := fieldAsgn_corollary_stack_eq hframe
    have frame_mem : frame.toFrame ∈ cfg.stack :=
      stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self _)
    dsimp
    intro frame'' hmem
    rw [List.mem_append, List.mem_singleton] at hmem
    cases hmem with
    | inl hdrop => exact l2 frame'' (List.mem_of_mem_dropLast hdrop)
    | inr heqframe => subst heqframe; exact l2 frame.toFrame frame_mem
  · subst hcfg'
    dsimp
    intro frame'' hmem
    obtain ⟨region0, hlookup0, hopen0⟩ := l2 frame'' hmem
    by_cases heq : frame''.regionId = rid
    · rw [heq] at hlookup0
      rw [hregion, Option.some_inj] at hlookup0
      refine ⟨{ region with
        objMap := AList.insert oid (AList.insert x.field (Reference.OId oid_y) obj) region.objMap }, ?_, ?_⟩
      · rw [heq, AList.lookup_insert]
      · dsimp
        exact hstatus
    · refine ⟨region0, ?_, hopen0⟩
      rw [AList.lookup_insert_ne heq]
      exact hlookup0

theorem fieldAsgn_S1 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  S1 cfg' := by
  intro vcfg h
  have s1 := vcfg.s1
  obtain ⟨frame, hframe, hcase⟩ := fieldAsgn_cases h
  unfold S1
  rcases hcase with
    ⟨oid, oid_y, obj, hxr, hyr, hloc, hobj, hcfg'⟩ |
    ⟨oid, oid_y, rid, region, obj, hxr, hyr, hloc, hregion, hobj, hyloc, hstatus, hfrid, hcfg'⟩
  · subst hcfg'
    obtain ⟨stack_eq, _⟩ := fieldAsgn_corollary_stack_eq hframe
    have s1' : (cfg.stack.dropLast.map (fun frame => frame.regionId) ++ [frame.regionId]).Nodup := by
      have := s1
      unfold S1 at this
      rw [stack_eq, List.map_append] at this
      exact this
    dsimp
    rw [List.map_append]
    exact s1'
  · subst hcfg'
    dsimp
    exact s1

theorem fieldAsgn_H1 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  H1 cfg' := by
  intro vcfg h
  have h1 := vcfg.h1
  obtain ⟨frame, hframe, hcase⟩ := fieldAsgn_cases h
  unfold H1
  rcases hcase with
    ⟨oid, oid_y, obj, hxr, hyr, hloc, hobj, hcfg'⟩ |
    ⟨oid, oid_y, rid, region, obj, hxr, hyr, hloc, hregion, hobj, hyloc, hstatus, hfrid, hcfg'⟩
  · subst hcfg'
    dsimp
    exact h1
  · subst hcfg'
    dsimp
    have region_mem : region ∈ cfg.heap.regions := by
      unfold Heap.regions
      exact List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hregion)
    intro region0 hregion0
    unfold Heap.regions at hregion0
    rw [AList.entries_insert, List.map_cons, List.mem_cons] at hregion0
    cases hregion0 with
    | inl heqregion =>
      subst heqregion
      dsimp
      exact (AList.mem_insert _).mpr (Or.inr (h1 region region_mem))
    | inr hkeraseregion =>
      apply h1
      unfold Heap.regions
      exact (List.Sublist.map _ (List.kerase_sublist rid cfg.heap.entries)).mem hkeraseregion

-- An Object's own refs after inserting/updating one field: every ref in the new refs is either the
-- newly-written value, or was already present before (whether or not the field was already present).
theorem fieldAsgn_corollary_object_insert_refs_mem {obj : Object} {field : FieldName} {v r : Reference}
    (hr : r ∈ Object.refs (obj.insert field v)) : r = v ∨ r ∈ Object.refs obj := by
  unfold Object.refs at hr ⊢
  by_cases hfield : field ∈ obj
  · obtain ⟨v0, l1e, l2e, hnotmem, heq, hkerase⟩ := List.exists_of_kerase (AList.mem_keys.mp hfield)
    rw [AList.entries_insert, hkerase, List.map_cons, List.map_append, List.mem_cons, List.mem_append] at hr
    rw [heq, List.map_append, List.map_cons, List.mem_append, List.mem_cons]
    tauto
  · rw [AList.entries_insert_of_notMem hfield, List.map_cons, List.mem_cons] at hr
    tauto

-- Once an object is already stored at some key of an ObjMap, its own refs already contribute to the
-- ObjMap-level bind-refs. Used to transport membership from the mutated object back up to the whole
-- Frame/Region's refs (mirrors the reasoning already used for HS1-style corollaries elsewhere).
theorem fieldAsgn_corollary_objMap_bind_refs_mem_of_lookup {m : ObjMap} {oid : ObjectId} {obj : Object}
    {r : Reference} (hobj : m.lookup oid = some obj) (hr : r ∈ Object.refs obj) :
    r ∈ (m.entries.map (·.2) >>= Object.refs) := by
  have hmem : (⟨oid, obj⟩ : Sigma (fun _ : ObjectId => Object)) ∈ m.entries :=
    AList.mem_lookup_iff.mp (by rw [hobj]; rfl)
  rw [List.bind_eq_flatMap, List.mem_flatMap]
  exact ⟨obj, List.mem_map_of_mem (f := (·.2)) hmem, hr⟩

-- An ObjMap's own bind-refs after inserting/updating the value at one key (`oid`, whether or not it
-- was already present): every ref in the new bind-refs is either from the newly-written object `v`,
-- or was already present before. Used for both `frame.objMap` (stack branch) and `region.objMap`
-- (region branch), since both share the `ObjMap` type.
theorem fieldAsgn_corollary_objMap_insert_bind_refs_mem {m : ObjMap} {oid : ObjectId} {v : Object} {r : Reference}
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

-- Wraps the ObjMap-level fact for a whole Frame: only the objMap-derived part of Frame.refs can
-- possibly change (varMap is untouched by fieldAsgn).
theorem fieldAsgn_corollary_frame_insert_refs_mem {frame : Frame} {oid : ObjectId} {v : Object} {r : Reference}
    (hr : r ∈ Frame.refs { frame with objMap := frame.objMap.insert oid v }) :
    r ∈ Object.refs v ∨ r ∈ frame.refs := by
  unfold Frame.refs at hr ⊢
  dsimp at hr
  rw [List.mem_append] at hr ⊢
  rcases hr with hr | hr
  · rcases fieldAsgn_corollary_objMap_insert_bind_refs_mem hr with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr hr)

-- Mirrors fieldAsgn_corollary_frame_insert_refs_mem for Region.refs.
theorem fieldAsgn_corollary_region_insert_refs_mem {region : Region} {oid : ObjectId} {v : Object} {r : Reference}
    (hr : r ∈ Region.refs { region with objMap := region.objMap.insert oid v }) :
    r ∈ Object.refs v ∨ r ∈ region.refs := by
  unfold Region.refs at hr ⊢
  dsimp at hr
  exact fieldAsgn_corollary_objMap_insert_bind_refs_mem hr

-- Combines the three ref-membership corollaries above into the single fact actually needed by
-- HS2/H2's stack branch: every ref newly present in the mutated frame is either the newly-written
-- field value `yRef`, or was already present in the frame before the mutation.
theorem fieldAsgn_corollary_frame_field_insert_refs_mem {frame : Frame} {oid : ObjectId} {obj : Object}
    {field : FieldName} {yRef r : Reference} (hobj : frame.objMap.lookup oid = some obj)
    (hr : r ∈ Frame.refs { frame with objMap := frame.objMap.insert oid (obj.insert field yRef) }) :
    r = yRef ∨ r ∈ frame.refs := by
  rcases fieldAsgn_corollary_frame_insert_refs_mem hr with h | h
  · rcases fieldAsgn_corollary_object_insert_refs_mem h with h' | h'
    · exact Or.inl h'
    · refine Or.inr ?_
      unfold Frame.refs
      exact List.mem_append_left _ (fieldAsgn_corollary_objMap_bind_refs_mem_of_lookup hobj h')
  · exact Or.inr h

-- Mirrors fieldAsgn_corollary_frame_field_insert_refs_mem for Region.refs (the region branch).
theorem fieldAsgn_corollary_region_field_insert_refs_mem {region : Region} {oid : ObjectId} {obj : Object}
    {field : FieldName} {yRef r : Reference} (hobj : region.objMap.lookup oid = some obj)
    (hr : r ∈ Region.refs { region with objMap := region.objMap.insert oid (obj.insert field yRef) }) :
    r = yRef ∨ r ∈ region.refs := by
  rcases fieldAsgn_corollary_region_insert_refs_mem hr with h | h
  · rcases fieldAsgn_corollary_object_insert_refs_mem h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (fieldAsgn_corollary_objMap_bind_refs_mem_of_lookup hobj h')
  · exact Or.inr h

-- Heap key set is unchanged by inserting at an already-present key (mirrors
-- varAsgn_corollary_bridge_heap_keys_mem).
theorem fieldAsgn_corollary_heap_insert_keys_mem {cfg : RuntimeConfig} {rid : RegionId} {newRegion : Region}
    (hridmem : rid ∈ cfg.heap.keys) (rid' : RegionId) :
    rid' ∈ (cfg.heap.insert rid newRegion).keys ↔ rid' ∈ cfg.heap.keys := by
  rw [← AList.mem_keys, AList.mem_insert, AList.mem_keys]
  exact or_iff_right_of_imp (fun heq => heq ▸ hridmem)

-- Heap-level analogue of fieldAsgn_corollary_objMap_insert_bind_refs_mem: every ref in
-- Heap.refs after inserting at an already-present region key is either from the newly-inserted
-- region, or was already present.
theorem fieldAsgn_corollary_heap_insert_refs_mem {cfg : RuntimeConfig} {rid : RegionId} {newRegion : Region}
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

-- Once a region is already stored at some key of a heap, its own refs already contribute to
-- Heap.refs (mirrors fieldAsgn_corollary_objMap_bind_refs_mem_of_lookup one level up).
theorem fieldAsgn_corollary_heap_refs_mem_of_lookup {cfg : RuntimeConfig} {rid : RegionId} {region : Region}
    {r : Reference} (hregion : cfg.heap.lookup rid = some region) (hr : r ∈ Region.refs region) :
    r ∈ Heap.refs cfg.heap := by
  have hmem : (⟨rid, region⟩ : Sigma (fun _ : RegionId => Region)) ∈ cfg.heap.entries :=
    AList.mem_lookup_iff.mp (by rw [hregion]; rfl)
  unfold Heap.refs
  rw [List.bind_eq_flatMap, List.mem_flatMap]
  exact ⟨region, List.mem_map_of_mem (f := (·.2)) hmem, hr⟩

-- The count-level analogue of fieldAsgn_corollary_object_insert_refs_mem: since the newly-written
-- value `v` is never equal to the target `t` we're counting (in this file, `v` is always
-- `Reference.OId _` and `t` is always `Reference.RId _`), inserting/updating one field can only
-- decrease-or-preserve the count of `t`, whether or not the field was already present.
theorem fieldAsgn_corollary_object_insert_count_le {obj : Object} {field : FieldName} {v t : Reference}
    (hne : (v == t) = false) :
    (Object.refs (obj.insert field v)).count t ≤ (Object.refs obj).count t := by
  unfold Object.refs
  by_cases hfield : field ∈ obj
  · obtain ⟨v0, l1e, l2e, hnotmem, heq, hkerase⟩ := List.exists_of_kerase (AList.mem_keys.mp hfield)
    have hnew : (AList.insert field v obj).entries.map (·.2) = v :: ((l1e ++ l2e).map (·.2)) := by
      rw [AList.entries_insert, hkerase, List.map_cons]
    have hold : obj.entries.map (·.2) = l1e.map (·.2) ++ v0 :: l2e.map (·.2) := by
      rw [heq, List.map_append, List.map_cons]
    rw [hnew, hold, List.count_cons, List.map_append, List.count_append, List.count_append,
      List.count_cons, hne, if_neg (by decide)]
    split_ifs <;> omega
  · have hnew : (AList.insert field v obj).entries.map (·.2) = v :: obj.entries.map (·.2) := by
      rw [AList.entries_insert_of_notMem hfield, List.map_cons]
    rw [hnew, List.count_cons, hne, if_neg (by decide)]
    omega

-- ObjMap-level count propagation: given the mutated object's own count bound (from
-- fieldAsgn_corollary_object_insert_count_le), the whole ObjMap-level bind-refs count is also
-- bounded. `oid` is always already-present in this file (fieldAsgn never allocates a fresh id).
theorem fieldAsgn_corollary_objMap_insert_bind_refs_count_le {m : ObjMap} {oid : ObjectId} {obj v : Object}
    {t : Reference} (hobj : m.lookup oid = some obj) (hle : (Object.refs v).count t ≤ (Object.refs obj).count t) :
    ((m.insert oid v).entries.map (·.2) >>= Object.refs).count t ≤ (m.entries.map (·.2) >>= Object.refs).count t := by
  obtain ⟨v0, l1e, l2e, hnotmem, heq, hkerase⟩ := List.exists_of_kerase (fieldAsgn_corollary_mem_keys_of_lookup hobj)
  have v0_eq : v0 = obj := by
    have hmem_v0 : (⟨oid, v0⟩ : Sigma (fun _ : ObjectId => Object)) ∈ m.entries :=
      heq ▸ List.mem_append_right _ List.mem_cons_self
    have hmem_obj : (⟨oid, obj⟩ : Sigma (fun _ : ObjectId => Object)) ∈ m.entries :=
      AList.mem_lookup_iff.mp (by rw [hobj]; rfl)
    exact List.NodupKeys.eq_of_mk_mem (β := fun _ : ObjectId => Object) m.nodupKeys hmem_v0 hmem_obj
  have hnewbind : (m.insert oid v).entries.map (·.2) >>= Object.refs =
      Object.refs v ++ ((l1e ++ l2e).map (·.2) >>= Object.refs) := by
    rw [AList.entries_insert, hkerase, List.map_cons, List.bind_eq_flatMap, List.flatMap_cons,
      ← List.bind_eq_flatMap]
  have holdbind : m.entries.map (·.2) >>= Object.refs =
      (l1e.map (·.2) >>= Object.refs) ++ (Object.refs obj ++ (l2e.map (·.2) >>= Object.refs)) := by
    rw [heq, v0_eq, List.map_append, List.map_cons, List.bind_eq_flatMap, List.flatMap_append,
      List.flatMap_cons, ← List.bind_eq_flatMap, ← List.bind_eq_flatMap]
  have splitbind : ((l1e ++ l2e).map (·.2) >>= Object.refs).count t =
      (l1e.map (·.2) >>= Object.refs).count t + (l2e.map (·.2) >>= Object.refs).count t := by
    rw [List.map_append, List.bind_eq_flatMap, List.flatMap_append, ← List.bind_eq_flatMap,
      ← List.bind_eq_flatMap, List.count_append]
  rw [hnewbind, holdbind, List.count_append, List.count_append, List.count_append, splitbind]
  omega

-- Wraps the ObjMap-level count bound for a whole Frame (varMap is untouched by fieldAsgn).
theorem fieldAsgn_corollary_frame_insert_refs_count_le {frame : Frame} {oid : ObjectId} {obj v : Object}
    {t : Reference} (hobj : frame.objMap.lookup oid = some obj)
    (hle : (Object.refs v).count t ≤ (Object.refs obj).count t) :
    (Frame.refs { frame with objMap := frame.objMap.insert oid v }).count t ≤ (Frame.refs frame).count t := by
  unfold Frame.refs
  dsimp only
  rw [List.count_append, List.count_append]
  have := fieldAsgn_corollary_objMap_insert_bind_refs_count_le hobj hle
  omega

-- Mirrors fieldAsgn_corollary_frame_insert_refs_count_le for Region.refs.
theorem fieldAsgn_corollary_region_insert_refs_count_le {region : Region} {oid : ObjectId} {obj v : Object}
    {t : Reference} (hobj : region.objMap.lookup oid = some obj)
    (hle : (Object.refs v).count t ≤ (Object.refs obj).count t) :
    (Region.refs { region with objMap := region.objMap.insert oid v }).count t ≤ (Region.refs region).count t := by
  unfold Region.refs
  dsimp
  exact fieldAsgn_corollary_objMap_insert_bind_refs_count_le hobj hle

-- Heap-level analogue of fieldAsgn_corollary_objMap_insert_bind_refs_count_le (one level up: Heap
-- of Regions instead of ObjMap of Objects). Used by H2's region branch.
theorem fieldAsgn_corollary_heap_insert_refs_count_le {cfg : RuntimeConfig} {rid : RegionId}
    {region newRegion : Region} {t : Reference} (hregion : cfg.heap.lookup rid = some region)
    (hle : (Region.refs newRegion).count t ≤ (Region.refs region).count t) :
    (Heap.refs (cfg.heap.insert rid newRegion)).count t ≤ (Heap.refs cfg.heap).count t := by
  obtain ⟨v0, l1e, l2e, hnotmem, heq, hkerase⟩ :=
    List.exists_of_kerase (fieldAsgn_corollary_mem_keys_of_lookup hregion)
  have v0_eq : v0 = region := by
    have hmem_v0 : (⟨rid, v0⟩ : Sigma (fun _ : RegionId => Region)) ∈ cfg.heap.entries :=
      heq ▸ List.mem_append_right _ List.mem_cons_self
    have hmem_region : (⟨rid, region⟩ : Sigma (fun _ : RegionId => Region)) ∈ cfg.heap.entries :=
      AList.mem_lookup_iff.mp (by rw [hregion]; rfl)
    exact List.NodupKeys.eq_of_mk_mem (β := fun _ : RegionId => Region) cfg.heap.nodupKeys hmem_v0 hmem_region
  unfold Heap.refs
  have hnewbind : (cfg.heap.insert rid newRegion).entries.map (·.2) >>= Region.refs =
      Region.refs newRegion ++ ((l1e ++ l2e).map (·.2) >>= Region.refs) := by
    rw [AList.entries_insert, hkerase, List.map_cons, List.bind_eq_flatMap, List.flatMap_cons,
      ← List.bind_eq_flatMap]
  have holdbind : cfg.heap.entries.map (·.2) >>= Region.refs =
      (l1e.map (·.2) >>= Region.refs) ++ (Region.refs region ++ (l2e.map (·.2) >>= Region.refs)) := by
    rw [heq, v0_eq, List.map_append, List.map_cons, List.bind_eq_flatMap, List.flatMap_append,
      List.flatMap_cons, ← List.bind_eq_flatMap, ← List.bind_eq_flatMap]
  have splitbind : ((l1e ++ l2e).map (·.2) >>= Region.refs).count t =
      (l1e.map (·.2) >>= Region.refs).count t + (l2e.map (·.2) >>= Region.refs).count t := by
    rw [List.map_append, List.bind_eq_flatMap, List.flatMap_append, ← List.bind_eq_flatMap,
      ← List.bind_eq_flatMap, List.count_append]
  rw [hnewbind, holdbind, List.count_append, List.count_append, List.count_append, splitbind]
  omega

theorem fieldAsgn_H2 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  H2 cfg' := by
  intro vcfg h
  have h2 := vcfg.h2
  obtain ⟨frame, hframe, hcase⟩ := fieldAsgn_cases h
  unfold H2
  rcases hcase with
    ⟨oid, oid_y, obj, hxr, hyr, hloc, hobj, hcfg'⟩ |
    ⟨oid, oid_y, rid, region, obj, hxr, hyr, hloc, hregion, hobj, hyloc, hstatus, hfrid, hcfg'⟩
  · subst hcfg'
    intro rid'
    obtain ⟨stack_eq, _⟩ := fieldAsgn_corollary_stack_eq hframe
    have stack_refs_append : ∀ (l : Stack) (f : Frame), Stack.refs (l ++ [f]) = Stack.refs l ++ f.refs := by
      intro l f
      unfold Stack.refs
      rw [List.bind_eq_flatMap, List.bind_eq_flatMap, List.flatMap_id, List.flatMap_id,
        List.map_append, List.flatten_append]
      simp
    have hle : (Object.refs (obj.insert x.field (Reference.OId oid_y))).count (Reference.RId rid') ≤
        (Object.refs obj).count (Reference.RId rid') :=
      fieldAsgn_corollary_object_insert_count_le rfl
    have hframele := fieldAsgn_corollary_frame_insert_refs_count_le hobj hle
    dsimp
    rw [stack_refs_append, List.count_append]
    have cfg_stack_eq : Stack.refs cfg.stack = Stack.refs cfg.stack.dropLast ++ frame.refs := by
      conv_lhs => rw [stack_eq]
      exact stack_refs_append _ _
    have h2' := h2 rid'
    rw [cfg_stack_eq, List.count_append] at h2'
    omega
  · subst hcfg'
    dsimp
    intro rid'
    have hle : (Region.refs { region with
        objMap := AList.insert oid (AList.insert x.field (Reference.OId oid_y) obj) region.objMap }).count
        (Reference.RId rid') ≤ (Region.refs region).count (Reference.RId rid') := by
      have hle0 : (Object.refs (obj.insert x.field (Reference.OId oid_y))).count (Reference.RId rid') ≤
          (Object.refs obj).count (Reference.RId rid') :=
        fieldAsgn_corollary_object_insert_count_le rfl
      exact fieldAsgn_corollary_region_insert_refs_count_le hobj hle0
    have hheaple := fieldAsgn_corollary_heap_insert_refs_count_le hregion hle
    have h2' := h2 rid'
    omega

-- A successful `resolveV` retrieves an already-live object reference -- either directly from some
-- frame's varMap (already ∈ cfg.refs, so vcfg.hs1 applies), or as a region's bridgeObjectId (already
-- ∈ cfg.objectIds via H1). Mirrors varAsgn_corollary_resolveV_loc_ancestor's case split but concludes
-- objectIds membership instead of a stack-ancestor witness. Used by HS1's newly-written field value.
theorem fieldAsgn_corollary_resolveV_oid_mem_objectIds {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {var : VarName} {oid : ObjectId} (hrv : resolveV var cfg = some (Reference.OId oid)) :
    oid ∈ cfg.objectIds := by
  have hs1 := vcfg.hs1
  have h1 := vcfg.h1
  unfold resolveV at hrv
  cases hfV : cfg.stackWithIndex.findRev? (fun frame => frame.varMap.keys.contains var ∨ frame.bridgeVar == var) with
  | none => rw [hfV] at hrv; contradiction
  | some frameV =>
    rw [hfV] at hrv
    dsimp at hrv
    cases hlookupV : frameV.varMap.lookup var with
    | some refV =>
      rw [hlookupV] at hrv
      dsimp at hrv
      rw [Option.some_inj] at hrv
      apply hs1
      have hmemV : refV ∈ frameV.refs := by
        unfold Frame.refs
        apply List.mem_append_right
        exact List.mem_map_of_mem (f := (·.2)) (AList.mem_lookup_iff.mp (by rw [hlookupV]; rfl))
      have hframeV_mem : frameV ∈ cfg.stackWithIndex := by
        rw [List.findRev?_eq_find?_reverse] at hfV
        exact List.mem_reverse.mp (List.mem_of_find?_eq_some hfV)
      obtain ⟨n, hn, heqn⟩ := List.mem_mapIdx.mp hframeV_mem
      unfold RuntimeConfig.refs
      apply List.mem_append_left
      unfold Stack.refs
      rw [List.bind_eq_flatMap, List.flatMap_id, List.mem_flatten]
      refine ⟨frameV.refs, ?_, hrv ▸ hmemV⟩
      rw [List.mem_map]
      exact ⟨cfg.stack[n], List.mem_iff_getElem.mpr ⟨n, hn, rfl⟩, by rw [← heqn]⟩
    | none =>
      rw [hlookupV] at hrv
      dsimp at hrv
      by_cases hbv : frameV.bridgeVar == var
      · rw [if_pos hbv] at hrv
        cases hregionV : cfg.heap.lookup frameV.regionId with
        | none => rw [hregionV] at hrv; dsimp at hrv; contradiction
        | some regionV =>
          rw [hregionV] at hrv
          dsimp at hrv
          rw [Option.some_inj, Reference.OId.injEq] at hrv
          have hmemBridge : regionV.bridgeObjectId ∈ regionV.objMap := h1 regionV
            (List.mem_map_of_mem (f := (·.2)) (AList.mem_lookup_iff.mp (by rw [hregionV]; rfl)))
          unfold RuntimeConfig.objectIds
          apply List.mem_append_right
          unfold Heap.objectIds
          rw [List.mem_flatten]
          refine ⟨regionV.objMap.keys, ?_, ?_⟩
          · exact List.mem_map_of_mem (f := fun e : Sigma (fun _ : RegionId => Region) => e.2.objectIds)
              (AList.mem_lookup_iff.mp (by rw [hregionV]; rfl))
          · rw [← hrv]; exact AList.mem_keys.mp hmemBridge
      · rw [if_neg hbv] at hrv; contradiction

-- A List.Perm doesn't change what `.contains` reports (order-independent).
theorem fieldAsgn_corollary_perm_contains_eq {α : Type*} [BEq α] [LawfulBEq α] {l l' : List α}
    (hperm : l.Perm l') (a : α) : l.contains a = l'.contains a := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]
  exact hperm.mem_iff

-- The stack branch never changes any objMap's *key set* (only the value at the already-present
-- `oid`), so `Reference.loc?`'s stack-side search finds the same frame at the same index for every
-- oid' -- unconditional, mirroring varAsgn_corollary_fresh_loc_eq, but needing the Perm-based
-- `.contains` equivalence (fieldAsgn_corollary_perm_contains_eq) since the key *list* itself, unlike
-- VarAsgn's untouched-objMap case, genuinely reorders (kerase+cons at the already-present `oid`).
theorem fieldAsgn_corollary_stack_loc_eq {cfg : RuntimeConfig} {frame : FrameWithIndex} {oid : ObjectId}
    {obj : Object} {field : FieldName} {yRef : Reference}
    (hframe : cfg.stackWithIndex.getLast? = some frame) (hobj : frame.objMap.lookup oid = some obj)
    (oid' : ObjectId) :
    (Reference.OId oid').loc? cfg =
      (Reference.OId oid').loc? { cfg with stack := cfg.stack.dropLast ++
        [({ frame with objMap := frame.objMap.insert oid (obj.insert field yRef) } : Frame)] } := by
  obtain ⟨stack_eq, _⟩ := fieldAsgn_corollary_stack_eq hframe
  set newFrame : Frame := { frame with objMap := frame.objMap.insert oid (obj.insert field yRef) } with newFrame_def
  have keys_perm : newFrame.objMap.keys.Perm frame.objMap.keys :=
    fieldAsgn_corollary_insert_keys_perm (fieldAsgn_corollary_mem_keys_of_lookup hobj)
  unfold Reference.loc?
  dsimp
  by_cases hb : frame.objMap.keys.contains oid'
  · have hb' : newFrame.objMap.keys.contains oid' := by
      rw [fieldAsgn_corollary_perm_contains_eq keys_perm]; exact hb
    have h1_cfg : cfg.stackWithIndex.findRev? (fun f => f.objMap.keys.contains oid') =
        some ({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex) := by
      unfold RuntimeConfig.stackWithIndex
      conv_lhs => rw [stack_eq]
      rw [List.mapIdx_concat, List.findRev?_eq_find?_reverse, List.reverse_append, List.reverse_singleton,
        List.singleton_append]
      exact List.find?_cons_of_pos hb
    have h1_cfg' :
        (RuntimeConfig.stackWithIndex { stack := cfg.stack.dropLast ++ [newFrame], heap := cfg.heap }).findRev?
          (fun f => f.objMap.keys.contains oid') =
        some ({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex) := by
      unfold RuntimeConfig.stackWithIndex
      dsimp
      rw [List.mapIdx_concat, List.findRev?_eq_find?_reverse, List.reverse_append, List.reverse_singleton,
        List.singleton_append]
      exact List.find?_cons_of_pos hb'
    rw [h1_cfg, h1_cfg']
    cases cfg.heap.entries.find? (fun x => x.snd.objMap.keys.contains oid') with
    | none => rfl
    | some _ => rfl
  · have hb' : ¬ newFrame.objMap.keys.contains oid' := by
      rw [fieldAsgn_corollary_perm_contains_eq keys_perm]; exact hb
    have h1_eq : cfg.stackWithIndex.findRev? (fun f => f.objMap.keys.contains oid') =
        (RuntimeConfig.stackWithIndex { stack := cfg.stack.dropLast ++ [newFrame], heap := cfg.heap }).findRev?
          (fun f => f.objMap.keys.contains oid') := by
      unfold RuntimeConfig.stackWithIndex
      dsimp
      conv_lhs => rw [stack_eq]
      rw [List.mapIdx_concat, List.mapIdx_concat, List.findRev?_eq_find?_reverse, List.findRev?_eq_find?_reverse,
        List.reverse_append, List.reverse_append, List.reverse_singleton, List.reverse_singleton,
        List.singleton_append, List.singleton_append]
      have hbL : ¬ ({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex).objMap.keys.contains
          oid' = true := hb
      have hbR : ¬ ({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex).objMap.keys.contains
          oid' = true := hb'
      have find_eqL :
          List.find? (fun f => f.objMap.keys.contains oid')
            (({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex) ::
              (List.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) cfg.stack.dropLast).reverse) =
          List.find? (fun f => f.objMap.keys.contains oid')
            (List.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) cfg.stack.dropLast).reverse :=
        List.find?_cons_of_neg hbL
      have find_eqR :
          List.find? (fun f => f.objMap.keys.contains oid')
            (({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex) ::
              (List.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) cfg.stack.dropLast).reverse) =
          List.find? (fun f => f.objMap.keys.contains oid')
            (List.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) cfg.stack.dropLast).reverse :=
        List.find?_cons_of_neg hbR
      rw [find_eqL, find_eqR]
    rw [h1_eq]

-- An oid can be found in at most one region's objMap (stated over bare L1, so it's usable on cfg
-- before cfg''s own validity is established). Mirrors varAsgn_corollary_region_unique.
theorem fieldAsgn_corollary_region_unique
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
  have disj := List.Pairwise.forall
    (R := fun (e1 e2 : Sigma (fun _ : RegionId => Region)) => List.Disjoint e1.2.objectIds e2.2.objectIds)
    (fun _ _ hd => List.disjoint_symm hd)
    pairwise_disjoint mem1 mem2 hneq
  unfold Region.objectIds at disj
  exact disj in1 in2

-- Reference.loc?'s (h1, h2)-match for OId factors through Option.map, so equal cfg's need only
-- agree on the *projected* index/rid, not the full FrameWithIndex/heap-entry value. Mirrors
-- makeObjRegion_corollary_loc_match_eq/varAsgn_corollary_loc_match_eq.
theorem fieldAsgn_corollary_loc_match_eq (o1 : Option FrameWithIndex)
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

-- The region branch's heap.insert at an already-present key `rid` reorders `entries`; the mutated
-- region's own key set is only Perm-related to the original (not literally equal, since `objMap`
-- genuinely changes at the already-present `oid`) -- uses fieldAsgn_corollary_perm_contains_eq to
-- show the `.contains oid'` check used by loc?'s heap-side search agrees regardless.
theorem fieldAsgn_corollary_region_loc_eq {cfg : RuntimeConfig} {rid oid : ObjectId} {region : Region}
    {obj : Object} {field : FieldName} {yRef : Reference} (vcfg : ValidConfig cfg)
    (hregion : cfg.heap.lookup rid = some region) (hobj : region.objMap.lookup oid = some obj)
    (oid' : ObjectId) :
    (Reference.OId oid').loc? cfg =
      (Reference.OId oid').loc? { cfg with heap := cfg.heap.insert rid { region with objMap := region.objMap.insert oid (obj.insert field yRef) } } := by
  have l1 := vcfg.l1
  have keys_perm : (region.objMap.insert oid (obj.insert field yRef)).keys.Perm region.objMap.keys :=
    fieldAsgn_corollary_insert_keys_perm (fieldAsgn_corollary_mem_keys_of_lookup hobj)
  unfold Reference.loc?
  dsimp
  have heap_h2_map_eq :
      (cfg.heap.entries.find? (fun p => p.snd.objMap.keys.contains oid')).map Sigma.fst =
      ((AList.insert rid { region with objMap := region.objMap.insert oid (obj.insert field yRef) } cfg.heap).entries.find?
        (fun p => p.snd.objMap.keys.contains oid')).map Sigma.fst := by
    obtain ⟨region2, l1e, l2e, hnotmem, heq, hkerase⟩ :=
      List.exists_of_kerase (fieldAsgn_corollary_mem_keys_of_lookup hregion)
    have region2_eq : region2 = region :=
      List.NodupKeys.eq_of_mk_mem cfg.heap.nodupKeys
        (heq ▸ List.mem_append_right _ List.mem_cons_self) (AList.mem_lookup_iff.mp (by rw [hregion]; rfl))
    rw [region2_eq] at heq
    rw [AList.entries_insert, hkerase]
    have region_mem_cfg : (⟨rid, region⟩ : Sigma (fun _ : RegionId => Region)) ∈ cfg.heap.entries :=
      heq ▸ List.mem_append_right _ List.mem_cons_self
    by_cases hb2 : region.objMap.keys.contains oid'
    · have hb2' : (region.objMap.insert oid (obj.insert field yRef)).keys.contains oid' := by
        rw [fieldAsgn_corollary_perm_contains_eq keys_perm]; exact hb2
      have find_eqR2 :
          List.find? (fun p => p.snd.objMap.keys.contains oid')
            ((⟨rid, { region with objMap := region.objMap.insert oid (obj.insert field yRef) }⟩ :
                Sigma (fun _ : RegionId => Region)) :: (l1e ++ l2e)) =
          some (⟨rid, { region with objMap := region.objMap.insert oid (obj.insert field yRef) }⟩ :
            Sigma (fun _ : RegionId => Region)) :=
        List.find?_cons_of_pos hb2'
      rw [find_eqR2]
      have find_eqL :
          cfg.heap.entries.find? (fun p => p.snd.objMap.keys.contains oid') =
          some (⟨rid, region⟩ : Sigma (fun _ : RegionId => Region)) := by
        apply List.find?_eq_some_of_unique region_mem_cfg hb2
        intro y hy hpy
        obtain ⟨rid_y, region_y⟩ := y
        have rid_y_eq : rid_y = rid :=
          fieldAsgn_corollary_region_unique l1 hy (List.contains_iff_mem.mp hpy)
            region_mem_cfg (List.contains_iff_mem.mp hb2)
        subst rid_y_eq
        have region_y_eq : region_y = region :=
          List.NodupKeys.eq_of_mk_mem cfg.heap.nodupKeys hy region_mem_cfg
        rw [region_y_eq]
      rw [find_eqL]
      rfl
    · have hb2' : ¬ (region.objMap.insert oid (obj.insert field yRef)).keys.contains oid' := by
        rw [fieldAsgn_corollary_perm_contains_eq keys_perm]; exact hb2
      have find_eqR2 :
          List.find? (fun p => p.snd.objMap.keys.contains oid')
            ((⟨rid, { region with objMap := region.objMap.insert oid (obj.insert field yRef) }⟩ :
                Sigma (fun _ : RegionId => Region)) :: (l1e ++ l2e)) =
          List.find? (fun p => p.snd.objMap.keys.contains oid') (l1e ++ l2e) :=
        List.find?_cons_of_neg hb2'
      rw [find_eqR2]
      have find_eqL :
          cfg.heap.entries.find? (fun p => p.snd.objMap.keys.contains oid') =
          List.find? (fun p => p.snd.objMap.keys.contains oid') (l1e ++ l2e) := by
        rw [heq]
        clear region_mem_cfg heq hkerase hnotmem find_eqR2
        induction l1e with
        | nil =>
          dsimp
          exact List.find?_cons_of_neg hb2
        | cons a as ih =>
          dsimp
          by_cases hpa : a.snd.objMap.keys.contains oid'
          · have find_eqA :
                List.find? (fun p => p.snd.objMap.keys.contains oid')
                  (a :: (as ++ (⟨rid, region⟩ : Sigma (fun _ : RegionId => Region)) :: l2e)) =
                some a := List.find?_cons_of_pos hpa
            have find_eqB :
                List.find? (fun p => p.snd.objMap.keys.contains oid') (a :: (as ++ l2e)) =
                some a := List.find?_cons_of_pos hpa
            rw [find_eqA, find_eqB]
          · have find_eqA :
                List.find? (fun p => p.snd.objMap.keys.contains oid')
                  (a :: (as ++ (⟨rid, region⟩ : Sigma (fun _ : RegionId => Region)) :: l2e)) =
                List.find? (fun p => p.snd.objMap.keys.contains oid')
                  (as ++ (⟨rid, region⟩ : Sigma (fun _ : RegionId => Region)) :: l2e) :=
              List.find?_cons_of_neg hpa
            have find_eqB :
                List.find? (fun p => p.snd.objMap.keys.contains oid') (a :: (as ++ l2e)) =
                List.find? (fun p => p.snd.objMap.keys.contains oid') (as ++ l2e) :=
              List.find?_cons_of_neg hpa
            rw [find_eqA, find_eqB]
            exact ih
      rw [find_eqL]
  have step1 := fieldAsgn_corollary_loc_match_eq
    (cfg.stackWithIndex.findRev? (fun f => f.objMap.keys.contains oid'))
    (cfg.heap.entries.find? (fun p => p.snd.objMap.keys.contains oid'))
  have step2 := fieldAsgn_corollary_loc_match_eq
    (cfg.stackWithIndex.findRev? (fun f => f.objMap.keys.contains oid'))
    ((AList.insert rid { region with objMap := region.objMap.insert oid (obj.insert field yRef) } cfg.heap).entries.find?
      (fun p => p.snd.objMap.keys.contains oid'))
  rw [heap_h2_map_eq] at step1
  exact step1.trans step2.symm

theorem fieldAsgn_H3 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  H3 cfg' := by
  intro vcfg h
  have h3 := vcfg.h3
  obtain ⟨frame, hframe, hcase⟩ := fieldAsgn_cases h
  unfold H3
  rcases hcase with
    ⟨oid, oid_y, obj, hxr, hyr, hloc, hobj, hcfg'⟩ |
    ⟨oid, oid_y, rid, region, obj, hxr, hyr, hloc, hregion, hobj, hyloc, hstatus, hfrid, hcfg'⟩
  · subst hcfg'
    intro rid0 oid0 region0 hlookup0 href0
    dsimp at hlookup0
    have h3fact := h3 rid0 oid0 region0 hlookup0 href0
    rw [← fieldAsgn_corollary_stack_loc_eq hframe hobj oid0]
    exact h3fact
  · subst hcfg'
    intro rid0 oid0 region0 hlookup0 href0
    dsimp at hlookup0
    by_cases hrideq : rid0 = rid
    · subst hrideq
      rw [AList.lookup_insert, Option.some_inj] at hlookup0
      subst hlookup0
      rcases fieldAsgn_corollary_region_field_insert_refs_mem hobj href0 with heq | horig
      · rw [Reference.OId.injEq] at heq
        rw [heq, ← fieldAsgn_corollary_region_loc_eq vcfg hregion hobj oid_y]
        exact hyloc
      · have h3fact := h3 rid0 oid0 region hregion horig
        rw [← fieldAsgn_corollary_region_loc_eq vcfg hregion hobj oid0]
        exact h3fact
    · rw [AList.lookup_insert_ne hrideq] at hlookup0
      have h3fact := h3 rid0 oid0 region0 hlookup0 href0
      rw [← fieldAsgn_corollary_region_loc_eq vcfg hregion hobj oid0]
      exact h3fact

theorem fieldAsgn_S2 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  S2 cfg' := by
  intro vcfg h
  have s2 := vcfg.s2
  obtain ⟨frame, hframe, hcase⟩ := fieldAsgn_cases h
  unfold S2
  rcases hcase with
    ⟨oid, oid_y, obj, hxr, hyr, hloc, hobj, hcfg'⟩ |
    ⟨oid, oid_y, rid, region, obj, hxr, hyr, hloc, hregion, hobj, hyloc, hstatus, hfrid, hcfg'⟩
  · subst hcfg'
    obtain ⟨stack_eq, _⟩ := fieldAsgn_corollary_stack_eq hframe
    set newFrame : Frame :=
      { frame with objMap := frame.objMap.insert oid (obj.insert x.field (Reference.OId oid_y)) } with newFrame_def
    have stackWithIndex_eq_cfg :
        cfg.stackWithIndex =
          cfg.stack.dropLast.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) ++
            [({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex)] := by
      unfold RuntimeConfig.stackWithIndex
      conv_lhs => rw [stack_eq]
      rw [List.mapIdx_concat]
    have stackWithIndex_eq :
        (RuntimeConfig.stackWithIndex { stack := cfg.stack.dropLast ++ [newFrame], heap := cfg.heap }) =
          cfg.stack.dropLast.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) ++
            [({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex)] := by
      unfold RuntimeConfig.stackWithIndex
      dsimp
      rw [List.mapIdx_concat]
    have hstacklen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by
      conv_lhs => rw [stack_eq]
      rw [List.length_append, List.length_singleton]
    intro frame' hframe' ref href fid' oid0 hrefeq hlocEq
    subst hrefeq
    rw [stackWithIndex_eq, List.mem_append, List.mem_singleton] at hframe'
    rcases hframe' with hold | hnew
    · have hframe'_in_cfg : frame' ∈ cfg.stackWithIndex := by
        rw [stackWithIndex_eq_cfg]
        exact List.mem_append_left _ hold
      have hlocEq_cfg : (Reference.OId oid0).loc? cfg = some (Location.Stk fid') := by
        rw [fieldAsgn_corollary_stack_loc_eq hframe hobj]; exact hlocEq
      exact s2 frame' hframe'_in_cfg (Reference.OId oid0) href fid' oid0 rfl hlocEq_cfg
    · subst hnew
      dsimp at href
      have hlocEq_cfg : (Reference.OId oid0).loc? cfg = some (Location.Stk fid') := by
        rw [fieldAsgn_corollary_stack_loc_eq hframe hobj]; exact hlocEq
      rcases fieldAsgn_corollary_frame_field_insert_refs_mem hobj href with hfreq | horig
      · rw [Reference.OId.injEq] at hfreq
        rw [hfreq] at hlocEq_cfg
        obtain ⟨frameW, hlookupW, _⟩ := (oid_loc_stk_iff_in_stack vcfg).mp hlocEq_cfg
        have hlt := (List.getElem?_eq_some_iff.mp hlookupW).1
        have hlen : cfg.stackWithIndex.length = cfg.stack.dropLast.length + 1 := by
          unfold RuntimeConfig.stackWithIndex
          rw [List.length_mapIdx, hstacklen]
        rw [hlen] at hlt
        dsimp
        exact Nat.le_of_lt_succ hlt
      · have hframe_in_cfg :
            ({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex) ∈ cfg.stackWithIndex := by
          rw [stackWithIndex_eq_cfg]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        exact s2 _ hframe_in_cfg (Reference.OId oid0) horig fid' oid0 rfl hlocEq_cfg
  · subst hcfg'
    intro frame' hframe' ref href fid' oid0 hrefeq hlocEq
    subst hrefeq
    rw [← fieldAsgn_corollary_region_loc_eq vcfg hregion hobj oid0] at hlocEq
    exact s2 frame' hframe' (Reference.OId oid0) href fid' oid0 rfl hlocEq

-- If `resolveV` finds oid0 (as a variable value or a bridge value) and oid0 resolves into a heap
-- region rid0, that region already has an owning ancestor frame currently on the stack. Mirrors
-- varAsgn_corollary_resolveV_loc_ancestor (a fully general fact about resolveV, not specific to any
-- one mutation). Needed for S3's stack branch: the value newly stored via fieldAsgn's `y : VarName`
-- parameter is resolved directly via `resolveV` (no FieldAccess indirection, unlike VarAsgn's `yf`).
theorem fieldAsgn_corollary_resolveV_loc_ancestor {cfg : RuntimeConfig} {var : VarName} {oid0 : ObjectId}
    (vcfg : ValidConfig cfg) (hrv : resolveV var cfg = some (Reference.OId oid0)) (rid0 : RegionId)
    (hloc0 : (Reference.OId oid0).loc? cfg = some (Location.Rgn rid0)) :
    ∃ frame'' ∈ cfg.stackWithIndex, frame''.regionId = rid0 ∧ frame''.index < cfg.stack.length := by
  unfold resolveV at hrv
  cases hfV : cfg.stackWithIndex.findRev? (fun frame => frame.varMap.keys.contains var ∨ frame.bridgeVar == var) with
  | none => rw [hfV] at hrv; contradiction
  | some frameV =>
    rw [hfV] at hrv
    dsimp at hrv
    have hframeV_mem : frameV ∈ cfg.stackWithIndex := by
      rw [List.findRev?_eq_find?_reverse] at hfV
      exact List.mem_reverse.mp (List.mem_of_find?_eq_some hfV)
    have hframeV_lt : frameV.index < cfg.stack.length := by
      unfold RuntimeConfig.stackWithIndex at hframeV_mem
      obtain ⟨n, hn, heqn⟩ := List.mem_mapIdx.mp hframeV_mem
      rw [← heqn]
      exact hn
    cases hlookupV : frameV.varMap.lookup var with
    | some refV =>
      rw [hlookupV] at hrv
      dsimp at hrv
      rw [Option.some_inj] at hrv
      have hmemV : refV ∈ frameV.refs := by
        unfold Frame.refs
        exact List.mem_append_right _
          (List.mem_map_of_mem (f := (·.2)) (AList.mem_lookup_iff.mp (by rw [hlookupV]; rfl)))
      rw [hrv] at hmemV
      obtain ⟨frame'', hmem'', hregion'', hidx''⟩ :=
        vcfg.s3 frameV hframeV_mem (Reference.OId oid0) hmemV rid0 oid0 rfl hloc0
      exact ⟨frame'', hmem'', hregion'', lt_of_le_of_lt hidx'' hframeV_lt⟩
    | none =>
      rw [hlookupV] at hrv
      dsimp at hrv
      by_cases hbv : frameV.bridgeVar == var
      · rw [if_pos hbv] at hrv
        cases hregionV : cfg.heap.lookup frameV.regionId with
        | none => rw [hregionV] at hrv; dsimp at hrv; contradiction
        | some regionV =>
          rw [hregionV] at hrv
          dsimp at hrv
          rw [Option.some_inj, Reference.OId.injEq] at hrv
          have h1 := vcfg.h1
          have hmemBridge : regionV.bridgeObjectId ∈ regionV.objMap :=
            h1 regionV (List.mem_map_of_mem (f := (·.2)) (AList.mem_lookup_iff.mp (by rw [hregionV]; rfl)))
          have hlocBridge : (Reference.OId regionV.bridgeObjectId).loc? cfg = some (Location.Rgn frameV.regionId) :=
            (oid_loc_rgn_iff_in_heap vcfg).mpr ⟨regionV, hregionV, hmemBridge⟩
          rw [hrv, hloc0, Option.some_inj, Location.Rgn.injEq] at hlocBridge
          exact ⟨frameV, hframeV_mem, hlocBridge.symm, hframeV_lt⟩
      · rw [if_neg hbv] at hrv; contradiction

theorem fieldAsgn_S3 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  S3 cfg' := by
  intro vcfg h
  have s3 := vcfg.s3
  obtain ⟨frame, hframe, hcase⟩ := fieldAsgn_cases h
  unfold S3
  rcases hcase with
    ⟨oid, oid_y, obj, hxr, hyr, hloc, hobj, hcfg'⟩ |
    ⟨oid, oid_y, rid, region, obj, hxr, hyr, hloc, hregion, hobj, hyloc, hstatus, hfrid, hcfg'⟩
  · subst hcfg'
    obtain ⟨stack_eq, _⟩ := fieldAsgn_corollary_stack_eq hframe
    set newFrame : Frame :=
      { frame with objMap := frame.objMap.insert oid (obj.insert x.field (Reference.OId oid_y)) } with newFrame_def
    have stackWithIndex_eq_cfg :
        cfg.stackWithIndex =
          cfg.stack.dropLast.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) ++
            [({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex)] := by
      unfold RuntimeConfig.stackWithIndex
      conv_lhs => rw [stack_eq]
      rw [List.mapIdx_concat]
    have stackWithIndex_eq :
        (RuntimeConfig.stackWithIndex { stack := cfg.stack.dropLast ++ [newFrame], heap := cfg.heap }) =
          cfg.stack.dropLast.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) ++
            [({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex)] := by
      unfold RuntimeConfig.stackWithIndex
      dsimp
      rw [List.mapIdx_concat]
    have transport : ∀ frame3 : FrameWithIndex, frame3 ∈ cfg.stackWithIndex →
        ∃ frame4 ∈ (RuntimeConfig.stackWithIndex { stack := cfg.stack.dropLast ++ [newFrame], heap := cfg.heap }),
          frame4.regionId = frame3.regionId ∧ frame4.index = frame3.index := by
      intro frame3 hmem3
      rw [stackWithIndex_eq_cfg, List.mem_append, List.mem_singleton] at hmem3
      rcases hmem3 with hd | hl
      · exact ⟨frame3, by rw [stackWithIndex_eq]; exact List.mem_append_left _ hd, rfl, rfl⟩
      · refine ⟨{ newFrame with index := cfg.stack.dropLast.length }, ?_, ?_, ?_⟩
        · rw [stackWithIndex_eq]; exact List.mem_append_right _ (List.mem_singleton_self _)
        · rw [hl]
        · rw [hl]
    have hstacklen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by
      conv_lhs => rw [stack_eq]
      rw [List.length_append, List.length_singleton]
    intro frame' hframe' ref href rid' oid0 hrefeq hlocEq
    subst hrefeq
    have hlocEq_cfg : (Reference.OId oid0).loc? cfg = some (Location.Rgn rid') := by
      rw [fieldAsgn_corollary_stack_loc_eq hframe hobj]; exact hlocEq
    rw [stackWithIndex_eq, List.mem_append, List.mem_singleton] at hframe'
    rcases hframe' with hold | hnew
    · have hframe'_in_cfg : frame' ∈ cfg.stackWithIndex := by
        rw [stackWithIndex_eq_cfg]
        exact List.mem_append_left _ hold
      obtain ⟨frame'', hmem'', hregion'', hidx''⟩ :=
        s3 frame' hframe'_in_cfg (Reference.OId oid0) href rid' oid0 rfl hlocEq_cfg
      obtain ⟨frame4, hmem4, hregion4, hidx4⟩ := transport frame'' hmem''
      exact ⟨frame4, hmem4, hregion4.trans hregion'', (le_of_eq hidx4).trans hidx''⟩
    · subst hnew
      dsimp at href
      rcases fieldAsgn_corollary_frame_field_insert_refs_mem hobj href with hfreq | horig
      · rw [Reference.OId.injEq] at hfreq
        rw [hfreq] at hlocEq_cfg
        obtain ⟨frame'', hmem'', hregion'', hidx''⟩ :=
          fieldAsgn_corollary_resolveV_loc_ancestor vcfg hyr rid' hlocEq_cfg
        obtain ⟨frame4, hmem4, hregion4, hidx4⟩ := transport frame'' hmem''
        refine ⟨frame4, hmem4, hregion4.trans hregion'', ?_⟩
        dsimp
        rw [hidx4]
        rw [hstacklen] at hidx''
        exact Nat.le_of_lt_succ hidx''
      · have hframe_in_cfg :
            ({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex) ∈ cfg.stackWithIndex := by
          rw [stackWithIndex_eq_cfg]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        obtain ⟨frame'', hmem'', hregion'', hidx''⟩ :=
          s3 _ hframe_in_cfg (Reference.OId oid0) horig rid' oid0 rfl hlocEq_cfg
        obtain ⟨frame4, hmem4, hregion4, hidx4⟩ := transport frame'' hmem''
        exact ⟨frame4, hmem4, hregion4.trans hregion'', (le_of_eq hidx4).trans hidx''⟩
  · subst hcfg'
    intro frame' hframe' ref href rid' oid0 hrefeq hlocEq
    subst hrefeq
    rw [← fieldAsgn_corollary_region_loc_eq vcfg hregion hobj oid0] at hlocEq
    exact s3 frame' hframe' (Reference.OId oid0) href rid' oid0 rfl hlocEq

theorem fieldAsgn_HS1 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  HS1 cfg' := by
  intro vcfg h
  have hs1 := vcfg.hs1
  obtain ⟨frame, hframe, hcase⟩ := fieldAsgn_cases h
  unfold HS1
  rcases hcase with
    ⟨oid, oid_y, obj, hxr, hyr, hloc, hobj, hcfg'⟩ |
    ⟨oid, oid_y, rid, region, obj, hxr, hyr, hloc, hregion, hobj, hyloc, hstatus, hfrid, hcfg'⟩
  · subst hcfg'
    obtain ⟨stack_eq, _⟩ := fieldAsgn_corollary_stack_eq hframe
    have hoidmem : oid ∈ frame.objMap.keys := fieldAsgn_corollary_mem_keys_of_lookup hobj
    have frame_perm := fieldAsgn_corollary_insert_keys_perm
      (l := frame.objMap) (v := obj.insert x.field (Reference.OId oid_y)) hoidmem
    have stack_objectIds_append : ∀ (l : Stack) (f : Frame),
        Stack.objectIds (l ++ [f]) = Stack.objectIds l ++ f.objectIds := by
      intro l f
      unfold Stack.objectIds
      rw [List.bind_eq_flatMap, List.bind_eq_flatMap, List.flatMap_id, List.flatMap_id,
        List.map_append, List.flatten_append]
      simp
    have stack_refs_append : ∀ (l : Stack) (f : Frame), Stack.refs (l ++ [f]) = Stack.refs l ++ f.refs := by
      intro l f
      unfold Stack.refs
      rw [List.bind_eq_flatMap, List.bind_eq_flatMap, List.flatMap_id, List.flatMap_id,
        List.map_append, List.flatten_append]
      simp
    have cfg_stack_eq : Stack.objectIds cfg.stack = Stack.objectIds cfg.stack.dropLast ++ frame.objMap.keys := by
      conv_lhs => rw [stack_eq]
      rw [stack_objectIds_append]
      rfl
    have relocate : ∀ oid'', oid'' ∈ cfg.objectIds →
        oid'' ∈ Stack.objectIds (cfg.stack.dropLast ++
          [({ frame with objMap := frame.objMap.insert oid (obj.insert x.field (Reference.OId oid_y)) } : Frame)]) ++
          cfg.heap.objectIds := by
      intro oid'' hmem
      unfold RuntimeConfig.objectIds at hmem
      rw [cfg_stack_eq, List.mem_append, List.mem_append] at hmem
      rw [stack_objectIds_append, List.mem_append, List.mem_append]
      rcases hmem with (h1 | h2) | h3
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr (frame_perm.symm.mem_iff.mp h2))
      · exact Or.inr h3
    intro oid'' hmem
    unfold RuntimeConfig.objectIds
    dsimp
    apply relocate
    unfold RuntimeConfig.refs at hmem
    dsimp at hmem
    rw [stack_refs_append, List.mem_append, List.mem_append] at hmem
    rcases hmem with (hdrop | hnew) | hheap
    · apply hs1
      unfold RuntimeConfig.refs
      apply List.mem_append_left
      rw [stack_eq, stack_refs_append]
      exact List.mem_append_left _ hdrop
    · rcases fieldAsgn_corollary_frame_field_insert_refs_mem hobj hnew with heq | horig
      · rw [Reference.OId.injEq] at heq
        rw [heq]
        exact fieldAsgn_corollary_resolveV_oid_mem_objectIds vcfg hyr
      · apply hs1
        unfold RuntimeConfig.refs
        apply List.mem_append_left
        rw [stack_eq, stack_refs_append]
        exact List.mem_append_right _ horig
    · exact hs1 oid'' (List.mem_append_right _ hheap)
  · subst hcfg'
    have region_perm := fieldAsgn_corollary_insert_keys_perm
      (l := region.objMap) (v := obj.insert x.field (Reference.OId oid_y)) (fieldAsgn_corollary_mem_keys_of_lookup hobj)
    have heap_perm := fieldAsgn_corollary_region_heap_objectIds_perm
      (newRegion := { region with objMap := AList.insert oid (AList.insert x.field (Reference.OId oid_y) obj) region.objMap })
      hregion region_perm
    have relocate : ∀ oid'', oid'' ∈ cfg.objectIds → oid'' ∈ cfg.stack.objectIds ++
        Heap.objectIds (cfg.heap.insert rid
          { region with objMap := AList.insert oid (AList.insert x.field (Reference.OId oid_y) obj) region.objMap }) := by
      intro oid'' hmem
      unfold RuntimeConfig.objectIds at hmem
      rw [List.mem_append] at hmem ⊢
      rcases hmem with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (heap_perm.symm.mem_iff.mp h2)
    intro oid'' hmem
    apply relocate
    unfold RuntimeConfig.refs at hmem
    dsimp at hmem
    rw [List.mem_append] at hmem
    rcases hmem with hstack | hheap
    · exact hs1 oid'' (List.mem_append_left _ hstack)
    · have hridmem : rid ∈ cfg.heap.keys := fieldAsgn_corollary_mem_keys_of_lookup hregion
      rcases fieldAsgn_corollary_heap_insert_refs_mem hridmem hheap with hnewregion | hold
      · rcases fieldAsgn_corollary_region_field_insert_refs_mem hobj hnewregion with heq | horig
        · rw [Reference.OId.injEq] at heq
          rw [heq]
          exact fieldAsgn_corollary_resolveV_oid_mem_objectIds vcfg hyr
        · exact hs1 oid'' (List.mem_append_right _ (fieldAsgn_corollary_heap_refs_mem_of_lookup hregion horig))
      · exact hs1 oid'' (List.mem_append_right _ hold)

theorem fieldAsgn_HS2 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  HS2 cfg' := by
  intro vcfg h
  have hs2 := vcfg.hs2
  obtain ⟨frame, hframe, hcase⟩ := fieldAsgn_cases h
  unfold HS2
  rcases hcase with
    ⟨oid, oid_y, obj, hxr, hyr, hloc, hobj, hcfg'⟩ |
    ⟨oid, oid_y, rid, region, obj, hxr, hyr, hloc, hregion, hobj, hyloc, hstatus, hfrid, hcfg'⟩
  · subst hcfg'
    obtain ⟨stack_eq, _⟩ := fieldAsgn_corollary_stack_eq hframe
    have stack_refs_append : ∀ (l : Stack) (f : Frame), Stack.refs (l ++ [f]) = Stack.refs l ++ f.refs := by
      intro l f
      unfold Stack.refs
      rw [List.bind_eq_flatMap, List.bind_eq_flatMap, List.flatMap_id, List.flatMap_id,
        List.map_append, List.flatten_append]
      simp
    intro rid'' hmem
    dsimp at hmem ⊢
    unfold RuntimeConfig.refs at hmem
    dsimp at hmem
    rw [stack_refs_append, List.mem_append, List.mem_append] at hmem
    rcases hmem with (hdrop | hnew) | hheap
    · apply hs2 rid''
      unfold RuntimeConfig.refs
      apply List.mem_append_left
      rw [stack_eq, stack_refs_append]
      exact List.mem_append_left _ hdrop
    · rcases fieldAsgn_corollary_frame_field_insert_refs_mem hobj hnew with heq | horig
      · exact absurd heq (by simp)
      · apply hs2 rid''
        unfold RuntimeConfig.refs
        apply List.mem_append_left
        rw [stack_eq, stack_refs_append]
        exact List.mem_append_right _ horig
    · exact hs2 rid'' (List.mem_append_right _ hheap)
  · subst hcfg'
    dsimp
    have hridmem : rid ∈ cfg.heap.keys := fieldAsgn_corollary_mem_keys_of_lookup hregion
    intro rid'' hmem
    rw [fieldAsgn_corollary_heap_insert_keys_mem hridmem]
    unfold RuntimeConfig.refs at hmem
    dsimp at hmem
    rw [List.mem_append] at hmem
    rcases hmem with hstack | hheap
    · exact hs2 rid'' (List.mem_append_left _ hstack)
    · rcases fieldAsgn_corollary_heap_insert_refs_mem hridmem hheap with hnewregion | hold
      · rcases fieldAsgn_corollary_region_field_insert_refs_mem hobj hnewregion with heq | horig
        · exact absurd heq (by simp)
        · exact hs2 rid'' (List.mem_append_right _ (fieldAsgn_corollary_heap_refs_mem_of_lookup hregion horig))
      · exact hs2 rid'' (List.mem_append_right _ hold)

theorem fieldAsgn_valid : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  ValidConfig cfg' := by
  intro vcfg h
  exact {
    l1 := fieldAsgn_L1 vcfg h,
    l2 := fieldAsgn_L2 vcfg h,
    h1 := fieldAsgn_H1 vcfg h,
    h2 := fieldAsgn_H2 vcfg h,
    h3 := fieldAsgn_H3 vcfg h,
    s1 := fieldAsgn_S1 vcfg h,
    s2 := fieldAsgn_S2 vcfg h,
    s3 := fieldAsgn_S3 vcfg h,
    hs1 := fieldAsgn_HS1 vcfg h,
    hs2 := fieldAsgn_HS2 vcfg h
  }
