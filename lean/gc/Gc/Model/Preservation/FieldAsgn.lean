import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Theorems
import Gc.Model.Mutation

import Mathlib.Data.List.Infix

theorem fieldAsgn_cases (h : fieldAsgn xf y cfg = some cfg') :
    ∃ frame : FrameWithIndex, cfg.stackWithIndex.getLast? = some frame ∧
      ((∃ oid oid_y obj,
          resolveV xf.root cfg = some (Reference.OId oid) ∧
          resolveV y cfg = some (Reference.OId oid_y) ∧
          (Reference.OId oid).loc? cfg = some (Location.Stk frame.index) ∧
          frame.objMap.lookup oid = some obj ∧
          cfg' = { cfg with stack := cfg.stack.dropLast ++
            [ { frame with objMap := frame.objMap.insert oid (obj.insert xf.field (Reference.OId oid_y)) } ] }) ∨
       (∃ oid oid_y rid region obj,
          resolveV xf.root cfg = some (Reference.OId oid) ∧
          resolveV y cfg = some (Reference.OId oid_y) ∧
          (Reference.OId oid).loc? cfg = some (Location.Rgn rid) ∧
          cfg.heap.lookup rid = some region ∧
          region.objMap.lookup oid = some obj ∧
          (Reference.OId oid_y).loc? cfg = some (Location.Rgn rid) ∧
          region.status = Status.Open ∧
          cfg' = { cfg with heap := cfg.heap.insert rid { region with
            objMap := region.objMap.insert oid (obj.insert xf.field (Reference.OId oid_y)) } })) := by
  unfold fieldAsgn at h
  cases hframe : cfg.stackWithIndex.getLast? with
  | none => rw [hframe] at h; contradiction
  | some frame =>
    rw [hframe] at h
    dsimp at h
    refine ⟨frame, rfl, ?_⟩
    cases hxr : resolveV xf.root cfg with
    | none => rw [hxr] at h; contradiction
    | some xRef =>
      rw [hxr] at h
      dsimp at h
      cases hyr : resolveV y cfg with
      | none => rw [hyr] at h; contradiction
      | some yRef =>
        rw [hyr] at h
        dsimp at h
        cases xRef with
        | RId rid0 => dsimp at h; contradiction
        | OId oid =>
          cases yRef with
          | RId rid1 => dsimp at h; contradiction
          | OId oid_y =>
            dsimp at h
            cases hloc : (Reference.OId oid).loc? cfg with
            | none => rw [hloc] at h; dsimp at h; contradiction
            | some loc =>
              rw [hloc] at h
              dsimp at h
              cases loc with
              | Stk fid =>
                dsimp at h
                by_cases hfid : (fid == frame.index) = true
                · rw [if_pos hfid] at h
                  rw [beq_iff_eq] at hfid
                  cases hobj : frame.objMap.lookup oid with
                  | none => rw [hobj] at h; contradiction
                  | some obj =>
                    rw [hobj] at h
                    dsimp at h
                    rw [Option.some_inj] at h
                    left
                    subst hfid
                    exact ⟨oid, oid_y, obj, rfl, rfl, hloc, hobj, h.symm⟩
                · rw [if_neg hfid] at h; contradiction
              | Rgn rid =>
                dsimp at h
                cases hregion : cfg.heap.lookup rid with
                | none => rw [hregion] at h; contradiction
                | some region =>
                  rw [hregion] at h
                  dsimp at h
                  cases hobj : region.objMap.lookup oid with
                  | none => rw [hobj] at h; contradiction
                  | some obj =>
                    rw [hobj] at h
                    dsimp at h
                    cases hyloc : (Reference.OId oid_y).loc? cfg with
                    | none => rw [hyloc] at h; dsimp at h; contradiction
                    | some yloc =>
                      rw [hyloc] at h
                      dsimp at h
                      cases yloc with
                      | Stk fid' => dsimp at h; contradiction
                      | Rgn rid' =>
                        dsimp at h
                        by_cases hcond : rid == rid' ∧ region.status == Status.Open
                        · rw [if_pos hcond] at h
                          obtain ⟨hridEq0, hstatusEq0'⟩ := hcond
                          rw [beq_iff_eq] at hridEq0
                          have hstatusEq0 : region.status = Status.Open := by
                            cases hs : region.status with
                            | Open => rfl
                            | Closed => rw [hs] at hstatusEq0'; contradiction
                          rw [Option.some_inj] at h
                          right
                          subst hridEq0
                          exact ⟨oid, oid_y, rid, region, obj, rfl, rfl, hloc, hregion, hobj, hyloc,
                            hstatusEq0, h.symm⟩
                        · rw [if_neg hcond] at h; contradiction

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
    ⟨oid, oid_y, rid, region, obj, hxr, hyr, hloc, hregion, hobj, hyloc, hstatus, hcfg'⟩
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
    ⟨oid, oid_y, rid, region, obj, hxr, hyr, hloc, hregion, hobj, hyloc, hstatus, hcfg'⟩
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
    ⟨oid, oid_y, rid, region, obj, hxr, hyr, hloc, hregion, hobj, hyloc, hstatus, hcfg'⟩
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
    ⟨oid, oid_y, rid, region, obj, hxr, hyr, hloc, hregion, hobj, hyloc, hstatus, hcfg'⟩
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
    ⟨oid, oid_y, rid, region, obj, hxr, hyr, hloc, hregion, hobj, hyloc, hstatus, hcfg'⟩
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

theorem fieldAsgn_H3 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  H3 cfg' := by
  sorry

theorem fieldAsgn_S2 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  S2 cfg' := by
  sorry

theorem fieldAsgn_S3 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  S3 cfg' := by
  sorry

theorem fieldAsgn_HS1 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  HS1 cfg' := by
  intro vcfg h
  have hs1 := vcfg.hs1
  obtain ⟨frame, hframe, hcase⟩ := fieldAsgn_cases h
  unfold HS1
  rcases hcase with
    ⟨oid, oid_y, obj, hxr, hyr, hloc, hobj, hcfg'⟩ |
    ⟨oid, oid_y, rid, region, obj, hxr, hyr, hloc, hregion, hobj, hyloc, hstatus, hcfg'⟩
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
    ⟨oid, oid_y, rid, region, obj, hxr, hyr, hloc, hregion, hobj, hyloc, hstatus, hcfg'⟩
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
