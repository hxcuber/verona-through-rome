import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Theorems
import Gc.Model.Mutation.Swap
import Gc.Model.Preservation.Common

import Mathlib.Data.List.Infix


-- Relates the `stackWithIndex.getLast?` frame used by `swap_cases` back to `cfg.stack`'s own
-- decomposition, mirroring fieldAsgn_corollary_stack_eq/VarAsgn.lean's stack_eq construction.
theorem swap_corollary_stack_eq {cfg : RuntimeConfig} {frame : FrameWithIndex}
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

theorem swap_S1 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  S1 cfg' := by
  intro vcfg h
  have s1 := vcfg.s1
  obtain ⟨frame, hframe, yRef, hyr, yRefLoc, hyrl, yfRef, hyf, yfRefLoc, hyfl, hcase⟩ := swap_cases h
  unfold S1
  obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
  have s1' : (cfg.stack.dropLast.map (fun frame => frame.regionId) ++ [frame.regionId]).Nodup := by
    have := s1
    unfold S1 at this
    rw [stack_eq, List.map_append] at this
    exact this
  rcases hcase with
    ⟨yoid, xRef, obj, hxb, hyoid, hyrloc, hxr, hobj, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xoid, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hxrl, hxrid, hstatus, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hstatus, hcfg'⟩ |
    ⟨yoid, yrid, yfoid, yfrid, region, obj, hxb, hyoid, hyrloc, hyfoid, hyfrloc, hyrid, hyfrid, hregion, hobj, hcfg'⟩
  · subst hcfg'
    dsimp
    rw [List.map_append]
    exact s1'
  · subst hcfg'
    dsimp
    rw [List.map_append]
    exact s1'
  · subst hcfg'
    dsimp
    rw [List.map_append]
    exact s1'
  · subst hcfg'
    dsimp
    exact s1

-- Generic AList fact (no domain dependency): replacing the value at an already-present key
-- reorders `entries` but only *permutes* `.keys`, never changes the key set. Used at both
-- nesting levels in this file (frame.objMap/region.objMap insert at the already-present `yoid`,
-- and the analogous facts for varMap-level operations aren't needed since swap never allocates).
theorem swap_corollary_insert_keys_perm {α : Type*} {β : α → Type*} [DecidableEq α]
    {l : AList β} {k : α} {v : β k} (hk : k ∈ l.keys) :
    (l.insert k v).keys.Perm l.keys := by
  obtain ⟨v0, l1e, l2e, hnotmem, heq, hkerase⟩ := List.exists_of_kerase hk
  unfold AList.keys
  rw [AList.entries_insert, hkerase]
  conv_rhs => rw [heq]
  rw [List.keys_cons, List.keys_append, List.keys_append, List.keys_cons]
  exact List.perm_middle.symm

-- Generic AList fact: a successful `lookup` means the key is already present.
theorem swap_corollary_mem_keys_of_lookup {α : Type*} {β : α → Type*} [DecidableEq α]
    {l : AList β} {k : α} {v : β k} (hv : l.lookup k = some v) : k ∈ l.keys :=
  AList.mem_keys.mp (AList.lookup_isSome.mp (by rw [hv]; rfl))

-- The region-touching branches' `heap.insert` at an already-present key, where the newly-inserted
-- region's objMap key set is only known up to a `Perm` of the old region's (the region's objMap
-- genuinely changes, not just a scalar field) -- composes the outer heap-entries reorder with the
-- inner region-level permutation. Mirrors fieldAsgn_corollary_region_heap_objectIds_perm.
theorem swap_corollary_region_heap_objectIds_perm {cfg : RuntimeConfig} {rid : RegionId}
    {region newRegion : Region} (hregion : cfg.heap.lookup rid = some region)
    (hperm : newRegion.objMap.keys.Perm region.objMap.keys) :
    (Heap.objectIds (cfg.heap.insert rid newRegion)).Perm cfg.heap.objectIds := by
  obtain ⟨region2, l1e, l2e, hnotmem, heq, hkerase⟩ :=
    List.exists_of_kerase (swap_corollary_mem_keys_of_lookup hregion)
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

-- Generic fact used for the stack-mutation branches: `Stack.objectIds` distributes over `++ [f]`.
theorem swap_corollary_stack_objectIds_append (l : Stack) (f : Frame) :
    Stack.objectIds (l ++ [f]) = Stack.objectIds l ++ f.objectIds := by
  unfold Stack.objectIds
  rw [List.bind_eq_flatMap, List.bind_eq_flatMap, List.flatMap_id, List.flatMap_id,
    List.map_append, List.flatten_append]
  simp

theorem swap_L1 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  L1 cfg' := by
  intro vcfg h
  have l1 := vcfg.l1
  obtain ⟨frame, hframe, yRef, hyr, yRefLoc, hyrl, yfRef, hyf, yfRefLoc, hyfl, hcase⟩ := swap_cases h
  unfold L1
  rcases hcase with
    ⟨yoid, xRef, obj, hxb, hyoid, hyrloc, hxr, hobj, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xoid, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hxrl, hxrid, hstatus, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hstatus, hcfg'⟩ |
    ⟨yoid, yrid, yfoid, yfrid, region, obj, hxb, hyoid, hyrloc, hyfoid, hyfrloc, hyrid, hyfrid, hregion, hobj, hcfg'⟩
  · subst hcfg'
    obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
    have hoidmem : yoid ∈ frame.objMap.keys := swap_corollary_mem_keys_of_lookup hobj
    have frame_perm := swap_corollary_insert_keys_perm (l := frame.objMap) (v := obj.insert yf.field xRef) hoidmem
    unfold RuntimeConfig.objectIds
    dsimp
    rw [swap_corollary_stack_objectIds_append]
    have cfg_stack_eq : Stack.objectIds cfg.stack = Stack.objectIds cfg.stack.dropLast ++ frame.objMap.keys := by
      conv_lhs => rw [stack_eq]
      rw [swap_corollary_stack_objectIds_append]
      rfl
    have perm2 :=
      (List.Perm.append_left (Stack.objectIds cfg.stack.dropLast) frame_perm).append_right cfg.heap.objectIds
    rw [← cfg_stack_eq] at perm2
    exact l1.perm perm2.symm
  · subst hcfg'
    obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
    have hoidmem : yoid ∈ region.objMap.keys := swap_corollary_mem_keys_of_lookup hobj
    have region_perm := swap_corollary_insert_keys_perm (l := region.objMap) (v := obj.insert yf.field (Reference.OId xoid)) hoidmem
    have heap_perm := swap_corollary_region_heap_objectIds_perm
      (newRegion := { region with objMap := AList.insert yoid (obj.insert yf.field (Reference.OId xoid)) region.objMap })
      hregion region_perm
    unfold RuntimeConfig.objectIds
    dsimp
    have cfg'_stack_eq : Stack.objectIds
        (cfg.stack.dropLast ++ [({ frame with varMap := frame.varMap.insert x yfRef } : Frame)]) =
        Stack.objectIds cfg.stack := by
      rw [swap_corollary_stack_objectIds_append]
      conv_rhs => rw [stack_eq]
      rw [swap_corollary_stack_objectIds_append]
      rfl
    rw [cfg'_stack_eq]
    exact l1.perm (List.Perm.append_left cfg.stack.objectIds heap_perm).symm
  · subst hcfg'
    obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
    have hoidmem : yoid ∈ region.objMap.keys := swap_corollary_mem_keys_of_lookup hobj
    have region_perm := swap_corollary_insert_keys_perm (l := region.objMap) (v := obj.insert yf.field (Reference.RId xrid)) hoidmem
    have heap_perm := swap_corollary_region_heap_objectIds_perm
      (newRegion := { region with objMap := AList.insert yoid (obj.insert yf.field (Reference.RId xrid)) region.objMap })
      hregion region_perm
    unfold RuntimeConfig.objectIds
    dsimp
    have cfg'_stack_eq : Stack.objectIds
        (cfg.stack.dropLast ++ [({ frame with varMap := frame.varMap.insert x yfRef } : Frame)]) =
        Stack.objectIds cfg.stack := by
      rw [swap_corollary_stack_objectIds_append]
      conv_rhs => rw [stack_eq]
      rw [swap_corollary_stack_objectIds_append]
      rfl
    rw [cfg'_stack_eq]
    exact l1.perm (List.Perm.append_left cfg.stack.objectIds heap_perm).symm
  · subst hcfg'
    have hoidmem : yoid ∈ region.objMap.keys := swap_corollary_mem_keys_of_lookup hobj
    have region_perm := swap_corollary_insert_keys_perm
      (l := region.objMap) (v := obj.insert yf.field (Reference.OId region.bridgeObjectId)) hoidmem
    have heap_perm := swap_corollary_region_heap_objectIds_perm
      (newRegion := { region with
        bridgeObjectId := yfoid,
        objMap := AList.insert yoid (obj.insert yf.field (Reference.OId region.bridgeObjectId)) region.objMap })
      hregion region_perm
    unfold RuntimeConfig.objectIds
    dsimp
    exact l1.perm (List.Perm.append_left cfg.stack.objectIds heap_perm).symm

theorem swap_L2 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  L2 cfg' := by
  intro vcfg h
  have l2 := vcfg.l2
  obtain ⟨frame, hframe, yRef, hyr, yRefLoc, hyrl, yfRef, hyf, yfRefLoc, hyfl, hcase⟩ := swap_cases h
  unfold L2
  rcases hcase with
    ⟨yoid, xRef, obj, hxb, hyoid, hyrloc, hxr, hobj, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xoid, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hxrl, hxrid, hstatus, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hstatus, hcfg'⟩ |
    ⟨yoid, yrid, yfoid, yfrid, region, obj, hxb, hyoid, hyrloc, hyfoid, hyfrloc, hyrid, hyfrid, hregion, hobj, hcfg'⟩
  · subst hcfg'
    obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
    have frame_mem : frame.toFrame ∈ cfg.stack :=
      stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self _)
    dsimp
    intro frame'' hmem
    rw [List.mem_append, List.mem_singleton] at hmem
    cases hmem with
    | inl hdrop => exact l2 frame'' (List.mem_of_mem_dropLast hdrop)
    | inr heqframe => subst heqframe; exact l2 frame.toFrame frame_mem
  · subst hcfg'
    obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
    have frame_mem : frame.toFrame ∈ cfg.stack :=
      stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self _)
    dsimp
    intro frame'' hmem
    rw [List.mem_append, List.mem_singleton] at hmem
    obtain ⟨region0, hlookup0, hopen0⟩ :
        ∃ region0, cfg.heap.lookup frame''.regionId = some region0 ∧ region0.status = Status.Open := by
      cases hmem with
      | inl hdrop => exact l2 frame'' (List.mem_of_mem_dropLast hdrop)
      | inr heqframe => subst heqframe; exact l2 frame.toFrame frame_mem
    by_cases heq : frame''.regionId = rid
    · rw [heq] at hlookup0
      rw [hregion, Option.some_inj] at hlookup0
      refine ⟨{ region with
          objMap := AList.insert yoid (AList.insert yf.field (Reference.OId xoid) obj) region.objMap }, ?_, ?_⟩
      · rw [heq, AList.lookup_insert]
      · dsimp; exact hstatus
    · refine ⟨region0, ?_, hopen0⟩
      rw [AList.lookup_insert_ne heq]
      exact hlookup0
  · subst hcfg'
    obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
    have frame_mem : frame.toFrame ∈ cfg.stack :=
      stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self _)
    dsimp
    intro frame'' hmem
    rw [List.mem_append, List.mem_singleton] at hmem
    obtain ⟨region0, hlookup0, hopen0⟩ :
        ∃ region0, cfg.heap.lookup frame''.regionId = some region0 ∧ region0.status = Status.Open := by
      cases hmem with
      | inl hdrop => exact l2 frame'' (List.mem_of_mem_dropLast hdrop)
      | inr heqframe => subst heqframe; exact l2 frame.toFrame frame_mem
    by_cases heq : frame''.regionId = rid
    · rw [heq] at hlookup0
      rw [hregion, Option.some_inj] at hlookup0
      refine ⟨{ region with
          objMap := AList.insert yoid (AList.insert yf.field (Reference.RId xrid) obj) region.objMap }, ?_, ?_⟩
      · rw [heq, AList.lookup_insert]
      · dsimp; exact hstatus
    · refine ⟨region0, ?_, hopen0⟩
      rw [AList.lookup_insert_ne heq]
      exact hlookup0
  · subst hcfg'
    dsimp
    intro frame'' hmem
    obtain ⟨region0, hlookup0, hopen0⟩ := l2 frame'' hmem
    by_cases heq : frame''.regionId = yrid
    · rw [heq] at hlookup0
      rw [hregion, Option.some_inj] at hlookup0
      refine ⟨{ region with
          bridgeObjectId := yfoid,
          objMap := AList.insert yoid (AList.insert yf.field (Reference.OId region.bridgeObjectId) obj) region.objMap
        }, ?_, ?_⟩
      · rw [heq, AList.lookup_insert]
      · dsimp; rw [hlookup0]; exact hopen0
    · refine ⟨region0, ?_, hopen0⟩
      rw [AList.lookup_insert_ne heq]
      exact hlookup0

theorem swap_H1 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  H1 cfg' := by
  intro vcfg h
  have h1 := vcfg.h1
  obtain ⟨frame, hframe, yRef, hyr, yRefLoc, hyrl, yfRef, hyf, yfRefLoc, hyfl, hcase⟩ := swap_cases h
  unfold H1
  rcases hcase with
    ⟨yoid, xRef, obj, hxb, hyoid, hyrloc, hxr, hobj, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xoid, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hxrl, hxrid, hstatus, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hstatus, hcfg'⟩ |
    ⟨yoid, yrid, yfoid, yfrid, region, obj, hxb, hyoid, hyrloc, hyfoid, hyfrloc, hyrid, hyfrid, hregion, hobj, hcfg'⟩
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
  · subst hcfg'
    dsimp
    have region_mem : region ∈ cfg.heap.regions := by
      unfold Heap.regions
      exact List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hregion)
    have hyfrid_eq : yrid = yfrid := hyrid.trans hyfrid.symm
    have hyfoid_loc : (Reference.OId yfoid).loc? cfg = some (Location.Rgn yrid) := by
      rw [← hyfoid, hyfl, hyfrloc, hyfrid_eq]
    obtain ⟨region', hregion', hyfoid_mem'⟩ := (oid_loc_rgn_iff_in_heap vcfg).mp hyfoid_loc
    have region'_eq : region' = region := by rw [hregion] at hregion'; exact Option.some_inj.mp hregion'.symm
    have hyfoid_mem : yfoid ∈ region.objMap := region'_eq ▸ hyfoid_mem'
    intro region0 hregion0
    unfold Heap.regions at hregion0
    rw [AList.entries_insert, List.map_cons, List.mem_cons] at hregion0
    cases hregion0 with
    | inl heqregion =>
      subst heqregion
      dsimp
      exact (AList.mem_insert _).mpr (Or.inr hyfoid_mem)
    | inr hkeraseregion =>
      apply h1
      unfold Heap.regions
      exact (List.Sublist.map _ (List.kerase_sublist yrid cfg.heap.entries)).mem hkeraseregion

-- Traces resolveFA's own computation to show it agrees with the already-known
-- frame.objMap.lookup yoid = some obj (the SWAP-STACK case's own derivation, independent of
-- resolveFA's internal one) -- establishing that the field being overwritten by the swap held
-- exactly `yfRef` beforehand, i.e. this genuinely IS an exchange of two live values, not merely an
-- overwrite of an unknown old one.
theorem swap_corollary_stack_field_eq_yfRef {cfg : RuntimeConfig} {frame : FrameWithIndex} {yoid : ObjectId}
    {obj : Object} {yf : FieldAccess} {yfRef : Reference}
    (hframe_mem : frame ∈ cfg.stackWithIndex)
    (hyr : resolveV yf.root cfg = some (Reference.OId yoid))
    (hyrl : (Reference.OId yoid).loc? cfg = some (Location.Stk frame.index))
    (hobj : frame.objMap.lookup yoid = some obj)
    (hyf : resolveFA yf cfg = some yfRef) :
    obj.lookup yf.field = some yfRef := by
  unfold resolveFA at hyf
  rw [hyr] at hyf
  dsimp at hyf
  rw [hyrl] at hyf
  dsimp at hyf
  rw [swap_corollary_stackWithIndex_find_eq hframe_mem] at hyf
  dsimp at hyf
  rw [hobj] at hyf
  dsimp at hyf
  exact hyf

-- Region-side analogue: resolveFA's internal heap/region lookups are literally the same function
-- calls as the ones already performed by the region-branch cases, so no uniqueness argument is
-- needed here (unlike the stack case's `.find?`).
theorem swap_corollary_region_field_eq_yfRef {cfg : RuntimeConfig} {yoid : ObjectId} {rid : RegionId}
    {region : Region} {obj : Object} {yf : FieldAccess} {yfRef : Reference}
    (hyr : resolveV yf.root cfg = some (Reference.OId yoid))
    (hyrl : (Reference.OId yoid).loc? cfg = some (Location.Rgn rid))
    (hregion : cfg.heap.lookup rid = some region)
    (hobj : region.objMap.lookup yoid = some obj)
    (hyf : resolveFA yf cfg = some yfRef) :
    obj.lookup yf.field = some yfRef := by
  unfold resolveFA at hyf
  rw [hyr] at hyf
  dsimp at hyf
  rw [hyrl] at hyf
  dsimp at hyf
  rw [hregion] at hyf
  dsimp at hyf
  rw [hobj] at hyf
  dsimp at hyf
  exact hyf

-- Generic AList fact (Reference-valued, α-indexed): membership after inserting at a key is either
-- the newly-written value or a pre-existing one. Covers both VarMap and Object (`Object := VarMap`).
theorem swap_corollary_alist_insert_refs_mem {α : Type*} [DecidableEq α] {l : AList (fun _ : α => Reference)}
    {k : α} {v r : Reference} (hr : r ∈ (l.insert k v).entries.map (·.2)) :
    r = v ∨ r ∈ l.entries.map (·.2) := by
  by_cases hk : k ∈ l
  · obtain ⟨v0, l1e, l2e, hnotmem, heq, hkerase⟩ := List.exists_of_kerase (AList.mem_keys.mp hk)
    rw [AList.entries_insert, hkerase, List.map_cons, List.mem_cons] at hr
    rw [heq, List.map_append, List.map_cons, List.mem_append, List.mem_cons]
    dsimp only at hr ⊢
    rw [List.map_append, List.mem_append] at hr
    tauto
  · rw [AList.entries_insert_of_notMem hk, List.map_cons, List.mem_cons] at hr
    dsimp only at hr
    tauto

-- Once an object is already stored at some key of an ObjMap, its own refs already contribute to
-- the ObjMap-level bind-refs.
theorem swap_corollary_objMap_bind_refs_mem_of_lookup {m : ObjMap} {oid : ObjectId} {obj : Object}
    {r : Reference} (hobj : m.lookup oid = some obj) (hr : r ∈ Object.refs obj) :
    r ∈ (m.entries.map (·.2) >>= Object.refs) := by
  have hmem : (⟨oid, obj⟩ : Sigma (fun _ : ObjectId => Object)) ∈ m.entries :=
    AList.mem_lookup_iff.mp (by rw [hobj]; rfl)
  rw [List.bind_eq_flatMap, List.mem_flatMap]
  exact ⟨obj, List.mem_map_of_mem (f := (·.2)) hmem, hr⟩

-- Membership after inserting at an ObjMap key: either from the newly-written object, or already present.
theorem swap_corollary_objMap_insert_bind_refs_mem {m : ObjMap} {oid : ObjectId} {v : Object} {r : Reference}
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
theorem swap_corollary_heap_refs_mem_of_lookup {cfg : RuntimeConfig} {rid : RegionId} {region : Region}
    {r : Reference} (hregion : cfg.heap.lookup rid = some region) (hr : r ∈ Region.refs region) :
    r ∈ Heap.refs cfg.heap := by
  have hmem : (⟨rid, region⟩ : Sigma (fun _ : RegionId => Region)) ∈ cfg.heap.entries :=
    AList.mem_lookup_iff.mp (by rw [hregion]; rfl)
  unfold Heap.refs
  rw [List.bind_eq_flatMap, List.mem_flatMap]
  exact ⟨region, List.mem_map_of_mem (f := (·.2)) hmem, hr⟩

-- Membership after inserting at a heap key: either from the newly-written region, or already present.
theorem swap_corollary_heap_insert_refs_mem {cfg : RuntimeConfig} {rid : RegionId} {newRegion : Region}
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
theorem swap_corollary_heap_insert_keys_mem {cfg : RuntimeConfig} {rid : RegionId} {newRegion : Region}
    (hridmem : rid ∈ cfg.heap.keys) (rid' : RegionId) :
    rid' ∈ (cfg.heap.insert rid newRegion).keys ↔ rid' ∈ cfg.heap.keys := by
  rw [← AList.mem_keys, AList.mem_insert, AList.mem_keys]
  exact or_iff_right_of_imp (fun heq => heq ▸ hridmem)

-- Generic fact used for the stack-mutation branches: `Stack.refs` distributes over `++ [f]`.
theorem swap_corollary_stack_refs_append (l : Stack) (f : Frame) :
    Stack.refs (l ++ [f]) = Stack.refs l ++ f.refs := by
  unfold Stack.refs
  rw [List.bind_eq_flatMap, List.bind_eq_flatMap, List.flatMap_id, List.flatMap_id,
    List.map_append, List.flatten_append]
  simp

-- A reference already present in some frame's own refs is already present in the whole stack's refs.
theorem swap_corollary_frame_refs_mem_stack {stack : Stack} {frame : Frame} {r : Reference}
    (hmem : frame ∈ stack) (hr : r ∈ Frame.refs frame) : r ∈ Stack.refs stack := by
  unfold Stack.refs
  rw [List.bind_eq_flatMap, List.flatMap_id, List.mem_flatten]
  exact ⟨Frame.refs frame, List.mem_map_of_mem hmem, hr⟩

-- Generic AList fact (Reference-valued): replacing the value at an already-present key changes
-- the count of any target `t` by exactly (v_new==t?1:0) - (v_old==t?1:0), captured additively (to
-- avoid Nat subtraction) as an equation relating the two counts via the two `==` conditions. This
-- is what makes `swap` provably an *exchange* rather than a plain overwrite: applying this once
-- for each of the two slots being swapped, the two `if`-terms cancel out exactly when combined.
theorem swap_corollary_alist_insert_count_eq {α : Type*} [DecidableEq α] {l : AList (fun _ : α => Reference)}
    {k : α} {v_old v_new t : Reference} (hlookup : l.lookup k = some v_old) :
    ((l.insert k v_new).entries.map (·.2)).count t + (if (v_old == t) = true then 1 else 0) =
    (l.entries.map (·.2)).count t + (if (v_new == t) = true then 1 else 0) := by
  obtain ⟨v0, l1e, l2e, hnotmem, heq, hkerase⟩ := List.exists_of_kerase (swap_corollary_mem_keys_of_lookup hlookup)
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

-- Container-level analogue, one level up: replacing the value at an already-present ObjMap key
-- changes the whole bind-refs count by exactly the delta of the object's own count -- a genuine
-- identity for *any* replacement value (not just ones related to the old one), since both sides
-- reduce to "other objects' count + old/new object's own count".
theorem swap_corollary_objMap_insert_bind_count_eq {m : ObjMap} {oid : ObjectId} {obj v : Object} {t : Reference}
    (hobj : m.lookup oid = some obj) :
    ((m.insert oid v).entries.map (·.2) >>= Object.refs).count t + (Object.refs obj).count t =
    (m.entries.map (·.2) >>= Object.refs).count t + (Object.refs v).count t := by
  obtain ⟨v0, l1e, l2e, hnotmem, heq, hkerase⟩ := List.exists_of_kerase (swap_corollary_mem_keys_of_lookup hobj)
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
  rw [hnewbind, holdbind, List.count_append, List.count_append, List.count_append]
  omega

-- Heap-level analogue of the above (Heap of Regions instead of ObjMap of Objects).
theorem swap_corollary_heap_insert_bind_count_eq {cfg : RuntimeConfig} {rid : RegionId}
    {region newRegion : Region} {t : Reference} (hregion : cfg.heap.lookup rid = some region) :
    (Heap.refs (cfg.heap.insert rid newRegion)).count t + (Region.refs region).count t =
    (Heap.refs cfg.heap).count t + (Region.refs newRegion).count t := by
  obtain ⟨v0, l1e, l2e, hnotmem, heq, hkerase⟩ :=
    List.exists_of_kerase (swap_corollary_mem_keys_of_lookup hregion)
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
  rw [hnewbind, holdbind, List.count_append, List.count_append, List.count_append]
  omega

theorem swap_H2 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  H2 cfg' := by
  intro vcfg h
  obtain ⟨frame, hframe, yRef, hyr, yRefLoc, hyrl, yfRef, hyf, yfRefLoc, hyfl, hcase⟩ := swap_cases h
  have frame_mem : frame ∈ cfg.stackWithIndex := List.mem_of_getLast? hframe
  unfold H2
  rcases hcase with
    ⟨yoid, xRef, obj, hxb, hyoid, hyrloc, hxr, hobj, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xoid, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hxrl, hxrid, hstatus, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hstatus, hcfg'⟩ |
    ⟨yoid, yrid, yfoid, yfrid, region, obj, hxb, hyoid, hyrloc, hyfoid, hyfrloc, hyrid, hyfrid, hregion, hobj, hcfg'⟩
  · -- SWAP-STACK: a genuine exchange within the same frame -- exact count preservation
    subst hcfg'
    have hfield : obj.lookup yf.field = some yfRef :=
      swap_corollary_stack_field_eq_yfRef frame_mem (hyoid ▸ hyr) (hyoid ▸ hyrloc ▸ hyrl) hobj hyf
    obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
    set newFrame : Frame := { frame with
        varMap := frame.varMap.insert x yfRef,
        objMap := frame.objMap.insert yoid (obj.insert yf.field xRef) } with newFrame_def
    have hframe_count_eq : ∀ t, (Frame.refs newFrame).count t = (Frame.refs frame.toFrame).count t := by
      intro t
      have eq_inner : (Object.refs (obj.insert yf.field xRef)).count t + (if (yfRef == t) = true then 1 else 0) =
          (Object.refs obj).count t + (if (xRef == t) = true then 1 else 0) :=
        swap_corollary_alist_insert_count_eq (l := obj) (k := yf.field) (v_old := yfRef)
          (v_new := xRef) (t := t) hfield
      have eq_outer := swap_corollary_objMap_insert_bind_count_eq (m := frame.objMap) (oid := yoid)
        (obj := obj) (v := obj.insert yf.field xRef) (t := t) hobj
      have eq_var := swap_corollary_alist_insert_count_eq (l := frame.varMap) (k := x) (v_old := xRef)
        (v_new := yfRef) (t := t) hxr
      have hgoal : (Frame.refs newFrame).count t =
          ((frame.objMap.insert yoid (obj.insert yf.field xRef)).entries.map (·.2) >>= Object.refs).count t +
          ((frame.varMap.insert x yfRef).entries.map (·.2)).count t := by
        unfold Frame.refs
        rw [newFrame_def, List.count_append]
      have hgoal' : (Frame.refs frame.toFrame).count t =
          (frame.objMap.entries.map (·.2) >>= Object.refs).count t + (frame.varMap.entries.map (·.2)).count t := by
        unfold Frame.refs
        rw [List.count_append]
      rw [hgoal, hgoal']
      omega
    have hstack_count_eq : ∀ t,
        (Stack.refs (cfg.stack.dropLast ++ [newFrame])).count t = (Stack.refs cfg.stack).count t := by
      intro t
      rw [swap_corollary_stack_refs_append, List.count_append]
      conv_rhs => rw [stack_eq, swap_corollary_stack_refs_append, List.count_append]
      rw [hframe_count_eq]
    intro rid'
    have h2' := vcfg.h2 rid'
    dsimp
    rw [hstack_count_eq]
    exact h2'
  · -- SWAP-REGION-OBJECT: the exchange spans the stack/heap boundary -- only the *sum* is preserved
    subst hcfg'
    have hfield : obj.lookup yf.field = some yfRef :=
      swap_corollary_region_field_eq_yfRef (hyoid ▸ hyr) (hyoid ▸ hyrloc ▸ hyrl) hregion hobj hyf
    obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
    set newFrame : Frame := { frame with varMap := frame.varMap.insert x yfRef } with newFrame_def
    set newRegion : Region := { region with
        objMap := AList.insert yoid (obj.insert yf.field (Reference.OId xoid)) region.objMap } with newRegion_def
    have hsum_eq : ∀ t,
        (Stack.refs (cfg.stack.dropLast ++ [newFrame])).count t + (Heap.refs (cfg.heap.insert rid newRegion)).count t =
        (Stack.refs cfg.stack).count t + (Heap.refs cfg.heap).count t := by
      intro t
      have eq_inner : (Object.refs (obj.insert yf.field (Reference.OId xoid))).count t +
            (if (yfRef == t) = true then 1 else 0) =
          (Object.refs obj).count t + (if ((Reference.OId xoid) == t) = true then 1 else 0) :=
        swap_corollary_alist_insert_count_eq (l := obj) (k := yf.field) (v_old := yfRef)
          (v_new := Reference.OId xoid) (t := t) hfield
      have eq_region : (Region.refs newRegion).count t + (Object.refs obj).count t =
          (Region.refs region).count t + (Object.refs (obj.insert yf.field (Reference.OId xoid))).count t :=
        swap_corollary_objMap_insert_bind_count_eq (m := region.objMap) (oid := yoid)
          (obj := obj) (v := obj.insert yf.field (Reference.OId xoid)) (t := t) hobj
      have eq_heap := swap_corollary_heap_insert_bind_count_eq (cfg := cfg) (rid := rid) (region := region)
        (newRegion := newRegion) (t := t) hregion
      have eq_var := swap_corollary_alist_insert_count_eq (l := frame.varMap) (k := x)
        (v_old := Reference.OId xoid) (v_new := yfRef) (t := t) hxr
      have hframecount : (Frame.refs newFrame).count t =
          (frame.objMap.entries.map (·.2) >>= Object.refs).count t +
          ((frame.varMap.insert x yfRef).entries.map (·.2)).count t := by
        unfold Frame.refs
        rw [newFrame_def, List.count_append]
      have hframecount' : (Frame.refs frame.toFrame).count t =
          (frame.objMap.entries.map (·.2) >>= Object.refs).count t + (frame.varMap.entries.map (·.2)).count t := by
        unfold Frame.refs
        rw [List.count_append]
      have hstackgoal : (Stack.refs (cfg.stack.dropLast ++ [newFrame])).count t =
          (Stack.refs cfg.stack.dropLast).count t + (Frame.refs newFrame).count t := by
        rw [swap_corollary_stack_refs_append, List.count_append]
      have hstackgoal' : (Stack.refs cfg.stack).count t =
          (Stack.refs cfg.stack.dropLast).count t + (Frame.refs frame.toFrame).count t := by
        conv_lhs => rw [stack_eq]
        rw [swap_corollary_stack_refs_append, List.count_append]
      rw [hstackgoal, hstackgoal', hframecount, hframecount']
      omega
    intro rid'
    have h2' := vcfg.h2 rid'
    dsimp
    rw [hsum_eq]
    exact h2'
  · -- SWAP-REGION-REGION: identical shape to SWAP-REGION-OBJECT, xRef is Reference.RId xrid instead
    subst hcfg'
    have hfield : obj.lookup yf.field = some yfRef :=
      swap_corollary_region_field_eq_yfRef (hyoid ▸ hyr) (hyoid ▸ hyrloc ▸ hyrl) hregion hobj hyf
    obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
    set newFrame : Frame := { frame with varMap := frame.varMap.insert x yfRef } with newFrame_def
    set newRegion : Region := { region with
        objMap := AList.insert yoid (obj.insert yf.field (Reference.RId xrid)) region.objMap } with newRegion_def
    have hsum_eq : ∀ t,
        (Stack.refs (cfg.stack.dropLast ++ [newFrame])).count t + (Heap.refs (cfg.heap.insert rid newRegion)).count t =
        (Stack.refs cfg.stack).count t + (Heap.refs cfg.heap).count t := by
      intro t
      have eq_inner : (Object.refs (obj.insert yf.field (Reference.RId xrid))).count t +
            (if (yfRef == t) = true then 1 else 0) =
          (Object.refs obj).count t + (if ((Reference.RId xrid) == t) = true then 1 else 0) :=
        swap_corollary_alist_insert_count_eq (l := obj) (k := yf.field) (v_old := yfRef)
          (v_new := Reference.RId xrid) (t := t) hfield
      have eq_region : (Region.refs newRegion).count t + (Object.refs obj).count t =
          (Region.refs region).count t + (Object.refs (obj.insert yf.field (Reference.RId xrid))).count t :=
        swap_corollary_objMap_insert_bind_count_eq (m := region.objMap) (oid := yoid)
          (obj := obj) (v := obj.insert yf.field (Reference.RId xrid)) (t := t) hobj
      have eq_heap := swap_corollary_heap_insert_bind_count_eq (cfg := cfg) (rid := rid) (region := region)
        (newRegion := newRegion) (t := t) hregion
      have eq_var := swap_corollary_alist_insert_count_eq (l := frame.varMap) (k := x)
        (v_old := Reference.RId xrid) (v_new := yfRef) (t := t) hxr
      have hframecount : (Frame.refs newFrame).count t =
          (frame.objMap.entries.map (·.2) >>= Object.refs).count t +
          ((frame.varMap.insert x yfRef).entries.map (·.2)).count t := by
        unfold Frame.refs
        rw [newFrame_def, List.count_append]
      have hframecount' : (Frame.refs frame.toFrame).count t =
          (frame.objMap.entries.map (·.2) >>= Object.refs).count t + (frame.varMap.entries.map (·.2)).count t := by
        unfold Frame.refs
        rw [List.count_append]
      have hstackgoal : (Stack.refs (cfg.stack.dropLast ++ [newFrame])).count t =
          (Stack.refs cfg.stack.dropLast).count t + (Frame.refs newFrame).count t := by
        rw [swap_corollary_stack_refs_append, List.count_append]
      have hstackgoal' : (Stack.refs cfg.stack).count t =
          (Stack.refs cfg.stack.dropLast).count t + (Frame.refs frame.toFrame).count t := by
        conv_lhs => rw [stack_eq]
        rw [swap_corollary_stack_refs_append, List.count_append]
      rw [hstackgoal, hstackgoal', hframecount, hframecount']
      omega
    intro rid'
    have h2' := vcfg.h2 rid'
    dsimp
    rw [hsum_eq]
    exact h2'
  · -- SWAP-REGION-BRIDGE: only the heap changes (bridgeObjectId doesn't feed into refs at all),
    -- and both the old and new field values are OId-wrapped -- constructor mismatch closes it
    -- directly for any RId target, no exchange-accounting needed.
    subst hcfg'
    have hfield : obj.lookup yf.field = some yfRef :=
      swap_corollary_region_field_eq_yfRef (hyoid ▸ hyr) (hyoid ▸ hyrloc ▸ hyrl) hregion hobj hyf
    set newRegion : Region := { region with
        bridgeObjectId := yfoid,
        objMap := AList.insert yoid (obj.insert yf.field (Reference.OId region.bridgeObjectId)) region.objMap
      } with newRegion_def
    intro rid'
    have h2' := vcfg.h2 rid'
    dsimp
    have hheap_eq : (Heap.refs (cfg.heap.insert yrid newRegion)).count (Reference.RId rid') =
        (Heap.refs cfg.heap).count (Reference.RId rid') := by
      have eq_inner : (Object.refs (obj.insert yf.field (Reference.OId region.bridgeObjectId))).count
              (Reference.RId rid') + (if (yfRef == Reference.RId rid') = true then 1 else 0) =
          (Object.refs obj).count (Reference.RId rid') +
          (if ((Reference.OId region.bridgeObjectId) == Reference.RId rid') = true then 1 else 0) :=
        swap_corollary_alist_insert_count_eq (l := obj) (k := yf.field) (v_old := yfRef)
          (v_new := Reference.OId region.bridgeObjectId) (t := Reference.RId rid') hfield
      have eq_region : (Region.refs newRegion).count (Reference.RId rid') + (Object.refs obj).count (Reference.RId rid') =
          (Region.refs region).count (Reference.RId rid') +
          (Object.refs (obj.insert yf.field (Reference.OId region.bridgeObjectId))).count (Reference.RId rid') :=
        swap_corollary_objMap_insert_bind_count_eq (m := region.objMap) (oid := yoid)
          (obj := obj) (v := obj.insert yf.field (Reference.OId region.bridgeObjectId)) (t := Reference.RId rid') hobj
      have eq_heap := swap_corollary_heap_insert_bind_count_eq (cfg := cfg) (rid := yrid) (region := region)
        (newRegion := newRegion) (t := Reference.RId rid') hregion
      have hb1 : (yfRef == Reference.RId rid') = false := by rw [hyfoid]; rfl
      have hb2 : ((Reference.OId region.bridgeObjectId) == Reference.RId rid') = false := rfl
      rw [hb1, hb2] at eq_inner
      omega
    rw [hheap_eq]
    exact h2'

-- A List.Perm doesn't change what `.contains` reports (order-independent).
theorem swap_corollary_perm_contains_eq {α : Type*} [BEq α] [LawfulBEq α] {l l' : List α}
    (hperm : l.Perm l') (a : α) : l.contains a = l'.contains a := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]
  exact hperm.mem_iff

-- swap never changes any frame's or region's objMap *key set* (only replaces values at
-- already-present keys, and varMap changes are irrelevant since Reference.loc? never reads
-- varMap at all) -- so `Reference.loc?` transports unconditionally across the mutation for every
-- object id, unlike MakeObjStack/MakeObjRegion which had to exclude a freshly-allocated id. This
-- covers SWAP-STACK: the last frame's varMap can be replaced by anything (`newVarMap`, unused by
-- the proof) since only the objMap-side insert (at the already-present `yoid`) matters.
theorem swap_corollary_stack_loc_eq {cfg : RuntimeConfig} {frame : FrameWithIndex} {yoid : ObjectId}
    {obj : Object} {field : FieldName} {newVal : Reference} {newVarMap : VarMap}
    (hframe : cfg.stackWithIndex.getLast? = some frame) (hobj : frame.objMap.lookup yoid = some obj)
    (oid' : ObjectId) :
    (Reference.OId oid').loc? cfg =
      (Reference.OId oid').loc? { cfg with stack := cfg.stack.dropLast ++
        [({ frame with varMap := newVarMap, objMap := frame.objMap.insert yoid (obj.insert field newVal) } :
          Frame)] } := by
  obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
  set newFrame : Frame :=
    { frame with varMap := newVarMap, objMap := frame.objMap.insert yoid (obj.insert field newVal) } with newFrame_def
  have keys_perm : newFrame.objMap.keys.Perm frame.objMap.keys :=
    swap_corollary_insert_keys_perm (swap_corollary_mem_keys_of_lookup hobj)
  unfold Reference.loc?
  dsimp
  by_cases hb : frame.objMap.keys.contains oid'
  · have hb' : newFrame.objMap.keys.contains oid' := by
      rw [swap_corollary_perm_contains_eq keys_perm]; exact hb
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
      rw [swap_corollary_perm_contains_eq keys_perm]; exact hb
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
-- before cfg''s own validity is established). Mirrors fieldAsgn_corollary_region_unique.
theorem swap_corollary_region_unique
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
-- agree on the *projected* index/rid, not the full FrameWithIndex/heap-entry value.
theorem swap_corollary_loc_match_eq (o1 : Option FrameWithIndex)
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

-- The region-touching branches' `heap.insert` at an already-present key `rid` reorders `entries`;
-- the mutated region's own key set is only Perm-related to the original (`newRegion`'s objMap is
-- an insert at the already-present `yoid`, whatever else about `newRegion` differs -- e.g.
-- SWAP-REGION-BRIDGE also changes `bridgeObjectId`, which `Reference.loc?` never reads).
theorem swap_corollary_region_loc_eq {cfg : RuntimeConfig} {rid yoid : ObjectId} {region newRegion : Region}
    {obj v : Object} (vcfg : ValidConfig cfg)
    (hregion : cfg.heap.lookup rid = some region) (hobj : region.objMap.lookup yoid = some obj)
    (hnewRegion : newRegion.objMap = region.objMap.insert yoid v)
    (oid' : ObjectId) :
    (Reference.OId oid').loc? cfg =
      (Reference.OId oid').loc? { cfg with heap := cfg.heap.insert rid newRegion } := by
  have l1 := vcfg.l1
  have keys_perm : newRegion.objMap.keys.Perm region.objMap.keys := by
    rw [hnewRegion]
    exact swap_corollary_insert_keys_perm (swap_corollary_mem_keys_of_lookup hobj)
  unfold Reference.loc?
  dsimp
  have heap_h2_map_eq :
      (cfg.heap.entries.find? (fun p => p.snd.objMap.keys.contains oid')).map Sigma.fst =
      ((AList.insert rid newRegion cfg.heap).entries.find?
        (fun p => p.snd.objMap.keys.contains oid')).map Sigma.fst := by
    obtain ⟨region2, l1e, l2e, hnotmem, heq, hkerase⟩ :=
      List.exists_of_kerase (swap_corollary_mem_keys_of_lookup hregion)
    have region2_eq : region2 = region :=
      List.NodupKeys.eq_of_mk_mem cfg.heap.nodupKeys
        (heq ▸ List.mem_append_right _ List.mem_cons_self) (AList.mem_lookup_iff.mp (by rw [hregion]; rfl))
    rw [region2_eq] at heq
    rw [AList.entries_insert, hkerase]
    have region_mem_cfg : (⟨rid, region⟩ : Sigma (fun _ : RegionId => Region)) ∈ cfg.heap.entries :=
      heq ▸ List.mem_append_right _ List.mem_cons_self
    by_cases hb2 : region.objMap.keys.contains oid'
    · have hb2' : newRegion.objMap.keys.contains oid' := by
        rw [swap_corollary_perm_contains_eq keys_perm]; exact hb2
      have find_eqR2 :
          List.find? (fun p => p.snd.objMap.keys.contains oid')
            ((⟨rid, newRegion⟩ : Sigma (fun _ : RegionId => Region)) :: (l1e ++ l2e)) =
          some (⟨rid, newRegion⟩ : Sigma (fun _ : RegionId => Region)) :=
        List.find?_cons_of_pos hb2'
      rw [find_eqR2]
      have find_eqL :
          cfg.heap.entries.find? (fun p => p.snd.objMap.keys.contains oid') =
          some (⟨rid, region⟩ : Sigma (fun _ : RegionId => Region)) := by
        apply List.find?_eq_some_of_unique region_mem_cfg hb2
        intro y hy hpy
        obtain ⟨rid_y, region_y⟩ := y
        have rid_y_eq : rid_y = rid :=
          swap_corollary_region_unique l1 hy (List.contains_iff_mem.mp hpy)
            region_mem_cfg (List.contains_iff_mem.mp hb2)
        subst rid_y_eq
        have region_y_eq : region_y = region :=
          List.NodupKeys.eq_of_mk_mem cfg.heap.nodupKeys hy region_mem_cfg
        rw [region_y_eq]
      rw [find_eqL]
      rfl
    · have hb2' : ¬ newRegion.objMap.keys.contains oid' := by
        rw [swap_corollary_perm_contains_eq keys_perm]; exact hb2
      have find_eqR2 :
          List.find? (fun p => p.snd.objMap.keys.contains oid')
            ((⟨rid, newRegion⟩ : Sigma (fun _ : RegionId => Region)) :: (l1e ++ l2e)) =
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
  have step1 := swap_corollary_loc_match_eq
    (cfg.stackWithIndex.findRev? (fun f => f.objMap.keys.contains oid'))
    (cfg.heap.entries.find? (fun p => p.snd.objMap.keys.contains oid'))
  have step2 := swap_corollary_loc_match_eq
    (cfg.stackWithIndex.findRev? (fun f => f.objMap.keys.contains oid'))
    ((AList.insert rid newRegion cfg.heap).entries.find? (fun p => p.snd.objMap.keys.contains oid'))
  rw [heap_h2_map_eq] at step1
  exact step1.trans step2.symm

-- A varMap-only change to the last frame never affects Reference.loc? at all -- unlike
-- swap_corollary_stack_loc_eq (which handles a *combined* varMap+objMap change), this needs no
-- Perm/uniqueness argument at all since the objMap key set is *literally* unchanged, not just
-- Perm-equal. Generic over any RuntimeConfig (any heap), so it composes with a heap-side
-- transport already performed on a possibly-different heap.
theorem swap_corollary_stack_varmap_loc_eq {cfg : RuntimeConfig} {frame : FrameWithIndex} {newVarMap : VarMap}
    (hframe : cfg.stackWithIndex.getLast? = some frame) (oid' : ObjectId) :
    (Reference.OId oid').loc? cfg =
      (Reference.OId oid').loc? { cfg with stack := cfg.stack.dropLast ++
        [({ frame with varMap := newVarMap } : Frame)] } := by
  obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
  set newFrame : Frame := { frame with varMap := newVarMap } with newFrame_def
  have hobjMap_eq : newFrame.objMap = frame.objMap := by rw [newFrame_def]
  unfold Reference.loc?
  dsimp
  by_cases hb : frame.objMap.keys.contains oid'
  · have hb' : newFrame.objMap.keys.contains oid' := by rw [hobjMap_eq]; exact hb
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
  · have hb' : ¬ newFrame.objMap.keys.contains oid' := by rw [hobjMap_eq]; exact hb
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

theorem swap_H3 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  H3 cfg' := by
  intro vcfg h
  have h3 := vcfg.h3
  obtain ⟨frame, hframe, yRef, hyr, yRefLoc, hyrl, yfRef, hyf, yfRefLoc, hyfl, hcase⟩ := swap_cases h
  unfold H3
  rcases hcase with
    ⟨yoid, xRef, obj, hxb, hyoid, hyrloc, hxr, hobj, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xoid, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hxrl, hxrid, hstatus, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hstatus, hcfg'⟩ |
    ⟨yoid, yrid, yfoid, yfrid, region, obj, hxb, hyoid, hyrloc, hyfoid, hyfrloc, hyrid, hyfrid, hregion, hobj, hcfg'⟩
  · subst hcfg'
    have loc_eq := swap_corollary_stack_loc_eq (field := yf.field) (newVal := xRef)
      (newVarMap := frame.varMap.insert x yfRef) hframe hobj
    intro rid0 oid0 region0 hlookup0 href0
    dsimp at hlookup0
    have h3fact := h3 rid0 oid0 region0 hlookup0 href0
    rw [← loc_eq]
    exact h3fact
  · subst hcfg'
    set newRegion : Region :=
      { region with objMap := AList.insert yoid (obj.insert yf.field (Reference.OId xoid)) region.objMap }
      with newRegion_def
    have loc_eq_heap := swap_corollary_region_loc_eq (region := region) (newRegion := newRegion)
      (obj := obj) (v := obj.insert yf.field (Reference.OId xoid)) vcfg hregion hobj rfl
    have loc_eq_stack := swap_corollary_stack_varmap_loc_eq
      (cfg := { cfg with heap := cfg.heap.insert rid newRegion })
      (newVarMap := frame.varMap.insert x yfRef) hframe
    have loc_eq : ∀ oid', (Reference.OId oid').loc? cfg =
        (Reference.OId oid').loc? { cfg with
          stack := cfg.stack.dropLast ++ [({ frame with varMap := frame.varMap.insert x yfRef } : Frame)],
          heap := cfg.heap.insert rid newRegion } :=
      fun oid' => (loc_eq_heap oid').trans (loc_eq_stack oid')
    intro rid0 oid0 region0 hlookup0 href0
    dsimp at hlookup0
    by_cases hrideq : rid0 = rid
    · subst hrideq
      rw [AList.lookup_insert, Option.some_inj] at hlookup0
      subst hlookup0
      rcases swap_corollary_objMap_insert_bind_refs_mem
        (show Reference.OId oid0 ∈ (region.objMap.insert yoid (obj.insert yf.field (Reference.OId xoid))).entries.map (·.2) >>= Object.refs from href0)
        with heq | horig
      · rcases swap_corollary_alist_insert_refs_mem
          (show Reference.OId oid0 ∈ (obj.insert yf.field (Reference.OId xoid)).entries.map (·.2) from heq)
          with heq2 | horig2
        · rw [Reference.OId.injEq] at heq2
          rw [heq2, ← loc_eq]
          rw [← hxrid.trans hrid.symm]
          exact hxrl
        · have h3fact := h3 rid0 oid0 region hregion
            (swap_corollary_objMap_bind_refs_mem_of_lookup hobj horig2)
          rw [← loc_eq]
          exact h3fact
      · have h3fact := h3 rid0 oid0 region hregion horig
        rw [← loc_eq]
        exact h3fact
    · rw [AList.lookup_insert_ne hrideq] at hlookup0
      have h3fact := h3 rid0 oid0 region0 hlookup0 href0
      rw [← loc_eq]
      exact h3fact
  · subst hcfg'
    set newRegion : Region :=
      { region with objMap := AList.insert yoid (obj.insert yf.field (Reference.RId xrid)) region.objMap }
      with newRegion_def
    have loc_eq_heap := swap_corollary_region_loc_eq (region := region) (newRegion := newRegion)
      (obj := obj) (v := obj.insert yf.field (Reference.RId xrid)) vcfg hregion hobj rfl
    have loc_eq_stack := swap_corollary_stack_varmap_loc_eq
      (cfg := { cfg with heap := cfg.heap.insert rid newRegion })
      (newVarMap := frame.varMap.insert x yfRef) hframe
    have loc_eq : ∀ oid', (Reference.OId oid').loc? cfg =
        (Reference.OId oid').loc? { cfg with
          stack := cfg.stack.dropLast ++ [({ frame with varMap := frame.varMap.insert x yfRef } : Frame)],
          heap := cfg.heap.insert rid newRegion } :=
      fun oid' => (loc_eq_heap oid').trans (loc_eq_stack oid')
    intro rid0 oid0 region0 hlookup0 href0
    dsimp at hlookup0
    by_cases hrideq : rid0 = rid
    · subst hrideq
      rw [AList.lookup_insert, Option.some_inj] at hlookup0
      subst hlookup0
      rcases swap_corollary_objMap_insert_bind_refs_mem
        (show Reference.OId oid0 ∈ (region.objMap.insert yoid (obj.insert yf.field (Reference.RId xrid))).entries.map (·.2) >>= Object.refs from href0)
        with heq | horig
      · rcases swap_corollary_alist_insert_refs_mem
          (show Reference.OId oid0 ∈ (obj.insert yf.field (Reference.RId xrid)).entries.map (·.2) from heq)
          with heq2 | horig2
        · exact absurd heq2 (by simp)
        · have h3fact := h3 rid0 oid0 region hregion
            (swap_corollary_objMap_bind_refs_mem_of_lookup hobj horig2)
          rw [← loc_eq]
          exact h3fact
      · have h3fact := h3 rid0 oid0 region hregion horig
        rw [← loc_eq]
        exact h3fact
    · rw [AList.lookup_insert_ne hrideq] at hlookup0
      have h3fact := h3 rid0 oid0 region0 hlookup0 href0
      rw [← loc_eq]
      exact h3fact
  · subst hcfg'
    have h1 := vcfg.h1
    have region_mem : region ∈ cfg.heap.regions := by
      unfold Heap.regions
      exact List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hregion)
    have hbridge_mem : region.bridgeObjectId ∈ region.objMap := h1 region region_mem
    set newRegion : Region := { region with
        bridgeObjectId := yfoid,
        objMap := AList.insert yoid (obj.insert yf.field (Reference.OId region.bridgeObjectId)) region.objMap
      } with newRegion_def
    have loc_eq := swap_corollary_region_loc_eq (region := region) (newRegion := newRegion)
      (obj := obj) (v := obj.insert yf.field (Reference.OId region.bridgeObjectId)) vcfg hregion hobj rfl
    intro rid0 oid0 region0 hlookup0 href0
    dsimp at hlookup0
    by_cases hrideq : rid0 = yrid
    · subst hrideq
      rw [AList.lookup_insert, Option.some_inj] at hlookup0
      subst hlookup0
      rcases swap_corollary_objMap_insert_bind_refs_mem
        (show Reference.OId oid0 ∈
          (region.objMap.insert yoid (obj.insert yf.field (Reference.OId region.bridgeObjectId))).entries.map (·.2) >>=
            Object.refs from href0)
        with heq | horig
      · rcases swap_corollary_alist_insert_refs_mem
          (show Reference.OId oid0 ∈ (obj.insert yf.field (Reference.OId region.bridgeObjectId)).entries.map (·.2)
            from heq)
          with heq2 | horig2
        · rw [Reference.OId.injEq] at heq2
          rw [heq2, ← loc_eq]
          exact (oid_loc_rgn_iff_in_heap vcfg).mpr ⟨region, hregion, hbridge_mem⟩
        · have h3fact := h3 rid0 oid0 region hregion
            (swap_corollary_objMap_bind_refs_mem_of_lookup hobj horig2)
          rw [← loc_eq]
          exact h3fact
      · have h3fact := h3 rid0 oid0 region hregion horig
        rw [← loc_eq]
        exact h3fact
    · rw [AList.lookup_insert_ne hrideq] at hlookup0
      have h3fact := h3 rid0 oid0 region0 hlookup0 href0
      rw [← loc_eq]
      exact h3fact

theorem swap_S2 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  S2 cfg' := by
  intro vcfg h
  have s2 := vcfg.s2
  obtain ⟨frame, hframe, yRef, hyr, yRefLoc, hyrl, yfRef, hyf, yfRefLoc, hyfl, hcase⟩ := swap_cases h
  have frame_mem : frame ∈ cfg.stackWithIndex := List.mem_of_getLast? hframe
  unfold S2
  rcases hcase with
    ⟨yoid, xRef, obj, hxb, hyoid, hyrloc, hxr, hobj, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xoid, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hxrl, hxrid, hstatus, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hstatus, hcfg'⟩ |
    ⟨yoid, yrid, yfoid, yfrid, region, obj, hxb, hyoid, hyrloc, hyfoid, hyfrloc, hyrid, hyfrid, hregion, hobj, hcfg'⟩
  · -- SWAP-STACK
    subst hcfg'
    have hfield : obj.lookup yf.field = some yfRef :=
      swap_corollary_stack_field_eq_yfRef frame_mem (hyoid ▸ hyr) (hyoid ▸ hyrloc ▸ hyrl) hobj hyf
    obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
    set newFrame : Frame := { frame with
        varMap := frame.varMap.insert x yfRef,
        objMap := frame.objMap.insert yoid (obj.insert yf.field xRef) } with newFrame_def
    have loc_eq := swap_corollary_stack_loc_eq (field := yf.field) (newVal := xRef)
      (newVarMap := frame.varMap.insert x yfRef) hframe hobj
    have stackWithIndex_eq_cfg : cfg.stackWithIndex =
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
    have hframe_mem_cfg : ({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex) ∈ cfg.stackWithIndex := by
      rw [stackWithIndex_eq_cfg]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    have hnewindex_bound : ∀ fid' oid0, (Reference.OId oid0).loc? cfg = some (Location.Stk fid') →
        fid' ≤ ({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex).index := by
      intro fid' oid0 hlocEq_cfg
      obtain ⟨frameW, hlookupW, _⟩ := (oid_loc_stk_iff_in_stack vcfg).mp hlocEq_cfg
      have hlt := (List.getElem?_eq_some_iff.mp hlookupW).1
      have hlen : cfg.stackWithIndex.length = cfg.stack.dropLast.length + 1 := by
        unfold RuntimeConfig.stackWithIndex
        rw [List.length_mapIdx, hstacklen]
      rw [hlen] at hlt
      dsimp
      exact Nat.le_of_lt_succ hlt
    intro frame' hframe' ref href fid' oid0 hrefeq hlocEq
    subst hrefeq
    rw [stackWithIndex_eq, List.mem_append, List.mem_singleton] at hframe'
    rcases hframe' with hold | hnew
    · have hframe'_in_cfg : frame' ∈ cfg.stackWithIndex := by
        rw [stackWithIndex_eq_cfg]; exact List.mem_append_left _ hold
      have hlocEq_cfg : (Reference.OId oid0).loc? cfg = some (Location.Stk fid') := by
        rw [loc_eq]; exact hlocEq
      exact s2 frame' hframe'_in_cfg (Reference.OId oid0) href fid' oid0 rfl hlocEq_cfg
    · subst hnew
      dsimp at href
      have hlocEq_cfg : (Reference.OId oid0).loc? cfg = some (Location.Stk fid') := by
        rw [loc_eq]; exact hlocEq
      unfold Frame.refs at href
      dsimp at href
      rw [List.mem_append] at href
      rcases href with href | href
      · rcases swap_corollary_objMap_insert_bind_refs_mem href with heq | horig
        · rcases swap_corollary_alist_insert_refs_mem heq with heq2 | horig2
          · exact hnewindex_bound fid' oid0 hlocEq_cfg
          · have horig' : Reference.OId oid0 ∈ frame.refs := by
              unfold Frame.refs
              exact List.mem_append_left _ (swap_corollary_objMap_bind_refs_mem_of_lookup hobj horig2)
            exact s2 _ hframe_mem_cfg (Reference.OId oid0) horig' fid' oid0 rfl hlocEq_cfg
        · have horig' : Reference.OId oid0 ∈ frame.refs := by
            unfold Frame.refs
            exact List.mem_append_left _ horig
          exact s2 _ hframe_mem_cfg (Reference.OId oid0) horig' fid' oid0 rfl hlocEq_cfg
      · rcases swap_corollary_alist_insert_refs_mem href with heq | horig
        · exact hnewindex_bound fid' oid0 hlocEq_cfg
        · have horig' : Reference.OId oid0 ∈ frame.refs := by
            unfold Frame.refs
            exact List.mem_append_right _ horig
          exact s2 _ hframe_mem_cfg (Reference.OId oid0) horig' fid' oid0 rfl hlocEq_cfg
  · -- SWAP-REGION-OBJECT
    subst hcfg'
    have hfield : obj.lookup yf.field = some yfRef :=
      swap_corollary_region_field_eq_yfRef (hyoid ▸ hyr) (hyoid ▸ hyrloc ▸ hyrl) hregion hobj hyf
    obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
    set newRegion : Region :=
      { region with objMap := AList.insert yoid (obj.insert yf.field (Reference.OId xoid)) region.objMap }
      with newRegion_def
    have loc_eq_heap := swap_corollary_region_loc_eq (region := region) (newRegion := newRegion)
      (obj := obj) (v := obj.insert yf.field (Reference.OId xoid)) vcfg hregion hobj rfl
    have loc_eq_stack := swap_corollary_stack_varmap_loc_eq
      (cfg := { cfg with heap := cfg.heap.insert rid newRegion })
      (newVarMap := frame.varMap.insert x yfRef) hframe
    have loc_eq : ∀ oid', (Reference.OId oid').loc? cfg =
        (Reference.OId oid').loc? { cfg with
          stack := cfg.stack.dropLast ++ [({ frame with varMap := frame.varMap.insert x yfRef } : Frame)],
          heap := cfg.heap.insert rid newRegion } :=
      fun oid' => (loc_eq_heap oid').trans (loc_eq_stack oid')
    set newFrame : Frame := { frame with varMap := frame.varMap.insert x yfRef } with newFrame_def
    have stackWithIndex_eq_cfg : cfg.stackWithIndex =
        cfg.stack.dropLast.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) ++
          [({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex)] := by
      unfold RuntimeConfig.stackWithIndex
      conv_lhs => rw [stack_eq]
      rw [List.mapIdx_concat]
    have stackWithIndex_eq :
        (RuntimeConfig.stackWithIndex
          { stack := cfg.stack.dropLast ++ [newFrame], heap := cfg.heap.insert rid newRegion }) =
          cfg.stack.dropLast.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) ++
            [({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex)] := by
      unfold RuntimeConfig.stackWithIndex
      dsimp
      rw [List.mapIdx_concat]
    have hstacklen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by
      conv_lhs => rw [stack_eq]
      rw [List.length_append, List.length_singleton]
    have hframe_mem_cfg : ({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex) ∈ cfg.stackWithIndex := by
      rw [stackWithIndex_eq_cfg]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    have hnewindex_bound : ∀ fid' oid0, (Reference.OId oid0).loc? cfg = some (Location.Stk fid') →
        fid' ≤ ({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex).index := by
      intro fid' oid0 hlocEq_cfg
      obtain ⟨frameW, hlookupW, _⟩ := (oid_loc_stk_iff_in_stack vcfg).mp hlocEq_cfg
      have hlt := (List.getElem?_eq_some_iff.mp hlookupW).1
      have hlen : cfg.stackWithIndex.length = cfg.stack.dropLast.length + 1 := by
        unfold RuntimeConfig.stackWithIndex
        rw [List.length_mapIdx, hstacklen]
      rw [hlen] at hlt
      dsimp
      exact Nat.le_of_lt_succ hlt
    intro frame' hframe' ref href fid' oid0 hrefeq hlocEq
    subst hrefeq
    rw [stackWithIndex_eq, List.mem_append, List.mem_singleton] at hframe'
    rcases hframe' with hold | hnew
    · have hframe'_in_cfg : frame' ∈ cfg.stackWithIndex := by
        rw [stackWithIndex_eq_cfg]; exact List.mem_append_left _ hold
      have hlocEq_cfg : (Reference.OId oid0).loc? cfg = some (Location.Stk fid') := by
        rw [loc_eq]; exact hlocEq
      exact s2 frame' hframe'_in_cfg (Reference.OId oid0) href fid' oid0 rfl hlocEq_cfg
    · subst hnew
      dsimp at href
      have hlocEq_cfg : (Reference.OId oid0).loc? cfg = some (Location.Stk fid') := by
        rw [loc_eq]; exact hlocEq
      unfold Frame.refs at href
      dsimp at href
      rw [List.mem_append] at href
      rcases href with href | href
      · have horig' : Reference.OId oid0 ∈ frame.refs := by
          unfold Frame.refs
          exact List.mem_append_left _ href
        exact s2 _ hframe_mem_cfg (Reference.OId oid0) horig' fid' oid0 rfl hlocEq_cfg
      · rcases swap_corollary_alist_insert_refs_mem href with heq | horig
        · exact hnewindex_bound fid' oid0 hlocEq_cfg
        · have horig' : Reference.OId oid0 ∈ frame.refs := by
            unfold Frame.refs
            exact List.mem_append_right _ horig
          exact s2 _ hframe_mem_cfg (Reference.OId oid0) horig' fid' oid0 rfl hlocEq_cfg
  · -- SWAP-REGION-REGION: identical shape to SWAP-REGION-OBJECT
    subst hcfg'
    have hfield : obj.lookup yf.field = some yfRef :=
      swap_corollary_region_field_eq_yfRef (hyoid ▸ hyr) (hyoid ▸ hyrloc ▸ hyrl) hregion hobj hyf
    obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
    set newRegion : Region :=
      { region with objMap := AList.insert yoid (obj.insert yf.field (Reference.RId xrid)) region.objMap }
      with newRegion_def
    have loc_eq_heap := swap_corollary_region_loc_eq (region := region) (newRegion := newRegion)
      (obj := obj) (v := obj.insert yf.field (Reference.RId xrid)) vcfg hregion hobj rfl
    have loc_eq_stack := swap_corollary_stack_varmap_loc_eq
      (cfg := { cfg with heap := cfg.heap.insert rid newRegion })
      (newVarMap := frame.varMap.insert x yfRef) hframe
    have loc_eq : ∀ oid', (Reference.OId oid').loc? cfg =
        (Reference.OId oid').loc? { cfg with
          stack := cfg.stack.dropLast ++ [({ frame with varMap := frame.varMap.insert x yfRef } : Frame)],
          heap := cfg.heap.insert rid newRegion } :=
      fun oid' => (loc_eq_heap oid').trans (loc_eq_stack oid')
    set newFrame : Frame := { frame with varMap := frame.varMap.insert x yfRef } with newFrame_def
    have stackWithIndex_eq_cfg : cfg.stackWithIndex =
        cfg.stack.dropLast.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) ++
          [({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex)] := by
      unfold RuntimeConfig.stackWithIndex
      conv_lhs => rw [stack_eq]
      rw [List.mapIdx_concat]
    have stackWithIndex_eq :
        (RuntimeConfig.stackWithIndex
          { stack := cfg.stack.dropLast ++ [newFrame], heap := cfg.heap.insert rid newRegion }) =
          cfg.stack.dropLast.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) ++
            [({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex)] := by
      unfold RuntimeConfig.stackWithIndex
      dsimp
      rw [List.mapIdx_concat]
    have hstacklen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by
      conv_lhs => rw [stack_eq]
      rw [List.length_append, List.length_singleton]
    have hframe_mem_cfg : ({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex) ∈ cfg.stackWithIndex := by
      rw [stackWithIndex_eq_cfg]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    have hnewindex_bound : ∀ fid' oid0, (Reference.OId oid0).loc? cfg = some (Location.Stk fid') →
        fid' ≤ ({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex).index := by
      intro fid' oid0 hlocEq_cfg
      obtain ⟨frameW, hlookupW, _⟩ := (oid_loc_stk_iff_in_stack vcfg).mp hlocEq_cfg
      have hlt := (List.getElem?_eq_some_iff.mp hlookupW).1
      have hlen : cfg.stackWithIndex.length = cfg.stack.dropLast.length + 1 := by
        unfold RuntimeConfig.stackWithIndex
        rw [List.length_mapIdx, hstacklen]
      rw [hlen] at hlt
      dsimp
      exact Nat.le_of_lt_succ hlt
    intro frame' hframe' ref href fid' oid0 hrefeq hlocEq
    subst hrefeq
    rw [stackWithIndex_eq, List.mem_append, List.mem_singleton] at hframe'
    rcases hframe' with hold | hnew
    · have hframe'_in_cfg : frame' ∈ cfg.stackWithIndex := by
        rw [stackWithIndex_eq_cfg]; exact List.mem_append_left _ hold
      have hlocEq_cfg : (Reference.OId oid0).loc? cfg = some (Location.Stk fid') := by
        rw [loc_eq]; exact hlocEq
      exact s2 frame' hframe'_in_cfg (Reference.OId oid0) href fid' oid0 rfl hlocEq_cfg
    · subst hnew
      dsimp at href
      have hlocEq_cfg : (Reference.OId oid0).loc? cfg = some (Location.Stk fid') := by
        rw [loc_eq]; exact hlocEq
      unfold Frame.refs at href
      dsimp at href
      rw [List.mem_append] at href
      rcases href with href | href
      · have horig' : Reference.OId oid0 ∈ frame.refs := by
          unfold Frame.refs
          exact List.mem_append_left _ href
        exact s2 _ hframe_mem_cfg (Reference.OId oid0) horig' fid' oid0 rfl hlocEq_cfg
      · rcases swap_corollary_alist_insert_refs_mem href with heq | horig
        · exact hnewindex_bound fid' oid0 hlocEq_cfg
        · have horig' : Reference.OId oid0 ∈ frame.refs := by
            unfold Frame.refs
            exact List.mem_append_right _ horig
          exact s2 _ hframe_mem_cfg (Reference.OId oid0) horig' fid' oid0 rfl hlocEq_cfg
  · -- SWAP-REGION-BRIDGE: stack untouched, so this is a direct transport, no stack case-split
    subst hcfg'
    have hfield : obj.lookup yf.field = some yfRef :=
      swap_corollary_region_field_eq_yfRef (hyoid ▸ hyr) (hyoid ▸ hyrloc ▸ hyrl) hregion hobj hyf
    set newRegion : Region := { region with
        bridgeObjectId := yfoid,
        objMap := AList.insert yoid (obj.insert yf.field (Reference.OId region.bridgeObjectId)) region.objMap
      } with newRegion_def
    have loc_eq := swap_corollary_region_loc_eq (region := region) (newRegion := newRegion)
      (obj := obj) (v := obj.insert yf.field (Reference.OId region.bridgeObjectId)) vcfg hregion hobj rfl
    intro frame' hframe' ref href fid' oid0 hrefeq hlocEq
    subst hrefeq
    have hlocEq_cfg : (Reference.OId oid0).loc? cfg = some (Location.Stk fid') := by
      rw [loc_eq]; exact hlocEq
    exact s2 frame' hframe' (Reference.OId oid0) href fid' oid0 rfl hlocEq_cfg

theorem swap_S3 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  S3 cfg' := by
  intro vcfg h
  have s3 := vcfg.s3
  obtain ⟨frame, hframe, yRef, hyr, yRefLoc, hyrl, yfRef, hyf, yfRefLoc, hyfl, hcase⟩ := swap_cases h
  have frame_mem : frame ∈ cfg.stackWithIndex := List.mem_of_getLast? hframe
  unfold S3
  rcases hcase with
    ⟨yoid, xRef, obj, hxb, hyoid, hyrloc, hxr, hobj, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xoid, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hxrl, hxrid, hstatus, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hstatus, hcfg'⟩ |
    ⟨yoid, yrid, yfoid, yfrid, region, obj, hxb, hyoid, hyrloc, hyfoid, hyfrloc, hyrid, hyfrid, hregion, hobj, hcfg'⟩
  · -- SWAP-STACK: a same-frame exchange -- every value in the mutated frame was already in
    -- frame.refs before, so self-reference (s3 applied to `frame` itself) always suffices.
    subst hcfg'
    have hfield : obj.lookup yf.field = some yfRef :=
      swap_corollary_stack_field_eq_yfRef frame_mem (hyoid ▸ hyr) (hyoid ▸ hyrloc ▸ hyrl) hobj hyf
    obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
    set newFrame : Frame := { frame with
        varMap := frame.varMap.insert x yfRef,
        objMap := frame.objMap.insert yoid (obj.insert yf.field xRef) } with newFrame_def
    have loc_eq := swap_corollary_stack_loc_eq (field := yf.field) (newVal := xRef)
      (newVarMap := frame.varMap.insert x yfRef) hframe hobj
    have stackWithIndex_eq_cfg : cfg.stackWithIndex =
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
    have transport : ∀ f ∈ cfg.stackWithIndex,
        ∃ g ∈ (RuntimeConfig.stackWithIndex { stack := cfg.stack.dropLast ++ [newFrame], heap := cfg.heap }),
          g.regionId = f.regionId ∧ g.index = f.index := by
      intro f hf
      rw [stackWithIndex_eq_cfg, List.mem_append, List.mem_singleton] at hf
      rcases hf with hf | hf
      · exact ⟨f, stackWithIndex_eq ▸ List.mem_append_left _ hf, rfl, rfl⟩
      · subst hf
        exact ⟨({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex),
          stackWithIndex_eq ▸ List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl⟩
    have hxRef_mem_frame : xRef ∈ frame.refs := by
      unfold Frame.refs
      exact List.mem_append_right _ (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hxr))
    have hyfRef_mem_frame : yfRef ∈ frame.refs := by
      unfold Frame.refs
      apply List.mem_append_left
      exact swap_corollary_objMap_bind_refs_mem_of_lookup hobj
        (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hfield))
    intro frame' hframe' ref href rid' oid0 hrefeq hlocEq
    subst hrefeq
    rw [stackWithIndex_eq, List.mem_append, List.mem_singleton] at hframe'
    rcases hframe' with hold | hnew
    · have hframe'_in_cfg : frame' ∈ cfg.stackWithIndex := by
        rw [stackWithIndex_eq_cfg]; exact List.mem_append_left _ hold
      have hlocEq_cfg : (Reference.OId oid0).loc? cfg = some (Location.Rgn rid') := by
        rw [loc_eq]; exact hlocEq
      obtain ⟨anc, hanc_mem, hanc_rid, hanc_idx⟩ :=
        s3 frame' hframe'_in_cfg (Reference.OId oid0) href rid' oid0 rfl hlocEq_cfg
      obtain ⟨anc', hanc'_mem, hanc'_rid, hanc'_idx⟩ := transport anc hanc_mem
      exact ⟨anc', hanc'_mem, hanc'_rid.trans hanc_rid, hanc'_idx ▸ hanc_idx⟩
    · subst hnew
      dsimp at href
      have hlocEq_cfg : (Reference.OId oid0).loc? cfg = some (Location.Rgn rid') := by
        rw [loc_eq]; exact hlocEq
      have href' : Reference.OId oid0 ∈ frame.refs := by
        unfold Frame.refs at href
        dsimp at href
        rw [List.mem_append] at href
        rcases href with href | href
        · rcases swap_corollary_objMap_insert_bind_refs_mem href with heq | horig
          · rcases swap_corollary_alist_insert_refs_mem heq with heq2 | horig2
            · exact heq2 ▸ hxRef_mem_frame
            · unfold Frame.refs
              exact List.mem_append_left _ (swap_corollary_objMap_bind_refs_mem_of_lookup hobj horig2)
          · unfold Frame.refs
            exact List.mem_append_left _ horig
        · rcases swap_corollary_alist_insert_refs_mem href with heq | horig
          · exact heq ▸ hyfRef_mem_frame
          · unfold Frame.refs
            exact List.mem_append_right _ horig
      obtain ⟨anc, hanc_mem, hanc_rid, hanc_idx⟩ :=
        s3 frame frame_mem (Reference.OId oid0) href' rid' oid0 rfl hlocEq_cfg
      obtain ⟨anc', hanc'_mem, hanc'_rid, hanc'_idx⟩ := transport anc hanc_mem
      have hframe_idx : frame.index = cfg.stack.dropLast.length := (swap_corollary_stack_eq hframe).2
      refine ⟨anc', hanc'_mem, hanc'_rid.trans hanc_rid, ?_⟩
      dsimp
      rw [hanc'_idx, ← hframe_idx]
      exact hanc_idx
  · -- SWAP-REGION-OBJECT: the touched region IS the current frame's own region (hrid : rid =
    -- frame.regionId), so any region-internal ref (yfRef) already has `frame` itself as a valid
    -- ancestor -- no resolveV/resolveFA provenance-tracing needed, unlike FieldAsgn/VarAsgn's S3.
    subst hcfg'
    have h3 := vcfg.h3
    have hfield : obj.lookup yf.field = some yfRef :=
      swap_corollary_region_field_eq_yfRef (hyoid ▸ hyr) (hyoid ▸ hyrloc ▸ hyrl) hregion hobj hyf
    have hyfRef_mem_region : yfRef ∈ region.refs :=
      swap_corollary_objMap_bind_refs_mem_of_lookup hobj
        (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hfield))
    obtain ⟨stack_eq, hframe_idx⟩ := swap_corollary_stack_eq hframe
    set newRegion : Region :=
      { region with objMap := AList.insert yoid (obj.insert yf.field (Reference.OId xoid)) region.objMap }
      with newRegion_def
    have loc_eq_heap := swap_corollary_region_loc_eq (region := region) (newRegion := newRegion)
      (obj := obj) (v := obj.insert yf.field (Reference.OId xoid)) vcfg hregion hobj rfl
    have loc_eq_stack := swap_corollary_stack_varmap_loc_eq
      (cfg := { cfg with heap := cfg.heap.insert rid newRegion })
      (newVarMap := frame.varMap.insert x yfRef) hframe
    have loc_eq : ∀ oid', (Reference.OId oid').loc? cfg =
        (Reference.OId oid').loc? { cfg with
          stack := cfg.stack.dropLast ++ [({ frame with varMap := frame.varMap.insert x yfRef } : Frame)],
          heap := cfg.heap.insert rid newRegion } :=
      fun oid' => (loc_eq_heap oid').trans (loc_eq_stack oid')
    set newFrame : Frame := { frame with varMap := frame.varMap.insert x yfRef } with newFrame_def
    have stackWithIndex_eq_cfg : cfg.stackWithIndex =
        cfg.stack.dropLast.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) ++
          [({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex)] := by
      unfold RuntimeConfig.stackWithIndex
      conv_lhs => rw [stack_eq]
      rw [List.mapIdx_concat]
    have stackWithIndex_eq :
        (RuntimeConfig.stackWithIndex
          { stack := cfg.stack.dropLast ++ [newFrame], heap := cfg.heap.insert rid newRegion }) =
          cfg.stack.dropLast.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) ++
            [({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex)] := by
      unfold RuntimeConfig.stackWithIndex
      dsimp
      rw [List.mapIdx_concat]
    have transport : ∀ f ∈ cfg.stackWithIndex,
        ∃ g ∈ (RuntimeConfig.stackWithIndex
          { stack := cfg.stack.dropLast ++ [newFrame], heap := cfg.heap.insert rid newRegion }),
          g.regionId = f.regionId ∧ g.index = f.index := by
      intro f hf
      rw [stackWithIndex_eq_cfg, List.mem_append, List.mem_singleton] at hf
      rcases hf with hf | hf
      · exact ⟨f, stackWithIndex_eq ▸ List.mem_append_left _ hf, rfl, rfl⟩
      · subst hf
        exact ⟨({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex),
          stackWithIndex_eq ▸ List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl⟩
    have hframe_mem_cfg : ({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex) ∈
        (RuntimeConfig.stackWithIndex
          { stack := cfg.stack.dropLast ++ [newFrame], heap := cfg.heap.insert rid newRegion }) := by
      rw [stackWithIndex_eq]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    intro frame' hframe' ref href rid' oid0 hrefeq hlocEq
    subst hrefeq
    rw [stackWithIndex_eq, List.mem_append, List.mem_singleton] at hframe'
    rcases hframe' with hold | hnew
    · have hframe'_in_cfg : frame' ∈ cfg.stackWithIndex := by
        rw [stackWithIndex_eq_cfg]; exact List.mem_append_left _ hold
      have hlocEq_cfg : (Reference.OId oid0).loc? cfg = some (Location.Rgn rid') := by
        rw [loc_eq]; exact hlocEq
      obtain ⟨anc, hanc_mem, hanc_rid, hanc_idx⟩ :=
        s3 frame' hframe'_in_cfg (Reference.OId oid0) href rid' oid0 rfl hlocEq_cfg
      obtain ⟨anc', hanc'_mem, hanc'_rid, hanc'_idx⟩ := transport anc hanc_mem
      exact ⟨anc', hanc'_mem, hanc'_rid.trans hanc_rid, hanc'_idx ▸ hanc_idx⟩
    · subst hnew
      dsimp at href
      have hlocEq_cfg : (Reference.OId oid0).loc? cfg = some (Location.Rgn rid') := by
        rw [loc_eq]; exact hlocEq
      unfold Frame.refs at href
      dsimp at href
      rw [List.mem_append] at href
      rcases href with href | href
      · have href' : Reference.OId oid0 ∈ frame.refs := by
          unfold Frame.refs
          exact List.mem_append_left _ href
        obtain ⟨anc, hanc_mem, hanc_rid, hanc_idx⟩ :=
          s3 frame frame_mem (Reference.OId oid0) href' rid' oid0 rfl hlocEq_cfg
        obtain ⟨anc', hanc'_mem, hanc'_rid, hanc'_idx⟩ := transport anc hanc_mem
        refine ⟨anc', hanc'_mem, hanc'_rid.trans hanc_rid, ?_⟩
        dsimp
        rw [hanc'_idx, ← hframe_idx]
        exact hanc_idx
      · rcases swap_corollary_alist_insert_refs_mem href with heq | horig
        · have hyfRef_rgn : (Reference.OId oid0).loc? cfg = some (Location.Rgn rid) :=
            h3 rid oid0 region hregion (heq ▸ hyfRef_mem_region)
          have heqloc : rid = rid' := by
            have := hyfRef_rgn.symm.trans hlocEq_cfg
            rw [Option.some_inj, Location.Rgn.injEq] at this
            exact this
          refine ⟨({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex),
            hframe_mem_cfg, ?_, le_refl _⟩
          dsimp
          rw [← heqloc, ← hrid]
        · have href' : Reference.OId oid0 ∈ frame.refs := by
            unfold Frame.refs
            exact List.mem_append_right _ horig
          obtain ⟨anc, hanc_mem, hanc_rid, hanc_idx⟩ :=
            s3 frame frame_mem (Reference.OId oid0) href' rid' oid0 rfl hlocEq_cfg
          obtain ⟨anc', hanc'_mem, hanc'_rid, hanc'_idx⟩ := transport anc hanc_mem
          refine ⟨anc', hanc'_mem, hanc'_rid.trans hanc_rid, ?_⟩
          dsimp
          rw [hanc'_idx, ← hframe_idx]
          exact hanc_idx
  · -- SWAP-REGION-REGION: identical shape to SWAP-REGION-OBJECT.
    subst hcfg'
    have h3 := vcfg.h3
    have hfield : obj.lookup yf.field = some yfRef :=
      swap_corollary_region_field_eq_yfRef (hyoid ▸ hyr) (hyoid ▸ hyrloc ▸ hyrl) hregion hobj hyf
    have hyfRef_mem_region : yfRef ∈ region.refs :=
      swap_corollary_objMap_bind_refs_mem_of_lookup hobj
        (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hfield))
    obtain ⟨stack_eq, hframe_idx⟩ := swap_corollary_stack_eq hframe
    set newRegion : Region :=
      { region with objMap := AList.insert yoid (obj.insert yf.field (Reference.RId xrid)) region.objMap }
      with newRegion_def
    have loc_eq_heap := swap_corollary_region_loc_eq (region := region) (newRegion := newRegion)
      (obj := obj) (v := obj.insert yf.field (Reference.RId xrid)) vcfg hregion hobj rfl
    have loc_eq_stack := swap_corollary_stack_varmap_loc_eq
      (cfg := { cfg with heap := cfg.heap.insert rid newRegion })
      (newVarMap := frame.varMap.insert x yfRef) hframe
    have loc_eq : ∀ oid', (Reference.OId oid').loc? cfg =
        (Reference.OId oid').loc? { cfg with
          stack := cfg.stack.dropLast ++ [({ frame with varMap := frame.varMap.insert x yfRef } : Frame)],
          heap := cfg.heap.insert rid newRegion } :=
      fun oid' => (loc_eq_heap oid').trans (loc_eq_stack oid')
    set newFrame : Frame := { frame with varMap := frame.varMap.insert x yfRef } with newFrame_def
    have stackWithIndex_eq_cfg : cfg.stackWithIndex =
        cfg.stack.dropLast.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) ++
          [({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex)] := by
      unfold RuntimeConfig.stackWithIndex
      conv_lhs => rw [stack_eq]
      rw [List.mapIdx_concat]
    have stackWithIndex_eq :
        (RuntimeConfig.stackWithIndex
          { stack := cfg.stack.dropLast ++ [newFrame], heap := cfg.heap.insert rid newRegion }) =
          cfg.stack.dropLast.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) ++
            [({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex)] := by
      unfold RuntimeConfig.stackWithIndex
      dsimp
      rw [List.mapIdx_concat]
    have transport : ∀ f ∈ cfg.stackWithIndex,
        ∃ g ∈ (RuntimeConfig.stackWithIndex
          { stack := cfg.stack.dropLast ++ [newFrame], heap := cfg.heap.insert rid newRegion }),
          g.regionId = f.regionId ∧ g.index = f.index := by
      intro f hf
      rw [stackWithIndex_eq_cfg, List.mem_append, List.mem_singleton] at hf
      rcases hf with hf | hf
      · exact ⟨f, stackWithIndex_eq ▸ List.mem_append_left _ hf, rfl, rfl⟩
      · subst hf
        exact ⟨({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex),
          stackWithIndex_eq ▸ List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl⟩
    have hframe_mem_cfg : ({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex) ∈
        (RuntimeConfig.stackWithIndex
          { stack := cfg.stack.dropLast ++ [newFrame], heap := cfg.heap.insert rid newRegion }) := by
      rw [stackWithIndex_eq]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    intro frame' hframe' ref href rid' oid0 hrefeq hlocEq
    subst hrefeq
    rw [stackWithIndex_eq, List.mem_append, List.mem_singleton] at hframe'
    rcases hframe' with hold | hnew
    · have hframe'_in_cfg : frame' ∈ cfg.stackWithIndex := by
        rw [stackWithIndex_eq_cfg]; exact List.mem_append_left _ hold
      have hlocEq_cfg : (Reference.OId oid0).loc? cfg = some (Location.Rgn rid') := by
        rw [loc_eq]; exact hlocEq
      obtain ⟨anc, hanc_mem, hanc_rid, hanc_idx⟩ :=
        s3 frame' hframe'_in_cfg (Reference.OId oid0) href rid' oid0 rfl hlocEq_cfg
      obtain ⟨anc', hanc'_mem, hanc'_rid, hanc'_idx⟩ := transport anc hanc_mem
      exact ⟨anc', hanc'_mem, hanc'_rid.trans hanc_rid, hanc'_idx ▸ hanc_idx⟩
    · subst hnew
      dsimp at href
      have hlocEq_cfg : (Reference.OId oid0).loc? cfg = some (Location.Rgn rid') := by
        rw [loc_eq]; exact hlocEq
      unfold Frame.refs at href
      dsimp at href
      rw [List.mem_append] at href
      rcases href with href | href
      · have href' : Reference.OId oid0 ∈ frame.refs := by
          unfold Frame.refs
          exact List.mem_append_left _ href
        obtain ⟨anc, hanc_mem, hanc_rid, hanc_idx⟩ :=
          s3 frame frame_mem (Reference.OId oid0) href' rid' oid0 rfl hlocEq_cfg
        obtain ⟨anc', hanc'_mem, hanc'_rid, hanc'_idx⟩ := transport anc hanc_mem
        refine ⟨anc', hanc'_mem, hanc'_rid.trans hanc_rid, ?_⟩
        dsimp
        rw [hanc'_idx, ← hframe_idx]
        exact hanc_idx
      · rcases swap_corollary_alist_insert_refs_mem href with heq | horig
        · have hyfRef_rgn : (Reference.OId oid0).loc? cfg = some (Location.Rgn rid) :=
            h3 rid oid0 region hregion (heq ▸ hyfRef_mem_region)
          have heqloc : rid = rid' := by
            have := hyfRef_rgn.symm.trans hlocEq_cfg
            rw [Option.some_inj, Location.Rgn.injEq] at this
            exact this
          refine ⟨({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex),
            hframe_mem_cfg, ?_, le_refl _⟩
          dsimp
          rw [← heqloc, ← hrid]
        · have href' : Reference.OId oid0 ∈ frame.refs := by
            unfold Frame.refs
            exact List.mem_append_right _ horig
          obtain ⟨anc, hanc_mem, hanc_rid, hanc_idx⟩ :=
            s3 frame frame_mem (Reference.OId oid0) href' rid' oid0 rfl hlocEq_cfg
          obtain ⟨anc', hanc'_mem, hanc'_rid, hanc'_idx⟩ := transport anc hanc_mem
          refine ⟨anc', hanc'_mem, hanc'_rid.trans hanc_rid, ?_⟩
          dsimp
          rw [hanc'_idx, ← hframe_idx]
          exact hanc_idx
  · -- SWAP-REGION-BRIDGE: stack untouched, so this transports directly, ancestor stays unchanged
    subst hcfg'
    have hfield : obj.lookup yf.field = some yfRef :=
      swap_corollary_region_field_eq_yfRef (hyoid ▸ hyr) (hyoid ▸ hyrloc ▸ hyrl) hregion hobj hyf
    set newRegion : Region := { region with
        bridgeObjectId := yfoid,
        objMap := AList.insert yoid (obj.insert yf.field (Reference.OId region.bridgeObjectId)) region.objMap
      } with newRegion_def
    have loc_eq := swap_corollary_region_loc_eq (region := region) (newRegion := newRegion)
      (obj := obj) (v := obj.insert yf.field (Reference.OId region.bridgeObjectId)) vcfg hregion hobj rfl
    intro frame' hframe' ref href rid' oid0 hrefeq hlocEq
    subst hrefeq
    have hlocEq_cfg : (Reference.OId oid0).loc? cfg = some (Location.Rgn rid') := by
      rw [loc_eq]; exact hlocEq
    exact s3 frame' hframe' (Reference.OId oid0) href rid' oid0 rfl hlocEq_cfg

theorem swap_HS1 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  HS1 cfg' := by
  intro vcfg h
  have hs1 := vcfg.hs1
  have h1 := vcfg.h1
  obtain ⟨frame, hframe, yRef, hyr, yRefLoc, hyrl, yfRef, hyf, yfRefLoc, hyfl, hcase⟩ := swap_cases h
  have frame_mem : frame ∈ cfg.stackWithIndex := List.mem_of_getLast? hframe
  unfold HS1
  rcases hcase with
    ⟨yoid, xRef, obj, hxb, hyoid, hyrloc, hxr, hobj, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xoid, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hxrl, hxrid, hstatus, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hstatus, hcfg'⟩ |
    ⟨yoid, yrid, yfoid, yfrid, region, obj, hxb, hyoid, hyrloc, hyfoid, hyfrloc, hyrid, hyfrid, hregion, hobj, hcfg'⟩
  · -- SWAP-STACK
    subst hcfg'
    have hfield : obj.lookup yf.field = some yfRef :=
      swap_corollary_stack_field_eq_yfRef frame_mem (hyoid ▸ hyr) (hyoid ▸ hyrloc ▸ hyrl) hobj hyf
    obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
    have frame_toFrame_mem : frame.toFrame ∈ cfg.stack :=
      stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self _)
    have hxRef_mem : xRef ∈ cfg.refs := List.mem_append_left _
      (swap_corollary_frame_refs_mem_stack frame_toFrame_mem
        (List.mem_append_right _ (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hxr))))
    have hyfRef_mem : yfRef ∈ cfg.refs := List.mem_append_left _
      (swap_corollary_frame_refs_mem_stack frame_toFrame_mem
        (List.mem_append_left _ (swap_corollary_objMap_bind_refs_mem_of_lookup hobj
          (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hfield)))))
    have hdrop_refs : ∀ r, r ∈ Stack.refs cfg.stack.dropLast → r ∈ cfg.refs := by
      intro r hr
      apply List.mem_append_left
      rw [stack_eq, swap_corollary_stack_refs_append]
      exact List.mem_append_left _ hr
    have hframe_refs : ∀ r, r ∈ Frame.refs frame.toFrame → r ∈ cfg.refs := by
      intro r hr
      apply List.mem_append_left
      rw [stack_eq, swap_corollary_stack_refs_append]
      exact List.mem_append_right _ hr
    have hstack_split : Stack.objectIds cfg.stack = Stack.objectIds cfg.stack.dropLast ++ frame.objMap.keys := by
      conv_lhs => rw [stack_eq]
      rw [swap_corollary_stack_objectIds_append]
      rfl
    set newFrame : Frame := { frame with
        varMap := frame.varMap.insert x yfRef,
        objMap := frame.objMap.insert yoid (obj.insert yf.field xRef) } with newFrame_def
    have hobjIds_of_old : ∀ oid0, oid0 ∈ cfg.objectIds → oid0 ∈
        RuntimeConfig.objectIds { stack := cfg.stack.dropLast ++ [newFrame], heap := cfg.heap } := by
      intro oid0 hoid0
      unfold RuntimeConfig.objectIds at hoid0 ⊢
      dsimp
      rw [hstack_split, List.mem_append, List.mem_append] at hoid0
      rw [swap_corollary_stack_objectIds_append, List.mem_append, List.mem_append]
      rcases hoid0 with (hoid0 | hoid0) | hoid0
      · exact Or.inl (Or.inl hoid0)
      · left; right
        unfold Frame.objectIds
        show oid0 ∈ AList.keys (frame.objMap.insert yoid (obj.insert yf.field xRef))
        rw [← AList.mem_keys, AList.mem_insert]
        exact Or.inr (AList.mem_keys.mpr hoid0)
      · exact Or.inr hoid0
    intro oid0 hr
    unfold RuntimeConfig.refs at hr
    dsimp at hr
    rw [swap_corollary_stack_refs_append, List.mem_append, List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · exact hobjIds_of_old oid0 (hs1 oid0 (hdrop_refs _ hr))
    · unfold Frame.refs at hr
      dsimp at hr
      rw [List.mem_append] at hr
      rcases hr with hr | hr
      · rcases swap_corollary_objMap_insert_bind_refs_mem hr with hr' | hr'
        · rcases swap_corollary_alist_insert_refs_mem hr' with hr'' | hr''
          · exact hobjIds_of_old oid0 (hs1 oid0 (hr'' ▸ hxRef_mem))
          · exact hobjIds_of_old oid0 (hs1 oid0 (hframe_refs _ (List.mem_append_left _
              (swap_corollary_objMap_bind_refs_mem_of_lookup hobj hr''))))
        · exact hobjIds_of_old oid0 (hs1 oid0 (hframe_refs _ (List.mem_append_left _ hr')))
      · rcases swap_corollary_alist_insert_refs_mem hr with hr' | hr'
        · exact hobjIds_of_old oid0 (hs1 oid0 (hr' ▸ hyfRef_mem))
        · exact hobjIds_of_old oid0 (hs1 oid0 (hframe_refs _ (List.mem_append_right _ hr')))
    · exact hobjIds_of_old oid0 (hs1 oid0 (List.mem_append_right _ hr))
  · -- SWAP-REGION-OBJECT
    subst hcfg'
    have hfield : obj.lookup yf.field = some yfRef :=
      swap_corollary_region_field_eq_yfRef (hyoid ▸ hyr) (hyoid ▸ hyrloc ▸ hyrl) hregion hobj hyf
    obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
    have frame_toFrame_mem : frame.toFrame ∈ cfg.stack :=
      stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self _)
    have hxoidRef_mem : Reference.OId xoid ∈ cfg.refs := List.mem_append_left _
      (swap_corollary_frame_refs_mem_stack frame_toFrame_mem
        (List.mem_append_right _ (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hxr))))
    have hyfRef_mem : yfRef ∈ cfg.refs := List.mem_append_right _
      (swap_corollary_heap_refs_mem_of_lookup hregion
        (swap_corollary_objMap_bind_refs_mem_of_lookup hobj
          (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hfield))))
    have hdrop_refs : ∀ r, r ∈ Stack.refs cfg.stack.dropLast → r ∈ cfg.refs := by
      intro r hr
      apply List.mem_append_left
      rw [stack_eq, swap_corollary_stack_refs_append]
      exact List.mem_append_left _ hr
    have hframe_refs : ∀ r, r ∈ Frame.refs frame.toFrame → r ∈ cfg.refs := by
      intro r hr
      apply List.mem_append_left
      rw [stack_eq, swap_corollary_stack_refs_append]
      exact List.mem_append_right _ hr
    set newFrame : Frame := { frame with varMap := frame.varMap.insert x yfRef } with newFrame_def
    set newRegion : Region := { region with
        objMap := AList.insert yoid (obj.insert yf.field (Reference.OId xoid)) region.objMap } with newRegion_def
    have region_perm := swap_corollary_insert_keys_perm (l := region.objMap)
      (v := obj.insert yf.field (Reference.OId xoid)) (swap_corollary_mem_keys_of_lookup hobj)
    have heap_perm := swap_corollary_region_heap_objectIds_perm (newRegion := newRegion) hregion region_perm
    have hstack_eq : Stack.objectIds (cfg.stack.dropLast ++ [newFrame]) = Stack.objectIds cfg.stack := by
      rw [swap_corollary_stack_objectIds_append]
      conv_rhs => rw [stack_eq]
      rw [swap_corollary_stack_objectIds_append]
      rfl
    have hobjIds_of_old : ∀ oid0, oid0 ∈ cfg.objectIds → oid0 ∈
        RuntimeConfig.objectIds { stack := cfg.stack.dropLast ++ [newFrame], heap := cfg.heap.insert rid newRegion } := by
      intro oid0 hoid0
      unfold RuntimeConfig.objectIds at hoid0 ⊢
      dsimp
      rw [hstack_eq]
      rw [List.mem_append] at hoid0 ⊢
      rcases hoid0 with hoid0 | hoid0
      · exact Or.inl hoid0
      · exact Or.inr (heap_perm.mem_iff.mpr hoid0)
    intro oid0 hr
    unfold RuntimeConfig.refs at hr
    dsimp at hr
    rw [swap_corollary_stack_refs_append, List.mem_append, List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · exact hobjIds_of_old oid0 (hs1 oid0 (hdrop_refs _ hr))
    · unfold Frame.refs at hr
      dsimp at hr
      rw [List.mem_append] at hr
      rcases hr with hr | hr
      · exact hobjIds_of_old oid0 (hs1 oid0 (hframe_refs _ (List.mem_append_left _ hr)))
      · rcases swap_corollary_alist_insert_refs_mem hr with hr' | hr'
        · exact hobjIds_of_old oid0 (hs1 oid0 (hr' ▸ hyfRef_mem))
        · exact hobjIds_of_old oid0 (hs1 oid0 (hframe_refs _ (List.mem_append_right _ hr')))
    · rcases swap_corollary_heap_insert_refs_mem (swap_corollary_mem_keys_of_lookup hregion) hr with hr' | hr'
      · unfold Region.refs at hr'
        dsimp at hr'
        rcases swap_corollary_objMap_insert_bind_refs_mem hr' with hr'' | hr''
        · rcases swap_corollary_alist_insert_refs_mem hr'' with hr''' | hr'''
          · exact hobjIds_of_old oid0 (hs1 oid0 (hr''' ▸ hxoidRef_mem))
          · exact hobjIds_of_old oid0 (hs1 oid0 (List.mem_append_right _
              (swap_corollary_heap_refs_mem_of_lookup hregion
                (swap_corollary_objMap_bind_refs_mem_of_lookup hobj hr'''))))
        · exact hobjIds_of_old oid0 (hs1 oid0 (List.mem_append_right _
            (swap_corollary_heap_refs_mem_of_lookup hregion hr'')))
      · exact hobjIds_of_old oid0 (hs1 oid0 (List.mem_append_right _ hr'))
  · -- SWAP-REGION-REGION
    subst hcfg'
    have hfield : obj.lookup yf.field = some yfRef :=
      swap_corollary_region_field_eq_yfRef (hyoid ▸ hyr) (hyoid ▸ hyrloc ▸ hyrl) hregion hobj hyf
    obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
    have frame_toFrame_mem : frame.toFrame ∈ cfg.stack :=
      stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self _)
    have hxridRef_mem : Reference.RId xrid ∈ cfg.refs := List.mem_append_left _
      (swap_corollary_frame_refs_mem_stack frame_toFrame_mem
        (List.mem_append_right _ (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hxr))))
    have hyfRef_mem : yfRef ∈ cfg.refs := List.mem_append_right _
      (swap_corollary_heap_refs_mem_of_lookup hregion
        (swap_corollary_objMap_bind_refs_mem_of_lookup hobj
          (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hfield))))
    have hdrop_refs : ∀ r, r ∈ Stack.refs cfg.stack.dropLast → r ∈ cfg.refs := by
      intro r hr
      apply List.mem_append_left
      rw [stack_eq, swap_corollary_stack_refs_append]
      exact List.mem_append_left _ hr
    have hframe_refs : ∀ r, r ∈ Frame.refs frame.toFrame → r ∈ cfg.refs := by
      intro r hr
      apply List.mem_append_left
      rw [stack_eq, swap_corollary_stack_refs_append]
      exact List.mem_append_right _ hr
    set newFrame : Frame := { frame with varMap := frame.varMap.insert x yfRef } with newFrame_def
    set newRegion : Region := { region with
        objMap := AList.insert yoid (obj.insert yf.field (Reference.RId xrid)) region.objMap } with newRegion_def
    have region_perm := swap_corollary_insert_keys_perm (l := region.objMap)
      (v := obj.insert yf.field (Reference.RId xrid)) (swap_corollary_mem_keys_of_lookup hobj)
    have heap_perm := swap_corollary_region_heap_objectIds_perm (newRegion := newRegion) hregion region_perm
    have hstack_eq : Stack.objectIds (cfg.stack.dropLast ++ [newFrame]) = Stack.objectIds cfg.stack := by
      rw [swap_corollary_stack_objectIds_append]
      conv_rhs => rw [stack_eq]
      rw [swap_corollary_stack_objectIds_append]
      rfl
    have hobjIds_of_old : ∀ oid0, oid0 ∈ cfg.objectIds → oid0 ∈
        RuntimeConfig.objectIds { stack := cfg.stack.dropLast ++ [newFrame], heap := cfg.heap.insert rid newRegion } := by
      intro oid0 hoid0
      unfold RuntimeConfig.objectIds at hoid0 ⊢
      dsimp
      rw [hstack_eq]
      rw [List.mem_append] at hoid0 ⊢
      rcases hoid0 with hoid0 | hoid0
      · exact Or.inl hoid0
      · exact Or.inr (heap_perm.mem_iff.mpr hoid0)
    intro oid0 hr
    unfold RuntimeConfig.refs at hr
    dsimp at hr
    rw [swap_corollary_stack_refs_append, List.mem_append, List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · exact hobjIds_of_old oid0 (hs1 oid0 (hdrop_refs _ hr))
    · unfold Frame.refs at hr
      dsimp at hr
      rw [List.mem_append] at hr
      rcases hr with hr | hr
      · exact hobjIds_of_old oid0 (hs1 oid0 (hframe_refs _ (List.mem_append_left _ hr)))
      · rcases swap_corollary_alist_insert_refs_mem hr with hr' | hr'
        · exact hobjIds_of_old oid0 (hs1 oid0 (hr' ▸ hyfRef_mem))
        · exact hobjIds_of_old oid0 (hs1 oid0 (hframe_refs _ (List.mem_append_right _ hr')))
    · rcases swap_corollary_heap_insert_refs_mem (swap_corollary_mem_keys_of_lookup hregion) hr with hr' | hr'
      · unfold Region.refs at hr'
        dsimp at hr'
        rcases swap_corollary_objMap_insert_bind_refs_mem hr' with hr'' | hr''
        · rcases swap_corollary_alist_insert_refs_mem hr'' with hr''' | hr'''
          · exact hobjIds_of_old oid0 (hs1 oid0 (hr''' ▸ hxridRef_mem))
          · exact hobjIds_of_old oid0 (hs1 oid0 (List.mem_append_right _
              (swap_corollary_heap_refs_mem_of_lookup hregion
                (swap_corollary_objMap_bind_refs_mem_of_lookup hobj hr'''))))
        · exact hobjIds_of_old oid0 (hs1 oid0 (List.mem_append_right _
            (swap_corollary_heap_refs_mem_of_lookup hregion hr'')))
      · exact hobjIds_of_old oid0 (hs1 oid0 (List.mem_append_right _ hr'))
  · -- SWAP-REGION-BRIDGE: the one branch that writes a genuinely "new" ref value (the old
    -- bridgeObjectId, now wrapped as a field value) -- handled via H1 instead of HS1/refs-tracing,
    -- since nothing guarantees a bridge object's own id was previously referenced as a *value*.
    subst hcfg'
    have hfield : obj.lookup yf.field = some yfRef :=
      swap_corollary_region_field_eq_yfRef (hyoid ▸ hyr) (hyoid ▸ hyrloc ▸ hyrl) hregion hobj hyf
    have region_mem : region ∈ cfg.heap.regions := by
      unfold Heap.regions
      exact List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hregion)
    have hbridge_mem : region.bridgeObjectId ∈ region.objMap := h1 region region_mem
    set newRegion : Region := { region with
        bridgeObjectId := yfoid,
        objMap := AList.insert yoid (obj.insert yf.field (Reference.OId region.bridgeObjectId)) region.objMap
      } with newRegion_def
    have region_perm := swap_corollary_insert_keys_perm (l := region.objMap)
      (v := obj.insert yf.field (Reference.OId region.bridgeObjectId))
      (swap_corollary_mem_keys_of_lookup hobj)
    have heap_perm := swap_corollary_region_heap_objectIds_perm (newRegion := newRegion) hregion region_perm
    have hobjIds_of_old : ∀ oid0, oid0 ∈ cfg.objectIds → oid0 ∈
        RuntimeConfig.objectIds { stack := cfg.stack, heap := cfg.heap.insert yrid newRegion } := by
      intro oid0 hoid0
      unfold RuntimeConfig.objectIds at hoid0 ⊢
      dsimp
      rw [List.mem_append] at hoid0 ⊢
      rcases hoid0 with hoid0 | hoid0
      · exact Or.inl hoid0
      · exact Or.inr (heap_perm.mem_iff.mpr hoid0)
    have hbridge_objIds : region.bridgeObjectId ∈
        RuntimeConfig.objectIds { stack := cfg.stack, heap := cfg.heap.insert yrid newRegion } := by
      apply hobjIds_of_old
      unfold RuntimeConfig.objectIds
      apply List.mem_append_right
      unfold Heap.objectIds
      rw [List.mem_flatten]
      refine ⟨region.objMap.keys, ?_, AList.mem_keys.mp hbridge_mem⟩
      exact List.mem_map_of_mem (f := fun e : Sigma (fun _ : RegionId => Region) => e.2.objectIds)
        (AList.lookup_mem_entries hregion)
    intro oid0 hr
    unfold RuntimeConfig.refs at hr
    dsimp at hr
    rw [List.mem_append] at hr
    rcases hr with hr | hr
    · exact hobjIds_of_old oid0 (hs1 oid0 (List.mem_append_left _ hr))
    · rcases swap_corollary_heap_insert_refs_mem (swap_corollary_mem_keys_of_lookup hregion) hr with hr' | hr'
      · unfold Region.refs at hr'
        dsimp at hr'
        rcases swap_corollary_objMap_insert_bind_refs_mem hr' with hr'' | hr''
        · rcases swap_corollary_alist_insert_refs_mem hr'' with hr''' | hr'''
          · rw [Reference.OId.injEq] at hr'''
            exact hr''' ▸ hbridge_objIds
          · exact hobjIds_of_old oid0 (hs1 oid0 (List.mem_append_right _
              (swap_corollary_heap_refs_mem_of_lookup hregion
                (swap_corollary_objMap_bind_refs_mem_of_lookup hobj hr'''))))
        · exact hobjIds_of_old oid0 (hs1 oid0 (List.mem_append_right _
            (swap_corollary_heap_refs_mem_of_lookup hregion hr'')))
      · exact hobjIds_of_old oid0 (hs1 oid0 (List.mem_append_right _ hr'))

theorem swap_HS2 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  HS2 cfg' := by
  intro vcfg h
  have hs2 := vcfg.hs2
  obtain ⟨frame, hframe, yRef, hyr, yRefLoc, hyrl, yfRef, hyf, yfRefLoc, hyfl, hcase⟩ := swap_cases h
  have frame_mem : frame ∈ cfg.stackWithIndex := List.mem_of_getLast? hframe
  unfold HS2
  rcases hcase with
    ⟨yoid, xRef, obj, hxb, hyoid, hyrloc, hxr, hobj, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xoid, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hxrl, hxrid, hstatus, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hstatus, hcfg'⟩ |
    ⟨yoid, yrid, yfoid, yfrid, region, obj, hxb, hyoid, hyrloc, hyfoid, hyfrloc, hyrid, hyfrid, hregion, hobj, hcfg'⟩
  · -- SWAP-STACK: heap untouched, transport refs through the mutated last frame
    subst hcfg'
    have hfield : obj.lookup yf.field = some yfRef :=
      swap_corollary_stack_field_eq_yfRef frame_mem (hyoid ▸ hyr) (hyoid ▸ hyrloc ▸ hyrl) hobj hyf
    obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
    have frame_toFrame_mem : frame.toFrame ∈ cfg.stack :=
      stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self _)
    have hxRef_mem : xRef ∈ cfg.refs := List.mem_append_left _
      (swap_corollary_frame_refs_mem_stack frame_toFrame_mem
        (List.mem_append_right _ (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hxr))))
    have hyfRef_mem : yfRef ∈ cfg.refs := List.mem_append_left _
      (swap_corollary_frame_refs_mem_stack frame_toFrame_mem
        (List.mem_append_left _ (swap_corollary_objMap_bind_refs_mem_of_lookup hobj
          (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hfield)))))
    have hdrop_refs : ∀ r, r ∈ Stack.refs cfg.stack.dropLast → r ∈ cfg.refs := by
      intro r hr
      apply List.mem_append_left
      rw [stack_eq, swap_corollary_stack_refs_append]
      exact List.mem_append_left _ hr
    have hframe_refs : ∀ r, r ∈ Frame.refs frame.toFrame → r ∈ cfg.refs := by
      intro r hr
      apply List.mem_append_left
      rw [stack_eq, swap_corollary_stack_refs_append]
      exact List.mem_append_right _ hr
    intro rid' hr
    dsimp at hr ⊢
    unfold RuntimeConfig.refs at hr
    dsimp at hr
    rw [swap_corollary_stack_refs_append, List.mem_append, List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · exact hs2 rid' (hdrop_refs _ hr)
    · unfold Frame.refs at hr
      dsimp at hr
      rw [List.mem_append] at hr
      rcases hr with hr | hr
      · rcases swap_corollary_objMap_insert_bind_refs_mem hr with hr' | hr'
        · rcases swap_corollary_alist_insert_refs_mem hr' with hr'' | hr''
          · exact hs2 rid' (hr'' ▸ hxRef_mem)
          · exact hs2 rid' (hframe_refs _ (List.mem_append_left _
              (swap_corollary_objMap_bind_refs_mem_of_lookup hobj hr'')))
        · exact hs2 rid' (hframe_refs _ (List.mem_append_left _ hr'))
      · rcases swap_corollary_alist_insert_refs_mem hr with hr' | hr'
        · exact hs2 rid' (hr' ▸ hyfRef_mem)
        · exact hs2 rid' (hframe_refs _ (List.mem_append_right _ hr'))
    · exact hs2 rid' (List.mem_append_right _ hr)
  · -- SWAP-REGION-OBJECT
    subst hcfg'
    have hfield : obj.lookup yf.field = some yfRef :=
      swap_corollary_region_field_eq_yfRef (hyoid ▸ hyr) (hyoid ▸ hyrloc ▸ hyrl) hregion hobj hyf
    obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
    have frame_toFrame_mem : frame.toFrame ∈ cfg.stack :=
      stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self _)
    have hridmem : rid ∈ cfg.heap.keys := swap_corollary_mem_keys_of_lookup hregion
    have hxoidRef_mem : Reference.OId xoid ∈ cfg.refs := List.mem_append_left _
      (swap_corollary_frame_refs_mem_stack frame_toFrame_mem
        (List.mem_append_right _ (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hxr))))
    have hyfRef_mem : yfRef ∈ cfg.refs := List.mem_append_right _
      (swap_corollary_heap_refs_mem_of_lookup hregion
        (swap_corollary_objMap_bind_refs_mem_of_lookup hobj
          (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hfield))))
    have hdrop_refs : ∀ r, r ∈ Stack.refs cfg.stack.dropLast → r ∈ cfg.refs := by
      intro r hr
      apply List.mem_append_left
      rw [stack_eq, swap_corollary_stack_refs_append]
      exact List.mem_append_left _ hr
    have hframe_refs : ∀ r, r ∈ Frame.refs frame.toFrame → r ∈ cfg.refs := by
      intro r hr
      apply List.mem_append_left
      rw [stack_eq, swap_corollary_stack_refs_append]
      exact List.mem_append_right _ hr
    intro rid' hr
    dsimp at hr ⊢
    rw [swap_corollary_heap_insert_keys_mem hridmem]
    unfold RuntimeConfig.refs at hr
    dsimp at hr
    rw [swap_corollary_stack_refs_append, List.mem_append, List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · exact hs2 rid' (hdrop_refs _ hr)
    · unfold Frame.refs at hr
      dsimp at hr
      rw [List.mem_append] at hr
      rcases hr with hr | hr
      · exact hs2 rid' (hframe_refs _ (List.mem_append_left _ hr))
      · rcases swap_corollary_alist_insert_refs_mem hr with hr' | hr'
        · exact hs2 rid' (hr' ▸ hyfRef_mem)
        · exact hs2 rid' (hframe_refs _ (List.mem_append_right _ hr'))
    · rcases swap_corollary_heap_insert_refs_mem hridmem hr with hr' | hr'
      · unfold Region.refs at hr'
        dsimp at hr'
        rcases swap_corollary_objMap_insert_bind_refs_mem hr' with hr'' | hr''
        · rcases swap_corollary_alist_insert_refs_mem hr'' with hr''' | hr'''
          · exact hs2 rid' (hr''' ▸ hxoidRef_mem)
          · exact hs2 rid' (List.mem_append_right _
              (swap_corollary_heap_refs_mem_of_lookup hregion
                (swap_corollary_objMap_bind_refs_mem_of_lookup hobj hr''')))
        · exact hs2 rid' (List.mem_append_right _ (swap_corollary_heap_refs_mem_of_lookup hregion hr''))
      · exact hs2 rid' (List.mem_append_right _ hr')
  · -- SWAP-REGION-REGION
    subst hcfg'
    have hfield : obj.lookup yf.field = some yfRef :=
      swap_corollary_region_field_eq_yfRef (hyoid ▸ hyr) (hyoid ▸ hyrloc ▸ hyrl) hregion hobj hyf
    obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
    have frame_toFrame_mem : frame.toFrame ∈ cfg.stack :=
      stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self _)
    have hridmem : rid ∈ cfg.heap.keys := swap_corollary_mem_keys_of_lookup hregion
    have hxridRef_mem : Reference.RId xrid ∈ cfg.refs := List.mem_append_left _
      (swap_corollary_frame_refs_mem_stack frame_toFrame_mem
        (List.mem_append_right _ (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hxr))))
    have hyfRef_mem : yfRef ∈ cfg.refs := List.mem_append_right _
      (swap_corollary_heap_refs_mem_of_lookup hregion
        (swap_corollary_objMap_bind_refs_mem_of_lookup hobj
          (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hfield))))
    have hdrop_refs : ∀ r, r ∈ Stack.refs cfg.stack.dropLast → r ∈ cfg.refs := by
      intro r hr
      apply List.mem_append_left
      rw [stack_eq, swap_corollary_stack_refs_append]
      exact List.mem_append_left _ hr
    have hframe_refs : ∀ r, r ∈ Frame.refs frame.toFrame → r ∈ cfg.refs := by
      intro r hr
      apply List.mem_append_left
      rw [stack_eq, swap_corollary_stack_refs_append]
      exact List.mem_append_right _ hr
    intro rid' hr
    dsimp at hr ⊢
    rw [swap_corollary_heap_insert_keys_mem hridmem]
    unfold RuntimeConfig.refs at hr
    dsimp at hr
    rw [swap_corollary_stack_refs_append, List.mem_append, List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · exact hs2 rid' (hdrop_refs _ hr)
    · unfold Frame.refs at hr
      dsimp at hr
      rw [List.mem_append] at hr
      rcases hr with hr | hr
      · exact hs2 rid' (hframe_refs _ (List.mem_append_left _ hr))
      · rcases swap_corollary_alist_insert_refs_mem hr with hr' | hr'
        · exact hs2 rid' (hr' ▸ hyfRef_mem)
        · exact hs2 rid' (hframe_refs _ (List.mem_append_right _ hr'))
    · rcases swap_corollary_heap_insert_refs_mem hridmem hr with hr' | hr'
      · unfold Region.refs at hr'
        dsimp at hr'
        rcases swap_corollary_objMap_insert_bind_refs_mem hr' with hr'' | hr''
        · rcases swap_corollary_alist_insert_refs_mem hr'' with hr''' | hr'''
          · exact hs2 rid' (hr''' ▸ hxridRef_mem)
          · exact hs2 rid' (List.mem_append_right _
              (swap_corollary_heap_refs_mem_of_lookup hregion
                (swap_corollary_objMap_bind_refs_mem_of_lookup hobj hr''')))
        · exact hs2 rid' (List.mem_append_right _ (swap_corollary_heap_refs_mem_of_lookup hregion hr''))
      · exact hs2 rid' (List.mem_append_right _ hr')
  · -- SWAP-REGION-BRIDGE: stack untouched, only the heap's region at yrid changes
    subst hcfg'
    have hfield : obj.lookup yf.field = some yfRef :=
      swap_corollary_region_field_eq_yfRef (hyoid ▸ hyr) (hyoid ▸ hyrloc ▸ hyrl) hregion hobj hyf
    have hridmem : yrid ∈ cfg.heap.keys := swap_corollary_mem_keys_of_lookup hregion
    intro rid' hr
    dsimp at hr ⊢
    rw [swap_corollary_heap_insert_keys_mem hridmem]
    unfold RuntimeConfig.refs at hr
    dsimp at hr
    rw [List.mem_append] at hr
    rcases hr with hr | hr
    · exact hs2 rid' (List.mem_append_left _ hr)
    · rcases swap_corollary_heap_insert_refs_mem hridmem hr with hr' | hr'
      · unfold Region.refs at hr'
        dsimp at hr'
        rcases swap_corollary_objMap_insert_bind_refs_mem hr' with hr'' | hr''
        · rcases swap_corollary_alist_insert_refs_mem hr'' with hr''' | hr'''
          · exact absurd hr''' (by simp)
          · exact hs2 rid' (List.mem_append_right _
              (swap_corollary_heap_refs_mem_of_lookup hregion
                (swap_corollary_objMap_bind_refs_mem_of_lookup hobj hr''')))
        · exact hs2 rid' (List.mem_append_right _ (swap_corollary_heap_refs_mem_of_lookup hregion hr''))
      · exact hs2 rid' (List.mem_append_right _ hr')

theorem swap_valid : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  ValidConfig cfg' := by
  intro vcfg h
  exact {
    l1 := swap_L1 vcfg h,
    l2 := swap_L2 vcfg h,
    h1 := swap_H1 vcfg h,
    h2 := swap_H2 vcfg h,
    h3 := swap_H3 vcfg h,
    s1 := swap_S1 vcfg h,
    s2 := swap_S2 vcfg h,
    s3 := swap_S3 vcfg h,
    hs1 := swap_HS1 vcfg h,
    hs2 := swap_HS2 vcfg h
  }
