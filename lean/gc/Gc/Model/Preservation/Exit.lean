import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Theorems
import Gc.Model.Mutation

import Mathlib.Data.List.Infix

theorem exit_corollary_1 :
  ValidConfig cfg →
  exit cfg = some cfg' →
  ∀ (ref : Reference), ref.loc? cfg = Location.Rgn rid ↔ ref.loc? cfg' = Location.Rgn rid := by
  intro vcfg h ref
  unfold exit at h
  by_cases stack_length : cfg.stack.length >= 2
  · rw [if_pos stack_length] at h
    cases stackGetLast : List.getLast? cfg.stack with
    | none =>
      rw [stackGetLast] at h
      contradiction
    | some frame' =>
      rw [stackGetLast] at h
      cases heapLookup : cfg.heap.lookup frame'.regionId with
      | none =>
        dsimp at h
        rw [heapLookup] at h
        dsimp at h
        contradiction
      | some region' =>
        dsimp at h
        rw [heapLookup] at h
        dsimp at h
        have helper : (region'.status == Status.Open) = true := by
          have l2 : L2 cfg := vcfg.l2
          rw [List.getLast?_eq_some_iff] at stackGetLast
          obtain ⟨stack_last, stack_last_in_stack⟩ := stackGetLast
          have frame'_in_stack : frame' ∈ cfg.stack := by
            rw [stack_last_in_stack, List.mem_append]
            right
            exact List.mem_singleton_self frame'
          obtain ⟨region'', region''_in_heap, region''_status⟩ := l2 frame' frame'_in_stack
          rw [heapLookup, Option.some_inj] at region''_in_heap
          rw [← region''_in_heap] at region''_status
          rw [region''_status]
          rfl
        rw [if_pos helper, Option.some_inj] at h
        constructor
        · intro forward
          cases ref with
          | RId rid =>
            unfold Reference.loc? at forward
            dsimp at forward
            by_cases heapLookup' : (AList.keys cfg.heap).contains rid
            · rw [if_pos heapLookup'] at forward
              by_cases rid_eq_frame'_regionId : rid = frame'.regionId
              · subst rid
                have : cfg'.heap.keys.contains frame'.regionId = true := by
                  rw [← h]
                  rw [List.contains_iff_mem, AList.keys_insert]
                  left
                unfold Reference.loc?
                dsimp
                rw [if_pos this]
                exact forward
              · have : cfg'.heap.keys.contains rid = true := by
                  rw [← h]
                  rw [List.contains_iff_mem, AList.keys_insert]
                  right
                  change rid ∈ cfg.heap.keys.erase frame'.regionId
                  rw [List.mem_erase_of_ne rid_eq_frame'_regionId]
                  exact List.contains_iff_mem.mp heapLookup'
                unfold Reference.loc?
                dsimp
                rw [if_pos this]
                exact forward
            · rw [if_neg heapLookup'] at forward
              contradiction
          | OId oid =>
            unfold Reference.loc? at forward
            dsimp at forward
            cases heapLookup' : List.find? (fun x => (AList.keys x.snd.objMap).contains oid) cfg.heap.entries with
            | none =>
              rw [heapLookup'] at forward
              cases stackLookup : List.findRev? (fun frame => (AList.keys frame.objMap).contains oid) cfg.stackWithIndex with
              | none =>
                rw [stackLookup] at forward
                dsimp at forward
                contradiction
              | some frame =>
                rw [stackLookup] at forward
                dsimp at forward
                rw [Option.some_inj] at forward
                contradiction
            | some ridregion =>
              obtain ⟨rid, region⟩ := ridregion
              have stackLookup_none := oid_in_heap_implies_not_in_stack vcfg heapLookup'
              have forward' := forward
              rw [heapLookup', stackLookup_none] at forward'
              dsimp at forward'
              have stackLookupNew_none : List.findRev? (fun frame => (AList.keys frame.objMap).contains oid)
                cfg'.stackWithIndex = none := by
                rw [← h]
                unfold RuntimeConfig.stackWithIndex
                dsimp

              sorry
        · intro backward
          cases ref with
          | RId rid =>
            unfold Reference.loc? at backward
            dsimp at backward
            by_cases heapLookup' : (AList.keys (AList.insert frame'.regionId
                { bridgeObjectId := region'.bridgeObjectId, objMap := region'.objMap, status := Status.Closed }
                cfg.heap)).contains rid
            · rw [if_pos heapLookup'] at backward
              unfold Reference.loc?
              dsimp
              by_cases rid_eq_frame'_regionId : rid = frame'.regionId
              · subst rid
                have : cfg.heap.keys.contains frame'.regionId = true := by
                  apply AList.lookup_mem_entries at heapLookup
                  apply List.mem_keys_of_mem at heapLookup
                  dsimp at heapLookup
                  unfold AList.keys
                  exact List.contains_iff_mem.mpr heapLookup
                rw [if_pos this]
                exact backward
              · have : cfg.heap.keys.contains rid = true := by
                  rw [List.contains_iff_mem, ← AList.mem_keys, AList.mem_insert] at heapLookup'
                  replace heapLookup' := Or.resolve_left heapLookup' rid_eq_frame'_regionId
                  exact List.contains_iff_mem.mpr heapLookup'
                rw [if_pos this]
                exact backward
            · rw [if_neg heapLookup'] at backward
              contradiction
          | OId oid =>
            sorry
  · rw [if_neg stack_length] at h
    contradiction

theorem exit_corollary_2 :
  ValidConfig cfg →
  exit cfg = some cfg' →
  cfg.heap.lookup rid = some region →
  cfg'.heap.lookup rid = some region'' →
  region.refs = region''.refs := by
  intro vcfg h region_in_old_heap region''_in_new_heap
  unfold exit at h
  by_cases stack_length : cfg.stack.length >= 2
  · rw [if_pos stack_length] at h
    cases stackGetLast : List.getLast? cfg.stack with
    | none =>
      rw [stackGetLast] at h
      contradiction
    | some frame' =>
      rw [stackGetLast] at h
      cases heapLookup : cfg.heap.lookup frame'.regionId with
      | none =>
        dsimp at h
        rw [heapLookup] at h
        dsimp at h
        contradiction
      | some region' =>
        dsimp at h
        rw [heapLookup] at h
        dsimp at h
        have helper : (region'.status == Status.Open) = true := by
          have l2 : L2 cfg := vcfg.l2
          rw [List.getLast?_eq_some_iff] at stackGetLast
          obtain ⟨stack_last, stack_last_in_stack⟩ := stackGetLast
          have frame'_in_stack : frame' ∈ cfg.stack := by
            rw [stack_last_in_stack, List.mem_append]
            right
            exact List.mem_singleton_self frame'
          obtain ⟨region'', region''_in_heap, region''_status⟩ := l2 frame' frame'_in_stack
          rw [heapLookup, Option.some_inj] at region''_in_heap
          rw [← region''_in_heap] at region''_status
          rw [region''_status]
          rfl
        rw [if_pos helper, Option.some_inj] at h
        subst h
        by_cases rid_eq_frame'_regionId : rid = frame'.regionId
        · subst rid
          unfold Region.refs
          rw [heapLookup, Option.some_inj] at region_in_old_heap
          rw [AList.lookup_insert, Option.some_inj] at region''_in_new_heap
          subst region''_in_new_heap region
          dsimp
        · unfold Region.refs
          rw [AList.lookup_insert_ne rid_eq_frame'_regionId] at region''_in_new_heap
          rw [region''_in_new_heap, Option.some_inj] at region_in_old_heap
          subst region_in_old_heap
          dsimp
  · rw [if_neg stack_length] at h
    contradiction

theorem exit_corollary_3 :
  ValidConfig cfg →
  exit cfg = some cfg' →
  ∀ (ref : Reference), ref.loc? cfg' = Location.Stk fid → ref.loc? cfg = Location.Stk fid := by
  intro vcfg h rid
  unfold exit at h
  by_cases stack_length : cfg.stack.length >= 2
  · rw [if_pos stack_length] at h
    cases stackGetLast : List.getLast? cfg.stack with
    | none =>
      rw [stackGetLast] at h
      contradiction
    | some frame' =>
      rw [stackGetLast] at h
      cases heapLookup : cfg.heap.lookup frame'.regionId with
      | none =>
        dsimp at h
        rw [heapLookup] at h
        dsimp at h
        contradiction
      | some region' =>
        dsimp at h
        rw [heapLookup] at h
        dsimp at h
        have helper : (region'.status == Status.Open) = true := by
          have l2 : L2 cfg := vcfg.l2
          rw [List.getLast?_eq_some_iff] at stackGetLast
          obtain ⟨stack_last, stack_last_in_stack⟩ := stackGetLast
          have frame'_in_stack : frame' ∈ cfg.stack := by
            rw [stack_last_in_stack, List.mem_append]
            right
            exact List.mem_singleton_self frame'
          obtain ⟨region'', region''_in_heap, region''_status⟩ := l2 frame' frame'_in_stack
          rw [heapLookup, Option.some_inj] at region''_in_heap
          rw [← region''_in_heap] at region''_status
          rw [region''_status]
          rfl
        rw [if_pos helper, Option.some_inj] at h
        subst h
        intro forwards
        sorry
  · rw [if_neg stack_length] at h
    contradiction

theorem exit_H1 : ValidConfig cfg →
  exit cfg = some cfg' →
  H1 cfg' := by
  intro vcfg h region region_in_heap
  unfold exit at h
  by_cases stack_length : cfg.stack.length >= 2
  · rw [if_pos stack_length] at h
    cases stackGetLast : List.getLast? cfg.stack with
    | none =>
      rw [stackGetLast] at h
      contradiction
    | some frame' =>
      rw [stackGetLast] at h
      cases heapLookup : cfg.heap.lookup frame'.regionId with
      | none =>
        dsimp at h
        rw [heapLookup] at h
        dsimp at h
        contradiction
      | some region' =>
        dsimp at h
        rw [heapLookup] at h
        dsimp at h
        have helper : (region'.status == Status.Open) = true := by
          have l2 : L2 cfg := vcfg.l2
          rw [List.getLast?_eq_some_iff] at stackGetLast
          obtain ⟨stack_last, stack_last_in_stack⟩ := stackGetLast
          have frame'_in_stack : frame' ∈ cfg.stack := by
            rw [stack_last_in_stack, List.mem_append]
            right
            exact List.mem_singleton_self frame'
          obtain ⟨region'', region''_in_heap, region''_status⟩ := l2 frame' frame'_in_stack
          rw [heapLookup, Option.some_inj] at region''_in_heap
          rw [← region''_in_heap] at region''_status
          rw [region''_status]
          rfl
        rw [if_pos helper, Option.some_inj] at h
        subst h
        have h1 : H1 cfg := vcfg.h1
        cases region_in_heap with
        | head =>
          have region'_in_old_heap : region' ∈ cfg.heap.regions := by
            exact List.mem_map_of_mem (AList.lookup_mem_entries heapLookup)
          exact h1 region' region'_in_old_heap
        | tail _ region_in_tail =>
          have region_in_old_heap : region ∈ cfg.heap.regions := by
            unfold RuntimeConfig.heap Heap.regions
            have kerase_sublist : (List.kerase frame'.regionId cfg.2.entries).Sublist (cfg.2.entries) := by
              apply List.kerase_sublist
            have sublist := List.Sublist.map (λ x => x.snd) kerase_sublist
            exact List.Sublist.mem region_in_tail sublist
          exact h1 region region_in_old_heap
  · rw [if_neg stack_length] at h
    contradiction

theorem exit_L1 : ValidConfig cfg →
  exit cfg = some cfg' →
  L1 cfg' := by
  intro vcfg h
  unfold exit at h
  unfold L1
  by_cases stack_length : cfg.stack.length >= 2
  · rw [if_pos stack_length] at h
    cases stackGetLast : List.getLast? cfg.stack with
    | none =>
      rw [stackGetLast] at h
      contradiction
    | some frame' =>
      rw [stackGetLast] at h
      cases heapLookup : cfg.heap.lookup frame'.regionId with
      | none =>
        dsimp at h
        rw [heapLookup] at h
        dsimp at h
        contradiction
      | some region' =>
        dsimp at h
        rw [heapLookup] at h
        dsimp at h
        have helper : (region'.status == Status.Open) = true := by
          have l2 : L2 cfg := vcfg.l2
          rw [List.getLast?_eq_some_iff] at stackGetLast
          obtain ⟨stack_last, stack_last_in_stack⟩ := stackGetLast
          have frame'_in_stack : frame' ∈ cfg.stack := by
            rw [stack_last_in_stack, List.mem_append]
            right
            exact List.mem_singleton_self frame'
          obtain ⟨region'', region''_in_heap, region''_status⟩ := l2 frame' frame'_in_stack
          rw [heapLookup, Option.some_inj] at region''_in_heap
          rw [← region''_in_heap] at region''_status
          rw [region''_status]
          rfl
        rw [if_pos helper, Option.some_inj] at h
        subst h
        have l1 : L1 cfg := vcfg.l1
        unfold L1
          RuntimeConfig.objectIds
        at l1
        have new_stack_objectIds_sublist_old_stack_objectIds :
          (Stack.objectIds (List.dropLast cfg.stack)).Sublist cfg.stack.objectIds := by
          have helper : ((List.dropLast cfg.stack).map Frame.objectIds).Sublist (cfg.stack.map Frame.objectIds) := by
            apply List.Sublist.map (λ x => x.objectIds) (List.dropLast_sublist cfg.stack)
          unfold Stack.objectIds
          dsimp
          rw [List.flatMap_id, List.flatMap_id]
          exact List.Sublist.flatten_sublist helper
        unfold RuntimeConfig.objectIds
        dsimp
        have new_heap_objectIds_perm_old_heap_objectIds :
          (Heap.objectIds (AList.insert frame'.regionId
            { bridgeObjectId := region'.bridgeObjectId,
              objMap := region'.objMap,
              status := Status.Closed
            } cfg.heap)).Perm (Heap.objectIds (cfg.heap)) := by
          apply List.Perm.flatten
          unfold Region.objectIds AList.insert
          dsimp
          obtain ⟨a, b, c, d, e, f⟩ := List.exists_of_kerase (
            List.mem_map_of_mem (AList.lookup_mem_entries heapLookup)
          )
          have a_eq_region' : a = region' := by
            have mem_a : ⟨frame'.regionId, a⟩ ∈ cfg.heap.entries := by
              rw [e, List.mem_append, List.mem_cons]
              right
              left
              dsimp
            exact List.NodupKeys.eq_of_mk_mem cfg.heap.nodupKeys mem_a (AList.lookup_mem_entries heapLookup)
          subst a
          rw [f, e, List.map_append, List.map_append, List.map_cons]
          dsimp
          exact List.perm_middle.symm
        obtain ⟨old_stack_objectIds_nodup, old_heap_objectIds_nodup, old_disjoint⟩ := List.nodup_append'.mp l1
        have new_stack_objectIds_nodup : (Stack.objectIds (List.dropLast cfg.stack)).Nodup := by
          exact List.Nodup.sublist new_stack_objectIds_sublist_old_stack_objectIds old_stack_objectIds_nodup
        have new_heap_objectIds_nodup : (Heap.objectIds (AList.insert frame'.regionId
            { bridgeObjectId := region'.bridgeObjectId,
              objMap := region'.objMap,
              status := Status.Closed
            } cfg.heap)).Nodup := by
          exact List.Nodup.perm old_heap_objectIds_nodup new_heap_objectIds_perm_old_heap_objectIds.symm
        have new_disjoint : (Stack.objectIds (List.dropLast cfg.stack)).Disjoint (Heap.objectIds (AList.insert frame'.regionId
            { bridgeObjectId := region'.bridgeObjectId,
              objMap := region'.objMap,
              status := Status.Closed
            } cfg.heap)) := by
          apply List.disjoint_of_subset_left (List.Sublist.subset new_stack_objectIds_sublist_old_stack_objectIds)
          apply (List.Perm.disjoint_right new_heap_objectIds_perm_old_heap_objectIds).mpr
          exact old_disjoint
        exact List.nodup_append'.mpr ⟨new_stack_objectIds_nodup, new_heap_objectIds_nodup, new_disjoint⟩
  · rw [if_neg stack_length] at h
    contradiction

theorem exit_H2 : ValidConfig cfg →
  exit cfg = some cfg' →
  H2 cfg' := by
  unfold H2
  intro vcfg h rid
  unfold exit at h
  by_cases stack_length : cfg.stack.length >= 2
  · rw [if_pos stack_length] at h
    cases stackGetLast : List.getLast? cfg.stack with
    | none =>
      rw [stackGetLast] at h
      contradiction
    | some frame' =>
      rw [stackGetLast] at h
      cases heapLookup : cfg.heap.lookup frame'.regionId with
      | none =>
        dsimp at h
        rw [heapLookup] at h
        dsimp at h
        contradiction
      | some region' =>
        dsimp at h
        rw [heapLookup] at h
        dsimp at h
        have helper : (region'.status == Status.Open) = true := by
          have l2 : L2 cfg := vcfg.l2
          rw [List.getLast?_eq_some_iff] at stackGetLast
          obtain ⟨stack_last, stack_last_in_stack⟩ := stackGetLast
          have frame'_in_stack : frame' ∈ cfg.stack := by
            rw [stack_last_in_stack, List.mem_append]
            right
            exact List.mem_singleton_self frame'
          obtain ⟨region'', region''_in_heap, region''_status⟩ := l2 frame' frame'_in_stack
          rw [heapLookup, Option.some_inj] at region''_in_heap
          rw [← region''_in_heap] at region''_status
          rw [region''_status]
          rfl
        rw [if_pos helper, Option.some_inj] at h
        subst h
        dsimp
        have h2 : H2 cfg := vcfg.h2

        -- stack.refs after dropLast is a sublist of the old stack.refs
        have stack_refs_sub : (Stack.refs (List.dropLast cfg.stack)).Sublist (Stack.refs cfg.stack) := by
          have : ((List.dropLast cfg.stack).map (λ f => Frame.refs f)).Sublist (cfg.stack.map (λ f => Frame.refs f)) := by
            apply List.Sublist.map (λ x => x.refs) (List.dropLast_sublist cfg.stack)
          unfold Stack.refs Frame.refs
          dsimp
          rw [List.flatMap_id, List.flatMap_id]
          exact List.Sublist.flatten_sublist this

        -- so the count of `Reference.RId rid` in the new stack ≤ old stack
        have stack_count_le := List.Sublist.countP_le stack_refs_sub (p := fun r => r == Reference.RId rid)

        -- heap.refs after the AList.insert is a permutation of the old heap.refs
        have heap_refs_perm :
          (Heap.refs (AList.insert frame'.regionId { region' with status := Status.Closed } cfg.heap)).Perm (Heap.refs cfg.heap) := by
          apply List.Perm.flatten
          unfold Region.refs AList.insert
          dsimp
          obtain ⟨a, b, c, d, e, f⟩ := List.exists_of_kerase (List.mem_map_of_mem (AList.lookup_mem_entries heapLookup))
          have a_eq_region' : a = region' := by
            have mem_a : ⟨frame'.regionId, a⟩ ∈ cfg.heap.entries := by
              rw [e, List.mem_append, List.mem_cons]
              right
              left
              dsimp
            exact List.NodupKeys.eq_of_mk_mem cfg.heap.nodupKeys mem_a (AList.lookup_mem_entries heapLookup)
          subst a
          rw [f, e, List.map_append, List.map_append, List.map_append, List.map_append, List.map_cons,]
          dsimp
          exact List.perm_middle.symm

        -- permutation gives equality of counts for the predicate
        have heap_count_eq := List.Perm.countP_eq heap_refs_perm (p := fun r => r == Reference.RId rid)

        -- assemble the inequality and finish via `h3`
        have new_le_old : (Stack.refs (List.dropLast cfg.stack)).count (Reference.RId rid) +
                         (Heap.refs (AList.insert frame'.regionId { region' with status := Status.Closed } cfg.heap)).count (Reference.RId rid)
                         ≤ cfg.stack.refs.count (Reference.RId rid) + cfg.heap.refs.count (Reference.RId rid) := by
          have A := stack_count_le
          have B := heap_count_eq
          rw [List.count_eq_countP, List.count_eq_countP, List.count_eq_countP, List.count_eq_countP]
          exact Nat.add_le_add A (Nat.le_of_eq B)

        exact Nat.le_trans new_le_old (h2 rid)
  · rw [if_neg stack_length] at h
    contradiction

theorem exit_H3 : ValidConfig cfg →
  exit cfg = some cfg' →
  H3 cfg' := by
  unfold H3
  intro vcfg h rid oid region region_in_new_heap region_contains_oid
  have h' := h
  unfold exit at h
  by_cases stack_length : cfg.stack.length >= 2
  · rw [if_pos stack_length] at h
    cases stackGetLast : List.getLast? cfg.stack with
    | none =>
      rw [stackGetLast] at h
      contradiction
    | some frame' =>
      rw [stackGetLast] at h
      cases heapLookup : cfg.heap.lookup frame'.regionId with
      | none =>
        dsimp at h
        rw [heapLookup] at h
        dsimp at h
        contradiction
      | some region' =>
        dsimp at h
        rw [heapLookup] at h
        dsimp at h
        have helper : (region'.status == Status.Open) = true := by
          have l2 : L2 cfg := vcfg.l2
          rw [List.getLast?_eq_some_iff] at stackGetLast
          obtain ⟨stack_last, stack_last_in_stack⟩ := stackGetLast
          have frame'_in_stack : frame' ∈ cfg.stack := by
            rw [stack_last_in_stack, List.mem_append]
            right
            exact List.mem_singleton_self frame'
          obtain ⟨region'', region''_in_heap, region''_status⟩ := l2 frame' frame'_in_stack
          rw [heapLookup, Option.some_inj] at region''_in_heap
          rw [← region''_in_heap] at region''_status
          rw [region''_status]
          rfl
        rw [if_pos helper, Option.some_inj] at h
        subst h
        have h3 : H3 cfg := vcfg.h3
        by_cases rid_eq_frame'_regionId : rid = frame'.regionId
        · subst rid
          have oid_in_region'_refs : Reference.OId oid ∈ region'.refs := by
            rw [exit_corollary_2 vcfg h' heapLookup region_in_new_heap]
            exact region_contains_oid
          replace h4 := h3 frame'.regionId oid region' heapLookup oid_in_region'_refs
          apply (exit_corollary_1 vcfg h' (Reference.OId oid)).mp
          exact h4
        · rw [AList.lookup_insert_ne rid_eq_frame'_regionId] at region_in_new_heap
          apply (exit_corollary_1 vcfg h' (Reference.OId oid)).mp
          exact h3 rid oid region region_in_new_heap region_contains_oid
  · rw [if_neg stack_length] at h
    contradiction

theorem exit_L2 : ValidConfig cfg →
  exit cfg = some cfg' →
  L2 cfg' := by
  intro vcfg h frame frame_in_new_stack
  unfold exit at h
  by_cases stack_length : cfg.stack.length >= 2
  · rw [if_pos stack_length] at h
    cases stackGetLast : List.getLast? cfg.stack with
    | none =>
      rw [stackGetLast] at h
      contradiction
    | some frame' =>
      rw [stackGetLast] at h
      cases heapLookup : cfg.heap.lookup frame'.regionId with
      | none =>
        dsimp at h
        rw [heapLookup] at h
        dsimp at h
        contradiction
      | some region' =>
        dsimp at h
        rw [heapLookup] at h
        dsimp at h
        have helper : (region'.status == Status.Open) = true := by
          have l2 : L2 cfg := vcfg.l2
          rw [List.getLast?_eq_some_iff] at stackGetLast
          obtain ⟨stack_last, stack_last_in_stack⟩ := stackGetLast
          have frame'_in_stack : frame' ∈ cfg.stack := by
            rw [stack_last_in_stack, List.mem_append]
            right
            exact List.mem_singleton_self frame'
          obtain ⟨region'', region''_in_heap, region''_status⟩ := l2 frame' frame'_in_stack
          rw [heapLookup, Option.some_inj] at region''_in_heap
          rw [← region''_in_heap] at region''_status
          rw [region''_status]
          rfl
        rw [if_pos helper, Option.some_inj] at h
        subst h
        dsimp at frame_in_new_stack
        obtain ⟨region_frame, region_frame_in_heap, region_frame_open⟩ :=
          vcfg.l2 frame (List.mem_of_mem_dropLast frame_in_new_stack)
        have frame_regionId_ne_frame'_regionId : frame.regionId ≠ frame'.regionId := by
          intro heq
          have frame_regionId_in_new_stack : frame.regionId ∈ (List.dropLast cfg.stack).map (λ f => f.regionId) := by
            apply List.mem_map_of_mem frame_in_new_stack
          have frame_regionId_nin_new_stack : frame.regionId ∉ (List.dropLast cfg.stack).map (λ f => f.regionId) := by
            have s1 : S1 cfg := vcfg.s1
            unfold S1 at s1
            have old_stack_nonempty : cfg.stack ≠ [] := by
              intro heq
              rw [heq] at stack_length
              contradiction
            have helper : cfg.stack = cfg.stack.dropLast ++ [cfg.stack.getLast old_stack_nonempty] := by
              exact (List.dropLast_append_getLast old_stack_nonempty).symm
            rw [List.getLast?_eq_getLast_of_ne_nil old_stack_nonempty, Option.some_inj] at stackGetLast
            rw [stackGetLast] at helper
            rw [helper, List.map_append] at s1
            dsimp at s1
            rw [List.nodup_append', List.disjoint_singleton] at s1
            rw [← heq] at s1
            exact s1.right.right
          contradiction
        rw [AList.lookup_insert_ne frame_regionId_ne_frame'_regionId]
        exact ⟨region_frame, region_frame_in_heap, region_frame_open⟩
  · rw [if_neg stack_length] at h
    contradiction

theorem exit_S2 : ValidConfig cfg →
  exit cfg = some cfg' →
  S1 cfg' := by
  intro vcfg h
  unfold exit at h
  unfold S1
  by_cases stack_length : cfg.stack.length >= 2
  · rw [if_pos stack_length] at h
    cases stackGetLast : List.getLast? cfg.stack with
    | none =>
      rw [stackGetLast] at h
      contradiction
    | some frame' =>
      rw [stackGetLast] at h
      cases heapLookup : cfg.heap.lookup frame'.regionId with
      | none =>
        dsimp at h
        rw [heapLookup] at h
        dsimp at h
        contradiction
      | some region' =>
        dsimp at h
        rw [heapLookup] at h
        dsimp at h
        have helper : (region'.status == Status.Open) = true := by
          have l2 : L2 cfg := vcfg.l2
          rw [List.getLast?_eq_some_iff] at stackGetLast
          obtain ⟨stack_last, stack_last_in_stack⟩ := stackGetLast
          have frame'_in_stack : frame' ∈ cfg.stack := by
            rw [stack_last_in_stack, List.mem_append]
            right
            exact List.mem_singleton_self frame'
          obtain ⟨region'', region''_in_heap, region''_status⟩ := l2 frame' frame'_in_stack
          rw [heapLookup, Option.some_inj] at region''_in_heap
          rw [← region''_in_heap] at region''_status
          rw [region''_status]
          rfl
        rw [if_pos helper, Option.some_inj] at h
        subst h
        have s1 : S1 cfg := vcfg.s1
        unfold S1 at s1
        have old_stack_nonempty : cfg.stack ≠ [] := by
          intro heq
          rw [heq] at stack_length
          contradiction
        have helper : cfg.stack = cfg.stack.dropLast ++ [cfg.stack.getLast old_stack_nonempty] := by
          exact (List.dropLast_append_getLast old_stack_nonempty).symm
        rw [List.getLast?_eq_getLast_of_ne_nil old_stack_nonempty, Option.some_inj] at stackGetLast
        rw [stackGetLast] at helper
        rw [helper, List.map_append] at s1
        dsimp at s1
        rw [List.nodup_append', List.disjoint_singleton] at s1
        exact s1.left
  · rw [if_neg stack_length] at h
    contradiction

theorem exit_S3 : ValidConfig cfg →
  exit cfg = some cfg' →
  S2 cfg' := by
  intro vcfg h
  unfold S2
  intro frame frame_in_new_stack ref ref_in_frame fid oid ref_eq ref_loc
  have h' := h
  unfold exit at h
  by_cases stack_length : cfg.stack.length >= 2
  · rw [if_pos stack_length] at h
    cases stackGetLast : List.getLast? cfg.stack with
    | none =>
      rw [stackGetLast] at h
      contradiction
    | some frame' =>
      rw [stackGetLast] at h
      cases heapLookup : cfg.heap.lookup frame'.regionId with
      | none =>
        dsimp at h
        rw [heapLookup] at h
        dsimp at h
        contradiction
      | some region' =>
        dsimp at h
        rw [heapLookup] at h
        dsimp at h
        have helper : (region'.status == Status.Open) = true := by
          have l2 : L2 cfg := vcfg.l2
          rw [List.getLast?_eq_some_iff] at stackGetLast
          obtain ⟨stack_last, stack_last_in_stack⟩ := stackGetLast
          have frame'_in_stack : frame' ∈ cfg.stack := by
            rw [stack_last_in_stack, List.mem_append]
            right
            exact List.mem_singleton_self frame'
          obtain ⟨region'', region''_in_heap, region''_status⟩ := l2 frame' frame'_in_stack
          rw [heapLookup, Option.some_inj] at region''_in_heap
          rw [← region''_in_heap] at region''_status
          rw [region''_status]
          rfl
        rw [if_pos helper, Option.some_inj] at h
        subst h
        have s2 : S2 cfg := vcfg.s2
        apply exit_corollary_3 vcfg h' ref at ref_loc
        have frame_in_old_stack : frame ∈ cfg.stackWithIndex := by
          unfold RuntimeConfig.stackWithIndex at frame_in_new_stack
          unfold RuntimeConfig.stackWithIndex
          dsimp at frame_in_new_stack
          apply List.mem_of_mem_dropLast_mapIdx at frame_in_new_stack
          exact frame_in_new_stack
        exact s2 frame frame_in_old_stack ref ref_in_frame fid oid ref_eq ref_loc
  · rw [if_neg stack_length] at h
    contradiction

theorem exit_S4 : ValidConfig cfg →
  exit cfg = some cfg' →
  S3 cfg' := by
  intro vcfg h
  unfold S3
  intro frame frame_in_new_stack ref ref_in_frame rid oid ref_eq ref_loc
  have h' := h
  unfold exit at h
  by_cases stack_length : cfg.stack.length >= 2
  · rw [if_pos stack_length] at h
    cases stackGetLast : List.getLast? cfg.stack with
    | none =>
      rw [stackGetLast] at h
      contradiction
    | some frame' =>
      rw [stackGetLast] at h
      cases heapLookup : cfg.heap.lookup frame'.regionId with
      | none =>
        dsimp at h
        rw [heapLookup] at h
        dsimp at h
        contradiction
      | some region' =>
        dsimp at h
        rw [heapLookup] at h
        dsimp at h
        have helper : (region'.status == Status.Open) = true := by
          have l2 : L2 cfg := vcfg.l2
          rw [List.getLast?_eq_some_iff] at stackGetLast
          obtain ⟨stack_last, stack_last_in_stack⟩ := stackGetLast
          have frame'_in_stack : frame' ∈ cfg.stack := by
            rw [stack_last_in_stack, List.mem_append]
            right
            exact List.mem_singleton_self frame'
          obtain ⟨region'', region''_in_heap, region''_status⟩ := l2 frame' frame'_in_stack
          rw [heapLookup, Option.some_inj] at region''_in_heap
          rw [← region''_in_heap] at region''_status
          rw [region''_status]
          rfl
        rw [if_pos helper, Option.some_inj] at h
        subst h
        have s4 : S3 cfg := vcfg.s3
        have frame_in_old_stack : frame ∈ cfg.stackWithIndex := by
          unfold RuntimeConfig.stackWithIndex at frame_in_new_stack
          unfold RuntimeConfig.stackWithIndex
          dsimp at frame_in_new_stack
          apply List.mem_of_mem_dropLast_mapIdx at frame_in_new_stack
          exact frame_in_new_stack
        apply (exit_corollary_1 vcfg h' ref).mpr at ref_loc
        obtain ⟨frame'', frame''_in_old_stack, frame''_regionId_eq_rid, frame''_index_le_frame_index⟩ :=
          s4 frame frame_in_old_stack ref ref_in_frame rid oid ref_eq ref_loc

        -- extract indices for `frame` (coming from dropLast) and `frame''` (in old stack)
        obtain ⟨n, n_lt, frame_eq⟩ := List.mem_mapIdx.mp frame_in_new_stack
        obtain ⟨k, k_lt, frame''_eq⟩ := List.mem_mapIdx.mp frame''_in_old_stack

        -- `frame.index = n` and `frame''.index = k`, so k ≤ n
        have k_le_n : k ≤ n := by
          unfold FrameWithIndex.index at frame''_index_le_frame_index
          rw [← frame_eq, ← frame''_eq] at frame''_index_le_frame_index
          exact frame''_index_le_frame_index

        -- stack is nonempty (we're in the branch `cfg.stack.length >= 2`)
        have old_stack_nonempty : cfg.stack ≠ [] := by
          intro heq; rw [heq] at stack_length; contradiction

        -- lengths: n < (cfg.stack.dropLast).length and thus k < (cfg.stack.dropLast).length
        have n_lt_dropLast : n < (cfg.stack.dropLast).length := n_lt
        have k_lt_dropLast : k < (cfg.stack.dropLast).length := Nat.lt_of_le_of_lt k_le_n n_lt_dropLast

        -- conclude `frame''` is still present in the new stackWithIndex (dropLast.mapIdx)
        have frame''_in_new_stack : frame'' ∈ (cfg.stack.dropLast).mapIdx (λ idx f => { f with index := idx }) := by
          apply List.mem_mapIdx.mpr
          use k
          constructor
          · rw [← List.getElem_dropLast k_lt_dropLast] at frame''_eq
            exact frame''_eq
        exact ⟨frame'', frame''_in_new_stack, frame''_regionId_eq_rid, frame''_index_le_frame_index⟩
  · rw [if_neg stack_length] at h
    contradiction

theorem exit_valid : ValidConfig cfg → exit cfg = some cfg' → ValidConfig cfg' := by
  intro vcfg h
  exact {
    l1 := exit_L1 vcfg h,
    l2 := exit_L2 vcfg h,
    h1 := exit_H1 vcfg h,
    h2 := exit_H2 vcfg h,
    h3 := exit_H3 vcfg h,
    s1 := exit_S2 vcfg h,
    s2 := exit_S3 vcfg h,
    s3 := exit_S4 vcfg h
  }
