import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Theorems
import Gc.Model.Mutation

theorem enter_corollary_4 : ValidConfig cfg →
  enter xf a cfg = some cfg' →
  cfg.stack.refs.Perm cfg'.stack.refs := by
  sorry

theorem enter_corollary_5 : ValidConfig cfg →
  enter xf a cfg = some cfg' →
  cfg.heap.refs.Perm cfg'.heap.refs := by
  sorry

theorem enter_corollary_6 : ValidConfig cfg →
  enter xf a cfg = some cfg' →
  cfg.heap.lookup rid = some region →
  cfg'.heap.lookup rid = some region' →
  region.refs = region'.refs := by
  sorry

theorem enter_corollary_7 : ∀ ref : Reference,
  ValidConfig cfg →
  enter xf a cfg = some cfg' →
  (ref.loc? cfg = loc ↔ ref.loc? cfg' = loc) := by
  sorry

theorem enter_L1 : ValidConfig cfg →
  enter xf a cfg = some cfg' →
  L1 cfg' := by
  intro vcfg h
  have h' := h
  unfold enter at h
  cases resolvexf: resolveFA xf cfg with
  | none =>
    rw [resolvexf] at h
    contradiction
  | some xfRef =>
    rw [resolvexf] at h
    dsimp at h
    cases xfRef with
    | OId _ =>
      contradiction
    | RId rid =>
      dsimp at h
      cases heapLookup : cfg.heap.lookup rid with
      | none =>
        rw [heapLookup] at h
        contradiction
      | some region =>
        rw [heapLookup] at h
        dsimp at h
        cases regionStatus : region.status with
        | Open =>
          rw [regionStatus] at h
          contradiction
        | Closed =>
          rw [regionStatus] at h
          rw [if_pos (by rfl)] at h
          rw [Option.some_inj] at h
          unfold L1
          have cfg_heap_objectIds_perm_cfg'_heap_objectIds : cfg.heap.objectIds.Perm cfg'.heap.objectIds := by
            rw [← h]
            apply List.Perm.flatten
            unfold Region.objectIds AList.insert
            dsimp
            obtain ⟨a, b, c, d, e, f⟩ := List.exists_of_kerase (
              List.mem_map_of_mem (AList.lookup_mem_entries heapLookup)
            )
            have a_eq_region' : a = region := by
              have mem_a : ⟨rid, a⟩ ∈ cfg.heap.entries := by
                rw [e, List.mem_append, List.mem_cons]
                right
                left
                dsimp
              exact List.NodupKeys.eq_of_mk_mem cfg.heap.nodupKeys mem_a (AList.lookup_mem_entries heapLookup)
            subst a
            rw [f, e, List.map_append, List.map_append, List.map_cons]
            dsimp
            exact List.perm_middle
          have cfg_stack_objectIds_perm_cfg'_stack_objectIds : cfg.stack.objectIds.Perm cfg'.stack.objectIds := by
            rw [← h]
            unfold RuntimeConfig.stack
            dsimp
            unfold Stack.objectIds
            rw [List.bind_eq_flatMap, List.bind_eq_flatMap, List.flatMap_id, List.flatMap_id, List.map_append]
            unfold Frame.objectIds
            dsimp
            rw [List.flatten_append]
            dsimp
            rw [List.append_nil]
          unfold RuntimeConfig.objectIds
          have cfg.objectIds_perm_cfg'_objectIds : cfg.objectIds.Perm cfg'.objectIds := by
            unfold RuntimeConfig.objectIds
            exact List.Perm.append cfg_stack_objectIds_perm_cfg'_stack_objectIds cfg_heap_objectIds_perm_cfg'_heap_objectIds
          exact List.Nodup.perm (vcfg.l1) cfg.objectIds_perm_cfg'_objectIds

theorem enter_L2 : ValidConfig cfg →
  enter xf a cfg = some cfg' →
  L2 cfg' := by
  intro vcfg h
  have h' := h
  unfold enter at h
  cases resolvexf: resolveFA xf cfg with
  | none =>
    rw [resolvexf] at h
    contradiction
  | some xfRef =>
    rw [resolvexf] at h
    dsimp at h
    cases xfRef with
    | OId _ =>
      contradiction
    | RId rid =>
      dsimp at h
      cases heapLookup : cfg.heap.lookup rid with
      | none =>
        rw [heapLookup] at h
        contradiction
      | some region =>
        rw [heapLookup] at h
        dsimp at h
        cases regionStatus : region.status with
        | Open =>
          rw [regionStatus] at h
          contradiction
        | Closed =>
          rw [regionStatus] at h
          rw [if_pos (by rfl)] at h
          rw [Option.some_inj] at h
          unfold L2
          have l2 := vcfg.l2
          intro frame frame_in_new_stack
          rw [← h] at frame_in_new_stack
          dsimp at frame_in_new_stack
          apply List.mem_append.mp at frame_in_new_stack
          cases frame_in_new_stack with
          | inl frame_in_old_stack =>
            obtain ⟨region', lookup_region', region'_open⟩ := l2 frame frame_in_old_stack
            use region'
            constructor
            · rw [← h]
              dsimp
              by_cases frame_regionId_ne_rid : frame.regionId ≠ rid
              · rw [AList.lookup_insert_ne frame_regionId_ne_rid]
                exact lookup_region'
              · have frame_regionId_eq_rid : frame.regionId = rid := by
                  dsimp at frame_regionId_ne_rid
                  exact not_not.mp frame_regionId_ne_rid
                subst rid
                rw [heapLookup, Option.some_inj] at lookup_region'
                rw [← lookup_region'] at region'_open
                rw [regionStatus] at region'_open
                contradiction
            · exact region'_open
          | inr frame_eq_new_frame =>
            rw [List.mem_singleton] at frame_eq_new_frame
            subst frame
            let region' := {region with status := Status.Open}
            use region'
            subst region'
            constructor
            · rw [← h]
              dsimp
              rw [AList.lookup_insert]
            · dsimp

theorem enter_H1 : ValidConfig cfg →
  enter xf a cfg = some cfg' →
  H1 cfg' := by
  intro vcfg h
  have h' := h
  unfold enter at h
  cases resolvexf: resolveFA xf cfg with
  | none =>
    rw [resolvexf] at h
    contradiction
  | some xfRef =>
    rw [resolvexf] at h
    dsimp at h
    cases xfRef with
    | OId _ =>
      contradiction
    | RId rid =>
      dsimp at h
      cases heapLookup : cfg.heap.lookup rid with
      | none =>
        rw [heapLookup] at h
        contradiction
      | some region =>
        rw [heapLookup] at h
        dsimp at h
        cases regionStatus : region.status with
        | Open =>
          rw [regionStatus] at h
          contradiction
        | Closed =>
          rw [regionStatus] at h
          rw [if_pos (by rfl)] at h
          rw [Option.some_inj] at h
          unfold H1
          have h1 := vcfg.h1
          intro region' region'_in_regions
          subst h
          cases region'_in_regions with
          | head =>
            have region_in_old_heap : region ∈ cfg.heap.regions := by
              exact List.mem_map_of_mem (AList.lookup_mem_entries heapLookup)
            exact h1 region region_in_old_heap
          | tail _ region_in_tail =>
            have region_in_old_heap : region' ∈ cfg.heap.regions := by
              unfold RuntimeConfig.heap Heap.regions
              have kerase_sublist : (List.kerase rid cfg.2.entries).Sublist (cfg.2.entries) := by
                apply List.kerase_sublist
              have sublist := List.Sublist.map (λ x => x.snd) kerase_sublist
              exact List.Sublist.mem region_in_tail sublist
            exact h1 region' region_in_old_heap

theorem enter_H2 : ValidConfig cfg →
  enter xf a cfg = some cfg' →
  H2 cfg' := by
  intro vcfg h
  have h' := h
  unfold enter at h
  cases resolvexf: resolveFA xf cfg with
  | none =>
    rw [resolvexf] at h
    contradiction
  | some xfRef =>
    rw [resolvexf] at h
    dsimp at h
    cases xfRef with
    | OId _ =>
      contradiction
    | RId rid =>
      dsimp at h
      cases heapLookup : cfg.heap.lookup rid with
      | none =>
        rw [heapLookup] at h
        contradiction
      | some region =>
        rw [heapLookup] at h
        dsimp at h
        cases regionStatus : region.status with
        | Open =>
          rw [regionStatus] at h
          contradiction
        | Closed =>
          rw [regionStatus] at h
          rw [if_pos (by rfl)] at h
          rw [Option.some_inj] at h
          unfold H2
          intro rid'
          have cfg_stack_refs_perm_cfg'_stack_refs : cfg.stack.refs.Perm cfg'.stack.refs := by
            rw [← h]
            unfold Stack.refs
            dsimp
            rw [List.flatMap_id, List.flatMap_id, List.map_append, List.flatten_append]
            simp [Frame.refs]
          have cfg'_heap_refs_perm_cfg_heap_refs : cfg'.heap.refs.Perm cfg.heap.refs := by
            rw [← h]
            dsimp
            apply List.Perm.flatten
            unfold Region.refs AList.insert
            dsimp
            obtain ⟨a, b, c, d, e, f⟩ := List.exists_of_kerase (List.mem_map_of_mem (AList.lookup_mem_entries heapLookup))
            have a_eq_region : a = region := by
              have mem_a : ⟨rid, a⟩ ∈ cfg.heap.entries := by
                rw [e, List.mem_append, List.mem_cons]
                right
                left
                dsimp
              exact List.NodupKeys.eq_of_mk_mem cfg.heap.nodupKeys mem_a (AList.lookup_mem_entries heapLookup)
            subst a
            rw [f, e, List.map_append, List.map_append, List.map_append, List.map_append, List.map_cons]
            dsimp
            exact List.perm_middle.symm
          have h2 := vcfg.h2 rid'
          rw [← cfg_stack_refs_perm_cfg'_stack_refs.count_eq, cfg'_heap_refs_perm_cfg_heap_refs.count_eq]
          exact h2

theorem enter_H3 : ValidConfig cfg →
  enter xf a cfg = some cfg' →
  H3 cfg' := by
  sorry

theorem enter_S1 : ValidConfig cfg →
  enter xf a cfg = some cfg' →
  S1 cfg' := by
  sorry

theorem enter_S2 : ValidConfig cfg →
  enter xf a cfg = some cfg' →
  S2 cfg' := by
  sorry

theorem enter_S3 : ValidConfig cfg →
  enter xf a cfg = some cfg' →
  S3 cfg' := by
  sorry

theorem enter_valid : ValidConfig cfg →
  enter xf a cfg = some cfg' →
  ValidConfig cfg' := by
  intro vcfg h
  exact {
    l1 := enter_L1 vcfg h,
    l2 := enter_L2 vcfg h,
    h1 := enter_H1 vcfg h,
    h2 := enter_H2 vcfg h,
    h3 := enter_H3 vcfg h,
    s1 := enter_S1 vcfg h,
    s2 := enter_S2 vcfg h,
    s3 := enter_S3 vcfg h
  }
