import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Theorems
import Gc.Model.Mutation

theorem enter_corollary_8 :
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

theorem enter_corollary_9 : ValidConfig cfg →
  enter xf a cfg = some cfg' →
  ∀ oid, (Reference.OId oid).loc? cfg = (Reference.OId oid).loc? cfg' := by
  intro vcfg h oid
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
          subst h
          have l1 := vcfg.l1
          unfold Reference.loc?
          dsimp
          have stack_eq :
              cfg.stackWithIndex.findRev? (fun frame => (AList.keys frame.objMap).contains oid) =
              (RuntimeConfig.stackWithIndex
                { stack := cfg.stack ++ [{ regionId := rid, bridgeVar := a, objMap := ∅, varMap := ∅ }],
                  heap := AList.insert rid { bridgeObjectId := region.bridgeObjectId, objMap := region.objMap, status := Status.Open } cfg.heap
                }).findRev? (fun frame => (AList.keys frame.objMap).contains oid) := by
            unfold RuntimeConfig.stackWithIndex
            dsimp
            rw [List.mapIdx_concat, List.findRev?_eq_find?_reverse, List.findRev?_eq_find?_reverse, List.reverse_append]
            have newFrame_pred_false :
                ¬ (fun frame => (AList.keys frame.objMap).contains oid)
                  ({ regionId := rid, bridgeVar := a, objMap := ∅, varMap := ∅, index := cfg.stack.length } :
                    FrameWithIndex) := by
              dsimp
              decide
            have find_eq :
                List.find? (fun frame => (AList.keys frame.objMap).contains oid)
                  (({ regionId := rid, bridgeVar := a, objMap := ∅, varMap := ∅, index := cfg.stack.length } :
                      FrameWithIndex) ::
                    (List.mapIdx (fun idx frame => { toFrame := frame, index := idx }) cfg.stack).reverse) =
                List.find? (fun frame => (AList.keys frame.objMap).contains oid)
                  (List.mapIdx (fun idx frame => { toFrame := frame, index := idx }) cfg.stack).reverse :=
              List.find?_cons_of_neg newFrame_pred_false
            rw [List.reverse_singleton, List.singleton_append, find_eq]
          rw [stack_eq]
          cases heapLookup' : List.find? (fun x => (AList.keys x.snd.objMap).contains oid) cfg.heap.entries with
          | none =>
            have new_none :
                List.find? (fun x => (AList.keys x.snd.objMap).contains oid)
                  (⟨rid, { bridgeObjectId := region.bridgeObjectId, objMap := region.objMap, status := Status.Open }⟩ ::
                    List.kerase rid cfg.heap.entries) = none := by
              rw [List.find?_eq_none]
              rw [List.find?_eq_none] at heapLookup'
              intro x hx
              rw [List.mem_cons] at hx
              cases hx with
              | inl heq =>
                subst heq
                have := heapLookup' ⟨rid, region⟩ (AList.lookup_mem_entries heapLookup)
                dsimp at this
                exact this
              | inr hmem =>
                exact heapLookup' x ((List.kerase_sublist rid cfg.heap.entries).subset hmem)
            rw [new_none]
          | some ridregion =>
            obtain ⟨rid1, region1⟩ := ridregion
            have region1_mem : (⟨rid1, region1⟩ : Sigma (fun _ : RegionId => Region)) ∈ cfg.heap.entries :=
              List.mem_of_find?_eq_some heapLookup'
            have region1_pred := List.find?_some heapLookup'
            have region1_contains_oid : oid ∈ region1.objMap.keys := by
              dsimp at region1_pred
              exact List.contains_iff_mem.mp region1_pred
            by_cases rid1_eq_rid : rid1 = rid
            · subst rid1_eq_rid
              have region1_eq_region : region1 = region :=
                List.NodupKeys.eq_of_mk_mem cfg.heap.nodupKeys region1_mem (AList.lookup_mem_entries heapLookup)
              subst region1
              have entry_pred :
                  (fun x => (AList.keys x.snd.objMap).contains oid)
                    (⟨rid1, { bridgeObjectId := region.bridgeObjectId, objMap := region.objMap, status := Status.Open }⟩ :
                      Sigma (fun _ : RegionId => Region)) = true := by
                dsimp
                exact List.contains_iff_mem.mpr region1_contains_oid
              have find_eq :
                  List.find? (fun x => (AList.keys x.snd.objMap).contains oid)
                    (⟨rid1, { bridgeObjectId := region.bridgeObjectId, objMap := region.objMap, status := Status.Open }⟩ ::
                      List.kerase rid1 cfg.heap.entries) =
                  some (⟨rid1, { bridgeObjectId := region.bridgeObjectId, objMap := region.objMap, status := Status.Open }⟩ :
                    Sigma (fun _ : RegionId => Region)) :=
                List.find?_cons_of_pos entry_pred
              rw [find_eq]
              have key : ∀ s : Option FrameWithIndex,
                  (match s, (some ⟨rid1, region⟩ : Option (Sigma (fun _ : RegionId => Region))) with
                    | some frame, none => some (Location.Stk frame.index)
                    | none, some ⟨rid, _⟩ => some (Location.Rgn rid)
                    | _, _ => none) =
                  (match s,
                      (some ⟨rid1, { bridgeObjectId := region.bridgeObjectId, objMap := region.objMap, status := Status.Open }⟩ :
                        Option (Sigma (fun _ : RegionId => Region))) with
                    | some frame, none => some (Location.Stk frame.index)
                    | none, some ⟨rid, _⟩ => some (Location.Rgn rid)
                    | _, _ => none) := by
                intro s
                cases s <;> rfl
              exact key _
            · have front_false :
                  ¬ (fun x => (AList.keys x.snd.objMap).contains oid)
                      (⟨rid, { bridgeObjectId := region.bridgeObjectId, objMap := region.objMap, status := Status.Open }⟩ :
                        Sigma (fun _ : RegionId => Region)) := by
                dsimp
                intro hcontra
                exact rid1_eq_rid
                  (enter_corollary_8 l1 region1_mem region1_contains_oid
                    (AList.lookup_mem_entries heapLookup) (List.contains_iff_mem.mp hcontra))
              obtain ⟨b, l1e, l2e, _, entries_eq, kerase_eq⟩ :=
                List.exists_of_kerase (a := rid) (l := cfg.heap.entries)
                  (List.mem_keys_of_mem (AList.lookup_mem_entries heapLookup))
              have b_eq_region : b = region :=
                List.NodupKeys.eq_of_mk_mem cfg.heap.nodupKeys
                  (entries_eq ▸ List.mem_append_right l1e List.mem_cons_self) (AList.lookup_mem_entries heapLookup)
              have b_pred_false :
                  ¬ (fun x => (AList.keys x.snd.objMap).contains oid)
                    (⟨rid, b⟩ : Sigma (fun _ : RegionId => Region)) := by
                rw [b_eq_region]
                exact front_false
              have find_eq :
                  List.find? (fun x => (AList.keys x.snd.objMap).contains oid)
                    (⟨rid, { bridgeObjectId := region.bridgeObjectId, objMap := region.objMap, status := Status.Open }⟩ ::
                      List.kerase rid cfg.heap.entries) =
                  List.find? (fun x => (AList.keys x.snd.objMap).contains oid) (List.kerase rid cfg.heap.entries) :=
                List.find?_cons_of_neg front_false
              rw [find_eq, kerase_eq]
              rw [entries_eq, List.find?_append] at heapLookup'
              have find_eq2 :
                  List.find? (fun x => (AList.keys x.snd.objMap).contains oid) (⟨rid, b⟩ :: l2e) =
                  List.find? (fun x => (AList.keys x.snd.objMap).contains oid) l2e :=
                List.find?_cons_of_neg b_pred_false
              rw [find_eq2] at heapLookup'
              rw [List.find?_append, heapLookup']

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
