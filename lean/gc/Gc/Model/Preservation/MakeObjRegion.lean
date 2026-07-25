import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Theorems
import Gc.Model.Mutation

import Mathlib.Data.List.Infix

-- freshObjectId can't already be sitting inside some region's objMap.
theorem makeObjRegion_corollary_fresh_not_in_region {cfg : RuntimeConfig} {rid : RegionId} {region : Region} :
  cfg.heap.lookup rid = some region →
  cfg.freshObjectId ∉ region.objMap.keys := by
  intro hlookup hmem
  apply RuntimeConfig.freshObjectId_not_mem cfg
  unfold RuntimeConfig.objectIds Heap.objectIds Region.objectIds
  apply List.mem_append_right
  refine List.mem_flatten.mpr ⟨region.objMap.keys, ?_, hmem⟩
  exact List.mem_map_of_mem (f := fun e => e.2.objectIds) (AList.lookup_mem_entries hlookup)

theorem makeObjRegion_L1 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  L1 cfg' := by
  intro vcfg h
  have h' := h
  unfold makeObjRegion at h
  cases stackGetLast : cfg.stack.getLast? with
  | none => rw [stackGetLast] at h; contradiction
  | some frame =>
    rw [stackGetLast] at h
    dsimp at h
    cases heapLookup : cfg.heap.lookup frame.regionId with
    | none => rw [heapLookup] at h; contradiction
    | some region =>
      rw [heapLookup] at h
      dsimp at h
      cases regionStatus : region.status with
      | Closed => rw [regionStatus] at h; contradiction
      | Open =>
        rw [regionStatus] at h
        rw [if_pos (by rfl)] at h
        rw [Option.some_inj] at h
        unfold L1
        rw [← h]
        have l1 := vcfg.l1
        have fresh_not_in_region := makeObjRegion_corollary_fresh_not_in_region heapLookup
        set newRegion : Region :=
          { bridgeObjectId := region.bridgeObjectId,
            objMap := AList.insert cfg.freshObjectId ∅ region.objMap,
            status := region.status } with newRegion_def
        have newRegion_objectIds : newRegion.objectIds = cfg.freshObjectId :: region.objectIds := by
          show newRegion.objMap.entries.keys = cfg.freshObjectId :: region.objMap.entries.keys
          rw [newRegion_def]
          dsimp only
          rw [AList.entries_insert_of_notMem fresh_not_in_region, List.keys_cons]
        have stack_objectIds_eq :
            Stack.objectIds (cfg.stack.dropLast ++ [{ frame with
              varMap := AList.insert x (Reference.OId cfg.freshObjectId) frame.varMap }]) =
            cfg.stack.objectIds := by
          have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
            (List.dropLast_append_getLast? frame stackGetLast).symm
          conv_rhs => rw [stack_eq]
          unfold Stack.objectIds
          simp [Frame.objectIds]
        obtain ⟨regionVal, l1e, l2e, hnotmem, heq, hkerase⟩ :=
          List.exists_of_kerase (List.mem_keys_of_mem (AList.lookup_mem_entries heapLookup))
        have regionVal_eq_region : regionVal = region := by
          have mem_regionVal : (⟨frame.regionId, regionVal⟩ : Sigma (fun _ : RegionId => Region)) ∈ cfg.heap.entries := by
            rw [heq]
            exact List.mem_append_right _ List.mem_cons_self
          exact List.NodupKeys.eq_of_mk_mem cfg.heap.nodupKeys mem_regionVal (AList.lookup_mem_entries heapLookup)
        subst regionVal
        have heap_objectIds_eq :
            Heap.objectIds cfg.heap =
            List.flatten (l1e.map (fun e => e.2.objectIds)) ++
              (region.objectIds ++ List.flatten (l2e.map (fun e => e.2.objectIds))) := by
          unfold Heap.objectIds
          rw [heq, List.map_append, List.map_cons, List.flatten_append, List.flatten_cons]
        have heap'_objectIds_eq :
            Heap.objectIds (AList.insert frame.regionId newRegion cfg.heap) =
            cfg.freshObjectId ::
              (region.objectIds ++
                (List.flatten (l1e.map (fun e => e.2.objectIds)) ++
                  List.flatten (l2e.map (fun e => e.2.objectIds)))) := by
          unfold Heap.objectIds
          rw [AList.entries_insert, hkerase, List.map_cons, List.flatten_cons, newRegion_objectIds,
            List.map_append, List.flatten_append, List.cons_append]
        set LA := List.flatten (l1e.map (fun e => e.2.objectIds)) with LA_def
        set LB := List.flatten (l2e.map (fun e => e.2.objectIds)) with LB_def
        have swap_perm : (LA ++ (region.objectIds ++ LB)).Perm (region.objectIds ++ (LA ++ LB)) := by
          rw [← List.append_assoc, ← List.append_assoc]
          exact (List.perm_append_comm).append_right LB
        have step1 : (LA ++ (region.objectIds ++ LB) ++ [cfg.freshObjectId]).Perm
            (cfg.freshObjectId :: (region.objectIds ++ (LA ++ LB))) := by
          have p1 : (LA ++ (region.objectIds ++ LB) ++ [cfg.freshObjectId]).Perm
              (cfg.freshObjectId :: (LA ++ (region.objectIds ++ LB))) :=
            List.perm_append_singleton cfg.freshObjectId (LA ++ (region.objectIds ++ LB))
          exact p1.trans (swap_perm.cons cfg.freshObjectId)
        have objectIds_perm :
            ({ stack := cfg.stack.dropLast ++ [{ frame with
                varMap := AList.insert x (Reference.OId cfg.freshObjectId) frame.varMap }],
               heap := AList.insert frame.regionId newRegion cfg.heap } : RuntimeConfig).objectIds.Perm
              (cfg.objectIds ++ [cfg.freshObjectId]) := by
          unfold RuntimeConfig.objectIds
          dsimp
          rw [stack_objectIds_eq, heap'_objectIds_eq, heap_objectIds_eq, List.append_assoc]
          exact List.Perm.append_left cfg.stack.objectIds step1.symm
        have nodup_ext : (cfg.objectIds ++ [cfg.freshObjectId]).Nodup := by
          apply List.nodup_append.mpr
          refine ⟨l1, List.nodup_singleton _, ?_⟩
          intro a ha b hb heqb
          subst heqb
          rw [List.mem_singleton] at hb
          exact RuntimeConfig.freshObjectId_not_mem cfg (hb ▸ ha)
        exact nodup_ext.perm objectIds_perm.symm

theorem makeObjRegion_L2 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  L2 cfg' := by
  intro vcfg h
  have h' := h
  unfold makeObjRegion at h
  cases stackGetLast : cfg.stack.getLast? with
  | none => rw [stackGetLast] at h; contradiction
  | some frame =>
    rw [stackGetLast] at h
    dsimp at h
    cases heapLookup : cfg.heap.lookup frame.regionId with
    | none => rw [heapLookup] at h; contradiction
    | some region =>
      rw [heapLookup] at h
      dsimp at h
      cases regionStatus : region.status with
      | Closed => rw [regionStatus] at h; contradiction
      | Open =>
        rw [regionStatus] at h
        rw [if_pos (by rfl)] at h
        rw [Option.some_inj] at h
        unfold L2
        rw [← h]
        dsimp
        set newRegion : Region :=
          { bridgeObjectId := region.bridgeObjectId,
            objMap := AList.insert cfg.freshObjectId ∅ region.objMap,
            status := Status.Open } with newRegion_def
        have l2 := vcfg.l2
        intro frame'' hframe''
        rw [List.mem_append, List.mem_singleton] at hframe''
        by_cases heq : frame''.regionId = frame.regionId
        · refine ⟨newRegion, ?_, ?_⟩
          · rw [heq, AList.lookup_insert]
          · rw [newRegion_def]
        · obtain ⟨region', lookup_region', region'_open⟩ := l2 frame'' (by
            cases hframe'' with
            | inl hdrop => exact List.mem_of_mem_dropLast hdrop
            | inr heqframe =>
              subst heqframe
              exact absurd rfl heq)
          refine ⟨region', ?_, region'_open⟩
          rw [AList.lookup_insert_ne heq]
          exact lookup_region'

theorem makeObjRegion_H1 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  H1 cfg' := by
  intro vcfg h
  have h' := h
  unfold makeObjRegion at h
  cases stackGetLast : cfg.stack.getLast? with
  | none => rw [stackGetLast] at h; contradiction
  | some frame =>
    rw [stackGetLast] at h
    dsimp at h
    cases heapLookup : cfg.heap.lookup frame.regionId with
    | none => rw [heapLookup] at h; contradiction
    | some region =>
      rw [heapLookup] at h
      dsimp at h
      cases regionStatus : region.status with
      | Closed => rw [regionStatus] at h; contradiction
      | Open =>
        rw [regionStatus] at h
        rw [if_pos (by rfl)] at h
        rw [Option.some_inj] at h
        unfold H1
        rw [← h]
        dsimp
        have h1 := vcfg.h1
        set newRegion : Region :=
          { bridgeObjectId := region.bridgeObjectId,
            objMap := AList.insert cfg.freshObjectId ∅ region.objMap,
            status := Status.Open } with newRegion_def
        have region_mem : region ∈ cfg.heap.regions := List.mem_map_of_mem (AList.lookup_mem_entries heapLookup)
        intro region' hregion'
        unfold Heap.regions at hregion'
        rw [AList.entries_insert, List.map_cons] at hregion'
        rw [List.mem_cons] at hregion'
        cases hregion' with
        | inl heqregion =>
          subst heqregion
          rw [newRegion_def]
          dsimp
          rw [AList.mem_insert]
          exact Or.inr (h1 region region_mem)
        | inr hkeraseregion =>
          apply h1
          unfold Heap.regions
          exact (List.Sublist.map _ (List.kerase_sublist frame.regionId cfg.heap.entries)).mem hkeraseregion

theorem makeObjRegion_H2 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  H2 cfg' := by
  sorry

theorem makeObjRegion_H3 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  H3 cfg' := by
  sorry

theorem makeObjRegion_S1 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  S1 cfg' := by
  intro vcfg h
  have h' := h
  unfold makeObjRegion at h
  cases stackGetLast : cfg.stack.getLast? with
  | none => rw [stackGetLast] at h; contradiction
  | some frame =>
    rw [stackGetLast] at h
    dsimp at h
    cases heapLookup : cfg.heap.lookup frame.regionId with
    | none => rw [heapLookup] at h; contradiction
    | some region =>
      rw [heapLookup] at h
      dsimp at h
      cases regionStatus : region.status with
      | Closed => rw [regionStatus] at h; contradiction
      | Open =>
        rw [regionStatus] at h
        rw [if_pos (by rfl)] at h
        rw [Option.some_inj] at h
        unfold S1
        rw [← h]
        dsimp
        have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
          (List.dropLast_append_getLast? frame stackGetLast).symm
        have regionId_eq : (cfg.stack.dropLast ++ [{ frame with
            varMap := AList.insert x (Reference.OId cfg.freshObjectId) frame.varMap }]).map
              (fun f : Frame => f.regionId) = cfg.stack.map (fun f : Frame => f.regionId) := by
          conv_rhs => rw [stack_eq]
          rw [List.map_append, List.map_append]
          rfl
        rw [regionId_eq]
        exact vcfg.s1

theorem makeObjRegion_S2 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  S2 cfg' := by
  sorry

theorem makeObjRegion_S3 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  S3 cfg' := by
  sorry

theorem makeObjRegion_HS1 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  HS1 cfg' := by
  sorry

theorem makeObjRegion_valid : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  ValidConfig cfg' := by
  intro vcfg h
  exact {
    l1 := makeObjRegion_L1 vcfg h,
    l2 := makeObjRegion_L2 vcfg h,
    h1 := makeObjRegion_H1 vcfg h,
    h2 := makeObjRegion_H2 vcfg h,
    h3 := makeObjRegion_H3 vcfg h,
    s1 := makeObjRegion_S1 vcfg h,
    s2 := makeObjRegion_S2 vcfg h,
    s3 := makeObjRegion_S3 vcfg h,
    hs1 := makeObjRegion_HS1 vcfg h
  }
