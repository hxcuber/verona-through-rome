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

-- cfg'.objectIds is cfg.objectIds with freshObjectId added (heap side gains it, stack side is
-- untouched by makeObjRegion). Reused by L1 (nodup transport) and HS1 (membership transport).
theorem makeObjRegion_corollary_objectIds_perm : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  cfg'.objectIds.Perm (cfg.objectIds ++ [cfg.freshObjectId]) := by
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
        rw [← h]
        exact objectIds_perm

theorem makeObjRegion_L1 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  L1 cfg' := by
  intro vcfg h
  have l1 := vcfg.l1
  have objectIds_perm := makeObjRegion_corollary_objectIds_perm vcfg h
  unfold L1
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

-- cfg'.heap.refs is a permutation of cfg.heap.refs: makeObjRegion only ever inserts an *empty*
-- object into the mutated region's objMap, so no ref is gained or lost heap-side, only reordered
-- by the kerase-based AList.insert at the (already-present) region key. Reused by H2 and HS1.
theorem makeObjRegion_corollary_heap_refs_perm : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  cfg'.heap.refs.Perm cfg.heap.refs := by
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
        have fresh_not_in_region := makeObjRegion_corollary_fresh_not_in_region heapLookup
        set newRegion : Region :=
          { bridgeObjectId := region.bridgeObjectId,
            objMap := AList.insert cfg.freshObjectId ∅ region.objMap,
            status := Status.Open } with newRegion_def
        have newRegion_refs_eq : newRegion.refs = region.refs := by
          show (AList.insert cfg.freshObjectId ∅ region.objMap).entries.map (·.2) >>= Object.refs = region.refs
          rw [AList.entries_insert_of_notMem fresh_not_in_region]
          simp [Object.refs, Region.refs, List.bind_eq_flatMap]
        have heap'_refs_perm : (Heap.refs (AList.insert frame.regionId newRegion cfg.heap)).Perm cfg.heap.refs := by
          apply List.Perm.flatten
          obtain ⟨regionVal2, l1e2, l2e2, hnotmem2, heq2, hkerase2⟩ :=
            List.exists_of_kerase (List.mem_keys_of_mem (AList.lookup_mem_entries heapLookup))
          have regionVal2_eq_region : regionVal2 = region := by
            have mem_regionVal2 : (⟨frame.regionId, regionVal2⟩ : Sigma (fun _ : RegionId => Region)) ∈ cfg.heap.entries := by
              rw [heq2]
              exact List.mem_append_right _ List.mem_cons_self
            exact List.NodupKeys.eq_of_mk_mem cfg.heap.nodupKeys mem_regionVal2 (AList.lookup_mem_entries heapLookup)
          subst regionVal2
          unfold AList.insert
          dsimp
          rw [hkerase2]
          simp only [heq2, List.map_append, List.map_cons]
          rw [newRegion_refs_eq]
          exact List.perm_middle.symm
        rw [← h]
        exact heap'_refs_perm

theorem makeObjRegion_H2 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  H2 cfg' := by
  intro vcfg h
  have h' := h
  have heap_refs_perm := makeObjRegion_corollary_heap_refs_perm vcfg h
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
        unfold H2
        intro rid
        rw [heap_refs_perm.count_eq]
        rw [← h]
        dsimp
        have h2 := vcfg.h2 rid
        have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
          (List.dropLast_append_getLast? frame stackGetLast).symm
        have newFrame_refs_le : (Frame.refs { frame with
            varMap := AList.insert x (Reference.OId cfg.freshObjectId) frame.varMap }).count
              (Reference.RId rid) ≤ frame.refs.count (Reference.RId rid) := by
          unfold Frame.refs
          dsimp
          rw [List.count_append, List.count_append]
          apply Nat.add_le_add_left
          rw [List.count_cons]
          have hne : (Reference.OId cfg.freshObjectId == Reference.RId rid) = false := rfl
          rw [hne]
          dsimp
          exact ((List.kerase_sublist x frame.varMap.entries).map (·.2)).count_le (Reference.RId rid)
        have stack_refs_le : (Stack.refs (cfg.stack.dropLast ++ [{ frame with
            varMap := AList.insert x (Reference.OId cfg.freshObjectId) frame.varMap }])).count
              (Reference.RId rid) ≤ cfg.stack.refs.count (Reference.RId rid) := by
          have split1 : Stack.refs (cfg.stack.dropLast ++ [{ frame with
              varMap := AList.insert x (Reference.OId cfg.freshObjectId) frame.varMap }]) =
              Stack.refs cfg.stack.dropLast ++ (Frame.refs { frame with
                varMap := AList.insert x (Reference.OId cfg.freshObjectId) frame.varMap }) := by
            unfold Stack.refs
            rw [List.bind_eq_flatMap, List.bind_eq_flatMap, List.flatMap_id, List.flatMap_id,
              List.map_append, List.flatten_append]
            simp
          have split2 : cfg.stack.refs = Stack.refs cfg.stack.dropLast ++ frame.refs := by
            conv_lhs => rw [stack_eq]
            unfold Stack.refs
            rw [List.bind_eq_flatMap, List.bind_eq_flatMap, List.flatMap_id, List.flatMap_id,
              List.map_append, List.flatten_append]
            simp
          rw [split1, split2, List.count_append, List.count_append]
          exact Nat.add_le_add_left newFrame_refs_le _
        exact Nat.le_trans (Nat.add_le_add_right stack_refs_le _) h2

-- An oid can be found in at most one region's objMap (stated over bare L1, so it's usable on cfg
-- before cfg''s own validity is established).
theorem makeObjRegion_corollary_region_unique
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
theorem makeObjRegion_corollary_loc_match_eq (o1 : Option FrameWithIndex)
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

-- The heart of H3/S2/S3: for any oid other than the freshly-allocated one, an OId reference
-- resolves to the exact same Location before and after makeObjRegion. The stack side is
-- unconditionally unaffected (only the last frame's varMap changes, never any objMap), so it
-- reduces to a case split on whether the frame's *own* objMap already contains oid. The heap side
-- genuinely reorders (the mutated region's entry moves to the front via the AList.insert kerase),
-- so it needs the region-uniqueness fact above to show find? still lands on the same region.
theorem makeObjRegion_corollary_loc_eq : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  ∀ oid, oid ≠ cfg.freshObjectId →
    (Reference.OId oid).loc? cfg = (Reference.OId oid).loc? cfg' := by
  intro vcfg h oid hne
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
        have l1 := vcfg.l1
        have fresh_not_in_region := makeObjRegion_corollary_fresh_not_in_region heapLookup
        rw [← h]
        set newRegion : Region :=
          { bridgeObjectId := region.bridgeObjectId,
            objMap := AList.insert cfg.freshObjectId ∅ region.objMap,
            status := Status.Open } with newRegion_def
        have newRegion_keys_eq : newRegion.objMap.keys = cfg.freshObjectId :: region.objMap.keys := by
          rw [newRegion_def]
          dsimp only
          rw [AList.keys_insert, List.erase_of_not_mem fresh_not_in_region]
        have newRegion_contains_eq :
            (newRegion.objMap.keys).contains oid = (region.objMap.keys).contains oid := by
          rw [newRegion_keys_eq]
          simp [hne]
        set newFrame : Frame :=
          { regionId := frame.regionId, bridgeVar := frame.bridgeVar, objMap := frame.objMap,
            varMap := AList.insert x (Reference.OId cfg.freshObjectId) frame.varMap } with newFrame_def
        set cfgLit : RuntimeConfig :=
          { stack := cfg.stack.dropLast ++ [newFrame], heap := AList.insert frame.regionId newRegion cfg.heap }
          with cfgLit_def
        have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
          (List.dropLast_append_getLast? frame stackGetLast).symm
        have stack_h1_map_eq :
            (cfg.stackWithIndex.findRev? (fun f => (AList.keys f.objMap).contains oid)).map
              FrameWithIndex.index =
            (cfgLit.stackWithIndex.findRev?
                (fun f => (AList.keys f.objMap).contains oid)).map FrameWithIndex.index := by
          rw [cfgLit_def]
          unfold RuntimeConfig.stackWithIndex
          dsimp
          conv_lhs => rw [stack_eq]
          rw [List.mapIdx_concat, List.mapIdx_concat, List.findRev?_eq_find?_reverse,
            List.findRev?_eq_find?_reverse, List.reverse_append, List.reverse_append,
            List.reverse_singleton, List.reverse_singleton, List.singleton_append, List.singleton_append]
          by_cases hb : (AList.keys frame.objMap).contains oid
          · have find_eqL :
                List.find? (fun f => (AList.keys f.objMap).contains oid)
                  (({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex) ::
                    (List.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex))
                      cfg.stack.dropLast).reverse) =
                some ({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex) :=
              List.find?_cons_of_pos hb
            have find_eqR :
                List.find? (fun f => (AList.keys f.objMap).contains oid)
                  (({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex) ::
                    (List.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex))
                      cfg.stack.dropLast).reverse) =
                some ({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex) :=
              List.find?_cons_of_pos hb
            rw [find_eqL, find_eqR]
            rfl
          · have hbL : ¬ (AList.keys ({ frame with index := cfg.stack.dropLast.length } :
                FrameWithIndex).objMap).contains oid = true := hb
            have hbR : ¬ (AList.keys ({ newFrame with
                index := cfg.stack.dropLast.length } : FrameWithIndex).objMap).contains oid = true := hb
            have find_eqL :
                List.find? (fun f => (AList.keys f.objMap).contains oid)
                  (({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex) ::
                    (List.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex))
                      cfg.stack.dropLast).reverse) =
                List.find? (fun f => (AList.keys f.objMap).contains oid)
                  (List.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex))
                    cfg.stack.dropLast).reverse :=
              List.find?_cons_of_neg hbL
            have find_eqR :
                List.find? (fun f => (AList.keys f.objMap).contains oid)
                  (({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex) ::
                    (List.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex))
                      cfg.stack.dropLast).reverse) =
                List.find? (fun f => (AList.keys f.objMap).contains oid)
                  (List.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex))
                    cfg.stack.dropLast).reverse :=
              List.find?_cons_of_neg hbR
            rw [find_eqL, find_eqR]
        have heap_h2_map_eq :
            (cfg.heap.entries.find? (fun p => (AList.keys p.snd.objMap).contains oid)).map Sigma.fst =
            (cfgLit.heap.entries.find?
              (fun p => (AList.keys p.snd.objMap).contains oid)).map Sigma.fst := by
          rw [cfgLit_def]
          obtain ⟨regionVal3, l1e3, l2e3, hnotmem3, heq3, hkerase3⟩ :=
            List.exists_of_kerase (List.mem_keys_of_mem (AList.lookup_mem_entries heapLookup))
          have regionVal3_eq_region : regionVal3 = region := by
            have mem_regionVal3 : (⟨frame.regionId, regionVal3⟩ : Sigma (fun _ : RegionId => Region)) ∈
                cfg.heap.entries := by
              rw [heq3]
              exact List.mem_append_right _ List.mem_cons_self
            exact List.NodupKeys.eq_of_mk_mem cfg.heap.nodupKeys mem_regionVal3
              (AList.lookup_mem_entries heapLookup)
          subst regionVal3
          rw [AList.entries_insert, hkerase3]
          have region_mem_cfg : (⟨frame.regionId, region⟩ : Sigma (fun _ : RegionId => Region)) ∈
              cfg.heap.entries := heq3 ▸ List.mem_append_right _ List.mem_cons_self
          by_cases hb2 : (AList.keys region.objMap).contains oid
          · have hb2' : (AList.keys newRegion.objMap).contains oid := by
              rw [newRegion_contains_eq]; exact hb2
            have find_eqR2 :
                List.find? (fun p => (AList.keys p.snd.objMap).contains oid)
                  ((⟨frame.regionId, newRegion⟩ : Sigma (fun _ : RegionId => Region)) :: (l1e3 ++ l2e3)) =
                some (⟨frame.regionId, newRegion⟩ : Sigma (fun _ : RegionId => Region)) :=
              List.find?_cons_of_pos hb2'
            rw [find_eqR2]
            have find_eqL :
                cfg.heap.entries.find? (fun p => (AList.keys p.snd.objMap).contains oid) =
                some (⟨frame.regionId, region⟩ : Sigma (fun _ : RegionId => Region)) := by
              apply List.find?_eq_some_of_unique region_mem_cfg hb2
              intro y hy hpy
              obtain ⟨rid_y, region_y⟩ := y
              have rid_y_eq : rid_y = frame.regionId :=
                makeObjRegion_corollary_region_unique l1 hy (List.contains_iff_mem.mp hpy)
                  region_mem_cfg (List.contains_iff_mem.mp hb2)
              subst rid_y_eq
              have region_y_eq : region_y = region :=
                List.NodupKeys.eq_of_mk_mem cfg.heap.nodupKeys hy region_mem_cfg
              rw [region_y_eq]
            rw [find_eqL]
            rfl
          · have hb2' : ¬ (AList.keys newRegion.objMap).contains oid := by
              rw [newRegion_contains_eq]; exact hb2
            have find_eqR2 :
                List.find? (fun p => (AList.keys p.snd.objMap).contains oid)
                  ((⟨frame.regionId, newRegion⟩ : Sigma (fun _ : RegionId => Region)) :: (l1e3 ++ l2e3)) =
                List.find? (fun p => (AList.keys p.snd.objMap).contains oid) (l1e3 ++ l2e3) :=
              List.find?_cons_of_neg hb2'
            rw [find_eqR2]
            have find_eqL :
                cfg.heap.entries.find? (fun p => (AList.keys p.snd.objMap).contains oid) =
                List.find? (fun p => (AList.keys p.snd.objMap).contains oid) (l1e3 ++ l2e3) := by
              rw [heq3]
              clear hb2' region_mem_cfg heq3 hkerase3 find_eqR2 hnotmem3
              induction l1e3 with
              | nil =>
                dsimp
                exact List.find?_cons_of_neg hb2
              | cons a as ih =>
                dsimp
                by_cases hpa : (AList.keys a.snd.objMap).contains oid
                · have find_eqA :
                      List.find? (fun p => (AList.keys p.snd.objMap).contains oid)
                        (a :: (as ++ (⟨frame.regionId, region⟩ : Sigma (fun _ : RegionId => Region)) :: l2e3)) =
                      some a := List.find?_cons_of_pos hpa
                  have find_eqB :
                      List.find? (fun p => (AList.keys p.snd.objMap).contains oid) (a :: (as ++ l2e3)) =
                      some a := List.find?_cons_of_pos hpa
                  rw [find_eqA, find_eqB]
                · have find_eqA :
                      List.find? (fun p => (AList.keys p.snd.objMap).contains oid)
                        (a :: (as ++ (⟨frame.regionId, region⟩ : Sigma (fun _ : RegionId => Region)) :: l2e3)) =
                      List.find? (fun p => (AList.keys p.snd.objMap).contains oid)
                        (as ++ (⟨frame.regionId, region⟩ : Sigma (fun _ : RegionId => Region)) :: l2e3) :=
                    List.find?_cons_of_neg hpa
                  have find_eqB :
                      List.find? (fun p => (AList.keys p.snd.objMap).contains oid) (a :: (as ++ l2e3)) =
                      List.find? (fun p => (AList.keys p.snd.objMap).contains oid) (as ++ l2e3) :=
                    List.find?_cons_of_neg hpa
                  rw [find_eqA, find_eqB]
                  exact ih
            rw [find_eqL]
        unfold Reference.loc?
        dsimp
        have step1 := makeObjRegion_corollary_loc_match_eq
          (cfg.stackWithIndex.findRev? (fun f => (AList.keys f.objMap).contains oid))
          (cfg.heap.entries.find? (fun p => (AList.keys p.snd.objMap).contains oid))
        have step2 := makeObjRegion_corollary_loc_match_eq
          (cfgLit.stackWithIndex.findRev? (fun f => (AList.keys f.objMap).contains oid))
          (cfgLit.heap.entries.find? (fun p => (AList.keys p.snd.objMap).contains oid))
        rw [stack_h1_map_eq, heap_h2_map_eq] at step1
        exact step1.trans step2.symm

theorem makeObjRegion_H3 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  H3 cfg' := by
  intro vcfg h
  have h' := h
  have hs1 := vcfg.hs1
  have h3 := vcfg.h3
  have loc_eq := makeObjRegion_corollary_loc_eq vcfg h
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
        have fresh_not_in_region := makeObjRegion_corollary_fresh_not_in_region heapLookup
        set newRegion : Region :=
          { bridgeObjectId := region.bridgeObjectId,
            objMap := AList.insert cfg.freshObjectId ∅ region.objMap,
            status := Status.Open } with newRegion_def
        have newRegion_refs_eq : newRegion.refs = region.refs := by
          show (AList.insert cfg.freshObjectId ∅ region.objMap).entries.map (·.2) >>= Object.refs = region.refs
          rw [AList.entries_insert_of_notMem fresh_not_in_region]
          simp [Object.refs, Region.refs, List.bind_eq_flatMap]
        have oid_ne_fresh_of_region_mem : ∀ oid1 rid1 region1, cfg.heap.lookup rid1 = some region1 →
            Reference.OId oid1 ∈ region1.refs → oid1 ≠ cfg.freshObjectId := by
          intro oid1 rid1 region1 hlookup1 hmem1 heq
          apply RuntimeConfig.freshObjectId_not_mem cfg
          rw [← heq]
          apply hs1
          apply List.mem_append_right
          unfold Heap.refs
          rw [List.bind_eq_flatMap, List.mem_flatMap]
          exact ⟨region1, List.mem_map_of_mem (AList.lookup_mem_entries hlookup1), hmem1⟩
        have heap_eq : cfg'.heap = AList.insert frame.regionId newRegion cfg.heap :=
          (congrArg RuntimeConfig.heap h).symm
        unfold H3
        intro rid0 oid0 region0 hlookup0 href0
        rw [heap_eq] at hlookup0
        by_cases hrideq : rid0 = frame.regionId
        · subst hrideq
          rw [AList.lookup_insert, Option.some_inj] at hlookup0
          subst hlookup0
          rw [newRegion_refs_eq] at href0
          have h3fact := h3 frame.regionId oid0 region heapLookup href0
          have oid_ne_fresh := oid_ne_fresh_of_region_mem oid0 frame.regionId region heapLookup href0
          rw [← loc_eq oid0 oid_ne_fresh]
          exact h3fact
        · rw [AList.lookup_insert_ne hrideq] at hlookup0
          have h3fact := h3 rid0 oid0 region0 hlookup0 href0
          have oid_ne_fresh := oid_ne_fresh_of_region_mem oid0 rid0 region0 hlookup0 href0
          rw [← loc_eq oid0 oid_ne_fresh]
          exact h3fact

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

-- The freshly-created object always resolves into the *heap*, at the region the current top
-- frame belongs to (never onto the stack, since the frame's objMap is untouched). Reused by both
-- S2 (to derive a contradiction, since the fresh ref can never resolve to a Stk location) and S3.
theorem makeObjRegion_corollary_loc_fresh : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  ∃ frame, cfg.stack.getLast? = some frame ∧
    (Reference.OId cfg.freshObjectId).loc? cfg' = some (Location.Rgn frame.regionId) := by
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
        refine ⟨frame, ?_, ?_⟩
        · rfl
        have fresh_not_in_region := makeObjRegion_corollary_fresh_not_in_region heapLookup
        rw [← h]
        set newRegion : Region :=
          { bridgeObjectId := region.bridgeObjectId,
            objMap := AList.insert cfg.freshObjectId ∅ region.objMap,
            status := Status.Open } with newRegion_def
        have newRegion_keys_eq : newRegion.objMap.keys = cfg.freshObjectId :: region.objMap.keys := by
          rw [newRegion_def]
          dsimp only
          rw [AList.keys_insert, List.erase_of_not_mem fresh_not_in_region]
        set newFrame : Frame :=
          { regionId := frame.regionId, bridgeVar := frame.bridgeVar, objMap := frame.objMap,
            varMap := AList.insert x (Reference.OId cfg.freshObjectId) frame.varMap } with newFrame_def
        set cfgLit : RuntimeConfig :=
          { stack := cfg.stack.dropLast ++ [newFrame], heap := AList.insert frame.regionId newRegion cfg.heap }
          with cfgLit_def
        have fresh_not_in_any_frame : ∀ f ∈ cfg.stack, cfg.freshObjectId ∉ f.objMap.keys := by
          intro f hf hmem
          apply RuntimeConfig.freshObjectId_not_mem cfg
          unfold RuntimeConfig.objectIds Stack.objectIds Frame.objectIds
          rw [List.bind_eq_flatMap, List.flatMap_id, List.mem_append, List.mem_flatten]
          exact Or.inl ⟨f.objMap.keys, List.mem_map_of_mem hf, hmem⟩
        have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
          (List.dropLast_append_getLast? frame stackGetLast).symm
        have frame_mem : frame ∈ cfg.stack := stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self frame)
        have dropLast_h1_none :
            List.find? (fun f => (AList.keys f.objMap).contains cfg.freshObjectId)
              (List.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex))
                cfg.stack.dropLast).reverse = none := by
          rw [List.find?_eq_none]
          intro f hf
          rw [List.mem_reverse] at hf
          obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hf
          intro hc
          apply fresh_not_in_any_frame cfg.stack.dropLast[n]
            (List.mem_of_mem_dropLast (List.mem_iff_getElem.mpr ⟨n, hn, rfl⟩))
          rw [← hfeq] at hc
          dsimp at hc
          exact List.contains_iff_mem.mp hc
        have h1_none :
            cfgLit.stackWithIndex.findRev?
              (fun f => (AList.keys f.objMap).contains cfg.freshObjectId) = none := by
          rw [cfgLit_def]
          unfold RuntimeConfig.stackWithIndex
          dsimp
          rw [List.mapIdx_concat, List.findRev?_eq_find?_reverse, List.reverse_append,
            List.reverse_singleton, List.singleton_append]
          have hnewFrame_false : ¬ (AList.keys ({ newFrame with
                index := cfg.stack.dropLast.length } : FrameWithIndex).objMap).contains
              cfg.freshObjectId = true := by
            dsimp
            intro hc
            exact fresh_not_in_any_frame frame frame_mem (List.contains_iff_mem.mp hc)
          have find_eq :
              List.find? (fun f => (AList.keys f.objMap).contains cfg.freshObjectId)
                (({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex) ::
                  (List.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex))
                    cfg.stack.dropLast).reverse) =
              List.find? (fun f => (AList.keys f.objMap).contains cfg.freshObjectId)
                (List.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex))
                  cfg.stack.dropLast).reverse :=
            List.find?_cons_of_neg hnewFrame_false
          rw [find_eq, dropLast_h1_none]
        have h2_some :
            cfgLit.heap.entries.find?
              (fun p => (AList.keys p.snd.objMap).contains cfg.freshObjectId) =
            some (⟨frame.regionId, newRegion⟩ : Sigma (fun _ : RegionId => Region)) := by
          rw [cfgLit_def]
          dsimp
          have hpos : (AList.keys newRegion.objMap).contains cfg.freshObjectId = true := by
            rw [newRegion_keys_eq]
            simp
          exact List.find?_cons_of_pos hpos
        unfold Reference.loc?
        dsimp
        rw [h1_none, h2_some]

theorem makeObjRegion_S2 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  S2 cfg' := by
  intro vcfg h
  have h' := h
  have hs1 := vcfg.hs1
  have s2 := vcfg.s2
  have loc_eq := makeObjRegion_corollary_loc_eq vcfg h
  obtain ⟨frame0, hframe0getLast, loc_fresh0⟩ := makeObjRegion_corollary_loc_fresh vcfg h
  unfold makeObjRegion at h
  cases stackGetLast : cfg.stack.getLast? with
  | none => rw [stackGetLast] at h; contradiction
  | some frame =>
    rw [stackGetLast] at h hframe0getLast
    rw [Option.some_inj] at hframe0getLast
    subst frame0
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
        set newFrame : Frame :=
          { regionId := frame.regionId, bridgeVar := frame.bridgeVar, objMap := frame.objMap,
            varMap := AList.insert x (Reference.OId cfg.freshObjectId) frame.varMap } with newFrame_def
        have newFrame_refs_mem : ∀ ref, ref ∈ newFrame.refs →
            ref = Reference.OId cfg.freshObjectId ∨ ref ∈ frame.refs := by
          intro ref href
          rw [newFrame_def] at href
          unfold Frame.refs at href
          dsimp at href
          rw [List.mem_append] at href
          rcases href with hobjmap | hvarmap
          · right
            exact List.mem_append_left _ hobjmap
          · rw [List.mem_cons] at hvarmap
            rcases hvarmap with heqref | hker
            · left; exact heqref
            · right
              unfold Frame.refs
              apply List.mem_append_right
              exact (List.kerase_sublist x frame.varMap.entries).map (·.2) |>.subset hker
        have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
          (List.dropLast_append_getLast? frame stackGetLast).symm
        have frame_mem : frame ∈ cfg.stack := stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self frame)
        have stackWithIndex_eq_cfg :
            cfg.stackWithIndex =
              cfg.stack.dropLast.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) ++
                [({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex)] := by
          unfold RuntimeConfig.stackWithIndex
          conv_lhs => rw [stack_eq]
          rw [List.mapIdx_concat]
        have stack_eq' : cfg'.stack = cfg.stack.dropLast ++ [newFrame] := (congrArg RuntimeConfig.stack h).symm
        have stackWithIndex_eq :
            cfg'.stackWithIndex =
              cfg.stack.dropLast.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) ++
                [({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex)] := by
          unfold RuntimeConfig.stackWithIndex
          rw [stack_eq', List.mapIdx_concat]
        unfold S2
        intro frame' hframe' ref href fid' oid hrefeq hlocEq
        subst hrefeq
        rw [stackWithIndex_eq, List.mem_append, List.mem_singleton] at hframe'
        rcases hframe' with hold | hnew
        · have hframe'_in_cfg : frame' ∈ cfg.stackWithIndex := by
            rw [stackWithIndex_eq_cfg]
            exact List.mem_append_left _ hold
          have href_in_cfg_refs : Reference.OId oid ∈ cfg.refs := by
            obtain ⟨n, n_lt_len, f_eq⟩ := List.mem_mapIdx.mp hframe'_in_cfg
            apply List.mem_append_left
            unfold Stack.refs
            rw [List.bind_eq_flatMap, List.flatMap_id, List.mem_flatten]
            refine ⟨frame'.refs, ?_, href⟩
            rw [List.mem_map]
            refine ⟨cfg.stack[n], List.mem_iff_getElem.mpr ⟨n, n_lt_len, rfl⟩, ?_⟩
            rw [← f_eq]
          have oid_ne_fresh : oid ≠ cfg.freshObjectId := by
            intro heq
            apply RuntimeConfig.freshObjectId_not_mem cfg
            rw [← heq]
            exact hs1 oid href_in_cfg_refs
          have hlocEq_cfg : (Reference.OId oid).loc? cfg = some (Location.Stk fid') := by
            rw [loc_eq oid oid_ne_fresh]
            exact hlocEq
          exact s2 frame' hframe'_in_cfg (Reference.OId oid) href fid' oid rfl hlocEq_cfg
        · subst hnew
          dsimp at href
          rcases newFrame_refs_mem (Reference.OId oid) href with hfreq | horig
          · rw [Reference.OId.injEq] at hfreq
            subst hfreq
            rw [loc_fresh0] at hlocEq
            simp at hlocEq
          · have href_in_cfg_refs : Reference.OId oid ∈ cfg.refs := by
              apply List.mem_append_left
              unfold Stack.refs
              rw [List.bind_eq_flatMap, List.flatMap_id, List.mem_flatten]
              exact ⟨frame.refs, List.mem_map_of_mem frame_mem, horig⟩
            have oid_ne_fresh : oid ≠ cfg.freshObjectId := by
              intro heq
              apply RuntimeConfig.freshObjectId_not_mem cfg
              rw [← heq]
              exact hs1 oid href_in_cfg_refs
            have hlocEq_cfg : (Reference.OId oid).loc? cfg = some (Location.Stk fid') := by
              rw [loc_eq oid oid_ne_fresh]
              exact hlocEq
            have hframe_in_cfg :
                ({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex) ∈ cfg.stackWithIndex := by
              rw [stackWithIndex_eq_cfg]
              exact List.mem_append_right _ (List.mem_singleton_self _)
            exact s2 _ hframe_in_cfg (Reference.OId oid) horig fid' oid rfl hlocEq_cfg

theorem makeObjRegion_S3 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  S3 cfg' := by
  intro vcfg h
  have h' := h
  have hs1 := vcfg.hs1
  have s3 := vcfg.s3
  have loc_eq := makeObjRegion_corollary_loc_eq vcfg h
  obtain ⟨frame0, hframe0getLast, loc_fresh0⟩ := makeObjRegion_corollary_loc_fresh vcfg h
  unfold makeObjRegion at h
  cases stackGetLast : cfg.stack.getLast? with
  | none => rw [stackGetLast] at h; contradiction
  | some frame =>
    rw [stackGetLast] at h hframe0getLast
    rw [Option.some_inj] at hframe0getLast
    subst frame0
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
        set newFrame : Frame :=
          { regionId := frame.regionId, bridgeVar := frame.bridgeVar, objMap := frame.objMap,
            varMap := AList.insert x (Reference.OId cfg.freshObjectId) frame.varMap } with newFrame_def
        have newFrame_refs_mem : ∀ ref, ref ∈ newFrame.refs →
            ref = Reference.OId cfg.freshObjectId ∨ ref ∈ frame.refs := by
          intro ref href
          rw [newFrame_def] at href
          unfold Frame.refs at href
          dsimp at href
          rw [List.mem_append] at href
          rcases href with hobjmap | hvarmap
          · right
            exact List.mem_append_left _ hobjmap
          · rw [List.mem_cons] at hvarmap
            rcases hvarmap with heqref | hker
            · left; exact heqref
            · right
              unfold Frame.refs
              apply List.mem_append_right
              exact (List.kerase_sublist x frame.varMap.entries).map (·.2) |>.subset hker
        have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
          (List.dropLast_append_getLast? frame stackGetLast).symm
        have frame_mem : frame ∈ cfg.stack := stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self frame)
        have stackWithIndex_eq_cfg :
            cfg.stackWithIndex =
              cfg.stack.dropLast.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) ++
                [({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex)] := by
          unfold RuntimeConfig.stackWithIndex
          conv_lhs => rw [stack_eq]
          rw [List.mapIdx_concat]
        have stack_eq' : cfg'.stack = cfg.stack.dropLast ++ [newFrame] := (congrArg RuntimeConfig.stack h).symm
        have stackWithIndex_eq :
            cfg'.stackWithIndex =
              cfg.stack.dropLast.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) ++
                [({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex)] := by
          unfold RuntimeConfig.stackWithIndex
          rw [stack_eq', List.mapIdx_concat]
        have transport : ∀ frame3 : FrameWithIndex, frame3 ∈ cfg.stackWithIndex →
            ∃ frame4 ∈ cfg'.stackWithIndex, frame4.regionId = frame3.regionId ∧ frame4.index = frame3.index := by
          intro frame3 hmem3
          rw [stackWithIndex_eq_cfg, List.mem_append, List.mem_singleton] at hmem3
          rcases hmem3 with hd | hl
          · exact ⟨frame3, by rw [stackWithIndex_eq]; exact List.mem_append_left _ hd, rfl, rfl⟩
          · refine ⟨{ newFrame with index := cfg.stack.dropLast.length }, ?_, ?_, ?_⟩
            · rw [stackWithIndex_eq]; exact List.mem_append_right _ (List.mem_singleton_self _)
            · rw [hl]
            · rw [hl]
        unfold S3
        intro frame' hframe' ref href rid' oid hrefeq hlocEq
        subst hrefeq
        rw [stackWithIndex_eq, List.mem_append, List.mem_singleton] at hframe'
        rcases hframe' with hold | hnew
        · have hframe'_in_cfg : frame' ∈ cfg.stackWithIndex := by
            rw [stackWithIndex_eq_cfg]
            exact List.mem_append_left _ hold
          have href_in_cfg_refs : Reference.OId oid ∈ cfg.refs := by
            obtain ⟨n, n_lt_len, f_eq⟩ := List.mem_mapIdx.mp hframe'_in_cfg
            apply List.mem_append_left
            unfold Stack.refs
            rw [List.bind_eq_flatMap, List.flatMap_id, List.mem_flatten]
            refine ⟨frame'.refs, ?_, href⟩
            rw [List.mem_map]
            refine ⟨cfg.stack[n], List.mem_iff_getElem.mpr ⟨n, n_lt_len, rfl⟩, ?_⟩
            rw [← f_eq]
          have oid_ne_fresh : oid ≠ cfg.freshObjectId := by
            intro heq
            apply RuntimeConfig.freshObjectId_not_mem cfg
            rw [← heq]
            exact hs1 oid href_in_cfg_refs
          have hlocEq_cfg : (Reference.OId oid).loc? cfg = some (Location.Rgn rid') := by
            rw [loc_eq oid oid_ne_fresh]
            exact hlocEq
          obtain ⟨frame'', hframe''_mem, hframe''_region, hframe''_le⟩ :=
            s3 frame' hframe'_in_cfg (Reference.OId oid) href rid' oid rfl hlocEq_cfg
          obtain ⟨frame4, hframe4_mem, hframe4_region, hframe4_index⟩ := transport frame'' hframe''_mem
          exact ⟨frame4, hframe4_mem, hframe4_region.trans hframe''_region, (le_of_eq hframe4_index).trans hframe''_le⟩
        · subst hnew
          dsimp at href
          rcases newFrame_refs_mem (Reference.OId oid) href with hfreq | horig
          · rw [Reference.OId.injEq] at hfreq
            subst hfreq
            rw [loc_fresh0] at hlocEq
            rw [Option.some_inj, Location.Rgn.injEq] at hlocEq
            subst hlocEq
            refine ⟨_, ?_, rfl, le_refl _⟩
            rw [stackWithIndex_eq]
            exact List.mem_append_right _ (List.mem_singleton_self _)
          · have href_in_cfg_refs : Reference.OId oid ∈ cfg.refs := by
              apply List.mem_append_left
              unfold Stack.refs
              rw [List.bind_eq_flatMap, List.flatMap_id, List.mem_flatten]
              exact ⟨frame.refs, List.mem_map_of_mem frame_mem, horig⟩
            have oid_ne_fresh : oid ≠ cfg.freshObjectId := by
              intro heq
              apply RuntimeConfig.freshObjectId_not_mem cfg
              rw [← heq]
              exact hs1 oid href_in_cfg_refs
            have hlocEq_cfg : (Reference.OId oid).loc? cfg = some (Location.Rgn rid') := by
              rw [loc_eq oid oid_ne_fresh]
              exact hlocEq
            have hframe_in_cfg :
                ({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex) ∈ cfg.stackWithIndex := by
              rw [stackWithIndex_eq_cfg]
              exact List.mem_append_right _ (List.mem_singleton_self _)
            obtain ⟨frame'', hframe''_mem, hframe''_region, hframe''_le⟩ :=
              s3 _ hframe_in_cfg (Reference.OId oid) horig rid' oid rfl hlocEq_cfg
            obtain ⟨frame4, hframe4_mem, hframe4_region, hframe4_index⟩ := transport frame'' hframe''_mem
            exact ⟨frame4, hframe4_mem, hframe4_region.trans hframe''_region, (le_of_eq hframe4_index).trans hframe''_le⟩

theorem makeObjRegion_HS1 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  HS1 cfg' := by
  intro vcfg h
  have h' := h
  have hs1 := vcfg.hs1
  have objectIds_perm := makeObjRegion_corollary_objectIds_perm vcfg h
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
        have fresh_not_in_region := makeObjRegion_corollary_fresh_not_in_region heapLookup
        set newRegion : Region :=
          { bridgeObjectId := region.bridgeObjectId,
            objMap := AList.insert cfg.freshObjectId ∅ region.objMap,
            status := Status.Open } with newRegion_def
        have newRegion_refs_eq : newRegion.refs = region.refs := by
          show (AList.insert cfg.freshObjectId ∅ region.objMap).entries.map (·.2) >>= Object.refs = region.refs
          rw [AList.entries_insert_of_notMem fresh_not_in_region]
          simp [Object.refs, Region.refs, List.bind_eq_flatMap]
        have newFrame_refs_mem : ∀ ref, ref ∈ ({ frame with
              varMap := AList.insert x (Reference.OId cfg.freshObjectId) frame.varMap } : Frame).refs →
            ref = Reference.OId cfg.freshObjectId ∨ ref ∈ frame.refs := by
          intro ref href
          unfold Frame.refs at href
          dsimp at href
          rw [List.mem_append] at href
          rcases href with hobjmap | hvarmap
          · right
            exact List.mem_append_left _ hobjmap
          · rw [List.mem_cons] at hvarmap
            rcases hvarmap with heqref | hker
            · left; exact heqref
            · right
              apply List.mem_append_right
              exact (List.kerase_sublist x frame.varMap.entries).map (·.2) |>.subset hker
        have heap'_refs_perm : (Heap.refs (AList.insert frame.regionId newRegion cfg.heap)).Perm cfg.heap.refs := by
          apply List.Perm.flatten
          obtain ⟨regionVal2, l1e2, l2e2, hnotmem2, heq2, hkerase2⟩ :=
            List.exists_of_kerase (List.mem_keys_of_mem (AList.lookup_mem_entries heapLookup))
          have regionVal2_eq_region : regionVal2 = region := by
            have mem_regionVal2 : (⟨frame.regionId, regionVal2⟩ : Sigma (fun _ : RegionId => Region)) ∈ cfg.heap.entries := by
              rw [heq2]
              exact List.mem_append_right _ List.mem_cons_self
            exact List.NodupKeys.eq_of_mk_mem cfg.heap.nodupKeys mem_regionVal2 (AList.lookup_mem_entries heapLookup)
          subst regionVal2
          unfold AList.insert
          dsimp
          rw [hkerase2]
          simp only [heq2, List.map_append, List.map_cons]
          rw [newRegion_refs_eq]
          exact List.perm_middle.symm
        unfold HS1
        intro oid hmem
        rw [← h] at hmem
        unfold RuntimeConfig.refs at hmem
        dsimp at hmem
        rw [List.mem_append] at hmem
        have stack_refs_append : ∀ (l : Stack) (f : Frame), Stack.refs (l ++ [f]) = Stack.refs l ++ f.refs := by
          intro l f
          unfold Stack.refs
          rw [List.bind_eq_flatMap, List.bind_eq_flatMap, List.flatMap_id, List.flatMap_id,
            List.map_append, List.flatten_append]
          simp
        have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
          (List.dropLast_append_getLast? frame stackGetLast).symm
        have frame_mem : frame ∈ cfg.stack := stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self frame)
        have target_mem : oid ∈ cfg.objectIds ++ [cfg.freshObjectId] := by
          rcases hmem with hstack | hheap
          · rw [stack_refs_append] at hstack
            rw [List.mem_append] at hstack
            rcases hstack with hdrop | hnew
            · have href_in_cfg_refs : Reference.OId oid ∈ cfg.refs := by
                apply List.mem_append_left
                rw [stack_eq, stack_refs_append]
                exact List.mem_append_left _ hdrop
              exact List.mem_append_left _ (hs1 oid href_in_cfg_refs)
            · rcases newFrame_refs_mem (Reference.OId oid) hnew with hfreq | horig
              · rw [Reference.OId.injEq] at hfreq
                exact List.mem_append_right _ (List.mem_singleton.mpr hfreq)
              · have href_in_cfg_refs : Reference.OId oid ∈ cfg.refs := by
                  apply List.mem_append_left
                  rw [stack_eq, stack_refs_append]
                  exact List.mem_append_right _ horig
                exact List.mem_append_left _ (hs1 oid href_in_cfg_refs)
          · have href_in_cfg_heap_refs : Reference.OId oid ∈ cfg.heap.refs := heap'_refs_perm.mem_iff.mp hheap
            exact List.mem_append_left _ (hs1 oid (List.mem_append_right _ href_in_cfg_heap_refs))
        exact objectIds_perm.mem_iff.mpr target_mem

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
