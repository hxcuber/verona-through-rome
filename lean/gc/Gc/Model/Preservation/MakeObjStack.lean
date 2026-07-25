import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Theorems
import Gc.Model.Mutation

import Mathlib.Data.List.Infix

-- old refs keep their location: nothing that already resolved in cfg moves in cfg'.
theorem makeObjStack_corollary_1 : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  ∀ (ref : Reference) loc, ref.loc? cfg = some loc → ref.loc? cfg' = some loc := by
  sorry

-- heap objects keep their region location (both directions: heap is untouched by makeObjStack).
theorem makeObjStack_corollary_2 : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  ∀ oid rid, (Reference.OId oid).loc? cfg = some (Location.Rgn rid) ↔
    (Reference.OId oid).loc? cfg' = some (Location.Rgn rid) := by
  sorry

-- stack objects that already had a frame location in cfg keep that same location in cfg'
-- (forward only: the freshly created object resolves to Stk in cfg' but not in cfg).
theorem makeObjStack_corollary_3 : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  ∀ oid fid, (Reference.OId oid).loc? cfg = some (Location.Stk fid) →
    (Reference.OId oid).loc? cfg' = some (Location.Stk fid) := by
  sorry

-- regions keep their location (both directions: makeObjStack never touches the heap).
theorem makeObjStack_corollary_4 : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  ∀ rid, (Reference.RId rid).loc? cfg = (Reference.RId rid).loc? cfg' := by
  sorry

theorem makeObjStack_L1 : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  L1 cfg' := by
  intro vcfg h
  have h' := h
  unfold makeObjStack at h
  cases stackGetLast : cfg.stack.getLast? with
  | none => rw [stackGetLast] at h; contradiction
  | some frame =>
    rw [stackGetLast] at h
    dsimp at h
    rw [Option.some_inj] at h
    unfold L1
    rw [← h]
    have l1 := vcfg.l1
    have hfresh := RuntimeConfig.freshObjectId_not_mem cfg
    have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
      (List.dropLast_append_getLast? frame stackGetLast).symm
    have frame_mem : frame ∈ cfg.stack := stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self frame)
    have fresh_not_in_frame : cfg.freshObjectId ∉ frame.objMap.keys := by
      intro hc
      apply hfresh
      unfold RuntimeConfig.objectIds Stack.objectIds Frame.objectIds
      rw [List.bind_eq_flatMap, List.flatMap_id, List.mem_append, List.mem_flatten]
      exact Or.inl ⟨frame.objMap.keys, List.mem_map_of_mem frame_mem, hc⟩
    set newFrame : Frame :=
      { regionId := frame.regionId, bridgeVar := frame.bridgeVar,
        objMap := AList.insert cfg.freshObjectId ∅ frame.objMap,
        varMap := AList.insert x (Reference.OId cfg.freshObjectId) frame.varMap } with newFrame_def
    have newFrame_objectIds : newFrame.objectIds = cfg.freshObjectId :: frame.objectIds := by
      rw [newFrame_def]
      unfold Frame.objectIds
      dsimp
      rw [AList.keys_insert, List.erase_of_not_mem fresh_not_in_frame]
    have stack_objectIds_split : Stack.objectIds (cfg.stack.dropLast ++ [newFrame]) =
        Stack.objectIds cfg.stack.dropLast ++ (cfg.freshObjectId :: frame.objectIds) := by
      unfold Stack.objectIds
      rw [List.bind_eq_flatMap, List.bind_eq_flatMap, List.flatMap_id, List.flatMap_id,
        List.map_append, List.flatten_append]
      dsimp
      rw [newFrame_objectIds, List.append_nil]
    have dropLast_frame_eq : Stack.objectIds cfg.stack.dropLast ++ frame.objectIds = cfg.stack.objectIds := by
      conv_rhs => rw [stack_eq]
      unfold Stack.objectIds
      simp [Frame.objectIds]
    have eq1 : Stack.objectIds (cfg.stack.dropLast ++ [newFrame]) ++ cfg.heap.objectIds =
        Stack.objectIds cfg.stack.dropLast ++ ([cfg.freshObjectId] ++ (frame.objectIds ++ cfg.heap.objectIds)) := by
      rw [stack_objectIds_split, List.append_assoc, List.cons_append]
      rfl
    have perm2 :
        (Stack.objectIds cfg.stack.dropLast ++ ([cfg.freshObjectId] ++ (frame.objectIds ++ cfg.heap.objectIds))).Perm
          (Stack.objectIds cfg.stack.dropLast ++ ((frame.objectIds ++ cfg.heap.objectIds) ++ [cfg.freshObjectId])) :=
      List.Perm.append_left _ List.perm_append_comm
    have eq2 : Stack.objectIds cfg.stack.dropLast ++ ((frame.objectIds ++ cfg.heap.objectIds) ++ [cfg.freshObjectId]) =
        cfg.objectIds ++ [cfg.freshObjectId] := by
      rw [← List.append_assoc, ← List.append_assoc, dropLast_frame_eq]
      rfl
    have objectIds_perm :
        ({ stack := cfg.stack.dropLast ++ [newFrame], heap := cfg.heap } : RuntimeConfig).objectIds.Perm
          (cfg.objectIds ++ [cfg.freshObjectId]) := by
      unfold RuntimeConfig.objectIds
      dsimp
      rw [eq1]
      exact eq2 ▸ perm2
    have nodup_ext : (cfg.objectIds ++ [cfg.freshObjectId]).Nodup := by
      apply List.nodup_append.mpr
      refine ⟨l1, List.nodup_singleton _, ?_⟩
      intro a ha b hb heq
      subst heq
      rw [List.mem_singleton] at hb
      exact hfresh (hb ▸ ha)
    exact nodup_ext.perm objectIds_perm.symm

theorem makeObjStack_L2 : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  L2 cfg' := by
  intro vcfg h
  have h' := h
  unfold makeObjStack at h
  cases stackGetLast : cfg.stack.getLast? with
  | none => rw [stackGetLast] at h; contradiction
  | some frame =>
    rw [stackGetLast] at h
    dsimp at h
    rw [Option.some_inj] at h
    unfold L2
    rw [← h]
    dsimp
    intro frame'' hframe''
    rw [List.mem_append, List.mem_singleton] at hframe''
    have l2 := vcfg.l2
    have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
      (List.dropLast_append_getLast? frame stackGetLast).symm
    have frame_mem : frame ∈ cfg.stack := stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self frame)
    cases hframe'' with
    | inl hdrop => exact l2 frame'' (List.mem_of_mem_dropLast hdrop)
    | inr heq => subst heq; exact l2 frame frame_mem

theorem makeObjStack_H1 : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  H1 cfg' := by
  intro vcfg h
  have h' := h
  unfold makeObjStack at h
  cases stackGetLast : cfg.stack.getLast? with
  | none => rw [stackGetLast] at h; contradiction
  | some frame =>
    rw [stackGetLast] at h
    dsimp at h
    rw [Option.some_inj] at h
    unfold H1
    rw [← h]
    exact vcfg.h1

theorem makeObjStack_H2 : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  H2 cfg' := by
  intro vcfg h
  have h' := h
  unfold makeObjStack at h
  cases stackGetLast : cfg.stack.getLast? with
  | none => rw [stackGetLast] at h; contradiction
  | some frame =>
    rw [stackGetLast] at h
    dsimp at h
    rw [Option.some_inj] at h
    unfold H2
    rw [← h]
    intro rid
    dsimp
    have h2 := vcfg.h2 rid
    have hfresh := RuntimeConfig.freshObjectId_not_mem cfg
    have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
      (List.dropLast_append_getLast? frame stackGetLast).symm
    have frame_mem : frame ∈ cfg.stack := stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self frame)
    have fresh_not_in_frame : cfg.freshObjectId ∉ frame.objMap.keys := by
      intro hc
      apply hfresh
      unfold RuntimeConfig.objectIds Stack.objectIds Frame.objectIds
      rw [List.bind_eq_flatMap, List.flatMap_id, List.mem_append, List.mem_flatten]
      exact Or.inl ⟨frame.objMap.keys, List.mem_map_of_mem frame_mem, hc⟩
    set newFrame : Frame :=
      { regionId := frame.regionId, bridgeVar := frame.bridgeVar,
        objMap := AList.insert cfg.freshObjectId ∅ frame.objMap,
        varMap := AList.insert x (Reference.OId cfg.freshObjectId) frame.varMap } with newFrame_def
    have newFrame_refs_le : newFrame.refs.count (Reference.RId rid) ≤ frame.refs.count (Reference.RId rid) := by
      rw [newFrame_def]
      unfold Frame.refs
      dsimp
      rw [List.kerase_of_notMem_keys fresh_not_in_frame, List.count_append, List.count_append]
      have objMap_eq : List.flatMap Object.refs (∅ :: List.map (·.2) frame.objMap.entries) =
          List.flatMap Object.refs (List.map (·.2) frame.objMap.entries) := by
        simp [Object.refs]
      rw [objMap_eq]
      have varMap_le : List.count (Reference.RId rid)
          (Reference.OId cfg.freshObjectId :: List.map (·.2) (List.kerase x frame.varMap.entries)) ≤
          List.count (Reference.RId rid) (List.map (·.2) frame.varMap.entries) := by
        rw [List.count_cons]
        have hne : (Reference.OId cfg.freshObjectId == Reference.RId rid) = false := rfl
        rw [hne]
        dsimp
        have hsub : (List.map (·.2) (List.kerase x frame.varMap.entries)).Sublist
            (List.map (·.2) frame.varMap.entries) :=
          List.Sublist.map _ (List.kerase_sublist x frame.varMap.entries)
        exact hsub.count_le (Reference.RId rid)
      exact Nat.add_le_add_left varMap_le _
    have stack_refs_le : (Stack.refs (cfg.stack.dropLast ++ [newFrame])).count
        (Reference.RId rid) ≤ cfg.stack.refs.count (Reference.RId rid) := by
      have split1 : Stack.refs (cfg.stack.dropLast ++ [newFrame]) =
          Stack.refs cfg.stack.dropLast ++ newFrame.refs := by
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

theorem makeObjStack_H3 : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  H3 cfg' := by
  intro vcfg h
  have h' := h
  unfold makeObjStack at h
  cases stackGetLast : cfg.stack.getLast? with
  | none => rw [stackGetLast] at h; contradiction
  | some frame =>
    rw [stackGetLast] at h
    dsimp at h
    rw [Option.some_inj] at h
    have heap_eq : cfg'.heap = cfg.heap := by rw [← h]
    unfold H3
    intro rid oid region hlookup href
    rw [heap_eq] at hlookup
    have h3 := vcfg.h3 rid oid region hlookup href
    exact (makeObjStack_corollary_2 vcfg h' oid rid).mp h3

theorem makeObjStack_S1 : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  S1 cfg' := by
  intro vcfg h
  have h' := h
  unfold makeObjStack at h
  cases stackGetLast : cfg.stack.getLast? with
  | none => rw [stackGetLast] at h; contradiction
  | some frame =>
    rw [stackGetLast] at h
    dsimp at h
    rw [Option.some_inj] at h
    unfold S1
    rw [← h]
    dsimp
    set newFrame : Frame :=
      { regionId := frame.regionId, bridgeVar := frame.bridgeVar,
        objMap := AList.insert cfg.freshObjectId ∅ frame.objMap,
        varMap := AList.insert x (Reference.OId cfg.freshObjectId) frame.varMap } with newFrame_def
    have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
      (List.dropLast_append_getLast? frame stackGetLast).symm
    have regionId_eq : (cfg.stack.dropLast ++ [newFrame]).map (fun f => f.regionId) =
        cfg.stack.map (fun f => f.regionId) := by
      conv_rhs => rw [stack_eq]
      rw [List.map_append, List.map_append, newFrame_def]
      dsimp
    rw [regionId_eq]
    exact vcfg.s1

theorem makeObjStack_S2 : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  S2 cfg' := by
  sorry

theorem makeObjStack_S3 : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  S3 cfg' := by
  sorry

theorem makeObjStack_HS1 : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  HS1 cfg' := by
  intro vcfg h
  have h' := h
  unfold makeObjStack at h
  cases stackGetLast : cfg.stack.getLast? with
  | none => rw [stackGetLast] at h; contradiction
  | some frame =>
    rw [stackGetLast] at h
    dsimp at h
    rw [Option.some_inj] at h
    unfold HS1
    rw [← h]
    intro oid hmem
    have hs1 := vcfg.hs1
    have hfresh := RuntimeConfig.freshObjectId_not_mem cfg
    have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
      (List.dropLast_append_getLast? frame stackGetLast).symm
    have frame_mem : frame ∈ cfg.stack := stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self frame)
    have fresh_not_in_frame : cfg.freshObjectId ∉ frame.objMap.keys := by
      intro hc
      apply hfresh
      unfold RuntimeConfig.objectIds Stack.objectIds Frame.objectIds
      rw [List.bind_eq_flatMap, List.flatMap_id, List.mem_append, List.mem_flatten]
      exact Or.inl ⟨frame.objMap.keys, List.mem_map_of_mem frame_mem, hc⟩
    set newFrame : Frame :=
      { regionId := frame.regionId, bridgeVar := frame.bridgeVar,
        objMap := AList.insert cfg.freshObjectId ∅ frame.objMap,
        varMap := AList.insert x (Reference.OId cfg.freshObjectId) frame.varMap } with newFrame_def
    have stack_refs_append : ∀ (l : Stack) (f : Frame), Stack.refs (l ++ [f]) = Stack.refs l ++ f.refs := by
      intro l f
      unfold Stack.refs
      rw [List.bind_eq_flatMap, List.bind_eq_flatMap, List.flatMap_id, List.flatMap_id,
        List.map_append, List.flatten_append]
      simp
    have stack_objectIds_append :
        ∀ (l : Stack) (f : Frame), Stack.objectIds (l ++ [f]) = Stack.objectIds l ++ f.objectIds := by
      intro l f
      unfold Stack.objectIds
      rw [List.bind_eq_flatMap, List.bind_eq_flatMap, List.flatMap_id, List.flatMap_id,
        List.map_append, List.flatten_append]
      simp
    have frame_refs_to_cfg_refs : ∀ ref, ref ∈ frame.refs → ref ∈ cfg.refs := by
      intro ref href
      apply List.mem_append_left
      rw [stack_eq, stack_refs_append]
      exact List.mem_append_right _ href
    have dropLast_refs_to_cfg_refs : ∀ ref, ref ∈ Stack.refs cfg.stack.dropLast → ref ∈ cfg.refs := by
      intro ref href
      apply List.mem_append_left
      rw [stack_eq, stack_refs_append]
      exact List.mem_append_left _ href
    have newFrame_objectIds : newFrame.objectIds = cfg.freshObjectId :: frame.objectIds := by
      rw [newFrame_def]
      unfold Frame.objectIds
      dsimp
      rw [AList.keys_insert, List.erase_of_not_mem fresh_not_in_frame]
    have dropLast_frame_eq : Stack.objectIds cfg.stack.dropLast ++ frame.objectIds = cfg.stack.objectIds := by
      conv_rhs => rw [stack_eq, stack_objectIds_append]
    have eq1 : Stack.objectIds (cfg.stack.dropLast ++ [newFrame]) ++ cfg.heap.objectIds =
        Stack.objectIds cfg.stack.dropLast ++ ([cfg.freshObjectId] ++ (frame.objectIds ++ cfg.heap.objectIds)) := by
      rw [stack_objectIds_append, newFrame_objectIds, List.append_assoc, List.cons_append]
      rfl
    have perm2 :
        (Stack.objectIds cfg.stack.dropLast ++ ([cfg.freshObjectId] ++ (frame.objectIds ++ cfg.heap.objectIds))).Perm
          (Stack.objectIds cfg.stack.dropLast ++ ((frame.objectIds ++ cfg.heap.objectIds) ++ [cfg.freshObjectId])) :=
      List.Perm.append_left _ List.perm_append_comm
    have eq2 : Stack.objectIds cfg.stack.dropLast ++ ((frame.objectIds ++ cfg.heap.objectIds) ++ [cfg.freshObjectId]) =
        cfg.objectIds ++ [cfg.freshObjectId] := by
      rw [← List.append_assoc, ← List.append_assoc, dropLast_frame_eq]
      rfl
    have objectIds_perm :
        ({ stack := cfg.stack.dropLast ++ [newFrame], heap := cfg.heap } : RuntimeConfig).objectIds.Perm
          (cfg.objectIds ++ [cfg.freshObjectId]) := by
      unfold RuntimeConfig.objectIds
      dsimp
      rw [eq1]
      exact eq2 ▸ perm2
    unfold RuntimeConfig.refs at hmem
    dsimp at hmem
    rw [List.mem_append] at hmem
    have target_mem : oid ∈ cfg.objectIds ++ [cfg.freshObjectId] := by
      rcases hmem with hstack | hheap
      · rw [stack_refs_append, List.mem_append] at hstack
        rcases hstack with hdrop | hnew
        · exact List.mem_append_left _ (hs1 oid (dropLast_refs_to_cfg_refs _ hdrop))
        · rw [newFrame_def] at hnew
          unfold Frame.refs at hnew
          dsimp at hnew
          rw [List.mem_append] at hnew
          rcases hnew with hobjmap | hvarmap
          · rw [List.kerase_of_notMem_keys fresh_not_in_frame] at hobjmap
            have hframe : Reference.OId oid ∈ frame.refs := by
              unfold Frame.refs
              apply List.mem_append_left
              simpa [Object.refs] using hobjmap
            exact List.mem_append_left _ (hs1 oid (frame_refs_to_cfg_refs _ hframe))
          · rw [List.mem_cons] at hvarmap
            rcases hvarmap with heq | hker
            · rw [Reference.OId.injEq] at heq
              exact List.mem_append_right _ (List.mem_singleton.mpr heq)
            · have hframe : Reference.OId oid ∈ frame.refs := by
                unfold Frame.refs
                apply List.mem_append_right
                exact (List.kerase_sublist x frame.varMap.entries).map (·.2) |>.subset hker
              exact List.mem_append_left _ (hs1 oid (frame_refs_to_cfg_refs _ hframe))
      · exact List.mem_append_left _ (hs1 oid (List.mem_append_right _ hheap))
    exact objectIds_perm.mem_iff.mpr target_mem

theorem makeObjStack_valid : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  ValidConfig cfg' := by
  intro vcfg h
  exact {
    l1 := makeObjStack_L1 vcfg h,
    l2 := makeObjStack_L2 vcfg h,
    h1 := makeObjStack_H1 vcfg h,
    h2 := makeObjStack_H2 vcfg h,
    h3 := makeObjStack_H3 vcfg h,
    s1 := makeObjStack_S1 vcfg h,
    s2 := makeObjStack_S2 vcfg h,
    s3 := makeObjStack_S3 vcfg h,
    hs1 := makeObjStack_HS1 vcfg h
  }
