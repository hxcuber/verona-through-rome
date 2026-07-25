import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Theorems
import Gc.Model.Mutation

import Mathlib.Data.List.Infix

theorem makeRegion_L1 : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  L1 cfg' := by
  intro vcfg h
  have h' := h
  have l1 := vcfg.l1
  unfold makeRegion at h
  cases stackGetLast : cfg.stack.getLast? with
  | none => rw [stackGetLast] at h; contradiction
  | some frame =>
    rw [stackGetLast] at h
    dsimp at h
    rw [Option.some_inj] at h
    unfold L1
    rw [← h]
    unfold RuntimeConfig.objectIds
    dsimp
    have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
      (List.dropLast_append_getLast? frame stackGetLast).symm
    have stack_objectIds_eq :
        Stack.objectIds (cfg.stack.dropLast ++
          [({ frame with varMap := frame.varMap.insert x (Reference.RId cfg.freshRegionId) } : Frame)]) =
        cfg.stack.objectIds := by
      conv_rhs => rw [stack_eq]
      unfold Stack.objectIds Frame.objectIds
      simp
    have heap_objectIds_eq :
        Heap.objectIds (AList.insert cfg.freshRegionId
          { bridgeObjectId := cfg.freshObjectId, objMap := AList.singleton cfg.freshObjectId ∅, status := Status.Closed }
          cfg.heap) =
        cfg.freshObjectId :: cfg.heap.objectIds := by
      unfold Heap.objectIds
      dsimp
      rw [List.kerase_of_notMem_keys (RuntimeConfig.freshRegionId_not_mem cfg)]
      unfold Region.objectIds
      dsimp
    rw [stack_objectIds_eq, heap_objectIds_eq]
    have eq1 : cfg.stack.objectIds ++ (cfg.freshObjectId :: cfg.heap.objectIds) =
        cfg.stack.objectIds ++ ([cfg.freshObjectId] ++ cfg.heap.objectIds) := by
      rw [List.singleton_append]
    have perm2 : (cfg.stack.objectIds ++ ([cfg.freshObjectId] ++ cfg.heap.objectIds)).Perm
        (cfg.stack.objectIds ++ (cfg.heap.objectIds ++ [cfg.freshObjectId])) :=
      List.Perm.append_left _ List.perm_append_comm
    have eq2 : cfg.stack.objectIds ++ (cfg.heap.objectIds ++ [cfg.freshObjectId]) =
        (cfg.stack.objectIds ++ cfg.heap.objectIds) ++ [cfg.freshObjectId] := by
      rw [List.append_assoc]
    have final_perm : (cfg.stack.objectIds ++ (cfg.freshObjectId :: cfg.heap.objectIds)).Perm
        (cfg.objectIds ++ [cfg.freshObjectId]) := by
      unfold RuntimeConfig.objectIds
      rw [eq1]
      exact eq2 ▸ perm2
    have nodup_ext : (cfg.objectIds ++ [cfg.freshObjectId]).Nodup := by
      apply List.nodup_append.mpr
      refine ⟨l1, List.nodup_singleton _, ?_⟩
      intro a ha b hb heqb
      subst heqb
      rw [List.mem_singleton] at hb
      exact RuntimeConfig.freshObjectId_not_mem cfg (hb ▸ ha)
    exact nodup_ext.perm final_perm.symm

theorem makeRegion_L2 : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  L2 cfg' := by
  intro vcfg h
  have h' := h
  have l2 := vcfg.l2
  unfold makeRegion at h
  cases stackGetLast : cfg.stack.getLast? with
  | none => rw [stackGetLast] at h; contradiction
  | some frame =>
    rw [stackGetLast] at h
    dsimp at h
    rw [Option.some_inj] at h
    unfold L2
    rw [← h]
    dsimp
    have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
      (List.dropLast_append_getLast? frame stackGetLast).symm
    have frame_mem : frame ∈ cfg.stack := stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self frame)
    intro frame'' hframe''
    rw [List.mem_append, List.mem_singleton] at hframe''
    rcases hframe'' with hdrop | heqframe
    · obtain ⟨region0, hlookup0, hopen0⟩ := l2 frame'' (List.mem_of_mem_dropLast hdrop)
      refine ⟨region0, ?_, hopen0⟩
      have hne : frame''.regionId ≠ cfg.freshRegionId := by
        intro heq
        have hmem : cfg.freshRegionId ∈ cfg.heap.keys := by
          rw [← AList.mem_keys, ← AList.lookup_isSome, ← heq, hlookup0]
          simp
        exact RuntimeConfig.freshRegionId_not_mem cfg hmem
      rw [AList.lookup_insert_ne hne]
      exact hlookup0
    · subst heqframe
      dsimp
      obtain ⟨region0, hlookup0, hopen0⟩ := l2 frame frame_mem
      refine ⟨region0, ?_, hopen0⟩
      have hne : frame.regionId ≠ cfg.freshRegionId := by
        intro heq
        have hmem : cfg.freshRegionId ∈ cfg.heap.keys := by
          rw [← AList.mem_keys, ← AList.lookup_isSome, ← heq, hlookup0]
          simp
        exact RuntimeConfig.freshRegionId_not_mem cfg hmem
      rw [AList.lookup_insert_ne hne]
      exact hlookup0

theorem makeRegion_H1 : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  H1 cfg' := by
  intro vcfg h
  have h' := h
  unfold makeRegion at h
  cases stackGetLast : cfg.stack.getLast? with
  | none => rw [stackGetLast] at h; contradiction
  | some frame =>
    rw [stackGetLast] at h
    dsimp at h
    rw [Option.some_inj] at h
    unfold H1
    intro region hregion
    rw [← h] at hregion
    unfold Heap.regions at hregion
    dsimp at hregion
    rw [List.kerase_of_notMem_keys (RuntimeConfig.freshRegionId_not_mem cfg), List.mem_cons] at hregion
    rcases hregion with heq | hold
    · subst heq
      dsimp
      rw [AList.mem_keys]
      simp
    · exact vcfg.h1 region hold

theorem makeRegion_H2 : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  H2 cfg' := by
  sorry

theorem makeRegion_corollary_loc_match_eq (o1 : Option FrameWithIndex)
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

theorem makeRegion_corollary_loc_eq : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  ∀ oid, oid ≠ cfg.freshObjectId →
    (Reference.OId oid).loc? cfg = (Reference.OId oid).loc? cfg' := by
  intro vcfg h oid hne
  have h' := h
  unfold makeRegion at h
  cases stackGetLast : cfg.stack.getLast? with
  | none => rw [stackGetLast] at h; contradiction
  | some frame =>
    rw [stackGetLast] at h
    dsimp at h
    rw [Option.some_inj] at h
    rw [← h]
    set newFrame : Frame :=
      { regionId := frame.regionId, bridgeVar := frame.bridgeVar, objMap := frame.objMap,
        varMap := AList.insert x (Reference.RId cfg.freshRegionId) frame.varMap } with newFrame_def
    set newRegionVal : Region :=
      { bridgeObjectId := cfg.freshObjectId, objMap := AList.singleton cfg.freshObjectId ∅, status := Status.Closed }
      with newRegionVal_def
    set cfgLit : RuntimeConfig :=
      { stack := cfg.stack.dropLast ++ [newFrame],
        heap := AList.insert cfg.freshRegionId newRegionVal cfg.heap }
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
    have heap_h2_eq :
        cfg.heap.entries.find? (fun p => (AList.keys p.snd.objMap).contains oid) =
        cfgLit.heap.entries.find? (fun p => (AList.keys p.snd.objMap).contains oid) := by
      rw [cfgLit_def]
      dsimp
      rw [List.kerase_of_notMem_keys (RuntimeConfig.freshRegionId_not_mem cfg)]
      have hb : ¬ (AList.keys newRegionVal.objMap).contains oid := by
        rw [newRegionVal_def]
        dsimp
        simp [hne]
      have find_eq :
          List.find? (fun p => (AList.keys p.snd.objMap).contains oid)
            ((⟨cfg.freshRegionId, newRegionVal⟩ : Sigma (fun _ : RegionId => Region)) :: cfg.heap.entries) =
          List.find? (fun p => (AList.keys p.snd.objMap).contains oid) cfg.heap.entries :=
        List.find?_cons_of_neg hb
      exact find_eq.symm
    unfold Reference.loc?
    dsimp
    have step1 := makeRegion_corollary_loc_match_eq
      (cfg.stackWithIndex.findRev? (fun f => (AList.keys f.objMap).contains oid))
      (cfg.heap.entries.find? (fun p => (AList.keys p.snd.objMap).contains oid))
    have step2 := makeRegion_corollary_loc_match_eq
      (cfgLit.stackWithIndex.findRev? (fun f => (AList.keys f.objMap).contains oid))
      (cfgLit.heap.entries.find? (fun p => (AList.keys p.snd.objMap).contains oid))
    have heap_h2_map_eq :
        (cfg.heap.entries.find? (fun p => (AList.keys p.snd.objMap).contains oid)).map Sigma.fst =
        (cfgLit.heap.entries.find? (fun p => (AList.keys p.snd.objMap).contains oid)).map Sigma.fst := by
      rw [heap_h2_eq]
    have rhs_eq :
        (match (cfg.stackWithIndex.findRev? (fun f => (AList.keys f.objMap).contains oid)).map
              FrameWithIndex.index,
            (cfg.heap.entries.find? (fun p => (AList.keys p.snd.objMap).contains oid)).map Sigma.fst with
          | some n, none => some (Location.Stk n)
          | none, some r => some (Location.Rgn r)
          | _, _ => none) =
        (match (cfgLit.stackWithIndex.findRev? (fun f => (AList.keys f.objMap).contains oid)).map
              FrameWithIndex.index,
            (cfgLit.heap.entries.find? (fun p => (AList.keys p.snd.objMap).contains oid)).map Sigma.fst with
          | some n, none => some (Location.Stk n)
          | none, some r => some (Location.Rgn r)
          | _, _ => none) := by
      rw [stack_h1_map_eq, heap_h2_map_eq]
    exact step1.trans (rhs_eq.trans step2.symm)

theorem makeRegion_H3 : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  H3 cfg' := by
  intro vcfg h
  have h' := h
  have hs1 := vcfg.hs1
  have h3 := vcfg.h3
  have loc_eq := makeRegion_corollary_loc_eq vcfg h
  unfold makeRegion at h
  cases stackGetLast : cfg.stack.getLast? with
  | none => rw [stackGetLast] at h; contradiction
  | some frame =>
    rw [stackGetLast] at h
    dsimp at h
    rw [Option.some_inj] at h
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
    have heap_eq : cfg'.heap = AList.insert cfg.freshRegionId
        { bridgeObjectId := cfg.freshObjectId, objMap := AList.singleton cfg.freshObjectId ∅, status := Status.Closed }
        cfg.heap :=
      (congrArg RuntimeConfig.heap h).symm
    unfold H3
    intro rid0 oid0 region0 hlookup0 href0
    rw [heap_eq] at hlookup0
    by_cases hrideq : rid0 = cfg.freshRegionId
    · subst hrideq
      rw [AList.lookup_insert, Option.some_inj] at hlookup0
      subst hlookup0
      simp [Region.refs, Object.refs, AList.singleton] at href0
    · rw [AList.lookup_insert_ne hrideq] at hlookup0
      have h3fact := h3 rid0 oid0 region0 hlookup0 href0
      have oid_ne_fresh := oid_ne_fresh_of_region_mem oid0 rid0 region0 hlookup0 href0
      rw [← loc_eq oid0 oid_ne_fresh]
      exact h3fact

theorem makeRegion_S1 : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  S1 cfg' := by
  intro vcfg h
  have h' := h
  unfold makeRegion at h
  cases stackGetLast : cfg.stack.getLast? with
  | none => rw [stackGetLast] at h; contradiction
  | some frame =>
    rw [stackGetLast] at h
    dsimp at h
    rw [Option.some_inj] at h
    unfold S1
    rw [← h]
    dsimp
    have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
      (List.dropLast_append_getLast? frame stackGetLast).symm
    have regionId_eq :
        (cfg.stack.dropLast ++
          [({ frame with varMap := frame.varMap.insert x (Reference.RId cfg.freshRegionId) } : Frame)]).map
          (fun f => f.regionId) =
        cfg.stack.map (fun f => f.regionId) := by
      conv_rhs => rw [stack_eq]
      simp
    rw [regionId_eq]
    exact vcfg.s1

theorem makeRegion_S2 : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  S2 cfg' := by
  intro vcfg h
  have h' := h
  have hs1 := vcfg.hs1
  have s2 := vcfg.s2
  have loc_eq := makeRegion_corollary_loc_eq vcfg h
  unfold makeRegion at h
  cases stackGetLast : cfg.stack.getLast? with
  | none => rw [stackGetLast] at h; contradiction
  | some frame =>
    rw [stackGetLast] at h
    dsimp at h
    rw [Option.some_inj] at h
    set newFrame : Frame :=
      { regionId := frame.regionId, bridgeVar := frame.bridgeVar, objMap := frame.objMap,
        varMap := AList.insert x (Reference.RId cfg.freshRegionId) frame.varMap } with newFrame_def
    have newFrame_refs_mem : ∀ ref, ref ∈ newFrame.refs →
        ref = Reference.RId cfg.freshRegionId ∨ ref ∈ frame.refs := by
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
      · simp at hfreq
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

theorem makeRegion_S3 : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  S3 cfg' := by
  intro vcfg h
  have h' := h
  have hs1 := vcfg.hs1
  have s3 := vcfg.s3
  have loc_eq := makeRegion_corollary_loc_eq vcfg h
  unfold makeRegion at h
  cases stackGetLast : cfg.stack.getLast? with
  | none => rw [stackGetLast] at h; contradiction
  | some frame =>
    rw [stackGetLast] at h
    dsimp at h
    rw [Option.some_inj] at h
    set newFrame : Frame :=
      { regionId := frame.regionId, bridgeVar := frame.bridgeVar, objMap := frame.objMap,
        varMap := AList.insert x (Reference.RId cfg.freshRegionId) frame.varMap } with newFrame_def
    have newFrame_refs_mem : ∀ ref, ref ∈ newFrame.refs →
        ref = Reference.RId cfg.freshRegionId ∨ ref ∈ frame.refs := by
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
      · simp at hfreq
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

theorem makeRegion_HS1 : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  HS1 cfg' := by
  intro vcfg h
  have h' := h
  have hs1 := vcfg.hs1
  unfold makeRegion at h
  cases stackGetLast : cfg.stack.getLast? with
  | none => rw [stackGetLast] at h; contradiction
  | some frame =>
    rw [stackGetLast] at h
    dsimp at h
    rw [Option.some_inj] at h
    have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
      (List.dropLast_append_getLast? frame stackGetLast).symm
    have stack_refs_append : ∀ (l : Stack) (f : Frame), Stack.refs (l ++ [f]) = Stack.refs l ++ f.refs := by
      intro l f
      unfold Stack.refs
      rw [List.bind_eq_flatMap, List.bind_eq_flatMap, List.flatMap_id, List.flatMap_id,
        List.map_append, List.flatten_append]
      simp
    have heap_refs_eq :
        Heap.refs (AList.insert cfg.freshRegionId
          { bridgeObjectId := cfg.freshObjectId, objMap := AList.singleton cfg.freshObjectId ∅, status := Status.Closed }
          cfg.heap) =
        cfg.heap.refs := by
      unfold Heap.refs
      dsimp
      rw [List.kerase_of_notMem_keys (RuntimeConfig.freshRegionId_not_mem cfg)]
      unfold Region.refs
      dsimp
      simp [Object.refs]
    have newFrame_refs_mem : ∀ ref, ref ∈ ({ frame with
          varMap := AList.insert x (Reference.RId cfg.freshRegionId) frame.varMap } : Frame).refs →
        ref = Reference.RId cfg.freshRegionId ∨ ref ∈ frame.refs := by
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
    have stack_objectIds_eq :
        Stack.objectIds (cfg.stack.dropLast ++
          [({ frame with varMap := frame.varMap.insert x (Reference.RId cfg.freshRegionId) } : Frame)]) =
        cfg.stack.objectIds := by
      conv_rhs => rw [stack_eq]
      unfold Stack.objectIds Frame.objectIds
      simp
    have heap_objectIds_eq :
        Heap.objectIds (AList.insert cfg.freshRegionId
          { bridgeObjectId := cfg.freshObjectId, objMap := AList.singleton cfg.freshObjectId ∅, status := Status.Closed }
          cfg.heap) =
        cfg.freshObjectId :: cfg.heap.objectIds := by
      unfold Heap.objectIds
      dsimp
      rw [List.kerase_of_notMem_keys (RuntimeConfig.freshRegionId_not_mem cfg)]
      unfold Region.objectIds
      dsimp
    unfold HS1
    rw [← h]
    unfold RuntimeConfig.refs RuntimeConfig.objectIds
    dsimp
    intro oid hmem
    rw [List.mem_append] at hmem
    have target_mem_cfg : Reference.OId oid ∈ cfg.refs := by
      rcases hmem with hstack | hheap
      · rw [stack_refs_append, List.mem_append] at hstack
        rcases hstack with hdrop | hnew
        · apply List.mem_append_left
          rw [stack_eq, stack_refs_append]
          exact List.mem_append_left _ hdrop
        · rcases newFrame_refs_mem (Reference.OId oid) hnew with hfreq | horig
          · simp at hfreq
          · apply List.mem_append_left
            rw [stack_eq, stack_refs_append]
            exact List.mem_append_right _ horig
      · apply List.mem_append_right
        exact heap_refs_eq ▸ hheap
    have oid_mem_cfg := hs1 oid target_mem_cfg
    unfold RuntimeConfig.objectIds at oid_mem_cfg
    rw [List.mem_append] at oid_mem_cfg
    rw [stack_objectIds_eq, heap_objectIds_eq, List.mem_append]
    rcases oid_mem_cfg with hs | hh
    · exact Or.inl hs
    · exact Or.inr (List.mem_cons_of_mem _ hh)

theorem makeRegion_HS2 : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  HS2 cfg' := by
  intro vcfg h
  have h' := h
  have hs2 := vcfg.hs2
  unfold makeRegion at h
  cases stackGetLast : cfg.stack.getLast? with
  | none => rw [stackGetLast] at h; contradiction
  | some frame =>
    rw [stackGetLast] at h
    dsimp at h
    rw [Option.some_inj] at h
    have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
      (List.dropLast_append_getLast? frame stackGetLast).symm
    have stack_refs_append : ∀ (l : Stack) (f : Frame), Stack.refs (l ++ [f]) = Stack.refs l ++ f.refs := by
      intro l f
      unfold Stack.refs
      rw [List.bind_eq_flatMap, List.bind_eq_flatMap, List.flatMap_id, List.flatMap_id,
        List.map_append, List.flatten_append]
      simp
    have heap_refs_eq :
        Heap.refs (AList.insert cfg.freshRegionId
          { bridgeObjectId := cfg.freshObjectId, objMap := AList.singleton cfg.freshObjectId ∅, status := Status.Closed }
          cfg.heap) =
        cfg.heap.refs := by
      unfold Heap.refs
      dsimp
      rw [List.kerase_of_notMem_keys (RuntimeConfig.freshRegionId_not_mem cfg)]
      unfold Region.refs
      dsimp
      simp [Object.refs]
    have newFrame_refs_mem : ∀ ref, ref ∈ ({ frame with
          varMap := AList.insert x (Reference.RId cfg.freshRegionId) frame.varMap } : Frame).refs →
        ref = Reference.RId cfg.freshRegionId ∨ ref ∈ frame.refs := by
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
    have new_key_mem : cfg.freshRegionId ∈ (AList.insert cfg.freshRegionId
        { bridgeObjectId := cfg.freshObjectId, objMap := AList.singleton cfg.freshObjectId ∅, status := Status.Closed }
        cfg.heap).keys := by
      rw [← AList.mem_keys, ← AList.lookup_isSome, AList.lookup_insert]
      simp
    have heap_keys_superset : ∀ r, r ∈ cfg.heap.keys → r ∈ (AList.insert cfg.freshRegionId
        { bridgeObjectId := cfg.freshObjectId, objMap := AList.singleton cfg.freshObjectId ∅, status := Status.Closed }
        cfg.heap).keys := by
      intro r hr
      have hne : r ≠ cfg.freshRegionId := by
        intro heq
        subst heq
        exact RuntimeConfig.freshRegionId_not_mem cfg hr
      rw [← AList.mem_keys, ← AList.lookup_isSome, AList.lookup_insert_ne hne, AList.lookup_isSome, AList.mem_keys]
      exact hr
    unfold HS2
    rw [← h]
    unfold RuntimeConfig.refs
    dsimp
    intro rid' hmem
    rw [List.mem_append] at hmem
    rcases hmem with hstack | hheap
    · rw [stack_refs_append, List.mem_append] at hstack
      rcases hstack with hdrop | hnew
      · have target_mem_cfg : Reference.RId rid' ∈ cfg.refs := by
          apply List.mem_append_left
          rw [stack_eq, stack_refs_append]
          exact List.mem_append_left _ hdrop
        exact heap_keys_superset rid' (hs2 rid' target_mem_cfg)
      · rcases newFrame_refs_mem (Reference.RId rid') hnew with hfreq | horig
        · rw [Reference.RId.injEq] at hfreq
          subst hfreq
          exact new_key_mem
        · have target_mem_cfg : Reference.RId rid' ∈ cfg.refs := by
            apply List.mem_append_left
            rw [stack_eq, stack_refs_append]
            exact List.mem_append_right _ horig
          exact heap_keys_superset rid' (hs2 rid' target_mem_cfg)
    · have target_mem_cfg : Reference.RId rid' ∈ cfg.refs := List.mem_append_right _ (heap_refs_eq ▸ hheap)
      exact heap_keys_superset rid' (hs2 rid' target_mem_cfg)

theorem makeRegion_valid : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  ValidConfig cfg' := by
  intro vcfg h
  exact {
    l1 := makeRegion_L1 vcfg h,
    l2 := makeRegion_L2 vcfg h,
    h1 := makeRegion_H1 vcfg h,
    h2 := makeRegion_H2 vcfg h,
    h3 := makeRegion_H3 vcfg h,
    s1 := makeRegion_S1 vcfg h,
    s2 := makeRegion_S2 vcfg h,
    s3 := makeRegion_S3 vcfg h,
    hs1 := makeRegion_HS1 vcfg h,
    hs2 := makeRegion_HS2 vcfg h
  }
