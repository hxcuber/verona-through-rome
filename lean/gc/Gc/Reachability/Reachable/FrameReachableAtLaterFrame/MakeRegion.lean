import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Mutation.Mutation
import Gc.Model.Mutation.Stmt
import Gc.Model.Preservation
import Gc.Reachability.Reachable.Semantics
import Gc.Reachability.Reachable.Basic
import Gc.Reachability.Reachable.Lemmas

theorem frameReachableAtLaterFrame_step_makeRegion (x : VarName) :
    FrameReachableAtLaterFrame_step (Stmt.makeRegion x) := by
  intro cfg cfg' vcfg h hFR3 frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  have h' : makeRegion x cfg = some cfg' := h
  have vcfg' : ValidConfig cfg' := makeRegion_valid vcfg h'
  obtain ⟨lastFrame, hlast, hcfg'⟩ := makeRegion_cases h'
  obtain ⟨region0, hlookupRid0, hopen0⟩ := l2_of_stackWithIndex vcfg (stackWithIndex_getLast_mem hlast)
  have hLf : ({ lastFrame with index := cfg.stack.length - 1 } : FrameWithIndex) ∈ cfg.stackWithIndex :=
    stackWithIndex_getLast_mem hlast
  have hne' : cfg.stack ≠ [] := by intro hnil; rw [hnil] at hlast; simp at hlast
  have hlen1 : 1 ≤ cfg.stack.length := List.length_pos_of_ne_nil hne'
  have hcfg'len : cfg'.stack.length = cfg.stack.length := by
    rw [hcfg']; dsimp only; rw [List.length_append, List.length_dropLast, List.length_singleton]; omega
  rcases makeRegion_frame_cases h' hframeMem with
    ⟨hframeMemCfg, hframeLt⟩ | ⟨lf, hlf, -, -, -, -, hframeIdx⟩
  swap
  · exfalso
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hframe'Mem
    have hframe'idx : frame'.index = n := by rw [← hfeq]
    rw [hcfg'len] at hn
    have hcontra : cfg.stack.length - 1 < n := by
      have heq1 : cfg.stack.length - 1 = frame.index := by rw [hframeIdx, List.length_dropLast]
      rw [heq1, ← hframe'idx]; exact hlt
    omega
  have hframeRidNe : frame.regionId ≠ cfg.freshRegionId := by
    obtain ⟨region1, hlookup1, -⟩ := l2_of_stackWithIndex vcfg hframeMemCfg
    intro heq
    apply RuntimeConfig.freshRegionId_not_mem cfg
    rw [← AList.mem_keys, ← AList.lookup_isSome, ← heq, hlookup1]
    simp
  have hidNe : oid ≠ cfg.freshObjectId := by
    intro heq
    subst heq
    obtain ⟨region1, hlookup1, hmem1⟩ := (oid_loc_rgn_iff_in_heap vcfg').mp hloc
    have hlookup1' : cfg.heap.lookup frame.regionId = some region1 := by
      rw [hcfg'] at hlookup1; dsimp only at hlookup1
      rw [AList.lookup_insert_ne hframeRidNe] at hlookup1
      exact hlookup1
    apply cfg.freshObjectId_not_mem
    unfold RuntimeConfig.objectIds
    rw [List.mem_append]
    right
    unfold Heap.objectIds
    rw [List.mem_flatten]
    exact ⟨region1.objectIds, List.mem_map_of_mem (AList.lookup_mem_entries hlookup1'), hmem1⟩
  have hloc_cfg : (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) := by
    rw [makeRegion_corollary_loc_eq vcfg h' oid hidNe]; exact hloc
  rcases makeRegion_frame_cases h' hframe'Mem with
    ⟨hframe'MemCfg, hframe'Lt⟩ | ⟨lf', hlf', hframe'RegionId, -, -, hframe'VarMap, hframe'Idx⟩
  · -- frame' is also not the last frame: unconditional iff transport both ways.
    have hreach_cfg : FrameReachable cfg frame'.index (Reference.OId oid) :=
      (makeRegion_frame_reachable_iff vcfg h' hframe'MemCfg hframe'Lt (Reference.OId oid)).mpr hreach
    have hresult_cfg : FrameReachable cfg frame.index (Reference.OId oid) :=
      hFR3 frame hframeMemCfg frame' hframe'MemCfg hlt oid hloc_cfg hreach_cfg
    exact (makeRegion_frame_reachable_iff vcfg h' hframeMemCfg hframeLt (Reference.OId oid)).mp hresult_cfg
  · -- frame' IS the last (mutated) frame.
    rw [hlast] at hlf'
    injection hlf' with hlf'
    subst hlf'
    rw [FrameReachable_iff_reflTransGen] at hreach
    obtain ⟨start, hroot, hrtg⟩ := hreach
    have hframe'Idx' : frame'.index = cfg.stack.length - 1 := by rw [hframe'Idx, List.length_dropLast]
    have hLfReach : FrameReachable cfg (cfg.stack.length - 1) (Reference.OId oid) := by
      rcases hroot with ⟨Xf, hXfmem, hXfidx, var, hvar⟩ | ⟨Xf, hXfmem, hXfidx, regionX, hlookupX, hbridge⟩
      · have hXfeq : Xf = frame' := swap_corollary_stackWithIndex_index_inj hXfmem hframe'Mem hXfidx
        rw [hXfeq, hframe'VarMap] at hvar
        by_cases hveq : var = x
        · subst hveq
          rw [AList.lookup_insert] at hvar
          injection hvar with hstart
          exfalso
          rw [← hstart] at hrtg
          rcases hrtg.cases_head with heqStart | ⟨c, hstep, hrest⟩
          · cases heqStart
          · rw [ReachableStep_rid_iff] at hstep
            obtain ⟨region2, hlookup2, -, hbeq⟩ := hstep
            have hlookup2' : cfg'.heap.lookup cfg.freshRegionId = some ({ bridgeObjectId := cfg.freshObjectId, objMap := (∅ : ObjMap).insert cfg.freshObjectId ∅, status := Status.Closed } : Region) := by
              rw [hcfg']; dsimp only; rw [AList.lookup_insert]
            rw [hlookup2'] at hlookup2
            injection hlookup2 with hlookup2eq
            rw [← hlookup2eq] at hbeq
            dsimp only at hbeq
            rw [hbeq] at hrest
            rcases hrest.cases_head with heq2 | ⟨c2, hstep2, -⟩
            · injection heq2 with heq2
              rw [← heq2, makeRegion_corollary_loc_fresh h'] at hloc
              injection hloc with hloc
              injection hloc with hloc
              exact hframeRidNe hloc.symm
            · rw [ReachableStep_oid_iff, makeRegion_fresh_objAt_cfg' h'] at hstep2
              obtain ⟨obj, hobjEq, hcontains⟩ := hstep2
              injection hobjEq with hobjEq
              rw [← hobjEq] at hcontains
              simp [Object.refs] at hcontains
        · rw [AList.lookup_insert_ne hveq] at hvar
          have hstackEq : cfg.stack = cfg.stack.dropLast ++ [lastFrame] :=
            (List.dropLast_append_getLast? lastFrame hlast).symm
          have hmemLast : lastFrame ∈ cfg.stack :=
            hstackEq ▸ List.mem_append_right _ (List.mem_singleton_self lastFrame)
          have hstartne : start ≠ Reference.RId cfg.freshRegionId := by
            intro heq
            rw [heq] at hvar
            have hmemrefs : Reference.RId cfg.freshRegionId ∈ lastFrame.refs :=
              mem_frame_refs_of_mem_varMap hvar
            have hmemStack : Reference.RId cfg.freshRegionId ∈ cfg.stack.refs := by
              rw [stack_refs_eq_flatMap, List.mem_flatMap]
              exact ⟨lastFrame, hmemLast, hmemrefs⟩
            have hmemCfg : Reference.RId cfg.freshRegionId ∈ cfg.refs := List.mem_append_left _ hmemStack
            exact RuntimeConfig.freshRegionId_not_mem cfg (vcfg.hs2 cfg.freshRegionId hmemCfg)
          obtain ⟨-, hrtgCfg⟩ := makeRegion_reflTransGen_transport_down vcfg h' hstartne hrtg
          exact (FrameReachable_iff_reflTransGen cfg (cfg.stack.length - 1) (Reference.OId oid)).mpr
            ⟨start, Or.inl ⟨{ lastFrame with index := cfg.stack.length - 1 }, hLf, rfl, var, hvar⟩, hrtgCfg⟩
      · have hXfeq : Xf = frame' := swap_corollary_stackWithIndex_index_inj hXfmem hframe'Mem hXfidx
        have hXfridEq : Xf.regionId = lastFrame.regionId := by rw [hXfeq]; exact hframe'RegionId
        have hne : Xf.regionId ≠ cfg.freshRegionId := by
          rw [hXfridEq]
          intro heq
          apply RuntimeConfig.freshRegionId_not_mem cfg
          rw [← AList.mem_keys, ← AList.lookup_isSome, ← heq, hlookupRid0]
          simp
        have hlookup' : cfg'.heap.lookup Xf.regionId = cfg.heap.lookup Xf.regionId := by
          rw [hcfg']; dsimp only; rw [AList.lookup_insert_ne hne]
        rw [hlookup', hXfridEq] at hlookupX
        have hstartne : start ≠ Reference.RId cfg.freshRegionId := by rw [hbridge]; simp
        obtain ⟨-, hrtgCfg⟩ := makeRegion_reflTransGen_transport_down vcfg h' hstartne hrtg
        exact (FrameReachable_iff_reflTransGen cfg (cfg.stack.length - 1) (Reference.OId oid)).mpr
          ⟨start, Or.inr ⟨{ lastFrame with index := cfg.stack.length - 1 }, hLf, rfl, regionX, hlookupX, hbridge⟩,
            hrtgCfg⟩
    have hlt' : frame.index < ({ lastFrame with index := cfg.stack.length - 1 } : FrameWithIndex).index := by
      show frame.index < cfg.stack.length - 1
      rw [← hframe'Idx']; exact hlt
    have hresult_cfg : FrameReachable cfg frame.index (Reference.OId oid) :=
      hFR3 frame hframeMemCfg _ hLf hlt' oid hloc_cfg hLfReach
    exact (makeRegion_frame_reachable_iff vcfg h' hframeMemCfg hframeLt (Reference.OId oid)).mp hresult_cfg
