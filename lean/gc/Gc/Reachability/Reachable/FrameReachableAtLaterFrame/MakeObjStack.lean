import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Mutation.Mutation
import Gc.Model.Mutation.Stmt
import Gc.Model.Preservation
import Gc.Reachability.Reachable.Semantics
import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.Def
import Gc.Reachability.Reachable.Lemmas

theorem frameReachableAtLaterFrame_step_makeObjStack (x : VarName) :
    FrameReachableAtLaterFrame_step (Stmt.makeObjStack x) := by
  intro cfg cfg' vcfg h hFR3 frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  have h' : makeObjStack x cfg = some cfg' := h
  have vcfg' : ValidConfig cfg' := makeObjStack_valid vcfg h'
  obtain ⟨lastFrame, hlast, hcfg'⟩ := makeObjStack_cases h'
  have hLf : ({ lastFrame with index := cfg.stack.length - 1 } : FrameWithIndex) ∈ cfg.stackWithIndex :=
    stackWithIndex_getLast_mem hlast
  have hne' : cfg.stack ≠ [] := by intro hnil; rw [hnil] at hlast; simp at hlast
  have hlen1 : 1 ≤ cfg.stack.length := List.length_pos_of_ne_nil hne'
  have hcfg'len : cfg'.stack.length = cfg.stack.length := by
    rw [hcfg']; dsimp only; rw [List.length_append, List.length_dropLast, List.length_singleton]; omega
  rcases makeObjStack_frame_cases hlast hcfg' hframeMem with
    ⟨hframeMemCfg, hframeLt⟩ | ⟨-, -, -, -, hframeIdx⟩
  swap
  · exfalso
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hframe'Mem
    have hframe'idx : frame'.index = n := by rw [← hfeq]
    rw [hcfg'len] at hn
    have hcontra : cfg.stack.length - 1 < n := by
      have heq1 : cfg.stack.length - 1 = frame.index := by rw [hframeIdx, List.length_dropLast]
      rw [heq1, ← hframe'idx]; exact hlt
    omega
  have hidNe : oid ≠ cfg.freshObjectId := by
    intro heq
    subst heq
    obtain ⟨region1, hlookup1, hmem1⟩ := (oid_loc_rgn_iff_in_heap vcfg').mp hloc
    have hlookup1' : cfg.heap.lookup frame.regionId = some region1 := by rw [hcfg'] at hlookup1; exact hlookup1
    apply cfg.freshObjectId_not_mem
    unfold RuntimeConfig.objectIds
    rw [List.mem_append]
    right
    unfold Heap.objectIds
    rw [List.mem_flatten]
    exact ⟨region1.objectIds, List.mem_map_of_mem (AList.lookup_mem_entries hlookup1'), hmem1⟩
  have hloc_cfg : (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) := by
    rw [makeObjStack_loc_eq_of_ne h' hidNe]; exact hloc
  rcases makeObjStack_frame_cases hlast hcfg' hframe'Mem with
    ⟨hframe'MemCfg, hframe'Lt⟩ | ⟨hframe'RegionId, -, hframe'VarMap, -, hframe'Idx⟩
  · -- frame' is also not the last frame: unconditional iff transport both ways.
    have hreach_cfg : FrameReachable cfg frame'.index (Reference.OId oid) :=
      (makeObjStack_frame_reachable_iff h' hframe'MemCfg hframe'Lt (Reference.OId oid)).mpr hreach
    have hresult_cfg : FrameReachable cfg frame.index (Reference.OId oid) :=
      hFR3 frame hframeMemCfg frame' hframe'MemCfg hlt oid hloc_cfg hreach_cfg
    exact (makeObjStack_frame_reachable_iff h' hframeMemCfg hframeLt (Reference.OId oid)).mp hresult_cfg
  · -- frame' IS the mutated frame: its chain came from lastFrame's pre-existing roots, or a fresh root that's a dead end (can't reach `oid`).
    rw [FrameReachable_iff_reflTransGen] at hreach
    obtain ⟨start, hroot, hrtg⟩ := hreach
    rw [← makeObjStack_step_eq h'] at hrtg
    have hframe'Idx' : frame'.index = cfg.stack.length - 1 := by rw [hframe'Idx, List.length_dropLast]
    have hLfReach : FrameReachable cfg (cfg.stack.length - 1) (Reference.OId oid) := by
      rcases hroot with ⟨Xf, hXfmem, hXfidx, var, hvar⟩ | ⟨Xf, hXfmem, hXfidx, region, hlookupX, hbridge⟩
      · have hXfeq : Xf = frame' := swap_corollary_stackWithIndex_index_inj hXfmem hframe'Mem hXfidx
        rw [hXfeq, hframe'VarMap] at hvar
        by_cases hveq : var = x
        · subst hveq
          rw [AList.lookup_insert] at hvar
          injection hvar with hstart
          exfalso
          rw [← hstart] at hrtg
          rcases hrtg.cases_head with heqStart | ⟨c, hstep, -⟩
          · rw [← heqStart] at hloc_cfg
            exact freshObjectId_loc_ne_rgn hloc_cfg
          · rw [ReachableStep_oid_iff] at hstep
            obtain ⟨obj, hobjAt, -⟩ := hstep
            rw [freshObjectId_objAt_none] at hobjAt
            exact absurd hobjAt (by simp)
        · rw [AList.lookup_insert_ne hveq] at hvar
          exact (FrameReachable_iff_reflTransGen cfg (cfg.stack.length - 1) (Reference.OId oid)).mpr
            ⟨start, Or.inl ⟨{ lastFrame with index := cfg.stack.length - 1 }, hLf, rfl, var, hvar⟩, hrtg⟩
      · have hXfeq : Xf = frame' := swap_corollary_stackWithIndex_index_inj hXfmem hframe'Mem hXfidx
        have hlookup' : cfg.heap.lookup Xf.regionId = some region := by rw [hcfg'] at hlookupX; exact hlookupX
        rw [hXfeq, hframe'RegionId] at hlookup'
        exact (FrameReachable_iff_reflTransGen cfg (cfg.stack.length - 1) (Reference.OId oid)).mpr
          ⟨start, Or.inr ⟨{ lastFrame with index := cfg.stack.length - 1 }, hLf, rfl, region, hlookup', hbridge⟩, hrtg⟩
    have hlt' : frame.index < ({ lastFrame with index := cfg.stack.length - 1 } : FrameWithIndex).index := by
      show frame.index < cfg.stack.length - 1
      rw [← hframe'Idx']; exact hlt
    have hresult_cfg : FrameReachable cfg frame.index (Reference.OId oid) :=
      hFR3 frame hframeMemCfg _ hLf hlt' oid hloc_cfg hLfReach
    exact (makeObjStack_frame_reachable_iff h' hframeMemCfg hframeLt (Reference.OId oid)).mp hresult_cfg
