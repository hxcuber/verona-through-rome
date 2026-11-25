module

public import Gc.Model.Types
public import Gc.Model.Helpers
public import Gc.Model.Validity
public import Gc.Model.Mutation.Mutation
public import Gc.Model.Mutation.Stmt
public import Gc.Model.Preservation
public import Gc.Reachability.Reachable.Semantics
public import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.Def
public import Gc.Reachability.Reachable.Lemmas

@[expose] public section

theorem frameReachableAtLaterFrame_step_exit :
    FrameReachableAtLaterFrame_step Stmt.exit := by
  intro cfg cfg' vcfg h hFR3 frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  have h' : exit cfg = some cfg' := h
  obtain ⟨poppedFrame, region0, hlen, hlast, hlookupRid, hopenRid, hcfg'⟩ := exit_cases h'
  obtain ⟨hframeMemCfg, hframeLt⟩ := exit_frame_mem_down h' hframeMem
  obtain ⟨hframe'MemCfg, -⟩ := exit_frame_mem_down h' hframe'Mem
  obtain ⟨region, hlookup, hopen⟩ := l2_of_stackWithIndex vcfg hframeMemCfg
  have hridNe : frame.regionId ≠ poppedFrame.regionId := regionId_ne_last_of_suspended vcfg hframeMemCfg hframeLt hlast
  have hlookup' : cfg'.heap.lookup frame.regionId = some region := by
    rw [hcfg']; dsimp only; rw [AList.lookup_insert_ne hridNe]; exact hlookup
  have hloc_cfg : (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) := by
    rw [oid_loc_rgn_iff_in_heap vcfg]
    rw [oid_loc_rgn_iff_in_heap (exit_valid vcfg h')] at hloc
    obtain ⟨region1, hlookup1, hmem1⟩ := hloc
    rw [hlookup'] at hlookup1
    injection hlookup1 with hregionEq
    exact ⟨region, hlookup, hregionEq ▸ hmem1⟩
  have hreach_cfg : FrameReachable cfg frame'.index (Reference.OId oid) :=
    exit_frame_reachable_transport_backward vcfg h' hlast hcfg' hlookup hlookup' hopen hloc hframe'Mem hreach
  have hresult_cfg : FrameReachable cfg frame.index (Reference.OId oid) :=
    hFR3 frame hframeMemCfg frame' hframe'MemCfg hlt oid hloc_cfg hreach_cfg
  exact exit_frame_reachable_transport vcfg h' hlast hcfg' hlookup hopen hloc_cfg
    hframeMemCfg hframeLt hresult_cfg
