module

public import Gc.Reachability.Reachable.Lemmas

@[expose] public section

theorem frameReachableAtLaterFrame_step_exit :
    FrameReachableAtLaterFrame_step Stmt.exit := by
  intro cfg cfg' vcfg h hFR3 frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  have h' : exit cfg = some cfg' := h
  obtain ⟨hfm, hflt⟩ := exit_frame_mem_down h' hframeMem
  obtain ⟨hf'm, hf'lt⟩ := exit_frame_mem_down h' hframe'Mem
  obtain ⟨hloc_cfg, hiff⟩ := exit_suspended_reach vcfg h' hfm hflt hloc
  exact (hiff frame hfm hflt).mp (hFR3 frame hfm frame' hf'm hlt oid hloc_cfg ((hiff frame' hf'm hf'lt).mpr hreach))
