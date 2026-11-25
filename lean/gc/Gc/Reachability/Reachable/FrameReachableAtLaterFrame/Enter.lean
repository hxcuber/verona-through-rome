module

public import Gc.Reachability.Reachable.Lemmas

@[expose] public section

theorem frameReachableAtLaterFrame_step_enter (xf : FieldAccess) (bridgeVar : VarName) :
    FrameReachableAtLaterFrame_step (Stmt.enter xf bridgeVar) := by
  intro cfg cfg' vcfg h hFR3 frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  have h' : enter xf bridgeVar cfg = some cfg' := h
  obtain ⟨_, _, -, -, -, hcfg'⟩ := enter_cases h'
  obtain ⟨hfm, hflt⟩ : frame ∈ cfg.stackWithIndex ∧ frame.index < cfg.stack.length := by
    rcases enter_frame_cases hcfg' hframeMem with hh | ⟨-, -, -, -, hidx⟩
    · exact hh
    · exfalso
      rcases enter_frame_cases hcfg' hframe'Mem with ⟨-, h2⟩ | ⟨-, -, -, -, h2⟩ <;> grind
  have hloc_cfg : (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) := by
    rwa [enter_corollary_2 vcfg h' oid]
  obtain ⟨hiff, hnew⟩ := enter_suspended_reach vcfg h' hfm hloc_cfg
  rcases enter_frame_cases hcfg' hframe'Mem with ⟨hf'm, -⟩ | ⟨-, -, -, -, hidx'⟩
  · exact (hiff frame hfm).mp (hFR3 frame hfm frame' hf'm hlt oid hloc_cfg ((hiff frame' hf'm).mpr hreach))
  · exact absurd (hidx' ▸ hreach) hnew
