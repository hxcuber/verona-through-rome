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

theorem frameReachableAtLaterFrame_step_swap (x : VarName) (yf : FieldAccess) :
    FrameReachableAtLaterFrame_step (Stmt.swap x yf) := by
  intro cfg cfg' vcfg h hFR3 frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  have h' : swap x yf cfg = some cfg' := h
  obtain ⟨frame0, hframe0, -⟩ := swap_cases h'
  obtain ⟨Gf0, hGf0mem, hidxGf0, hridGf0, -⟩ := swap_frame_transport_down h' frame hframeMem
  obtain ⟨Gd, hGdmem, hidxGd, -, -⟩ := swap_frame_transport_down h' frame' hframe'Mem
  have hloc_cfg : (Reference.OId oid).loc? cfg = some (Location.Rgn Gf0.regionId) := by
    rw [hridGf0, ← swap_loc_eq vcfg h' oid, hloc]
  have hframeLt : frame.index < cfg.stack.dropLast.length :=
    (stack_eq_of_stackWithIndex_getLast? hframe0).2 ▸ hlt.trans_le (hidxGd ▸ index_le_last hframe0 hGdmem)
  exact (swap_frame_reachable_iff_of_lt vcfg (swap_valid vcfg h') h' frame hframeLt _).mp
    (hidxGf0 ▸ FrameReachable_of_StackReachable vcfg hFR3 hGf0mem hloc_cfg (swap_reach_down vcfg h' hframe'Mem hreach))
