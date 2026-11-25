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

theorem frameReachableAtLaterFrame_step_varAsgn (x : VarName) (yf : FieldAccess) :
    FrameReachableAtLaterFrame_step (Stmt.varAsgn x yf) := by
  intro cfg cfg' vcfg h hFR3 frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  have h' : varAsgn x yf cfg = some cfg' := h
  have hfr := index_lt_length_sub_one (varAsgn_length h') hframe'Mem hlt
  rw [← varAsgn_corollary_loc_eq vcfg h'] at hloc
  have hsr := varAsgn_suspended_reach vcfg h' hFR3
    ((varAsgn_frame_mem_iff h' (by simpa [RuntimeConfig.stackWithIndex] using hfr)).mpr hframeMem) hfr hloc
  exact hsr.2.1 (hsr.2.2 _ hreach)
