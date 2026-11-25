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

theorem frameReachableAtLaterFrame_step_fieldAsgn (xf : FieldAccess) (y : VarName) :
    FrameReachableAtLaterFrame_step (Stmt.fieldAsgn xf y) := by
  intro cfg cfg' vcfg h hFR3 frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  have h' : fieldAsgn xf y cfg = some cfg' := h
  obtain ⟨hlen, hlocEq, hmemIff⟩ := fieldAsgn_shape vcfg h'
  have hfr := index_lt_length_sub_one hlen hframe'Mem hlt
  rw [hlocEq] at hloc
  have hsr := fieldAsgn_suspended_reach vcfg h' hFR3 ((hmemIff frame hfr).mpr hframeMem) hfr hloc
  exact hsr.2.1 (hsr.2.2 _ hreach)
