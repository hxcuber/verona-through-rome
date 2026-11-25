module

public import Gc.Model.Preservation.Enter
public import Gc.Model.Preservation.Exit
public import Gc.Model.Preservation.FieldAsgn
public import Gc.Model.Preservation.MakeObjRegion
public import Gc.Model.Preservation.MakeObjStack
public import Gc.Model.Preservation.MakeRegion
public import Gc.Model.Preservation.Merge
public import Gc.Model.Preservation.Swap
public import Gc.Model.Preservation.VarAsgn
public import Gc.Model.Mutation.Stmt

@[expose] public section

-- `StepPreserves P cmd`: one `step cmd` preserves `P`; `AllPreserve P`: every operation does.
def StepPreserves (P : RuntimeConfig → Prop) (cmd : Stmt) : Prop :=
  ∀ cfg cfg', step cmd cfg = some cfg' → P cfg → P cfg'

def AllPreserve (P : RuntimeConfig → Prop) : Prop :=
  ∀ (cmd : Stmt), StepPreserves P cmd

theorem allPreserve_ValidConfig : AllPreserve ValidConfig := by
  intro cmd cfg cfg' hstep hvalid
  simp [step] at hstep
  cases cmd with
  | enter xf bridgeVar => exact enter_valid hvalid hstep
  | exit               => exact exit_valid hvalid hstep
  | fieldAsgn xf y     => exact fieldAsgn_valid hvalid hstep
  | makeObjRegion x    => exact makeObjRegion_valid hvalid hstep
  | makeObjStack x     => exact makeObjStack_valid hvalid hstep
  | makeRegion x       => exact makeRegion_valid hvalid hstep
  | merge x            => exact merge_valid hvalid hstep
  | swap x yf          => exact swap_valid hvalid hstep
  | varAsgn x yf       => exact varAsgn_valid hvalid hstep
