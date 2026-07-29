import Gc.Model.Preservation.Enter
import Gc.Model.Preservation.Exit
import Gc.Model.Preservation.FieldAsgn
import Gc.Model.Preservation.MakeObjRegion
import Gc.Model.Preservation.MakeObjStack
import Gc.Model.Preservation.MakeRegion
import Gc.Model.Preservation.Merge
import Gc.Model.Preservation.Swap
import Gc.Model.Preservation.VarAsgn
import Gc.Model.Mutation.Stmt

-- `Stmt`-generic preservation: a property `P` of configs is preserved by a single `step`, and
-- `AllPreserve P` says it's preserved no matter which of the 9 operations ran.
def StepPreserves (P : RuntimeConfig → Prop) (cmd : Stmt) : Prop :=
  ∀ cfg cfg', step cmd cfg = some cfg' → P cfg → P cfg'

def AllPreserve (P : RuntimeConfig → Prop) : Prop :=
  ∀ (cmd : Stmt), StepPreserves P cmd

def allPreserve_ValidConfig : AllPreserve ValidConfig := by
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
