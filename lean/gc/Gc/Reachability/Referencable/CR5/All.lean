import Gc.Reachability.Referencable.Basic
import Gc.Model.Mutation.Stmt
import Gc.Reachability.Referencable.CR5.Enter
import Gc.Reachability.Referencable.CR5.Exit
import Gc.Reachability.Referencable.CR5.FieldAsgn
import Gc.Reachability.Referencable.CR5.MakeObjRegion
import Gc.Reachability.Referencable.CR5.MakeObjStack
import Gc.Reachability.Referencable.CR5.MakeRegion
import Gc.Reachability.Referencable.CR5.Merge
import Gc.Reachability.Referencable.CR5.Swap
import Gc.Reachability.Referencable.CR5.VarAsgn

-- Every operation satisfies CR5_step -- the layer-1 statement, in full generality. Each of the 9
-- cases already closes with `cr5_step_of_helper` internally (see each proof's own `apply
-- cr5_step_of_helper` first line), so there's no separately-named `CR5_helper_step` dispatcher
-- anymore -- if a future multi-step generalization ends up needing that iff-chaining form again,
-- it'll have to be re-derived (each op's proof still proves it internally, just not under a name).
theorem cr5_step_all : ∀ cmd, CR5_step cmd := by
  intro cmd
  cases cmd with
  | enter xf a => exact cr5_step_enter xf a
  | exit => exact cr5_step_exit
  | fieldAsgn xf y => exact cr5_step_fieldAsgn xf y
  | makeObjRegion x => exact cr5_step_makeObjRegion x
  | makeObjStack x => exact cr5_step_makeObjStack x
  | makeRegion x => exact cr5_step_makeRegion x
  | merge x => exact cr5_step_merge x
  | swap x yf => exact cr5_step_swap x yf
  | varAsgn x yf => exact cr5_step_varAsgn x yf
