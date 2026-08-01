import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Mutation.Mutation
import Gc.Model.Mutation.Stmt
import Gc.Model.Preservation
import Gc.Reachability.Reachable.Semantics
import Gc.Reachability.Reachable.Basic
import Gc.Reachability.Reachable.Lemmas
import Gc.Reachability.Reachable.StackReachableInvariant.Enter
import Gc.Reachability.Reachable.StackReachableInvariant.Exit
import Gc.Reachability.Reachable.StackReachableInvariant.MakeObjStack
import Gc.Reachability.Reachable.StackReachableInvariant.MakeObjRegion
import Gc.Reachability.Reachable.StackReachableInvariant.MakeRegion
import Gc.Reachability.Reachable.StackReachableInvariant.Merge
import Gc.Reachability.Reachable.StackReachableInvariant.VarAsgn
import Gc.Reachability.Reachable.StackReachableInvariant.FieldAsgn
import Gc.Reachability.Reachable.StackReachableInvariant.Swap

theorem stackReachable_invariant_all (cmd : Stmt) :
    StackReachable_invariant_for_suspended_region_objects cmd := by
  cases cmd with
  | enter xf bridgeVar => exact stackReachable_invariant_enter xf bridgeVar
  | exit => exact stackReachable_invariant_exit
  | fieldAsgn xf y => exact stackReachable_invariant_fieldAsgn xf y
  | makeObjRegion x => exact stackReachable_invariant_makeObjRegion x
  | makeObjStack x => exact stackReachable_invariant_makeObjStack x
  | makeRegion x => exact stackReachable_invariant_makeRegion x
  | merge x => exact stackReachable_invariant_merge x
  | swap x yf => exact stackReachable_invariant_swap x yf
  | varAsgn x yf => exact stackReachable_invariant_varAsgn x yf

