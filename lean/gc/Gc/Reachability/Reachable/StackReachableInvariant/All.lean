module

public import Gc.Reachability.Reachable.StackReachableInvariant.Enter
public import Gc.Reachability.Reachable.StackReachableInvariant.Exit
public import Gc.Reachability.Reachable.StackReachableInvariant.MakeObjStack
public import Gc.Reachability.Reachable.StackReachableInvariant.MakeObjRegion
public import Gc.Reachability.Reachable.StackReachableInvariant.MakeRegion
public import Gc.Reachability.Reachable.StackReachableInvariant.Merge
public import Gc.Reachability.Reachable.StackReachableInvariant.VarAsgn
public import Gc.Reachability.Reachable.StackReachableInvariant.FieldAsgn
public import Gc.Reachability.Reachable.StackReachableInvariant.Swap

@[expose] public section

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

