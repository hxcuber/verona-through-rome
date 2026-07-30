import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Mutation.Mutation
import Gc.Model.Mutation.Stmt
import Gc.Model.Preservation
import Gc.Reachability.Reachable.Semantics
import Gc.Reachability.Reachable.Corollaries
import Gc.Reachability.Reachable.Lemmas

-- Per-operation skeletons for `StackReachable_invariant_for_suspended_region_objects`
-- (defined in `Gc/Reachability/Reachable/Corollaries.lean`), one per `Stmt` constructor,
-- ordered easiest-to-hardest per the plan: additive/untouched-key ops first
-- (enter/exit/makeObjStack/makeObjRegion/makeRegion/merge), then the ops that genuinely
-- mutate existing content (varAsgn, fieldAsgn, swap).

theorem stackReachable_invariant_enter (xf : FieldAccess) (bridgeVar : VarName) :
    StackReachable_invariant_for_suspended_region_objects (Stmt.enter xf bridgeVar) := by
  sorry

theorem stackReachable_invariant_exit :
    StackReachable_invariant_for_suspended_region_objects Stmt.exit := by
  sorry

theorem stackReachable_invariant_makeObjStack (x : VarName) :
    StackReachable_invariant_for_suspended_region_objects (Stmt.makeObjStack x) := by
  sorry

theorem stackReachable_invariant_makeObjRegion (x : VarName) :
    StackReachable_invariant_for_suspended_region_objects (Stmt.makeObjRegion x) := by
  sorry

theorem stackReachable_invariant_makeRegion (x : VarName) :
    StackReachable_invariant_for_suspended_region_objects (Stmt.makeRegion x) := by
  sorry

theorem stackReachable_invariant_merge (x : VarName) :
    StackReachable_invariant_for_suspended_region_objects (Stmt.merge x) := by
  sorry

theorem stackReachable_invariant_varAsgn (x : VarName) (yf : FieldAccess) :
    StackReachable_invariant_for_suspended_region_objects (Stmt.varAsgn x yf) := by
  sorry

theorem stackReachable_invariant_fieldAsgn (xf : FieldAccess) (y : VarName) :
    StackReachable_invariant_for_suspended_region_objects (Stmt.fieldAsgn xf y) := by
  sorry

theorem stackReachable_invariant_swap (x : VarName) (yf : FieldAccess) :
    StackReachable_invariant_for_suspended_region_objects (Stmt.swap x yf) := by
  sorry

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
