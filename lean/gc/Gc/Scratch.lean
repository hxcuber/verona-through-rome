import Gc.Model.Types
import Gc.Model.Mutation.Mutation
import Gc.Model.Validity
import Gc.Model.Preservation
import Gc.Reachability.Validity.Reachable
import Gc.Reachability.Validity.Preservation

inductive Stmt where
  | enter (xf : FieldAccess) (bridgeVar : VarName)
  | exit
  | fieldAsgn (xf : FieldAccess) (y : VarName)
  | makeObjRegion (x : VarName)
  | makeObjStack (x : VarName)
  | makeRegion (x : VarName)
  | merge (x : VarName)
  | swap (x : VarName) (yf : FieldAccess)
  | varAsgn (x : VarName) (yf : FieldAccess)

def step (stmt : Stmt) (cfg : RuntimeConfig) : Option (RuntimeConfig) :=
  match stmt with
  | Stmt.enter xf bridgeVar => enter xf bridgeVar cfg
  | Stmt.exit => exit cfg
  | Stmt.fieldAsgn xf y => fieldAsgn xf y cfg
  | Stmt.makeObjRegion x => makeObjRegion x cfg
  | Stmt.makeObjStack x => makeObjStack x cfg
  | Stmt.makeRegion x => makeRegion x cfg
  | Stmt.merge x => merge x cfg
  | Stmt.swap x yf => swap x yf cfg
  | Stmt.varAsgn x yf => varAsgn x yf cfg

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

def allPreserve_ValidReachableConfig : AllPreserve ValidReachableConfig := by
  intro cmd cfg cfg' hstep hvalid
  simp [step] at hstep
  cases cmd with
  | enter xf bridgeVar => exact enter_reachable_valid hvalid hstep
  | exit               => exact exit_reachable_valid hvalid hstep
  | fieldAsgn xf y     => exact fieldAsgn_reachable_valid hvalid hstep
  | makeObjRegion x    => exact makeObjRegion_reachable_valid hvalid hstep
  | makeObjStack x     => exact makeObjStack_reachable_valid hvalid hstep
  | makeRegion x       => exact makeRegion_reachable_valid hvalid hstep
  | merge x            => exact merge_reachable_valid hvalid hstep
  | swap x yf          => exact swap_reachable_valid hvalid hstep
  | varAsgn x yf       => exact varAsgn_reachable_valid hvalid hstep
