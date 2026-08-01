import Gc.Model.Types
import Gc.Model.Mutation.Mutation

-- A single `Mutation.lean` operation, reified as data so it can be quantified over (used by
-- `Gc/Reachability/Referencable/Basic.lean`/`CR5/*.lean` to state "every operation" facts, and by `AllPreserve`
-- below to dispatch a generic config-preservation claim to each operation's own proof).
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
