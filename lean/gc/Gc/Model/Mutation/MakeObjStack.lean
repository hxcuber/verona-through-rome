module

public import Gc.Model.Helpers
public import Gc.Model.Types

@[expose] public section

def makeObjStack (x : VarName) (cfg : RuntimeConfig) : Option (RuntimeConfig) := do
  let frame ← cfg.stack.getLast?
  let newObjId := cfg.freshObjectId
  some { cfg with
    stack := cfg.stack.dropLast ++ [ { frame with
      varMap := frame.varMap.insert x (Reference.OId newObjId),
      objMap := frame.objMap.insert newObjId ∅
    } ]
  }

theorem makeObjStack_cases {cfg cfg' : RuntimeConfig} (h : makeObjStack x cfg = some cfg') :
    ∃ frame, cfg.stack.getLast? = some frame ∧
      cfg' = { cfg with
        stack := cfg.stack.dropLast ++ [ { frame with
          varMap := frame.varMap.insert x (Reference.OId cfg.freshObjectId),
          objMap := frame.objMap.insert cfg.freshObjectId ∅
        } ] } := by
  unfold makeObjStack at h
  rcases hframe : cfg.stack.getLast? with _ | frame <;> simp_all
