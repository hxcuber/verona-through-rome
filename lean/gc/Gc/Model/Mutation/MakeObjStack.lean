import Gc.Model.Helpers
import Gc.Model.Types

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
  cases hframe : cfg.stack.getLast? with
  | none => rw [hframe] at h; contradiction
  | some frame =>
    rw [hframe] at h
    dsimp at h
    rw [Option.some_inj] at h
    exact ⟨frame, rfl, h.symm⟩
