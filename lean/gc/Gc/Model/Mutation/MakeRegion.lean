import Gc.Model.Helpers
import Gc.Model.Types

def makeRegion (x : VarName) (cfg : RuntimeConfig) : Option (RuntimeConfig) := do
  let frame ← cfg.stack.getLast?
  let newRegionId := cfg.freshRegionId
  let newObjectId := cfg.freshObjectId
  some { cfg with
    stack := cfg.stack.dropLast ++ [ { frame with
      varMap := frame.varMap.insert x (Reference.RId newRegionId)
    } ],
    heap := cfg.heap.insert newRegionId {
      status := Status.Closed,
      objMap := (∅ : ObjMap).insert newObjectId ∅,
      bridgeObjectId := newObjectId
    }
  }

theorem makeRegion_cases {cfg cfg' : RuntimeConfig} (h : makeRegion x cfg = some cfg') :
    ∃ frame, cfg.stack.getLast? = some frame ∧
      cfg' = { cfg with
        stack := cfg.stack.dropLast ++ [ { frame with
          varMap := frame.varMap.insert x (Reference.RId cfg.freshRegionId) } ],
        heap := cfg.heap.insert cfg.freshRegionId {
          status := Status.Closed,
          objMap := (∅ : ObjMap).insert cfg.freshObjectId ∅,
          bridgeObjectId := cfg.freshObjectId
        } } := by
  unfold makeRegion at h
  cases hframe : cfg.stack.getLast? with
  | none => rw [hframe] at h; contradiction
  | some frame =>
    rw [hframe] at h
    dsimp at h
    rw [Option.some_inj] at h
    exact ⟨frame, rfl, h.symm⟩
