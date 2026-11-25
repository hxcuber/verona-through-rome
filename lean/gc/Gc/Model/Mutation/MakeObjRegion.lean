module

public import Gc.Model.Helpers
public import Gc.Model.Types

@[expose] public section

def makeObjRegion (x : VarName) (cfg : RuntimeConfig) : Option (RuntimeConfig) := do
  let frame ← cfg.stack.getLast?
  let region ← cfg.heap.lookup frame.regionId
  let newObjId := cfg.freshObjectId
  if region.status == Status.Open then
    some { cfg with
      stack := cfg.stack.dropLast ++ [ { frame with
        varMap := frame.varMap.insert x (Reference.OId newObjId)
      } ],
      heap := cfg.heap.insert frame.regionId { region with
        objMap := region.objMap.insert newObjId ∅
      }
    }
  else
    none

theorem makeObjRegion_cases {cfg cfg' : RuntimeConfig} (h : makeObjRegion x cfg = some cfg') :
    ∃ frame region, cfg.stack.getLast? = some frame ∧ cfg.heap.lookup frame.regionId = some region ∧
      region.status = Status.Open ∧
      cfg' = { cfg with
        stack := cfg.stack.dropLast ++ [ { frame with
          varMap := frame.varMap.insert x (Reference.OId cfg.freshObjectId) } ],
        heap := cfg.heap.insert frame.regionId { region with
          objMap := region.objMap.insert cfg.freshObjectId ∅ } } := by
  unfold makeObjRegion at h
  rcases hframe : cfg.stack.getLast? with _ | frame
  · simp_all
  · rcases hl : cfg.heap.lookup frame.regionId with _ | region
    · simp_all
    · cases hs : region.status <;> simp_all
      exact absurd h.1 (by decide)
