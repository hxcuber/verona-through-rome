module

public import Gc.Model.Helpers

public import Mathlib.Data.List.Infix

@[expose] public section

def merge (x : VarName) (cfg : RuntimeConfig) : Option (RuntimeConfig) := do
  let frame ← cfg.stack.getLast?
  let xRef ← frame.varMap.lookup x
  match xRef with
  | Reference.OId _ => none
  | Reference.RId rid' =>
    let region ← cfg.heap.lookup frame.regionId
    let region' ← cfg.heap.lookup rid'
    if region'.status = Status.Closed ∧ region.status = Status.Open then
      some { cfg with
        heap := (cfg.heap.erase rid').insert frame.regionId { region with
          objMap := region.objMap.union region'.objMap
        }
        stack := cfg.stack.dropLast ++ [ { frame with
          varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId)
        } ]
      }
    else
      none

theorem merge_cases (h : merge x cfg = some cfg') :
    ∃ frame rid' region region',
      cfg.stack.getLast? = some frame ∧
      frame.varMap.lookup x = some (Reference.RId rid') ∧
      cfg.heap.lookup frame.regionId = some region ∧
      cfg.heap.lookup rid' = some region' ∧
      region'.status = Status.Closed ∧ region.status = Status.Open ∧
      cfg' = { cfg with
        heap := (cfg.heap.erase rid').insert frame.regionId { region with
          objMap := region.objMap.union region'.objMap },
        stack := cfg.stack.dropLast ++
          [ { frame with varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) } ]
      } := by
  unfold merge at h
  rcases hframe : cfg.stack.getLast? with _ | frame
  · simp_all
  · rcases hx : frame.varMap.lookup x with _ | ⟨rid' | oid⟩
    · simp_all
    · rcases hr : cfg.heap.lookup frame.regionId with _ | region <;>
        rcases hr' : cfg.heap.lookup rid' with _ | region' <;> simp_all
    · simp_all
