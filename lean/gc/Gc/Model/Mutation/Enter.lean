module

public import Gc.Model.Helpers

@[expose] public section

def enter (xf : FieldAccess) (bridgeVar : VarName) (cfg : RuntimeConfig) : Option (RuntimeConfig) := do
  let xfRef ← resolveFA xf cfg
  match xfRef with
  | Reference.OId _ => none
  | Reference.RId rid =>
    let region ← cfg.heap.lookup rid
    if region.status == Status.Closed then
      some { cfg with
        stack := cfg.stack ++
        [ { regionId := rid,
            bridgeVar := bridgeVar,
            objMap := ∅,
            varMap := ∅
        } ]
        heap := cfg.heap.insert rid { region with status := Status.Open }
      }
    else
      none

theorem enter_cases {cfg cfg' : RuntimeConfig} (h : enter xf a cfg = some cfg') :
    ∃ rid region, resolveFA xf cfg = some (Reference.RId rid) ∧ cfg.heap.lookup rid = some region ∧
      region.status = Status.Closed ∧
      cfg' = { cfg with
        stack := cfg.stack ++ [{ regionId := rid, bridgeVar := a, objMap := ∅, varMap := ∅ }],
        heap := cfg.heap.insert rid { region with status := Status.Open } } := by
  unfold enter at h
  rcases hr : resolveFA xf cfg with _ | _ | _ | rid <;> simp [hr] at h
  rename_i rid
  rcases hl : cfg.heap.lookup rid with _ | region
  · simp_all
  · cases hs : region.status <;> simp_all
    exact absurd h.1 (by decide)
