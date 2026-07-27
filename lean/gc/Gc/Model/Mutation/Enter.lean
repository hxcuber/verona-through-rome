import Gc.Model.Helpers
import Gc.Model.Types

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
  cases hresolve : resolveFA xf cfg with
  | none => rw [hresolve] at h; contradiction
  | some xfRef =>
    rw [hresolve] at h
    dsimp at h
    cases xfRef with
    | OId _ => contradiction
    | RId rid =>
      dsimp at h
      cases hheapLookup : cfg.heap.lookup rid with
      | none => rw [hheapLookup] at h; contradiction
      | some region =>
        rw [hheapLookup] at h
        dsimp at h
        cases hstatus : region.status with
        | Open => rw [hstatus] at h; contradiction
        | Closed =>
          rw [hstatus] at h
          rw [if_pos (by rfl)] at h
          rw [Option.some_inj] at h
          exact ⟨rid, region, rfl, hheapLookup, hstatus, h.symm⟩
