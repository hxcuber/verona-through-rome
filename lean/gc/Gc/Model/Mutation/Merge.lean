import Gc.Model.Helpers
import Gc.Model.Types

import Mathlib.Data.List.Infix

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
  cases hframe : cfg.stack.getLast? with
  | none => rw [hframe] at h; contradiction
  | some frame =>
    rw [hframe] at h
    dsimp at h
    cases hxref : frame.varMap.lookup x with
    | none => rw [hxref] at h; contradiction
    | some xRef =>
      rw [hxref] at h
      dsimp at h
      cases xRef with
      | OId oid0 => dsimp at h; contradiction
      | RId rid' =>
        dsimp at h
        cases hregion : cfg.heap.lookup frame.regionId with
        | none => rw [hregion] at h; contradiction
        | some region =>
          rw [hregion] at h
          dsimp at h
          cases hregion' : cfg.heap.lookup rid' with
          | none => rw [hregion'] at h; contradiction
          | some region' =>
            rw [hregion'] at h
            dsimp at h
            by_cases hcond : region'.status = Status.Closed ∧ region.status = Status.Open
            · rw [if_pos hcond] at h
              rw [Option.some_inj] at h
              exact ⟨frame, rid', region, region', rfl, hxref, hregion, hregion', hcond.1, hcond.2, h.symm⟩
            · rw [if_neg hcond] at h; contradiction
