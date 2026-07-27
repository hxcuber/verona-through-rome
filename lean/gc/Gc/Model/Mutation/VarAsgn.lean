import Gc.Model.Helpers
import Gc.Model.Types

import Mathlib.Data.List.Infix

def varAsgn (x : VarName) (yf : FieldAccess) (cfg : RuntimeConfig) : Option (RuntimeConfig) := do
  let frame ← cfg.stack.getLast?
  let yfRef ← resolveFA yf cfg
  match yfRef with
  | Reference.RId _ => none
  | Reference.OId oid =>
    if x == frame.bridgeVar then
      let yfRefLoc ← yfRef.loc? cfg
      match yfRefLoc with
      | Location.Stk _ => none
      | Location.Rgn rid =>
        if frame.regionId == rid then
          let region ← cfg.heap.lookup rid
          some { cfg with
            heap := cfg.heap.insert rid { region with bridgeObjectId := oid }
          }
        else
          none
    else
      if resolveV x cfg == none then
        some { cfg with
          stack := cfg.stack.dropLast ++ [ { frame with varMap := frame.varMap.insert x yfRef } ]
        }
      else
        none

theorem varAsgn_cases (h : varAsgn xf y cfg = some cfg') :
    ∃ frame, cfg.stack.getLast? = some frame ∧
      ((∃ oid rid region,
          resolveFA y cfg = some (Reference.OId oid) ∧
          xf = frame.bridgeVar ∧
          (Reference.OId oid).loc? cfg = some (Location.Rgn rid) ∧
          frame.regionId = rid ∧
          cfg.heap.lookup rid = some region ∧
          cfg' = { cfg with heap := cfg.heap.insert rid { region with bridgeObjectId := oid } }) ∨
       (∃ oid,
          resolveFA y cfg = some (Reference.OId oid) ∧
          xf ≠ frame.bridgeVar ∧
          resolveV xf cfg = none ∧
          cfg' = { cfg with
            stack := cfg.stack.dropLast ++
              [ { frame with varMap := frame.varMap.insert xf (Reference.OId oid) } ] })) := by
  unfold varAsgn at h
  cases hframe : cfg.stack.getLast? with
  | none => rw [hframe] at h; contradiction
  | some frame =>
    rw [hframe] at h
    dsimp at h
    refine ⟨frame, rfl, ?_⟩
    cases hyf : resolveFA y cfg with
    | none => rw [hyf] at h; contradiction
    | some yfRef =>
      rw [hyf] at h
      dsimp at h
      cases yfRef with
      | RId rid0 => dsimp at h; contradiction
      | OId oid =>
        dsimp at h
        by_cases hxb : (xf == frame.bridgeVar) = true
        · rw [if_pos hxb] at h
          rw [beq_iff_eq] at hxb
          cases hloc : (Reference.OId oid).loc? cfg with
          | none => rw [hloc] at h; dsimp at h; contradiction
          | some loc =>
            rw [hloc] at h
            dsimp at h
            cases loc with
            | Stk fid0 => dsimp at h; contradiction
            | Rgn rid =>
              dsimp at h
              by_cases hrid : (frame.regionId == rid) = true
              · rw [if_pos hrid] at h
                rw [beq_iff_eq] at hrid
                cases hregion : cfg.heap.lookup rid with
                | none => rw [hregion] at h; contradiction
                | some region =>
                  rw [hregion] at h
                  dsimp at h
                  rw [Option.some_inj] at h
                  left
                  exact ⟨oid, rid, region, rfl, hxb, hloc, hrid, hregion, h.symm⟩
              · rw [if_neg hrid] at h; contradiction
        · rw [if_neg hxb] at h
          rw [beq_iff_eq] at hxb
          by_cases hrv : (resolveV xf cfg == none) = true
          · rw [if_pos hrv] at h
            rw [beq_iff_eq] at hrv
            rw [Option.some_inj] at h
            right
            exact ⟨oid, rfl, hxb, hrv, h.symm⟩
          · rw [if_neg hrv] at h; contradiction
