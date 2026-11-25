module

public import Gc.Model.Helpers
public import Gc.Model.Types

public import Mathlib.Data.List.Infix

@[expose] public section

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
  rcases hframe : cfg.stack.getLast? with _ | frame
  · simp_all
  · refine ⟨frame, rfl, ?_⟩
    rcases hyf : resolveFA y cfg with _ | ⟨_ | oid⟩ <;> simp_all
    by_cases hxb : xf = frame.bridgeVar
    · rcases hloc : (Reference.OId oid).loc? cfg with _ | _ | rid <;> simp_all
      obtain ⟨rfl, h⟩ := h
      rcases hl : cfg.heap.lookup frame.regionId with _ | region <;> simp_all
    · simp_all
