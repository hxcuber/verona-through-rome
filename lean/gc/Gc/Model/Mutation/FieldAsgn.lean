module

public import Gc.Model.Helpers

public import Mathlib.Data.List.Infix

@[expose] public section

def fieldAsgn (xf : FieldAccess) (y : VarName) (cfg : RuntimeConfig) : Option (RuntimeConfig) := do
  let frame ← cfg.stackWithIndex.getLast?
  let xRef ← resolveV xf.root cfg
  let yRef ← resolveV y cfg
  match xRef, yRef with
  | Reference.OId oid, Reference.OId _ =>
    let xRefLoc ← xRef.loc? cfg
    match xRefLoc with
    | Location.Stk fid =>
      if fid == frame.index then
        let obj ← frame.objMap.lookup oid
        -- FIELD-ASGN-STACK
        some { cfg with
          stack := cfg.stack.dropLast ++ [ { frame with
            objMap := frame.objMap.insert oid (obj.insert xf.field yRef)
          } ]
        }
      else
        none
    | Location.Rgn rid =>
      if rid == frame.regionId then
        let region ← cfg.heap.lookup rid
        let obj ← region.objMap.lookup oid
        let yfRefLoc ← yRef.loc? cfg
        match yfRefLoc with
        | Location.Stk _ => none
        | Location.Rgn rid' =>
          if rid == rid' ∧ region.status == Status.Open then
            -- FIELD-ASGN-REGION
            some { cfg with
              heap := cfg.heap.insert rid { region with
                objMap := region.objMap.insert oid (obj.insert xf.field yRef)
              }
            }
          else
            none
      else
        none
  | _, _ => none

theorem fieldAsgn_cases (h : fieldAsgn xf y cfg = some cfg') :
    ∃ frame : FrameWithIndex, cfg.stackWithIndex.getLast? = some frame ∧
      ((∃ oid oid_y obj,
          resolveV xf.root cfg = some (Reference.OId oid) ∧
          resolveV y cfg = some (Reference.OId oid_y) ∧
          (Reference.OId oid).loc? cfg = some (Location.Stk frame.index) ∧
          frame.objMap.lookup oid = some obj ∧
          cfg' = { cfg with stack := cfg.stack.dropLast ++
            [ { frame with objMap := frame.objMap.insert oid (obj.insert xf.field (Reference.OId oid_y)) } ] }) ∨
       (∃ oid oid_y rid region obj,
          resolveV xf.root cfg = some (Reference.OId oid) ∧
          resolveV y cfg = some (Reference.OId oid_y) ∧
          (Reference.OId oid).loc? cfg = some (Location.Rgn rid) ∧
          cfg.heap.lookup rid = some region ∧
          region.objMap.lookup oid = some obj ∧
          (Reference.OId oid_y).loc? cfg = some (Location.Rgn rid) ∧
          region.status = Status.Open ∧
          rid = frame.regionId ∧
          cfg' = { cfg with heap := cfg.heap.insert rid { region with
            objMap := region.objMap.insert oid (obj.insert xf.field (Reference.OId oid_y)) } })) := by
  unfold fieldAsgn at h
  rcases hframe : cfg.stackWithIndex.getLast? with _ | frame
  · simp_all
  · refine ⟨frame, rfl, ?_⟩
    rcases hxr : resolveV xf.root cfg with _ | ⟨_ | oid⟩ <;> simp_all
    rcases hyr : resolveV y cfg with _ | ⟨_ | oid_y⟩ <;> simp_all
    rcases hloc : (Reference.OId oid).loc? cfg with _ | ⟨fid | rid⟩ <;> simp_all
    · obtain ⟨rfl, h⟩ := h
      rcases hl : cfg.heap.lookup frame.regionId with _ | region <;> simp_all
      rcases ho : region.objMap.lookup oid with _ | obj <;> simp_all
      rcases hy : (Reference.OId oid_y).loc? cfg with _ | ⟨rid' | _⟩ <;> simp_all
      cases hs : region.status <;> simp_all
      exact absurd h.1.2 (by decide)
    · obtain ⟨rfl, h⟩ := h
      rcases ho : frame.objMap.lookup oid with _ | obj <;> simp_all
