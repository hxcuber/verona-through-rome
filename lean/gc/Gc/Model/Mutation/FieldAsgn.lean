import Gc.Model.Helpers
import Gc.Model.Types

import Mathlib.Data.List.Infix

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
  cases hframe : cfg.stackWithIndex.getLast? with
  | none => rw [hframe] at h; contradiction
  | some frame =>
    rw [hframe] at h
    dsimp at h
    refine ⟨frame, rfl, ?_⟩
    cases hxr : resolveV xf.root cfg with
    | none => rw [hxr] at h; contradiction
    | some xRef =>
      rw [hxr] at h
      dsimp at h
      cases hyr : resolveV y cfg with
      | none => rw [hyr] at h; contradiction
      | some yRef =>
        rw [hyr] at h
        dsimp at h
        cases xRef with
        | RId rid0 => dsimp at h; contradiction
        | OId oid =>
          cases yRef with
          | RId rid1 => dsimp at h; contradiction
          | OId oid_y =>
            dsimp at h
            cases hloc : (Reference.OId oid).loc? cfg with
            | none => rw [hloc] at h; dsimp at h; contradiction
            | some loc =>
              rw [hloc] at h
              dsimp at h
              cases loc with
              | Stk fid =>
                dsimp at h
                by_cases hfid : (fid == frame.index) = true
                · rw [if_pos hfid] at h
                  rw [beq_iff_eq] at hfid
                  cases hobj : frame.objMap.lookup oid with
                  | none => rw [hobj] at h; contradiction
                  | some obj =>
                    rw [hobj] at h
                    dsimp at h
                    rw [Option.some_inj] at h
                    left
                    subst hfid
                    exact ⟨oid, oid_y, obj, rfl, rfl, hloc, hobj, h.symm⟩
                · rw [if_neg hfid] at h; contradiction
              | Rgn rid =>
                dsimp at h
                by_cases hfrid : (rid == frame.regionId) = true
                · rw [if_pos hfrid] at h
                  rw [beq_iff_eq] at hfrid
                  cases hregion : cfg.heap.lookup rid with
                  | none => rw [hregion] at h; contradiction
                  | some region =>
                    rw [hregion] at h
                    dsimp at h
                    cases hobj : region.objMap.lookup oid with
                    | none => rw [hobj] at h; contradiction
                    | some obj =>
                      rw [hobj] at h
                      dsimp at h
                      cases hyloc : (Reference.OId oid_y).loc? cfg with
                      | none => rw [hyloc] at h; dsimp at h; contradiction
                      | some yloc =>
                        rw [hyloc] at h
                        dsimp at h
                        cases yloc with
                        | Stk fid' => dsimp at h; contradiction
                        | Rgn rid' =>
                          dsimp at h
                          by_cases hcond : rid == rid' ∧ region.status == Status.Open
                          · rw [if_pos hcond] at h
                            obtain ⟨hridEq0, hstatusEq0'⟩ := hcond
                            rw [beq_iff_eq] at hridEq0
                            have hstatusEq0 : region.status = Status.Open := by
                              cases hs : region.status with
                              | Open => rfl
                              | Closed => rw [hs] at hstatusEq0'; contradiction
                            rw [Option.some_inj] at h
                            right
                            subst hridEq0
                            exact ⟨oid, oid_y, rid, region, obj, rfl, rfl, hloc, hregion, hobj, hyloc,
                              hstatusEq0, hfrid, h.symm⟩
                          · rw [if_neg hcond] at h; contradiction
                · rw [if_neg hfrid] at h; contradiction
