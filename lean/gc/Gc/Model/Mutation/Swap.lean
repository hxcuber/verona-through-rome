import Gc.Model.Helpers
import Gc.Model.Types

import Mathlib.Data.List.Infix

def swap (x : VarName) (yf : FieldAccess) (cfg : RuntimeConfig) : Option (RuntimeConfig) := do
  let frame ← cfg.stackWithIndex.getLast?
  let yRef ← resolveV yf.root cfg
  let yRefLoc ← yRef.loc? cfg
  let yfRef ← resolveFA yf cfg
  let yfRefLoc ← yfRef.loc? cfg
  if x != frame.bridgeVar then
    let xRef ← frame.varMap.lookup x
    match yRef with
    | Reference.OId yoid =>
      match yRefLoc with
      | Location.Stk fid =>
        if fid == frame.index then
          let obj ← frame.objMap.lookup yoid
          -- SWAP-STACK
          pure { cfg with
            stack := cfg.stack.dropLast ++ [{ frame with
              varMap := frame.varMap.insert x yfRef,
              objMap := frame.objMap.insert yoid (obj.insert yf.field xRef)
            }],
          }
        else
          none
      | Location.Rgn rid =>
        if rid == frame.regionId then
          let region ← cfg.heap.lookup rid
          let obj ← region.objMap.lookup yoid
          match xRef with
          | Reference.OId _ =>
            let xRefLoc ← xRef.loc? cfg
            match xRefLoc with
            | Location.Stk _ => none
            | Location.Rgn xrid =>
              if xrid == frame.regionId ∧ region.status == Status.Open then
                -- SWAP-REGION-OBJECT
                pure { cfg with
                  stack := cfg.stack.dropLast ++ [{ frame with varMap := frame.varMap.insert x yfRef }],
                  heap := cfg.heap.insert rid { region with
                    objMap := region.objMap.insert yoid (obj.insert yf.field xRef)
                  }
                }
              else
                none
          | Reference.RId _ =>
            -- SWAP-REGION-REGION
            if region.status == Status.Open then
              pure { cfg with
                stack := cfg.stack.dropLast ++ [{ frame with varMap := frame.varMap.insert x yfRef }],
                heap := cfg.heap.insert rid { region with
                  objMap := region.objMap.insert yoid (obj.insert yf.field xRef)
                }
              }
            else
              none
        else
          none
    | Reference.RId _ => none
  else
    match yRef, yRefLoc, yfRef, yfRefLoc with
    | Reference.OId yoid, Location.Rgn yrid, Reference.OId yfoid, Location.Rgn yfrid =>
      if yrid == frame.regionId ∧ yfrid == frame.regionId then
        let region ← cfg.heap.lookup yrid
        let obj ← region.objMap.lookup yoid
        let obj' := obj.insert yf.field (Reference.OId region.bridgeObjectId)
        -- SWAP-REGION-BRIDGE
        some { cfg with
          heap := cfg.heap.insert yrid { region with
            bridgeObjectId := yfoid,
            objMap := region.objMap.insert yoid obj'
          }
        }
      else
        none
    | _, _, _, _ => none

theorem swap_cases (h : swap x yf cfg = some cfg') :
    ∃ frame : FrameWithIndex, cfg.stackWithIndex.getLast? = some frame ∧
    ∃ yRef, resolveV yf.root cfg = some yRef ∧
    ∃ yRefLoc, yRef.loc? cfg = some yRefLoc ∧
    ∃ yfRef, resolveFA yf cfg = some yfRef ∧
    ∃ yfRefLoc, yfRef.loc? cfg = some yfRefLoc ∧
    ((-- SWAP-STACK
      ∃ yoid xRef obj,
        x ≠ frame.bridgeVar ∧
        yRef = Reference.OId yoid ∧
        yRefLoc = Location.Stk frame.index ∧
        frame.varMap.lookup x = some xRef ∧
        frame.objMap.lookup yoid = some obj ∧
        cfg' = { cfg with stack := cfg.stack.dropLast ++ [ { frame with
          varMap := frame.varMap.insert x yfRef,
          objMap := frame.objMap.insert yoid (obj.insert yf.field xRef)
        } ] }) ∨
     (-- SWAP-REGION-OBJECT
      ∃ yoid rid region obj xoid xrid,
        x ≠ frame.bridgeVar ∧
        yRef = Reference.OId yoid ∧
        yRefLoc = Location.Rgn rid ∧
        rid = frame.regionId ∧
        cfg.heap.lookup rid = some region ∧
        region.objMap.lookup yoid = some obj ∧
        frame.varMap.lookup x = some (Reference.OId xoid) ∧
        (Reference.OId xoid).loc? cfg = some (Location.Rgn xrid) ∧
        xrid = frame.regionId ∧
        region.status = Status.Open ∧
        cfg' = { cfg with
          stack := cfg.stack.dropLast ++ [ { frame with varMap := frame.varMap.insert x yfRef } ],
          heap := cfg.heap.insert rid { region with
            objMap := region.objMap.insert yoid (obj.insert yf.field (Reference.OId xoid)) }
        }) ∨
     (-- SWAP-REGION-REGION
      ∃ yoid rid region obj xrid,
        x ≠ frame.bridgeVar ∧
        yRef = Reference.OId yoid ∧
        yRefLoc = Location.Rgn rid ∧
        rid = frame.regionId ∧
        cfg.heap.lookup rid = some region ∧
        region.objMap.lookup yoid = some obj ∧
        frame.varMap.lookup x = some (Reference.RId xrid) ∧
        region.status = Status.Open ∧
        cfg' = { cfg with
          stack := cfg.stack.dropLast ++ [ { frame with varMap := frame.varMap.insert x yfRef } ],
          heap := cfg.heap.insert rid { region with
            objMap := region.objMap.insert yoid (obj.insert yf.field (Reference.RId xrid)) }
        }) ∨
     (-- SWAP-REGION-BRIDGE
      ∃ yoid yrid yfoid yfrid region obj,
        x = frame.bridgeVar ∧
        yRef = Reference.OId yoid ∧
        yRefLoc = Location.Rgn yrid ∧
        yfRef = Reference.OId yfoid ∧
        yfRefLoc = Location.Rgn yfrid ∧
        yrid = frame.regionId ∧
        yfrid = frame.regionId ∧
        cfg.heap.lookup yrid = some region ∧
        region.objMap.lookup yoid = some obj ∧
        cfg' = { cfg with
          heap := cfg.heap.insert yrid { region with
            bridgeObjectId := yfoid,
            objMap := region.objMap.insert yoid (obj.insert yf.field (Reference.OId region.bridgeObjectId)) }
        })) := by
  unfold swap at h
  cases hframe : cfg.stackWithIndex.getLast? with
  | none => rw [hframe] at h; contradiction
  | some frame =>
    rw [hframe] at h
    dsimp at h
    refine ⟨frame, rfl, ?_⟩
    cases hyr : resolveV yf.root cfg with
    | none => rw [hyr] at h; contradiction
    | some yRef =>
      rw [hyr] at h
      dsimp at h
      refine ⟨yRef, rfl, ?_⟩
      cases hyrl : yRef.loc? cfg with
      | none => rw [hyrl] at h; contradiction
      | some yRefLoc =>
        rw [hyrl] at h
        dsimp at h
        refine ⟨yRefLoc, rfl, ?_⟩
        cases hyf : resolveFA yf cfg with
        | none => rw [hyf] at h; contradiction
        | some yfRef =>
          rw [hyf] at h
          dsimp at h
          refine ⟨yfRef, rfl, ?_⟩
          cases hyfl : yfRef.loc? cfg with
          | none => rw [hyfl] at h; contradiction
          | some yfRefLoc =>
            rw [hyfl] at h
            dsimp at h
            refine ⟨yfRefLoc, rfl, ?_⟩
            by_cases hxb : (x != frame.bridgeVar) = true
            · rw [if_pos hxb] at h
              rw [bne_iff_ne] at hxb
              cases hxr : frame.varMap.lookup x with
              | none => rw [hxr] at h; contradiction
              | some xRef =>
                rw [hxr] at h
                dsimp at h
                cases yRef with
                | RId yrid0 => dsimp at h; contradiction
                | OId yoid =>
                  dsimp at h
                  cases yRefLoc with
                  | Stk fid =>
                    dsimp at h
                    by_cases hfid : (fid == frame.index) = true
                    · rw [if_pos hfid] at h
                      rw [beq_iff_eq] at hfid
                      cases hobj : frame.objMap.lookup yoid with
                      | none => rw [hobj] at h; contradiction
                      | some obj =>
                        rw [hobj] at h
                        dsimp at h
                        rw [Option.some_inj] at h
                        left
                        subst hfid
                        exact ⟨yoid, xRef, obj, hxb, rfl, rfl, rfl, hobj, h.symm⟩
                    · rw [if_neg hfid] at h; contradiction
                  | Rgn rid =>
                    dsimp at h
                    by_cases hrid : (rid == frame.regionId) = true
                    · rw [if_pos hrid] at h
                      rw [beq_iff_eq] at hrid
                      cases hregion : cfg.heap.lookup rid with
                      | none => rw [hregion] at h; contradiction
                      | some region =>
                        rw [hregion] at h
                        dsimp at h
                        cases hobj : region.objMap.lookup yoid with
                        | none => rw [hobj] at h; contradiction
                        | some obj =>
                          rw [hobj] at h
                          dsimp at h
                          cases xRef with
                          | OId xoid =>
                            dsimp at h
                            cases hxrl : (Reference.OId xoid).loc? cfg with
                            | none => rw [hxrl] at h; dsimp at h; contradiction
                            | some xRefLoc =>
                              rw [hxrl] at h
                              dsimp at h
                              cases xRefLoc with
                              | Stk fid' => dsimp at h; contradiction
                              | Rgn xrid =>
                                dsimp at h
                                by_cases hcond : xrid == frame.regionId ∧ region.status == Status.Open
                                · rw [if_pos hcond] at h
                                  obtain ⟨hxridEq0, hstatusEq0'⟩ := hcond
                                  rw [beq_iff_eq] at hxridEq0
                                  have hstatusEq0 : region.status = Status.Open := by
                                    cases hs : region.status with
                                    | Open => rfl
                                    | Closed => rw [hs] at hstatusEq0'; contradiction
                                  rw [Option.some_inj] at h
                                  right; left
                                  exact ⟨yoid, rid, region, obj, xoid, xrid, hxb, rfl, rfl, hrid, hregion, hobj,
                                    rfl, hxrl, hxridEq0, hstatusEq0, h.symm⟩
                                · rw [if_neg hcond] at h; contradiction
                          | RId xrid0 =>
                            dsimp at h
                            by_cases hstatus : region.status == Status.Open
                            · rw [if_pos hstatus] at h
                              have hstatusEq : region.status = Status.Open := by
                                cases hs : region.status with
                                | Open => rfl
                                | Closed => rw [hs] at hstatus; contradiction
                              rw [Option.some_inj] at h
                              right; right; left
                              exact ⟨yoid, rid, region, obj, xrid0, hxb, rfl, rfl, hrid, hregion, hobj, rfl,
                                hstatusEq, h.symm⟩
                            · rw [if_neg hstatus] at h; contradiction
                    · rw [if_neg hrid] at h; contradiction
            · rw [if_neg hxb] at h
              rw [Bool.not_eq_true] at hxb
              have hxb' : x = frame.bridgeVar := by
                by_contra hne
                have : (x != frame.bridgeVar) = true := by
                  rw [bne_iff_ne]; exact hne
                rw [this] at hxb; contradiction
              cases yRef with
              | RId yrid0 => dsimp at h; contradiction
              | OId yoid =>
                cases yRefLoc with
                | Stk fid => dsimp at h; contradiction
                | Rgn yrid =>
                  cases yfRef with
                  | RId yfrid0 => dsimp at h; contradiction
                  | OId yfoid =>
                    cases yfRefLoc with
                    | Stk fid' => dsimp at h; contradiction
                    | Rgn yfrid =>
                      dsimp at h
                      by_cases hcond2 : yrid == frame.regionId ∧ yfrid == frame.regionId
                      · rw [if_pos hcond2] at h
                        obtain ⟨hyridEq, hyfridEq⟩ := hcond2
                        rw [beq_iff_eq] at hyridEq hyfridEq
                        cases hregion : cfg.heap.lookup yrid with
                        | none => rw [hregion] at h; contradiction
                        | some region =>
                          rw [hregion] at h
                          dsimp at h
                          cases hobj : region.objMap.lookup yoid with
                          | none => rw [hobj] at h; contradiction
                          | some obj =>
                            rw [hobj] at h
                            dsimp at h
                            rw [Option.some_inj] at h
                            right; right; right
                            exact ⟨yoid, yrid, yfoid, yfrid, region, obj, hxb', rfl, rfl, rfl, rfl,
                              hyridEq, hyfridEq, hregion, hobj, h.symm⟩
                      · rw [if_neg hcond2] at h; contradiction
