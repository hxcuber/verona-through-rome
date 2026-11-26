module

public import Gc.Model.Helpers

public import Mathlib.Data.List.Infix

@[expose] public section

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
  rcases hframe : cfg.stackWithIndex.getLast? with _ | frame
  · simp_all
  rw [hframe] at h
  dsimp at h
  refine ⟨frame, rfl, ?_⟩
  rcases hyr : resolveV yf.root cfg with _ | yRef
  · simp_all
  rw [hyr] at h
  dsimp at h
  refine ⟨yRef, rfl, ?_⟩
  rcases hyrl : yRef.loc? cfg with _ | yRefLoc
  · simp_all
  rw [hyrl] at h
  dsimp at h
  refine ⟨yRefLoc, rfl, ?_⟩
  rcases hyf : resolveFA yf cfg with _ | yfRef
  · simp_all
  rw [hyf] at h
  dsimp at h
  refine ⟨yfRef, rfl, ?_⟩
  rcases hyfl : yfRef.loc? cfg with _ | yfRefLoc
  · simp_all
  rw [hyfl] at h
  dsimp at h
  refine ⟨yfRefLoc, rfl, ?_⟩
  clear hframe hyr hyrl hyf hyfl
  by_cases hxb : x = frame.bridgeVar
  · rcases yRef with _ | yoid <;> rcases yRefLoc with yrid | _ <;> rcases yfRef with _ | yfoid <;>
      rcases yfRefLoc with yfrid | _ <;> simp [hxb] at h
    obtain ⟨⟨rfl, rfl⟩, h⟩ := h
    rcases hl : cfg.heap.lookup frame.regionId with _ | region
    · simp [hl] at h
    rcases ho : region.objMap.lookup yoid with _ | obj
    · simp [hl, ho] at h
    simp only [hl, ho, Option.bind_some, Option.some.injEq] at h
    exact Or.inr (Or.inr (Or.inr ⟨yoid, _, yfoid, _, region, obj, hxb, rfl, rfl, rfl, rfl, rfl, rfl, hl, ho,
      h.symm⟩))
  · simp [hxb] at h
    rcases hx : frame.varMap.lookup x with _ | xRef
    · simp [hx] at h
    simp only [hx, Option.bind_some] at h
    rcases yRef with _ | yoid
    · simp at h
    rcases yRefLoc with rid | fid
    · simp at h
      obtain ⟨rfl, h⟩ := h
      rcases hl : cfg.heap.lookup frame.regionId with _ | region
      · simp [hl] at h
      rcases ho : region.objMap.lookup yoid with _ | obj
      · simp [hl, ho] at h
      simp only [hl, ho, Option.bind_some] at h
      rcases xRef with xrid | xoid
      · cases hs : region.status <;> simp_all
        exact absurd h.1 (by decide)
      · dsimp only at h
        rcases hxl : (Reference.OId xoid).loc? cfg with _ | ⟨xrid | fid⟩
        · simp [hxl] at h
        · simp only [hxl, Option.bind_some] at h
          cases hs : region.status <;> simp [hs] at h
          · obtain ⟨⟨rfl, -⟩, rfl⟩ := h
            exact Or.inr (Or.inl ⟨yoid, _, region, obj, xoid, _, hxb, rfl, rfl, rfl, hl, ho, rfl, hxl, rfl, hs,
              by rw [hs]⟩)
          · exact absurd h.1.2 (by decide)
        · simp [hxl] at h
    · simp at h
      obtain ⟨rfl, h⟩ := h
      rcases ho : frame.objMap.lookup yoid with _ | obj
      · simp [ho] at h
      simp only [ho, Option.bind_some, Option.some.injEq] at h
      exact Or.inl ⟨yoid, xRef, obj, hxb, rfl, rfl, rfl, ho, h.symm⟩
