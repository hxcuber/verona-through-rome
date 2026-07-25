import Gc.Model.Helpers
import Gc.Model.Types
import Mathlib.Data.List.Sigma

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
  | _, _ => none

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

def exit (cfg : RuntimeConfig) : Option (RuntimeConfig) := do
  if cfg.stack.length >= 2 then
    let frame ← cfg.stack.getLast?
    let region ← cfg.heap.lookup frame.regionId
    if region.status == Status.Open then
      some { cfg with
        stack := cfg.stack.dropLast,
        heap := cfg.heap.insert frame.regionId { region with status := Status.Closed }
      }
    else
      none
  else
    none

def makeObjStack (x : VarName) (cfg : RuntimeConfig) : Option (RuntimeConfig) := do
  let frame ← cfg.stack.getLast?
  let newObjId := cfg.freshObjectId
  some { cfg with
    stack := cfg.stack.dropLast ++ [ { frame with
      varMap := frame.varMap.insert x (Reference.OId newObjId),
      objMap := frame.objMap.insert newObjId ∅
    } ]
  }

def makeObjRegion (x : VarName) (cfg : RuntimeConfig) : Option (RuntimeConfig) := do
  let frame ← cfg.stack.getLast?
  let region ← cfg.heap.lookup frame.regionId
  let newObjId := cfg.freshObjectId
  if region.status == Status.Open then
    some { cfg with
      stack := cfg.stack.dropLast ++ [ { frame with
        varMap := frame.varMap.insert x (Reference.OId newObjId)
      } ],
      heap := cfg.heap.insert frame.regionId { region with
        objMap := region.objMap.insert newObjId ∅
      }
    }
  else
    none

def makeRegion (x : VarName) (cfg : RuntimeConfig) : Option (RuntimeConfig) := do
  let frame ← cfg.stack.getLast?
  let newRegionId := cfg.freshRegionId
  let newObjectId := cfg.freshObjectId
  some { cfg with
    stack := cfg.stack.dropLast ++ [ { frame with
      varMap := frame.varMap.insert x (Reference.RId newRegionId)
    } ],
    heap := cfg.heap.insert newRegionId {
      status := Status.Closed,
      objMap := (∅ : ObjMap).insert newObjectId ∅,
      bridgeObjectId := newObjectId
    }
  }

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
