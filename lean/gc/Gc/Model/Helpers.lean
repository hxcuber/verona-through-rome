module

public import Gc.Model.Types
public import Gc.Model.Theorems
public import Mathlib.Data.List.AList

@[expose] public section

def Heap.regions (heap : Heap) : List Region := heap.entries.map (·.2)

def Object.refs (obj : Object) : List Reference := obj.entries.map (·.2)
def Region.refs (region : Region) : List Reference :=
  region.objMap.entries.map (·.2) >>= Object.refs
def Heap.refs (heap : Heap) : List Reference :=
  heap.entries.map (·.2) >>= Region.refs
def Frame.refs (frame : Frame) : List Reference :=
  (frame.objMap.entries.map (·.2) >>= Object.refs) ++
  frame.varMap.entries.map (·.2)
def Stack.refs (stack : Stack) : List Reference :=
  stack.map Frame.refs >>= id
def RuntimeConfig.refs (cfg : RuntimeConfig) : List Reference :=
  cfg.stack.refs ++ cfg.heap.refs

def Region.objectIds (region : Region) : List ObjectId := region.2.1.keys
def Heap.objectIds (heap : Heap) : List ObjectId :=
  (heap.entries.map (λ e => e.2.objectIds)).flatten
def Frame.objectIds (frame : Frame) : List ObjectId :=
  frame.objMap.keys
def Stack.objectIds (stack : Stack) : List ObjectId :=
  stack.map Frame.objectIds >>= id
def RuntimeConfig.objectIds (cfg : RuntimeConfig) : List ObjectId :=
  cfg.stack.objectIds ++ cfg.heap.objectIds

def RuntimeConfig.regionIds (cfg : RuntimeConfig) : List RegionId := cfg.heap.keys

def RuntimeConfig.freshRegionId (cfg : RuntimeConfig) : RegionId :=
  match cfg.heap.keys with
  | [] => 0
  | keys => keys.foldl max 0 + 1

def RuntimeConfig.freshObjectId (cfg : RuntimeConfig) : ObjectId :=
  match cfg.objectIds with
  | [] => 0
  | ids => ids.foldl max 0 + 1

private theorem foldl_max_succ_not_mem (l : List Nat) : l.foldl max 0 + 1 ∉ l :=
  fun h => by have := List.mem_le_foldl_max 0 _ h; omega

theorem RuntimeConfig.freshObjectId_not_mem (cfg : RuntimeConfig) : cfg.freshObjectId ∉ cfg.objectIds := by
  unfold RuntimeConfig.freshObjectId
  split <;> simp_all [foldl_max_succ_not_mem]

theorem RuntimeConfig.freshRegionId_not_mem (cfg : RuntimeConfig) : cfg.freshRegionId ∉ cfg.heap.keys := by
  unfold RuntimeConfig.freshRegionId
  split <;> simp_all [foldl_max_succ_not_mem]

def Reference.loc? (ref : Reference) (cfg : RuntimeConfig) : Option Location :=
  match ref with
  | Reference.RId rid =>
    if cfg.heap.keys.contains rid then some (Location.Rgn rid) else none
  | Reference.OId oid =>
    let h1 := cfg.stackWithIndex.findRev? (λ frame => frame.objMap.keys.contains oid)
    let h2 := cfg.heap.entries.find? (λ ⟨_, region⟩ => region.objMap.keys.contains oid)
    match h1, h2 with
    | some frame, none => some (Location.Stk frame.index)
    | none, some ⟨rid, _⟩ => some (Location.Rgn rid)
    | _, _ => none

def Reference.objAt? (cfg : RuntimeConfig) : Reference → Option Object
  | Reference.RId _ => none
  | Reference.OId oid =>
    match (Reference.OId oid).loc? cfg with
    | some (Location.Rgn rid) =>
      (cfg.heap.lookup rid).bind (fun region => region.objMap.lookup oid)
    | some (Location.Stk fid) =>
      (cfg.stackWithIndex.find? (fun frame => frame.index == fid)).bind
        (fun frame => frame.objMap.lookup oid)
    | none => none

def resolveV (var : VarName) (cfg : RuntimeConfig) : Option Reference := do
  let frame ← cfg.stackWithIndex.findRev? (λ frame => frame.varMap.keys.contains var ∨ frame.bridgeVar == var)
  let ref ← frame.varMap.lookup var <|>
    (if frame.bridgeVar == var then do
      let region ← cfg.heap.lookup frame.regionId
      Reference.OId <$> region.bridgeObjectId
    else
      none)
  some ref

def resolveFA (fieldAccess : FieldAccess) (cfg : RuntimeConfig) : Option Reference := do
  let ref ← resolveV fieldAccess.root cfg
  match ref with
  | Reference.RId _ => none
  | Reference.OId oid =>
    let loc ← ref.loc? cfg
    match loc with
    | Location.Stk fid =>
      let frame ← cfg.stackWithIndex.find? (λ frame => frame.index == fid)
      let obj ← frame.objMap.lookup oid
      obj.lookup fieldAccess.field
    | Location.Rgn rid =>
      let region ← cfg.heap.lookup rid
      let obj ← region.objMap.lookup oid
      obj.lookup fieldAccess.field
