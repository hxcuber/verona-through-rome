import Gc.Model.Types
import Gc.Model.Theorems
import Mathlib.Data.List.AList

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

def RuntimeConfig.freshObjectId (cfg : RuntimeConfig) : ObjectId :=
  match cfg.objectIds with
  | [] => 0
  | ids => ids.foldl max 0 + 1

theorem RuntimeConfig.freshObjectId_not_mem (cfg : RuntimeConfig) : cfg.freshObjectId ∉ cfg.objectIds := by
  intro hmem
  unfold RuntimeConfig.freshObjectId at hmem
  cases h : cfg.objectIds with
  | nil => rw [h] at hmem; exact absurd hmem List.not_mem_nil
  | cons a l =>
    rw [h] at hmem
    have hle := List.mem_le_foldl_max 0 (List.foldl max 0 (a :: l) + 1) hmem
    omega

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
