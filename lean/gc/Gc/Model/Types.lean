module

public import Mathlib.Data.List.AList

@[expose] public section

abbrev RegionId := Nat
abbrev ObjectId := Nat
abbrev BridgeObjectId := ObjectId
abbrev Index := Nat
abbrev VarName := String
abbrev FieldName := String

inductive Reference where
| RId (rid : RegionId)
| OId (oid : ObjectId) deriving DecidableEq

instance : BEq Reference := instBEqOfDecidableEq
instance : LawfulBEq Reference := instLawfulBEq

abbrev VarMap := AList (λ _ : VarName => Reference)
abbrev Object := VarMap
abbrev ObjMap := AList (λ _ : ObjectId => Object)
inductive Status where | Open | Closed deriving BEq, DecidableEq

structure Region where
  bridgeObjectId : BridgeObjectId
  objMap : ObjMap
  status : Status

structure Frame where
  regionId : RegionId
  bridgeVar : VarName
  objMap : ObjMap
  varMap : VarMap
  deriving BEq, DecidableEq

structure FrameWithIndex extends Frame where
  index : Index

-- frames are pushed by appending: the top of the stack is the end of the list, and a bigger index is a later frame
abbrev Stack := List Frame
abbrev StackWithIndex := List FrameWithIndex
abbrev Heap := AList (λ _ : RegionId => Region)

structure RuntimeConfig where
  stack : Stack
  heap : Heap

def RuntimeConfig.stackWithIndex (cfg : RuntimeConfig) : StackWithIndex :=
  cfg.stack.mapIdx (λ idx frame => {frame with index := idx})

inductive Location where
| Rgn (rid : RegionId)
| Stk (fid : Index) deriving BEq, DecidableEq

structure FieldAccess where
  root : VarName
  field : FieldName

