import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity

import Mathlib.Data.List.AList

def RuntimeConfig.start : RuntimeConfig :=
  { heap := (∅ : Heap).insert 0 {
      bridgeObjectId := 0,
      objMap := (∅ : ObjMap).insert 0 ∅,
      status := Status.Open
    },
    stack := [{ regionId := 0, bridgeVar := "main", varMap := ∅, objMap := ∅ }],
  }

theorem RuntimeConfig.start_H1 : H1 RuntimeConfig.start := by
  unfold H1
  intro region h
  unfold RuntimeConfig.start Heap.regions at h
  dsimp at h
  unfold Region.bridgeObjectId Region.objMap
  cases h with
  | head =>
    rw [AList.mem_keys]
    dsimp
    rw [List.mem_singleton]
  | tail =>
    contradiction

theorem RuntimeConfig.start_L1 : L1 RuntimeConfig.start := by
  unfold L1
    RuntimeConfig.start
    RuntimeConfig.objectIds
    Heap.objectIds
    Region.objectIds
    Stack.objectIds
    Frame.objectIds
  dsimp
  exact List.nodup_singleton 0

theorem RuntimeConfig.start_H3 : H2 RuntimeConfig.start := by
  unfold H2
  intro rid
  unfold RuntimeConfig.start Stack.refs Frame.refs Heap.refs Region.refs Object.refs
  dsimp
  simp

theorem RuntimeConfig.start_H4 : H3 RuntimeConfig.start := by
  unfold H3
  intro rid oid region hlookup hin
  unfold RuntimeConfig.start at hlookup
  dsimp at hlookup
  rw [← AList.insert_empty] at hlookup
  by_cases h : rid = 0
  · subst h
    rw [AList.lookup_insert] at hlookup
    injection hlookup with hregion
    subst hregion
    unfold Region.refs Region.objMap Object.refs at hin
    dsimp at hin
    contradiction
  · rw [AList.lookup_insert_ne h] at hlookup
    contradiction

theorem RuntimeConfig.start_L2 : L2 RuntimeConfig.start := by
  unfold L2
  intro frame h
  unfold RuntimeConfig.start RuntimeConfig.stack at h
  dsimp at h
  rw [List.mem_singleton] at h
  subst h
  unfold Frame.regionId RuntimeConfig.start RuntimeConfig.heap Region.status
  dsimp
  rw [← AList.insert_empty]
  rw [AList.lookup_insert]
  simp

theorem RuntimeConfig.start_valid_S2 : S1 RuntimeConfig.start := by
  unfold S1
  unfold RuntimeConfig.start
  dsimp
  exact List.nodup_singleton 0

theorem RuntimeConfig.start_valid_S3 : S2 RuntimeConfig.start := by
  unfold S2
  intro frame hframe ref href fid' oid href_eq hloc
  unfold RuntimeConfig.start RuntimeConfig.stackWithIndex at hframe
  dsimp at hframe
  cases hframe with
  | head =>
    dsimp at href
    unfold Frame.refs at href
    dsimp at href
    contradiction
  | tail =>
    contradiction

theorem RuntimeConfig.start_valid_S4 : S3 RuntimeConfig.start := by
  unfold S3
  intro frame hframe ref href rid' oid href_eq hloc
  unfold RuntimeConfig.start RuntimeConfig.stackWithIndex at hframe
  dsimp at hframe
  cases hframe with
  | head =>
    dsimp at href
    unfold Frame.refs at href
    dsimp at href
    contradiction
  | tail =>
    contradiction

theorem RuntimeConfig.start_HS1 : HS1 RuntimeConfig.start := by
  unfold HS1
  intro oid hmem
  unfold RuntimeConfig.start RuntimeConfig.refs Stack.refs Frame.refs Heap.refs Region.refs Object.refs at hmem
  dsimp at hmem
  simp at hmem

theorem RuntimeConfig.start_valid : ValidConfig RuntimeConfig.start :=
  { l1 := RuntimeConfig.start_L1,
    l2 := RuntimeConfig.start_L2,
    h1 := RuntimeConfig.start_H1,
    h2 := RuntimeConfig.start_H3,
    h3 := RuntimeConfig.start_H4,
    s1 := RuntimeConfig.start_valid_S2,
    s2 := RuntimeConfig.start_valid_S3,
    s3 := RuntimeConfig.start_valid_S4,
    hs1 := RuntimeConfig.start_HS1,
  }
