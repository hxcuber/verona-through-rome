module

public import Gc.Model.Validity

@[expose] public section

def RuntimeConfig.start : RuntimeConfig :=
  { heap := (∅ : Heap).insert 0 {
      bridgeObjectId := 0,
      objMap := (∅ : ObjMap).insert 0 ∅,
      status := Status.Open
    },
    stack := [{ regionId := 0, bridgeVar := "main", varMap := ∅, objMap := ∅ }],
  }

theorem RuntimeConfig.start_valid : ValidConfig RuntimeConfig.start where
  l1 := by simp [L1, start, objectIds, Heap.objectIds, Region.objectIds, Stack.objectIds, Frame.objectIds]
  l2 := by simpa [L2, start] using ⟨⟨0, AList.singleton 0 ∅, .Open⟩, AList.mem_lookup_iff.mpr (by simp [AList.singleton_entries]), rfl⟩
  h1 := by simp [H1, start, Heap.regions, AList.mem_keys]
  h2 := by simp [H2, start, Stack.refs, Frame.refs, Heap.refs, Region.refs, Object.refs]
  h3 := by
    intro rid oid region hlookup hin
    have := AList.mem_lookup_iff.mp hlookup
    simp [start, AList.singleton_entries] at this
    obtain ⟨-, rfl⟩ := this
    simp [Region.refs, Object.refs] at hin
  s1 := by simp [S1, start]
  s2 := by simp [S2, start, stackWithIndex, Frame.refs]
  s3 := by simp [S3, start, stackWithIndex, Frame.refs]
  hs1 := by simp [HS1, start, refs, Stack.refs, Frame.refs, Heap.refs, Region.refs, Object.refs]
  hs2 := by simp [HS2, start, refs, Stack.refs, Frame.refs, Heap.refs, Region.refs, Object.refs]
