import Gc.Model.Start
import Gc.Reachability.Referencable.Validity.Reachable

theorem RuntimeConfig.start_cr3 : CR3 RuntimeConfig.start := by
  unfold CR3
  intro frame hframe frame' hframe' hlt oid hloc hreach
  unfold RuntimeConfig.start RuntimeConfig.stackWithIndex at hframe hframe'
  dsimp at hframe hframe'
  obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hframe
  obtain ⟨n', hn', hfeq'⟩ := List.mem_mapIdx.mp hframe'
  have hidx : frame.index = n := by rw [← hfeq]
  have hidx' : frame'.index = n' := by rw [← hfeq']
  simp at hn hn'
  rw [hidx, hidx', hn, hn'] at hlt
  exact absurd hlt (lt_irrefl 0)

theorem RuntimeConfig.start_reachable_valid : ValidReachableConfig RuntimeConfig.start :=
  { RuntimeConfig.start_valid with
    cr3 := RuntimeConfig.start_cr3 }
