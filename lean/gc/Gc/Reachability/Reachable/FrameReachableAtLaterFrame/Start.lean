import Gc.Model.Start
import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.Def

theorem RuntimeConfig.start_frameReachableAtLaterFrame :
    FrameReachable_at_later_frame_implies_FrameReachable_at_frame RuntimeConfig.start := by
  unfold FrameReachable_at_later_frame_implies_FrameReachable_at_frame
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
