module

public import Gc.Model.Start
public import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.Def

@[expose] public section

theorem RuntimeConfig.start_frameReachableAtLaterFrame :
    FrameReachable_at_later_frame_implies_FrameReachable_at_frame RuntimeConfig.start := by
  intro frame hframe frame' hframe' hlt
  obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp hframe
  obtain ⟨n', hn', rfl⟩ := List.mem_mapIdx.mp hframe'
  simp [RuntimeConfig.start] at hn hn'
  simp [hn, hn'] at hlt
