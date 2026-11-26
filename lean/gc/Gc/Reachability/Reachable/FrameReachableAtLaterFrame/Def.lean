module

public import Gc.Model.Validity
public import Gc.Model.Mutation.Stmt
public import Gc.Reachability.Reachable.Semantics

@[expose] public section

def FrameReachable_at_later_frame_implies_FrameReachable_at_frame (cfg : RuntimeConfig) : Prop :=
  ∀ frame ∈ cfg.stackWithIndex, ∀ frame' ∈ cfg.stackWithIndex,
    frame.index < frame'.index →
    ∀ oid, (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) →
    FrameReachable cfg frame'.index (Reference.OId oid) →
    FrameReachable cfg frame.index (Reference.OId oid)

def FrameReachableAtLaterFrame_step (cmd : Stmt) : Prop :=
  ∀ cfg cfg' : RuntimeConfig, ValidConfig cfg → step cmd cfg = some cfg' →
    FrameReachable_at_later_frame_implies_FrameReachable_at_frame cfg →
    FrameReachable_at_later_frame_implies_FrameReachable_at_frame cfg'
