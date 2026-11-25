module

public import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.Def

@[expose] public section

def StackReachable_invariant_for_suspended_region_objects (cmd : Stmt) : Prop :=
  ∀ cfg cfg' : RuntimeConfig, ValidConfig cfg → step cmd cfg = some cfg' →
    FrameReachable_at_later_frame_implies_FrameReachable_at_frame cfg →
    ∀ frame : FrameWithIndex, frame ∈ cfg.stackWithIndex →
    frame.index < cfg.stackWithIndex.length - 1 →
    ∀ oid : ObjectId, (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) →
    (StackReachable cfg (Reference.OId oid) ↔ StackReachable cfg' (Reference.OId oid))
