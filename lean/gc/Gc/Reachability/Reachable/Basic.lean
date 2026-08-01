import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Reachability.Reachable.Semantics
import Gc.Model.Validity
import Gc.Model.Preservation

-- `ReachableStep`'s new content vs. `RefStep`: `RId rid` steps directly to `rid`'s own bridge object when `rid` is Closed.
theorem ReachableStep_rid_iff (cfg : RuntimeConfig) (rid : RegionId) (b : Reference) :
    ReachableStep cfg (Reference.RId rid) b ↔
      ∃ region, cfg.heap.lookup rid = some region ∧
        region.status = Status.Closed ∧ b = Reference.OId region.bridgeObjectId :=
  Iff.rfl

-- `ReachableStep` on an `OId` source reduces to `objAt?`/`.refs.contains`, the same shape `RefStep` uses.
theorem ReachableStep_oid_iff (cfg : RuntimeConfig) (oid : ObjectId) (b : Reference) :
    ReachableStep cfg (Reference.OId oid) b ↔
      ∃ obj, (Reference.OId oid).objAt? cfg = some obj ∧ obj.refs.contains b := by
  simp only [ReachableStep, Reference.objAt?]
  cases (Reference.OId oid).loc? cfg with
  | none => rfl
  | some loc => cases loc <;> rfl

-- `rid` is explicit (not fixed to `frame.regionId`) since `induction h` needs a bare-variable index to generalize over.
theorem RegionReachable_implies_FrameRechable (cfg : RuntimeConfig) (rid : RegionId) (ref : Reference)
    (hframe : frame ∈ cfg.stackWithIndex) (hrid : frame.regionId = rid)
    (h : RegionReachable cfg rid ref) :
    FrameReachable cfg frame.index ref := by
  induction h with
  | bridge hlookup hbridge =>
    subst hrid
    exact FrameReachable.bridge hframe hlookup hbridge
  | step hstep _ ih =>
    subst hrid
    exact FrameReachable.step hstep (ih hframe rfl)

def FrameReachable_at_later_frame_implies_FrameReachable_at_frame (cfg : RuntimeConfig) : Prop :=
  ∀ frame ∈ cfg.stackWithIndex, ∀ frame' ∈ cfg.stackWithIndex,
    frame.index < frame'.index →
    ∀ oid, (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) →
    FrameReachable cfg frame'.index (Reference.OId oid) →
    FrameReachable cfg frame.index (Reference.OId oid)

-- Single-step preservation of the property above; this layer's analogue of `Referencable`'s CR3 preservation.
def FrameReachableAtLaterFrame_step (cmd : Stmt) : Prop :=
  ∀ cfg cfg' : RuntimeConfig, ValidConfig cfg → step cmd cfg = some cfg' →
    FrameReachable_at_later_frame_implies_FrameReachable_at_frame cfg →
    FrameReachable_at_later_frame_implies_FrameReachable_at_frame cfg'

def StackReachable_invariant_for_suspended_region_objects (cmd : Stmt) : Prop :=
  ∀ cfg cfg' : RuntimeConfig, ValidConfig cfg → step cmd cfg = some cfg' →
    -- CR3-style hypothesis, assumed for now -- its preservation isn't proved yet.
    FrameReachable_at_later_frame_implies_FrameReachable_at_frame cfg →
    ∀ frame : FrameWithIndex, frame ∈ cfg.stackWithIndex →
    frame.index < cfg.stackWithIndex.length - 1 →
    ∀ oid : ObjectId, (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) →
    (StackReachable cfg (Reference.OId oid) ↔ StackReachable cfg' (Reference.OId oid))

-- report.pdf CR6: given the Closed region `rid` itself is stack-reachable, stack-reachability of an object inside it is exactly region-reachability within it.
theorem StackReachable_iff_RegionReachable_of_closed (cfg : RuntimeConfig) (vcfg : ValidConfig cfg)
    (rid : RegionId) (region : Region) (hlookup : cfg.heap.lookup rid = some region)
    (hclosed : region.status = Status.Closed)
    (hridreachable : StackReachable cfg (Reference.RId rid))
    (oid : ObjectId) (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn rid)) :
    StackReachable cfg (Reference.OId oid) ↔ RegionReachable cfg rid (Reference.OId oid) := by
  sorry

-- -- Companion to the theorem above, easiest via its contrapositive (`StackReachable` oid → `StackReachable` (RId rid)): an unreachable Closed region's own objects are all unreachable too.
-- theorem not_StackReachable_rid_implies_not_StackReachable_objects_of_closed
--     (cfg : RuntimeConfig) (vcfg : ValidConfig cfg)
--     (rid : RegionId) (region : Region) (hlookup : cfg.heap.lookup rid = some region)
--     (hclosed : region.status = Status.Closed)
--     (hridunreachable : ¬ StackReachable cfg (Reference.RId rid)) :
--     ∀ oid : ObjectId, (Reference.OId oid).loc? cfg = some (Location.Rgn rid) →
--       ¬ StackReachable cfg (Reference.OId oid) := by
--   sorry
