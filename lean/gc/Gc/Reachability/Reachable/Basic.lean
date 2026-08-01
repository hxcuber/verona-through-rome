import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Reachability.Reachable.Semantics
import Gc.Model.Validity
import Gc.Model.Preservation

-- `deref?`'s `OId` branch is `objAt?` restated via `do`-notation; the new content is `RId` stepping into a Closed region's bridge object.
theorem deref?_oid_eq_objAt? (cfg : RuntimeConfig) (oid : ObjectId) :
    (Reference.OId oid).deref? cfg = (Reference.OId oid).objAt? cfg := by
  simp only [Reference.deref?, Reference.objAt?]
  cases (Reference.OId oid).loc? cfg with
  | none => rfl
  | some loc => cases loc <;> rfl

-- `ReachableStep`'s new content vs. `RefStep`: `RId rid` steps to `b` when `rid` is Closed and `b` is a field of its bridge object.
theorem ReachableStep_rid_iff (cfg : RuntimeConfig) (rid : RegionId) (b : Reference) :
    ReachableStep cfg (Reference.RId rid) b ↔
      ∃ region, cfg.heap.lookup rid = some region ∧ region.status = Status.Closed ∧
        ∃ obj, region.objMap.lookup region.bridgeObjectId = some obj ∧ obj.refs.contains b := by
  unfold ReachableStep Reference.deref?
  cases hlookup : cfg.heap.lookup rid with
  | none => simp [hlookup]
  | some region =>
    simp only [hlookup]
    cases hstatus : region.status with
    | Open =>
      have hbeq : (Status.Open == Status.Closed) = false := rfl
      have hfail : (failure : Option Unit).bind
          (fun _ => AList.lookup region.bridgeObjectId region.objMap) = none := rfl
      simp [guard, hstatus, hbeq, hfail]
    | Closed =>
      have hbeq : (Status.Closed == Status.Closed) = true := rfl
      simp [guard, hstatus, hbeq]

-- `ReachableStep` on an `OId` source reduces to `objAt?`/`.refs.contains`, the same shape `RefStep` uses.
theorem ReachableStep_oid_iff (cfg : RuntimeConfig) (oid : ObjectId) (b : Reference) :
    ReachableStep cfg (Reference.OId oid) b ↔
      ∃ obj, (Reference.OId oid).objAt? cfg = some obj ∧ obj.refs.contains b := by
  unfold ReachableStep
  rw [deref?_oid_eq_objAt?]

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
