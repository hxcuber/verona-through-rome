import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Reachability.Reachable.Semantics
import Gc.Model.Validity
import Gc.Model.Preservation

-- `deref?`'s `OId` branch is exactly `Reference.objAt?` restated via `do`-notation; the two
-- differ only on `RId`, where `objAt?` always returns `none` but `deref?` steps into a Closed
-- region's own bridge object. Stated fresh here (rather than importing
-- `Gc.Reachability.Referencable.Semantics.RefStep`, which is defined in terms of `objAt?`) so this
-- layer's machinery doesn't depend on anything under `Gc.Reachability.Referencable`.
theorem deref?_oid_eq_objAt? (cfg : RuntimeConfig) (oid : ObjectId) :
    (Reference.OId oid).deref? cfg = (Reference.OId oid).objAt? cfg := by
  simp only [Reference.deref?, Reference.objAt?]
  cases (Reference.OId oid).loc? cfg with
  | none => rfl
  | some loc => cases loc <;> rfl

-- The genuinely new content in `ReachableStep` relative to what `RefStep` alone would give: an
-- `RId rid` steps to `b` exactly when `rid` names a Closed region and `b` is a field of that
-- region's own bridge object.
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

-- `ReachableStep` on an `OId` source reduces to a plain `objAt?`/`.refs.contains` fact, via
-- `deref?_oid_eq_objAt?` -- the same shape `RefStep` itself is defined with.
theorem ReachableStep_oid_iff (cfg : RuntimeConfig) (oid : ObjectId) (b : Reference) :
    ReachableStep cfg (Reference.OId oid) b ↔
      ∃ obj, (Reference.OId oid).objAt? cfg = some obj ∧ obj.refs.contains b := by
  unfold ReachableStep
  rw [deref?_oid_eq_objAt?]

-- `rid` is an explicit parameter (rather than fixing `rid := frame.regionId` up front): `frame.regionId`
-- is a projection, not a bare variable, so `induction h` needs a bare-variable index to
-- generalize over.
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

def StackReachable_invariant_for_suspended_region_objects (cmd : Stmt) : Prop :=
  ∀ cfg cfg' : RuntimeConfig, ValidConfig cfg → step cmd cfg = some cfg' →
    -- CR3-style hypothesis, assumed here rather than proved: anything frame-reachable
    -- from a later frame into an earlier frame's own region is already frame-reachable
    -- from that earlier frame itself. Needed for the content-mutating ops (varAsgn,
    -- fieldAsgn, swap) to rule out a newly-written edge being the *only* witness for a
    -- suspended-region object's reachability. Its own preservation across `step` is not
    -- proved yet -- see the `Reachable/Scratch.lean`/`Lemmas.lean` TODOs.
    FrameReachable_at_later_frame_implies_FrameReachable_at_frame cfg →
    ∀ frame : FrameWithIndex, frame ∈ cfg.stackWithIndex →
    frame.index < cfg.stackWithIndex.length - 1 →
    ∀ oid : ObjectId, (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) →
    (StackReachable cfg (Reference.OId oid) ↔ StackReachable cfg' (Reference.OId oid))
