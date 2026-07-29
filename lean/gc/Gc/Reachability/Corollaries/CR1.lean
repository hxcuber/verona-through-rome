import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Reachability.Semantics

-- Generalized over `rid` (rather than fixing `rid := frame.regionId` up front), for the same
-- reason as RegionReachable_stays_in_region_aux: `frame.regionId` is a projection, not a bare
-- variable, so `induction h` needs a bare-variable index to generalize over.
private theorem RegionReachable_implies_FrameReachable_aux (cfg : RuntimeConfig) (rid : RegionId)
    (ref : Reference) (h : RegionReachable cfg rid ref) :
    ∀ frame, frame ∈ cfg.stackWithIndex → frame.regionId = rid → FrameReachable cfg frame.index ref := by
  induction h with
  | bridge hlookup hbridge =>
    intro frame hframe hrid
    subst hrid
    exact FrameReachable.bridge hframe hlookup hbridge
  | step hobj hcontains hrr ih =>
    intro frame hframe hrid
    exact FrameReachable.step hobj hcontains (ih frame hframe hrid)

-- report.pdf CR1: "Region-reachability implies frame-reachability. If an object o is
-- region-reachable in a region R, then there is a path from the bridge object to o. If R has
-- an associated frame F, then R's region object is represented by the bridge variable in frame
-- F. Then, there is a path from the bridge variable to o, so o is frame-reachable." `R` is
-- `frame.regionId` throughout (see RegionReachable_implies_FrameReachable_aux's comment for why).
theorem RegionReachable_implies_FrameReachable :
  frame ∈ cfg.stackWithIndex ->
  RegionReachable cfg frame.regionId ref ->
  FrameReachable cfg frame.index ref := by
  -- each case of RegionReachable matches to a case of FrameReachable directly:
  -- bridge -> bridge, step -> step (the objAt?/contains premises carry over unchanged)
  intro hframe h
  exact RegionReachable_implies_FrameReachable_aux cfg frame.regionId ref h frame hframe rfl
