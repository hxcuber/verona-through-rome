import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Reachability.Semantics

-- Generalized over `rid` (rather than fixing `rid := frame.regionId` up front), for the same
-- reason as RegionReferencable_stays_in_region_aux: `frame.regionId` is a projection, not a bare
-- variable, so `induction h` needs a bare-variable index to generalize over.
private theorem RegionReferencable_implies_FrameReferencable_aux (cfg : RuntimeConfig) (rid : RegionId)
    (ref : Reference) (h : RegionReferencable cfg rid ref) :
    ∀ frame, frame ∈ cfg.stackWithIndex → frame.regionId = rid → FrameReferencable cfg frame.index ref := by
  induction h with
  | bridge hlookup hbridge =>
    intro frame hframe hrid
    subst hrid
    exact FrameReferencable.bridge hframe hlookup hbridge
  | step hobj hcontains hrr ih =>
    intro frame hframe hrid
    exact FrameReferencable.step hobj hcontains (ih frame hframe hrid)

-- report.pdf CR1: "Region-reachability implies frame-reachability. If an object o is
-- region-reachable in a region R, then there is a path from the bridge object to o. If R has
-- an associated frame F, then R's region object is represented by the bridge variable in frame
-- F. Then, there is a path from the bridge variable to o, so o is frame-reachable." `R` is
-- `frame.regionId` throughout (see RegionReferencable_implies_FrameReferencable_aux's comment for why).
theorem CR1 :
  frame ∈ cfg.stackWithIndex ->
  RegionReferencable cfg frame.regionId ref ->
  FrameReferencable cfg frame.index ref := by
  -- each case of RegionReferencable matches to a case of FrameReferencable directly:
  -- bridge -> bridge, step -> step (the objAt?/contains premises carry over unchanged)
  intro hframe h
  exact RegionReferencable_implies_FrameReferencable_aux cfg frame.regionId ref h frame hframe rfl
