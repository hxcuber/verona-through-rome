import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Reachability.Semantics

theorem RegionReachable_stays_in_region : ValidConfig cfg ->
  RegionReachable cfg rid (Reference.OId oid) ->
  (Reference.OId oid).loc? cfg = some (Location.Rgn rid) := by
  -- per case anaylsis on the RegionReachable inductive definition
  -- bridge case is trivial, as the bridge object is in the region
  -- region_step case -> use H3 to know that an object always refers to another
  -- object in the same region
  -- frame_step case -> arrive at a contradiction by H3.
  sorry

theorem RegionReachable_implies_FrameReachable : ValidConfig cfg ->
  frame ∈ cfg.stackWithIndex ->
  cfg.heap.lookup frame.regionId = some region ->
  RegionReachable cfg frame.regionId ref ->
  FrameReachable cfg frame.index ref := by
  -- each case of RegionReachable matches to a case of FrameReachable
  -- essentially obtain the proofs from RegionReachable, and use them in FrameReachable
  sorry
