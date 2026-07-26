import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Reachability.Semantics

theorem RegionReachable_stays_in_region : ValidConfig cfg ->
  RegionReachable cfg rid (Reference.OId oid) ->
  (Reference.OId oid).loc? cfg = some (Location.Rgn rid) := by
  -- per case anaylsis on the RegionReachable inductive definition
  -- bridge case is trivial, as the bridge object is in the region
  -- step case -> the IH gives (OId oid).loc? cfg = some (Rgn rid); objAt? succeeding at
  -- oid means oid.loc? cfg is some loc (either Rgn or Stk), so H3 pins loc = Rgn rid
  -- (a frame-resident object would contradict H3, since the IH already places oid in rid)
  sorry

theorem RegionReachable_implies_FrameReachable : ValidConfig cfg ->
  frame ∈ cfg.stackWithIndex ->
  cfg.heap.lookup frame.regionId = some region ->
  RegionReachable cfg frame.regionId ref ->
  FrameReachable cfg frame.index ref := by
  -- each case of RegionReachable matches to a case of FrameReachable directly:
  -- bridge -> bridge, step -> step (the objAt?/contains premises carry over unchanged)
  sorry
