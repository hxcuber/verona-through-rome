import Gc.Reachability.Reachable.Lemmas.Common

-- report.pdf CR6: given the Closed region `rid` itself is stack-reachable, stack-reachability of an object inside it is exactly region-reachability within it.
theorem StackReachable_iff_RegionReachable_of_closed (cfg : RuntimeConfig) (vcfg : ValidConfig cfg)
    (rid : RegionId) (region : Region) (hlookup : cfg.heap.lookup rid = some region)
    (hclosed : region.status = Status.Closed)
    (hridreachable : StackReachable cfg (Reference.RId rid))
    (oid : ObjectId) (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn rid)) :
    StackReachable cfg (Reference.OId oid) ↔ RegionReachable cfg rid (Reference.OId oid) := by
  constructor
  · rintro ⟨frame, hmem, hreach⟩
    exact RegionReachable_of_FrameReachable_closed vcfg hlookup hclosed hloc hreach
  · intro hrr
    obtain ⟨frame0, hmem0, hreach0⟩ := hridreachable
    have hstepBridge : ReachableStep cfg (Reference.RId rid) (Reference.OId region.bridgeObjectId) :=
      (ReachableStep_rid_iff cfg rid _).mpr ⟨region, hlookup, hclosed, rfl⟩
    have hreachBridge : FrameReachable cfg frame0.index (Reference.OId region.bridgeObjectId) :=
      FrameReachable.step hstepBridge hreach0
    obtain ⟨region', hlookup', hrtg⟩ := (RegionReachable_iff_reflTransGen cfg rid (Reference.OId oid)).mp hrr
    rw [hlookup] at hlookup'
    injection hlookup' with hregionEq
    rw [hregionEq] at hreachBridge
    exact ⟨frame0, hmem0, FrameReachable_extend hreachBridge hrtg⟩

-- -- Companion to the theorem above, easiest via its contrapositive (`StackReachable` oid → `StackReachable` (RId rid)): an unreachable Closed region's own objects are all unreachable too.
-- theorem not_StackReachable_rid_implies_not_StackReachable_objects_of_closed
--     (cfg : RuntimeConfig) (vcfg : ValidConfig cfg)
--     (rid : RegionId) (region : Region) (hlookup : cfg.heap.lookup rid = some region)
--     (hclosed : region.status = Status.Closed)
--     (hridunreachable : ¬ StackReachable cfg (Reference.RId rid)) :
--     ∀ oid : ObjectId, (Reference.OId oid).loc? cfg = some (Location.Rgn rid) →
--       ¬ StackReachable cfg (Reference.OId oid) := by
--   sorry
