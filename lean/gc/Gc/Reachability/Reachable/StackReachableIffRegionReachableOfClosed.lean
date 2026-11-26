module

public import Gc.Reachability.Reachable.Lemmas.Common

@[expose] public section

-- report.pdf CR6: given the Closed region `rid` itself is stack-reachable, stack-reachability of an object inside it is exactly region-reachability within it.
theorem StackReachable_iff_RegionReachable_of_closed (cfg : RuntimeConfig) (vcfg : ValidConfig cfg)
    (rid : RegionId) (region : Region) (hlookup : cfg.heap.lookup rid = some region)
    (hclosed : region.status = Status.Closed)
    (hridreachable : StackReachable cfg (Reference.RId rid))
    (oid : ObjectId) (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn rid)) :
    StackReachable cfg (Reference.OId oid) ↔ RegionReachable cfg rid (Reference.OId oid) := by
  constructor
  · rintro ⟨frame, -, hreach⟩
    exact RegionReachable_of_FrameReachable_closed vcfg hlookup hclosed hloc hreach
  · intro hrr
    obtain ⟨frame0, hmem0, hreach0⟩ := hridreachable
    obtain ⟨region', hlookup', hrtg⟩ := (RegionReachable_iff_reflTransGen cfg rid _).mp hrr
    rw [hlookup, Option.some_inj] at hlookup'
    subst hlookup'
    exact ⟨frame0, hmem0, FrameReachable_extend (.step (ref' := .RId rid) ⟨region, hlookup, hclosed, rfl⟩ hreach0) hrtg⟩

-- Companion to the theorem above, via its contrapositive (`StackReachable` oid → `StackReachable` (RId rid)): an unreachable Closed region's own objects are all unreachable too.
theorem not_StackReachable_rid_implies_not_StackReachable_objects_of_closed
    (cfg : RuntimeConfig) (vcfg : ValidConfig cfg)
    (rid : RegionId) (region : Region) (hlookup : cfg.heap.lookup rid = some region)
    (hclosed : region.status = Status.Closed)
    (hridunreachable : ¬ StackReachable cfg (Reference.RId rid)) :
    ∀ oid : ObjectId, (Reference.OId oid).loc? cfg = some (Location.Rgn rid) →
      ¬ StackReachable cfg (Reference.OId oid) := by
  rintro oid hloc ⟨frame, hmem, hreach⟩
  exact hridunreachable ⟨frame, hmem, FrameReachable_rid_of_closed_container vcfg hlookup hclosed hloc hreach⟩
