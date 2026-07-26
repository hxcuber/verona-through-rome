import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Reachability.Semantics

-- Generalized over `ref` (rather than fixing `ref := Reference.OId oid` up front) so that
-- `induction h` below works directly: `h`'s type is stated over a bare-variable index, and
-- the `∀ oid, ref = Reference.OId oid → ...` hypothesis is vacuous in a hypothetical `RId` case.
private theorem RegionReachable_stays_in_region_aux (cfg : RuntimeConfig) (hvalid : ValidConfig cfg)
    (rid : RegionId) (ref : Reference) (h : RegionReachable cfg rid ref) :
    ∀ oid, ref = Reference.OId oid → ref.loc? cfg = some (Location.Rgn rid) := by
  induction h with
  | bridge hlookup hbridge =>
    intro _ _
    subst hbridge
    refine (oid_loc_rgn_iff_in_heap hvalid).mpr ⟨_, hlookup, hvalid.h1 _ ?_⟩
    exact List.mem_map_of_mem (AList.mem_lookup_iff.mp (Option.mem_def.mpr hlookup))
  | step hobj hcontains hrr ih =>
    intro oid' href'
    have hloc := ih hvalid _ rfl
    obtain ⟨region, hlookup, hmem⟩ := (oid_loc_rgn_iff_in_heap hvalid).mp hloc
    dsimp only [Reference.objAt?] at hobj
    rw [hloc] at hobj
    dsimp only at hobj
    rw [hlookup] at hobj
    dsimp at hobj
    have hobj_mem_entries := AList.mem_lookup_iff.mp (Option.mem_def.mpr hobj)
    have hobj_mem_values := List.mem_map_of_mem (f := (·.2)) hobj_mem_entries
    dsimp only at hobj_mem_values
    have href_in_obj_refs := List.contains_iff_mem.mp hcontains
    have href_in_region_refs : _ ∈ region.refs :=
      List.mem_flatMap_of_mem hobj_mem_values href_in_obj_refs
    rw [href'] at href_in_region_refs ⊢
    exact hvalid.h3 _ oid' region hlookup href_in_region_refs

theorem RegionReachable_stays_in_region : ValidConfig cfg ->
  RegionReachable cfg rid (Reference.OId oid) ->
  (Reference.OId oid).loc? cfg = some (Location.Rgn rid) := by
  -- per case anaylsis on the RegionReachable inductive definition
  -- bridge case is trivial, as the bridge object is in the region
  -- step case -> the IH gives (OId oid).loc? cfg = some (Rgn rid); objAt? succeeding at
  -- oid means oid.loc? cfg is some loc (either Rgn or Stk), so H3 pins loc = Rgn rid
  -- (a frame-resident object would contradict H3, since the IH already places oid in rid)
  intro hvalid h
  exact RegionReachable_stays_in_region_aux cfg hvalid rid _ h oid rfl

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

theorem RegionReachable_implies_FrameReachable :
  frame ∈ cfg.stackWithIndex ->
  RegionReachable cfg frame.regionId ref ->
  FrameReachable cfg frame.index ref := by
  -- each case of RegionReachable matches to a case of FrameReachable directly:
  -- bridge -> bridge, step -> step (the objAt?/contains premises carry over unchanged)
  intro hframe h
  exact RegionReachable_implies_FrameReachable_aux cfg frame.regionId ref h frame hframe rfl
