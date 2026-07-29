import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Preservation.Common
import Gc.Reachability.Semantics
import Gc.Reachability.Path
import Gc.Reachability.Validity.Reachable

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

-- CR3 helper: the exact same H3 argument as `RegionReachable_stays_in_region_aux`'s `step` case
-- (a region's own refs can never point anywhere but back into that same region), just proved for
-- an arbitrary `ReflTransGen` start instead of one rooted at a region's bridge object specifically
-- -- so it applies to a chain that enters a region from *any* stack-held reference partway through,
-- not only from `RegionReachable`'s own bridge-rooted starting point. `head_induction_on` fixes the
-- target (here `Reference.OId oid`) and walks forward from an arbitrary start one hop at a time,
-- which is exactly the shape needed: propagate "resolves into `rid`" *forward*, hop by hop, from
-- wherever a chain element first resolves into `rid` all the way to the fixed final target.
theorem ReflTransGen_rgn_confined (cfg : RuntimeConfig) (hvalid : ValidConfig cfg)
    {start : Reference} {oid : ObjectId}
    (hrtg : Relation.ReflTransGen (RefStep cfg) start (Reference.OId oid))
    (rid : RegionId) (hoid_rgn : (Reference.OId oid).loc? cfg = some (Location.Rgn rid)) :
    ∀ oids, start = Reference.OId oids →
      ∀ rid', (Reference.OId oids).loc? cfg = some (Location.Rgn rid') → rid' = rid := by
  induction hrtg using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro oids hoids rid' hrgn'
    injection hoids with hoid_eq
    rw [← hoid_eq] at hrgn'
    have heq := hoid_rgn.symm.trans hrgn'
    simp only [Option.some.injEq, Location.Rgn.injEq] at heq
    exact heq.symm
  | head hstep hrest ih =>
    intro oids hoids rid' hrgn'
    subst hoids
    rename_i c
    have hc_oid : ∃ oidc, c = Reference.OId oidc := by
      rcases hrest.cases_head with heq | ⟨d, hcd, _⟩
      · exact ⟨oid, heq⟩
      · exact hcd.exists_oid_left
    obtain ⟨oidc, hc_eq⟩ := hc_oid
    have hc_rgn : (Reference.OId oidc).loc? cfg = some (Location.Rgn rid') := by
      obtain ⟨obj, hobjAt, hcontains⟩ := hstep
      dsimp only [Reference.objAt?] at hobjAt
      rw [hrgn'] at hobjAt
      dsimp only at hobjAt
      obtain ⟨region, hlookup, hmem⟩ := (oid_loc_rgn_iff_in_heap hvalid).mp hrgn'
      rw [hlookup] at hobjAt
      dsimp at hobjAt
      have hobj_mem_entries := AList.mem_lookup_iff.mp (Option.mem_def.mpr hobjAt)
      have hobj_mem_values := List.mem_map_of_mem (f := (·.2)) hobj_mem_entries
      dsimp only at hobj_mem_values
      have hc_in_obj_refs := List.contains_iff_mem.mp hcontains
      rw [hc_eq] at hc_in_obj_refs
      have hc_in_region_refs : _ ∈ region.refs :=
        List.mem_flatMap_of_mem hobj_mem_values hc_in_obj_refs
      exact hvalid.h3 rid' oidc region hlookup hc_in_region_refs
    exact ih oidc hc_eq rid' hc_rgn

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

-- report.pdf CR2 is proved via three pieces: (1) every element of a path ending in an object
-- reference must itself be an object reference -- an `RId` can only ever be the *last* element
-- of an `IsChain (RefStep cfg)`, since `RefStep` can never step *from* an `RId` (`objAt?` is
-- always `none` there); (2) a path rooted at F can only ever resolve at or *before* F (S2/S3,
-- propagated forward hop-by-hop, monotonically non-increasing); (3) a path ending at an object
-- known to live in F's own region R can only ever resolve at or *after* F (S3 + S1-uniqueness,
-- propagated *backward* from the target). Combining (2) and (3) forces exact equality with F.

-- Piece (1). Proved by induction on the chain; the head of any `a :: b :: l` is forced `OId` by
-- `RefStep.exists_oid_left`, and `getLast?` is unaffected by dropping that head
-- (`List.getLast?_cons_cons`), so the IH (about `b :: l`) still applies to the same target.
private theorem Path_refs_all_oid (cfg : RuntimeConfig) (oid : ObjectId) (l : List Reference)
    (hchain : l.IsChain (RefStep cfg)) (hlast : l.getLast? = some (Reference.OId oid)) :
    ∀ r ∈ l, ∃ oidr, r = Reference.OId oidr := by
  induction hchain with
  | nil => intro r hr; exact absurd hr (List.not_mem_nil)
  | singleton a =>
    intro r hr
    rw [List.mem_singleton] at hr
    subst hr
    exact ⟨oid, (Option.some.inj hlast)⟩
  | cons_cons hr hrest ih =>
    rename_i a b rest
    intro r hr'
    have hlast' : (b :: rest).getLast? = some (Reference.OId oid) := by
      rw [← List.getLast?_cons_cons]; exact hlast
    rw [List.mem_cons] at hr'
    rcases hr' with rfl | hr'
    · exact hr.exists_oid_left
    · exact ih hlast' r hr'

-- Piece (2), the forward/upper-bound half. Base case is `FrameRoot`'s two disjuncts: the
-- var-root case is a direct one-hop S2/S3 application (`start ∈ frame1.refs`, `frame1.index =
-- frame.index` already given); the bridge-root case shows `start` resolves into `Rgn
-- frame.regionId` (via H1 + `oid_loc_rgn_iff_in_heap`, the same fact `bridge` needs), so its
-- Stk-clause is vacuous and its Rgn-clause is `frame.index ≤ frame.index` trivially. The
-- step case case-splits on whether the *source* of the `RefStep` resolves to `Stk` or `Rgn`:
-- from `Stk fid_a` (bounded `≤ frame.index` by IH), one more S2/S3 hop bounds the target by
-- `fid_a`, hence transitively by `frame.index`; from `Rgn rid_a` (whose *every* owning frame is
-- bounded `≤ frame.index` by IH), H3 pins the target back into the *same* `rid_a`, so the IH's
-- own bound applies unchanged.
-- `start`'s own bound, directly from `FrameRoot`'s two disjuncts (no chain induction needed).
private theorem FrameRoot_upper_bound (cfg : RuntimeConfig) (hvalid : ValidConfig cfg)
    (frame : FrameWithIndex) (start : Reference) (hroot : FrameRoot cfg frame.index start) :
    ∀ oidr, start = Reference.OId oidr →
      (∀ fid, (Reference.OId oidr).loc? cfg = some (Location.Stk fid) → fid ≤ frame.index) ∧
      (∀ frame' ∈ cfg.stackWithIndex, ∀ rid, (Reference.OId oidr).loc? cfg = some (Location.Rgn rid) →
        frame'.regionId = rid → frame'.index ≤ frame.index) := by
  rcases hroot with
    ⟨frame1, hframe1, hidx1, var, hlookup1⟩ | ⟨frame1, hframe1, hidx1, region1, hlookup1, hstart_eq⟩
  · intro oidr hoidr
    have hstart_mem_entries := AList.mem_lookup_iff.mp (Option.mem_def.mpr hlookup1)
    have hstart_mem_values := List.mem_map_of_mem (f := (·.2)) hstart_mem_entries
    dsimp only at hstart_mem_values
    have hstart_in_refs : start ∈ frame1.refs := List.mem_append_right _ hstart_mem_values
    rw [hoidr] at hstart_in_refs
    refine ⟨fun fid hstk => ?_, fun frame' hframe' rid hrgn hfr => ?_⟩
    · have hle := hvalid.s2 frame1 hframe1 (Reference.OId oidr) hstart_in_refs fid oidr rfl hstk
      rw [hidx1] at hle
      exact hle
    · obtain ⟨frame'', hframe''_mem, hframe''_rid, hframe''_le⟩ :=
        hvalid.s3 frame1 hframe1 (Reference.OId oidr) hstart_in_refs rid oidr rfl hrgn
      rw [hidx1] at hframe''_le
      have hidx_eq := merge_corollary_regionId_unique_index hvalid.s1 hframe' hframe''_mem
        (hfr.trans hframe''_rid.symm)
      rw [hidx_eq]
      exact hframe''_le
  · intro oidr hoidr
    rw [hoidr] at hstart_eq
    injection hstart_eq with hoidr_eq
    have hmem : region1 ∈ cfg.heap.regions :=
      List.mem_map_of_mem (AList.mem_lookup_iff.mp (Option.mem_def.mpr hlookup1))
    have hstart_rgn : (Reference.OId oidr).loc? cfg = some (Location.Rgn frame1.regionId) := by
      rw [hoidr_eq]
      exact (oid_loc_rgn_iff_in_heap hvalid).mpr ⟨region1, hlookup1, hvalid.h1 region1 hmem⟩
    refine ⟨fun fid hstk => ?_, fun frame' hframe' rid hrgn hfr => ?_⟩
    · rw [hstart_rgn] at hstk; simp at hstk
    · rw [hstart_rgn, Option.some.injEq, Location.Rgn.injEq] at hrgn
      subst hrgn
      have hidx_eq := merge_corollary_regionId_unique_index hvalid.s1 hframe' hframe1 hfr
      rw [hidx_eq, hidx1]

-- One RefStep hop, propagating an already-known upper bound on the source to the target.
private theorem RefStep_upper_bound_step (cfg : RuntimeConfig) (hvalid : ValidConfig cfg)
    (frame : FrameWithIndex) (a b : Reference) (hr : RefStep cfg a b)
    (oida : ObjectId) (ha_eq : a = Reference.OId oida)
    (ha_stk : ∀ fid, (Reference.OId oida).loc? cfg = some (Location.Stk fid) → fid ≤ frame.index)
    (ha_rgn : ∀ frame' ∈ cfg.stackWithIndex, ∀ rid, (Reference.OId oida).loc? cfg = some (Location.Rgn rid) →
      frame'.regionId = rid → frame'.index ≤ frame.index) :
    ∀ oidb, b = Reference.OId oidb →
      (∀ fid, (Reference.OId oidb).loc? cfg = some (Location.Stk fid) → fid ≤ frame.index) ∧
      (∀ frame' ∈ cfg.stackWithIndex, ∀ rid, (Reference.OId oidb).loc? cfg = some (Location.Rgn rid) →
        frame'.regionId = rid → frame'.index ≤ frame.index) := by
  obtain ⟨obj, hobjAt, hcontains⟩ := hr
  rw [ha_eq] at hobjAt
  dsimp only [Reference.objAt?] at hobjAt
  intro oidb hb_eq
  cases hloc : (Reference.OId oida).loc? cfg with
  | none => rw [hloc] at hobjAt; simp at hobjAt
  | some loc =>
    rw [hloc] at hobjAt
    cases loc with
    | Rgn rid_a =>
      dsimp only at hobjAt
      cases hlookup : cfg.heap.lookup rid_a with
      | none => rw [hlookup] at hobjAt; simp at hobjAt
      | some region_a =>
        rw [hlookup] at hobjAt
        dsimp at hobjAt
        have hobj_mem_entries := AList.mem_lookup_iff.mp (Option.mem_def.mpr hobjAt)
        have hobj_mem_values := List.mem_map_of_mem (f := (·.2)) hobj_mem_entries
        dsimp only at hobj_mem_values
        have hb_in_obj_refs := List.contains_iff_mem.mp hcontains
        have hb_in_region_refs : _ ∈ region_a.refs :=
          List.mem_flatMap_of_mem hobj_mem_values hb_in_obj_refs
        rw [hb_eq] at hb_in_region_refs
        have hb_rgn : (Reference.OId oidb).loc? cfg = some (Location.Rgn rid_a) :=
          hvalid.h3 rid_a oidb region_a hlookup hb_in_region_refs
        refine ⟨fun fid hstk => ?_, fun frame' hframe' rid hrgn hfr => ?_⟩
        · rw [hb_rgn] at hstk; simp at hstk
        · rw [hb_rgn, Option.some.injEq, Location.Rgn.injEq] at hrgn
          subst hrgn
          exact ha_rgn frame' hframe' rid_a hloc hfr
    | Stk fid_a =>
      dsimp only at hobjAt
      cases hfind : cfg.stackWithIndex.find? (fun frame => frame.index == fid_a) with
      | none => rw [hfind] at hobjAt; simp at hobjAt
      | some frameA =>
        rw [hfind] at hobjAt
        dsimp at hobjAt
        have hframeA_mem := List.mem_of_find?_eq_some hfind
        have hframeA_pred := List.find?_some hfind
        have hframeA_idx : frameA.index = fid_a := by
          simpa using hframeA_pred
        have hfid_a_le : fid_a ≤ frame.index := ha_stk fid_a hloc
        have hobj_mem_entries := AList.mem_lookup_iff.mp (Option.mem_def.mpr hobjAt)
        have hobj_mem_values := List.mem_map_of_mem (f := (·.2)) hobj_mem_entries
        dsimp only at hobj_mem_values
        have hb_in_obj_refs := List.contains_iff_mem.mp hcontains
        have hb_in_frame_refs : _ ∈ frameA.refs :=
          List.mem_append_left _ (List.mem_flatMap_of_mem hobj_mem_values hb_in_obj_refs)
        rw [hb_eq] at hb_in_frame_refs
        refine ⟨fun fid hstk => ?_, fun frame' hframe' rid hrgn hfr => ?_⟩
        · have := hvalid.s2 frameA hframeA_mem (Reference.OId oidb) hb_in_frame_refs fid oidb rfl hstk
          rw [hframeA_idx] at this
          exact le_trans this hfid_a_le
        · obtain ⟨frame'', hframe''_mem, hframe''_rid, hframe''_le⟩ :=
            hvalid.s3 frameA hframeA_mem (Reference.OId oidb) hb_in_frame_refs rid oidb rfl hrgn
          rw [hframeA_idx] at hframe''_le
          have hidx_eq := merge_corollary_regionId_unique_index hvalid.s1 hframe' hframe''_mem
            (hfr.trans hframe''_rid.symm)
          rw [hidx_eq]
          exact le_trans hframe''_le hfid_a_le

-- Given the bound already established for the head of `l`, propagate it to every element.
-- Generalized over `a0`/`hhead`/`hbound0` (rather than fixing them as top-level parameters), for
-- the same reason as `RegionReachable_stays_in_region_aux`: the recursive call needs to supply a
-- *different* head (`b`, for the tail `b :: rest`) than the outer theorem's own `a0`, so `a0` has
-- to be part of what `induction` generalizes over, not fixed before it.
private theorem Path_bound_of_head_bound (cfg : RuntimeConfig) (hvalid : ValidConfig cfg)
    (frame : FrameWithIndex) (l : List Reference) (hchain : l.IsChain (RefStep cfg)) :
    ∀ a0, l.head? = some a0 →
    (∀ oida, a0 = Reference.OId oida →
      (∀ fid, (Reference.OId oida).loc? cfg = some (Location.Stk fid) → fid ≤ frame.index) ∧
      (∀ frame' ∈ cfg.stackWithIndex, ∀ rid, (Reference.OId oida).loc? cfg = some (Location.Rgn rid) →
        frame'.regionId = rid → frame'.index ≤ frame.index)) →
    ∀ r ∈ l, ∀ oidr, r = Reference.OId oidr →
      (∀ fid, (Reference.OId oidr).loc? cfg = some (Location.Stk fid) → fid ≤ frame.index) ∧
      (∀ frame' ∈ cfg.stackWithIndex, ∀ rid, (Reference.OId oidr).loc? cfg = some (Location.Rgn rid) →
        frame'.regionId = rid → frame'.index ≤ frame.index) := by
  induction hchain with
  | nil => intro a0 hhead hbound0 r hr; exact absurd hr List.not_mem_nil
  | singleton c =>
    intro a0 hhead hbound0 r hr
    rw [List.mem_singleton] at hr
    subst hr
    have hc : r = a0 := Option.some.inj hhead
    intro oidr hoidr
    rw [hc] at hoidr
    exact hbound0 oidr hoidr
  | cons_cons hr hrest ih =>
    rename_i a b rest
    intro a0 hhead hbound0
    have ha_eq0 : a = a0 := Option.some.inj hhead
    obtain ⟨oida, ha_eq⟩ := hr.exists_oid_left
    have hoida0 : a0 = Reference.OId oida := by rw [← ha_eq0, ha_eq]
    have hbound_a := hbound0 oida hoida0
    have hbound_b := RefStep_upper_bound_step cfg hvalid frame a b hr oida ha_eq
      hbound_a.1 hbound_a.2
    intro r hr'
    rw [List.mem_cons] at hr'
    rcases hr' with rfl | hr'
    · intro oidr hoidr
      rw [ha_eq0] at hoidr
      exact hbound0 oidr hoidr
    · exact ih b rfl hbound_b r hr'

private theorem Path_from_frame_upper_bound (cfg : RuntimeConfig) (hvalid : ValidConfig cfg)
    (frame : FrameWithIndex) (start : Reference) (hroot : FrameRoot cfg frame.index start)
    (l : List Reference) (hchain : l.IsChain (RefStep cfg)) (hhead : l.head? = some start) :
    ∀ r ∈ l, ∀ oidr, r = Reference.OId oidr →
      (∀ fid, (Reference.OId oidr).loc? cfg = some (Location.Stk fid) → fid ≤ frame.index) ∧
      (∀ frame' ∈ cfg.stackWithIndex, ∀ rid, (Reference.OId oidr).loc? cfg = some (Location.Rgn rid) →
        frame'.regionId = rid → frame'.index ≤ frame.index) :=
  Path_bound_of_head_bound cfg hvalid frame l hchain start hhead
    (FrameRoot_upper_bound cfg hvalid frame start hroot)

-- `ReflTransGen`-flavored restatement of `Path_from_frame_upper_bound`: any owner of a region
-- reached along a chain rooted at `frameY` has index ≤ `frameY.index` (mirrors the Rgn-side of the
-- same S2/S3 upper-bound argument used for CR2, just phrased via `Relation.ReflTransGen` instead
-- of an explicit `List`/`Path`, since that's what CR3's `FrameReachable_iff_reflTransGen` produces).
-- Used by CR3 proofs of the Preservation/*.lean operations that write a *pre-existing* reference
-- value into a new slot (VarAsgn/FieldAsgn/Swap): if that value resolves into a suspended region
-- `rid`, its owner cannot be *later* than wherever the value was read from.
theorem ReflTransGen_upper_bound (cfg : RuntimeConfig) (hvalid : ValidConfig cfg)
    (frameY : FrameWithIndex) {start target : Reference}
    (hrtg : Relation.ReflTransGen (RefStep cfg) start target)
    (hbound0 : ∀ oida, start = Reference.OId oida →
      (∀ fid, (Reference.OId oida).loc? cfg = some (Location.Stk fid) → fid ≤ frameY.index) ∧
      (∀ frame' ∈ cfg.stackWithIndex, ∀ rid, (Reference.OId oida).loc? cfg = some (Location.Rgn rid) →
        frame'.regionId = rid → frame'.index ≤ frameY.index)) :
    ∀ oidr, target = Reference.OId oidr →
      (∀ fid, (Reference.OId oidr).loc? cfg = some (Location.Stk fid) → fid ≤ frameY.index) ∧
      (∀ frame' ∈ cfg.stackWithIndex, ∀ rid, (Reference.OId oidr).loc? cfg = some (Location.Rgn rid) →
        frame'.regionId = rid → frame'.index ≤ frameY.index) := by
  induction hrtg with
  | refl => exact hbound0
  | tail _ hstep ih =>
    intro oidr hoidr
    obtain ⟨oida, ha_eq⟩ := hstep.exists_oid_left
    exact RefStep_upper_bound_step cfg hvalid frameY _ _ hstep oida ha_eq
      (ih oida ha_eq).1 (ih oida ha_eq).2 oidr hoidr

-- Packages `ReflTransGen_upper_bound` together with `FrameRoot_upper_bound` for the common case
-- where the chain is rooted via an actual `FrameRoot` (rather than an arbitrary already-known
-- bound on `start`).
theorem FrameReachable_owner_index_le (cfg : RuntimeConfig) (hvalid : ValidConfig cfg)
    (frameY : FrameWithIndex) {oid : ObjectId} (hreach : FrameReachable cfg frameY.index (Reference.OId oid))
    (rid : RegionId) (hoid_rgn : (Reference.OId oid).loc? cfg = some (Location.Rgn rid))
    (frameOwner : FrameWithIndex) (hframeOwnerMem : frameOwner ∈ cfg.stackWithIndex)
    (hframeOwnerRid : frameOwner.regionId = rid) :
    frameOwner.index ≤ frameY.index := by
  rw [FrameReachable_iff_reflTransGen] at hreach
  obtain ⟨start, hroot, hrtg⟩ := hreach
  exact (ReflTransGen_upper_bound cfg hvalid frameY hrtg (FrameRoot_upper_bound cfg hvalid frameY start hroot)
    oid rfl).2 frameOwner hframeOwnerMem rid hoid_rgn hframeOwnerRid

-- Stk-side analogue of `FrameReachable_owner_index_le`: an object `FrameReachable` from `frameY`
-- that resolves onto the stack itself can only resolve at or before `frameY.index`.
theorem FrameReachable_stk_index_le (cfg : RuntimeConfig) (hvalid : ValidConfig cfg)
    (frameY : FrameWithIndex) {oid : ObjectId} (hreach : FrameReachable cfg frameY.index (Reference.OId oid))
    (fid : Index) (hoid_stk : (Reference.OId oid).loc? cfg = some (Location.Stk fid)) :
    fid ≤ frameY.index := by
  rw [FrameReachable_iff_reflTransGen] at hreach
  obtain ⟨start, hroot, hrtg⟩ := hreach
  exact (ReflTransGen_upper_bound cfg hvalid frameY hrtg (FrameRoot_upper_bound cfg hvalid frameY start hroot)
    oid rfl).1 fid hoid_stk

-- An allocated object id always resolves somewhere (never `none`) -- needed because the backward
-- step below has to determine whether the *successor* in a step resolves `Stk` or `Rgn` before it
-- can pick which of S2/S3 to chain through.
theorem loc_ne_none_of_mem_objectIds (cfg : RuntimeConfig) (hvalid : ValidConfig cfg) (oid : ObjectId)
    (hmem : oid ∈ cfg.objectIds) : (Reference.OId oid).loc? cfg ≠ none := by
  unfold RuntimeConfig.objectIds at hmem
  rw [List.mem_append] at hmem
  unfold Reference.loc?
  dsimp only
  cases hs : cfg.stackWithIndex.findRev? (fun frame => frame.objMap.keys.contains oid) with
  | some frame => rw [oid_in_stack_implies_not_in_heap hvalid hs]; simp
  | none =>
    cases hh : cfg.heap.entries.find? (fun x => x.snd.objMap.keys.contains oid) with
    | some pr => simp
    | none =>
      simp only [ne_eq, not_true_eq_false]
      rcases hmem with hmem_stack | hmem_heap
      · unfold Stack.objectIds at hmem_stack
        rw [List.bind_eq_flatMap, List.flatMap_id, List.mem_flatten] at hmem_stack
        obtain ⟨keys, hkeys_mem, hoid_mem⟩ := hmem_stack
        obtain ⟨frame0, hframe0_mem, hframe0_eq⟩ := List.mem_map.mp hkeys_mem
        unfold Frame.objectIds at hframe0_eq
        rw [← hframe0_eq] at hoid_mem
        obtain ⟨n, hn, hn_eq⟩ := List.mem_iff_getElem.mp hframe0_mem
        have hlen : n < cfg.stackWithIndex.length := by
          unfold RuntimeConfig.stackWithIndex; rwa [List.length_mapIdx]
        have hget : cfg.stackWithIndex[n].objMap = frame0.objMap := by
          unfold RuntimeConfig.stackWithIndex
          rw [List.getElem_mapIdx, hn_eq]
        have hmemW := List.getElem_mem hlen
        have hcontains : cfg.stackWithIndex[n].objMap.keys.contains oid = true := by
          rw [hget]; exact List.contains_iff_mem.mpr (AList.mem_keys.mpr hoid_mem)
        rw [List.findRev?_eq_find?_reverse] at hs
        exact List.find?_eq_none.mp hs cfg.stackWithIndex[n] (List.mem_reverse.mpr hmemW) hcontains
      · unfold Heap.objectIds at hmem_heap
        rw [List.mem_flatten] at hmem_heap
        obtain ⟨keys, hkeys_mem, hoid_mem⟩ := hmem_heap
        obtain ⟨pr, hpr_mem, hpr_eq⟩ := List.mem_map.mp hkeys_mem
        unfold Region.objectIds at hpr_eq
        rw [← hpr_eq] at hoid_mem
        have hcontains : pr.2.objMap.keys.contains oid = true :=
          List.contains_iff_mem.mpr (AList.mem_keys.mpr hoid_mem)
        exact List.find?_eq_none.mp hh pr hpr_mem hcontains

-- One RefStep hop, propagating an already-known lower bound on the target back to the source.
private theorem RefStep_lower_bound_step (cfg : RuntimeConfig) (hvalid : ValidConfig cfg)
    (frame : FrameWithIndex) (a b : Reference) (hr : RefStep cfg a b)
    (oidb : ObjectId) (hb_eq : b = Reference.OId oidb)
    (hb_stk : ∀ fid, (Reference.OId oidb).loc? cfg = some (Location.Stk fid) → fid ≥ frame.index)
    (hb_rgn : ∀ frame' ∈ cfg.stackWithIndex, ∀ rid, (Reference.OId oidb).loc? cfg = some (Location.Rgn rid) →
      frame'.regionId = rid → frame'.index ≥ frame.index)
    (oida : ObjectId) (ha_eq : a = Reference.OId oida) :
    (∀ fid, (Reference.OId oida).loc? cfg = some (Location.Stk fid) → fid ≥ frame.index) ∧
    (∀ frame' ∈ cfg.stackWithIndex, ∀ rid, (Reference.OId oida).loc? cfg = some (Location.Rgn rid) →
      frame'.regionId = rid → frame'.index ≥ frame.index) := by
  obtain ⟨obj, hobjAt, hcontains⟩ := hr
  rw [ha_eq] at hobjAt
  dsimp only [Reference.objAt?] at hobjAt
  cases hloc : (Reference.OId oida).loc? cfg with
  | none => rw [hloc] at hobjAt; simp at hobjAt
  | some loc =>
    rw [hloc] at hobjAt
    cases loc with
    | Rgn rid_a =>
      dsimp only at hobjAt
      cases hlookup : cfg.heap.lookup rid_a with
      | none => rw [hlookup] at hobjAt; simp at hobjAt
      | some region_a =>
        rw [hlookup] at hobjAt
        dsimp at hobjAt
        have hobj_mem_entries := AList.mem_lookup_iff.mp (Option.mem_def.mpr hobjAt)
        have hobj_mem_values := List.mem_map_of_mem (f := (·.2)) hobj_mem_entries
        dsimp only at hobj_mem_values
        have hb_in_obj_refs := List.contains_iff_mem.mp hcontains
        have hb_in_region_refs : _ ∈ region_a.refs :=
          List.mem_flatMap_of_mem hobj_mem_values hb_in_obj_refs
        rw [hb_eq] at hb_in_region_refs
        have hb_rgn' : (Reference.OId oidb).loc? cfg = some (Location.Rgn rid_a) :=
          hvalid.h3 rid_a oidb region_a hlookup hb_in_region_refs
        refine ⟨fun fid hstk => ?_, fun frame' hframe' rid hrgn hfr => ?_⟩
        · simp at hstk
        · rw [Option.some.injEq, Location.Rgn.injEq] at hrgn
          subst hrgn
          exact hb_rgn frame' hframe' rid_a hb_rgn' hfr
    | Stk fid_a =>
      dsimp only at hobjAt
      cases hfind : cfg.stackWithIndex.find? (fun frame => frame.index == fid_a) with
      | none => rw [hfind] at hobjAt; simp at hobjAt
      | some frameA =>
        rw [hfind] at hobjAt
        dsimp at hobjAt
        have hframeA_mem := List.mem_of_find?_eq_some hfind
        have hframeA_pred := List.find?_some hfind
        have hframeA_idx : frameA.index = fid_a := by simpa using hframeA_pred
        have hobj_mem_entries := AList.mem_lookup_iff.mp (Option.mem_def.mpr hobjAt)
        have hobj_mem_values := List.mem_map_of_mem (f := (·.2)) hobj_mem_entries
        dsimp only at hobj_mem_values
        have hb_in_obj_refs := List.contains_iff_mem.mp hcontains
        have hb_in_frame_refs : _ ∈ frameA.refs :=
          List.mem_append_left _ (List.mem_flatMap_of_mem hobj_mem_values hb_in_obj_refs)
        rw [hb_eq] at hb_in_frame_refs
        have hb_alloc : oidb ∈ cfg.objectIds := by
          apply hvalid.hs1
          have hframeA_mem' : frameA ∈ cfg.stackWithIndex := hframeA_mem
          unfold RuntimeConfig.stackWithIndex at hframeA_mem'
          obtain ⟨n, hn_len, hn_eq⟩ := List.mem_mapIdx.mp hframeA_mem'
          have hg_in_stack : frameA.toFrame ∈ cfg.stack := by
            rw [← hn_eq]
            dsimp
            exact List.mem_iff_getElem.mpr ⟨n, _, rfl⟩
          unfold RuntimeConfig.refs Stack.refs
          apply List.mem_append_left
          rw [List.bind_eq_flatMap, List.mem_flatMap]
          exact ⟨Frame.refs frameA.toFrame, List.mem_map_of_mem hg_in_stack, hb_in_frame_refs⟩
        have hb_ne_none := loc_ne_none_of_mem_objectIds cfg hvalid oidb hb_alloc
        cases hlocb : (Reference.OId oidb).loc? cfg with
        | none => exact absurd hlocb hb_ne_none
        | some locb =>
          cases locb with
          | Stk fid_b =>
            have hfid_b_ge := hb_stk fid_b hlocb
            have hfid_b_le := hvalid.s2 frameA hframeA_mem (Reference.OId oidb) hb_in_frame_refs fid_b oidb rfl hlocb
            rw [hframeA_idx] at hfid_b_le
            refine ⟨fun fid hstk => ?_, fun frame' hframe' rid hrgn hfr => ?_⟩
            · rw [Option.some.injEq, Location.Stk.injEq] at hstk
              rw [← hstk]
              exact le_trans hfid_b_ge hfid_b_le
            · simp at hrgn
          | Rgn rid_b =>
            obtain ⟨frame'', hframe''_mem, hframe''_rid, hframe''_le⟩ :=
              hvalid.s3 frameA hframeA_mem (Reference.OId oidb) hb_in_frame_refs rid_b oidb rfl hlocb
            rw [hframeA_idx] at hframe''_le
            have hframe''_ge := hb_rgn frame'' hframe''_mem rid_b hlocb hframe''_rid
            refine ⟨fun fid hstk => ?_, fun frame' hframe' rid hrgn hfr => ?_⟩
            · rw [Option.some.injEq, Location.Stk.injEq] at hstk
              rw [← hstk]
              exact le_trans hframe''_ge hframe''_le
            · simp at hrgn

-- Piece (3), the backward/lower-bound half. Base case is `htarget`/`hoid`: the last element is
-- exactly `OId oid`, resolving into `Rgn frame.regionId`, and `frame` itself is (trivially) an
-- owner of that region with index `= frame.index ≥ frame.index`; any *other* claimed owner is
-- forced to also have index `= frame.index` by S1-uniqueness (`merge_corollary_regionId_unique_index`).
-- The step case propagates *backward*: given the bound already established for the successor
-- `b` (via the IH, using `Path_refs_all_oid` to know `b` is itself `OId`-shaped so the IH's
-- bound is actually usable, not vacuous), derive the bound for the source `a`. From `a` resolving
-- `Rgn rid_a`: H3 pins `b` into the *same* `rid_a`, so `b`'s (now-known) bound on `rid_a`'s
-- owners transfers unchanged to `a`'s own goal. From `a` resolving `Stk fid_a`: S3 applied to
-- `a`'s own frame gives, for *b* resolving into some region, an owning frame with index `≤
-- fid_a`; chaining through `b`'s bound (index of that same owner `≥ frame.index`, by
-- S1-uniqueness identifying it with whatever owner `b`'s IH bound was stated about) yields
-- `fid_a ≥ frame.index`.
private theorem Path_from_frame_lower_bound (cfg : RuntimeConfig) (hvalid : ValidConfig cfg)
    (frame : FrameWithIndex) (hframe : frame ∈ cfg.stackWithIndex)
    (oid : ObjectId) (hoid : (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId))
    (l : List Reference) (hchain : l.IsChain (RefStep cfg))
    (hlast : l.getLast? = some (Reference.OId oid)) :
    ∀ r ∈ l, ∀ oidr, r = Reference.OId oidr →
      (∀ fid, (Reference.OId oidr).loc? cfg = some (Location.Stk fid) → fid ≥ frame.index) ∧
      (∀ frame' ∈ cfg.stackWithIndex, ∀ rid, (Reference.OId oidr).loc? cfg = some (Location.Rgn rid) →
        frame'.regionId = rid → frame'.index ≥ frame.index) := by
  induction hchain with
  | nil => intro r hr; exact absurd hr List.not_mem_nil
  | singleton c =>
    intro r hr
    rw [List.mem_singleton] at hr
    subst hr
    have hc : r = Reference.OId oid := Option.some.inj hlast
    intro oidr hoidr
    rw [hc] at hoidr
    injection hoidr with hoidr_eq
    subst hoidr_eq
    refine ⟨fun fid hstk => ?_, fun frame' hframe' rid hrgn hfr => ?_⟩
    · rw [hoid] at hstk; simp at hstk
    · rw [hoid, Option.some.injEq, Location.Rgn.injEq] at hrgn
      subst hrgn
      have hidx_eq := merge_corollary_regionId_unique_index hvalid.s1 hframe' hframe hfr
      rw [hidx_eq]
  | cons_cons hr hrest ih =>
    rename_i a b rest
    have hlast' : (b :: rest).getLast? = some (Reference.OId oid) := by
      rw [← List.getLast?_cons_cons]; exact hlast
    obtain ⟨oidb, hb_eq⟩ := Path_refs_all_oid cfg oid (b :: rest) hrest hlast' b (List.mem_cons_self ..)
    have hbound_b := ih hlast' b (List.mem_cons_self ..) oidb hb_eq
    obtain ⟨oida, ha_eq⟩ := hr.exists_oid_left
    have hbound_a := RefStep_lower_bound_step cfg hvalid frame a b hr oidb hb_eq
      hbound_b.1 hbound_b.2 oida ha_eq
    intro r hr'
    rw [List.mem_cons] at hr'
    rcases hr' with rfl | hr'
    · intro oidr hoidr
      rw [ha_eq] at hoidr
      injection hoidr with hoidr_eq
      subst hoidr_eq
      exact hbound_a
    · exact ih hlast' r hr'

-- report.pdf CR2: "A path to an object o in region R with an associated frame F from F
-- passes through F or no frame at all." `R` is `frame.regionId` (the region F opened/owns) and
-- "from F" is captured by `FrameRoot cfg frame.index start` (the path's first reference is one
-- of the two ways a path can originate at F: a stack/bridge variable's value). "Passes through
-- frame F'" is read as: some reference along the path resolves (via `loc?`) into F''s stack
-- slot. The conclusion states the contrapositive of "F' ≠ F is impossible": whenever a
-- reference in the path resolves to a stack location at all, that location is F's own.
theorem Path_from_frame_to_own_region_stays_in_frame (cfg : RuntimeConfig) (hvalid : ValidConfig cfg)
    (frame : FrameWithIndex) (hframe : frame ∈ cfg.stackWithIndex)
    (oid : ObjectId) (hoid : (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId))
    (path : Path) (hvalidpath : ValidPath cfg path)
    (start : Reference) (hstart : path.refs.head? = some start) (hroot : FrameRoot cfg frame.index start)
    (htarget : path.refs.getLast? = some (Reference.OId oid)) :
    ∀ ref ∈ path.refs, ∀ fid, ref.loc? cfg = some (Location.Stk fid) → fid = frame.index := by
  intro ref hmem fid hfid
  obtain ⟨oidr, hoidr⟩ := Path_refs_all_oid cfg oid path.refs hvalidpath htarget ref hmem
  rw [hoidr] at hfid
  have hle := (Path_from_frame_upper_bound cfg hvalid frame start hroot path.refs hvalidpath hstart
    ref hmem oidr hoidr).1 fid hfid
  have hge := (Path_from_frame_lower_bound cfg hvalid frame hframe oid hoid path.refs hvalidpath htarget
    ref hmem oidr hoidr).1 fid hfid
  exact le_antisymm hle hge

-- A successful `resolveV` always retrieves a value that's already a `FrameRoot` witness
-- somewhere -- directly as a var's value, or as a region's bridge object. Shared by every
-- `Preservation` operation whose semantics resolves a `VarName`/`FieldAccess` root value that was
-- already present pre-mutation (`VarAsgn`, `FieldAsgn`, `Swap`'s `resolveFA_frameReach` below) --
-- previously three byte-for-byte-identical private copies, one per file (see CLAUDE.md's "Next
-- planned step" section for the consolidation rationale).
theorem resolveV_frameRoot {cfg : RuntimeConfig} {var : VarName} {oid : ObjectId}
    (hrv : resolveV var cfg = some (Reference.OId oid)) :
    ∃ frameY : FrameWithIndex, frameY ∈ cfg.stackWithIndex ∧ FrameRoot cfg frameY.index (Reference.OId oid) := by
  unfold resolveV at hrv
  cases hfV : cfg.stackWithIndex.findRev? (fun frame => frame.varMap.keys.contains var ∨ frame.bridgeVar == var) with
  | none => rw [hfV] at hrv; contradiction
  | some frameV =>
    rw [hfV] at hrv
    dsimp at hrv
    have hframeV_mem : frameV ∈ cfg.stackWithIndex := by
      rw [List.findRev?_eq_find?_reverse] at hfV
      exact List.mem_reverse.mp (List.mem_of_find?_eq_some hfV)
    cases hlookupV : frameV.varMap.lookup var with
    | some refV =>
      rw [hlookupV] at hrv
      dsimp at hrv
      rw [Option.some_inj] at hrv
      subst hrv
      exact ⟨frameV, hframeV_mem, Or.inl ⟨frameV, hframeV_mem, rfl, var, hlookupV⟩⟩
    | none =>
      rw [hlookupV] at hrv
      dsimp at hrv
      by_cases hbv : frameV.bridgeVar == var
      · rw [if_pos hbv] at hrv
        cases hregionV : cfg.heap.lookup frameV.regionId with
        | none => rw [hregionV] at hrv; dsimp at hrv; contradiction
        | some regionV =>
          rw [hregionV] at hrv
          dsimp at hrv
          rw [Option.some_inj, Reference.OId.injEq] at hrv
          exact ⟨frameV, hframeV_mem, Or.inr ⟨frameV, hframeV_mem, rfl, regionV, hregionV, by rw [hrv]⟩⟩
      · rw [if_neg hbv] at hrv; contradiction

-- A successful `resolveFA` retrieves a value that's already `FrameReachable` from *some* frame:
-- the root var/bridge value resolves to some container object oid0 (via `resolveV_frameRoot`),
-- and the field access itself is exactly one more `RefStep` hop from oid0's own object. Shared by
-- `VarAsgn`/`Swap` (both resolve a `FieldAccess`, unlike `FieldAsgn` whose `y : VarName` only
-- needs `resolveV_frameRoot` directly) -- previously two identical private copies.
theorem resolveFA_frameReach {cfg : RuntimeConfig} {y : FieldAccess} {oid : ObjectId}
    (hyf : resolveFA y cfg = some (Reference.OId oid)) :
    ∃ frameY : FrameWithIndex, frameY ∈ cfg.stackWithIndex ∧ FrameReachable cfg frameY.index (Reference.OId oid) := by
  unfold resolveFA at hyf
  cases hrv : resolveV y.root cfg with
  | none => rw [hrv] at hyf; contradiction
  | some ref0 =>
    rw [hrv] at hyf
    dsimp at hyf
    cases ref0 with
    | RId rid0 => dsimp at hyf; contradiction
    | OId oid0 =>
      dsimp at hyf
      cases hloc0 : (Reference.OId oid0).loc? cfg with
      | none => rw [hloc0] at hyf; dsimp at hyf; contradiction
      | some loc0 =>
        rw [hloc0] at hyf
        dsimp at hyf
        obtain ⟨frameY, hframeYMem, hrootY⟩ := resolveV_frameRoot hrv
        have hreachY0 : FrameReachable cfg frameY.index (Reference.OId oid0) := by
          rw [FrameReachable_iff_reflTransGen]
          exact ⟨Reference.OId oid0, hrootY, Relation.ReflTransGen.refl⟩
        cases loc0 with
        | Stk fid0 =>
          dsimp at hyf
          cases hframe0 : cfg.stackWithIndex.find? (fun frame => frame.index == fid0) with
          | none => rw [hframe0] at hyf; dsimp at hyf; contradiction
          | some frame0 =>
            rw [hframe0] at hyf
            dsimp at hyf
            cases hobj0 : frame0.objMap.lookup oid0 with
            | none => rw [hobj0] at hyf; dsimp at hyf; contradiction
            | some obj0 =>
              rw [hobj0] at hyf
              dsimp at hyf
              have hobjAt0 : (Reference.OId oid0).objAt? cfg = some obj0 := by
                unfold Reference.objAt?
                dsimp only
                rw [hloc0]
                dsimp only
                rw [hframe0]
                exact hobj0
              exact ⟨frameY, hframeYMem, FrameReachable.step hobjAt0 (List.contains_iff_mem.mpr
                (AList.mem_lookup_iff.mp (Option.mem_def.mpr hyf) |> (List.mem_map_of_mem (f := (·.2))) )
                ) hreachY0⟩
        | Rgn rid0 =>
          dsimp at hyf
          cases hregion0 : cfg.heap.lookup rid0 with
          | none => rw [hregion0] at hyf; dsimp at hyf; contradiction
          | some region0 =>
            rw [hregion0] at hyf
            dsimp at hyf
            cases hobj0 : region0.objMap.lookup oid0 with
            | none => rw [hobj0] at hyf; dsimp at hyf; contradiction
            | some obj0 =>
              rw [hobj0] at hyf
              dsimp at hyf
              have hobjAt0 : (Reference.OId oid0).objAt? cfg = some obj0 := by
                unfold Reference.objAt?
                dsimp only
                rw [hloc0]
                dsimp only
                rw [hregion0]
                exact hobj0
              exact ⟨frameY, hframeYMem, FrameReachable.step hobjAt0 (List.contains_iff_mem.mpr
                (AList.mem_lookup_iff.mp (Option.mem_def.mpr hyf) |> (List.mem_map_of_mem (f := (·.2))) )
                ) hreachY0⟩

-- Unpacks a `Rgn`-located `objAt?` success into the concrete region and objMap lookup witnessing
-- it -- used to line up two `Rgn`-located objects against the *same* region record before
-- invoking `two_oid_fields_mem_heap_refs`.
private theorem oid_region_lookup (cfg : RuntimeConfig) (oid : ObjectId) (rid : RegionId) (obj : Object)
    (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn rid))
    (hobjAt : (Reference.OId oid).objAt? cfg = some obj) :
    ∃ region, cfg.heap.lookup rid = some region ∧ region.objMap.lookup oid = some obj := by
  dsimp only [Reference.objAt?] at hobjAt
  rw [hloc] at hobjAt
  dsimp only at hobjAt
  cases hlookup : cfg.heap.lookup rid with
  | none => rw [hlookup] at hobjAt; simp at hobjAt
  | some region =>
    rw [hlookup] at hobjAt
    dsimp at hobjAt
    exact ⟨region, rfl, hobjAt⟩

-- An object already stored at some key of a region's objMap already contributes its own field
-- values to the whole region's refs.
private theorem objMap_lookup_mem_region_refs (region : Region) (oid : ObjectId) (obj : Object)
    (hobj : region.objMap.lookup oid = some obj) (r : Reference) (hcontains : obj.refs.contains r = true) :
    r ∈ Region.refs region := by
  have hobj_mem_entries := AList.mem_lookup_iff.mp (Option.mem_def.mpr hobj)
  have hobj_mem_values := List.mem_map_of_mem (f := (·.2)) hobj_mem_entries
  dsimp only at hobj_mem_values
  have hr_in_obj_refs := List.contains_iff_mem.mp hcontains
  exact List.mem_flatMap_of_mem hobj_mem_values hr_in_obj_refs

-- If `oid` resolves into region `rid` and some `r` is one of its object's own field values,
-- `r` already contributes to the whole heap's refs. Used by the CR4-for-regions case below to
-- turn an in-region object's field occurrence of a region reference into an `H2`-countable fact.
private theorem oid_field_mem_heap_refs (cfg : RuntimeConfig) (oid : ObjectId) (rid : RegionId)
    (obj : Object) (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn rid))
    (hobjAt : (Reference.OId oid).objAt? cfg = some obj) (r : Reference)
    (hcontains : obj.refs.contains r = true) :
    r ∈ cfg.heap.refs := by
  dsimp only [Reference.objAt?] at hobjAt
  rw [hloc] at hobjAt
  dsimp only at hobjAt
  cases hlookup : cfg.heap.lookup rid with
  | none => rw [hlookup] at hobjAt; simp at hobjAt
  | some region =>
    rw [hlookup] at hobjAt
    dsimp at hobjAt
    have hobj_mem_entries := AList.mem_lookup_iff.mp (Option.mem_def.mpr hobjAt)
    have hobj_mem_values := List.mem_map_of_mem (f := (·.2)) hobj_mem_entries
    dsimp only at hobj_mem_values
    have hr_in_obj_refs := List.contains_iff_mem.mp hcontains
    have hr_in_region_refs : r ∈ region.refs :=
      List.mem_flatMap_of_mem hobj_mem_values hr_in_obj_refs
    have hregion_mem_entries : (⟨rid, region⟩ : Sigma (fun _ : RegionId => Region)) ∈ cfg.heap.entries :=
      AList.mem_lookup_iff.mp (Option.mem_def.mpr hlookup)
    have hregion_mem_values := List.mem_map_of_mem (f := (·.2)) hregion_mem_entries
    dsimp only at hregion_mem_values
    unfold Heap.refs
    rw [List.bind_eq_flatMap, List.mem_flatMap]
    exact ⟨region, hregion_mem_values, hr_in_region_refs⟩

-- Any reference already present in some on-stack frame's own refs already contributes to the
-- whole stack's refs.
private theorem frame_refs_mem_stack_refs (cfg : RuntimeConfig) (frame1 : FrameWithIndex)
    (hframe1mem : frame1 ∈ cfg.stackWithIndex) (r : Reference) (hr : r ∈ frame1.refs) :
    r ∈ cfg.stack.refs := by
  have hframe1mem' : frame1 ∈ cfg.stackWithIndex := hframe1mem
  unfold RuntimeConfig.stackWithIndex at hframe1mem'
  obtain ⟨n, hn_len, hn_eq⟩ := List.mem_mapIdx.mp hframe1mem'
  have hg_in_stack : frame1.toFrame ∈ cfg.stack := by
    rw [← hn_eq]
    dsimp
    exact List.mem_iff_getElem.mpr ⟨n, _, rfl⟩
  unfold Stack.refs
  rw [List.bind_eq_flatMap, List.mem_flatMap]
  exact ⟨Frame.refs frame1.toFrame, List.mem_map_of_mem hg_in_stack, hr⟩

-- Any value in a stack frame's own varMap already contributes to the whole stack's refs.
private theorem var_mem_stack_refs (cfg : RuntimeConfig) (frame1 : FrameWithIndex)
    (hframe1mem : frame1 ∈ cfg.stackWithIndex) (var : VarName) (r : Reference)
    (hlookup : frame1.varMap.lookup var = some r) :
    r ∈ cfg.stack.refs := by
  have hr_mem_entries := AList.mem_lookup_iff.mp (Option.mem_def.mpr hlookup)
  have hr_mem_values := List.mem_map_of_mem (f := (·.2)) hr_mem_entries
  dsimp only at hr_mem_values
  exact frame_refs_mem_stack_refs cfg frame1 hframe1mem r (List.mem_append_right _ hr_mem_values)

-- If `oid` resolves onto the stack at index `fid` and some `r` is one of its object's own field
-- values, `r` already contributes to the whole stack's refs. Mirrors `oid_field_mem_heap_refs`.
private theorem oid_field_mem_stack_refs (cfg : RuntimeConfig) (oid : ObjectId) (fid : Index)
    (obj : Object) (hloc : (Reference.OId oid).loc? cfg = some (Location.Stk fid))
    (hobjAt : (Reference.OId oid).objAt? cfg = some obj) (r : Reference)
    (hcontains : obj.refs.contains r = true) :
    r ∈ cfg.stack.refs := by
  dsimp only [Reference.objAt?] at hobjAt
  rw [hloc] at hobjAt
  dsimp only at hobjAt
  cases hfind : cfg.stackWithIndex.find? (fun frame => frame.index == fid) with
  | none => rw [hfind] at hobjAt; simp at hobjAt
  | some frameA =>
    rw [hfind] at hobjAt
    dsimp at hobjAt
    have hobj_mem_entries := AList.mem_lookup_iff.mp (Option.mem_def.mpr hobjAt)
    have hobj_mem_values := List.mem_map_of_mem (f := (·.2)) hobj_mem_entries
    dsimp only at hobj_mem_values
    have hr_in_obj_refs := List.contains_iff_mem.mp hcontains
    have hr_in_frame_refs : r ∈ frameA.refs :=
      List.mem_append_left _ (List.mem_flatMap_of_mem hobj_mem_values hr_in_obj_refs)
    exact frame_refs_mem_stack_refs cfg frameA (List.mem_of_find?_eq_some hfind) r hr_in_frame_refs

-- Two distinct objects in the *same* region, both holding `r` as a field value, already forces
-- `cfg.heap.refs.count r ≥ 2` -- used (contrapositively) to rule out a region reference having
-- two distinct storage locations inside one region, per `H2`.
private theorem two_oid_fields_mem_heap_refs (cfg : RuntimeConfig) (rid : RegionId) (region : Region)
    (hlookup : cfg.heap.lookup rid = some region)
    (oid1 : ObjectId) (obj1 : Object) (hobj1 : region.objMap.lookup oid1 = some obj1)
    (oid2 : ObjectId) (obj2 : Object) (hobj2 : region.objMap.lookup oid2 = some obj2)
    (hne : oid1 ≠ oid2) (r : Reference)
    (hcontains1 : obj1.refs.contains r = true) (hcontains2 : obj2.refs.contains r = true) :
    2 ≤ cfg.heap.refs.count r := by
  have hmem1 : (⟨oid1, obj1⟩ : Sigma (fun _ : ObjectId => Object)) ∈ region.objMap.entries :=
    AList.mem_lookup_iff.mp (Option.mem_def.mpr hobj1)
  have hmem2 : (⟨oid2, obj2⟩ : Sigma (fun _ : ObjectId => Object)) ∈ region.objMap.entries :=
    AList.mem_lookup_iff.mp (Option.mem_def.mpr hobj2)
  have hneq : (⟨oid1, obj1⟩ : Sigma (fun _ : ObjectId => Object)) ≠ ⟨oid2, obj2⟩ := by
    intro h; exact hne (congrArg Sigma.fst h)
  have hb1 : r ∈ Object.refs obj1 := List.contains_iff_mem.mp hcontains1
  have hb2 : r ∈ Object.refs obj2 := List.contains_iff_mem.mp hcontains2
  have hcount := List.two_le_count_flatMap_of_ne (f := fun e => Object.refs e.2) hneq hmem1 hmem2 hb1 hb2
  have hregion_eq : region.objMap.entries.flatMap (fun e => Object.refs e.2) = Region.refs region := by
    unfold Region.refs
    rw [List.bind_eq_flatMap, List.flatMap_map]
  rw [hregion_eq] at hcount
  have hregion_mem : region ∈ cfg.heap.entries.map (·.2) :=
    List.mem_map_of_mem (AList.mem_lookup_iff.mp (Option.mem_def.mpr hlookup))
  have hle := List.count_le_count_flatMap_of_mem (f := Region.refs) hregion_mem (b := r)
  unfold Heap.refs
  rw [List.bind_eq_flatMap]
  omega

-- Two distinct regions, both holding `r` as a field value somewhere inside them, already forces
-- `cfg.heap.refs.count r ≥ 2` -- used (contrapositively) to rule out a region reference having
-- two distinct storage locations across different regions, per `H2`.
private theorem two_region_refs_mem_heap_refs (cfg : RuntimeConfig)
    (rid1 : RegionId) (region1 : Region) (hlookup1 : cfg.heap.lookup rid1 = some region1)
    (rid2 : RegionId) (region2 : Region) (hlookup2 : cfg.heap.lookup rid2 = some region2)
    (hne : rid1 ≠ rid2) (r : Reference)
    (hmem1 : r ∈ Region.refs region1) (hmem2 : r ∈ Region.refs region2) :
    2 ≤ cfg.heap.refs.count r := by
  have hmemE1 : (⟨rid1, region1⟩ : Sigma (fun _ : RegionId => Region)) ∈ cfg.heap.entries :=
    AList.mem_lookup_iff.mp (Option.mem_def.mpr hlookup1)
  have hmemE2 : (⟨rid2, region2⟩ : Sigma (fun _ : RegionId => Region)) ∈ cfg.heap.entries :=
    AList.mem_lookup_iff.mp (Option.mem_def.mpr hlookup2)
  have hneq : (⟨rid1, region1⟩ : Sigma (fun _ : RegionId => Region)) ≠ ⟨rid2, region2⟩ := by
    intro h; exact hne (congrArg Sigma.fst h)
  have hcount := List.two_le_count_flatMap_of_ne (f := fun e => Region.refs e.2) hneq hmemE1 hmemE2 hmem1 hmem2
  have hheap_eq : cfg.heap.entries.flatMap (fun e => Region.refs e.2) = Heap.refs cfg.heap := by
    unfold Heap.refs
    rw [List.bind_eq_flatMap, List.flatMap_map]
  rwa [hheap_eq] at hcount

-- Core CR4 argument for an object directly resident in the suspended region, reused both by
-- `StackReachable_iff_FrameReachable`'s own `OId` case and by its `RId` case (once an `RId`'s
-- unique storage location is traced back to an in-region object, see `oid_field_unique` below).
private theorem stackReachable_iff_frameReachable_oid (cfg : RuntimeConfig)
    (vrcfg : ValidReachableConfig cfg) (frame : FrameWithIndex) (hframemem : frame ∈ cfg.stackWithIndex)
    (oid : ObjectId) (hoid : (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId)) :
    StackReachable cfg (Reference.OId oid) ↔ FrameReachable cfg frame.index (Reference.OId oid) := by
  constructor
  · intro hstackreachable
    unfold StackReachable at hstackreachable
    obtain ⟨frame', hframe'mem, hframe'framereachable⟩ := hstackreachable
    have cr3 := vrcfg.cr3
    unfold CR3 at cr3
    have hle := FrameReachable_owner_index_le cfg vrcfg.toValidConfig frame' hframe'framereachable
      frame.regionId hoid frame hframemem rfl
    rcases hle.lt_or_eq with hlt | heq
    · exact cr3 frame hframemem frame' hframe'mem hlt oid hoid hframe'framereachable
    · have hframeq : frame = frame' := swap_corollary_stackWithIndex_index_inj hframemem hframe'mem heq
      rw [hframeq]; exact hframe'framereachable
  · intro hframereachable
    exists frame

-- report.pdf CR4, generalized to arbitrary references (not just objects): the hypothesis
-- `RegionReachable cfg frame.regionId ref` covers both the original OId-restricted case (`ref`
-- itself resides in the suspended region -- H3 forces every OId reachable *within* a region to
-- stay `loc?`-located in that same region, so this case reduces to the original argument via
-- `RegionReachable_stays_in_region`) and the new case where `ref` is a region reference
-- (`Reference.RId rid'`) sitting one field-hop beyond an in-region object -- `RegionReachable`'s
-- own `step` constructor already allows this, since only its *source* needs to be `OId`-shaped.
-- `_hframesus` isn't needed by the proof (CR3 already forces it vacuously when `frame` is the
-- active/last frame) -- kept only to stay faithful to the report's statement.
-- turns out this is irrespective of the frame, so we do not need a hypothesis saying that the
-- frame is suspended.
theorem StackReachable_iff_FrameReachable (cfg : RuntimeConfig) (vrcfg : ValidReachableConfig cfg)
    (frame : FrameWithIndex) (hframemem : frame ∈ cfg.stackWithIndex)
    (ref : Reference) (href : RegionReachable cfg frame.regionId ref) :
    StackReachable cfg ref ↔
    FrameReachable cfg frame.index ref := by
  cases ref with
  | OId oid =>
    have hoid : (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) :=
      RegionReachable_stays_in_region vrcfg.toValidConfig href
    exact stackReachable_iff_frameReachable_oid cfg vrcfg frame hframemem oid hoid
  | RId rid' =>
    cases href with
    | step hobj hcontains hrr =>
      rename_i oid obj
      have hoid : (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) :=
        RegionReachable_stays_in_region vrcfg.toValidConfig hrr
      constructor
      · intro hstackreachable
        obtain ⟨frame', hframe'mem, hframe'framereachable⟩ := hstackreachable
        have hrtg := (FrameReachable_iff_reflTransGen cfg frame'.index (Reference.RId rid')).mp
          hframe'framereachable
        obtain ⟨start, hroot, hchain⟩ := hrtg
        cases hchain with
        | refl =>
          exfalso
          rcases hroot with ⟨frame1, hframe1mem, _, var, hlookup⟩ |
            ⟨_, _, _, region1, _, hbridge⟩
          · have h1 : Reference.RId rid' ∈ cfg.stack.refs :=
              var_mem_stack_refs cfg frame1 hframe1mem var (Reference.RId rid') hlookup
            have h2 : Reference.RId rid' ∈ cfg.heap.refs :=
              oid_field_mem_heap_refs cfg oid frame.regionId obj hoid hobj (Reference.RId rid') hcontains
            have hc1 := List.count_pos_iff.mpr h1
            have hc2 := List.count_pos_iff.mpr h2
            have hbound := vrcfg.h2 rid'
            omega
          · exact absurd hbridge (by simp)
        | tail hprev hstep =>
          rename_i y
          obtain ⟨oid0, hy_eq⟩ := hstep.exists_oid_left
          subst hy_eq
          obtain ⟨obj0, hobjAt0, hcontains0⟩ := hstep
          cases hloc0 : (Reference.OId oid0).loc? cfg with
          | none =>
            exfalso
            dsimp only [Reference.objAt?] at hobjAt0
            rw [hloc0] at hobjAt0
            simp at hobjAt0
          | some loc0 =>
            cases loc0 with
            | Stk fid0 =>
              exfalso
              have h1 : Reference.RId rid' ∈ cfg.stack.refs :=
                oid_field_mem_stack_refs cfg oid0 fid0 obj0 hloc0 hobjAt0 (Reference.RId rid') hcontains0
              have h2 : Reference.RId rid' ∈ cfg.heap.refs :=
                oid_field_mem_heap_refs cfg oid frame.regionId obj hoid hobj (Reference.RId rid') hcontains
              have hc1 := List.count_pos_iff.mpr h1
              have hc2 := List.count_pos_iff.mpr h2
              have hbound := vrcfg.h2 rid'
              omega
            | Rgn rid0 =>
              obtain ⟨region0, hlookup0, hobjlookup0⟩ := oid_region_lookup cfg oid0 rid0 obj0 hloc0 hobjAt0
              obtain ⟨region, hlookup, hobjlookup⟩ := oid_region_lookup cfg oid frame.regionId obj hoid hobj
              by_cases heqrid : rid0 = frame.regionId
              · subst heqrid
                rw [hlookup] at hlookup0
                injection hlookup0 with hregion_eq
                subst hregion_eq
                by_cases heqoid : oid0 = oid
                · subst heqoid
                  rw [hobjlookup] at hobjlookup0
                  injection hobjlookup0 with hobj_eq
                  subst hobj_eq
                  have hoidreach : FrameReachable cfg frame'.index (Reference.OId oid0) :=
                    (FrameReachable_iff_reflTransGen cfg frame'.index (Reference.OId oid0)).mpr
                      ⟨start, hroot, hprev⟩
                  have hoidstack : StackReachable cfg (Reference.OId oid0) := ⟨frame', hframe'mem, hoidreach⟩
                  have hoidframe :=
                    (stackReachable_iff_frameReachable_oid cfg vrcfg frame hframemem oid0 hoid).mp hoidstack
                  exact FrameReachable.step hobj hcontains hoidframe
                · exfalso
                  have hcount := two_oid_fields_mem_heap_refs cfg frame.regionId region hlookup
                    oid obj hobjlookup oid0 obj0 hobjlookup0 (Ne.symm heqoid) (Reference.RId rid')
                    hcontains hcontains0
                  have hbound := vrcfg.h2 rid'
                  have hcstack : 0 ≤ cfg.stack.refs.count (Reference.RId rid') := Nat.zero_le _
                  omega
              · exfalso
                have hmem : Reference.RId rid' ∈ Region.refs region :=
                  objMap_lookup_mem_region_refs region oid obj hobjlookup (Reference.RId rid') hcontains
                have hmem0 : Reference.RId rid' ∈ Region.refs region0 :=
                  objMap_lookup_mem_region_refs region0 oid0 obj0 hobjlookup0 (Reference.RId rid') hcontains0
                have hcount := two_region_refs_mem_heap_refs cfg frame.regionId region hlookup rid0 region0
                  hlookup0 (Ne.symm heqrid) (Reference.RId rid') hmem hmem0
                have hbound := vrcfg.h2 rid'
                have hcstack : 0 ≤ cfg.stack.refs.count (Reference.RId rid') := Nat.zero_le _
                omega
      · intro hframereachable
        exists frame
