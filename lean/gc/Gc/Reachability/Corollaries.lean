import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Preservation.Merge
import Gc.Reachability.Semantics
import Gc.Reachability.Path

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
