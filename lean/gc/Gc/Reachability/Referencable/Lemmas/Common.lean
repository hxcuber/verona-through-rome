import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Preservation.Common
import Gc.Reachability.Referencable.Semantics

/-!
Generic, non-CR-specific reachability facts shared across `CR1.lean`,
`CR2.lean`, `CR4.lean`, and several `Gc/Reachability/Referencable/Lemmas/*.lean` files. Extracted
from the original monolithic `Corollaries.lean` (mirrors `Gc/Model/Preservation/Common.lean`'s own
consolidation).
-/

-- Generalized over `ref` (rather than fixing `ref := Reference.OId oid` up front) so that
-- `induction h` below works directly: `h`'s type is stated over a bare-variable index, and
-- the `∀ oid, ref = Reference.OId oid → ...` hypothesis is vacuous in a hypothetical `RId` case.
theorem RegionReferencable_stays_in_region_aux (cfg : RuntimeConfig) (hvalid : ValidConfig cfg)
    (rid : RegionId) (ref : Reference) (h : RegionReferencable cfg rid ref) :
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

theorem RegionReferencable_stays_in_region : ValidConfig cfg ->
  RegionReferencable cfg rid (Reference.OId oid) ->
  (Reference.OId oid).loc? cfg = some (Location.Rgn rid) := by
  -- per case anaylsis on the RegionReferencable inductive definition
  -- bridge case is trivial, as the bridge object is in the region
  -- step case -> the IH gives (OId oid).loc? cfg = some (Rgn rid); objAt? succeeding at
  -- oid means oid.loc? cfg is some loc (either Rgn or Stk), so H3 pins loc = Rgn rid
  -- (a frame-resident object would contradict H3, since the IH already places oid in rid)
  intro hvalid h
  exact RegionReferencable_stays_in_region_aux cfg hvalid rid _ h oid rfl

-- CR3 helper: the exact same H3 argument as `RegionReferencable_stays_in_region_aux`'s `step` case
-- (a region's own refs can never point anywhere but back into that same region), just proved for
-- an arbitrary `ReflTransGen` start instead of one rooted at a region's bridge object specifically
-- -- so it applies to a chain that enters a region from *any* stack-held reference partway through,
-- not only from `RegionReferencable`'s own bridge-rooted starting point. `head_induction_on` fixes the
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
-- Used by `CR2.lean`'s own path-based upper bound, and by `ReflTransGen_upper_bound`/
-- `FrameReferencable_owner_index_le`/`FrameReferencable_stk_index_le` below.
theorem FrameRoot_upper_bound (cfg : RuntimeConfig) (hvalid : ValidConfig cfg)
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

-- One RefStep hop, propagating an already-known upper bound on the source to the target. Used by
-- `CR2.lean`'s own `Path_bound_of_head_bound` and by `ReflTransGen_upper_bound` below.
theorem RefStep_upper_bound_step (cfg : RuntimeConfig) (hvalid : ValidConfig cfg)
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

-- `ReflTransGen`-flavored restatement of `Path_from_frame_upper_bound`: any owner of a region
-- reached along a chain rooted at `frameY` has index ≤ `frameY.index` (mirrors the Rgn-side of the
-- same S2/S3 upper-bound argument used for CR2, just phrased via `Relation.ReflTransGen` instead
-- of an explicit `List`/`Path`, since that's what CR3's `FrameReferencable_iff_reflTransGen` produces).
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
theorem FrameReferencable_owner_index_le (cfg : RuntimeConfig) (hvalid : ValidConfig cfg)
    (frameY : FrameWithIndex) {oid : ObjectId} (hreach : FrameReferencable cfg frameY.index (Reference.OId oid))
    (rid : RegionId) (hoid_rgn : (Reference.OId oid).loc? cfg = some (Location.Rgn rid))
    (frameOwner : FrameWithIndex) (hframeOwnerMem : frameOwner ∈ cfg.stackWithIndex)
    (hframeOwnerRid : frameOwner.regionId = rid) :
    frameOwner.index ≤ frameY.index := by
  rw [FrameReferencable_iff_reflTransGen] at hreach
  obtain ⟨start, hroot, hrtg⟩ := hreach
  exact (ReflTransGen_upper_bound cfg hvalid frameY hrtg (FrameRoot_upper_bound cfg hvalid frameY start hroot)
    oid rfl).2 frameOwner hframeOwnerMem rid hoid_rgn hframeOwnerRid

-- Stk-side analogue of `FrameReferencable_owner_index_le`: an object `FrameReferencable` from `frameY`
-- that resolves onto the stack itself can only resolve at or before `frameY.index`.
theorem FrameReferencable_stk_index_le (cfg : RuntimeConfig) (hvalid : ValidConfig cfg)
    (frameY : FrameWithIndex) {oid : ObjectId} (hreach : FrameReferencable cfg frameY.index (Reference.OId oid))
    (fid : Index) (hoid_stk : (Reference.OId oid).loc? cfg = some (Location.Stk fid)) :
    fid ≤ frameY.index := by
  rw [FrameReferencable_iff_reflTransGen] at hreach
  obtain ⟨start, hroot, hrtg⟩ := hreach
  exact (ReflTransGen_upper_bound cfg hvalid frameY hrtg (FrameRoot_upper_bound cfg hvalid frameY start hroot)
    oid rfl).1 fid hoid_stk

-- An allocated object id always resolves somewhere (never `none`) -- needed because the backward
-- step below has to determine whether the *successor* in a step resolves `Stk` or `Rgn` before it
-- can pick which of S2/S3 to chain through. Used by `CR2.lean`'s own
-- `RefStep_lower_bound_step`, and directly by `Merge`/`Exit`'s CR3 preservation proofs.
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

-- A successful `resolveFA` retrieves a value that's already `FrameReferencable` from *some* frame:
-- the root var/bridge value resolves to some container object oid0 (via `resolveV_frameRoot`),
-- and the field access itself is exactly one more `RefStep` hop from oid0's own object. Shared by
-- `VarAsgn`/`Swap` (both resolve a `FieldAccess`, unlike `FieldAsgn` whose `y : VarName` only
-- needs `resolveV_frameRoot` directly) -- previously two identical private copies.
theorem resolveFA_frameReach {cfg : RuntimeConfig} {y : FieldAccess} {oid : ObjectId}
    (hyf : resolveFA y cfg = some (Reference.OId oid)) :
    ∃ frameY : FrameWithIndex, frameY ∈ cfg.stackWithIndex ∧ FrameReferencable cfg frameY.index (Reference.OId oid) := by
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
        have hreachY0 : FrameReferencable cfg frameY.index (Reference.OId oid0) := by
          rw [FrameReferencable_iff_reflTransGen]
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
              exact ⟨frameY, hframeYMem, FrameReferencable.step hobjAt0 (List.contains_iff_mem.mpr
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
              exact ⟨frameY, hframeYMem, FrameReferencable.step hobjAt0 (List.contains_iff_mem.mpr
                (AList.mem_lookup_iff.mp (Option.mem_def.mpr hyf) |> (List.mem_map_of_mem (f := (·.2))) )
                ) hreachY0⟩
