module

public import Gc.Model.Types
public import Gc.Model.Helpers
public import Gc.Model.Validity
public import Gc.Model.Mutation.Mutation
public import Gc.Model.Mutation.Stmt
public import Gc.Model.Preservation
public import Gc.Reachability.Reachable.Semantics
public import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.Def
public import Gc.Reachability.Reachable.Lemmas

@[expose] public section

-- An on-stack frame's region is never the fresh region id.
private theorem frame_regionId_ne_fresh {cfg : RuntimeConfig} (vcfg : ValidConfig cfg) {S : FrameWithIndex}
    (hS : S ∈ cfg.stackWithIndex) : S.regionId ≠ cfg.freshRegionId := fun he => by
  obtain ⟨_, hl, -⟩ := l2_of_stackWithIndex vcfg hS
  exact cfg.freshRegionId_not_mem (he ▸ AList.mem_keys_of_lookup_eq_some hl)

-- A `cfg'` frame root is either the fresh region (via `x`) or already a `cfg` root.
private theorem makeRegion_root_down {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeRegion x cfg = some cfg') {fid : Index} {start : Reference} (hr : FrameRoot cfg' fid start) :
    start = .RId cfg.freshRegionId ∨ FrameRoot cfg fid start := by
  have hcases := fun {S} (hS : S ∈ cfg'.stackWithIndex) => makeRegion_frame_cases h hS
  obtain ⟨L, hL, rfl⟩ := makeRegion_cases h
  have hLm := stackWithIndex_getLast_mem hL
  rcases hr with ⟨S, hS, rfl, v, hv⟩ | ⟨S, hS, rfl, region, hl, rfl⟩ <;>
    rcases hcases hS with ⟨hS, -⟩ | ⟨L', hL', hrid, -, -, hvm, hi⟩
  · exact .inr (.inl ⟨S, hS, rfl, v, hv⟩)
  · obtain rfl : L' = L := Option.some_inj.mp (hL'.symm.trans hL)
    rw [hvm] at hv
    by_cases hvx : v = x
    · subst hvx
      simp at hv
      exact .inl hv.symm
    · rw [AList.lookup_insert_ne hvx] at hv
      exact .inr (.inl ⟨_, hLm, by simp [hi], v, hv⟩)
  · rw [AList.lookup_insert_ne (frame_regionId_ne_fresh vcfg hS)] at hl
    exact .inr (.inr ⟨S, hS, rfl, region, hl, rfl⟩)
  · obtain rfl : L' = L := Option.some_inj.mp (hL'.symm.trans hL)
    rw [hrid, AList.lookup_insert_ne (frame_regionId_ne_fresh vcfg hLm)] at hl
    exact .inr (.inr ⟨_, hLm, by simp [hi], region, hl, rfl⟩)

-- Reachability of a non-fresh object from any `cfg'` frame already holds in `cfg` from a frame at that index.
private theorem makeRegion_reach_down {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeRegion x cfg = some cfg') {oid : ObjectId} (hne : oid ≠ cfg.freshObjectId) {fid : Index}
    (hr : FrameReachable cfg' fid (.OId oid)) :
    ∃ S ∈ cfg.stackWithIndex, S.index = fid ∧ FrameReachable cfg fid (.OId oid) := by
  obtain ⟨start, hs, hc⟩ := (FrameReachable_iff_reflTransGen ..).mp hr
  rcases makeRegion_root_down vcfg h hs with rfl | hs
  · rcases hc.cases_head with he | ⟨c, ⟨region, hl, -, rfl⟩, hc⟩
    · cases he
    obtain ⟨L, hL, hcfg'⟩ := makeRegion_cases h
    rw [hcfg', AList.lookup_insert, Option.some_inj] at hl
    subst hl
    rcases hc.cases_head with he | ⟨c, ⟨obj, ho, hco⟩, -⟩
    · exact absurd (Reference.OId.inj he).symm hne
    · rw [makeRegion_fresh_objAt_cfg' h, Option.some_inj] at ho
      subst ho
      simp [Object.refs] at hco
  · have hsne : start ≠ .RId cfg.freshRegionId := by
      rintro rfl
      rcases hs with ⟨S, hS, -, v, hv⟩ | ⟨_, _, _, _, _, ⟨⟩⟩
      exact cfg.freshRegionId_not_mem (vcfg.hs2 _ (refs_mem_of_stackWithIndex hS (mem_frame_refs_of_mem_varMap hv)))
    have hfr := (FrameReachable_iff_reflTransGen ..).mpr
      ⟨start, hs, (makeRegion_reflTransGen_transport_down vcfg h hsne hc).2⟩
    rcases hs with ⟨S, hS, rfl, -⟩ | ⟨S, hS, rfl, -⟩ <;> exact ⟨S, hS, rfl, hfr⟩

-- For `oid` in a suspended frame `F`'s region, makeRegion neither creates nor destroys its reachability from `F`.
theorem makeRegion_suspended_reach {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeRegion x cfg = some cfg') (hFR3 : FrameReachable_at_later_frame_implies_FrameReachable_at_frame cfg)
    {F : FrameWithIndex} (hF : F ∈ cfg.stackWithIndex) (hFlt : F.index < cfg.stackWithIndex.length - 1)
    {oid : ObjectId} (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn F.regionId)) :
    F ∈ cfg'.stackWithIndex ∧ (StackReachable cfg (.OId oid) → FrameReachable cfg' F.index (.OId oid)) ∧
    ∀ fid, FrameReachable cfg' fid (.OId oid) → StackReachable cfg (.OId oid) := by
  have hFlt' : F.index < cfg.stack.length - 1 := by simpa [RuntimeConfig.stackWithIndex] using hFlt
  obtain ⟨regionF, hlkF, hopenF⟩ := l2_of_stackWithIndex vcfg hF
  refine ⟨makeRegion_frame_mem_up h hF hFlt',
    fun ⟨E, hE, hr⟩ => (makeRegion_frame_reachable_iff vcfg h hF hFlt' _).mp ?_, fun fid hr => ?_⟩
  · rcases (region_container_confined vcfg hlkF hopenF hF rfl hloc hr).eq_or_lt with heq | hlt
    · exact swap_corollary_stackWithIndex_index_inj hE hF heq.symm ▸ hr
    · exact hFR3 F hF E hE hlt oid hloc hr
  · obtain ⟨S, hS, rfl, hr⟩ :=
      makeRegion_reach_down vcfg h (fun he => freshObjectId_loc_ne_rgn (he ▸ hloc)) hr
    exact ⟨S, hS, hr⟩

theorem frameReachableAtLaterFrame_step_makeRegion (x : VarName) :
    FrameReachableAtLaterFrame_step (Stmt.makeRegion x) := by
  intro cfg cfg' vcfg h hFR3 frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  have h' : makeRegion x cfg = some cfg' := h
  have hle : frame'.index ≤ cfg.stack.length - 1 := by
    rcases makeRegion_frame_cases h' hframe'Mem with ⟨-, h1⟩ | ⟨-, -, -, -, -, -, h1⟩
    · exact h1.le
    · simp [h1]
  obtain ⟨hF, hFlt⟩ := (makeRegion_frame_cases h' hframeMem).resolve_right
    fun ⟨_, _, _, _, _, _, h1⟩ => by simp at h1; exact absurd hle (Nat.not_le.mpr (h1 ▸ hlt))
  have hne : oid ≠ cfg.freshObjectId := by
    rintro rfl
    simp only [makeRegion_corollary_loc_fresh h', Option.some_inj, Location.Rgn.injEq] at hloc
    exact frame_regionId_ne_fresh vcfg hF hloc.symm
  rw [← makeRegion_corollary_loc_eq vcfg h' oid hne] at hloc
  have hsr := makeRegion_suspended_reach vcfg h' hFR3 hF (by simpa [RuntimeConfig.stackWithIndex] using hFlt) hloc
  exact hsr.2.1 (hsr.2.2 _ hreach)
