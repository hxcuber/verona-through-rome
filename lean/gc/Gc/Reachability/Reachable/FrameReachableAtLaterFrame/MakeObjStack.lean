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

-- A `cfg'` frame root is either the fresh object (via `x`) or already a `cfg` root.
private theorem makeObjStack_root_down {cfg cfg' : RuntimeConfig} (h : makeObjStack x cfg = some cfg')
    {fid : Index} {start : Reference} (hr : FrameRoot cfg' fid start) :
    start = .OId cfg.freshObjectId ∨ FrameRoot cfg fid start := by
  obtain ⟨L, hL, rfl⟩ := makeObjStack_cases h
  have hLm := stackWithIndex_getLast_mem hL
  rcases hr with ⟨S, hS, rfl, v, hv⟩ | ⟨S, hS, rfl, region, hl, rfl⟩ <;>
    rcases makeObjStack_frame_cases hL rfl hS with ⟨hS, -⟩ | ⟨hrid, -, hvm, -, hi⟩
  · exact .inr (.inl ⟨S, hS, rfl, v, hv⟩)
  · rw [hvm] at hv
    by_cases hvx : v = x
    · subst hvx
      simp at hv
      exact .inl hv.symm
    · rw [AList.lookup_insert_ne hvx] at hv
      exact .inr (.inl ⟨_, hLm, by simp [hi], v, hv⟩)
  · exact .inr (.inr ⟨S, hS, rfl, region, hl, rfl⟩)
  · exact .inr (.inr ⟨_, hLm, by simp [hi], region, hrid ▸ hl, rfl⟩)

-- Reachability of a non-fresh object from any `cfg'` frame already holds in `cfg` from a frame at that index.
private theorem makeObjStack_reach_down {cfg cfg' : RuntimeConfig} (h : makeObjStack x cfg = some cfg')
    {oid : ObjectId} (hne : oid ≠ cfg.freshObjectId) {fid : Index} (hr : FrameReachable cfg' fid (.OId oid)) :
    ∃ S ∈ cfg.stackWithIndex, S.index = fid ∧ FrameReachable cfg fid (.OId oid) := by
  obtain ⟨start, hs, hc⟩ := (FrameReachable_iff_reflTransGen ..).mp hr
  rw [← makeObjStack_step_eq h] at hc
  rcases makeObjStack_root_down h hs with rfl | hs
  · rcases hc.cases_head with he | ⟨c, ⟨obj, ho, -⟩, -⟩
    · exact absurd (Reference.OId.inj he).symm hne
    · simp [freshObjectId_objAt_none] at ho
  · have hfr := (FrameReachable_iff_reflTransGen ..).mpr ⟨start, hs, hc⟩
    rcases hs with ⟨S, hS, rfl, -⟩ | ⟨S, hS, rfl, -⟩ <;> exact ⟨S, hS, rfl, hfr⟩

-- For `oid` in a suspended frame `F`'s region, makeObjStack neither creates nor destroys its reachability from `F`.
theorem makeObjStack_suspended_reach {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeObjStack x cfg = some cfg') (hFR3 : FrameReachable_at_later_frame_implies_FrameReachable_at_frame cfg)
    {F : FrameWithIndex} (hF : F ∈ cfg.stackWithIndex) (hFlt : F.index < cfg.stackWithIndex.length - 1)
    {oid : ObjectId} (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn F.regionId)) :
    F ∈ cfg'.stackWithIndex ∧ (StackReachable cfg (.OId oid) → FrameReachable cfg' F.index (.OId oid)) ∧
    ∀ fid, FrameReachable cfg' fid (.OId oid) → StackReachable cfg (.OId oid) := by
  have hFlt' : F.index < cfg.stack.length - 1 := by simpa [RuntimeConfig.stackWithIndex] using hFlt
  obtain ⟨regionF, hlkF, hopenF⟩ := l2_of_stackWithIndex vcfg hF
  refine ⟨makeObjStack_frame_mem_up h hF hFlt',
    fun ⟨E, hE, hr⟩ => (makeObjStack_frame_reachable_iff h hF hFlt' _).mp ?_, fun fid hr => ?_⟩
  · rcases (region_container_confined vcfg hlkF hopenF hF rfl hloc hr).eq_or_lt with heq | hlt
    · exact swap_corollary_stackWithIndex_index_inj hE hF heq.symm ▸ hr
    · exact hFR3 F hF E hE hlt oid hloc hr
  · obtain ⟨S, hS, rfl, hr⟩ := makeObjStack_reach_down h (fun he => freshObjectId_loc_ne_rgn (he ▸ hloc)) hr
    exact ⟨S, hS, hr⟩

theorem frameReachableAtLaterFrame_step_makeObjStack (x : VarName) :
    FrameReachableAtLaterFrame_step (Stmt.makeObjStack x) := by
  intro cfg cfg' vcfg h hFR3 frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  have h' : makeObjStack x cfg = some cfg' := h
  obtain ⟨L, hL, hcfg'⟩ := makeObjStack_cases h'
  have hle : frame'.index ≤ cfg.stack.length - 1 := by
    rcases makeObjStack_frame_cases hL hcfg' hframe'Mem with ⟨-, h1⟩ | ⟨-, -, -, -, h1⟩
    · exact h1.le
    · simp [h1]
  obtain ⟨hF, hFlt⟩ := (makeObjStack_frame_cases hL hcfg' hframeMem).resolve_right
    fun ⟨_, _, _, _, h1⟩ => by simp at h1; exact absurd hle (Nat.not_le.mpr (h1 ▸ hlt))
  have hne : oid ≠ cfg.freshObjectId := by
    rintro rfl
    obtain ⟨r, hl, hm⟩ := (oid_loc_rgn_iff_in_heap (makeObjStack_valid vcfg h')).mp hloc
    subst hcfg'
    exact cfg.freshObjectId_not_mem (List.mem_append_right _ (heap_objectIds_of_mem (AList.lookup_mem_entries hl) hm))
  rw [← makeObjStack_loc_eq_of_ne h' hne] at hloc
  have hsr := makeObjStack_suspended_reach vcfg h' hFR3 hF (by simpa [RuntimeConfig.stackWithIndex] using hFlt) hloc
  exact hsr.2.1 (hsr.2.2 _ hreach)
