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

-- merge preserves the stack length.
private theorem merge_length {cfg cfg' : RuntimeConfig} (h : merge x cfg = some cfg') :
    cfg'.stackWithIndex.length = cfg.stackWithIndex.length := by
  obtain ⟨A, -, -, -, hA, -, -, -, -, -, rfl⟩ := merge_cases h
  have := congrArg List.length (List.dropLast_append_getLast? A hA)
  simp [RuntimeConfig.stackWithIndex] at this ⊢
  omega

-- Anything reachable after merge is stack-reachable before it: only the merged frame's roots change, and `x`'s new value is one hop past `RId rid'`.
private theorem merge_reach_down {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg) (h : merge x cfg = some cfg')
    {fid : Index} {oid : ObjectId} (hfr : FrameReachable cfg' fid (.OId oid)) : StackReachable cfg (.OId oid) := by
  obtain ⟨start, hs, hc⟩ := (FrameReachable_iff_reflTransGen ..).mp hfr
  obtain ⟨A, rid', region1, region', hA, hxref, hregion1, hregion', hclosed, hopen, hcfg'⟩ := merge_cases h
  have hsw := stackWithIndex_eq_of_getLast? hA
  have hlastA : ({ A with index := cfg.stack.dropLast.length } : FrameWithIndex) ∈ cfg.stackWithIndex := by
    simp [hsw]
  have hdown := fun hne => merge_chain_transport_down vcfg h hA hxref hregion1 hregion' hclosed hopen hcfg' hne hc
  have hfin : ∀ s, FrameRoot cfg cfg.stack.dropLast.length s → Relation.ReflTransGen (ReachableStep cfg) s (.OId oid) →
      StackReachable cfg (.OId oid) := fun s hs hc => ⟨_, hlastA, (FrameReachable_iff_reflTransGen ..).mpr ⟨s, hs, hc⟩⟩
  have hleft : ∀ G ∈ cfg.stack.dropLast.mapIdx (fun i f => ({ f with index := i } : FrameWithIndex)),
      FrameReachable cfg' G.index (.OId oid) → StackReachable cfg (.OId oid) := fun G hG hr => by
    have hGc : G ∈ cfg.stackWithIndex := hsw ▸ List.mem_append_left _ hG
    obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp hG
    exact ⟨_, hGc, (merge_frame_reachable_iff vcfg h hGc (by simp at hn ⊢; omega) _).mpr hr⟩
  rw [hcfg'] at hs
  rcases hs with ⟨G, hG, rfl, v, hv⟩ | ⟨G, hG, rfl, r, hr, rfl⟩ <;>
    rw [stackWithIndex_mk_append_singleton] at hG <;> rcases List.mem_append.mp hG with hG | hG
  · exact hleft G hG hfr
  · obtain rfl := List.mem_singleton.mp hG
    by_cases hvx : v = x
    · subst hvx
      simp only [AList.lookup_insert, Option.some.injEq] at hv
      subst hv
      exact hfin _ (.inl ⟨_, hlastA, rfl, _, hxref⟩) (.head ⟨region', hregion', hclosed, rfl⟩ (hdown (by simp)))
    · rw [AList.lookup_insert_ne hvx] at hv
      exact hfin _ (.inl ⟨_, hlastA, rfl, v, hv⟩)
        (hdown fun he => merge_ridPrime_var_unique vcfg (List.mem_of_getLast? hA) hxref hvx (he ▸ hv))
  · exact hleft G hG hfr
  · obtain rfl := List.mem_singleton.mp hG
    simp only [AList.lookup_insert, Option.some.injEq] at hr
    subst hr
    exact hfin _ (.inr ⟨_, hlastA, rfl, region1, hregion1, rfl⟩) (hdown (by simp))

-- For `oid` in a suspended frame `F`'s region, merge neither creates nor destroys its reachability from `F`.
theorem merge_suspended_reach {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : merge x cfg = some cfg') (hFR3 : FrameReachable_at_later_frame_implies_FrameReachable_at_frame cfg)
    {F : FrameWithIndex} (hF : F ∈ cfg.stackWithIndex) (hFlt : F.index < cfg.stackWithIndex.length - 1)
    {oid : ObjectId} (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn F.regionId)) :
    F ∈ cfg'.stackWithIndex ∧ (StackReachable cfg (.OId oid) → FrameReachable cfg' F.index (.OId oid)) ∧
    ∀ fid, FrameReachable cfg' fid (.OId oid) → StackReachable cfg (.OId oid) := by
  have hFlt' : F.index < cfg.stack.length - 1 := by simpa [RuntimeConfig.stackWithIndex] using hFlt
  obtain ⟨regionF, hlkF, hopenF⟩ := l2_of_stackWithIndex vcfg hF
  obtain ⟨A, rid', region1, region', hA, hxref, hregion1, hregion', hclosed, hopen, hcfg'⟩ := merge_cases h
  refine ⟨merge_frame_transport_up hA hxref hregion1 hregion' hclosed hopen hcfg' hF (by simpa using hFlt'),
    fun ⟨E, hE, hr⟩ => (merge_frame_reachable_iff vcfg h hF hFlt' _).mp ?_, fun _ => merge_reach_down vcfg h⟩
  rcases (region_container_confined vcfg hlkF hopenF hF rfl hloc hr).eq_or_lt with heq | hlt
  · exact swap_corollary_stackWithIndex_index_inj hE hF heq.symm ▸ hr
  · exact hFR3 F hF E hE hlt oid hloc hr

theorem frameReachableAtLaterFrame_step_merge (x : VarName) :
    FrameReachableAtLaterFrame_step (Stmt.merge x) := by
  intro cfg cfg' vcfg h hFR3 frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  have h' : merge x cfg = some cfg' := h
  have hfr : frame.index < cfg.stackWithIndex.length - 1 := Nat.lt_sub_of_add_lt (lt_of_le_of_lt hlt
    (merge_length h' ▸ (List.getElem?_eq_some_iff.mp (stackWithIndex_mem_getElem_eq hframe'Mem)).1))
  have hfr' : frame.index < cfg.stack.length - 1 := by simpa [RuntimeConfig.stackWithIndex] using hfr
  obtain ⟨A, rid', region1, region', hA, hxref, hregion1, hregion', hclosed, hopen, hcfg'⟩ := merge_cases h'
  have hF := merge_frame_transport_down hA hxref hregion1 hregion' hclosed hopen hcfg' hframeMem (by simpa using hfr')
  rw [oid_loc_rgn_iff_in_heap (merge_valid vcfg h'), hcfg'] at hloc
  simp only [AList.lookup_insert_ne (regionId_ne_last_of_suspended vcfg hF hfr' hA),
    AList.lookup_erase_ne (closed_region_not_owned vcfg hregion' hclosed hF ·)] at hloc
  have hsr := merge_suspended_reach vcfg h' hFR3 hF hfr ((oid_loc_rgn_iff_in_heap vcfg).mpr hloc)
  exact hsr.2.1 (hsr.2.2 _ hreach)
