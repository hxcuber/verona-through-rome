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

-- varAsgn preserves the stack length.
private theorem varAsgn_length {cfg cfg' : RuntimeConfig} (h : varAsgn xf y cfg = some cfg') :
    cfg'.stackWithIndex.length = cfg.stackWithIndex.length := by
  obtain ⟨A, hA, ⟨-, -, -, -, -, -, -, -, rfl⟩ | ⟨-, -, -, -, rfl⟩⟩ := varAsgn_cases h
  · rfl
  · have := congrArg List.length (List.dropLast_append_getLast? A hA)
    simp [RuntimeConfig.stackWithIndex] at this ⊢
    omega

-- Every root after varAsgn is stack-reachable before it: the only new root value is `y`'s resolved object.
private theorem varAsgn_root_reach {cfg cfg' : RuntimeConfig} (h : varAsgn xf y cfg = some cfg')
    {fid : Index} {start : Reference} (hs : FrameRoot cfg' fid start) : StackReachable cfg start := by
  have hR : ∀ fid, FrameRoot cfg fid start → StackReachable cfg start := fun fid hr => by
    rcases id hr with ⟨S, hS, rfl, -⟩ | ⟨S, hS, rfl, -⟩ <;>
      exact ⟨S, hS, (FrameReachable_iff_reflTransGen ..).mpr ⟨_, hr, .refl⟩⟩
  obtain ⟨A, hA, ⟨oidY, rid, region, hyf, -, -, rfl, hregion, rfl⟩ | ⟨oidY, hyf, -, -, rfl⟩⟩ := varAsgn_cases h
  · rcases hs with ⟨f, hf, rfl, v, hv⟩ | ⟨f, hf, rfl, r, hr, rfl⟩
    · exact hR _ (.inl ⟨f, hf, rfl, v, hv⟩)
    · by_cases he : f.regionId = A.regionId
      · rw [he, AList.lookup_insert] at hr
        obtain rfl := Option.some.inj hr
        exact resolveFA_frameReach hyf
      · exact hR _ (.inr ⟨f, hf, rfl, r, by simpa [AList.lookup_insert_ne he] using hr, rfl⟩)
  · have hsw := stackWithIndex_eq_of_getLast? hA
    have hlastA : ({ A with index := cfg.stack.dropLast.length } : FrameWithIndex) ∈ cfg.stackWithIndex := by
      simp [hsw]
    rw [FrameRoot, stackWithIndex_mk_append_singleton] at hs
    rcases hs with ⟨f, hf, rfl, v, hv⟩ | ⟨f, hf, rfl, r, hr, rfl⟩ <;>
      rcases List.mem_append.mp hf with hf | hf
    · exact hR _ (.inl ⟨f, hsw ▸ List.mem_append_left _ hf, rfl, v, hv⟩)
    · obtain rfl := List.mem_singleton.mp hf
      by_cases hv' : v = xf
      · subst hv'
        simp at hv
        exact hv ▸ resolveFA_frameReach hyf
      · exact hR _ (.inl ⟨_, hlastA, rfl, v, by simpa [AList.lookup_insert_ne hv'] using hv⟩)
    · exact hR _ (.inr ⟨f, hsw ▸ List.mem_append_left _ hf, rfl, r, hr, rfl⟩)
    · obtain rfl := List.mem_singleton.mp hf
      exact hR _ (.inr ⟨_, hlastA, rfl, r, hr, rfl⟩)

-- For `oid` in a suspended frame `F`'s region, varAsgn neither creates nor destroys its reachability from `F`.
theorem varAsgn_suspended_reach {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : varAsgn xf y cfg = some cfg') (hFR3 : FrameReachable_at_later_frame_implies_FrameReachable_at_frame cfg)
    {F : FrameWithIndex} (hF : F ∈ cfg.stackWithIndex) (hFlt : F.index < cfg.stackWithIndex.length - 1)
    {oid : ObjectId} (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn F.regionId)) :
    F ∈ cfg'.stackWithIndex ∧ (StackReachable cfg (.OId oid) → FrameReachable cfg' F.index (.OId oid)) ∧
    ∀ fid, FrameReachable cfg' fid (.OId oid) → StackReachable cfg (.OId oid) := by
  have hFlt' : F.index < cfg.stack.length - 1 := by simpa [RuntimeConfig.stackWithIndex] using hFlt
  obtain ⟨regionF, hlkF, hopenF⟩ := l2_of_stackWithIndex vcfg hF
  refine ⟨(varAsgn_frame_mem_iff h hFlt').mp hF,
    fun ⟨E, hE, hr⟩ => (varAsgn_frame_reachable_iff vcfg h hF hFlt' _).mp ?_, fun fid hr => ?_⟩
  · rcases (region_container_confined vcfg hlkF hopenF hF rfl hloc hr).eq_or_lt with heq | hlt
    · exact swap_corollary_stackWithIndex_index_inj hE hF heq.symm ▸ hr
    · exact hFR3 F hF E hE hlt oid hloc hr
  · obtain ⟨start, hs, hc⟩ := (FrameReachable_iff_reflTransGen ..).mp hr
    obtain ⟨S, hS, hSr⟩ := varAsgn_root_reach h hs
    exact ⟨S, hS, FrameReachable_extend hSr (varAsgn_step_eq vcfg h ▸ hc)⟩

theorem frameReachableAtLaterFrame_step_varAsgn (x : VarName) (yf : FieldAccess) :
    FrameReachableAtLaterFrame_step (Stmt.varAsgn x yf) := by
  intro cfg cfg' vcfg h hFR3 frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  have h' : varAsgn x yf cfg = some cfg' := h
  have hfr : frame.index < cfg.stackWithIndex.length - 1 := Nat.lt_sub_of_add_lt (lt_of_le_of_lt hlt
    (varAsgn_length h' ▸ (List.getElem?_eq_some_iff.mp (stackWithIndex_mem_getElem_eq hframe'Mem)).1))
  rw [← varAsgn_corollary_loc_eq vcfg h'] at hloc
  have hsr := varAsgn_suspended_reach vcfg h' hFR3
    ((varAsgn_frame_mem_iff h' (by simpa [RuntimeConfig.stackWithIndex] using hfr)).mpr hframeMem) hfr hloc
  exact hsr.2.1 (hsr.2.2 _ hreach)
