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

-- A `R'`-chain, where `R'` only adds the edge `x → y` to `R`, is an `R`-chain or ends in an `R`-chain from `y`.
private theorem reflTransGen_split {α : Type*} {R R' : α → α → Prop} {x y : α}
    (hne : ∀ a, a ≠ x → ∀ b, R' a b → R a b) (hx : ∀ c, R' x c → c = y ∨ R x c)
    {a b : α} (h : Relation.ReflTransGen R' a b) :
    Relation.ReflTransGen R a b ∨ Relation.ReflTransGen R y b := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .inl .refl
  | @head p c hstep _ ih =>
    rcases ih with ih | ih
    · by_cases hp : p = x
      · subst hp
        rcases hx c hstep with rfl | hs
        · exact .inr ih
        · exact .inl (.head hs ih)
      · exact .inl (.head (hne p hp c hstep) ih)
    · exact .inr ih

-- fieldAsgn preserves the stack length, every object's `loc?`, and every frame below the active one.
private theorem fieldAsgn_shape {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : fieldAsgn xf y cfg = some cfg') :
    cfg'.stackWithIndex.length = cfg.stackWithIndex.length ∧
    (∀ o, (Reference.OId o).loc? cfg' = (Reference.OId o).loc? cfg) ∧
    ∀ X : FrameWithIndex, X.index < cfg.stackWithIndex.length - 1 →
      (X ∈ cfg.stackWithIndex ↔ X ∈ cfg'.stackWithIndex) := by
  have hmem := fun X (hX : X.index < cfg.stackWithIndex.length - 1) => fieldAsgn_frame_mem_iff h
    (X := X) (activeIdx := cfg.stack.dropLast.length) (by simpa [RuntimeConfig.stackWithIndex] using hX) rfl
  obtain ⟨A, hA, ⟨_, _, _, _, _, _, hobj, rfl⟩ | ⟨_, _, _, _, _, _, _, _, hregion, hobj, _, _, _, rfl⟩⟩ :=
    fieldAsgn_cases h
  · refine ⟨?_, fun o => (fieldAsgn_corollary_stack_loc_eq hA hobj o).symm, hmem⟩
    have := congrArg List.length (stack_eq_of_stackWithIndex_getLast? hA).1
    simp [RuntimeConfig.stackWithIndex] at this ⊢
    omega
  · exact ⟨rfl, fun o => (fieldAsgn_corollary_region_loc_eq vcfg hregion hobj o).symm, hmem⟩

-- For `oid` in a suspended frame `F`'s region, fieldAsgn neither creates nor destroys its reachability from `F`.
theorem fieldAsgn_suspended_reach {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : fieldAsgn xf y cfg = some cfg') (hFR3 : FrameReachable_at_later_frame_implies_FrameReachable_at_frame cfg)
    {F : FrameWithIndex} (hF : F ∈ cfg.stackWithIndex) (hFlt : F.index < cfg.stackWithIndex.length - 1)
    {oid : ObjectId} (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn F.regionId)) :
    F ∈ cfg'.stackWithIndex ∧ (StackReachable cfg (.OId oid) → FrameReachable cfg' F.index (.OId oid)) ∧
    ∀ fid, FrameReachable cfg' fid (.OId oid) → StackReachable cfg (.OId oid) := by
  obtain ⟨oidC, hxrC, hne⟩ := fieldAsgn_step_iff_of_ne vcfg h
  have hroot := fieldAsgn_frame_root_iff h
  obtain ⟨regionF, hlkF, hopenF⟩ := l2_of_stackWithIndex vcfg hF
  obtain ⟨A, hA, hcase⟩ := fieldAsgn_cases h
  have hAmem := List.mem_of_getLast? hA
  have hFA : F.index < A.index := by
    have := (stack_eq_of_stackWithIndex_getLast? hA).2
    simp [RuntimeConfig.stackWithIndex] at hFlt
    rw [this, List.length_dropLast]
    omega
  obtain ⟨hbound, oid_y, hstepC, hesc⟩ : (∀ fid, FrameReachable cfg fid (.OId oidC) → A.index ≤ fid) ∧
      ∃ oid_y, (∀ c, ReachableStep cfg' (.OId oidC) c → c = .OId oid_y ∨ ReachableStep cfg (.OId oidC) c) ∧
      (Relation.ReflTransGen (ReachableStep cfg) (.OId oid_y) (.OId oid) → StackReachable cfg (.OId oid)) := by
    rcases hcase with ⟨oid0, oid_y, obj, hxr0, hyr, hlocC, hobj, hcfg'⟩ |
        ⟨oid0, oid_y, rid, region, obj, hxr0, hyr, hlocC, hregion, hobj, hyloc, hstatus, hfrid, hcfg'⟩
    · obtain rfl : oidC = oid0 := by simpa using hxrC.symm.trans hxr0
      refine ⟨fun _ => stack_container_confined vcfg hlocC, oid_y,
        fun _ => fieldAsgn_stack_oidC_step_of_ne_oidY hA hlocC hobj hcfg', fun hc => ?_⟩
      obtain ⟨Y, hY, hrootY⟩ := resolveV_frameRoot hyr
      exact ⟨Y, hY, (FrameReachable_iff_reflTransGen ..).mpr ⟨_, hrootY, hc⟩⟩
    · obtain rfl : oidC = oid0 := by simpa using hxrC.symm.trans hxr0
      refine ⟨fun _ => region_container_confined vcfg hregion hstatus hAmem hfrid.symm hlocC, oid_y,
        fun _ => fieldAsgn_region_oidC_step_of_ne_oidY vcfg hregion hlocC hobj hcfg', fun hc => ?_⟩
      exact (reflTransGen_region_open_ne_absurd vcfg hregion hyloc hloc hlkF hopenF (fun he => Nat.ne_of_lt hFA
        (merge_corollary_regionId_unique_index vcfg.s1 hF hAmem (he.trans hfrid))) hc).elim
  refine ⟨((fieldAsgn_shape vcfg h).2.2 F hFlt).mp hF, fun ⟨E, hE, hr⟩ => ?_, fun fid hr => ?_⟩
  · refine fieldAsgn_confined_transport hne hroot (fun r hr he => absurd (hbound _ (he ▸ hr)) (Nat.not_le.mpr hFA)) ?_
    rcases (region_container_confined vcfg hlkF hopenF hF rfl hloc hr).eq_or_lt with heq | hlt
    · exact swap_corollary_stackWithIndex_index_inj hE hF heq.symm ▸ hr
    · exact hFR3 F hF E hE hlt oid hloc hr
  · obtain ⟨start, hs, hc⟩ := (FrameReachable_iff_reflTransGen ..).mp hr
    rcases reflTransGen_split (fun a ha b => (hne a ha b).mpr) hstepC hc with hc | hc
    · have hrc := (hroot fid start).mpr hs
      have hfr : FrameReachable cfg fid (.OId oid) := (FrameReachable_iff_reflTransGen ..).mpr ⟨start, hrc, hc⟩
      rcases hrc with ⟨S, hS, rfl, -⟩ | ⟨S, hS, rfl, -⟩ <;> exact ⟨S, hS, hfr⟩
    · exact hesc hc

theorem frameReachableAtLaterFrame_step_fieldAsgn (xf : FieldAccess) (y : VarName) :
    FrameReachableAtLaterFrame_step (Stmt.fieldAsgn xf y) := by
  intro cfg cfg' vcfg h hFR3 frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  have h' : fieldAsgn xf y cfg = some cfg' := h
  obtain ⟨hlen, hlocEq, hmemIff⟩ := fieldAsgn_shape vcfg h'
  have hfr : frame.index < cfg.stackWithIndex.length - 1 := Nat.lt_sub_of_add_lt (lt_of_le_of_lt hlt
    (hlen ▸ (List.getElem?_eq_some_iff.mp (stackWithIndex_mem_getElem_eq hframe'Mem)).1))
  rw [hlocEq] at hloc
  have hsr := fieldAsgn_suspended_reach vcfg h' hFR3 ((hmemIff frame hfr).mpr hframeMem) hfr hloc
  exact hsr.2.1 (hsr.2.2 _ hreach)
