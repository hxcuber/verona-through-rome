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

-- For `oid` in an on-stack frame's region, `enter` preserves frame-reachability from every old frame and the fresh frame reaches nothing of it.
theorem enter_suspended_reach {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : enter xf a cfg = some cfg') {F : FrameWithIndex} (hF : F ∈ cfg.stackWithIndex) {oid : ObjectId}
    (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn F.regionId)) :
    (∀ G ∈ cfg.stackWithIndex, FrameReachable cfg G.index (.OId oid) ↔ FrameReachable cfg' G.index (.OId oid)) ∧
    ¬ FrameReachable cfg' cfg.stack.length (.OId oid) := by
  have vcfg' := enter_valid vcfg h
  obtain ⟨rid, regionEntered, -, hlookupRid, hclosedRid, hcfg'⟩ := enter_cases h
  obtain ⟨region, hlookup, hopen⟩ := l2_of_stackWithIndex vcfg hF
  have hne := enter_regionId_ne vcfg hF hlookupRid hclosedRid
  have hlk : ∀ X ∈ cfg.stackWithIndex, cfg'.heap.lookup X.regionId = cfg.heap.lookup X.regionId := fun X hX => by
    rw [hcfg']; dsimp only
    rw [AList.lookup_insert_ne (enter_regionId_ne vcfg hX hlookupRid hclosedRid)]
  have hlookup' : cfg'.heap.lookup F.regionId = some region := (hlk F hF).trans hlookup
  have hloc' : (Reference.OId oid).loc? cfg' = some (Location.Rgn F.regionId) := by
    rwa [← enter_corollary_2 vcfg h oid]
  have hroot : ∀ G ∈ cfg.stackWithIndex, ∀ s, FrameRoot cfg G.index s ↔ FrameRoot cfg' G.index s := by
    intro G hG s
    have hGlt : G.index < cfg.stack.length := by
      obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp hG
      exact hn
    constructor
    · rintro (⟨X, hX, hi, v, hv⟩ | ⟨X, hX, hi, r, hl, hb⟩)
      · exact .inl ⟨X, enter_frame_mem_up h hX, hi, v, hv⟩
      · exact .inr ⟨X, enter_frame_mem_up h hX, hi, r, (hlk X hX).trans hl, hb⟩
    · rintro (⟨X, hX, hi, v, hv⟩ | ⟨X, hX, hi, r, hl, hb⟩)
      · exact .inl ⟨X, enter_frame_mem_down h hX (hi ▸ hGlt), hi, v, hv⟩
      · have hX' := enter_frame_mem_down h hX (hi ▸ hGlt)
        exact .inr ⟨X, hX', hi, r, (hlk X hX').symm.trans hl, hb⟩
  refine ⟨fun G hG => ?_, fun hr => ?_⟩
  · simp only [FrameReachable_iff_reflTransGen]
    constructor
    · rintro ⟨s, hs, hc⟩
      exact ⟨s, (hroot G hG s).mp hs,
        safe_reflTransGen_transport vcfg hlookup hopen (enter_oid_step_iff vcfg h) hc (.inl hloc)⟩
    · rintro ⟨s, hs, hc⟩
      exact ⟨s, (hroot G hG s).mpr hs, safe_reflTransGen_transport vcfg' hlookup' hopen
        (fun o b => (enter_oid_step_iff vcfg h o b).symm) hc (.inl hloc')⟩
  · obtain ⟨s, hs, hc⟩ := (FrameReachable_iff_reflTransGen ..).mp hr
    have hbr : s = Reference.OId regionEntered.bridgeObjectId := by
      rcases hs with ⟨X, hX, hi, v, hv⟩ | ⟨X, hX, hi, r, hl, hb⟩ <;>
        rcases enter_frame_cases hcfg' hX with ⟨-, hlt⟩ | ⟨hrid, -, hvm, -, -⟩
      · exact absurd hi hlt.ne
      · simp [hvm] at hv
      · exact absurd hi hlt.ne
      · rw [hrid, hcfg'] at hl
        dsimp only at hl
        rw [AList.lookup_insert] at hl
        cases hl
        exact hb
    subst hbr
    have hbridgeLoc : (Reference.OId regionEntered.bridgeObjectId).loc? cfg' = some (Location.Rgn rid) := by
      rw [oid_loc_rgn_iff_in_heap vcfg']
      refine ⟨{ regionEntered with status := Status.Open }, ?_, vcfg.h1 regionEntered ?_⟩
      · rw [hcfg']; dsimp only; rw [AList.lookup_insert]
      · exact List.mem_map_of_mem (AList.lookup_mem_entries hlookupRid)
    have hsafe := safe_reflTransGen_root_safe vcfg' hlookup' hopen hc (.inl hloc')
    simp only [SafeRef] at hsafe
    rcases hsafe with hb | ⟨f, hb⟩
    · simp [hbridgeLoc] at hb
      exact hne hb.symm
    · simp [hbridgeLoc] at hb

theorem frameReachableAtLaterFrame_step_enter (xf : FieldAccess) (bridgeVar : VarName) :
    FrameReachableAtLaterFrame_step (Stmt.enter xf bridgeVar) := by
  intro cfg cfg' vcfg h hFR3 frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  have h' : enter xf bridgeVar cfg = some cfg' := h
  obtain ⟨_, _, -, -, -, hcfg'⟩ := enter_cases h'
  obtain ⟨hfm, hflt⟩ : frame ∈ cfg.stackWithIndex ∧ frame.index < cfg.stack.length := by
    rcases enter_frame_cases hcfg' hframeMem with hh | ⟨-, -, -, -, hidx⟩
    · exact hh
    · exfalso
      rcases enter_frame_cases hcfg' hframe'Mem with ⟨-, h2⟩ | ⟨-, -, -, -, h2⟩ <;> grind
  have hloc_cfg : (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) := by
    rwa [enter_corollary_2 vcfg h' oid]
  obtain ⟨hiff, hnew⟩ := enter_suspended_reach vcfg h' hfm hloc_cfg
  rcases enter_frame_cases hcfg' hframe'Mem with ⟨hf'm, -⟩ | ⟨-, -, -, -, hidx'⟩
  · exact (hiff frame hfm).mp (hFR3 frame hfm frame' hf'm hlt oid hloc_cfg ((hiff frame' hf'm).mpr hreach))
  · exact absurd (hidx' ▸ hreach) hnew
