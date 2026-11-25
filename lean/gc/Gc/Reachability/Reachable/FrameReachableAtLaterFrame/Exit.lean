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

-- For `oid` in a suspended frame's region, `exit` preserves frame-reachability from every surviving frame.
theorem exit_suspended_reach {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg) (h : exit cfg = some cfg')
    {F : FrameWithIndex} (hF : F ∈ cfg.stackWithIndex) (hFlt : F.index < cfg.stack.length - 1) {oid : ObjectId}
    (hloc' : (Reference.OId oid).loc? cfg' = some (Location.Rgn F.regionId)) :
    (Reference.OId oid).loc? cfg = some (Location.Rgn F.regionId) ∧
    ∀ X ∈ cfg.stackWithIndex, X.index < cfg.stack.length - 1 →
      (FrameReachable cfg X.index (.OId oid) ↔ FrameReachable cfg' X.index (.OId oid)) := by
  obtain ⟨p, r0, -, hlast, -, -, hcfg'⟩ := exit_cases h
  obtain ⟨region, hlookup, hopen⟩ := l2_of_stackWithIndex vcfg hF
  have hlookup' : cfg'.heap.lookup F.regionId = some region := by
    rw [hcfg']; dsimp only
    rw [AList.lookup_insert_ne (regionId_ne_last_of_suspended vcfg hF hFlt hlast)]; exact hlookup
  have hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn F.regionId) := by
    rw [oid_loc_rgn_iff_in_heap vcfg]
    rw [oid_loc_rgn_iff_in_heap (exit_valid vcfg h)] at hloc'
    obtain ⟨r1, hl1, hm1⟩ := hloc'
    rw [hlookup'] at hl1
    cases hl1
    exact ⟨region, hlookup, hm1⟩
  exact ⟨hloc, fun X hX hXlt => ⟨fun hr => exit_frame_reachable_transport vcfg h hlast hcfg' hlookup hopen hloc hX hXlt hr,
    fun hr => exit_frame_reachable_transport_backward vcfg h hlast hcfg' hlookup hlookup' hopen hloc'
      (exit_frame_mem_up h hX hXlt) hr⟩⟩

theorem frameReachableAtLaterFrame_step_exit :
    FrameReachableAtLaterFrame_step Stmt.exit := by
  intro cfg cfg' vcfg h hFR3 frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  have h' : exit cfg = some cfg' := h
  obtain ⟨hfm, hflt⟩ := exit_frame_mem_down h' hframeMem
  obtain ⟨hf'm, hf'lt⟩ := exit_frame_mem_down h' hframe'Mem
  obtain ⟨hloc_cfg, hiff⟩ := exit_suspended_reach vcfg h' hfm hflt hloc
  exact (hiff frame hfm hflt).mp (hFR3 frame hfm frame' hf'm hlt oid hloc_cfg ((hiff frame' hf'm hf'lt).mpr hreach))
