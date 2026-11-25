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

theorem frameReachableAtLaterFrame_step_merge (x : VarName) :
    FrameReachableAtLaterFrame_step (Stmt.merge x) := by
  intro cfg cfg' vcfg h hFR3 frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  have h' : merge x cfg = some cfg' := h
  have hfr := index_lt_length_sub_one (merge_length h') hframe'Mem hlt
  have hfr' : frame.index < cfg.stack.length - 1 := by simpa [RuntimeConfig.stackWithIndex] using hfr
  obtain ⟨A, rid', region1, region', hA, hxref, hregion1, hregion', hclosed, hopen, hcfg'⟩ := merge_cases h'
  have hF := merge_frame_transport_down hA hxref hregion1 hregion' hclosed hopen hcfg' hframeMem (by simpa using hfr')
  rw [oid_loc_rgn_iff_in_heap (merge_valid vcfg h'), hcfg'] at hloc
  simp only [AList.lookup_insert_ne (regionId_ne_last_of_suspended vcfg hF hfr' hA),
    AList.lookup_erase_ne (closed_region_not_owned vcfg hregion' hclosed hF ·)] at hloc
  have hsr := merge_suspended_reach vcfg h' hFR3 hF hfr ((oid_loc_rgn_iff_in_heap vcfg).mpr hloc)
  exact hsr.2.1 (hsr.2.2 _ hreach)
