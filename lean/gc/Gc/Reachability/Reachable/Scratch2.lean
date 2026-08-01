import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Mutation.Mutation
import Gc.Model.Mutation.Stmt
import Gc.Model.Preservation
import Gc.Reachability.Reachable.Semantics
import Gc.Reachability.Reachable.Corollaries
import Gc.Reachability.Reachable.Lemmas

-- Preservation of `FrameReachable_at_later_frame_implies_FrameReachable_at_frame` across a single
-- mutation -- the Reachable-layer analogue of `Referencable/Validity/Reachable.lean`'s `CR3`
-- preservation, restated over this layer's own `ReachableStep`/`FrameReachable`.
def FrameReachableAtLaterFrame_step (cmd : Stmt) : Prop :=
  ∀ cfg cfg' : RuntimeConfig, ValidConfig cfg → step cmd cfg = some cfg' →
    FrameReachable_at_later_frame_implies_FrameReachable_at_frame cfg →
    FrameReachable_at_later_frame_implies_FrameReachable_at_frame cfg'

-- Per-operation proofs, ordered easiest-to-hardest.

theorem frameReachableAtLaterFrame_step_enter (xf : FieldAccess) (bridgeVar : VarName) :
    FrameReachableAtLaterFrame_step (Stmt.enter xf bridgeVar) := by
  intro cfg cfg' vcfg h hFR3 frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  have h' : enter xf bridgeVar cfg = some cfg' := h
  have vcfg' : ValidConfig cfg' := enter_valid vcfg h'
  obtain ⟨rid, regionEntered, -, hlookupRid, hclosedRid, hcfg'⟩ := enter_cases h'
  rcases enter_frame_cases hcfg' hframeMem with
    ⟨hframeMemCfg, hframeLt⟩ | ⟨hframeRegionId, -, -, -, hframeIdx⟩
  swap
  · -- frame is the freshly-pushed frame: no frame' can have a strictly larger index.
    exfalso
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hframe'Mem
    have hframe'idx : frame'.index = n := by rw [← hfeq]
    have hcfg'len : cfg'.stack.length = cfg.stack.length + 1 := by rw [hcfg']; simp
    rw [hcfg'len] at hn
    have hcontra : cfg.stack.length < n := by rw [← hframeIdx, ← hframe'idx]; exact hlt
    omega
  -- frame is pre-existing.
  obtain ⟨region, hlookup, hopen⟩ := l2_of_stackWithIndex vcfg hframeMemCfg
  have hridNe : frame.regionId ≠ rid := enter_regionId_ne vcfg hframeMemCfg hlookupRid hclosedRid
  have hlookup' : cfg'.heap.lookup frame.regionId = some region := by
    rw [hcfg']; dsimp only; rw [AList.lookup_insert_ne hridNe]; exact hlookup
  have hloc_cfg : (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) := by
    rw [enter_corollary_2 vcfg h' oid]; exact hloc
  have hsafe' : SafeRef cfg' frame.regionId (Reference.OId oid) := Or.inl hloc
  rcases enter_frame_cases hcfg' hframe'Mem with
    ⟨hframe'MemCfg, hframe'Lt⟩ | ⟨hframe'RegionId, -, hframe'VarMap, -, hframe'Idx⟩
  · -- frame' is also pre-existing: transport reachability down to cfg, apply hFR3, transport back up.
    rw [FrameReachable_iff_reflTransGen] at hreach
    obtain ⟨start, hroot, hrtg⟩ := hreach
    have hrtg2 : Relation.ReflTransGen (ReachableStep cfg) start (Reference.OId oid) :=
      safe_reflTransGen_transport vcfg' hlookup' hopen
        (fun oid0 b => (enter_oid_step_iff vcfg h' oid0 b).symm) hrtg hsafe'
    have hroot2 : FrameRoot cfg frame'.index start := by
      rcases hroot with
        ⟨Xf, hXfmem, hXfidx, var, hvar⟩ | ⟨Xf, hXfmem, hXfidx, region', hlookupX, hbridge⟩
      · have hXflt : Xf.index < cfg.stack.length := hXfidx ▸ hframe'Lt
        exact Or.inl ⟨Xf, enter_frame_mem_down h' hXfmem hXflt, hXfidx, var, hvar⟩
      · have hXflt : Xf.index < cfg.stack.length := hXfidx ▸ hframe'Lt
        have hXfmemcfg : Xf ∈ cfg.stackWithIndex := enter_frame_mem_down h' hXfmem hXflt
        have hXfne : Xf.regionId ≠ rid := enter_regionId_ne vcfg hXfmemcfg hlookupRid hclosedRid
        have hlookupXcfg : cfg.heap.lookup Xf.regionId = some region' := by
          rw [hcfg'] at hlookupX; dsimp only at hlookupX
          rw [AList.lookup_insert_ne hXfne] at hlookupX; exact hlookupX
        exact Or.inr ⟨Xf, hXfmemcfg, hXfidx, region', hlookupXcfg, hbridge⟩
    have hreach_cfg : FrameReachable cfg frame'.index (Reference.OId oid) :=
      (FrameReachable_iff_reflTransGen cfg frame'.index (Reference.OId oid)).mpr ⟨start, hroot2, hrtg2⟩
    have hresult_cfg : FrameReachable cfg frame.index (Reference.OId oid) :=
      hFR3 frame hframeMemCfg frame' hframe'MemCfg hlt oid hloc_cfg hreach_cfg
    rw [FrameReachable_iff_reflTransGen] at hresult_cfg
    obtain ⟨start2, hroot3, hrtg3⟩ := hresult_cfg
    have hsafe_cfg : SafeRef cfg frame.regionId (Reference.OId oid) := Or.inl hloc_cfg
    have hrtg4 : Relation.ReflTransGen (ReachableStep cfg') start2 (Reference.OId oid) :=
      safe_reflTransGen_transport vcfg hlookup hopen (enter_oid_step_iff vcfg h') hrtg3 hsafe_cfg
    have hroot4 : FrameRoot cfg' frame.index start2 := by
      rcases hroot3 with
        ⟨Xf, hXfmem, hXfidx, var, hvar⟩ | ⟨Xf, hXfmem, hXfidx, region', hlookupX, hbridge⟩
      · exact Or.inl ⟨Xf, enter_frame_mem_up h' hXfmem, hXfidx, var, hvar⟩
      · have hXfne : Xf.regionId ≠ rid := enter_regionId_ne vcfg hXfmem hlookupRid hclosedRid
        have hlookupX' : cfg'.heap.lookup Xf.regionId = some region' := by
          rw [hcfg']; dsimp only; rw [AList.lookup_insert_ne hXfne]; exact hlookupX
        exact Or.inr ⟨Xf, enter_frame_mem_up h' hXfmem, hXfidx, region', hlookupX', hbridge⟩
    exact (FrameReachable_iff_reflTransGen cfg' frame.index (Reference.OId oid)).mpr ⟨start2, hroot4, hrtg4⟩
  · -- frame' is the freshly-pushed frame: its only possible root is the entered region's bridge, unsafe.
    exfalso
    rw [FrameReachable_iff_reflTransGen] at hreach
    obtain ⟨start, hroot, hrtg⟩ := hreach
    have hstart : start = Reference.OId regionEntered.bridgeObjectId := by
      rcases hroot with
        ⟨Xf, hXfmem, hXfidx, var, hvar⟩ | ⟨Xf, hXfmem, hXfidx, region', hlookupX, hbridge⟩
      · exfalso
        have hXfeq : Xf = frame' := swap_corollary_stackWithIndex_index_inj hXfmem hframe'Mem hXfidx
        rw [hXfeq, hframe'VarMap] at hvar
        simp at hvar
      · have hXfeq : Xf = frame' := swap_corollary_stackWithIndex_index_inj hXfmem hframe'Mem hXfidx
        have hlookupF' : cfg'.heap.lookup rid = some { regionEntered with status := Status.Open } := by
          rw [hcfg']; dsimp only; rw [AList.lookup_insert]
        rw [hXfeq, hframe'RegionId, hlookupF'] at hlookupX
        injection hlookupX with hregionEq
        rw [← hregionEq] at hbridge
        exact hbridge
    rw [hstart] at hrtg
    have hbridgeMem : regionEntered ∈ cfg.heap.regions := by
      unfold Heap.regions
      exact List.mem_map_of_mem (AList.lookup_mem_entries hlookupRid)
    have hbridgeIn : regionEntered.bridgeObjectId ∈ regionEntered.objMap := vcfg.h1 regionEntered hbridgeMem
    have hbridgeLoc : (Reference.OId regionEntered.bridgeObjectId).loc? cfg' = some (Location.Rgn rid) := by
      rw [oid_loc_rgn_iff_in_heap vcfg']
      refine ⟨{ regionEntered with status := Status.Open }, ?_, hbridgeIn⟩
      rw [hcfg']; dsimp only; rw [AList.lookup_insert]
    have hsafeStart := safe_reflTransGen_root_safe vcfg' hlookup' hopen hrtg hsafe'
    unfold SafeRef at hsafeStart
    rcases hsafeStart with hbad | ⟨fid, hbad⟩
    · rw [hbad] at hbridgeLoc
      injection hbridgeLoc with hbadEq
      injection hbadEq with hbadEq
      exact hridNe hbadEq
    · rw [hbad] at hbridgeLoc
      exact absurd hbridgeLoc (by simp)

theorem frameReachableAtLaterFrame_step_exit :
    FrameReachableAtLaterFrame_step Stmt.exit := by
  intro cfg cfg' vcfg h hFR3 frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  have h' : exit cfg = some cfg' := h
  obtain ⟨poppedFrame, region0, hlen, hlast, hlookupRid, hopenRid, hcfg'⟩ := exit_cases h'
  obtain ⟨hframeMemCfg, hframeLt⟩ := exit_frame_mem_down h' hframeMem
  obtain ⟨hframe'MemCfg, -⟩ := exit_frame_mem_down h' hframe'Mem
  obtain ⟨region, hlookup, hopen⟩ := l2_of_stackWithIndex vcfg hframeMemCfg
  have hridNe : frame.regionId ≠ poppedFrame.regionId := exit_regionId_ne vcfg hframeMemCfg hframeLt hlast hlen
  have hlookup' : cfg'.heap.lookup frame.regionId = some region := by
    rw [hcfg']; dsimp only; rw [AList.lookup_insert_ne hridNe]; exact hlookup
  have hloc_cfg : (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) := by
    rw [oid_loc_rgn_iff_in_heap vcfg]
    rw [oid_loc_rgn_iff_in_heap (exit_valid vcfg h')] at hloc
    obtain ⟨region1, hlookup1, hmem1⟩ := hloc
    rw [hlookup'] at hlookup1
    injection hlookup1 with hregionEq
    exact ⟨region, hlookup, hregionEq ▸ hmem1⟩
  have hreach_cfg : FrameReachable cfg frame'.index (Reference.OId oid) :=
    exit_frame_reachable_transport_backward vcfg h' hlast hlen hcfg' hlookup hlookup' hopen hloc hframe'Mem hreach
  have hresult_cfg : FrameReachable cfg frame.index (Reference.OId oid) :=
    hFR3 frame hframeMemCfg frame' hframe'MemCfg hlt oid hloc_cfg hreach_cfg
  exact exit_frame_reachable_transport vcfg h' hlast hlen hlookupRid hopenRid hcfg' hlookup hopen hloc_cfg
    hframeMemCfg hframeLt hresult_cfg

theorem frameReachableAtLaterFrame_step_makeObjStack (x : VarName) :
    FrameReachableAtLaterFrame_step (Stmt.makeObjStack x) := by
  intro cfg cfg' vcfg h hFR3 frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  have h' : makeObjStack x cfg = some cfg' := h
  have vcfg' : ValidConfig cfg' := makeObjStack_valid vcfg h'
  obtain ⟨lastFrame, hlast, hcfg'⟩ := makeObjStack_cases h'
  have hLf : ({ lastFrame with index := cfg.stack.length - 1 } : FrameWithIndex) ∈ cfg.stackWithIndex :=
    stackWithIndex_getLast_mem hlast
  have hne' : cfg.stack ≠ [] := by intro hnil; rw [hnil] at hlast; simp at hlast
  have hlen1 : 1 ≤ cfg.stack.length := List.length_pos_of_ne_nil hne'
  have hcfg'len : cfg'.stack.length = cfg.stack.length := by
    rw [hcfg']; dsimp only; rw [List.length_append, List.length_dropLast, List.length_singleton]; omega
  rcases makeObjStack_frame_cases hlast hcfg' hframeMem with
    ⟨hframeMemCfg, hframeLt⟩ | ⟨-, -, -, -, hframeIdx⟩
  swap
  · exfalso
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hframe'Mem
    have hframe'idx : frame'.index = n := by rw [← hfeq]
    rw [hcfg'len] at hn
    have hcontra : cfg.stack.length - 1 < n := by
      have heq1 : cfg.stack.length - 1 = frame.index := by rw [hframeIdx, List.length_dropLast]
      rw [heq1, ← hframe'idx]; exact hlt
    omega
  have hidNe : oid ≠ cfg.freshObjectId := by
    intro heq
    subst heq
    obtain ⟨region1, hlookup1, hmem1⟩ := (oid_loc_rgn_iff_in_heap vcfg').mp hloc
    have hlookup1' : cfg.heap.lookup frame.regionId = some region1 := by rw [hcfg'] at hlookup1; exact hlookup1
    apply cfg.freshObjectId_not_mem
    unfold RuntimeConfig.objectIds
    rw [List.mem_append]
    right
    unfold Heap.objectIds
    rw [List.mem_flatten]
    exact ⟨region1.objectIds, List.mem_map_of_mem (AList.lookup_mem_entries hlookup1'), hmem1⟩
  have hloc_cfg : (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) := by
    rw [makeObjStack_loc_eq_of_ne h' hidNe]; exact hloc
  rcases makeObjStack_frame_cases hlast hcfg' hframe'Mem with
    ⟨hframe'MemCfg, hframe'Lt⟩ | ⟨hframe'RegionId, -, hframe'VarMap, -, hframe'Idx⟩
  · -- frame' is also not the last frame: unconditional iff transport both ways.
    have hreach_cfg : FrameReachable cfg frame'.index (Reference.OId oid) :=
      (makeObjStack_frame_reachable_iff h' hframe'MemCfg hframe'Lt (Reference.OId oid)).mpr hreach
    have hresult_cfg : FrameReachable cfg frame.index (Reference.OId oid) :=
      hFR3 frame hframeMemCfg frame' hframe'MemCfg hlt oid hloc_cfg hreach_cfg
    exact (makeObjStack_frame_reachable_iff h' hframeMemCfg hframeLt (Reference.OId oid)).mp hresult_cfg
  · -- frame' IS the last (mutated) frame: its own reachability chain either came from
    -- lastFrame's pre-existing roots, or was rooted at the fresh var/object -- a dead end,
    -- since it never resolves anywhere and so can't reach `oid`'s known Rgn location.
    rw [FrameReachable_iff_reflTransGen] at hreach
    obtain ⟨start, hroot, hrtg⟩ := hreach
    rw [← makeObjStack_step_eq h'] at hrtg
    have hframe'Idx' : frame'.index = cfg.stack.length - 1 := by rw [hframe'Idx, List.length_dropLast]
    have hLfReach : FrameReachable cfg (cfg.stack.length - 1) (Reference.OId oid) := by
      rcases hroot with ⟨Xf, hXfmem, hXfidx, var, hvar⟩ | ⟨Xf, hXfmem, hXfidx, region, hlookupX, hbridge⟩
      · have hXfeq : Xf = frame' := swap_corollary_stackWithIndex_index_inj hXfmem hframe'Mem hXfidx
        rw [hXfeq, hframe'VarMap] at hvar
        by_cases hveq : var = x
        · subst hveq
          rw [AList.lookup_insert] at hvar
          injection hvar with hstart
          exfalso
          rw [← hstart] at hrtg
          rcases hrtg.cases_head with heqStart | ⟨c, hstep, -⟩
          · rw [← heqStart] at hloc_cfg
            exact freshObjectId_loc_ne_rgn hloc_cfg
          · rw [ReachableStep_oid_iff] at hstep
            obtain ⟨obj, hobjAt, -⟩ := hstep
            rw [freshObjectId_objAt_none] at hobjAt
            exact absurd hobjAt (by simp)
        · rw [AList.lookup_insert_ne hveq] at hvar
          exact (FrameReachable_iff_reflTransGen cfg (cfg.stack.length - 1) (Reference.OId oid)).mpr
            ⟨start, Or.inl ⟨{ lastFrame with index := cfg.stack.length - 1 }, hLf, rfl, var, hvar⟩, hrtg⟩
      · have hXfeq : Xf = frame' := swap_corollary_stackWithIndex_index_inj hXfmem hframe'Mem hXfidx
        have hlookup' : cfg.heap.lookup Xf.regionId = some region := by rw [hcfg'] at hlookupX; exact hlookupX
        rw [hXfeq, hframe'RegionId] at hlookup'
        exact (FrameReachable_iff_reflTransGen cfg (cfg.stack.length - 1) (Reference.OId oid)).mpr
          ⟨start, Or.inr ⟨{ lastFrame with index := cfg.stack.length - 1 }, hLf, rfl, region, hlookup', hbridge⟩, hrtg⟩
    have hlt' : frame.index < ({ lastFrame with index := cfg.stack.length - 1 } : FrameWithIndex).index := by
      show frame.index < cfg.stack.length - 1
      rw [← hframe'Idx']; exact hlt
    have hresult_cfg : FrameReachable cfg frame.index (Reference.OId oid) :=
      hFR3 frame hframeMemCfg _ hLf hlt' oid hloc_cfg hLfReach
    exact (makeObjStack_frame_reachable_iff h' hframeMemCfg hframeLt (Reference.OId oid)).mp hresult_cfg

theorem frameReachableAtLaterFrame_step_makeObjRegion (x : VarName) :
    FrameReachableAtLaterFrame_step (Stmt.makeObjRegion x) := by
  sorry

theorem frameReachableAtLaterFrame_step_makeRegion (x : VarName) :
    FrameReachableAtLaterFrame_step (Stmt.makeRegion x) := by
  sorry

theorem frameReachableAtLaterFrame_step_merge (x : VarName) :
    FrameReachableAtLaterFrame_step (Stmt.merge x) := by
  sorry

theorem frameReachableAtLaterFrame_step_varAsgn (x : VarName) (yf : FieldAccess) :
    FrameReachableAtLaterFrame_step (Stmt.varAsgn x yf) := by
  sorry

theorem frameReachableAtLaterFrame_step_fieldAsgn (xf : FieldAccess) (y : VarName) :
    FrameReachableAtLaterFrame_step (Stmt.fieldAsgn xf y) := by
  sorry

theorem frameReachableAtLaterFrame_step_swap (x : VarName) (yf : FieldAccess) :
    FrameReachableAtLaterFrame_step (Stmt.swap x yf) := by
  sorry

theorem frameReachableAtLaterFrame_step_all (cmd : Stmt) :
    FrameReachableAtLaterFrame_step cmd := by
  cases cmd with
  | enter xf bridgeVar => exact frameReachableAtLaterFrame_step_enter xf bridgeVar
  | exit => exact frameReachableAtLaterFrame_step_exit
  | fieldAsgn xf y => exact frameReachableAtLaterFrame_step_fieldAsgn xf y
  | makeObjRegion x => exact frameReachableAtLaterFrame_step_makeObjRegion x
  | makeObjStack x => exact frameReachableAtLaterFrame_step_makeObjStack x
  | makeRegion x => exact frameReachableAtLaterFrame_step_makeRegion x
  | merge x => exact frameReachableAtLaterFrame_step_merge x
  | swap x yf => exact frameReachableAtLaterFrame_step_swap x yf
  | varAsgn x yf => exact frameReachableAtLaterFrame_step_varAsgn x yf
