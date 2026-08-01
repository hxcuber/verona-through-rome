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
  intro cfg cfg' vcfg h hFR3 frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  have h' : makeObjRegion x cfg = some cfg' := h
  have vcfg' : ValidConfig cfg' := makeObjRegion_valid vcfg h'
  obtain ⟨lastFrame, region0, hlast, hlookupRid0, hopen0, hcfg'⟩ := makeObjRegion_cases h'
  have hLf : ({ lastFrame with index := cfg.stack.length - 1 } : FrameWithIndex) ∈ cfg.stackWithIndex :=
    stackWithIndex_getLast_mem hlast
  have hne' : cfg.stack ≠ [] := by intro hnil; rw [hnil] at hlast; simp at hlast
  have hlen1 : 1 ≤ cfg.stack.length := List.length_pos_of_ne_nil hne'
  have hcfg'len : cfg'.stack.length = cfg.stack.length := by
    rw [hcfg']; dsimp only; rw [List.length_append, List.length_dropLast, List.length_singleton]; omega
  rcases makeObjRegion_frame_cases h' hframeMem with
    ⟨hframeMemCfg, hframeLt⟩ | ⟨lf, hlf, -, -, -, -, hframeIdx⟩
  swap
  · exfalso
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hframe'Mem
    have hframe'idx : frame'.index = n := by rw [← hfeq]
    rw [hcfg'len] at hn
    have hcontra : cfg.stack.length - 1 < n := by
      have heq1 : cfg.stack.length - 1 = frame.index := by rw [hframeIdx, List.length_dropLast]
      rw [heq1, ← hframe'idx]; exact hlt
    omega
  have hframeRidNe : frame.regionId ≠ lastFrame.regionId :=
    makeObjRegion_regionId_ne vcfg hframeMemCfg hframeLt hlast
  have hidNe : oid ≠ cfg.freshObjectId := by
    intro heq
    subst heq
    obtain ⟨region1, hlookup1, hmem1⟩ := (oid_loc_rgn_iff_in_heap vcfg').mp hloc
    have hlookup1' : cfg.heap.lookup frame.regionId = some region1 := by
      rw [hcfg'] at hlookup1; dsimp only at hlookup1
      rw [AList.lookup_insert_ne hframeRidNe] at hlookup1
      exact hlookup1
    apply cfg.freshObjectId_not_mem
    unfold RuntimeConfig.objectIds
    rw [List.mem_append]
    right
    unfold Heap.objectIds
    rw [List.mem_flatten]
    exact ⟨region1.objectIds, List.mem_map_of_mem (AList.lookup_mem_entries hlookup1'), hmem1⟩
  have hloc_cfg : (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) := by
    rw [makeObjRegion_corollary_loc_eq vcfg h' oid hidNe]; exact hloc
  rcases makeObjRegion_frame_cases h' hframe'Mem with
    ⟨hframe'MemCfg, hframe'Lt⟩ | ⟨lf', hlf', hframe'RegionId, -, -, hframe'VarMap, hframe'Idx⟩
  · -- frame' is also not the last frame: unconditional iff transport both ways.
    have hreach_cfg : FrameReachable cfg frame'.index (Reference.OId oid) :=
      (makeObjRegion_frame_reachable_iff vcfg h' hframe'MemCfg hframe'Lt (Reference.OId oid)).mpr hreach
    have hresult_cfg : FrameReachable cfg frame.index (Reference.OId oid) :=
      hFR3 frame hframeMemCfg frame' hframe'MemCfg hlt oid hloc_cfg hreach_cfg
    exact (makeObjRegion_frame_reachable_iff vcfg h' hframeMemCfg hframeLt (Reference.OId oid)).mp hresult_cfg
  · -- frame' IS the last (mutated) frame.
    rw [hlast] at hlf'
    injection hlf' with hlf'
    subst hlf'
    rw [FrameReachable_iff_reflTransGen] at hreach
    obtain ⟨start, hroot, hrtg⟩ := hreach
    rw [← makeObjRegion_step_eq vcfg h'] at hrtg
    have hframe'Idx' : frame'.index = cfg.stack.length - 1 := by rw [hframe'Idx, List.length_dropLast]
    have hLfReach : FrameReachable cfg (cfg.stack.length - 1) (Reference.OId oid) := by
      rcases hroot with ⟨Xf, hXfmem, hXfidx, var, hvar⟩ | ⟨Xf, hXfmem, hXfidx, regionX, hlookupX, hbridge⟩
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
        have hXfridEq : Xf.regionId = lastFrame.regionId := by rw [hXfeq]; exact hframe'RegionId
        have hlookup' : cfg'.heap.lookup Xf.regionId =
            some { region0 with objMap := region0.objMap.insert cfg.freshObjectId ∅ } := by
          rw [hXfridEq, hcfg']; dsimp only; rw [AList.lookup_insert]
        rw [hlookup'] at hlookupX
        injection hlookupX with hlookupEq
        rw [← hlookupEq] at hbridge
        dsimp only at hbridge
        exact (FrameReachable_iff_reflTransGen cfg (cfg.stack.length - 1) (Reference.OId oid)).mpr
          ⟨start, Or.inr ⟨{ lastFrame with index := cfg.stack.length - 1 }, hLf, rfl, region0, hlookupRid0, hbridge⟩,
            hrtg⟩
    have hlt' : frame.index < ({ lastFrame with index := cfg.stack.length - 1 } : FrameWithIndex).index := by
      show frame.index < cfg.stack.length - 1
      rw [← hframe'Idx']; exact hlt
    have hresult_cfg : FrameReachable cfg frame.index (Reference.OId oid) :=
      hFR3 frame hframeMemCfg _ hLf hlt' oid hloc_cfg hLfReach
    exact (makeObjRegion_frame_reachable_iff vcfg h' hframeMemCfg hframeLt (Reference.OId oid)).mp hresult_cfg

theorem frameReachableAtLaterFrame_step_makeRegion (x : VarName) :
    FrameReachableAtLaterFrame_step (Stmt.makeRegion x) := by
  intro cfg cfg' vcfg h hFR3 frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  have h' : makeRegion x cfg = some cfg' := h
  have vcfg' : ValidConfig cfg' := makeRegion_valid vcfg h'
  obtain ⟨lastFrame, hlast, hcfg'⟩ := makeRegion_cases h'
  obtain ⟨region0, hlookupRid0, hopen0⟩ := l2_of_stackWithIndex vcfg (stackWithIndex_getLast_mem hlast)
  have hLf : ({ lastFrame with index := cfg.stack.length - 1 } : FrameWithIndex) ∈ cfg.stackWithIndex :=
    stackWithIndex_getLast_mem hlast
  have hne' : cfg.stack ≠ [] := by intro hnil; rw [hnil] at hlast; simp at hlast
  have hlen1 : 1 ≤ cfg.stack.length := List.length_pos_of_ne_nil hne'
  have hcfg'len : cfg'.stack.length = cfg.stack.length := by
    rw [hcfg']; dsimp only; rw [List.length_append, List.length_dropLast, List.length_singleton]; omega
  rcases makeRegion_frame_cases h' hframeMem with
    ⟨hframeMemCfg, hframeLt⟩ | ⟨lf, hlf, -, -, -, -, hframeIdx⟩
  swap
  · exfalso
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hframe'Mem
    have hframe'idx : frame'.index = n := by rw [← hfeq]
    rw [hcfg'len] at hn
    have hcontra : cfg.stack.length - 1 < n := by
      have heq1 : cfg.stack.length - 1 = frame.index := by rw [hframeIdx, List.length_dropLast]
      rw [heq1, ← hframe'idx]; exact hlt
    omega
  have hframeRidNe : frame.regionId ≠ cfg.freshRegionId := by
    obtain ⟨region1, hlookup1, -⟩ := l2_of_stackWithIndex vcfg hframeMemCfg
    intro heq
    apply RuntimeConfig.freshRegionId_not_mem cfg
    rw [← AList.mem_keys, ← AList.lookup_isSome, ← heq, hlookup1]
    simp
  have hidNe : oid ≠ cfg.freshObjectId := by
    intro heq
    subst heq
    obtain ⟨region1, hlookup1, hmem1⟩ := (oid_loc_rgn_iff_in_heap vcfg').mp hloc
    have hlookup1' : cfg.heap.lookup frame.regionId = some region1 := by
      rw [hcfg'] at hlookup1; dsimp only at hlookup1
      rw [AList.lookup_insert_ne hframeRidNe] at hlookup1
      exact hlookup1
    apply cfg.freshObjectId_not_mem
    unfold RuntimeConfig.objectIds
    rw [List.mem_append]
    right
    unfold Heap.objectIds
    rw [List.mem_flatten]
    exact ⟨region1.objectIds, List.mem_map_of_mem (AList.lookup_mem_entries hlookup1'), hmem1⟩
  have hloc_cfg : (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) := by
    rw [makeRegion_corollary_loc_eq vcfg h' oid hidNe]; exact hloc
  rcases makeRegion_frame_cases h' hframe'Mem with
    ⟨hframe'MemCfg, hframe'Lt⟩ | ⟨lf', hlf', hframe'RegionId, -, -, hframe'VarMap, hframe'Idx⟩
  · -- frame' is also not the last frame: unconditional iff transport both ways.
    have hreach_cfg : FrameReachable cfg frame'.index (Reference.OId oid) :=
      (makeRegion_frame_reachable_iff vcfg h' hframe'MemCfg hframe'Lt (Reference.OId oid)).mpr hreach
    have hresult_cfg : FrameReachable cfg frame.index (Reference.OId oid) :=
      hFR3 frame hframeMemCfg frame' hframe'MemCfg hlt oid hloc_cfg hreach_cfg
    exact (makeRegion_frame_reachable_iff vcfg h' hframeMemCfg hframeLt (Reference.OId oid)).mp hresult_cfg
  · -- frame' IS the last (mutated) frame.
    rw [hlast] at hlf'
    injection hlf' with hlf'
    subst hlf'
    rw [FrameReachable_iff_reflTransGen] at hreach
    obtain ⟨start, hroot, hrtg⟩ := hreach
    rw [← makeRegion_step_eq vcfg h'] at hrtg
    have hframe'Idx' : frame'.index = cfg.stack.length - 1 := by rw [hframe'Idx, List.length_dropLast]
    have hLfReach : FrameReachable cfg (cfg.stack.length - 1) (Reference.OId oid) := by
      rcases hroot with ⟨Xf, hXfmem, hXfidx, var, hvar⟩ | ⟨Xf, hXfmem, hXfidx, regionX, hlookupX, hbridge⟩
      · have hXfeq : Xf = frame' := swap_corollary_stackWithIndex_index_inj hXfmem hframe'Mem hXfidx
        rw [hXfeq, hframe'VarMap] at hvar
        by_cases hveq : var = x
        · subst hveq
          rw [AList.lookup_insert] at hvar
          injection hvar with hstart
          exfalso
          rw [← hstart] at hrtg
          rcases hrtg.cases_head with heqStart | ⟨c, hstep, -⟩
          · cases heqStart
          · exact absurd hstep freshRegionId_no_step
        · rw [AList.lookup_insert_ne hveq] at hvar
          exact (FrameReachable_iff_reflTransGen cfg (cfg.stack.length - 1) (Reference.OId oid)).mpr
            ⟨start, Or.inl ⟨{ lastFrame with index := cfg.stack.length - 1 }, hLf, rfl, var, hvar⟩, hrtg⟩
      · have hXfeq : Xf = frame' := swap_corollary_stackWithIndex_index_inj hXfmem hframe'Mem hXfidx
        have hXfridEq : Xf.regionId = lastFrame.regionId := by rw [hXfeq]; exact hframe'RegionId
        have hne : Xf.regionId ≠ cfg.freshRegionId := by
          rw [hXfridEq]
          intro heq
          apply RuntimeConfig.freshRegionId_not_mem cfg
          rw [← AList.mem_keys, ← AList.lookup_isSome, ← heq, hlookupRid0]
          simp
        have hlookup' : cfg'.heap.lookup Xf.regionId = cfg.heap.lookup Xf.regionId := by
          rw [hcfg']; dsimp only; rw [AList.lookup_insert_ne hne]
        rw [hlookup', hXfridEq] at hlookupX
        exact (FrameReachable_iff_reflTransGen cfg (cfg.stack.length - 1) (Reference.OId oid)).mpr
          ⟨start, Or.inr ⟨{ lastFrame with index := cfg.stack.length - 1 }, hLf, rfl, regionX, hlookupX, hbridge⟩,
            hrtg⟩
    have hlt' : frame.index < ({ lastFrame with index := cfg.stack.length - 1 } : FrameWithIndex).index := by
      show frame.index < cfg.stack.length - 1
      rw [← hframe'Idx']; exact hlt
    have hresult_cfg : FrameReachable cfg frame.index (Reference.OId oid) :=
      hFR3 frame hframeMemCfg _ hLf hlt' oid hloc_cfg hLfReach
    exact (makeRegion_frame_reachable_iff vcfg h' hframeMemCfg hframeLt (Reference.OId oid)).mp hresult_cfg

theorem frameReachableAtLaterFrame_step_merge (x : VarName) :
    FrameReachableAtLaterFrame_step (Stmt.merge x) := by
  intro cfg cfg' vcfg h hFR3 frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  have h' : merge x cfg = some cfg' := h
  have vcfg' : ValidConfig cfg' := merge_valid vcfg h'
  obtain ⟨frame1, rid', region1, region', hframe1, hxref, hregion1, hregion', hclosed, hopen, hcfg'⟩ :=
    merge_cases h'
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame1] :=
    (List.dropLast_append_getLast? frame1 hframe1).symm
  have hframe1MemStack : frame1 ∈ cfg.stack := by
    rw [stack_eq]; exact List.mem_append_right _ (List.mem_singleton_self _)
  have hlast1_mem : ({ frame1 with index := cfg.stack.dropLast.length } : FrameWithIndex) ∈ cfg.stackWithIndex := by
    have hframe1_get : cfg.stack[cfg.stack.dropLast.length]? = some frame1 := by
      conv_lhs => rw [stack_eq]; simp
    obtain ⟨hh1, hheq⟩ := List.getElem?_eq_some_iff.mp hframe1_get
    unfold RuntimeConfig.stackWithIndex
    exact List.mem_mapIdx.mpr ⟨cfg.stack.dropLast.length, hh1, by rw [hheq]⟩
  have hridNe1 : ∀ G0 : FrameWithIndex, G0 ∈ cfg.stackWithIndex → G0.regionId ≠ rid' := by
    intro G0 hG0mem hc
    obtain ⟨region0, hlk0, hopen0⟩ := l2_of_stackWithIndex vcfg hG0mem
    rw [hc, hregion'] at hlk0
    injection hlk0 with hlk0eq
    rw [← hlk0eq] at hopen0
    exact absurd (hopen0.symm.trans hclosed) (by decide)
  have hridNeFrame1 : ∀ G0 : FrameWithIndex, G0 ∈ cfg.stackWithIndex →
      G0.index < cfg.stack.dropLast.length → G0.regionId ≠ frame1.regionId := by
    intro G0 hG0mem hG0lt hc
    have hidxeq := merge_corollary_regionId_unique_index vcfg.s1 hG0mem hlast1_mem hc
    exact absurd hidxeq (Nat.ne_of_lt hG0lt)
  have hstepIffOfNe : ∀ a : Reference, a ≠ Reference.RId rid' → ∀ b, ReachableStep cfg a b ↔ ReachableStep cfg' a b := by
    intro a hane b
    cases a with
    | OId oid0 => exact merge_oid_step_iff vcfg h' oid0 b
    | RId rid0 =>
      have hne0 : rid0 ≠ rid' := fun hc => hane (by rw [hc])
      exact merge_rid_step_iff_of_ne hframe1 hxref hregion1 hregion' hclosed hopen hcfg' hne0 b
  have hnotTarget : ∀ a, ¬ ReachableStep cfg a (Reference.RId rid') :=
    merge_ridPrime_not_step_target vcfg hframe1MemStack hxref
  have hchainAvoids : ∀ {start target : Reference}, start ≠ Reference.RId rid' →
      Relation.ReflTransGen (ReachableStep cfg) start target → target ≠ Reference.RId rid' := by
    intro start target hstartne hrtg
    induction hrtg with
    | refl => exact hstartne
    | tail _ hstep _ => intro hc; rw [hc] at hstep; exact hnotTarget _ hstep
  have hchainTransportUp : ∀ {start target : Reference}, start ≠ Reference.RId rid' →
      Relation.ReflTransGen (ReachableStep cfg) start target →
      Relation.ReflTransGen (ReachableStep cfg') start target := by
    intro start target hstartne hrtg
    induction hrtg with
    | refl => exact Relation.ReflTransGen.refl
    | tail hprev hstep ih =>
      rename_i prev cur
      exact Relation.ReflTransGen.tail ih ((hstepIffOfNe prev (hchainAvoids hstartne hprev) cur).mp hstep)
  have hneRidFrame1 : rid' ≠ frame1.regionId := merge_corollary_rid_ne_regionId hregion1 hregion' hclosed hopen
  have hnotTargetCfg' : ∀ a, ¬ ReachableStep cfg' a (Reference.RId rid') := by
    intro a hstep
    by_cases hane : a = Reference.RId rid'
    · subst hane
      rw [ReachableStep_rid_iff] at hstep
      obtain ⟨region2, hlookup2, -, -⟩ := hstep
      have hnone : cfg'.heap.lookup rid' = none := by
        rw [hcfg']; dsimp only
        rw [AList.lookup_insert_ne hneRidFrame1, AList.lookup_erase]
      rw [hnone] at hlookup2
      exact absurd hlookup2 (by simp)
    · exact hnotTarget a ((hstepIffOfNe a hane (Reference.RId rid')).mpr hstep)
  have hchainAvoidsCfg' : ∀ {start target : Reference}, start ≠ Reference.RId rid' →
      Relation.ReflTransGen (ReachableStep cfg') start target → target ≠ Reference.RId rid' := by
    intro start target hstartne hrtg
    induction hrtg with
    | refl => exact hstartne
    | tail _ hstep _ => intro hc; rw [hc] at hstep; exact hnotTargetCfg' _ hstep
  have hchainTransportDown : ∀ {start target : Reference}, start ≠ Reference.RId rid' →
      Relation.ReflTransGen (ReachableStep cfg') start target →
      Relation.ReflTransGen (ReachableStep cfg) start target := by
    intro start target hstartne hrtg
    induction hrtg with
    | refl => exact Relation.ReflTransGen.refl
    | tail hprev hstep ih =>
      rename_i prev cur
      exact Relation.ReflTransGen.tail ih
        ((hstepIffOfNe prev (hchainAvoidsCfg' hstartne hprev) cur).mpr hstep)
  have frame_transport_down : ∀ fr : FrameWithIndex, fr ∈ cfg'.stackWithIndex →
      fr.index < cfg.stack.dropLast.length → fr ∈ cfg.stackWithIndex := by
    intro fr hfr hltfr
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr
    have hidx_n : fr.index = n := by rw [← hfeq]
    have hlt2 : n < cfg.stack.dropLast.length := by rw [← hidx_n]; exact hltfr
    have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
      conv_lhs => rw [stack_eq]
      rw [List.getElem?_append_left hlt2]
    have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
      rw [hcfg']; dsimp only; rw [List.getElem?_append_left hlt2]
    have hfr_get? : cfg'.stack[n]? = some fr.toFrame := by
      rw [show fr.toFrame = cfg'.stack[n] from by rw [← hfeq]]
      exact List.getElem?_eq_getElem hn
    have hcfgn : cfg.stack[n]? = some fr.toFrame := by rw [e1, ← e2, hfr_get?]
    obtain ⟨h1, heq⟩ := List.getElem?_eq_some_iff.mp hcfgn
    unfold RuntimeConfig.stackWithIndex
    exact List.mem_mapIdx.mpr ⟨n, h1, by rw [heq, ← hidx_n]⟩
  have frame_transport_up : ∀ fr : FrameWithIndex, fr ∈ cfg.stackWithIndex →
      fr.index < cfg.stack.dropLast.length → fr ∈ cfg'.stackWithIndex := by
    intro fr hfr hltfr
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr
    have hidx_n : fr.index = n := by rw [← hfeq]
    have hlt2 : n < cfg.stack.dropLast.length := by rw [← hidx_n]; exact hltfr
    have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
      conv_lhs => rw [stack_eq]
      rw [List.getElem?_append_left hlt2]
    have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
      rw [hcfg']; dsimp only; rw [List.getElem?_append_left hlt2]
    have hfr_get? : cfg.stack[n]? = some fr.toFrame := by
      rw [show fr.toFrame = cfg.stack[n] from by rw [← hfeq]]
      exact List.getElem?_eq_getElem hn
    have hcfg'n : cfg'.stack[n]? = some fr.toFrame := by rw [e2, ← e1, hfr_get?]
    obtain ⟨h1, heq⟩ := List.getElem?_eq_some_iff.mp hcfg'n
    unfold RuntimeConfig.stackWithIndex
    exact List.mem_mapIdx.mpr ⟨n, h1, by rw [heq, ← hidx_n]⟩
  have hframeRootIffNe : ∀ {fid : Index}, fid < cfg.stack.dropLast.length → ∀ (start : Reference),
      FrameRoot cfg fid start ↔ FrameRoot cfg' fid start := by
    intro fid hfidlt start
    constructor
    · rintro (⟨G0, hG0mem, hG0idx, var, hvar⟩ | ⟨G0, hG0mem, hG0idx, region0, hlk0, hbridge0⟩)
      · have hG0lt : G0.index < cfg.stack.dropLast.length := hG0idx ▸ hfidlt
        exact Or.inl ⟨G0, frame_transport_up G0 hG0mem hG0lt, hG0idx, var, hvar⟩
      · have hG0lt : G0.index < cfg.stack.dropLast.length := hG0idx ▸ hfidlt
        have hlk0' : cfg'.heap.lookup G0.regionId = some region0 := by
          rw [hcfg']; dsimp only
          rw [AList.lookup_insert_ne (hridNeFrame1 G0 hG0mem hG0lt), AList.lookup_erase_ne (hridNe1 G0 hG0mem)]
          exact hlk0
        exact Or.inr ⟨G0, frame_transport_up G0 hG0mem hG0lt, hG0idx, region0, hlk0', hbridge0⟩
    · rintro (⟨G0, hG0mem, hG0idx, var, hvar⟩ | ⟨G0, hG0mem, hG0idx, region0, hlk0, hbridge0⟩)
      · have hG0lt : G0.index < cfg.stack.dropLast.length := hG0idx ▸ hfidlt
        exact Or.inl ⟨G0, frame_transport_down G0 hG0mem hG0lt, hG0idx, var, hvar⟩
      · have hG0lt : G0.index < cfg.stack.dropLast.length := hG0idx ▸ hfidlt
        have hG0memCfg := frame_transport_down G0 hG0mem hG0lt
        have hlk0' : cfg.heap.lookup G0.regionId = some region0 := by
          rw [hcfg'] at hlk0; dsimp only at hlk0
          rw [AList.lookup_insert_ne (hridNeFrame1 G0 hG0memCfg hG0lt),
            AList.lookup_erase_ne (hridNe1 G0 hG0memCfg)] at hlk0
          exact hlk0
        exact Or.inr ⟨G0, hG0memCfg, hG0idx, region0, hlk0', hbridge0⟩
  have frameReachIffNe : ∀ {fid : Index}, fid < cfg.stack.dropLast.length → ∀ (ref : Reference),
      FrameReachable cfg fid ref ↔ FrameReachable cfg' fid ref := by
    intro fid hfidlt ref
    rw [FrameReachable_iff_reflTransGen, FrameReachable_iff_reflTransGen]
    constructor
    · rintro ⟨start, hroot, hrtg⟩
      have hstartne : start ≠ Reference.RId rid' := by
        rintro rfl
        rcases hroot with ⟨G0, hG0mem, hG0idx, var, hvar⟩ | ⟨G0, hG0mem, hG0idx, region0, hlk0, hbridge0⟩
        · have hG0lt : G0.index < cfg.stack.dropLast.length := hG0idx ▸ hfidlt
          have hG0memStack : G0.toFrame ∈ cfg.stack := by
            obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hG0mem
            rw [← hfeq]; exact List.getElem_mem hn
          exact merge_ridPrime_no_other_frame_var vcfg hframe1MemStack hxref hG0memStack
            (hridNeFrame1 G0 hG0mem hG0lt) hvar
        · exact absurd hbridge0 (by simp)
      exact ⟨start, (hframeRootIffNe hfidlt start).mp hroot, hchainTransportUp hstartne hrtg⟩
    · rintro ⟨start, hroot, hrtg⟩
      have hstartne : start ≠ Reference.RId rid' := by
        rintro rfl
        rcases hroot with ⟨G0, hG0mem, hG0idx, var, hvar⟩ | ⟨G0, hG0mem, hG0idx, region0, hlk0, hbridge0⟩
        · have hG0lt : G0.index < cfg.stack.dropLast.length := hG0idx ▸ hfidlt
          have hG0memCfg := frame_transport_down G0 hG0mem hG0lt
          have hG0memStack : G0.toFrame ∈ cfg.stack := by
            obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hG0memCfg
            rw [← hfeq]; exact List.getElem_mem hn
          exact merge_ridPrime_no_other_frame_var vcfg hframe1MemStack hxref hG0memStack
            (hridNeFrame1 G0 hG0memCfg hG0lt) hvar
        · exact absurd hbridge0 (by simp)
      exact ⟨start, (hframeRootIffNe hfidlt start).mpr hroot, hchainTransportDown hstartne hrtg⟩
  have hlenEq2 : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq]; simp
  set newFrame1 : Frame := ({ regionId := frame1.regionId, bridgeVar := frame1.bridgeVar, objMap := frame1.objMap, varMap := frame1.varMap.insert x (Reference.OId region'.bridgeObjectId) } : Frame) with newFrame1_def
  have hcfg'stack : cfg'.stack = cfg.stack.dropLast ++ [newFrame1] := by rw [hcfg']
  have hnewFrame1_get : cfg'.stack[cfg.stack.dropLast.length]? = some newFrame1 := by rw [hcfg'stack]; simp
  have hLf' : ({ newFrame1 with index := cfg.stack.dropLast.length } : FrameWithIndex) ∈ cfg'.stackWithIndex := by
    obtain ⟨hh1, hheq⟩ := List.getElem?_eq_some_iff.mp hnewFrame1_get
    unfold RuntimeConfig.stackWithIndex
    exact List.mem_mapIdx.mpr ⟨cfg.stack.dropLast.length, hh1, by rw [hheq]⟩
  have hstackLenEq : cfg.stack.length = cfg'.stack.length := by
    have hlenApp : cfg'.stack.length = cfg.stack.dropLast.length + 1 := by rw [hcfg'stack]; simp
    omega
  have hallLt : ∀ fr : FrameWithIndex, fr ∈ cfg'.stackWithIndex → fr.index < cfg.stack.dropLast.length + 1 := by
    intro fr hfr
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr
    have hidx : fr.index = n := by rw [← hfeq]
    have hn' : n < cfg'.stack.length := hn
    rw [← hstackLenEq, hlenEq2] at hn'
    rw [hidx]; exact hn'
  have hframeLt : frame.index < cfg.stack.dropLast.length := by
    have h2 := hallLt frame' hframe'Mem
    exact lt_of_lt_of_le hlt (Nat.le_of_lt_succ h2)
  have hframeMemCfg : frame ∈ cfg.stackWithIndex := frame_transport_down frame hframeMem hframeLt
  have hframeRidNeRidPrime : frame.regionId ≠ rid' := hridNe1 frame hframeMemCfg
  have hframeRidNeFrame1 : frame.regionId ≠ frame1.regionId := hridNeFrame1 frame hframeMemCfg hframeLt
  have hloc_cfg : (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) := by
    rw [oid_loc_rgn_iff_in_heap vcfg]
    rw [oid_loc_rgn_iff_in_heap vcfg'] at hloc
    obtain ⟨region1', hlookup1', hmem1'⟩ := hloc
    have hlookup1'' : cfg.heap.lookup frame.regionId = some region1' := by
      rw [hcfg'] at hlookup1'; dsimp only at hlookup1'
      rw [AList.lookup_insert_ne hframeRidNeFrame1, AList.lookup_erase_ne hframeRidNeRidPrime] at hlookup1'
      exact hlookup1'
    exact ⟨region1', hlookup1'', hmem1'⟩
  by_cases hframe'eq : frame'.index = cfg.stack.dropLast.length
  · -- frame' IS the merged (last) frame.
    rw [FrameReachable_iff_reflTransGen] at hreach
    obtain ⟨start, hroot, hrtg⟩ := hreach
    have hoidNeRidPrime : Reference.OId oid ≠ Reference.RId rid' := by intro hc; exact absurd hc (by simp)
    have hoidNeBridge : oid ≠ region'.bridgeObjectId := by
      intro hc
      subst hc
      have hbridgeMem : region' ∈ cfg.heap.regions := by
        unfold Heap.regions
        exact List.mem_map_of_mem (AList.lookup_mem_entries hregion')
      have hbridgeIn : region'.bridgeObjectId ∈ region'.objMap := vcfg.h1 region' hbridgeMem
      have hlocBridge : (Reference.OId region'.bridgeObjectId).loc? cfg = some (Location.Rgn rid') :=
        (oid_loc_rgn_iff_in_heap vcfg).mpr ⟨region', hregion', hbridgeIn⟩
      rw [hloc_cfg] at hlocBridge
      injection hlocBridge with hlocBridgeEq
      injection hlocBridgeEq with hlocBridgeEq
      exact hframeRidNeRidPrime hlocBridgeEq
    rcases hroot with ⟨Gf, hGfmem, hGfidx, var, hvar⟩ | ⟨Gf, hGfmem, hGfidx, region0, hlk0, hbridge0⟩
    · have hGfeq : Gf = { newFrame1 with index := cfg.stack.dropLast.length } :=
        swap_corollary_stackWithIndex_index_inj hGfmem hLf' (hGfidx.trans hframe'eq)
      rw [hGfeq] at hvar
      by_cases hveq : var = x
      · rw [hveq] at hvar
        rw [newFrame1_def] at hvar
        dsimp only at hvar
        rw [AList.lookup_insert] at hvar
        injection hvar with hvarEq
        rw [← hvarEq] at hrtg
        have hne2 : Reference.OId oid ≠ Reference.OId region'.bridgeObjectId := by
          intro hc; injection hc with hc; exact hoidNeBridge hc
        have hrtgDown : Relation.ReflTransGen (ReachableStep cfg) (Reference.OId region'.bridgeObjectId)
            (Reference.OId oid) := hchainTransportDown (by intro hc; exact absurd hc (by simp)) hrtg
        have hrtgRidPrime : Relation.ReflTransGen (ReachableStep cfg) (Reference.RId rid') (Reference.OId oid) :=
          (merge_ridPrime_reflTransGen_iff vcfg hregion' hclosed hoidNeRidPrime hne2).mpr hrtgDown
        have hFrameReach : FrameReachable cfg (cfg.stack.dropLast.length) (Reference.OId oid) :=
          (FrameReachable_iff_reflTransGen cfg (cfg.stack.dropLast.length) (Reference.OId oid)).mpr
            ⟨Reference.RId rid', Or.inl ⟨{ frame1 with index := cfg.stack.dropLast.length }, hlast1_mem, rfl, x,
              hxref⟩, hrtgRidPrime⟩
        have hresult_cfg : FrameReachable cfg frame.index (Reference.OId oid) :=
          hFR3 frame hframeMemCfg { frame1 with index := cfg.stack.dropLast.length } hlast1_mem hframeLt oid
            hloc_cfg hFrameReach
        exact (frameReachIffNe hframeLt (Reference.OId oid)).mp hresult_cfg
      · rw [newFrame1_def] at hvar
        dsimp only at hvar
        rw [AList.lookup_insert_ne hveq] at hvar
        have hstartne : start ≠ Reference.RId rid' := by
          intro hc
          rw [hc] at hvar
          exact merge_ridPrime_var_unique vcfg hframe1MemStack hxref hveq hvar
        have hrtgDown := hchainTransportDown hstartne hrtg
        have hFrameReach : FrameReachable cfg (cfg.stack.dropLast.length) (Reference.OId oid) :=
          (FrameReachable_iff_reflTransGen cfg (cfg.stack.dropLast.length) (Reference.OId oid)).mpr
            ⟨start, Or.inl ⟨{ frame1 with index := cfg.stack.dropLast.length }, hlast1_mem, rfl, var, hvar⟩,
              hrtgDown⟩
        have hresult_cfg : FrameReachable cfg frame.index (Reference.OId oid) :=
          hFR3 frame hframeMemCfg { frame1 with index := cfg.stack.dropLast.length } hlast1_mem hframeLt oid
            hloc_cfg hFrameReach
        exact (frameReachIffNe hframeLt (Reference.OId oid)).mp hresult_cfg
    · have hGfeq : Gf = { newFrame1 with index := cfg.stack.dropLast.length } :=
        swap_corollary_stackWithIndex_index_inj hGfmem hLf' (hGfidx.trans hframe'eq)
      rw [hGfeq, newFrame1_def] at hlk0
      dsimp only at hlk0
      rw [hcfg'] at hlk0
      dsimp only at hlk0
      rw [AList.lookup_insert] at hlk0
      injection hlk0 with hlk0Eq
      rw [← hlk0Eq] at hbridge0
      dsimp only at hbridge0
      have hstartne : start ≠ Reference.RId rid' := by rw [hbridge0]; intro hc; exact absurd hc (by simp)
      have hrtgDown := hchainTransportDown hstartne hrtg
      have hFrameReach : FrameReachable cfg (cfg.stack.dropLast.length) (Reference.OId oid) :=
        (FrameReachable_iff_reflTransGen cfg (cfg.stack.dropLast.length) (Reference.OId oid)).mpr
          ⟨start, Or.inr ⟨{ frame1 with index := cfg.stack.dropLast.length }, hlast1_mem, rfl, region1, hregion1,
            hbridge0⟩, hrtgDown⟩
      have hresult_cfg : FrameReachable cfg frame.index (Reference.OId oid) :=
        hFR3 frame hframeMemCfg { frame1 with index := cfg.stack.dropLast.length } hlast1_mem hframeLt oid
          hloc_cfg hFrameReach
      exact (frameReachIffNe hframeLt (Reference.OId oid)).mp hresult_cfg
  · -- frame' is not the merged frame: unconditional transport both ways.
    have h2 := hallLt frame' hframe'Mem
    have hframe'Lt : frame'.index < cfg.stack.dropLast.length :=
      lt_of_le_of_ne (Nat.le_of_lt_succ h2) hframe'eq
    have hreach_cfg : FrameReachable cfg frame'.index (Reference.OId oid) :=
      (frameReachIffNe hframe'Lt (Reference.OId oid)).mpr hreach
    have hresult_cfg : FrameReachable cfg frame.index (Reference.OId oid) :=
      hFR3 frame hframeMemCfg frame' (frame_transport_down frame' hframe'Mem hframe'Lt) hlt oid hloc_cfg hreach_cfg
    exact (frameReachIffNe hframeLt (Reference.OId oid)).mp hresult_cfg

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
