import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Mutation.Mutation
import Gc.Model.Mutation.Stmt
import Gc.Model.Preservation
import Gc.Reachability.Reachable.Semantics
import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.Def
import Gc.Reachability.Reachable.Lemmas

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
