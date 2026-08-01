import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Mutation.Mutation
import Gc.Model.Mutation.Stmt
import Gc.Model.Preservation
import Gc.Reachability.Reachable.Semantics
import Gc.Reachability.Reachable.StackReachableInvariant.Def
import Gc.Reachability.Reachable.Lemmas

theorem stackReachable_invariant_enter (xf : FieldAccess) (bridgeVar : VarName) :
    StackReachable_invariant_for_suspended_region_objects (Stmt.enter xf bridgeVar) := by
  intro cfg cfg' vcfg h _hcr3 frame hframeMem hframeSusp oid hloc
  have h' : enter xf bridgeVar cfg = some cfg' := h
  have vcfg' : ValidConfig cfg' := enter_valid vcfg h'
  obtain ⟨rid, regionEntered, -, hlookupRid, hclosedRid, hcfg'⟩ := enter_cases h'
  obtain ⟨region, hlookup, hopen⟩ := l2_of_stackWithIndex vcfg hframeMem
  have hridNe : frame.regionId ≠ rid := enter_regionId_ne vcfg hframeMem hlookupRid hclosedRid
  have hlookup' : cfg'.heap.lookup frame.regionId = some region := by
    subst hcfg'; dsimp only; rw [AList.lookup_insert_ne hridNe]; exact hlookup
  have hloc' : (Reference.OId oid).loc? cfg' = some (Location.Rgn frame.regionId) := by
    rw [← enter_corollary_2 vcfg h' oid]; exact hloc
  constructor
  · -- forward: any pre-existing witness frame transports up unchanged.
    rintro ⟨G, hGmem, hGreach⟩
    rw [FrameReachable_iff_reflTransGen] at hGreach
    obtain ⟨start, hroot, hrtg⟩ := hGreach
    have hsafe : SafeRef cfg frame.regionId (Reference.OId oid) := Or.inl hloc
    have hrtg' : Relation.ReflTransGen (ReachableStep cfg') start (Reference.OId oid) :=
      safe_reflTransGen_transport vcfg hlookup hopen (enter_oid_step_iff vcfg h') hrtg hsafe
    have hroot' : FrameRoot cfg' G.index start := by
      rcases hroot with ⟨Gf, hGfmem, hGfidx, var, hvar⟩ | ⟨Gf, hGfmem, hGfidx, region', hlookupG, hbridge⟩
      · exact Or.inl ⟨Gf, enter_frame_mem_up h' hGfmem, hGfidx, var, hvar⟩
      · have hGfridNe : Gf.regionId ≠ rid := enter_regionId_ne vcfg hGfmem hlookupRid hclosedRid
        have hlookupG' : cfg'.heap.lookup Gf.regionId = some region' := by
          subst hcfg'; dsimp only; rw [AList.lookup_insert_ne hGfridNe]; exact hlookupG
        exact Or.inr ⟨Gf, enter_frame_mem_up h' hGfmem, hGfidx, region', hlookupG', hbridge⟩
    exact ⟨G, enter_frame_mem_up h' hGmem,
      (FrameReachable_iff_reflTransGen cfg' G.index (Reference.OId oid)).mpr ⟨start, hroot', hrtg'⟩⟩
  · -- backward: G is either pre-existing (transports down) or the fresh empty frame, whose only root is the entered region's bridge — unsafe.
    rintro ⟨G, hGmem, hGreach⟩
    rcases enter_frame_cases hcfg' hGmem with ⟨hGmemcfg, hGlt⟩ | ⟨hGregionId, -, hGvarMap, -, hGidx⟩
    · rw [FrameReachable_iff_reflTransGen] at hGreach
      obtain ⟨start, hroot, hrtg⟩ := hGreach
      have hsafe' : SafeRef cfg' frame.regionId (Reference.OId oid) := Or.inl hloc'
      have hrtg2 : Relation.ReflTransGen (ReachableStep cfg) start (Reference.OId oid) :=
        safe_reflTransGen_transport vcfg' hlookup' hopen (fun oid0 b => (enter_oid_step_iff vcfg h' oid0 b).symm)
          hrtg hsafe'
      have hroot2 : FrameRoot cfg G.index start := by
        rcases hroot with ⟨Gf, hGfmem, hGfidx, var, hvar⟩ | ⟨Gf, hGfmem, hGfidx, region', hlookupG, hbridge⟩
        · have hGflt : Gf.index < cfg.stack.length := hGfidx ▸ hGlt
          exact Or.inl ⟨Gf, enter_frame_mem_down h' hGfmem hGflt, hGfidx, var, hvar⟩
        · have hGflt : Gf.index < cfg.stack.length := hGfidx ▸ hGlt
          have hGfmemcfg : Gf ∈ cfg.stackWithIndex := enter_frame_mem_down h' hGfmem hGflt
          have hGfridNe : Gf.regionId ≠ rid := enter_regionId_ne vcfg hGfmemcfg hlookupRid hclosedRid
          have hlookupGcfg : cfg.heap.lookup Gf.regionId = some region' := by
            rw [hcfg'] at hlookupG; dsimp only at hlookupG
            rw [AList.lookup_insert_ne hGfridNe] at hlookupG; exact hlookupG
          exact Or.inr ⟨Gf, hGfmemcfg, hGfidx, region', hlookupGcfg, hbridge⟩
      exact ⟨G, hGmemcfg, (FrameReachable_iff_reflTransGen cfg G.index (Reference.OId oid)).mpr ⟨start, hroot2, hrtg2⟩⟩
    · exfalso
      rw [FrameReachable_iff_reflTransGen] at hGreach
      obtain ⟨start, hroot, hrtg⟩ := hGreach
      have hstart : start = Reference.OId regionEntered.bridgeObjectId := by
        rcases hroot with ⟨Gf, hGfmem, hGfidx, var, hvar⟩ | ⟨Gf, hGfmem, hGfidx, region', hlookupG, hbridge⟩
        · exfalso
          have hGfeqG : Gf = G := swap_corollary_stackWithIndex_index_inj hGfmem hGmem hGfidx
          rw [hGfeqG, hGvarMap] at hvar
          simp at hvar
        · have hGfeqG : Gf = G := swap_corollary_stackWithIndex_index_inj hGfmem hGmem hGfidx
          have hlookupG' : cfg'.heap.lookup rid = some { regionEntered with status := Status.Open } := by
            rw [hcfg']; dsimp only; rw [AList.lookup_insert]
          rw [hGfeqG, hGregionId, hlookupG'] at hlookupG
          injection hlookupG with hregionEq
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
      have hsafe : SafeRef cfg' frame.regionId (Reference.OId oid) := Or.inl hloc'
      have hsafeStart := safe_reflTransGen_root_safe vcfg' hlookup' hopen hrtg hsafe
      unfold SafeRef at hsafeStart
      rcases hsafeStart with hbad | ⟨fid, hbad⟩
      · rw [hbad] at hbridgeLoc
        injection hbridgeLoc with hbadEq
        injection hbadEq with hbadEq
        exact hridNe hbadEq
      · rw [hbad] at hbridgeLoc
        exact absurd hbridgeLoc (by simp)
