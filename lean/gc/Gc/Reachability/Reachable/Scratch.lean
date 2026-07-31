import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Mutation.Mutation
import Gc.Model.Mutation.Stmt
import Gc.Model.Preservation
import Gc.Reachability.Reachable.Semantics
import Gc.Reachability.Reachable.Corollaries
import Gc.Reachability.Reachable.Lemmas

-- Per-operation skeletons, ordered easiest-to-hardest.

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
  · -- backward: witness frame G is either pre-existing (transports down) or the fresh
    -- empty frame, whose only possible root is the entered region's bridge -- unsafe.
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

theorem stackReachable_invariant_exit :
    StackReachable_invariant_for_suspended_region_objects Stmt.exit := by
  intro cfg cfg' vcfg h hcr3 frame hframeMem hframeSusp oid hloc
  have h' : exit cfg = some cfg' := h
  obtain ⟨poppedFrame, region0, hlen, hlast, hlookupRid, hopenRid, hcfg'⟩ := exit_cases h'
  obtain ⟨region, hlookup, hopen⟩ := l2_of_stackWithIndex vcfg hframeMem
  have hlenEq : cfg.stackWithIndex.length = cfg.stack.length := by
    unfold RuntimeConfig.stackWithIndex; rw [List.length_mapIdx]
  have hframeSusp' : frame.index < cfg.stack.length - 1 := by rw [← hlenEq]; exact hframeSusp
  have hridNe : frame.regionId ≠ poppedFrame.regionId := exit_regionId_ne vcfg hframeMem hframeSusp' hlast hlen
  have hlookup' : cfg'.heap.lookup frame.regionId = some region := by
    rw [hcfg']; dsimp only; rw [AList.lookup_insert_ne hridNe]; exact hlookup
  have hne_oid : (Reference.OId oid).loc? cfg ≠ some (Location.Stk (cfg.stack.length - 1)) := by
    rw [hloc]; simp
  have hloc' : (Reference.OId oid).loc? cfg' = some (Location.Rgn frame.regionId) := by
    rw [← exit_loc_eq_of_ne_popped vcfg h' oid hne_oid]; exact hloc
  constructor
  · -- forward: G = poppedFrame collapses to `frame` via the CR3-style hypothesis;
    -- any other G survives `exit` unchanged.
    rintro ⟨G, hGmem, hGreach⟩
    by_cases hGeq : G.index = cfg.stack.length - 1
    · have hlt : frame.index < G.index := by rw [hGeq]; exact hframeSusp'
      have hframeReach : FrameReachable cfg frame.index (Reference.OId oid) :=
        hcr3 frame hframeMem G hGmem hlt oid hloc hGreach
      have hframeReach' : FrameReachable cfg' frame.index (Reference.OId oid) :=
        exit_frame_reachable_transport vcfg h' hlast hlen hlookupRid hopenRid hcfg' hlookup hopen hloc
          hframeMem hframeSusp' hframeReach
      exact ⟨frame, exit_frame_mem_up h' hframeMem hframeSusp', hframeReach'⟩
    · have hGltlen : G.index < cfg.stack.length := by
        obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hGmem
        have hidx : G.index = n := by rw [← hfeq]
        rw [hidx]; exact hn
      have hGlt : G.index < cfg.stack.length - 1 :=
        lt_of_le_of_ne (Nat.le_sub_one_of_lt hGltlen) hGeq
      have hGreach' := exit_frame_reachable_transport vcfg h' hlast hlen hlookupRid hopenRid hcfg' hlookup hopen hloc
        hGmem hGlt hGreach
      exact ⟨G, exit_frame_mem_up h' hGmem hGlt, hGreach'⟩
  · -- backward: every `cfg'.stackWithIndex` member is automatically a surviving frame.
    rintro ⟨G, hGmem, hGreach⟩
    obtain ⟨hGmemcfg, hGlt⟩ := exit_frame_mem_down h' hGmem
    have hGreach2 := exit_frame_reachable_transport_backward vcfg h' hlast hlen hcfg' hlookup hlookup' hopen hloc'
      hGmem hGreach
    exact ⟨G, hGmemcfg, hGreach2⟩

theorem stackReachable_invariant_makeObjStack (x : VarName) :
    StackReachable_invariant_for_suspended_region_objects (Stmt.makeObjStack x) := by
  intro cfg cfg' vcfg h hcr3 frame hframeMem hframeSusp oid hloc
  have h' : makeObjStack x cfg = some cfg' := h
  obtain ⟨lastFrame, hlast, hcfg'⟩ := makeObjStack_cases h'
  have hlenEq : cfg.stackWithIndex.length = cfg.stack.length := by
    unfold RuntimeConfig.stackWithIndex; rw [List.length_mapIdx]
  have hframeSusp' : frame.index < cfg.stack.length - 1 := by rw [← hlenEq]; exact hframeSusp
  have hLf : ({ lastFrame with index := cfg.stack.length - 1 } : FrameWithIndex) ∈ cfg.stackWithIndex :=
    stackWithIndex_getLast_mem hlast
  have hlt : frame.index < ({ lastFrame with index := cfg.stack.length - 1 } : FrameWithIndex).index := hframeSusp'
  constructor
  · -- forward: G = last frame collapses to `frame` via the CR3-style hypothesis;
    -- any other G survives `makeObjStack` unchanged (content untouched below the last frame).
    rintro ⟨G, hGmem, hGreach⟩
    by_cases hGeq : G.index = cfg.stack.length - 1
    · have hlt' : frame.index < G.index := by rw [hGeq]; exact hframeSusp'
      have hframeReach : FrameReachable cfg frame.index (Reference.OId oid) :=
        hcr3 frame hframeMem G hGmem hlt' oid hloc hGreach
      have hframeReach' : FrameReachable cfg' frame.index (Reference.OId oid) :=
        (makeObjStack_frame_reachable_iff h' hframeMem hframeSusp' (Reference.OId oid)).mp hframeReach
      exact ⟨frame, makeObjStack_frame_mem_up h' hframeMem hframeSusp', hframeReach'⟩
    · have hGltlen : G.index < cfg.stack.length := by
        obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hGmem
        have hidx : G.index = n := by rw [← hfeq]
        rw [hidx]; exact hn
      have hGlt : G.index < cfg.stack.length - 1 :=
        lt_of_le_of_ne (Nat.le_sub_one_of_lt hGltlen) hGeq
      have hGreach' := (makeObjStack_frame_reachable_iff h' hGmem hGlt (Reference.OId oid)).mp hGreach
      exact ⟨G, makeObjStack_frame_mem_up h' hGmem hGlt, hGreach'⟩
  · -- backward: witness frame G is either pre-existing (transports down unchanged) or the
    -- mutated last frame, whose reachability chain either came from `lastFrame`'s own
    -- pre-existing roots (transported to `hcr3`) or was rooted at the fresh var/object
    -- itself, which resolves nowhere and so can't reach `oid` (whose location is known).
    rintro ⟨G, hGmem, hGreach⟩
    rcases makeObjStack_frame_cases hlast hcfg' hGmem with
      ⟨hGmemcfg, hGlt⟩ | ⟨hGregionId, -, hGvarMap, -, -⟩
    · exact ⟨G, hGmemcfg, (makeObjStack_frame_reachable_iff h' hGmemcfg hGlt (Reference.OId oid)).mpr hGreach⟩
    · rw [FrameReachable_iff_reflTransGen] at hGreach
      obtain ⟨start, hroot, hrtg⟩ := hGreach
      rw [← makeObjStack_step_eq h'] at hrtg
      have hLfReach : FrameReachable cfg (cfg.stack.length - 1) (Reference.OId oid) := by
        rcases hroot with ⟨Gf, hGfmem, hGfidx, var, hvar⟩ | ⟨Gf, hGfmem, hGfidx, region, hlookup, hbridge⟩
        · have hGfeqG : Gf = G := swap_corollary_stackWithIndex_index_inj hGfmem hGmem hGfidx
          rw [hGfeqG, hGvarMap] at hvar
          by_cases hveq : var = x
          · subst hveq
            rw [AList.lookup_insert] at hvar
            injection hvar with hstart
            exfalso
            rw [← hstart] at hrtg
            rcases hrtg.cases_head with heq | ⟨c, hstep, -⟩
            · rw [← heq] at hloc
              exact freshObjectId_loc_ne_rgn hloc
            · rw [ReachableStep_oid_iff] at hstep
              obtain ⟨obj, hobjAt, -⟩ := hstep
              rw [freshObjectId_objAt_none] at hobjAt
              exact absurd hobjAt (by simp)
          · rw [AList.lookup_insert_ne hveq] at hvar
            exact (FrameReachable_iff_reflTransGen cfg (cfg.stack.length - 1) (Reference.OId oid)).mpr
              ⟨start, Or.inl ⟨{ lastFrame with index := cfg.stack.length - 1 }, hLf, rfl, var, hvar⟩, hrtg⟩
        · have hGfeqG : Gf = G := swap_corollary_stackWithIndex_index_inj hGfmem hGmem hGfidx
          have hlookup' : cfg.heap.lookup Gf.regionId = some region := by rw [hcfg'] at hlookup; exact hlookup
          rw [hGfeqG, hGregionId] at hlookup'
          exact (FrameReachable_iff_reflTransGen cfg (cfg.stack.length - 1) (Reference.OId oid)).mpr
            ⟨start, Or.inr ⟨{ lastFrame with index := cfg.stack.length - 1 }, hLf, rfl, region, hlookup', hbridge⟩, hrtg⟩
      exact ⟨frame, hframeMem, hcr3 frame hframeMem _ hLf hlt oid hloc hLfReach⟩

theorem stackReachable_invariant_makeObjRegion (x : VarName) :
    StackReachable_invariant_for_suspended_region_objects (Stmt.makeObjRegion x) := by
  intro cfg cfg' vcfg h hcr3 frame hframeMem hframeSusp oid hloc
  have h' : makeObjRegion x cfg = some cfg' := h
  obtain ⟨lastFrame, region0, hlast, hlookupRid0, hopen0, hcfg'⟩ := makeObjRegion_cases h'
  have hlenEq : cfg.stackWithIndex.length = cfg.stack.length := by
    unfold RuntimeConfig.stackWithIndex; rw [List.length_mapIdx]
  have hframeSusp' : frame.index < cfg.stack.length - 1 := by rw [← hlenEq]; exact hframeSusp
  have hLf : ({ lastFrame with index := cfg.stack.length - 1 } : FrameWithIndex) ∈ cfg.stackWithIndex :=
    stackWithIndex_getLast_mem hlast
  have hlt : frame.index < ({ lastFrame with index := cfg.stack.length - 1 } : FrameWithIndex).index := hframeSusp'
  constructor
  · -- forward: G = last frame collapses to `frame` via the CR3-style hypothesis;
    -- any other G survives `makeObjRegion` unchanged (content untouched below the last frame).
    rintro ⟨G, hGmem, hGreach⟩
    by_cases hGeq : G.index = cfg.stack.length - 1
    · have hlt' : frame.index < G.index := by rw [hGeq]; exact hframeSusp'
      have hframeReach : FrameReachable cfg frame.index (Reference.OId oid) :=
        hcr3 frame hframeMem G hGmem hlt' oid hloc hGreach
      have hframeReach' : FrameReachable cfg' frame.index (Reference.OId oid) :=
        (makeObjRegion_frame_reachable_iff vcfg h' hframeMem hframeSusp' (Reference.OId oid)).mp hframeReach
      exact ⟨frame, makeObjRegion_frame_mem_up h' hframeMem hframeSusp', hframeReach'⟩
    · have hGltlen : G.index < cfg.stack.length := by
        obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hGmem
        have hidx : G.index = n := by rw [← hfeq]
        rw [hidx]; exact hn
      have hGlt : G.index < cfg.stack.length - 1 :=
        lt_of_le_of_ne (Nat.le_sub_one_of_lt hGltlen) hGeq
      have hGreach' := (makeObjRegion_frame_reachable_iff vcfg h' hGmem hGlt (Reference.OId oid)).mp hGreach
      exact ⟨G, makeObjRegion_frame_mem_up h' hGmem hGlt, hGreach'⟩
  · -- backward: witness frame G is either pre-existing (transports down unchanged) or the
    -- mutated last frame, whose reachability chain either came from `lastFrame`'s own
    -- pre-existing roots (transported to `hcr3`) or was rooted at the fresh var itself, which
    -- resolves nowhere in `cfg` and so can't reach `oid` (whose location is already known).
    rintro ⟨G, hGmem, hGreach⟩
    rcases makeObjRegion_frame_cases h' hGmem with
      ⟨hGmemcfg, hGlt⟩ | ⟨lf, hlf, hGregionId, -, -, hGvarMap, -⟩
    · exact ⟨G, hGmemcfg, (makeObjRegion_frame_reachable_iff vcfg h' hGmemcfg hGlt (Reference.OId oid)).mpr hGreach⟩
    · rw [hlast] at hlf
      injection hlf with hlf
      subst hlf
      rw [FrameReachable_iff_reflTransGen] at hGreach
      obtain ⟨start, hroot, hrtg⟩ := hGreach
      rw [← makeObjRegion_step_eq vcfg h'] at hrtg
      have hLfReach : FrameReachable cfg (cfg.stack.length - 1) (Reference.OId oid) := by
        rcases hroot with ⟨Gf, hGfmem, hGfidx, var, hvar⟩ | ⟨Gf, hGfmem, hGfidx, regionX, hlookup, hbridge⟩
        · have hGfeqG : Gf = G := swap_corollary_stackWithIndex_index_inj hGfmem hGmem hGfidx
          rw [hGfeqG, hGvarMap] at hvar
          by_cases hveq : var = x
          · subst hveq
            rw [AList.lookup_insert] at hvar
            injection hvar with hstart
            exfalso
            rw [← hstart] at hrtg
            rcases hrtg.cases_head with heq | ⟨c, hstep, -⟩
            · rw [← heq] at hloc
              exact freshObjectId_loc_ne_rgn hloc
            · rw [ReachableStep_oid_iff] at hstep
              obtain ⟨obj, hobjAt, -⟩ := hstep
              rw [freshObjectId_objAt_none] at hobjAt
              exact absurd hobjAt (by simp)
          · rw [AList.lookup_insert_ne hveq] at hvar
            exact (FrameReachable_iff_reflTransGen cfg (cfg.stack.length - 1) (Reference.OId oid)).mpr
              ⟨start, Or.inl ⟨{ lastFrame with index := cfg.stack.length - 1 }, hLf, rfl, var, hvar⟩, hrtg⟩
        · have hGfeqG : Gf = G := swap_corollary_stackWithIndex_index_inj hGfmem hGmem hGfidx
          have hGfridEq : Gf.regionId = lastFrame.regionId := by rw [hGfeqG]; exact hGregionId
          have hlookup' : cfg'.heap.lookup Gf.regionId =
              some { region0 with objMap := region0.objMap.insert cfg.freshObjectId ∅ } := by
            rw [hGfridEq, hcfg']; dsimp only; rw [AList.lookup_insert]
          rw [hlookup'] at hlookup
          injection hlookup with hlookupEq
          rw [← hlookupEq] at hbridge
          dsimp only at hbridge
          exact (FrameReachable_iff_reflTransGen cfg (cfg.stack.length - 1) (Reference.OId oid)).mpr
            ⟨start, Or.inr ⟨{ lastFrame with index := cfg.stack.length - 1 }, hLf, rfl, region0, hlookupRid0, hbridge⟩,
              hrtg⟩
      exact ⟨frame, hframeMem, hcr3 frame hframeMem _ hLf hlt oid hloc hLfReach⟩

theorem stackReachable_invariant_makeRegion (x : VarName) :
    StackReachable_invariant_for_suspended_region_objects (Stmt.makeRegion x) := by
  intro cfg cfg' vcfg h hcr3 frame hframeMem hframeSusp oid hloc
  have h' : makeRegion x cfg = some cfg' := h
  obtain ⟨lastFrame, hlast, hcfg'⟩ := makeRegion_cases h'
  obtain ⟨region0, hlookupRid0, hopen0⟩ := l2_of_stackWithIndex vcfg (stackWithIndex_getLast_mem hlast)
  have hlenEq : cfg.stackWithIndex.length = cfg.stack.length := by
    unfold RuntimeConfig.stackWithIndex; rw [List.length_mapIdx]
  have hframeSusp' : frame.index < cfg.stack.length - 1 := by rw [← hlenEq]; exact hframeSusp
  have hLf : ({ lastFrame with index := cfg.stack.length - 1 } : FrameWithIndex) ∈ cfg.stackWithIndex :=
    stackWithIndex_getLast_mem hlast
  have hlt : frame.index < ({ lastFrame with index := cfg.stack.length - 1 } : FrameWithIndex).index := hframeSusp'
  constructor
  · -- forward: G = last frame collapses to `frame` via the CR3-style hypothesis;
    -- any other G survives `makeRegion` unchanged (content untouched below the last frame).
    rintro ⟨G, hGmem, hGreach⟩
    by_cases hGeq : G.index = cfg.stack.length - 1
    · have hlt' : frame.index < G.index := by rw [hGeq]; exact hframeSusp'
      have hframeReach : FrameReachable cfg frame.index (Reference.OId oid) :=
        hcr3 frame hframeMem G hGmem hlt' oid hloc hGreach
      have hframeReach' : FrameReachable cfg' frame.index (Reference.OId oid) :=
        (makeRegion_frame_reachable_iff vcfg h' hframeMem hframeSusp' (Reference.OId oid)).mp hframeReach
      exact ⟨frame, makeRegion_frame_mem_up h' hframeMem hframeSusp', hframeReach'⟩
    · have hGltlen : G.index < cfg.stack.length := by
        obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hGmem
        have hidx : G.index = n := by rw [← hfeq]
        rw [hidx]; exact hn
      have hGlt : G.index < cfg.stack.length - 1 :=
        lt_of_le_of_ne (Nat.le_sub_one_of_lt hGltlen) hGeq
      have hGreach' := (makeRegion_frame_reachable_iff vcfg h' hGmem hGlt (Reference.OId oid)).mp hGreach
      exact ⟨G, makeRegion_frame_mem_up h' hGmem hGlt, hGreach'⟩
  · -- backward: witness frame G is either pre-existing (transports down unchanged) or the
    -- mutated last frame, whose reachability chain either came from `lastFrame`'s own
    -- pre-existing roots (transported to `hcr3`) or was rooted at the fresh var itself, which
    -- resolves nowhere in `cfg` (the fresh region doesn't exist yet) and so can't reach `oid`.
    rintro ⟨G, hGmem, hGreach⟩
    rcases makeRegion_frame_cases h' hGmem with
      ⟨hGmemcfg, hGlt⟩ | ⟨lf, hlf, hGregionId, -, -, hGvarMap, -⟩
    · exact ⟨G, hGmemcfg, (makeRegion_frame_reachable_iff vcfg h' hGmemcfg hGlt (Reference.OId oid)).mpr hGreach⟩
    · rw [hlast] at hlf
      injection hlf with hlf
      subst hlf
      rw [FrameReachable_iff_reflTransGen] at hGreach
      obtain ⟨start, hroot, hrtg⟩ := hGreach
      rw [← makeRegion_step_eq vcfg h'] at hrtg
      have hLfReach : FrameReachable cfg (cfg.stack.length - 1) (Reference.OId oid) := by
        rcases hroot with ⟨Gf, hGfmem, hGfidx, var, hvar⟩ | ⟨Gf, hGfmem, hGfidx, regionX, hlookup, hbridge⟩
        · have hGfeqG : Gf = G := swap_corollary_stackWithIndex_index_inj hGfmem hGmem hGfidx
          rw [hGfeqG, hGvarMap] at hvar
          by_cases hveq : var = x
          · subst hveq
            rw [AList.lookup_insert] at hvar
            injection hvar with hstart
            exfalso
            rw [← hstart] at hrtg
            rcases hrtg.cases_head with heq | ⟨c, hstep, -⟩
            · cases heq
            · exact absurd hstep freshRegionId_no_step
          · rw [AList.lookup_insert_ne hveq] at hvar
            exact (FrameReachable_iff_reflTransGen cfg (cfg.stack.length - 1) (Reference.OId oid)).mpr
              ⟨start, Or.inl ⟨{ lastFrame with index := cfg.stack.length - 1 }, hLf, rfl, var, hvar⟩, hrtg⟩
        · have hGfeqG : Gf = G := swap_corollary_stackWithIndex_index_inj hGfmem hGmem hGfidx
          have hGfridEq : Gf.regionId = lastFrame.regionId := by rw [hGfeqG]; exact hGregionId
          have hne : Gf.regionId ≠ cfg.freshRegionId := by
            rw [hGfridEq]
            intro heq
            apply RuntimeConfig.freshRegionId_not_mem cfg
            rw [← AList.mem_keys, ← AList.lookup_isSome, ← heq, hlookupRid0]
            simp
          have hlookup' : cfg'.heap.lookup Gf.regionId = cfg.heap.lookup Gf.regionId := by
            rw [hcfg']; dsimp only; rw [AList.lookup_insert_ne hne]
          rw [hlookup', hGfridEq] at hlookup
          exact (FrameReachable_iff_reflTransGen cfg (cfg.stack.length - 1) (Reference.OId oid)).mpr
            ⟨start, Or.inr ⟨{ lastFrame with index := cfg.stack.length - 1 }, hLf, rfl, regionX, hlookup, hbridge⟩,
              hrtg⟩
      exact ⟨frame, hframeMem, hcr3 frame hframeMem _ hLf hlt oid hloc hLfReach⟩

theorem stackReachable_invariant_merge (x : VarName) :
    StackReachable_invariant_for_suspended_region_objects (Stmt.merge x) := by
  sorry

theorem stackReachable_invariant_varAsgn (x : VarName) (yf : FieldAccess) :
    StackReachable_invariant_for_suspended_region_objects (Stmt.varAsgn x yf) := by
  intro cfg cfg' vcfg h _hcr3 frame hframeMem hframeSusp oid hloc
  have h' : varAsgn x yf cfg = some cfg' := h
  obtain ⟨lastFrame, hlast, hcase⟩ := varAsgn_cases h'
  have hlenEq : cfg.stackWithIndex.length = cfg.stack.length := by
    unfold RuntimeConfig.stackWithIndex; rw [List.length_mapIdx]
  have hframeSusp' : frame.index < cfg.stack.length - 1 := by rw [← hlenEq]; exact hframeSusp
  have hLf : ({ lastFrame with index := cfg.stack.length - 1 } : FrameWithIndex) ∈ cfg.stackWithIndex :=
    stackWithIndex_getLast_mem hlast
  have hstep_eq : ReachableStep cfg = ReachableStep cfg' := varAsgn_step_eq vcfg h'
  have hstackLenEq : cfg.stack.length = cfg'.stack.length := by
    rcases hcase with ⟨oidY, rid, region, hyf, hxb, hlocY, hridEq, hregion, hcfg'⟩ | ⟨oidY, hyf, hxb, hresolve, hcfg'⟩
    · rw [hcfg']
    · have hstackEq : cfg.stack = cfg.stack.dropLast ++ [lastFrame] :=
        (List.dropLast_append_getLast? lastFrame hlast).symm
      rw [hcfg']
      dsimp only
      conv_lhs => rw [hstackEq]
      simp
  constructor
  · -- forward: G = last frame needs per-branch handling (bridge disjunct is either confined away
    -- or transports directly; var disjunct transports, possibly to a new witness frame in the
    -- fresh-var branch); any other G survives via `varAsgn_frame_reachable_iff`.
    rintro ⟨G, hGmem, hGreach⟩
    by_cases hGeq : G.index = cfg.stack.length - 1
    · rw [FrameReachable_iff_reflTransGen] at hGreach
      obtain ⟨start, hroot, hrtg⟩ := hGreach
      rw [hstep_eq] at hrtg
      have hGeqLf : G = { lastFrame with index := cfg.stack.length - 1 } :=
        swap_corollary_stackWithIndex_index_inj hGmem hLf hGeq
      rcases hroot with ⟨Gf, hGfmem, hGfidx, var, hvar⟩ | ⟨Gf, hGfmem, hGfidx, regionG, hlookupG, hbridge⟩
      · have hGfeqG : Gf = G := swap_corollary_stackWithIndex_index_inj hGfmem hGmem hGfidx
        have hGfeqLf : Gf = { lastFrame with index := cfg.stack.length - 1 } := by rw [hGfeqG, hGeqLf]
        rcases hcase with
            ⟨oidY, rid, region, hyf, hxb, hlocY, hridEq, hregion, hcfg'⟩ |
            ⟨oidY, hyf, hxb, hresolve, hcfg'⟩
        · have hstackEq : cfg'.stack = cfg.stack := by rw [hcfg']
          have hGmem' : G ∈ cfg'.stackWithIndex := by
            unfold RuntimeConfig.stackWithIndex at hGmem ⊢; rw [hstackEq]; exact hGmem
          have hvar' : G.varMap.lookup var = some start := by rw [hGfeqG] at hvar; exact hvar
          exact ⟨G, hGmem', (FrameReachable_iff_reflTransGen cfg' G.index (Reference.OId oid)).mpr
            ⟨start, Or.inl ⟨G, hGmem', rfl, var, hvar'⟩, hrtg⟩⟩
        · by_cases hveq : var = x
          · exfalso
            have hfresh : x ∉ lastFrame.varMap.keys := varAsgn_corollary_fresh_not_in_frame hlast hresolve
            rw [hGfeqLf, hveq] at hvar
            exact hfresh (AList.mem_keys.mpr (AList.lookup_isSome.mp (Option.isSome_iff_exists.mpr ⟨start, hvar⟩)))

          · have hnewMem := varAsgn_freshvar_last_mem hlast hcfg'
            set newLastFrame : FrameWithIndex := { lastFrame with varMap := lastFrame.varMap.insert x (Reference.OId oidY), index := cfg.stack.length - 1 } with newLastFrame_def
            have hnewVar : newLastFrame.varMap.lookup var = some start := by
              rw [newLastFrame_def]
              dsimp only
              rw [AList.lookup_insert_ne hveq]
              rw [hGfeqLf] at hvar
              exact hvar
            exact ⟨_, hnewMem, (FrameReachable_iff_reflTransGen cfg' newLastFrame.index (Reference.OId oid)).mpr
              ⟨start, Or.inl ⟨_, hnewMem, rfl, var, hnewVar⟩, hrtg⟩⟩
      · have hGfeqG : Gf = G := swap_corollary_stackWithIndex_index_inj hGfmem hGmem hGfidx
        have hGfeqLf : Gf = { lastFrame with index := cfg.stack.length - 1 } := by rw [hGfeqG, hGeqLf]
        rcases hcase with
            ⟨oidY, rid, region, hyf, hxb, hlocY, hridEq, hregion, hcfg'⟩ |
            ⟨oidY, hyf, hxb, hresolve, hcfg'⟩
        · -- bridge-var branch, G = last frame's own bridge: confinement rules this out, since
          -- `oid` lives in the SUSPENDED region `frame.regionId`, distinct (S1) from `rid`.
          exfalso
          have hGfridEq : Gf.regionId = rid := by rw [hGfeqLf]; dsimp only; exact hridEq
          rw [hGfridEq] at hlookupG
          rw [hregion] at hlookupG
          injection hlookupG with hlookupGEq
          rw [← hlookupGEq] at hbridge
          rw [hbridge, ← hstep_eq] at hrtg
          have hrr : RegionReachable cfg rid (Reference.OId oid) :=
            (RegionReachable_iff_reflTransGen cfg rid (Reference.OId oid)).mpr ⟨region, hregion, hrtg⟩
          obtain ⟨regionF, hlkF, hopenF⟩ := l2_of_stackWithIndex vcfg hframeMem
          have hneRid : frame.regionId ≠ rid := by
            rw [← hridEq]; exact varAsgn_regionId_ne vcfg hframeMem hframeSusp' hlast
          exact region_reachable_open_ne_absurd vcfg hregion hloc hlkF hopenF hneRid hrr
        · -- fresh-var branch: heap untouched, so the bridge value transports directly; the
          -- witness frame is the *new* last frame (G's own record with the old varMap is gone).
          have hlookupG' : cfg'.heap.lookup Gf.regionId = some regionG := by rw [hcfg']; exact hlookupG
          have hnewMem := varAsgn_freshvar_last_mem hlast hcfg'
          set newLastFrame : FrameWithIndex := { lastFrame with varMap := lastFrame.varMap.insert x (Reference.OId oidY), index := cfg.stack.length - 1 } with newLastFrame_def
          have hnewRegionEq : newLastFrame.regionId = Gf.regionId := by
            rw [newLastFrame_def]; dsimp only; rw [hGfeqLf]
          have hlookupNew : cfg'.heap.lookup newLastFrame.regionId = some regionG := by
            rw [hnewRegionEq]; exact hlookupG'
          exact ⟨_, hnewMem, (FrameReachable_iff_reflTransGen cfg' newLastFrame.index (Reference.OId oid)).mpr
            ⟨start, Or.inr ⟨_, hnewMem, rfl, regionG, hlookupNew, hbridge⟩, hrtg⟩⟩
    · have hGltlen : G.index < cfg.stack.length := by
        obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hGmem
        have hidx : G.index = n := by rw [← hfeq]
        rw [hidx]; exact hn
      have hGlt : G.index < cfg.stack.length - 1 :=
        lt_of_le_of_ne (Nat.le_sub_one_of_lt hGltlen) hGeq
      have hGreach' := (varAsgn_frame_reachable_iff vcfg h' hGmem hGlt (Reference.OId oid)).mp hGreach
      exact ⟨G, (varAsgn_frame_mem_iff h' hGlt).mp hGmem, hGreach'⟩
  · -- backward: symmetric, but the "new root" in each branch is always a *pre-existing*
    -- reference (never a fresh id), so it's handled by tracing its own provenance via
    -- `resolveFA_frameReach` rather than by recursing into `hcr3`.
    rintro ⟨G, hGmem, hGreach⟩
    by_cases hGeq : G.index = cfg.stack.length - 1
    · rw [FrameReachable_iff_reflTransGen] at hGreach
      obtain ⟨start, hroot, hrtg⟩ := hGreach
      rw [← hstep_eq] at hrtg
      rcases hcase with
          ⟨oidY, rid, region, hyf, hxb, hlocY, hridEq, hregion, hcfg'⟩ |
          ⟨oidY, hyf, hxb, hresolve, hcfg'⟩
      · have hstackEq : cfg'.stack = cfg.stack := by rw [hcfg']
        have hGmemCfg : G ∈ cfg.stackWithIndex := by
          unfold RuntimeConfig.stackWithIndex at hGmem ⊢; rw [hstackEq] at hGmem; exact hGmem
        rcases hroot with ⟨Gf, hGfmem, hGfidx, var, hvar⟩ | ⟨Gf, hGfmem, hGfidx, regionG, hlookupG, hbridge⟩
        · have hGfmemCfg : Gf ∈ cfg.stackWithIndex := by
            unfold RuntimeConfig.stackWithIndex at hGfmem ⊢; rw [hstackEq] at hGfmem; exact hGfmem
          exact ⟨G, hGmemCfg, (FrameReachable_iff_reflTransGen cfg G.index (Reference.OId oid)).mpr
            ⟨start, Or.inl ⟨Gf, hGfmemCfg, hGfidx, var, hvar⟩, hrtg⟩⟩
        · have hGfmemCfg : Gf ∈ cfg.stackWithIndex := by
            unfold RuntimeConfig.stackWithIndex at hGfmem ⊢; rw [hstackEq] at hGfmem; exact hGfmem
          by_cases heqrid : Gf.regionId = rid
          · have hlookupG' : cfg'.heap.lookup Gf.regionId = some ({ region with bridgeObjectId := oidY } : Region) := by
              rw [heqrid, hcfg']; dsimp only; rw [AList.lookup_insert]
            rw [hlookupG'] at hlookupG
            injection hlookupG with hlookupGEq
            rw [← hlookupGEq] at hbridge
            dsimp only at hbridge
            obtain ⟨frameY, hframeYmem, hreachY⟩ := resolveFA_frameReach hyf
            rw [FrameReachable_iff_reflTransGen] at hreachY
            obtain ⟨startY, hrootY, hrtgY⟩ := hreachY
            rw [hbridge] at hrtg
            exact ⟨frameY, hframeYmem, (FrameReachable_iff_reflTransGen cfg frameY.index (Reference.OId oid)).mpr
              ⟨startY, hrootY, hrtgY.trans hrtg⟩⟩
          · have hlookupG' : cfg.heap.lookup Gf.regionId = some regionG := by
              rw [hcfg'] at hlookupG; dsimp only at hlookupG
              rw [AList.lookup_insert_ne heqrid] at hlookupG; exact hlookupG
            exact ⟨G, hGmemCfg, (FrameReachable_iff_reflTransGen cfg G.index (Reference.OId oid)).mpr
              ⟨start, Or.inr ⟨Gf, hGfmemCfg, hGfidx, regionG, hlookupG', hbridge⟩, hrtg⟩⟩
      · have hnewMem := varAsgn_freshvar_last_mem hlast hcfg'
        set newLastFrame : FrameWithIndex := { lastFrame with varMap := lastFrame.varMap.insert x (Reference.OId oidY), index := cfg.stack.length - 1 } with newLastFrame_def
        have hGeqNew : G = newLastFrame := swap_corollary_stackWithIndex_index_inj hGmem hnewMem hGeq
        rcases hroot with ⟨Gf, hGfmem, hGfidx, var, hvar⟩ | ⟨Gf, hGfmem, hGfidx, regionG, hlookupG, hbridge⟩
        · have hGfeqG : Gf = G := swap_corollary_stackWithIndex_index_inj hGfmem hGmem hGfidx
          rw [hGfeqG, hGeqNew, newLastFrame_def] at hvar
          dsimp only at hvar
          by_cases hveq : var = x
          · rw [hveq, AList.lookup_insert] at hvar
            injection hvar with hstartEq
            subst hstartEq
            obtain ⟨frameY, hframeYmem, hreachY⟩ := resolveFA_frameReach hyf
            rw [FrameReachable_iff_reflTransGen] at hreachY
            obtain ⟨startY, hrootY, hrtgY⟩ := hreachY
            exact ⟨frameY, hframeYmem, (FrameReachable_iff_reflTransGen cfg frameY.index (Reference.OId oid)).mpr
              ⟨startY, hrootY, hrtgY.trans hrtg⟩⟩
          · rw [AList.lookup_insert_ne hveq] at hvar
            exact ⟨_, hLf, (FrameReachable_iff_reflTransGen cfg (cfg.stack.length - 1) (Reference.OId oid)).mpr
              ⟨start, Or.inl ⟨_, hLf, rfl, var, hvar⟩, hrtg⟩⟩
        · have hGfeqG : Gf = G := swap_corollary_stackWithIndex_index_inj hGfmem hGmem hGfidx
          have hlookupG' : cfg.heap.lookup Gf.regionId = some regionG := by rw [hcfg'] at hlookupG; exact hlookupG
          have hGfRegionEq : Gf.regionId = lastFrame.regionId := by rw [hGfeqG, hGeqNew, newLastFrame_def]
          exact ⟨_, hLf, (FrameReachable_iff_reflTransGen cfg (cfg.stack.length - 1) (Reference.OId oid)).mpr
            ⟨start, Or.inr ⟨_, hLf, rfl, regionG, hGfRegionEq ▸ hlookupG', hbridge⟩, hrtg⟩⟩
    · have hGltlen : G.index < cfg.stack.length := by
        obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hGmem
        have hidx : G.index = n := by rw [← hfeq]
        rw [hidx, hstackLenEq]; exact hn
      have hGlt : G.index < cfg.stack.length - 1 :=
        lt_of_le_of_ne (Nat.le_sub_one_of_lt hGltlen) hGeq
      have hGmemCfg := (varAsgn_frame_mem_iff h' hGlt).mpr hGmem
      have hGreach' := (varAsgn_frame_reachable_iff vcfg h' hGmemCfg hGlt (Reference.OId oid)).mpr hGreach
      exact ⟨G, hGmemCfg, hGreach'⟩

theorem stackReachable_invariant_fieldAsgn (xf : FieldAccess) (y : VarName) :
    StackReachable_invariant_for_suspended_region_objects (Stmt.fieldAsgn xf y) := by
  intro cfg cfg' vcfg h hcr3 frame hframeMem hframeSusp oid hloc
  have h' : fieldAsgn xf y cfg = some cfg' := h
  obtain ⟨oidC, hxrC, hstepIffOfNe⟩ := fieldAsgn_step_iff_of_ne vcfg h'
  have hframeRootIff := fieldAsgn_frame_root_iff h'
  have vcfg' : ValidConfig cfg' := fieldAsgn_valid vcfg h'
  obtain ⟨activeFrame, hactive, hcase⟩ := fieldAsgn_cases h'
  obtain ⟨stack_eq, hactiveidx⟩ := fieldAsgn_corollary_stack_eq hactive
  have hlenEq : cfg.stackWithIndex.length = cfg.stack.length := by
    unfold RuntimeConfig.stackWithIndex; rw [List.length_mapIdx]
  have hactiveidx' : activeFrame.index = cfg.stackWithIndex.length - 1 := by
    rw [hactiveidx, hlenEq, List.length_dropLast]
  have hframeSusp' : frame.index < activeFrame.index := by rw [hactiveidx']; exact hframeSusp
  have hframeLastA : cfg.stack.getLast? = some activeFrame.toFrame := by rw [stack_eq]; simp
  have hactivemem : activeFrame ∈ cfg.stackWithIndex := by
    have hm := stackWithIndex_getLast_mem hframeLastA
    have hidxeq : cfg.stack.length - 1 = activeFrame.index := by rw [hactiveidx, List.length_dropLast]
    rw [hidxeq] at hm
    exact hm
  have hstackLenEq' : cfg.stackWithIndex.length = cfg'.stackWithIndex.length := by
    unfold RuntimeConfig.stackWithIndex
    rw [List.length_mapIdx, List.length_mapIdx]
    rcases hcase with
        ⟨oid0, oid_y, obj, hxr0, hyr, hlocC, hobj, hcfg'⟩ |
        ⟨oid0, oid_y, rid, region, obj, hxr0, hyr, hlocC, hregion, hobj, hyloc, hstatus, hfrid, hcfg'⟩
    · have hlenA : cfg.stack.length = cfg.stack.dropLast.length + 1 := by
        conv_lhs => rw [stack_eq]
        rw [List.length_append, List.length_cons, List.length_nil]
      rw [hcfg']
      dsimp only
      rw [List.length_append, List.length_cons, List.length_nil]
      omega
    · rw [hcfg']
  have hactiveidx'' : activeFrame.index = cfg'.stackWithIndex.length - 1 := by
    rw [hactiveidx', hstackLenEq']
  have hOwnerBoundCfg : ∀ fid, FrameReachable cfg fid (Reference.OId oidC) → activeFrame.index ≤ fid := by
    rcases hcase with
        ⟨oid0, oid_y, obj, hxr0, hyr, hlocC, hobj, hcfg'⟩ |
        ⟨oid0, oid_y, rid, region, obj, hxr0, hyr, hlocC, hregion, hobj, hyloc, hstatus, hfrid, hcfg'⟩
    · have hoideq : oidC = oid0 := by
        have hcomb := hxrC.symm.trans hxr0
        injection hcomb with hcomb2
        injection hcomb2
      subst hoideq
      intro fid hreach
      exact fieldAsgn_stack_container_confined vcfg hlocC hreach
    · have hoideq : oidC = oid0 := by
        have hcomb := hxrC.symm.trans hxr0
        injection hcomb with hcomb2
        injection hcomb2
      subst hoideq
      intro fid hreach
      exact fieldAsgn_region_container_confined vcfg hregion hstatus hactivemem hfrid.symm hlocC hreach
  have hOwnerBoundCfg' : ∀ fid, FrameReachable cfg' fid (Reference.OId oidC) → activeFrame.index ≤ fid := by
    rcases hcase with
        ⟨oid0, oid_y, obj, hxr0, hyr, hlocC, hobj, hcfg'⟩ |
        ⟨oid0, oid_y, rid, region, obj, hxr0, hyr, hlocC, hregion, hobj, hyloc, hstatus, hfrid, hcfg'⟩
    · have hoideq : oidC = oid0 := by
        have hcomb := hxrC.symm.trans hxr0
        injection hcomb with hcomb2
        injection hcomb2
      subst hoideq
      have hlocC' : (Reference.OId oidC).loc? cfg' = some (Location.Stk activeFrame.index) := by
        rw [hcfg', ← fieldAsgn_corollary_stack_loc_eq hactive hobj]
        exact hlocC
      intro fid hreach
      exact fieldAsgn_stack_container_confined vcfg' hlocC' hreach
    · have hoideq : oidC = oid0 := by
        have hcomb := hxrC.symm.trans hxr0
        injection hcomb with hcomb2
        injection hcomb2
      subst hoideq
      have hlocC' : (Reference.OId oidC).loc? cfg' = some (Location.Rgn rid) := by
        rw [hcfg', ← fieldAsgn_corollary_region_loc_eq vcfg hregion hobj]
        exact hlocC
      have hactivemem' : activeFrame ∈ cfg'.stackWithIndex := by
        have hstackEq : cfg'.stack = cfg.stack := by rw [hcfg']
        unfold RuntimeConfig.stackWithIndex
        rw [hstackEq]
        exact hactivemem
      have hregion' : cfg'.heap.lookup rid = some
          ({ region with objMap := region.objMap.insert oidC (obj.insert xf.field (Reference.OId oid_y)) } : Region) := by
        rw [hcfg']
        dsimp only
        rw [AList.lookup_insert]
      intro fid hreach
      exact fieldAsgn_region_container_confined vcfg' hregion' hstatus hactivemem' hfrid.symm hlocC' hreach
  have hframemem' : frame ∈ cfg'.stackWithIndex :=
    (fieldAsgn_frame_mem_iff h' hframeSusp' hactiveidx).mp hframeMem
  have hlocSusp' : (Reference.OId oid).loc? cfg' = some (Location.Rgn frame.regionId) := by
    rcases hcase with
        ⟨oid0, oid_y, obj, hxr0, hyr, hlocC, hobj, hcfg'⟩ |
        ⟨oid0, oid_y, rid, region, obj, hxr0, hyr, hlocC, hregion, hobj, hyloc, hstatus, hfrid, hcfg'⟩
    · rw [hcfg', ← fieldAsgn_corollary_stack_loc_eq hactive hobj]; exact hloc
    · rw [hcfg', ← fieldAsgn_corollary_region_loc_eq vcfg hregion hobj]; exact hloc
  obtain ⟨regionF, hlkF, hopenF⟩ := l2_of_stackWithIndex vcfg hframeMem
  obtain ⟨regionF', hlkF', hopenF'⟩ := l2_of_stackWithIndex vcfg' hframemem'
  have finish : ∀ (E : FrameWithIndex), E ∈ cfg.stackWithIndex → FrameReachable cfg E.index (Reference.OId oid) →
      FrameReachable cfg frame.index (Reference.OId oid) := by
    intro E hEmem hEreach
    have hboundE : frame.index ≤ E.index :=
      fieldAsgn_region_container_confined vcfg hlkF hopenF hframeMem rfl hloc hEreach
    rcases eq_or_lt_of_le hboundE with heqE | hltE
    · exact (swap_corollary_stackWithIndex_index_inj hEmem hframeMem heqE.symm) ▸ hEreach
    · exact hcr3 frame hframeMem E hEmem hltE oid hloc hEreach
  constructor
  · -- forward
    rintro ⟨G, hGmem, hGreach⟩
    have hbound : frame.index ≤ G.index :=
      fieldAsgn_region_container_confined vcfg hlkF hopenF hframeMem rfl hloc hGreach
    have hFrameReach : FrameReachable cfg frame.index (Reference.OId oid) := by
      rcases eq_or_lt_of_le hbound with heq | hlt
      · exact (swap_corollary_stackWithIndex_index_inj hGmem hframeMem heq.symm) ▸ hGreach
      · exact hcr3 frame hframeMem G hGmem hlt oid hloc hGreach
    have hconfinedFwd : ∀ refX, FrameReachable cfg frame.index refX → refX ≠ Reference.OId oidC := by
      intro refX hreachX heqX
      rw [heqX] at hreachX
      exact absurd (hOwnerBoundCfg frame.index hreachX) (Nat.not_le.mpr hframeSusp')
    have hFrameReach' : FrameReachable cfg' frame.index (Reference.OId oid) :=
      fieldAsgn_confined_transport hstepIffOfNe hframeRootIff hconfinedFwd hFrameReach
    exact ⟨frame, hframemem', hFrameReach'⟩
  · -- backward
    rintro ⟨G, hGmem, hGreach⟩
    have hbound' : frame.index ≤ G.index :=
      fieldAsgn_region_container_confined vcfg' hlkF' hopenF' hframemem' rfl hlocSusp' hGreach
    have hconfinedBwd : ∀ refX, FrameReachable cfg' frame.index refX → refX ≠ Reference.OId oidC := by
      intro refX hreachX heqX
      rw [heqX] at hreachX
      exact absurd (hOwnerBoundCfg' frame.index hreachX) (Nat.not_le.mpr hframeSusp')
    have hFrameReach : FrameReachable cfg frame.index (Reference.OId oid) := by
      rcases eq_or_lt_of_le hbound' with heq | hlt
      · have hGeqFrame : G = frame := swap_corollary_stackWithIndex_index_inj hGmem hframemem' heq.symm
        have hGreach2 : FrameReachable cfg' frame.index (Reference.OId oid) := hGeqFrame ▸ hGreach
        exact fieldAsgn_confined_transport (fun a hane b => (hstepIffOfNe a hane b).symm)
          (fun fid start => (hframeRootIff fid start).symm) hconfinedBwd hGreach2
      · by_cases hGeqActive : G.index = activeFrame.index
        · -- G = active frame: genuine escape needed.
          rw [FrameReachable_iff_reflTransGen] at hGreach
          obtain ⟨start, hrootG, hrtgG⟩ := hGreach
          have hrootGcfg : FrameRoot cfg G.index start := (hframeRootIff G.index start).mpr hrootG
          rw [hGeqActive] at hrootGcfg
          rcases hcase with
              ⟨oid0, oid_y, obj, hxr0, hyr, hlocC, hobj, hcfg'⟩ |
              ⟨oid0, oid_y, rid, region, obj, hxr0, hyr, hlocC, hregion, hobj, hyloc, hstatus, hfrid, hcfg'⟩
          · -- STACK branch: an escaping chain hops onto the newly-written value `oid_y`, which
            -- already has its own independent root via `resolveV_frameRoot`.
            have hoideq : oidC = oid0 := by
              have hcomb := hxrC.symm.trans hxr0
              injection hcomb with hcomb2
              injection hcomb2
            subst hoideq
            have main_claim : ∀ a b : Reference, Relation.ReflTransGen (ReachableStep cfg') a b →
                Relation.ReflTransGen (ReachableStep cfg) a b ∨
                ∃ frameE ∈ cfg.stackWithIndex, FrameReachable cfg frameE.index b := by
              intro a b hrtg2
              induction hrtg2 using Relation.ReflTransGen.head_induction_on with
              | refl => left; exact Relation.ReflTransGen.refl
              | @head p c hstep hrest ih =>
                rcases ih with hchain | hesc
                · by_cases hpeq : p = Reference.OId oidC
                  · subst hpeq
                    rcases fieldAsgn_stack_oidC_step_of_ne_oidY hactive hlocC hobj hcfg' hstep with hceq | hstepOld
                    · subst hceq
                      right
                      obtain ⟨frameY, hframeYmem, hrootY⟩ := resolveV_frameRoot hyr
                      refine ⟨frameY, hframeYmem, ?_⟩
                      rw [FrameReachable_iff_reflTransGen]
                      exact ⟨Reference.OId oid_y, hrootY, hchain⟩
                    · left; exact Relation.ReflTransGen.head hstepOld hchain
                  · left
                    exact Relation.ReflTransGen.head ((hstepIffOfNe p hpeq c).mpr hstep) hchain
                · right; exact hesc
            rcases hrootGcfg with
                ⟨frameV, hVmem, hVidx, var, hvar⟩ |
                ⟨frameV, hVmem, hVidx, regionV, hVlookup, hVbridge⟩
            · have hVeqActive : frameV = activeFrame := swap_corollary_stackWithIndex_index_inj hVmem hactivemem hVidx
              rw [hVeqActive] at hvar
              rcases main_claim start (Reference.OId oid) hrtgG with hchainFull | ⟨frameE, hEmem, hEreach⟩
              · exact finish activeFrame hactivemem
                  ((FrameReachable_iff_reflTransGen cfg activeFrame.index (Reference.OId oid)).mpr
                    ⟨start, Or.inl ⟨activeFrame, hactivemem, rfl, var, hvar⟩, hchainFull⟩)
              · exact finish frameE hEmem hEreach
            · have hVeqActive : frameV = activeFrame := swap_corollary_stackWithIndex_index_inj hVmem hactivemem hVidx
              rw [hVeqActive] at hVlookup
              rcases main_claim start (Reference.OId oid) hrtgG with hchainFull | ⟨frameE, hEmem, hEreach⟩
              · exact finish activeFrame hactivemem
                  ((FrameReachable_iff_reflTransGen cfg activeFrame.index (Reference.OId oid)).mpr
                    ⟨start, Or.inr ⟨activeFrame, hactivemem, rfl, regionV, hVlookup, hVbridge⟩, hchainFull⟩)
              · exact finish frameE hEmem hEreach
          · -- REGION branch: the new edge (oid0 --> oid_y) stays inside region `rid` (the active
            -- frame's own region). If an escaping chain ever uses it, the *suffix* from `oid_y`
            -- onward is confined to `rid` (H3) and can never reach `oid`, which lives in the
            -- suspended frame's *different*, also-Open region -- so that case is vacuous.
            have hridNe : frame.regionId ≠ rid := by
              intro heq
              have heq2 : frame.regionId = activeFrame.regionId := heq.trans hfrid
              have hidxEq := merge_corollary_regionId_unique_index vcfg.s1 hframeMem hactivemem heq2
              exact absurd hidxEq (Nat.ne_of_lt hframeSusp')
            have hoideq : oidC = oid0 := by
              have hcomb := hxrC.symm.trans hxr0
              injection hcomb with hcomb2
              injection hcomb2
            subst hoideq
            have main_claim : ∀ a b : Reference, Relation.ReflTransGen (ReachableStep cfg') a b →
                Relation.ReflTransGen (ReachableStep cfg) a b ∨
                Relation.ReflTransGen (ReachableStep cfg) (Reference.OId oid_y) b := by
              intro a b hrtg2
              induction hrtg2 using Relation.ReflTransGen.head_induction_on with
              | refl => left; exact Relation.ReflTransGen.refl
              | @head p c hstep hrest ih =>
                rcases ih with hchain | hesc
                · by_cases hpeq : p = Reference.OId oidC
                  · subst hpeq
                    rcases fieldAsgn_region_oidC_step_of_ne_oidY vcfg hregion hlocC hobj hcfg' hstep with hceq | hstepOld
                    · subst hceq; right; exact hchain
                    · left; exact Relation.ReflTransGen.head hstepOld hchain
                  · left
                    exact Relation.ReflTransGen.head ((hstepIffOfNe p hpeq c).mpr hstep) hchain
                · right; exact hesc
            rcases main_claim start (Reference.OId oid) hrtgG with hchainFull | hescChain
            · rcases hrootGcfg with
                  ⟨frameV, hVmem, hVidx, var, hvar⟩ |
                  ⟨frameV, hVmem, hVidx, regionV, hVlookup, hVbridge⟩
              · have hVeqActive : frameV = activeFrame := swap_corollary_stackWithIndex_index_inj hVmem hactivemem hVidx
                rw [hVeqActive] at hvar
                exact finish activeFrame hactivemem
                  ((FrameReachable_iff_reflTransGen cfg activeFrame.index (Reference.OId oid)).mpr
                    ⟨start, Or.inl ⟨activeFrame, hactivemem, rfl, var, hvar⟩, hchainFull⟩)
              · have hVeqActive : frameV = activeFrame := swap_corollary_stackWithIndex_index_inj hVmem hactivemem hVidx
                rw [hVeqActive] at hVlookup
                exact finish activeFrame hactivemem
                  ((FrameReachable_iff_reflTransGen cfg activeFrame.index (Reference.OId oid)).mpr
                    ⟨start, Or.inr ⟨activeFrame, hactivemem, rfl, regionV, hVlookup, hVbridge⟩, hchainFull⟩)
            · exfalso
              exact reflTransGen_region_open_ne_absurd vcfg hregion hyloc hloc hlkF hopenF hridNe hescChain
        · have hGltLen : G.index < cfg'.stackWithIndex.length := by
            have hGmemCopy := hGmem
            unfold RuntimeConfig.stackWithIndex at hGmemCopy
            obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hGmemCopy
            have hidx : G.index = n := by rw [← hfeq]
            unfold RuntimeConfig.stackWithIndex
            rw [List.length_mapIdx, hidx]
            exact hn
          have hGltActive : G.index < activeFrame.index :=
            lt_of_le_of_ne (hactiveidx'' ▸ Nat.le_pred_of_lt hGltLen) hGeqActive
          have hconfinedG' : ∀ refX, FrameReachable cfg' G.index refX → refX ≠ Reference.OId oidC := by
            intro refX hreachX heqX
            rw [heqX] at hreachX
            exact absurd (hOwnerBoundCfg' G.index hreachX) (Nat.not_le.mpr hGltActive)
          have hGreachCfg : FrameReachable cfg G.index (Reference.OId oid) :=
            fieldAsgn_confined_transport (fun a hane b => (hstepIffOfNe a hane b).symm)
              (fun fid start => (hframeRootIff fid start).symm) hconfinedG' hGreach
          have hGmemCfg : G ∈ cfg.stackWithIndex := (fieldAsgn_frame_mem_iff h' hGltActive hactiveidx).mpr hGmem
          exact hcr3 frame hframeMem G hGmemCfg hlt oid hloc hGreachCfg
    exact ⟨frame, hframeMem, hFrameReach⟩

theorem stackReachable_invariant_swap (x : VarName) (yf : FieldAccess) :
    StackReachable_invariant_for_suspended_region_objects (Stmt.swap x yf) := by
  sorry

theorem stackReachable_invariant_all (cmd : Stmt) :
    StackReachable_invariant_for_suspended_region_objects cmd := by
  cases cmd with
  | enter xf bridgeVar => exact stackReachable_invariant_enter xf bridgeVar
  | exit => exact stackReachable_invariant_exit
  | fieldAsgn xf y => exact stackReachable_invariant_fieldAsgn xf y
  | makeObjRegion x => exact stackReachable_invariant_makeObjRegion x
  | makeObjStack x => exact stackReachable_invariant_makeObjStack x
  | makeRegion x => exact stackReachable_invariant_makeRegion x
  | merge x => exact stackReachable_invariant_merge x
  | swap x yf => exact stackReachable_invariant_swap x yf
  | varAsgn x yf => exact stackReachable_invariant_varAsgn x yf
