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
  sorry

theorem stackReachable_invariant_fieldAsgn (xf : FieldAccess) (y : VarName) :
    StackReachable_invariant_for_suspended_region_objects (Stmt.fieldAsgn xf y) := by
  sorry

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
