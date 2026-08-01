import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Mutation.Mutation
import Gc.Model.Mutation.Stmt
import Gc.Model.Preservation
import Gc.Reachability.Reachable.Semantics
import Gc.Reachability.Reachable.Basic
import Gc.Reachability.Reachable.Lemmas

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
  · -- forward: G = last frame collapses via the CR3-style hypothesis; any other G survives `makeRegion` unchanged.
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
  · -- backward: G is pre-existing (transports down) or the mutated last frame, whose chain came from `lastFrame`'s roots or a fresh root that can't reach `oid` (region doesn't exist yet).
    rintro ⟨G, hGmem, hGreach⟩
    rcases makeRegion_frame_cases h' hGmem with
      ⟨hGmemcfg, hGlt⟩ | ⟨lf, hlf, hGregionId, -, -, hGvarMap, -⟩
    · exact ⟨G, hGmemcfg, (makeRegion_frame_reachable_iff vcfg h' hGmemcfg hGlt (Reference.OId oid)).mpr hGreach⟩
    · rw [hlast] at hlf
      injection hlf with hlf
      subst hlf
      rw [FrameReachable_iff_reflTransGen] at hGreach
      obtain ⟨start, hroot, hrtg⟩ := hGreach
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
            rcases hrtg.cases_head with heq | ⟨c, hstep, hrest⟩
            · cases heq
            · rw [ReachableStep_rid_iff] at hstep
              obtain ⟨region2, hlookup2, -, hbeq⟩ := hstep
              have hlookup2' : cfg'.heap.lookup cfg.freshRegionId = some ({ bridgeObjectId := cfg.freshObjectId, objMap := (∅ : ObjMap).insert cfg.freshObjectId ∅, status := Status.Closed } : Region) := by
                rw [hcfg']; dsimp only; rw [AList.lookup_insert]
              rw [hlookup2'] at hlookup2
              injection hlookup2 with hlookup2eq
              rw [← hlookup2eq] at hbeq
              dsimp only at hbeq
              rw [hbeq] at hrest
              rcases hrest.cases_head with heq2 | ⟨c2, hstep2, -⟩
              · injection heq2 with heq2
                rw [← heq2, freshObjectId_loc_none] at hloc
                exact absurd hloc (by simp)
              · rw [ReachableStep_oid_iff, makeRegion_fresh_objAt_cfg' h'] at hstep2
                obtain ⟨obj, hobjEq, hcontains⟩ := hstep2
                injection hobjEq with hobjEq
                rw [← hobjEq] at hcontains
                simp [Object.refs] at hcontains
          · rw [AList.lookup_insert_ne hveq] at hvar
            have hstackEq : cfg.stack = cfg.stack.dropLast ++ [lastFrame] :=
              (List.dropLast_append_getLast? lastFrame hlast).symm
            have hmemLast : lastFrame ∈ cfg.stack :=
              hstackEq ▸ List.mem_append_right _ (List.mem_singleton_self lastFrame)
            have hstartne : start ≠ Reference.RId cfg.freshRegionId := by
              intro heq
              rw [heq] at hvar
              have hmemrefs : Reference.RId cfg.freshRegionId ∈ lastFrame.refs :=
                mem_frame_refs_of_mem_varMap hvar
              have hmemStack : Reference.RId cfg.freshRegionId ∈ cfg.stack.refs := by
                rw [stack_refs_eq_flatMap, List.mem_flatMap]
                exact ⟨lastFrame, hmemLast, hmemrefs⟩
              have hmemCfg : Reference.RId cfg.freshRegionId ∈ cfg.refs := List.mem_append_left _ hmemStack
              exact RuntimeConfig.freshRegionId_not_mem cfg (vcfg.hs2 cfg.freshRegionId hmemCfg)
            obtain ⟨-, hrtgCfg⟩ := makeRegion_reflTransGen_transport_down vcfg h' hstartne hrtg
            exact (FrameReachable_iff_reflTransGen cfg (cfg.stack.length - 1) (Reference.OId oid)).mpr
              ⟨start, Or.inl ⟨{ lastFrame with index := cfg.stack.length - 1 }, hLf, rfl, var, hvar⟩, hrtgCfg⟩
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
          have hstartne : start ≠ Reference.RId cfg.freshRegionId := by rw [hbridge]; simp
          obtain ⟨-, hrtgCfg⟩ := makeRegion_reflTransGen_transport_down vcfg h' hstartne hrtg
          exact (FrameReachable_iff_reflTransGen cfg (cfg.stack.length - 1) (Reference.OId oid)).mpr
            ⟨start, Or.inr ⟨{ lastFrame with index := cfg.stack.length - 1 }, hLf, rfl, regionX, hlookup, hbridge⟩,
              hrtgCfg⟩
      exact ⟨frame, hframeMem, hcr3 frame hframeMem _ hLf hlt oid hloc hLfReach⟩
