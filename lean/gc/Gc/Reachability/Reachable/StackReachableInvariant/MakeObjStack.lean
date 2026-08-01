import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Mutation.Mutation
import Gc.Model.Mutation.Stmt
import Gc.Model.Preservation
import Gc.Reachability.Reachable.Semantics
import Gc.Reachability.Reachable.StackReachableInvariant.Def
import Gc.Reachability.Reachable.Lemmas

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
  · -- forward: G = last frame collapses via the CR3-style hypothesis; any other G survives `makeObjStack` unchanged.
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
  · -- backward: G is pre-existing (transports down) or the mutated last frame, whose chain came from `lastFrame`'s roots or a fresh root that can't reach `oid`.
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
