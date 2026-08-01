import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Mutation.Mutation
import Gc.Model.Mutation.Stmt
import Gc.Model.Preservation
import Gc.Reachability.Reachable.Semantics
import Gc.Reachability.Reachable.Basic
import Gc.Reachability.Reachable.Lemmas

theorem stackReachable_invariant_merge (x : VarName) :
    StackReachable_invariant_for_suspended_region_objects (Stmt.merge x) := by
  intro cfg cfg' vcfg h hcr3 frame hframeMem hframeSusp oid hloc
  have h' : merge x cfg = some cfg' := h
  obtain ⟨frame1, rid', region1, region', hframe1, hxref, hregion1, hregion', hclosed, hopen, hcfg'⟩ :=
    merge_cases h'
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame1] :=
    (List.dropLast_append_getLast? frame1 hframe1).symm
  have hframe1MemStack : frame1 ∈ cfg.stack := by
    rw [stack_eq]; exact List.mem_append_right _ (List.mem_singleton_self _)
  have hlenEq : cfg.stackWithIndex.length = cfg.stack.length := by
    unfold RuntimeConfig.stackWithIndex; rw [List.length_mapIdx]
  have hdropLen : cfg.stack.dropLast.length = cfg.stack.length - 1 := List.length_dropLast
  have hframeSusp' : frame.index < cfg.stack.dropLast.length := by
    rw [hdropLen, ← hlenEq]; exact hframeSusp
  have hlast1_mem : ({ frame1 with index := cfg.stack.dropLast.length } : FrameWithIndex) ∈ cfg.stackWithIndex := by
    have hframe1_get : cfg.stack[cfg.stack.dropLast.length]? = some frame1 := by
      conv_lhs => rw [stack_eq]
      simp
    obtain ⟨hh1, hheq⟩ := List.getElem?_eq_some_iff.mp hframe1_get
    unfold RuntimeConfig.stackWithIndex
    exact List.mem_mapIdx.mpr ⟨cfg.stack.dropLast.length, hh1, by rw [hheq]⟩
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
  constructor
  · rintro ⟨G, hGmem, hGreach⟩
    by_cases hGeq : G.index = cfg.stack.dropLast.length
    · have hltG : frame.index < G.index := by rw [hGeq]; exact hframeSusp'
      have hframeReach : FrameReachable cfg frame.index (Reference.OId oid) :=
        hcr3 frame hframeMem G hGmem hltG oid hloc hGreach
      have hframeReach' : FrameReachable cfg' frame.index (Reference.OId oid) :=
        (merge_frame_reachable_iff vcfg h' hframeMem (hdropLen ▸ hframeSusp') (Reference.OId oid)).mp hframeReach
      exact ⟨frame, merge_frame_transport_up hframe1 hxref hregion1 hregion' hclosed hopen hcfg' hframeMem hframeSusp',
        hframeReach'⟩
    · have hGltlen : G.index < cfg.stack.length := by
        obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hGmem
        have hidx : G.index = n := by rw [← hfeq]
        rw [hidx]; exact hn
      have hGlt : G.index < cfg.stack.dropLast.length := by
        have hGltlen' : G.index < cfg.stack.dropLast.length + 1 := hlenEq2 ▸ hGltlen
        exact lt_of_le_of_ne (Nat.le_of_lt_succ hGltlen') hGeq
      exact ⟨G, merge_frame_transport_up hframe1 hxref hregion1 hregion' hclosed hopen hcfg' hGmem hGlt,
        (merge_frame_reachable_iff vcfg h' hGmem (hdropLen ▸ hGlt) (Reference.OId oid)).mp hGreach⟩
  · rintro ⟨G, hGmem, hGreach⟩
    by_cases hGeq : G.index = cfg.stack.dropLast.length
    · rw [FrameReachable_iff_reflTransGen] at hGreach
      obtain ⟨start, hroot, hrtg⟩ := hGreach
      have hGeqLf : G = { newFrame1 with index := cfg.stack.dropLast.length } :=
        swap_corollary_stackWithIndex_index_inj hGmem hLf' hGeq
      have hoidNeRidPrime : Reference.OId oid ≠ Reference.RId rid' := by intro hc; exact absurd hc (by simp)
      rcases hroot with ⟨Gf, hGfmem, hGfidx, var, hvar⟩ | ⟨Gf, hGfmem, hGfidx, region0, hlk0, hbridge0⟩
      · have hGfeq : Gf = { newFrame1 with index := cfg.stack.dropLast.length } :=
          swap_corollary_stackWithIndex_index_inj hGfmem hLf' (hGfidx.trans hGeq)
        rw [hGfeq] at hvar
        by_cases hveq : var = x
        · rw [hveq] at hvar
          rw [newFrame1_def] at hvar
          dsimp only at hvar
          rw [AList.lookup_insert] at hvar
          injection hvar with hvarEq
          rw [← hvarEq] at hrtg
          have hrtgDown : Relation.ReflTransGen (ReachableStep cfg) (Reference.OId region'.bridgeObjectId)
              (Reference.OId oid) :=
            merge_chain_transport_down vcfg h' hframe1 hxref hregion1 hregion' hclosed hopen hcfg'
              (by intro hc; exact absurd hc (by simp)) hrtg
          have hrtgRidPrime : Relation.ReflTransGen (ReachableStep cfg) (Reference.RId rid') (Reference.OId oid) :=
            (merge_ridPrime_reflTransGen_iff hregion' hclosed hoidNeRidPrime).mpr hrtgDown
          have hFrameReach : FrameReachable cfg (cfg.stack.dropLast.length) (Reference.OId oid) :=
            (FrameReachable_iff_reflTransGen cfg (cfg.stack.dropLast.length) (Reference.OId oid)).mpr
              ⟨Reference.RId rid', Or.inl ⟨{ frame1 with index := cfg.stack.dropLast.length }, hlast1_mem, rfl, x,
                hxref⟩, hrtgRidPrime⟩
          exact ⟨{ frame1 with index := cfg.stack.dropLast.length }, hlast1_mem, hFrameReach⟩
        · rw [newFrame1_def] at hvar
          dsimp only at hvar
          rw [AList.lookup_insert_ne hveq] at hvar
          have hstartne : start ≠ Reference.RId rid' := by
            intro hc
            rw [hc] at hvar
            exact merge_ridPrime_var_unique vcfg hframe1MemStack hxref hveq hvar
          have hrtgDown :=
            merge_chain_transport_down vcfg h' hframe1 hxref hregion1 hregion' hclosed hopen hcfg' hstartne hrtg
          have hFrameReach : FrameReachable cfg (cfg.stack.dropLast.length) (Reference.OId oid) :=
            (FrameReachable_iff_reflTransGen cfg (cfg.stack.dropLast.length) (Reference.OId oid)).mpr
              ⟨start, Or.inl ⟨{ frame1 with index := cfg.stack.dropLast.length }, hlast1_mem, rfl, var, hvar⟩,
                hrtgDown⟩
          exact ⟨{ frame1 with index := cfg.stack.dropLast.length }, hlast1_mem, hFrameReach⟩
      · have hGfeq : Gf = { newFrame1 with index := cfg.stack.dropLast.length } :=
          swap_corollary_stackWithIndex_index_inj hGfmem hLf' (hGfidx.trans hGeq)
        rw [hGfeq, newFrame1_def] at hlk0
        dsimp only at hlk0
        rw [hcfg'] at hlk0
        dsimp only at hlk0
        rw [AList.lookup_insert] at hlk0
        injection hlk0 with hlk0Eq
        rw [← hlk0Eq] at hbridge0
        dsimp only at hbridge0
        have hstartne : start ≠ Reference.RId rid' := by rw [hbridge0]; intro hc; exact absurd hc (by simp)
        have hrtgDown :=
          merge_chain_transport_down vcfg h' hframe1 hxref hregion1 hregion' hclosed hopen hcfg' hstartne hrtg
        have hFrameReach : FrameReachable cfg (cfg.stack.dropLast.length) (Reference.OId oid) :=
          (FrameReachable_iff_reflTransGen cfg (cfg.stack.dropLast.length) (Reference.OId oid)).mpr
            ⟨start, Or.inr ⟨{ frame1 with index := cfg.stack.dropLast.length }, hlast1_mem, rfl, region1, hregion1,
              hbridge0⟩, hrtgDown⟩
        exact ⟨{ frame1 with index := cfg.stack.dropLast.length }, hlast1_mem, hFrameReach⟩
    · have hGltlen : G.index < cfg.stack.length := by
        obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hGmem
        have hidx : G.index = n := by rw [← hfeq]
        rw [hidx, hstackLenEq]; exact hn
      have hGlt : G.index < cfg.stack.dropLast.length := by
        have hGltlen' : G.index < cfg.stack.dropLast.length + 1 := hlenEq2 ▸ hGltlen
        exact lt_of_le_of_ne (Nat.le_of_lt_succ hGltlen') hGeq
      have hGmemCfg := merge_frame_transport_down hframe1 hxref hregion1 hregion' hclosed hopen hcfg' hGmem hGlt
      exact ⟨G, hGmemCfg, (merge_frame_reachable_iff vcfg h' hGmemCfg (hdropLen ▸ hGlt) (Reference.OId oid)).mpr hGreach⟩
