import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Mutation.Mutation
import Gc.Model.Mutation.Stmt
import Gc.Model.Preservation
import Gc.Reachability.Reachable.Semantics
import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.Def
import Gc.Reachability.Reachable.Lemmas

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
  have hframeMemCfg : frame ∈ cfg.stackWithIndex :=
    merge_frame_transport_down hframe1 hxref hregion1 hregion' hclosed hopen hcfg' hframeMem hframeLt
  have hframeRidNeRidPrime : frame.regionId ≠ rid' :=
    merge_regionId_ne_ridPrime vcfg hregion' hclosed frame hframeMemCfg
  have hframeRidNeFrame1 : frame.regionId ≠ frame1.regionId := by
    intro hc
    have hidxeq := merge_corollary_regionId_unique_index vcfg.s1 hframeMemCfg hlast1_mem hc
    exact absurd hidxeq (Nat.ne_of_lt hframeLt)
  have hloc_cfg : (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) := by
    rw [oid_loc_rgn_iff_in_heap vcfg]
    rw [oid_loc_rgn_iff_in_heap vcfg'] at hloc
    obtain ⟨region1', hlookup1', hmem1'⟩ := hloc
    have hlookup1'' : cfg.heap.lookup frame.regionId = some region1' := by
      rw [hcfg'] at hlookup1'; dsimp only at hlookup1'
      rw [AList.lookup_insert_ne hframeRidNeFrame1, AList.lookup_erase_ne hframeRidNeRidPrime] at hlookup1'
      exact hlookup1'
    exact ⟨region1', hlookup1'', hmem1'⟩
  have hdropLen : cfg.stack.dropLast.length = cfg.stack.length - 1 := List.length_dropLast
  by_cases hframe'eq : frame'.index = cfg.stack.dropLast.length
  · -- frame' IS the merged (last) frame.
    rw [FrameReachable_iff_reflTransGen] at hreach
    obtain ⟨start, hroot, hrtg⟩ := hreach
    have hoidNeRidPrime : Reference.OId oid ≠ Reference.RId rid' := by intro hc; exact absurd hc (by simp)
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
        have hresult_cfg : FrameReachable cfg frame.index (Reference.OId oid) :=
          hFR3 frame hframeMemCfg { frame1 with index := cfg.stack.dropLast.length } hlast1_mem hframeLt oid
            hloc_cfg hFrameReach
        exact (merge_frame_reachable_iff vcfg h' hframeMemCfg (hdropLen ▸ hframeLt) (Reference.OId oid)).mp
          hresult_cfg
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
        have hresult_cfg : FrameReachable cfg frame.index (Reference.OId oid) :=
          hFR3 frame hframeMemCfg { frame1 with index := cfg.stack.dropLast.length } hlast1_mem hframeLt oid
            hloc_cfg hFrameReach
        exact (merge_frame_reachable_iff vcfg h' hframeMemCfg (hdropLen ▸ hframeLt) (Reference.OId oid)).mp
          hresult_cfg
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
      have hrtgDown :=
        merge_chain_transport_down vcfg h' hframe1 hxref hregion1 hregion' hclosed hopen hcfg' hstartne hrtg
      have hFrameReach : FrameReachable cfg (cfg.stack.dropLast.length) (Reference.OId oid) :=
        (FrameReachable_iff_reflTransGen cfg (cfg.stack.dropLast.length) (Reference.OId oid)).mpr
          ⟨start, Or.inr ⟨{ frame1 with index := cfg.stack.dropLast.length }, hlast1_mem, rfl, region1, hregion1,
            hbridge0⟩, hrtgDown⟩
      have hresult_cfg : FrameReachable cfg frame.index (Reference.OId oid) :=
        hFR3 frame hframeMemCfg { frame1 with index := cfg.stack.dropLast.length } hlast1_mem hframeLt oid
          hloc_cfg hFrameReach
      exact (merge_frame_reachable_iff vcfg h' hframeMemCfg (hdropLen ▸ hframeLt) (Reference.OId oid)).mp hresult_cfg
  · -- frame' is not the merged frame: unconditional transport both ways.
    have h2 := hallLt frame' hframe'Mem
    have hframe'Lt : frame'.index < cfg.stack.dropLast.length :=
      lt_of_le_of_ne (Nat.le_of_lt_succ h2) hframe'eq
    have hframe'MemCfg :=
      merge_frame_transport_down hframe1 hxref hregion1 hregion' hclosed hopen hcfg' hframe'Mem hframe'Lt
    have hreach_cfg : FrameReachable cfg frame'.index (Reference.OId oid) :=
      (merge_frame_reachable_iff vcfg h' hframe'MemCfg (hdropLen ▸ hframe'Lt) (Reference.OId oid)).mpr hreach
    have hresult_cfg : FrameReachable cfg frame.index (Reference.OId oid) :=
      hFR3 frame hframeMemCfg frame' hframe'MemCfg hlt oid hloc_cfg hreach_cfg
    exact (merge_frame_reachable_iff vcfg h' hframeMemCfg (hdropLen ▸ hframeLt) (Reference.OId oid)).mp hresult_cfg
