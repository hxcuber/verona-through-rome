import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Mutation.Mutation
import Gc.Model.Mutation.Stmt
import Gc.Model.Preservation
import Gc.Reachability.Reachable.Semantics
import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.Def
import Gc.Reachability.Reachable.Lemmas

theorem frameReachableAtLaterFrame_step_varAsgn (x : VarName) (yf : FieldAccess) :
    FrameReachableAtLaterFrame_step (Stmt.varAsgn x yf) := by
  intro cfg cfg' vcfg h hFR3 frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  have h' : varAsgn x yf cfg = some cfg' := h
  obtain ⟨lastFrame, hlast, hcase⟩ := varAsgn_cases h'
  have hLf : ({ lastFrame with index := cfg.stack.length - 1 } : FrameWithIndex) ∈ cfg.stackWithIndex :=
    stackWithIndex_getLast_mem hlast
  have hstep_eq : ReachableStep cfg = ReachableStep cfg' := varAsgn_step_eq vcfg h'
  have hstackLenEq : cfg.stack.length = cfg'.stack.length := by
    rcases hcase with ⟨oidY, rid, region, hyf, hxb, hlocY, hridEq, hregion, hcfg'⟩ | ⟨oidY, hyf, hxb, hresolve, hcfg'⟩
    · rw [hcfg']
    · have hne0 : cfg.stack ≠ [] := by intro hnil; rw [hnil] at hlast; simp at hlast
      have hlen1 : 1 ≤ cfg.stack.length := List.length_pos_of_ne_nil hne0
      have hstackEq0 : cfg.stack = cfg.stack.dropLast ++ [lastFrame] :=
        (List.dropLast_append_getLast? lastFrame hlast).symm
      rw [hcfg']; dsimp only
      rw [List.length_append, List.length_dropLast, List.length_singleton]
      omega
  have hloc_cfg : (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) := by
    rw [varAsgn_corollary_loc_eq vcfg h' oid]; exact hloc
  have hframe'Ltlen : frame'.index < cfg'.stack.length := by
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hframe'Mem
    have hidx : frame'.index = n := by rw [← hfeq]
    rw [hidx]; exact hn
  have hframe'Ltlen' : frame'.index < cfg.stack.length := by rw [hstackLenEq]; exact hframe'Ltlen
  have hframeLt : frame.index < cfg.stack.length - 1 :=
    lt_of_lt_of_le hlt (Nat.le_sub_one_of_lt hframe'Ltlen')
  have hframeMemCfg : frame ∈ cfg.stackWithIndex := (varAsgn_frame_mem_iff h' hframeLt).mpr hframeMem
  obtain ⟨region_f, hlk_f, hopen_f⟩ := l2_of_stackWithIndex vcfg hframeMemCfg
  -- A `target` with an independent root `frameY` reaching `oid` has `frame.index ≤ frameY.index` (`region_container_confined`); equality or `hFR3` both land on `FrameReachable cfg frame.index oid`.
  have escape : ∀ target : Reference,
      (∃ frameY : FrameWithIndex, frameY ∈ cfg.stackWithIndex ∧ FrameReachable cfg frameY.index target) →
      Relation.ReflTransGen (ReachableStep cfg) target (Reference.OId oid) →
      FrameReachable cfg frame.index (Reference.OId oid) := by
    rintro target ⟨frameY, hframeYmem, hreachY⟩ htail
    have hreachYFull : FrameReachable cfg frameY.index (Reference.OId oid) := by
      rw [FrameReachable_iff_reflTransGen] at hreachY ⊢
      obtain ⟨startY, hrootY, hrtgY⟩ := hreachY
      exact ⟨startY, hrootY, hrtgY.trans htail⟩
    have hbound : frame.index ≤ frameY.index :=
      region_container_confined vcfg hlk_f hopen_f hframeMemCfg rfl hloc_cfg hreachYFull
    rcases hbound.lt_or_eq with hltY | heqY
    · exact hFR3 frame hframeMemCfg frameY hframeYmem hltY oid hloc_cfg hreachYFull
    · have hfeq : frame = frameY := swap_corollary_stackWithIndex_index_inj hframeMemCfg hframeYmem heqY
      rw [hfeq]; exact hreachYFull
  by_cases hframe'eq : frame'.index = cfg.stack.length - 1
  · -- frame' IS the last (mutated) frame.
    rw [FrameReachable_iff_reflTransGen] at hreach
    obtain ⟨start, hroot, hrtg⟩ := hreach
    rw [← hstep_eq] at hrtg
    have hlt' : frame.index < ({ lastFrame with index := cfg.stack.length - 1 } : FrameWithIndex).index := by
      show frame.index < cfg.stack.length - 1
      rw [← hframe'eq]; exact hlt
    rcases hcase with
        ⟨oidY, rid, region, hyf, hxb, hlocY, hridEq, hregion, hcfg'⟩ |
        ⟨oidY, hyf, hxb, hresolve, hcfg'⟩
    · -- bridge-var branch: stack is literally unchanged.
      have hstackEq0 : cfg'.stack = cfg.stack := by rw [hcfg']
      have hframe'MemCfg : frame' ∈ cfg.stackWithIndex := by
        unfold RuntimeConfig.stackWithIndex at hframe'Mem ⊢; rw [hstackEq0] at hframe'Mem; exact hframe'Mem
      rcases hroot with ⟨Gf, hGfmem, hGfidx, var, hvar⟩ | ⟨Gf, hGfmem, hGfidx, regionG, hlookupG, hbridge⟩
      · have hGfmemCfg : Gf ∈ cfg.stackWithIndex := by
          unfold RuntimeConfig.stackWithIndex at hGfmem ⊢; rw [hstackEq0] at hGfmem; exact hGfmem
        have hFrameReachFrame' : FrameReachable cfg frame'.index (Reference.OId oid) :=
          (FrameReachable_iff_reflTransGen cfg frame'.index (Reference.OId oid)).mpr
            ⟨start, Or.inl ⟨Gf, hGfmemCfg, hGfidx, var, hvar⟩, hrtg⟩
        exact (varAsgn_frame_reachable_iff vcfg h' hframeMemCfg hframeLt (Reference.OId oid)).mp
          (hFR3 frame hframeMemCfg frame' hframe'MemCfg hlt oid hloc_cfg hFrameReachFrame')
      · have hGfmemCfg : Gf ∈ cfg.stackWithIndex := by
          unfold RuntimeConfig.stackWithIndex at hGfmem ⊢; rw [hstackEq0] at hGfmem; exact hGfmem
        by_cases heqrid : Gf.regionId = rid
        · have hlookupG' : cfg'.heap.lookup Gf.regionId = some ({ region with bridgeObjectId := oidY } : Region) := by
            rw [heqrid, hcfg']; dsimp only; rw [AList.lookup_insert]
          rw [hlookupG'] at hlookupG
          injection hlookupG with hlookupGEq
          rw [← hlookupGEq] at hbridge
          dsimp only at hbridge
          rw [hbridge] at hrtg
          exact (varAsgn_frame_reachable_iff vcfg h' hframeMemCfg hframeLt (Reference.OId oid)).mp
            (escape (Reference.OId oidY) (resolveFA_frameReach hyf) hrtg)
        · have hlookupG' : cfg.heap.lookup Gf.regionId = some regionG := by
            rw [hcfg'] at hlookupG; dsimp only at hlookupG
            rw [AList.lookup_insert_ne heqrid] at hlookupG; exact hlookupG
          have hFrameReachFrame' : FrameReachable cfg frame'.index (Reference.OId oid) :=
            (FrameReachable_iff_reflTransGen cfg frame'.index (Reference.OId oid)).mpr
              ⟨start, Or.inr ⟨Gf, hGfmemCfg, hGfidx, regionG, hlookupG', hbridge⟩, hrtg⟩
          exact (varAsgn_frame_reachable_iff vcfg h' hframeMemCfg hframeLt (Reference.OId oid)).mp
            (hFR3 frame hframeMemCfg frame' hframe'MemCfg hlt oid hloc_cfg hFrameReachFrame')
    · -- fresh-var branch.
      have hnewMem := varAsgn_freshvar_last_mem hlast hcfg'
      set newLastFrame : FrameWithIndex := { lastFrame with
        varMap := lastFrame.varMap.insert x (Reference.OId oidY), index := cfg.stack.length - 1 } with newLastFrame_def
      have hframe'eqNew : frame' = newLastFrame := swap_corollary_stackWithIndex_index_inj hframe'Mem hnewMem hframe'eq
      rcases hroot with ⟨Gf, hGfmem, hGfidx, var, hvar⟩ | ⟨Gf, hGfmem, hGfidx, regionG, hlookupG, hbridge⟩
      · have hGfeqFrame' : Gf = frame' := swap_corollary_stackWithIndex_index_inj hGfmem hframe'Mem hGfidx
        rw [hGfeqFrame', hframe'eqNew, newLastFrame_def] at hvar
        dsimp only at hvar
        by_cases hveq : var = x
        · rw [hveq, AList.lookup_insert] at hvar
          injection hvar with hstartEq
          subst hstartEq
          exact (varAsgn_frame_reachable_iff vcfg h' hframeMemCfg hframeLt (Reference.OId oid)).mp
            (escape (Reference.OId oidY) (resolveFA_frameReach hyf) hrtg)
        · rw [AList.lookup_insert_ne hveq] at hvar
          have hFrameReachLf : FrameReachable cfg (cfg.stack.length - 1) (Reference.OId oid) :=
            (FrameReachable_iff_reflTransGen cfg (cfg.stack.length - 1) (Reference.OId oid)).mpr
              ⟨start, Or.inl ⟨_, hLf, rfl, var, hvar⟩, hrtg⟩
          exact (varAsgn_frame_reachable_iff vcfg h' hframeMemCfg hframeLt (Reference.OId oid)).mp
            (hFR3 frame hframeMemCfg _ hLf hlt' oid hloc_cfg hFrameReachLf)
      · have hGfeqFrame' : Gf = frame' := swap_corollary_stackWithIndex_index_inj hGfmem hframe'Mem hGfidx
        have hlookupG' : cfg.heap.lookup Gf.regionId = some regionG := by rw [hcfg'] at hlookupG; exact hlookupG
        have hGfRegionEq : Gf.regionId = lastFrame.regionId := by rw [hGfeqFrame', hframe'eqNew, newLastFrame_def]
        have hFrameReachLf : FrameReachable cfg (cfg.stack.length - 1) (Reference.OId oid) :=
          (FrameReachable_iff_reflTransGen cfg (cfg.stack.length - 1) (Reference.OId oid)).mpr
            ⟨start, Or.inr ⟨_, hLf, rfl, regionG, hGfRegionEq ▸ hlookupG', hbridge⟩, hrtg⟩
        exact (varAsgn_frame_reachable_iff vcfg h' hframeMemCfg hframeLt (Reference.OId oid)).mp
          (hFR3 frame hframeMemCfg _ hLf hlt' oid hloc_cfg hFrameReachLf)
  · -- frame' is not the last frame: unconditional transport both ways.
    have hframe'Lt : frame'.index < cfg.stack.length - 1 :=
      lt_of_le_of_ne (Nat.le_sub_one_of_lt hframe'Ltlen') hframe'eq
    have hframe'MemCfg : frame' ∈ cfg.stackWithIndex := (varAsgn_frame_mem_iff h' hframe'Lt).mpr hframe'Mem
    have hreach_cfg : FrameReachable cfg frame'.index (Reference.OId oid) :=
      (varAsgn_frame_reachable_iff vcfg h' hframe'MemCfg hframe'Lt (Reference.OId oid)).mpr hreach
    have hresult_cfg : FrameReachable cfg frame.index (Reference.OId oid) :=
      hFR3 frame hframeMemCfg frame' hframe'MemCfg hlt oid hloc_cfg hreach_cfg
    exact (varAsgn_frame_reachable_iff vcfg h' hframeMemCfg hframeLt (Reference.OId oid)).mp hresult_cfg
