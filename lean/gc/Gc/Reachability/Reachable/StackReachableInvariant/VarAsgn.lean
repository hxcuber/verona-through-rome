import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Mutation.Mutation
import Gc.Model.Mutation.Stmt
import Gc.Model.Preservation
import Gc.Reachability.Reachable.Semantics
import Gc.Reachability.Reachable.StackReachableInvariant.Def
import Gc.Reachability.Reachable.Lemmas

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
  · -- forward: G = last frame needs per-branch handling; any other G survives via `varAsgn_frame_reachable_iff`.
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
        · -- bridge-var branch: confinement rules this out — `oid` lives in the suspended region `frame.regionId`, distinct (S1) from `rid`.
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
        · -- fresh-var branch: heap untouched, bridge transports directly; witness frame is the new last frame.
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
  · -- backward: symmetric, but the new root is always pre-existing (never fresh), traced via `resolveFA_frameReach` rather than `hcr3`.
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
