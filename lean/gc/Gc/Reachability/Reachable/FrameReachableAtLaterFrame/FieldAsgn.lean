import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Mutation.Mutation
import Gc.Model.Mutation.Stmt
import Gc.Model.Preservation
import Gc.Reachability.Reachable.Semantics
import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.Def
import Gc.Reachability.Reachable.Lemmas

theorem frameReachableAtLaterFrame_step_fieldAsgn (xf : FieldAccess) (y : VarName) :
    FrameReachableAtLaterFrame_step (Stmt.fieldAsgn xf y) := by
  intro cfg cfg' vcfg h hFR3 frame hframeMem frame' hframe'Mem hlt oid hloc hreach
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
      intro fid hreach2
      exact stack_container_confined vcfg hlocC hreach2
    · have hoideq : oidC = oid0 := by
        have hcomb := hxrC.symm.trans hxr0
        injection hcomb with hcomb2
        injection hcomb2
      subst hoideq
      intro fid hreach2
      exact region_container_confined vcfg hregion hstatus hactivemem hfrid.symm hlocC hreach2
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
      intro fid hreach2
      exact stack_container_confined vcfg' hlocC' hreach2
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
      intro fid hreach2
      exact region_container_confined vcfg' hregion' hstatus hactivemem' hfrid.symm hlocC' hreach2
  -- `frame` is always strictly before the active frame (something -- `frame'` -- is after it).
  have hframe'LtLen : frame'.index < cfg'.stackWithIndex.length := by
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hframe'Mem
    have hidx : frame'.index = n := by rw [← hfeq]
    unfold RuntimeConfig.stackWithIndex
    rw [List.length_mapIdx, hidx]
    exact hn
  have hframeLt : frame.index < activeFrame.index := by
    rw [hactiveidx'']
    exact lt_of_lt_of_le hlt (Nat.le_sub_one_of_lt hframe'LtLen)
  have hframeMemCfg : frame ∈ cfg.stackWithIndex :=
    (fieldAsgn_frame_mem_iff h' hframeLt hactiveidx).mpr hframeMem
  have hloc_cfg : (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) := by
    rcases hcase with
        ⟨oid0, oid_y, obj, hxr0, hyr, hlocC, hobj, hcfg'⟩ |
        ⟨oid0, oid_y, rid, region, obj, hxr0, hyr, hlocC, hregion, hobj, hyloc, hstatus, hfrid, hcfg'⟩
    · rw [fieldAsgn_corollary_stack_loc_eq hactive hobj, ← hcfg']; exact hloc
    · rw [fieldAsgn_corollary_region_loc_eq vcfg hregion hobj, ← hcfg']; exact hloc
  obtain ⟨regionF, hlkF, hopenF⟩ := l2_of_stackWithIndex vcfg hframeMemCfg
  -- Collapses a `cfg`-side witness at or beyond `frame`'s index back to `frame`, via confinement plus index-uniqueness or `hFR3`.
  have finish : ∀ (E : FrameWithIndex), E ∈ cfg.stackWithIndex → FrameReachable cfg E.index (Reference.OId oid) →
      FrameReachable cfg frame.index (Reference.OId oid) := by
    intro E hEmem hEreach
    have hboundE : frame.index ≤ E.index :=
      region_container_confined vcfg hlkF hopenF hframeMemCfg rfl hloc_cfg hEreach
    rcases eq_or_lt_of_le hboundE with heqE | hltE
    · exact (swap_corollary_stackWithIndex_index_inj hEmem hframeMemCfg heqE.symm) ▸ hEreach
    · exact hFR3 frame hframeMemCfg E hEmem hltE oid hloc_cfg hEreach
  have transportUp : FrameReachable cfg frame.index (Reference.OId oid) →
      FrameReachable cfg' frame.index (Reference.OId oid) := by
    intro hFrameReach
    have hconfinedFwd : ∀ refX, FrameReachable cfg frame.index refX → refX ≠ Reference.OId oidC := by
      intro refX hreachX heqX
      rw [heqX] at hreachX
      exact absurd (hOwnerBoundCfg frame.index hreachX) (Nat.not_le.mpr hframeLt)
    exact fieldAsgn_confined_transport hstepIffOfNe hframeRootIff hconfinedFwd hFrameReach
  by_cases hframe'eq : frame'.index = activeFrame.index
  · -- frame' IS the active frame: genuine escape needed.
    apply transportUp
    rw [FrameReachable_iff_reflTransGen] at hreach
    obtain ⟨start, hrootG, hrtgG⟩ := hreach
    have hrootGcfg : FrameRoot cfg frame'.index start := (hframeRootIff frame'.index start).mpr hrootG
    rw [hframe'eq] at hrootGcfg
    rcases hcase with
        ⟨oid0, oid_y, obj, hxr0, hyr, hlocC, hobj, hcfg'⟩ |
        ⟨oid0, oid_y, rid, region, obj, hxr0, hyr, hlocC, hregion, hobj, hyloc, hstatus, hfrid, hcfg'⟩
    · -- STACK branch: an escaping chain hops onto `oid_y`, which has its own root via `resolveV_frameRoot`.
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
    · -- REGION branch: the new edge stays inside `rid`; any suffix from `oid_y` is H3-confined to `rid`, so it can never reach `oid` in `frame`'s different Open region.
      have hridNe : frame.regionId ≠ rid := by
        intro heq
        have heq2 : frame.regionId = activeFrame.regionId := heq.trans hfrid
        have hidxEq := merge_corollary_regionId_unique_index vcfg.s1 hframeMemCfg hactivemem heq2
        exact absurd hidxEq (Nat.ne_of_lt hframeLt)
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
        exact reflTransGen_region_open_ne_absurd vcfg hregion hyloc hloc_cfg hlkF hopenF hridNe hescChain
  · -- frame' is not the active frame: unconditional transport both ways.
    have hframe'LtActive : frame'.index < activeFrame.index :=
      lt_of_le_of_ne (hactiveidx'' ▸ Nat.le_pred_of_lt hframe'LtLen) hframe'eq
    have hconfinedG' : ∀ refX, FrameReachable cfg' frame'.index refX → refX ≠ Reference.OId oidC := by
      intro refX hreachX heqX
      rw [heqX] at hreachX
      exact absurd (hOwnerBoundCfg' frame'.index hreachX) (Nat.not_le.mpr hframe'LtActive)
    have hreach_cfg : FrameReachable cfg frame'.index (Reference.OId oid) :=
      fieldAsgn_confined_transport (fun a hane b => (hstepIffOfNe a hane b).symm)
        (fun fid start => (hframeRootIff fid start).symm) hconfinedG' hreach
    have hframe'MemCfg : frame' ∈ cfg.stackWithIndex :=
      (fieldAsgn_frame_mem_iff h' hframe'LtActive hactiveidx).mpr hframe'Mem
    exact transportUp (hFR3 frame hframeMemCfg frame' hframe'MemCfg hlt oid hloc_cfg hreach_cfg)
