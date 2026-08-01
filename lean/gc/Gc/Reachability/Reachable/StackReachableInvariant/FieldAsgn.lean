import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Mutation.Mutation
import Gc.Model.Mutation.Stmt
import Gc.Model.Preservation
import Gc.Reachability.Reachable.Semantics
import Gc.Reachability.Reachable.StackReachableInvariant.Def
import Gc.Reachability.Reachable.Lemmas

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
      exact stack_container_confined vcfg hlocC hreach
    · have hoideq : oidC = oid0 := by
        have hcomb := hxrC.symm.trans hxr0
        injection hcomb with hcomb2
        injection hcomb2
      subst hoideq
      intro fid hreach
      exact region_container_confined vcfg hregion hstatus hactivemem hfrid.symm hlocC hreach
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
      exact stack_container_confined vcfg' hlocC' hreach
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
      exact region_container_confined vcfg' hregion' hstatus hactivemem' hfrid.symm hlocC' hreach
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
      region_container_confined vcfg hlkF hopenF hframeMem rfl hloc hEreach
    rcases eq_or_lt_of_le hboundE with heqE | hltE
    · exact (swap_corollary_stackWithIndex_index_inj hEmem hframeMem heqE.symm) ▸ hEreach
    · exact hcr3 frame hframeMem E hEmem hltE oid hloc hEreach
  constructor
  · -- forward
    rintro ⟨G, hGmem, hGreach⟩
    have hbound : frame.index ≤ G.index :=
      region_container_confined vcfg hlkF hopenF hframeMem rfl hloc hGreach
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
      region_container_confined vcfg' hlkF' hopenF' hframemem' rfl hlocSusp' hGreach
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
          · -- REGION branch: the new edge stays inside `rid`; any suffix from `oid_y` is H3-confined to `rid`, so it can never reach `oid` in a different Open region.
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
