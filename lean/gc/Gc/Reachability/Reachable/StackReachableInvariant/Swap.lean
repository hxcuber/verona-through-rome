import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Mutation.Mutation
import Gc.Model.Mutation.Stmt
import Gc.Model.Preservation
import Gc.Reachability.Reachable.Semantics
import Gc.Reachability.Reachable.StackReachableInvariant.Def
import Gc.Reachability.Reachable.Lemmas

theorem stackReachable_invariant_swap (x : VarName) (yf : FieldAccess) :
    StackReachable_invariant_for_suspended_region_objects (Stmt.swap x yf) := by
  intro cfg cfg' vcfg h hcr3 frame hframeMem hframeSusp oid hloc
  have h' : swap x yf cfg = some cfg' := h
  have vcfg' : ValidConfig cfg' := swap_valid vcfg h'
  obtain ⟨frame0, hframe0, yRef, hyr, yRefLoc, hyrl, yfRef, hyf, yfRefLoc, hyfl, hcase⟩ := swap_cases h'
  have hframe0_mem : frame0 ∈ cfg.stackWithIndex := List.mem_of_getLast? hframe0
  obtain ⟨stack_eq0, hidx00⟩ := swap_corollary_stack_eq hframe0
  have hlenEq : cfg.stackWithIndex.length = cfg.stack.length := by
    unfold RuntimeConfig.stackWithIndex; rw [List.length_mapIdx]
  have hframeSusp' : frame.index < cfg.stack.dropLast.length := by
    rw [List.length_dropLast, ← hlenEq]; exact hframeSusp
  have hltd : frame.index < frame0.index := by rw [hidx00]; exact hframeSusp'
  obtain ⟨regionF, hlkF, hopenF⟩ := l2_of_stackWithIndex vcfg hframeMem
  have finish : ∀ E : FrameWithIndex, E ∈ cfg.stackWithIndex → FrameReachable cfg E.index (Reference.OId oid) →
      FrameReachable cfg frame.index (Reference.OId oid) := by
    intro E hEmem hEreach
    have hboundE : frame.index ≤ E.index :=
      region_container_confined vcfg hlkF hopenF hframeMem rfl hloc hEreach
    rcases eq_or_lt_of_le hboundE with heqE | hltE
    · exact (swap_corollary_stackWithIndex_index_inj hEmem hframeMem heqE.symm) ▸ hEreach
    · exact hcr3 frame hframeMem E hEmem hltE oid hloc hEreach
  constructor
  · -- forward: collapse the witness down to `frame`, then transport unconditionally (always below the mutated frame).
    rintro ⟨G, hGmem, hGreach⟩
    have hFrameReach : FrameReachable cfg frame.index (Reference.OId oid) := finish G hGmem hGreach
    have hFrameReach' : FrameReachable cfg' frame.index (Reference.OId oid) :=
      (swap_frame_reachable_iff_of_lt vcfg vcfg' h' frame hframeSusp' (Reference.OId oid)).mp hFrameReach
    obtain ⟨frw, hfrwmem, hidxfrw, -, -⟩ := swap_frame_transport_up h' frame hframeMem
    exact ⟨frw, hfrwmem, hidxfrw ▸ hFrameReach'⟩
  · -- backward: G is either the mutated frame (real escape work) or below it (transports directly); "G is active" is detected via the transported `Gd`'s index.
    rintro ⟨G, hGmem, hGreach⟩
    obtain ⟨Gd, hGdmem, hidxGd, -, -⟩ := swap_frame_transport_down h' G hGmem
    by_cases hGeq : Gd.index = frame0.index
    · -- Gd (hence G) is the active/mutated frame: real escape work, per branch.
      have hGidxEq : G.index = frame0.index := by rw [← hidxGd]; exact hGeq
      have hGreachFrame0 : FrameReachable cfg' frame0.index (Reference.OId oid) := by
        rw [← hGidxEq]; exact hGreach
      obtain ⟨start, hroot, hrtg⟩ :=
        (FrameReachable_iff_reflTransGen cfg' frame0.index (Reference.OId oid)).mp hGreachFrame0
      rcases hcase with
          ⟨yoid, xRef, obj, hxb, hyoid, hyrloc, hxr, hobj, hcfg''⟩ |
          ⟨yoid, rid, region, obj, xoid, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hxrl, hxridEq, hstatus,
            hcfg''⟩ |
          ⟨yoid, rid, region, obj, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hstatus, hcfg''⟩ |
          ⟨yoid, yrid, yfoid, yfrid, region, obj, hxb, hyoid, hyrloc, hyfoid, hyfrloc, hyridEq, hyfridEq, hregion,
            hobj, hcfg''⟩
      · -- SWAP-STACK
        have hyloc0 : (Reference.OId yoid).loc? cfg = some (Location.Stk frame0.index) := by
          rw [← hyoid, ← hyrloc]; exact hyrl
        set newFrame0 : Frame := { frame0 with varMap := frame0.varMap.insert x yfRef, objMap := frame0.objMap.insert yoid (obj.insert yf.field xRef) } with newFrame0_def
        have hnewFrame0Mem : ({ newFrame0 with index := frame0.index } : FrameWithIndex) ∈ cfg'.stackWithIndex := by
          unfold RuntimeConfig.stackWithIndex
          rw [hcfg'']
          dsimp only
          rw [List.mapIdx_concat, ← hidx00]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        have main_claim : ∀ a b : Reference, Relation.ReflTransGen (ReachableStep cfg') a b →
            Relation.ReflTransGen (ReachableStep cfg) a b ∨
            ∃ frameE ∈ cfg.stackWithIndex, FrameReachable cfg frameE.index b := by
          intro a b hrtg2
          induction hrtg2 using Relation.ReflTransGen.head_induction_on with
          | refl => left; exact Relation.ReflTransGen.refl
          | @head p c hstep hrest ih =>
            rcases ih with hchain | hesc
            · by_cases hpeq : p = Reference.OId yoid
              · subst hpeq
                rcases swap_stack_yoid_step_of_ne hframe0 hyloc0 hobj hcfg'' hstep with hceq | hstepOld
                · rw [hceq] at hchain
                  right
                  refine ⟨frame0, hframe0_mem, ?_⟩
                  rw [FrameReachable_iff_reflTransGen]
                  exact ⟨xRef, Or.inl ⟨frame0, hframe0_mem, rfl, x, hxr⟩, hchain⟩
                · left; exact Relation.ReflTransGen.head hstepOld hchain
              · left
                exact Relation.ReflTransGen.head ((swap_stack_step_iff_of_ne hframe0 hobj hcfg'' p hpeq c).mpr hstep)
                  hchain
            · right; exact hesc
        rcases hroot with
            ⟨Gf, hGfmem, hGfidx, var, hvar⟩ |
            ⟨Gf, hGfmem, hGfidx, regionG, hlookupG, hbridge⟩
        · have hGfeq : Gf = ({ newFrame0 with index := frame0.index } : FrameWithIndex) :=
            swap_corollary_stackWithIndex_index_inj hGfmem hnewFrame0Mem hGfidx
          rw [hGfeq] at hvar
          by_cases hveq : var = x
          · rw [hveq, newFrame0_def] at hvar
            dsimp only at hvar
            rw [AList.lookup_insert] at hvar
            injection hvar with hstartEq
            subst hstartEq
            obtain ⟨frameY, hframeYmem, hreachYw⟩ := resolveFA_frameReach hyf
            rcases main_claim yfRef (Reference.OId oid) hrtg with hchainFull | ⟨frameE, hEmem, hEreach⟩
            · have hreachY : FrameReachable cfg frameY.index (Reference.OId oid) := by
                rw [FrameReachable_iff_reflTransGen] at hreachYw ⊢
                obtain ⟨startY, hrootY, hrtgY⟩ := hreachYw
                exact ⟨startY, hrootY, hrtgY.trans hchainFull⟩
              exact ⟨frame, hframeMem, finish frameY hframeYmem hreachY⟩
            · exact ⟨frame, hframeMem, finish frameE hEmem hEreach⟩
          · rw [newFrame0_def] at hvar
            dsimp only at hvar
            rw [AList.lookup_insert_ne hveq] at hvar
            rcases main_claim start (Reference.OId oid) hrtg with hchainFull | ⟨frameE, hEmem, hEreach⟩
            · have hreach0 : FrameReachable cfg frame0.index (Reference.OId oid) :=
                (FrameReachable_iff_reflTransGen cfg frame0.index (Reference.OId oid)).mpr
                  ⟨start, Or.inl ⟨frame0, hframe0_mem, rfl, var, hvar⟩, hchainFull⟩
              exact ⟨frame, hframeMem, finish frame0 hframe0_mem hreach0⟩
            · exact ⟨frame, hframeMem, finish frameE hEmem hEreach⟩
        · -- bridge disjunct: STACK branch never touches the heap, so this is always unaffected.
          have hGfeq : Gf = ({ newFrame0 with index := frame0.index } : FrameWithIndex) :=
            swap_corollary_stackWithIndex_index_inj hGfmem hnewFrame0Mem hGfidx
          have hheapEq : cfg'.heap = cfg.heap := by rw [hcfg'']
          rw [hGfeq] at hlookupG
          dsimp only at hlookupG
          rw [hheapEq] at hlookupG
          rcases main_claim start (Reference.OId oid) hrtg with hchainFull | ⟨frameE, hEmem, hEreach⟩
          · have hreach0 : FrameReachable cfg frame0.index (Reference.OId oid) :=
              (FrameReachable_iff_reflTransGen cfg frame0.index (Reference.OId oid)).mpr
                ⟨start, Or.inr ⟨frame0, hframe0_mem, rfl, regionG, hlookupG, hbridge⟩, hchainFull⟩
            exact ⟨frame, hframeMem, finish frame0 hframe0_mem hreach0⟩
          · exact ⟨frame, hframeMem, finish frameE hEmem hEreach⟩
      · -- SWAP-REGION-OBJECT
        have hyloc0 : (Reference.OId yoid).loc? cfg = some (Location.Rgn rid) := by
          rw [← hyoid, ← hyrloc]; exact hyrl
        set newFrame0 : Frame := { frame0 with varMap := frame0.varMap.insert x yfRef } with newFrame0_def
        have hnewFrame0Mem : ({ newFrame0 with index := frame0.index } : FrameWithIndex) ∈ cfg'.stackWithIndex := by
          unfold RuntimeConfig.stackWithIndex
          rw [hcfg'']
          dsimp only
          rw [List.mapIdx_concat, ← hidx00]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        have main_claim : ∀ a b : Reference, Relation.ReflTransGen (ReachableStep cfg') a b →
            Relation.ReflTransGen (ReachableStep cfg) a b ∨
            ∃ frameE ∈ cfg.stackWithIndex, FrameReachable cfg frameE.index b := by
          intro a b hrtg2
          induction hrtg2 using Relation.ReflTransGen.head_induction_on with
          | refl => left; exact Relation.ReflTransGen.refl
          | @head p c hstep hrest ih =>
            rcases ih with hchain | hesc
            · by_cases hpeq : p = Reference.OId yoid
              · subst hpeq
                rw [hcfg''] at hstep
                rcases swap_region_stack_yoid_step_of_ne vcfg hframe0 hregion hobj hyloc0 hstep with
                    hceq | hstepOld
                · rw [hceq] at hchain
                  right
                  refine ⟨frame0, hframe0_mem, ?_⟩
                  rw [FrameReachable_iff_reflTransGen]
                  exact ⟨Reference.OId xoid, Or.inl ⟨frame0, hframe0_mem, rfl, x, hxr⟩, hchain⟩
                · left; exact Relation.ReflTransGen.head hstepOld hchain
              · left
                exact Relation.ReflTransGen.head
                  ((swap_region_stack_step_iff_of_ne vcfg hframe0 hregion hobj hstatus hcfg'' p hpeq c).mpr hstep)
                  hchain
            · right; exact hesc
        rcases hroot with
            ⟨Gf, hGfmem, hGfidx, var, hvar⟩ |
            ⟨Gf, hGfmem, hGfidx, regionG, hlookupG, hbridge⟩
        · have hGfeq : Gf = ({ newFrame0 with index := frame0.index } : FrameWithIndex) :=
            swap_corollary_stackWithIndex_index_inj hGfmem hnewFrame0Mem hGfidx
          rw [hGfeq] at hvar
          by_cases hveq : var = x
          · rw [hveq, newFrame0_def] at hvar
            dsimp only at hvar
            rw [AList.lookup_insert] at hvar
            injection hvar with hstartEq
            subst hstartEq
            obtain ⟨frameY, hframeYmem, hreachYw⟩ := resolveFA_frameReach hyf
            rcases main_claim yfRef (Reference.OId oid) hrtg with hchainFull | ⟨frameE, hEmem, hEreach⟩
            · have hreachY : FrameReachable cfg frameY.index (Reference.OId oid) := by
                rw [FrameReachable_iff_reflTransGen] at hreachYw ⊢
                obtain ⟨startY, hrootY, hrtgY⟩ := hreachYw
                exact ⟨startY, hrootY, hrtgY.trans hchainFull⟩
              exact ⟨frame, hframeMem, finish frameY hframeYmem hreachY⟩
            · exact ⟨frame, hframeMem, finish frameE hEmem hEreach⟩
          · rw [newFrame0_def] at hvar
            dsimp only at hvar
            rw [AList.lookup_insert_ne hveq] at hvar
            rcases main_claim start (Reference.OId oid) hrtg with hchainFull | ⟨frameE, hEmem, hEreach⟩
            · have hreach0 : FrameReachable cfg frame0.index (Reference.OId oid) :=
                (FrameReachable_iff_reflTransGen cfg frame0.index (Reference.OId oid)).mpr
                  ⟨start, Or.inl ⟨frame0, hframe0_mem, rfl, var, hvar⟩, hchainFull⟩
              exact ⟨frame, hframeMem, finish frame0 hframe0_mem hreach0⟩
            · exact ⟨frame, hframeMem, finish frameE hEmem hEreach⟩
        · -- bridge disjunct: this branch only touches `objMap`, never `bridgeObjectId` — always safe.
          have hGfeq : Gf = ({ newFrame0 with index := frame0.index } : FrameWithIndex) :=
            swap_corollary_stackWithIndex_index_inj hGfmem hnewFrame0Mem hGfidx
          have hGfridEq : Gf.regionId = rid := by rw [hGfeq, newFrame0_def]; exact hrid.symm
          have hlookup' : cfg'.heap.lookup Gf.regionId =
              some ({ region with objMap := region.objMap.insert yoid (obj.insert yf.field (Reference.OId xoid)) } :
                Region) := by
            rw [hGfridEq, hcfg'']; dsimp only; exact AList.lookup_insert cfg.heap
          rw [hlookup'] at hlookupG
          injection hlookupG with hlookupGEq
          rw [← hlookupGEq] at hbridge
          dsimp only at hbridge
          rcases main_claim start (Reference.OId oid) hrtg with hchainFull | ⟨frameE, hEmem, hEreach⟩
          · have hregion0 : cfg.heap.lookup frame0.regionId = some region := by rw [← hrid]; exact hregion
            have hreach0 : FrameReachable cfg frame0.index (Reference.OId oid) :=
              (FrameReachable_iff_reflTransGen cfg frame0.index (Reference.OId oid)).mpr
                ⟨start, Or.inr ⟨frame0, hframe0_mem, rfl, region, hregion0, hbridge⟩, hchainFull⟩
            exact ⟨frame, hframeMem, finish frame0 hframe0_mem hreach0⟩
          · exact ⟨frame, hframeMem, finish frameE hEmem hEreach⟩
      · -- SWAP-REGION-REGION: same shape as SWAP-REGION-OBJECT with an `RId`-valued swap; already absorbed into `hchain`, so no shape inspection needed.
        have hyloc0 : (Reference.OId yoid).loc? cfg = some (Location.Rgn rid) := by
          rw [← hyoid, ← hyrloc]; exact hyrl
        set newFrame0 : Frame := { frame0 with varMap := frame0.varMap.insert x yfRef } with newFrame0_def
        have hnewFrame0Mem : ({ newFrame0 with index := frame0.index } : FrameWithIndex) ∈ cfg'.stackWithIndex := by
          unfold RuntimeConfig.stackWithIndex
          rw [hcfg'']
          dsimp only
          rw [List.mapIdx_concat, ← hidx00]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        have main_claim : ∀ a b : Reference, Relation.ReflTransGen (ReachableStep cfg') a b →
            Relation.ReflTransGen (ReachableStep cfg) a b ∨
            ∃ frameE ∈ cfg.stackWithIndex, FrameReachable cfg frameE.index b := by
          intro a b hrtg2
          induction hrtg2 using Relation.ReflTransGen.head_induction_on with
          | refl => left; exact Relation.ReflTransGen.refl
          | @head p c hstep hrest ih =>
            rcases ih with hchain | hesc
            · by_cases hpeq : p = Reference.OId yoid
              · subst hpeq
                rw [hcfg''] at hstep
                rcases swap_region_stack_yoid_step_of_ne vcfg hframe0 hregion hobj hyloc0 hstep with
                    hceq | hstepOld
                · rw [hceq] at hchain
                  right
                  refine ⟨frame0, hframe0_mem, ?_⟩
                  rw [FrameReachable_iff_reflTransGen]
                  exact ⟨Reference.RId xrid, Or.inl ⟨frame0, hframe0_mem, rfl, x, hxr⟩, hchain⟩
                · left; exact Relation.ReflTransGen.head hstepOld hchain
              · left
                exact Relation.ReflTransGen.head
                  ((swap_region_stack_step_iff_of_ne vcfg hframe0 hregion hobj hstatus hcfg'' p hpeq c).mpr hstep)
                  hchain
            · right; exact hesc
        rcases hroot with
            ⟨Gf, hGfmem, hGfidx, var, hvar⟩ |
            ⟨Gf, hGfmem, hGfidx, regionG, hlookupG, hbridge⟩
        · have hGfeq : Gf = ({ newFrame0 with index := frame0.index } : FrameWithIndex) :=
            swap_corollary_stackWithIndex_index_inj hGfmem hnewFrame0Mem hGfidx
          rw [hGfeq] at hvar
          by_cases hveq : var = x
          · rw [hveq, newFrame0_def] at hvar
            dsimp only at hvar
            rw [AList.lookup_insert] at hvar
            injection hvar with hstartEq
            subst hstartEq
            obtain ⟨frameY, hframeYmem, hreachYw⟩ := resolveFA_frameReach hyf
            rcases main_claim yfRef (Reference.OId oid) hrtg with hchainFull | ⟨frameE, hEmem, hEreach⟩
            · have hreachY : FrameReachable cfg frameY.index (Reference.OId oid) := by
                rw [FrameReachable_iff_reflTransGen] at hreachYw ⊢
                obtain ⟨startY, hrootY, hrtgY⟩ := hreachYw
                exact ⟨startY, hrootY, hrtgY.trans hchainFull⟩
              exact ⟨frame, hframeMem, finish frameY hframeYmem hreachY⟩
            · exact ⟨frame, hframeMem, finish frameE hEmem hEreach⟩
          · rw [newFrame0_def] at hvar
            dsimp only at hvar
            rw [AList.lookup_insert_ne hveq] at hvar
            rcases main_claim start (Reference.OId oid) hrtg with hchainFull | ⟨frameE, hEmem, hEreach⟩
            · have hreach0 : FrameReachable cfg frame0.index (Reference.OId oid) :=
                (FrameReachable_iff_reflTransGen cfg frame0.index (Reference.OId oid)).mpr
                  ⟨start, Or.inl ⟨frame0, hframe0_mem, rfl, var, hvar⟩, hchainFull⟩
              exact ⟨frame, hframeMem, finish frame0 hframe0_mem hreach0⟩
            · exact ⟨frame, hframeMem, finish frameE hEmem hEreach⟩
        · -- bridge disjunct: this branch only touches `objMap`, never `bridgeObjectId` — always safe.
          have hGfeq : Gf = ({ newFrame0 with index := frame0.index } : FrameWithIndex) :=
            swap_corollary_stackWithIndex_index_inj hGfmem hnewFrame0Mem hGfidx
          have hGfridEq : Gf.regionId = rid := by rw [hGfeq, newFrame0_def]; exact hrid.symm
          have hlookup' : cfg'.heap.lookup Gf.regionId =
              some ({ region with objMap := region.objMap.insert yoid (obj.insert yf.field (Reference.RId xrid)) } :
                Region) := by
            rw [hGfridEq, hcfg'']; dsimp only; exact AList.lookup_insert cfg.heap
          rw [hlookup'] at hlookupG
          injection hlookupG with hlookupGEq
          rw [← hlookupGEq] at hbridge
          dsimp only at hbridge
          rcases main_claim start (Reference.OId oid) hrtg with hchainFull | ⟨frameE, hEmem, hEreach⟩
          · have hregion0 : cfg.heap.lookup frame0.regionId = some region := by rw [← hrid]; exact hregion
            have hreach0 : FrameReachable cfg frame0.index (Reference.OId oid) :=
              (FrameReachable_iff_reflTransGen cfg frame0.index (Reference.OId oid)).mpr
                ⟨start, Or.inr ⟨frame0, hframe0_mem, rfl, region, hregion0, hbridge⟩, hchainFull⟩
            exact ⟨frame, hframeMem, finish frame0 hframe0_mem hreach0⟩
          · exact ⟨frame, hframeMem, finish frameE hEmem hEreach⟩
      · -- SWAP-REGION-BRIDGE
        have hyloc0 : (Reference.OId yoid).loc? cfg = some (Location.Rgn yrid) := by
          rw [← hyoid, ← hyrloc]; exact hyrl
        have hregion0 : cfg.heap.lookup frame0.regionId = some region := by rw [← hyridEq]; exact hregion
        obtain ⟨regionL2, hlkL2, hopenL2⟩ := l2_of_stackWithIndex vcfg hframe0_mem
        have hopenReg : region.status = Status.Open := by
          rw [hlkL2] at hregion0; injection hregion0 with hregion0eq; rw [← hregion0eq]; exact hopenL2
        have hswi_eq : cfg'.stackWithIndex = cfg.stackWithIndex := by
          unfold RuntimeConfig.stackWithIndex
          rw [show cfg'.stack = cfg.stack from by rw [hcfg'']]
        have main_claim : ∀ a b : Reference, Relation.ReflTransGen (ReachableStep cfg') a b →
            Relation.ReflTransGen (ReachableStep cfg) a b ∨
            ∃ frameE ∈ cfg.stackWithIndex, FrameReachable cfg frameE.index b := by
          intro a b hrtg2
          induction hrtg2 using Relation.ReflTransGen.head_induction_on with
          | refl => left; exact Relation.ReflTransGen.refl
          | @head p c hstep hrest ih =>
            rcases ih with hchain | hesc
            · by_cases hpeq : p = Reference.OId yoid
              · subst hpeq
                rw [hcfg''] at hstep
                rcases swap_bridge_yoid_step_of_ne vcfg hregion hobj hyloc0 hstep with hceq | hstepOld
                · rw [hceq] at hchain
                  right
                  refine ⟨frame0, hframe0_mem, ?_⟩
                  rw [FrameReachable_iff_reflTransGen]
                  exact ⟨Reference.OId region.bridgeObjectId, Or.inr ⟨frame0, hframe0_mem, rfl, region, hregion0, rfl⟩,
                    hchain⟩
                · left; exact Relation.ReflTransGen.head hstepOld hchain
              · left
                exact Relation.ReflTransGen.head
                  ((swap_bridge_step_iff_of_ne vcfg hregion hobj hopenReg hcfg'' p hpeq c).mpr hstep) hchain
            · right; exact hesc
        rcases hroot with
            ⟨Gf, hGfmem, hGfidx, var, hvar⟩ |
            ⟨Gf, hGfmem, hGfidx, regionG, hlookupG, hbridge⟩
        · -- var disjunct: `varMap` is never touched by this branch, so it's always unaffected.
          have hGfeq : Gf = frame0 := swap_corollary_stackWithIndex_index_inj (hswi_eq ▸ hGfmem) hframe0_mem hGfidx
          rw [hGfeq] at hvar
          rcases main_claim start (Reference.OId oid) hrtg with hchainFull | ⟨frameE, hEmem, hEreach⟩
          · have hreach0 : FrameReachable cfg frame0.index (Reference.OId oid) :=
              (FrameReachable_iff_reflTransGen cfg frame0.index (Reference.OId oid)).mpr
                ⟨start, Or.inl ⟨frame0, hframe0_mem, rfl, var, hvar⟩, hchainFull⟩
            exact ⟨frame, hframeMem, finish frame0 hframe0_mem hreach0⟩
          · exact ⟨frame, hframeMem, finish frameE hEmem hEreach⟩
        · -- bridge disjunct: always the escape trigger (the region's `bridgeObjectId` always changes, to `yfoid`).
          have hGfeq : Gf = frame0 := swap_corollary_stackWithIndex_index_inj (hswi_eq ▸ hGfmem) hframe0_mem hGfidx
          have hGfridEq : Gf.regionId = yrid := by rw [hGfeq]; exact hyridEq.symm
          have hlookup' : cfg'.heap.lookup Gf.regionId = some ({ region with bridgeObjectId := yfoid, objMap := region.objMap.insert yoid (obj.insert yf.field (Reference.OId region.bridgeObjectId)) } : Region) := by
            rw [hGfridEq, hcfg'']; dsimp only; exact AList.lookup_insert cfg.heap
          rw [hlookup'] at hlookupG
          injection hlookupG with hlookupGEq
          rw [← hlookupGEq] at hbridge
          dsimp only at hbridge
          have hstarteq : start = yfRef := by rw [hbridge, hyfoid]
          rw [hstarteq] at hrtg
          obtain ⟨frameY, hframeYmem, hreachYw⟩ := resolveFA_frameReach hyf
          rcases main_claim yfRef (Reference.OId oid) hrtg with hchainFull | ⟨frameE, hEmem, hEreach⟩
          · have hreachY : FrameReachable cfg frameY.index (Reference.OId oid) := by
              rw [FrameReachable_iff_reflTransGen] at hreachYw ⊢
              obtain ⟨startY, hrootY, hrtgY⟩ := hreachYw
              exact ⟨startY, hrootY, hrtgY.trans hchainFull⟩
            exact ⟨frame, hframeMem, finish frameY hframeYmem hreachY⟩
          · exact ⟨frame, hframeMem, finish frameE hEmem hEreach⟩
    · have hGdltlen : Gd.index < cfg.stack.length := by
        obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hGdmem
        have hidx : Gd.index = n := by rw [← hfeq]
        rw [hidx]; exact hn
      have hstackLen1 : cfg.stack.length = frame0.index + 1 := by
        conv_lhs => rw [stack_eq0]
        rw [List.length_append, List.length_singleton, hidx00]
      have hGdle : Gd.index ≤ frame0.index := by
        have hlt : Gd.index < frame0.index + 1 := by rw [← hstackLen1]; exact hGdltlen
        exact Nat.lt_succ_iff.mp hlt
      have hGdlt0 : Gd.index < frame0.index := lt_of_le_of_ne hGdle hGeq
      have hGdlt : Gd.index < cfg.stack.dropLast.length := by rw [← hidx00]; exact hGdlt0
      have hGreachGd : FrameReachable cfg' Gd.index (Reference.OId oid) := by rw [hidxGd]; exact hGreach
      have hGdreach : FrameReachable cfg Gd.index (Reference.OId oid) :=
        (swap_frame_reachable_iff_of_lt vcfg vcfg' h' Gd hGdlt (Reference.OId oid)).mpr hGreachGd
      have hFrameReach := finish Gd hGdmem hGdreach
      exact ⟨frame, hframeMem, hFrameReach⟩
