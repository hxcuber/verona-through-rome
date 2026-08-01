import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Mutation.Mutation
import Gc.Model.Mutation.Stmt
import Gc.Model.Preservation
import Gc.Reachability.Reachable.Semantics
import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.Def
import Gc.Reachability.Reachable.Lemmas

theorem frameReachableAtLaterFrame_step_swap (x : VarName) (yf : FieldAccess) :
    FrameReachableAtLaterFrame_step (Stmt.swap x yf) := by
  intro cfg cfg' vcfg h hFR3 frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  have h' : swap x yf cfg = some cfg' := h
  have vcfg' : ValidConfig cfg' := swap_valid vcfg h'
  obtain ⟨frame0, hframe0, yRef, hyr, yRefLoc, hyrl, yfRef, hyf, yfRefLoc, hyfl, hcase⟩ := swap_cases h'
  have hframe0_mem : frame0 ∈ cfg.stackWithIndex := List.mem_of_getLast? hframe0
  obtain ⟨stack_eq0, hidx00⟩ := swap_corollary_stack_eq hframe0
  -- Cfg-side stand-ins for `frame`/`frame'`, sharing index/regionId (all the generic transport lemma guarantees).
  obtain ⟨Gf0, hGf0mem, hidxGf0, hridGf0, -⟩ := swap_frame_transport_down h' frame hframeMem
  obtain ⟨Gd, hGdmem, hidxGd, -, -⟩ := swap_frame_transport_down h' frame' hframe'Mem
  have hGdltlen : Gd.index < cfg.stack.length := by
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hGdmem
    have hidx : Gd.index = n := by rw [← hfeq]
    rw [hidx]; exact hn
  have hstackLen1 : cfg.stack.length = frame0.index + 1 := by
    conv_lhs => rw [stack_eq0]
    rw [List.length_append, List.length_singleton, hidx00]
  have hGdle : Gd.index ≤ frame0.index := by
    have hlt2 : Gd.index < frame0.index + 1 := by rw [← hstackLen1]; exact hGdltlen
    exact Nat.lt_succ_iff.mp hlt2
  have hframe'leFrame0 : frame'.index ≤ frame0.index := hidxGd ▸ hGdle
  have hframeLt : frame.index < cfg.stack.dropLast.length := by
    rw [← hidx00]
    exact lt_of_lt_of_le hlt hframe'leFrame0
  have hloc_cfg : (Reference.OId oid).loc? cfg = some (Location.Rgn Gf0.regionId) := by
    rw [hridGf0]
    rcases hcase with
        ⟨yoid, xRef, obj, hxb, hyoid, hyrloc, hxr, hobj, hcfg''⟩ |
        ⟨yoid, rid, region, obj, xoid, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hxrl, hxridEq, hstatus,
          hcfg''⟩ |
        ⟨yoid, rid, region, obj, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hstatus, hcfg''⟩ |
        ⟨yoid, yrid, yfoid, yfrid, region, obj, hxb, hyoid, hyrloc, hyfoid, hyfrloc, hyridEq, hyfridEq, hregion, hobj,
          hcfg''⟩
    · have hlocEq : (Reference.OId oid).loc? cfg = (Reference.OId oid).loc? cfg' := by
        rw [hcfg'']; exact swap_corollary_stack_loc_eq hframe0 hobj oid
      rw [hlocEq]; exact hloc
    · have hlocEq : (Reference.OId oid).loc? cfg = (Reference.OId oid).loc? cfg' := by
        rw [hcfg'']; exact swap_region_stack_loc_eq vcfg hframe0 hregion hobj oid
      rw [hlocEq]; exact hloc
    · have hlocEq : (Reference.OId oid).loc? cfg = (Reference.OId oid).loc? cfg' := by
        rw [hcfg'']; exact swap_region_stack_loc_eq vcfg hframe0 hregion hobj oid
      rw [hlocEq]; exact hloc
    · have hlocEq : (Reference.OId oid).loc? cfg = (Reference.OId oid).loc? cfg' := by
        rw [hcfg'']
        exact swap_corollary_region_loc_eq vcfg hregion hobj rfl oid
      rw [hlocEq]; exact hloc
  obtain ⟨regionF, hlkF, hopenF⟩ := l2_of_stackWithIndex vcfg hGf0mem
  -- Collapses a `cfg`-side witness at or beyond `Gf0`'s index back to `frame`, via `Gf0`.
  have finish : ∀ E : FrameWithIndex, E ∈ cfg.stackWithIndex → FrameReachable cfg E.index (Reference.OId oid) →
      FrameReachable cfg frame.index (Reference.OId oid) := by
    intro E hEmem hEreach
    have hboundE : Gf0.index ≤ E.index :=
      region_container_confined vcfg hlkF hopenF hGf0mem rfl hloc_cfg hEreach
    rcases eq_or_lt_of_le hboundE with heqE | hltE
    · rw [← hidxGf0]
      exact (swap_corollary_stackWithIndex_index_inj hEmem hGf0mem heqE.symm) ▸ hEreach
    · have hresult : FrameReachable cfg Gf0.index (Reference.OId oid) :=
        hFR3 Gf0 hGf0mem E hEmem hltE oid hloc_cfg hEreach
      rw [hidxGf0] at hresult
      exact hresult
  have transportUp : FrameReachable cfg frame.index (Reference.OId oid) →
      FrameReachable cfg' frame.index (Reference.OId oid) :=
    fun hFrameReach => (swap_frame_reachable_iff_of_lt vcfg vcfg' h' frame hframeLt (Reference.OId oid)).mp hFrameReach
  by_cases hframe'eq : frame'.index = frame0.index
  · -- frame' IS the active/mutated frame: real escape work, per branch.
    apply transportUp
    have hreachFrame0 : FrameReachable cfg' frame0.index (Reference.OId oid) := by
      rw [← hframe'eq]; exact hreach
    obtain ⟨start, hroot, hrtg⟩ :=
      (FrameReachable_iff_reflTransGen cfg' frame0.index (Reference.OId oid)).mp hreachFrame0
    rcases hcase with
        ⟨yoid, xRef, obj, hxb, hyoid, hyrloc, hxr, hobj, hcfg''⟩ |
        ⟨yoid, rid, region, obj, xoid, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hxrl, hxridEq, hstatus,
          hcfg''⟩ |
        ⟨yoid, rid, region, obj, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hstatus, hcfg''⟩ |
        ⟨yoid, yrid, yfoid, yfrid, region, obj, hxb, hyoid, hyrloc, hyfoid, hyfrloc, hyridEq, hyfridEq, hregion, hobj,
          hcfg''⟩
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
            exact finish frameY hframeYmem hreachY
          · exact finish frameE hEmem hEreach
        · rw [newFrame0_def] at hvar
          dsimp only at hvar
          rw [AList.lookup_insert_ne hveq] at hvar
          rcases main_claim start (Reference.OId oid) hrtg with hchainFull | ⟨frameE, hEmem, hEreach⟩
          · have hreach0 : FrameReachable cfg frame0.index (Reference.OId oid) :=
              (FrameReachable_iff_reflTransGen cfg frame0.index (Reference.OId oid)).mpr
                ⟨start, Or.inl ⟨frame0, hframe0_mem, rfl, var, hvar⟩, hchainFull⟩
            exact finish frame0 hframe0_mem hreach0
          · exact finish frameE hEmem hEreach
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
          exact finish frame0 hframe0_mem hreach0
        · exact finish frameE hEmem hEreach
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
            exact finish frameY hframeYmem hreachY
          · exact finish frameE hEmem hEreach
        · rw [newFrame0_def] at hvar
          dsimp only at hvar
          rw [AList.lookup_insert_ne hveq] at hvar
          rcases main_claim start (Reference.OId oid) hrtg with hchainFull | ⟨frameE, hEmem, hEreach⟩
          · have hreach0 : FrameReachable cfg frame0.index (Reference.OId oid) :=
              (FrameReachable_iff_reflTransGen cfg frame0.index (Reference.OId oid)).mpr
                ⟨start, Or.inl ⟨frame0, hframe0_mem, rfl, var, hvar⟩, hchainFull⟩
            exact finish frame0 hframe0_mem hreach0
          · exact finish frameE hEmem hEreach
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
          exact finish frame0 hframe0_mem hreach0
        · exact finish frameE hEmem hEreach
    · -- SWAP-REGION-REGION: same shape as SWAP-REGION-OBJECT, just with an `RId`-valued swap.
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
            exact finish frameY hframeYmem hreachY
          · exact finish frameE hEmem hEreach
        · rw [newFrame0_def] at hvar
          dsimp only at hvar
          rw [AList.lookup_insert_ne hveq] at hvar
          rcases main_claim start (Reference.OId oid) hrtg with hchainFull | ⟨frameE, hEmem, hEreach⟩
          · have hreach0 : FrameReachable cfg frame0.index (Reference.OId oid) :=
              (FrameReachable_iff_reflTransGen cfg frame0.index (Reference.OId oid)).mpr
                ⟨start, Or.inl ⟨frame0, hframe0_mem, rfl, var, hvar⟩, hchainFull⟩
            exact finish frame0 hframe0_mem hreach0
          · exact finish frameE hEmem hEreach
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
          exact finish frame0 hframe0_mem hreach0
        · exact finish frameE hEmem hEreach
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
          exact finish frame0 hframe0_mem hreach0
        · exact finish frameE hEmem hEreach
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
          exact finish frameY hframeYmem hreachY
        · exact finish frameE hEmem hEreach
  · -- frame' is not the active/mutated frame: unconditional transport both ways.
    have hGdlt0 : Gd.index < frame0.index := by
      rw [hidxGd]; exact lt_of_le_of_ne hframe'leFrame0 hframe'eq
    have hGdlt : Gd.index < cfg.stack.dropLast.length := by rw [← hidx00]; exact hGdlt0
    have hframe'Lt : frame'.index < cfg.stack.dropLast.length := by rw [← hidxGd]; exact hGdlt
    have hreach_cfg : FrameReachable cfg frame'.index (Reference.OId oid) :=
      (swap_frame_reachable_iff_of_lt vcfg vcfg' h' frame' hframe'Lt (Reference.OId oid)).mpr hreach
    have hGdreach : FrameReachable cfg Gd.index (Reference.OId oid) := by rw [hidxGd]; exact hreach_cfg
    have hltGd : Gf0.index < Gd.index := by rw [hidxGf0, hidxGd]; exact hlt
    have hresult : FrameReachable cfg Gf0.index (Reference.OId oid) :=
      hFR3 Gf0 hGf0mem Gd hGdmem hltGd oid hloc_cfg hGdreach
    apply transportUp
    rw [hidxGf0] at hresult
    exact hresult
