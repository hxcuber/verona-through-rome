import Gc.Reachability.Referencable.Basic
import Gc.Reachability.Referencable.Lemmas

theorem varAsgn_cr3 : ValidReachableConfig cfg →
  varAsgn xf y cfg = some cfg' →
  CR3 cfg' := by
  intro vrcfg h
  have vcfg := vrcfg.toValidConfig
  have vcfg' := varAsgn_valid vcfg h
  have hRefStepIff : ∀ a b, RefStep cfg a b ↔ RefStep cfg' a b := by
    intro a b
    unfold RefStep
    rw [varAsgn_corollary_objAt_eq vcfg vcfg' h a]
  obtain ⟨frame0, hframe0, hcase⟩ := varAsgn_cases h
  have stack_eq0 : cfg.stack = cfg.stack.dropLast ++ [frame0] :=
    (List.dropLast_append_getLast? frame0 hframe0).symm
  set frame0W : FrameWithIndex := { frame0 with index := cfg.stack.dropLast.length } with frame0W_def
  have hframe0W_mem : frame0W ∈ cfg.stackWithIndex := by
    unfold RuntimeConfig.stackWithIndex
    rw [stack_eq0, List.mapIdx_concat]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hframe0_max : ∀ fr : FrameWithIndex, fr ∈ cfg.stackWithIndex → fr.index ≤ frame0W.index := by
    intro fr hfr
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr
    have hidxfr : fr.index = n := by rw [← hfeq]
    have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq0]; simp
    rw [hlen] at hn
    rw [hidxfr]
    exact Nat.le_of_lt_succ hn
  unfold CR3
  intro frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  obtain ⟨frameD, hframeDMem, hidxD, hridD, _⟩ := varAsgn_corollary_frame_transport_down h frame hframeMem
  obtain ⟨frameD', hframeD'Mem, hidxD', hridD', hbvD'⟩ :=
    varAsgn_corollary_frame_transport_down h frame' hframe'Mem
  have hltD : frameD.index < frameD'.index := by rw [hidxD, hidxD']; exact hlt
  have hD'_le_frame0 : frameD'.index ≤ frame0W.index := hframe0_max frameD' hframeD'Mem
  have hD_lt_frame0 : frameD.index < frame0W.index := lt_of_lt_of_le hltD hD'_le_frame0
  have hlocDown : (Reference.OId oid).loc? cfg = some (Location.Rgn frameD.regionId) := by
    rw [hridD, varAsgn_corollary_loc_eq vcfg h oid]; exact hloc
  rw [FrameReferencable_iff_reflTransGen] at hreach
  obtain ⟨start, hroot, hrtg⟩ := hreach
  have hrtgDown : Relation.ReflTransGen (RefStep cfg) start (Reference.OId oid) :=
    hrtg.mono (fun a b hab => (hRefStepIff a b).mpr hab)
  have escape : ∀ oidw : ObjectId, resolveFA y cfg = some (Reference.OId oidw) →
      start = Reference.OId oidw →
      FrameReferencable cfg frameD.index (Reference.OId oid) := by
    intro oidw hyf hstarteq
    have hrtgDownW : Relation.ReflTransGen (RefStep cfg) (Reference.OId oidw) (Reference.OId oid) := by
      rw [← hstarteq]; exact hrtgDown
    obtain ⟨frameY, hframeYMem, hreachYw⟩ := resolveFA_frameReach hyf
    have hreachY : FrameReferencable cfg frameY.index (Reference.OId oid) := by
      rw [FrameReferencable_iff_reflTransGen] at hreachYw ⊢
      obtain ⟨startY, hrootY, hrtgY⟩ := hreachYw
      exact ⟨startY, hrootY, hrtgY.trans hrtgDownW⟩
    have hownerbound := FrameReferencable_owner_index_le cfg vcfg frameY hreachY frameD.regionId
      hlocDown frameD hframeDMem rfl
    by_cases heqidx : frameD.index = frameY.index
    · have hFYeq : frameY = frameD := swap_corollary_stackWithIndex_index_inj hframeYMem hframeDMem heqidx.symm
      rw [← hFYeq]; exact hreachY
    · have hltidx : frameD.index < frameY.index := lt_of_le_of_ne hownerbound heqidx
      exact vrcfg.cr3 frameD hframeDMem frameY hframeYMem hltidx oid hlocDown hreachY
  have hconcDown : FrameReferencable cfg frameD.index (Reference.OId oid) := by
    rcases hcase with
      ⟨oidw, ridw, regionw, hyf, hxb, hlocw, hridEqw, hregionw, hcfg'⟩ | ⟨oidw, hyf, hxb, hresolve, hcfg'⟩
    · -- BRIDGE branch: cfg'.stack = cfg.stack literally, so FrameRoot's var disjunct is
      -- unconditionally unaffected; the bridge disjunct changes only frame0's own region's
      -- bridgeObjectId (old value -> oidw).
      have hswi_eq : cfg'.stackWithIndex = cfg.stackWithIndex := by
        unfold RuntimeConfig.stackWithIndex; rw [show cfg'.stack = cfg.stack from by rw [hcfg']]
      rcases hroot with ⟨fr1, hfr1, hidx1, var, hlookup1⟩ | ⟨fr1, hfr1, hidx1, region1, hlookup1, hstart⟩
      · rw [hswi_eq] at hfr1
        have hrootDown : FrameRoot cfg frameD'.index start := Or.inl ⟨fr1, hfr1, by rw [hidxD', ← hidx1], var, hlookup1⟩
        have hreachD' : FrameReferencable cfg frameD'.index (Reference.OId oid) :=
          (FrameReferencable_iff_reflTransGen cfg frameD'.index (Reference.OId oid)).mpr ⟨start, hrootDown, hrtgDown⟩
        exact vrcfg.cr3 frameD hframeDMem frameD' hframeD'Mem hltD oid hlocDown hreachD'
      · rw [hswi_eq] at hfr1
        by_cases hrideq : fr1.regionId = ridw
        · have hridEqw' : frame0W.regionId = ridw := hridEqw
          have hidx_eq := merge_corollary_regionId_unique_index vcfg.s1 hfr1 hframe0W_mem (hrideq.trans hridEqw'.symm)
          have hfr1eq : fr1 = frame0W := swap_corollary_stackWithIndex_index_inj hfr1 hframe0W_mem hidx_eq
          have hbridgeEq : region1.bridgeObjectId = oidw := by
            have hlookup1' : cfg'.heap.lookup ridw =
                some ({ bridgeObjectId := oidw, objMap := regionw.objMap, status := regionw.status } : Region) := by
              rw [hcfg']; exact AList.lookup_insert (a := ridw)
                (b := ({ bridgeObjectId := oidw, objMap := regionw.objMap, status := regionw.status } : Region)) cfg.heap
            rw [hrideq, hlookup1'] at hlookup1
            injection hlookup1 with hlookup1_eq
            rw [← hlookup1_eq]
          have hstarteq : start = Reference.OId oidw := by rw [hstart, hbridgeEq]
          exact escape oidw hyf hstarteq
        · have hlookup1_cfg : cfg.heap.lookup fr1.regionId = some region1 := by
            have heq : cfg'.heap.lookup fr1.regionId = cfg.heap.lookup fr1.regionId := by
              rw [hcfg']; exact AList.lookup_insert_ne hrideq
            rw [← heq]; exact hlookup1
          have hrootDown : FrameRoot cfg frameD'.index start :=
            Or.inr ⟨fr1, hfr1, by rw [hidxD', ← hidx1], region1, hlookup1_cfg, hstart⟩
          have hreachD' : FrameReferencable cfg frameD'.index (Reference.OId oid) :=
            (FrameReferencable_iff_reflTransGen cfg frameD'.index (Reference.OId oid)).mpr ⟨start, hrootDown, hrtgDown⟩
          exact vrcfg.cr3 frameD hframeDMem frameD' hframeD'Mem hltD oid hlocDown hreachD'
    · -- FRESH-VAR branch: heap is untouched entirely, and only frame0's own varMap gains one new
      -- key (`xf`, previously unbound per `hresolve`); every other position (and every bridge
      -- root, at every position) is unaffected.
      have hswi_bridge_ok : ∀ fr1 : FrameWithIndex, fr1 ∈ cfg'.stackWithIndex →
          ∃ fr1D : FrameWithIndex, fr1D ∈ cfg.stackWithIndex ∧ fr1D.index = fr1.index ∧ fr1D.regionId = fr1.regionId :=
        fun fr1 hfr1 => by
          obtain ⟨fr1D, hfr1DMem, hidx1D, hrid1D, _⟩ := varAsgn_corollary_frame_transport_down h fr1 hfr1
          exact ⟨fr1D, hfr1DMem, hidx1D, hrid1D⟩
      have hheap_eq : cfg'.heap = cfg.heap := by rw [hcfg']
      rcases hroot with ⟨fr1, hfr1, hidx1, var, hlookup1⟩ | ⟨fr1, hfr1, hidx1, region1, hlookup1, hstart⟩
      · obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr1
        have hidx1n : fr1.index = n := by rw [← hfeq]
        by_cases hlast : n = cfg.stack.dropLast.length
        · -- fr1 sits at frame0's own (mutated) position: either an OLD var (transports directly
          -- via `AList.lookup_insert_ne`), or exactly the newly-inserted `xf`.
          have hfr1_varMap : fr1.varMap = frame0.varMap.insert xf (Reference.OId oidw) := by
            have hget' : cfg'.stack[n]? = some fr1.toFrame := by
              rw [show fr1.toFrame = cfg'.stack[n] from by rw [← hfeq]]
              exact List.getElem?_eq_getElem hn
            rw [hcfg'] at hget'
            dsimp only at hget'
            rw [hlast] at hget'
            simp only [List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero] at hget'
            injection hget' with hget'_eq
            rw [← hget'_eq]
          by_cases hvareq : var = xf
          · have hstarteq : start = Reference.OId oidw := by
              have heq1 : fr1.varMap.lookup var = some start := hlookup1
              rw [hvareq, hfr1_varMap, AList.lookup_insert] at heq1
              injection heq1 with heq1'
              exact heq1'.symm
            exact escape oidw hyf hstarteq
          · have hlookup1_cfg : frame0.varMap.lookup var = some start := by
              have heq1 : fr1.varMap.lookup var = some start := hlookup1
              rw [hfr1_varMap, AList.lookup_insert_ne hvareq] at heq1
              exact heq1
            have hrootDown : FrameRoot cfg frameD'.index start :=
              Or.inl ⟨frame0W, hframe0W_mem, by rw [hidxD', ← hidx1, hidx1n, frame0W_def, hlast], var,
                hlookup1_cfg⟩
            have hreachD' : FrameReferencable cfg frameD'.index (Reference.OId oid) :=
              (FrameReferencable_iff_reflTransGen cfg frameD'.index (Reference.OId oid)).mpr ⟨start, hrootDown, hrtgDown⟩
            exact vrcfg.cr3 frameD hframeDMem frameD' hframeD'Mem hltD oid hlocDown hreachD'
        · have hlt : n < cfg.stack.dropLast.length := by
            have hlen' : cfg'.stack.length = cfg.stack.dropLast.length + 1 := by rw [hcfg']; simp
            have hn' : n < cfg'.stack.length := hn
            rw [hlen'] at hn'
            exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hn') hlast
          have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
            conv_lhs => rw [stack_eq0]
            rw [List.getElem?_append_left hlt]
          have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
            rw [hcfg']; dsimp only; rw [List.getElem?_append_left hlt]
          have hfr1_get : cfg'.stack[n]? = some fr1.toFrame := by
            rw [show fr1.toFrame = cfg'.stack[n] from by rw [← hfeq]]
            exact List.getElem?_eq_getElem hn
          have hcfgn : cfg.stack[n]? = some fr1.toFrame := by rw [e1, ← e2, hfr1_get]
          obtain ⟨h1, heq⟩ := List.getElem?_eq_some_iff.mp hcfgn
          have hfr1Mem : fr1 ∈ cfg.stackWithIndex := by
            unfold RuntimeConfig.stackWithIndex
            exact List.mem_mapIdx.mpr ⟨n, h1, by rw [heq, ← hidx1n]⟩
          have hrootDown : FrameRoot cfg frameD'.index start := Or.inl ⟨fr1, hfr1Mem, by rw [hidxD', ← hidx1], var, hlookup1⟩
          have hreachD' : FrameReferencable cfg frameD'.index (Reference.OId oid) :=
            (FrameReferencable_iff_reflTransGen cfg frameD'.index (Reference.OId oid)).mpr ⟨start, hrootDown, hrtgDown⟩
          exact vrcfg.cr3 frameD hframeDMem frameD' hframeD'Mem hltD oid hlocDown hreachD'
      · obtain ⟨fr1D, hfr1DMem, hidx1D, hrid1D⟩ := hswi_bridge_ok fr1 hfr1
        have hlookup1_cfg : cfg.heap.lookup fr1D.regionId = some region1 := by
          rw [hrid1D, ← hheap_eq]; exact hlookup1
        have hrootDown : FrameRoot cfg frameD'.index start :=
          Or.inr ⟨fr1D, hfr1DMem, by rw [hidxD', ← hidx1, hidx1D], region1, hlookup1_cfg, hstart⟩
        have hreachD' : FrameReferencable cfg frameD'.index (Reference.OId oid) :=
          (FrameReferencable_iff_reflTransGen cfg frameD'.index (Reference.OId oid)).mpr ⟨start, hrootDown, hrtgDown⟩
        exact vrcfg.cr3 frameD hframeDMem frameD' hframeD'Mem hltD oid hlocDown hreachD'
  -- Final UP transport: `frame` (the CR3-quantified suspended-region owner) is never frame0
  -- (index/regionId untouched everywhere), so its own root set and every RefStep hop are
  -- unconditionally unaffected by the mutation.
  have hframe_lt_frame0 : frameD.index < frame0W.index := hD_lt_frame0
  rw [FrameReferencable_iff_reflTransGen] at hconcDown
  obtain ⟨start2, hroot2, hrtg2⟩ := hconcDown
  have hrootUp : FrameRoot cfg' frameD.index start2 := by
    have hne : frameD.index ≠ frame0W.index := Nat.ne_of_lt hframe_lt_frame0
    rcases hroot2 with ⟨fr2, hfr2, hidx2, var, hlookup2⟩ | ⟨fr2, hfr2, hidx2, region2, hlookup2, hstart2⟩
    · rw [← hidx2] at hne
      obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr2
      have hidx2n : fr2.index = n := by rw [← hfeq]
      have hlast : n ≠ cfg.stack.dropLast.length := by rw [hidx2n] at hne; exact hne
      have hlt : n < cfg.stack.dropLast.length := by
        have hn' : n < cfg.stack.length := hn
        rw [show cfg.stack.length = cfg.stack.dropLast.length + 1 from by rw [stack_eq0]; simp] at hn'
        exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hn') hlast
      have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
        conv_lhs => rw [stack_eq0]
        rw [List.getElem?_append_left hlt]
      have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
        rcases hcase with
          ⟨oidw, ridw, regionw, hyf, hxb, hlocw, hridEqw, hregionw, hcfg'⟩ | ⟨oidw, hyf, hxb, hresolve, hcfg'⟩
        · rw [hcfg']; exact e1
        · rw [hcfg']; dsimp only; rw [List.getElem?_append_left hlt]
      have hfr2_get : cfg.stack[n]? = some fr2.toFrame := by
        rw [show fr2.toFrame = cfg.stack[n] from by rw [← hfeq]]
        exact List.getElem?_eq_getElem hn
      have hcfg'n : cfg'.stack[n]? = some fr2.toFrame := by rw [e2, ← e1, hfr2_get]
      obtain ⟨h1, heq⟩ := List.getElem?_eq_some_iff.mp hcfg'n
      have hfr2Mem : fr2 ∈ cfg'.stackWithIndex := by
        unfold RuntimeConfig.stackWithIndex
        exact List.mem_mapIdx.mpr ⟨n, h1, by rw [heq, ← hidx2n]⟩
      exact Or.inl ⟨fr2, hfr2Mem, hidx2, var, hlookup2⟩
    · rcases hcase with
        ⟨oidw, ridw, regionw, hyf, hxb, hlocw, hridEqw, hregionw, hcfg'⟩ | ⟨oidw, hyf, hxb, hresolve, hcfg'⟩
      · have hswi_eq2 : cfg'.stackWithIndex = cfg.stackWithIndex := by
          unfold RuntimeConfig.stackWithIndex; rw [show cfg'.stack = cfg.stack from by rw [hcfg']]
        have hfr2Mem' : fr2 ∈ cfg'.stackWithIndex := by rw [hswi_eq2]; exact hfr2
        by_cases hrideq : fr2.regionId = ridw
        · exfalso
          have hridEqw' : frame0W.regionId = ridw := hridEqw
          have hidx_eq := merge_corollary_regionId_unique_index vcfg.s1 hfr2 hframe0W_mem (hrideq.trans hridEqw'.symm)
          rw [hidx2] at hidx_eq
          exact hne hidx_eq
        · have hlookup2' : cfg'.heap.lookup fr2.regionId = some region2 := by
            rw [hcfg']; rw [AList.lookup_insert_ne hrideq]; exact hlookup2
          exact Or.inr ⟨fr2, hfr2Mem', hidx2, region2, hlookup2', hstart2⟩
      · have hheap_eq : cfg'.heap = cfg.heap := by rw [hcfg']
        obtain ⟨fr2D', hfr2D'Mem, hidx2D', hrid2D', _⟩ := varAsgn_corollary_frame_transport_up h fr2 hfr2
        refine Or.inr ⟨fr2D', hfr2D'Mem, ?_, region2, ?_, hstart2⟩
        · rw [hidx2D', hidx2]
        · rw [hrid2D', hheap_eq]; exact hlookup2
  have hrtg2Up : Relation.ReflTransGen (RefStep cfg') start2 (Reference.OId oid) :=
    hrtg2.mono (fun a b hab => (hRefStepIff a b).mp hab)
  rw [FrameReferencable_iff_reflTransGen, ← hidxD]
  exact ⟨start2, hrootUp, hrtg2Up⟩

theorem varAsgn_reachable_valid : ValidReachableConfig cfg →
  varAsgn xf y cfg = some cfg' →
  ValidReachableConfig cfg' := by
  intro vrcfg h
  exact { varAsgn_valid vrcfg.toValidConfig h with cr3 := varAsgn_cr3 vrcfg h }
