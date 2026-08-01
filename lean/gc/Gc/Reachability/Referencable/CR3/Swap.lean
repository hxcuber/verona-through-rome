import Gc.Reachability.Referencable.Basic
import Gc.Reachability.Referencable.Lemmas

theorem swap_cr3 : ValidReachableConfig cfg →
  swap x yf cfg = some cfg' →
  CR3 cfg' := by
  intro vrcfg h
  have vcfg := vrcfg.toValidConfig
  have vcfg' := swap_valid vcfg h
  obtain ⟨frame0, hframe0, yRef, hyr, yRefLoc, hyrl, yfRef, hyf, yfRefLoc, hyfl, hcase⟩ := swap_cases h
  have hframe0_mem : frame0 ∈ cfg.stackWithIndex := List.mem_of_getLast? hframe0
  obtain ⟨stack_eq0, hidx00⟩ := swap_corollary_stack_eq hframe0
  have hframe0_max : ∀ fr : FrameWithIndex, fr ∈ cfg.stackWithIndex → fr.index ≤ frame0.index := by
    intro fr hfr
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr
    have hidxfr : fr.index = n := by rw [← hfeq]
    have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq0]; simp
    rw [hlen] at hn
    rw [hidxfr, hidx00]
    exact Nat.le_of_lt_succ hn
  unfold CR3
  intro frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  obtain ⟨frameD, hframeDMem, hidxD, hridD, hbvD⟩ := swap_corollary_frame_transport_down h frame hframeMem
  obtain ⟨frameD', hframeD'Mem, hidxD', hridD', hbvD'⟩ := swap_corollary_frame_transport_down h frame' hframe'Mem
  have hltD : frameD.index < frameD'.index := by rw [hidxD, hidxD']; exact hlt
  have hD'_le_frame0 : frameD'.index ≤ frame0.index := hframe0_max frameD' hframeD'Mem
  have hD_lt_frame0 : frameD.index < frame0.index := lt_of_lt_of_le hltD hD'_le_frame0
  have hframe_lt_frame0 : frame.index < frame0.index := by rw [← hidxD]; exact hD_lt_frame0
  rcases hcase with
    ⟨yoid, xRef, obj, hxb, hyoid, hyrloc, hxr, hobj, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xoid, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hxrl, hxridEq, hstatus, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hstatus, hcfg'⟩ |
    ⟨yoid, yrid, yfoid, yfrid, region, obj, hxb, hyoid, hyrloc, hyfoid, hyfrloc, hyridEq, hyfridEq, hregion, hobj,
      hcfg'⟩
  · -- SWAP-STACK: a genuine exchange within frame0 -- var x's OLD value (xRef) and the field
    -- yf.field of container yoid's OLD value (yfRef) trade places.
    have hyloc0 : (Reference.OId yoid).loc? cfg = some (Location.Stk frame0.index) := by
      rw [← hyoid, ← hyrloc]; exact hyrl
    have hfield : obj.lookup yf.field = some yfRef :=
      swap_corollary_stack_field_eq_yfRef hframe0_mem (hyoid ▸ hyr) hyloc0 hobj hyf
    have hlocEq0 := swap_corollary_stack_loc_eq (field := yf.field) (newVal := xRef)
      (newVarMap := frame0.varMap.insert x yfRef) hframe0 hobj oid
    rw [← hcfg'] at hlocEq0
    have hlocDown : (Reference.OId oid).loc? cfg = some (Location.Rgn frameD.regionId) := by
      rw [hridD, hlocEq0]; exact hloc
    have hoidAtM := swap_corollary_stack_objAt_mutated (newVarMap := frame0.varMap.insert x yfRef)
      hframe0 hobj hyloc0 hcfg'
    have hoidAtM_cfg : (Reference.OId yoid).objAt? cfg = some obj := by
      unfold Reference.objAt?
      dsimp only
      rw [hyloc0]
      dsimp only
      rw [swap_corollary_stackWithIndex_find_eq hframe0_mem]
      exact hobj
    have hxRoot : FrameRoot cfg frame0.index xRef := Or.inl ⟨frame0, hframe0_mem, rfl, x, hxr⟩
    have hoidm_ne : ∀ oidx, FrameReferencable cfg frame.index (Reference.OId oidx) → oidx ≠ yoid := by
      intro oidx hreachx heq
      subst heq
      have := FrameReferencable_stk_index_le cfg vcfg frame hreachx frame0.index hyloc0
      exact absurd this (Nat.not_le.mpr hframe_lt_frame0)
    have escape := swap_corollary_escape vcfg vrcfg hyf hframeDMem hlocDown
    -- MID-CHAIN escape (via main_claim): a hop out of the mutated container yoid, using the
    -- newly-written field value xRef, is already covered by hxRoot (no resolveFA tracing needed,
    -- since xRef is literally frame0's own var x value).
    have main_claim : ∀ start', Relation.ReflTransGen (RefStep cfg') start' (Reference.OId oid) →
        Relation.ReflTransGen (RefStep cfg) start' (Reference.OId oid) ∨
          FrameReferencable cfg frameD.index (Reference.OId oid) := by
      intro start' hrtg'
      induction hrtg' using Relation.ReflTransGen.head_induction_on with
      | refl => left; exact Relation.ReflTransGen.refl
      | head hstep hrest ih =>
        rename_i a c
        rcases ih with ihchain | ihgoal
        · obtain ⟨oida, ha_eq⟩ := hstep.exists_oid_left
          subst ha_eq
          have hc_oid : ∃ oidc, c = Reference.OId oidc := by
            rcases hrest.cases_head with heq | ⟨d, hcd, _⟩
            · exact ⟨oid, heq⟩
            · exact hcd.exists_oid_left
          obtain ⟨oidc, hc_eq⟩ := hc_oid
          subst hc_eq
          by_cases haeq : oida = yoid
          · have hmemc : Reference.OId oidc ∈ Object.refs (obj.insert yf.field xRef) := by
              obtain ⟨objv, hobjAt, hcontains⟩ := hstep
              rw [haeq, hoidAtM] at hobjAt
              injection hobjAt with hobjAt_eq
              rw [← hobjAt_eq] at hcontains
              exact List.contains_iff_mem.mp hcontains
            rcases swap_corollary_object_insert_refs_mem hmemc with heqv | hmemold
            · right
              exact swap_corollary_root_escape vcfg vrcfg hxRoot hframe0_mem hframeDMem hlocDown heqv ihchain
            · left
              have hstep_cfg : RefStep cfg (Reference.OId oida) (Reference.OId oidc) := by
                rw [haeq]
                exact ⟨obj, hoidAtM_cfg, List.contains_iff_mem.mpr hmemold⟩
              exact ihchain.head hstep_cfg
          · left
            have hstep_cfg : RefStep cfg (Reference.OId oida) (Reference.OId oidc) := by
              obtain ⟨objv, hobjAt, hcontains⟩ := hstep
              have heqA := swap_corollary_stack_objAt_eq_of_ne (yoid := yoid) (obj := obj) (field := yf.field)
                (newVal := xRef) (newVarMap := frame0.varMap.insert x yfRef) (oid' := oida) hframe0 hobj haeq
              rw [← hcfg'] at heqA
              exact ⟨objv, heqA ▸ hobjAt, hcontains⟩
            exact ihchain.head hstep_cfg
        · right; exact ihgoal
    have hconcDown : FrameReferencable cfg frame.index (Reference.OId oid) := by
      rw [FrameReferencable_iff_reflTransGen] at hreach
      obtain ⟨start, hroot, hrtg⟩ := hreach
      rcases main_claim start hrtg with hchain | hgoal
      · rcases hroot with ⟨fr1, hfr1, hidx1, var, hlookup1⟩ | ⟨fr1, hfr1, hidx1, region1, hlookup1, hstart⟩
        · obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr1
          have hidx1n : fr1.index = n := by rw [← hfeq]
          by_cases hlast : n = cfg.stack.dropLast.length
          · have hfr1_varMap : fr1.varMap = frame0.varMap.insert x yfRef := by
              have hget' : cfg'.stack[n]? = some fr1.toFrame := by
                rw [show fr1.toFrame = cfg'.stack[n] from by rw [← hfeq]]
                exact List.getElem?_eq_getElem hn
              rw [hcfg'] at hget'
              dsimp only at hget'
              rw [hlast] at hget'
              simp only [List.getElem?_append_right (le_refl _), Nat.sub_self,
                List.getElem?_cons_zero] at hget'
              injection hget' with hget'_eq
              rw [← hget'_eq]
            by_cases hvareq : var = x
            · have hstarteq : start = yfRef := by
                have heq1 : fr1.varMap.lookup var = some start := hlookup1
                rw [hvareq, hfr1_varMap, AList.lookup_insert] at heq1
                injection heq1 with heq1'
                exact heq1'.symm
              have hres := escape start hstarteq hchain
              rwa [hidxD] at hres
            · have hlookup1_cfg : frame0.varMap.lookup var = some start := by
                have heq1 : fr1.varMap.lookup var = some start := hlookup1
                rw [hfr1_varMap, AList.lookup_insert_ne hvareq] at heq1
                exact heq1
              have hrootDown : FrameRoot cfg frameD'.index start :=
                Or.inl ⟨frame0, hframe0_mem, by rw [hidxD', ← hidx1, hidx1n, hlast, hidx00], var,
                  hlookup1_cfg⟩
              have hreachD' : FrameReferencable cfg frameD'.index (Reference.OId oid) :=
                (FrameReferencable_iff_reflTransGen cfg frameD'.index (Reference.OId oid)).mpr
                  ⟨start, hrootDown, hchain⟩
              have hres := vrcfg.cr3 frameD hframeDMem frameD' hframeD'Mem hltD oid hlocDown hreachD'
              rwa [hidxD] at hres
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
            have hrootDown : FrameRoot cfg frameD'.index start :=
              Or.inl ⟨fr1, hfr1Mem, by rw [hidxD', ← hidx1], var, hlookup1⟩
            have hreachD' : FrameReferencable cfg frameD'.index (Reference.OId oid) :=
              (FrameReferencable_iff_reflTransGen cfg frameD'.index (Reference.OId oid)).mpr
                ⟨start, hrootDown, hchain⟩
            have hres := vrcfg.cr3 frameD hframeDMem frameD' hframeD'Mem hltD oid hlocDown hreachD'
            rwa [hidxD] at hres
        · -- bridge root: heap is completely untouched by SWAP-STACK; transport fr1 down for regionId
          obtain ⟨fr1D, hfr1DMem, hidx1D, hrid1D, _⟩ := swap_corollary_frame_transport_down h fr1 hfr1
          have hheap_eq : cfg'.heap = cfg.heap := by rw [hcfg']
          have hlookup1_cfg : cfg.heap.lookup fr1D.regionId = some region1 := by
            rw [hrid1D, ← hheap_eq]; exact hlookup1
          have hrootDown : FrameRoot cfg frameD'.index start :=
            Or.inr ⟨fr1D, hfr1DMem, by rw [hidxD', ← hidx1, hidx1D], region1, hlookup1_cfg, hstart⟩
          have hreachD' : FrameReferencable cfg frameD'.index (Reference.OId oid) :=
            (FrameReferencable_iff_reflTransGen cfg frameD'.index (Reference.OId oid)).mpr
              ⟨start, hrootDown, hchain⟩
          have hres := vrcfg.cr3 frameD hframeDMem frameD' hframeD'Mem hltD oid hlocDown hreachD'
          rwa [hidxD] at hres
      · rwa [hidxD] at hgoal
    rw [FrameReferencable_iff_reflTransGen] at hconcDown
    obtain ⟨start2, hroot2, hrtg2⟩ := hconcDown
    have main_claim_up : ∀ target3 : Reference, Relation.ReflTransGen (RefStep cfg) start2 target3 →
        ∀ oid3, target3 = Reference.OId oid3 →
          FrameReferencable cfg frame.index (Reference.OId oid3) ∧
            Relation.ReflTransGen (RefStep cfg') start2 (Reference.OId oid3) := by
      intro target3 hrtg3
      induction hrtg3 with
      | refl =>
        intro oid3 heq3
        refine ⟨?_, by rw [← heq3]⟩
        rw [FrameReferencable_iff_reflTransGen, ← heq3]
        exact ⟨start2, hroot2, Relation.ReflTransGen.refl⟩
      | tail hprev hstep ih =>
        intro oid3 heq3
        obtain ⟨oidb, hb_eq⟩ := hstep.exists_oid_left
        obtain ⟨ihreach, ihrtg⟩ := ih oidb hb_eq
        have hbne : oidb ≠ yoid := hoidm_ne oidb ihreach
        have heqB := swap_corollary_stack_objAt_eq_of_ne (yoid := yoid) (obj := obj) (field := yf.field)
          (newVal := xRef) (newVarMap := frame0.varMap.insert x yfRef) (oid' := oidb) hframe0 hobj hbne
        rw [← hcfg'] at heqB
        obtain ⟨objv, hobjAt, hcontains⟩ := hstep
        rw [hb_eq] at hobjAt
        rw [heq3] at hcontains
        refine ⟨FrameReferencable.step hobjAt hcontains ihreach, ihrtg.tail ⟨objv, ?_, hcontains⟩⟩
        rw [← heqB]; exact hobjAt
    have hup := main_claim_up (Reference.OId oid) hrtg2 oid rfl
    rw [FrameReferencable_iff_reflTransGen]
    refine ⟨start2, ?_, hup.2⟩
    rcases hroot2 with ⟨fr2, hfr2, hidx2, var, hlookup2⟩ | ⟨fr2, hfr2, hidx2, region2, hlookup2, hstart2⟩
    · have hne : fr2.index ≠ frame0.index := by rw [hidx2]; exact Nat.ne_of_lt hframe_lt_frame0
      obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr2
      have hidx2n : fr2.index = n := by rw [← hfeq]
      have hlast : n ≠ cfg.stack.dropLast.length := by rw [hidx2n] at hne; rwa [hidx00] at hne
      have hlt : n < cfg.stack.dropLast.length := by
        have hn' : n < cfg.stack.length := hn
        rw [show cfg.stack.length = cfg.stack.dropLast.length + 1 from by rw [stack_eq0]; simp] at hn'
        exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hn') hlast
      have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
        conv_lhs => rw [stack_eq0]
        rw [List.getElem?_append_left hlt]
      have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
        rw [hcfg']; dsimp only; rw [List.getElem?_append_left hlt]
      have hfr2_get : cfg.stack[n]? = some fr2.toFrame := by
        rw [show fr2.toFrame = cfg.stack[n] from by rw [← hfeq]]
        exact List.getElem?_eq_getElem hn
      have hcfg'n : cfg'.stack[n]? = some fr2.toFrame := by rw [e2, ← e1, hfr2_get]
      obtain ⟨h1, heq⟩ := List.getElem?_eq_some_iff.mp hcfg'n
      have hfr2Mem : fr2 ∈ cfg'.stackWithIndex := by
        unfold RuntimeConfig.stackWithIndex
        exact List.mem_mapIdx.mpr ⟨n, h1, by rw [heq, ← hidx2n]⟩
      exact Or.inl ⟨fr2, hfr2Mem, hidx2, var, hlookup2⟩
    · obtain ⟨fr2U, hfr2UMem, hidx2U, hrid2U, _⟩ := swap_corollary_frame_transport_up h fr2 hfr2
      have hheap_eq : cfg'.heap = cfg.heap := by rw [hcfg']
      have hlookup2' : cfg'.heap.lookup fr2U.regionId = some region2 := by
        rw [hrid2U, hheap_eq]; exact hlookup2
      exact Or.inr ⟨fr2U, hfr2UMem, by rw [hidx2U, hidx2], region2, hlookup2', hstart2⟩
  · -- SWAP-REGION-OBJECT: var x's OLD value (OId xoid) and the region's field yf.field trade places.
    have hyloc0 : (Reference.OId yoid).loc? cfg = some (Location.Rgn rid) := by
      rw [← hyoid, ← hyrloc]; exact hyrl
    have hfield : obj.lookup yf.field = some yfRef :=
      swap_corollary_region_field_eq_yfRef (hyoid ▸ hyr) hyloc0 hregion hobj hyf
    have hlocEq0 : (Reference.OId oid).loc? cfg = (Reference.OId oid).loc? cfg' := by
      rw [hcfg']
      exact swap_corollary_region_stack_loc_eq vcfg (rid := rid) (yoid := yoid) (region := region)
        (obj := obj) (field := yf.field) (newVal := Reference.OId xoid) (frame0 := frame0)
        (newVarMap := frame0.varMap.insert x yfRef) hframe0 hregion hobj oid
    have hlocDown : (Reference.OId oid).loc? cfg = some (Location.Rgn frameD.regionId) := by
      rw [hridD, hlocEq0]; exact hloc
    have hoidAtM : (Reference.OId yoid).objAt? cfg' = some (obj.insert yf.field (Reference.OId xoid)) := by
      rw [hcfg']
      exact swap_corollary_region_stack_objAt_mutated vcfg (rid := rid) (yoid := yoid) (region := region)
        (obj := obj) (field := yf.field) (newVal := Reference.OId xoid) (frame0 := frame0)
        (newVarMap := frame0.varMap.insert x yfRef) hframe0 hregion hobj hyloc0
    have hoidAtM_cfg : (Reference.OId yoid).objAt? cfg = some obj := by
      unfold Reference.objAt?
      dsimp only
      rw [hyloc0]
      dsimp only
      rw [hregion]
      exact hobj
    have hxRoot : FrameRoot cfg frame0.index (Reference.OId xoid) := Or.inl ⟨frame0, hframe0_mem, rfl, x, hxr⟩
    have hoidm_ne : ∀ oidx, FrameReferencable cfg frame.index (Reference.OId oidx) → oidx ≠ yoid := by
      intro oidx hreachx heq
      subst heq
      have := FrameReferencable_owner_index_le cfg vcfg frame hreachx rid hyloc0 frame0 hframe0_mem hrid.symm
      exact absurd this (Nat.not_le.mpr hframe_lt_frame0)
    have escape := swap_corollary_escape vcfg vrcfg hyf hframeDMem hlocDown
    have main_claim : ∀ start', Relation.ReflTransGen (RefStep cfg') start' (Reference.OId oid) →
        Relation.ReflTransGen (RefStep cfg) start' (Reference.OId oid) ∨
          FrameReferencable cfg frameD.index (Reference.OId oid) := by
      intro start' hrtg'
      induction hrtg' using Relation.ReflTransGen.head_induction_on with
      | refl => left; exact Relation.ReflTransGen.refl
      | head hstep hrest ih =>
        rename_i a c
        rcases ih with ihchain | ihgoal
        · obtain ⟨oida, ha_eq⟩ := hstep.exists_oid_left
          subst ha_eq
          have hc_oid : ∃ oidc, c = Reference.OId oidc := by
            rcases hrest.cases_head with heq | ⟨d, hcd, _⟩
            · exact ⟨oid, heq⟩
            · exact hcd.exists_oid_left
          obtain ⟨oidc, hc_eq⟩ := hc_oid
          subst hc_eq
          by_cases haeq : oida = yoid
          · have hmemc : Reference.OId oidc ∈ Object.refs (obj.insert yf.field (Reference.OId xoid)) := by
              obtain ⟨objv, hobjAt, hcontains⟩ := hstep
              rw [haeq, hoidAtM] at hobjAt
              injection hobjAt with hobjAt_eq
              rw [← hobjAt_eq] at hcontains
              exact List.contains_iff_mem.mp hcontains
            rcases swap_corollary_object_insert_refs_mem hmemc with heqv | hmemold
            · right
              exact swap_corollary_root_escape vcfg vrcfg hxRoot hframe0_mem hframeDMem hlocDown heqv ihchain
            · left
              have hstep_cfg : RefStep cfg (Reference.OId oida) (Reference.OId oidc) := by
                rw [haeq]
                exact ⟨obj, hoidAtM_cfg, List.contains_iff_mem.mpr hmemold⟩
              exact ihchain.head hstep_cfg
          · left
            have hstep_cfg : RefStep cfg (Reference.OId oida) (Reference.OId oidc) := by
              obtain ⟨objv, hobjAt, hcontains⟩ := hstep
              have heqA : (Reference.OId oida).objAt? cfg = (Reference.OId oida).objAt? cfg' := by
                rw [hcfg']
                exact swap_corollary_region_stack_objAt_eq_of_ne vcfg (rid := rid) (yoid := yoid)
                  (region := region) (obj := obj) (field := yf.field) (newVal := Reference.OId xoid)
                  (frame0 := frame0) (newVarMap := frame0.varMap.insert x yfRef) (oid' := oida)
                  hframe0 hregion hobj haeq
              exact ⟨objv, heqA ▸ hobjAt, hcontains⟩
            exact ihchain.head hstep_cfg
        · right; exact ihgoal
    have hconcDown : FrameReferencable cfg frame.index (Reference.OId oid) := by
      rw [FrameReferencable_iff_reflTransGen] at hreach
      obtain ⟨start, hroot, hrtg⟩ := hreach
      rcases main_claim start hrtg with hchain | hgoal
      · rcases hroot with ⟨fr1, hfr1, hidx1, var, hlookup1⟩ | ⟨fr1, hfr1, hidx1, region1, hlookup1, hstart⟩
        · obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr1
          have hidx1n : fr1.index = n := by rw [← hfeq]
          by_cases hlast : n = cfg.stack.dropLast.length
          · have hfr1_varMap : fr1.varMap = frame0.varMap.insert x yfRef := by
              have hget' : cfg'.stack[n]? = some fr1.toFrame := by
                rw [show fr1.toFrame = cfg'.stack[n] from by rw [← hfeq]]
                exact List.getElem?_eq_getElem hn
              rw [hcfg'] at hget'
              dsimp only at hget'
              rw [hlast] at hget'
              simp only [List.getElem?_append_right (le_refl _), Nat.sub_self,
                List.getElem?_cons_zero] at hget'
              injection hget' with hget'_eq
              rw [← hget'_eq]
            by_cases hvareq : var = x
            · have hstarteq : start = yfRef := by
                have heq1 : fr1.varMap.lookup var = some start := hlookup1
                rw [hvareq, hfr1_varMap, AList.lookup_insert] at heq1
                injection heq1 with heq1'
                exact heq1'.symm
              have hres := escape start hstarteq hchain
              rwa [hidxD] at hres
            · have hlookup1_cfg : frame0.varMap.lookup var = some start := by
                have heq1 : fr1.varMap.lookup var = some start := hlookup1
                rw [hfr1_varMap, AList.lookup_insert_ne hvareq] at heq1
                exact heq1
              have hrootDown : FrameRoot cfg frameD'.index start :=
                Or.inl ⟨frame0, hframe0_mem, by rw [hidxD', ← hidx1, hidx1n, hlast, hidx00], var,
                  hlookup1_cfg⟩
              have hreachD' : FrameReferencable cfg frameD'.index (Reference.OId oid) :=
                (FrameReferencable_iff_reflTransGen cfg frameD'.index (Reference.OId oid)).mpr
                  ⟨start, hrootDown, hchain⟩
              have hres := vrcfg.cr3 frameD hframeDMem frameD' hframeD'Mem hltD oid hlocDown hreachD'
              rwa [hidxD] at hres
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
            have hrootDown : FrameRoot cfg frameD'.index start :=
              Or.inl ⟨fr1, hfr1Mem, by rw [hidxD', ← hidx1], var, hlookup1⟩
            have hreachD' : FrameReferencable cfg frameD'.index (Reference.OId oid) :=
              (FrameReferencable_iff_reflTransGen cfg frameD'.index (Reference.OId oid)).mpr
                ⟨start, hrootDown, hchain⟩
            have hres := vrcfg.cr3 frameD hframeDMem frameD' hframeD'Mem hltD oid hlocDown hreachD'
            rwa [hidxD] at hres
        · -- bridge root: bridgeObjectId is unaffected by an objMap-only region mutation
          obtain ⟨fr1D, hfr1DMem, hidx1D, hrid1D, _⟩ := swap_corollary_frame_transport_down h fr1 hfr1
          have hheap_eq := swap_corollary_region_heap_bridge_eq (rid := rid)
            (newRegion := { region with objMap := region.objMap.insert yoid (obj.insert yf.field (Reference.OId xoid)) })
            hregion rfl fr1D.regionId
          have hheap'_eq : cfg'.heap = cfg.heap.insert rid ({ region with objMap := region.objMap.insert yoid (obj.insert yf.field (Reference.OId xoid)) } : Region) := by
            rw [hcfg']
          have hlookup1' : (cfg.heap.insert rid ({ region with objMap := region.objMap.insert yoid (obj.insert yf.field (Reference.OId xoid)) } : Region)).lookup fr1D.regionId = some region1 := by
            rw [hrid1D, ← hheap'_eq]; exact hlookup1
          rw [hlookup1', Option.map_some] at hheap_eq
          obtain ⟨region1D, hregion1D, hbridge1D⟩ := Option.map_eq_some_iff.mp hheap_eq
          have hrootDown : FrameRoot cfg frameD'.index start :=
            Or.inr ⟨fr1D, hfr1DMem, by rw [hidxD', ← hidx1, hidx1D], region1D, hregion1D, by rw [hstart, hbridge1D]⟩
          have hreachD' : FrameReferencable cfg frameD'.index (Reference.OId oid) :=
            (FrameReferencable_iff_reflTransGen cfg frameD'.index (Reference.OId oid)).mpr
              ⟨start, hrootDown, hchain⟩
          have hres := vrcfg.cr3 frameD hframeDMem frameD' hframeD'Mem hltD oid hlocDown hreachD'
          rwa [hidxD] at hres
      · rwa [hidxD] at hgoal
    rw [FrameReferencable_iff_reflTransGen] at hconcDown
    obtain ⟨start2, hroot2, hrtg2⟩ := hconcDown
    have main_claim_up : ∀ target3 : Reference, Relation.ReflTransGen (RefStep cfg) start2 target3 →
        ∀ oid3, target3 = Reference.OId oid3 →
          FrameReferencable cfg frame.index (Reference.OId oid3) ∧
            Relation.ReflTransGen (RefStep cfg') start2 (Reference.OId oid3) := by
      intro target3 hrtg3
      induction hrtg3 with
      | refl =>
        intro oid3 heq3
        refine ⟨?_, by rw [← heq3]⟩
        rw [FrameReferencable_iff_reflTransGen, ← heq3]
        exact ⟨start2, hroot2, Relation.ReflTransGen.refl⟩
      | tail hprev hstep ih =>
        intro oid3 heq3
        obtain ⟨oidb, hb_eq⟩ := hstep.exists_oid_left
        obtain ⟨ihreach, ihrtg⟩ := ih oidb hb_eq
        have hbne : oidb ≠ yoid := hoidm_ne oidb ihreach
        have heqB : (Reference.OId oidb).objAt? cfg = (Reference.OId oidb).objAt? cfg' := by
          rw [hcfg']
          exact swap_corollary_region_stack_objAt_eq_of_ne vcfg (rid := rid) (yoid := yoid)
            (region := region) (obj := obj) (field := yf.field) (newVal := Reference.OId xoid)
            (frame0 := frame0) (newVarMap := frame0.varMap.insert x yfRef) (oid' := oidb)
            hframe0 hregion hobj hbne
        obtain ⟨objv, hobjAt, hcontains⟩ := hstep
        rw [hb_eq] at hobjAt
        rw [heq3] at hcontains
        refine ⟨FrameReferencable.step hobjAt hcontains ihreach, ihrtg.tail ⟨objv, ?_, hcontains⟩⟩
        rw [← heqB]; exact hobjAt
    have hup := main_claim_up (Reference.OId oid) hrtg2 oid rfl
    rw [FrameReferencable_iff_reflTransGen]
    refine ⟨start2, ?_, hup.2⟩
    rcases hroot2 with ⟨fr2, hfr2, hidx2, var, hlookup2⟩ | ⟨fr2, hfr2, hidx2, region2, hlookup2, hstart2⟩
    · have hne : fr2.index ≠ frame0.index := by rw [hidx2]; exact Nat.ne_of_lt hframe_lt_frame0
      obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr2
      have hidx2n : fr2.index = n := by rw [← hfeq]
      have hlast : n ≠ cfg.stack.dropLast.length := by rw [hidx2n] at hne; rwa [hidx00] at hne
      have hlt : n < cfg.stack.dropLast.length := by
        have hn' : n < cfg.stack.length := hn
        rw [show cfg.stack.length = cfg.stack.dropLast.length + 1 from by rw [stack_eq0]; simp] at hn'
        exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hn') hlast
      have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
        conv_lhs => rw [stack_eq0]
        rw [List.getElem?_append_left hlt]
      have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
        rw [hcfg']; dsimp only; rw [List.getElem?_append_left hlt]
      have hfr2_get : cfg.stack[n]? = some fr2.toFrame := by
        rw [show fr2.toFrame = cfg.stack[n] from by rw [← hfeq]]
        exact List.getElem?_eq_getElem hn
      have hcfg'n : cfg'.stack[n]? = some fr2.toFrame := by rw [e2, ← e1, hfr2_get]
      obtain ⟨h1, heq⟩ := List.getElem?_eq_some_iff.mp hcfg'n
      have hfr2Mem : fr2 ∈ cfg'.stackWithIndex := by
        unfold RuntimeConfig.stackWithIndex
        exact List.mem_mapIdx.mpr ⟨n, h1, by rw [heq, ← hidx2n]⟩
      exact Or.inl ⟨fr2, hfr2Mem, hidx2, var, hlookup2⟩
    · -- bridge root, up: bridgeObjectId unaffected by the objMap-only mutation
      obtain ⟨fr2U, hfr2UMem, hidx2U, hrid2U, _⟩ := swap_corollary_frame_transport_up h fr2 hfr2
      have hheap_eq := swap_corollary_region_heap_bridge_eq (rid := rid)
        (newRegion := { region with objMap := region.objMap.insert yoid (obj.insert yf.field (Reference.OId xoid)) })
        hregion rfl fr2U.regionId
      have hlookup2U : cfg.heap.lookup fr2U.regionId = some region2 := by rw [hrid2U]; exact hlookup2
      rw [hlookup2U, Option.map_some] at hheap_eq
      obtain ⟨region2', hregion2', hbridge2'⟩ := Option.map_eq_some_iff.mp hheap_eq.symm
      have hregion2'' : cfg'.heap.lookup fr2U.regionId = some region2' := by rw [hcfg']; exact hregion2'
      exact Or.inr ⟨fr2U, hfr2UMem, by rw [hidx2U, hidx2], region2', hregion2'', by rw [hstart2, hbridge2']⟩
  · -- SWAP-REGION-REGION: identical shape to SWAP-REGION-OBJECT, except var x's OLD value is
    -- Reference.RId xrid (a region reference) -- so the mid-chain escape can never actually fire
    -- (an RId can never be a mid-chain hop target of a chain whose overall target is Reference.OId
    -- oid, since RefStep can only ever step *into* an RId as the chain's very last element).
    have hyloc0 : (Reference.OId yoid).loc? cfg = some (Location.Rgn rid) := by
      rw [← hyoid, ← hyrloc]; exact hyrl
    have hfield : obj.lookup yf.field = some yfRef :=
      swap_corollary_region_field_eq_yfRef (hyoid ▸ hyr) hyloc0 hregion hobj hyf
    have hlocEq0 : (Reference.OId oid).loc? cfg = (Reference.OId oid).loc? cfg' := by
      rw [hcfg']
      exact swap_corollary_region_stack_loc_eq vcfg (rid := rid) (yoid := yoid) (region := region)
        (obj := obj) (field := yf.field) (newVal := Reference.RId xrid) (frame0 := frame0)
        (newVarMap := frame0.varMap.insert x yfRef) hframe0 hregion hobj oid
    have hlocDown : (Reference.OId oid).loc? cfg = some (Location.Rgn frameD.regionId) := by
      rw [hridD, hlocEq0]; exact hloc
    have hoidAtM : (Reference.OId yoid).objAt? cfg' = some (obj.insert yf.field (Reference.RId xrid)) := by
      rw [hcfg']
      exact swap_corollary_region_stack_objAt_mutated vcfg (rid := rid) (yoid := yoid) (region := region)
        (obj := obj) (field := yf.field) (newVal := Reference.RId xrid) (frame0 := frame0)
        (newVarMap := frame0.varMap.insert x yfRef) hframe0 hregion hobj hyloc0
    have hoidAtM_cfg : (Reference.OId yoid).objAt? cfg = some obj := by
      unfold Reference.objAt?
      dsimp only
      rw [hyloc0]
      dsimp only
      rw [hregion]
      exact hobj
    have hxRoot : FrameRoot cfg frame0.index (Reference.RId xrid) := Or.inl ⟨frame0, hframe0_mem, rfl, x, hxr⟩
    have hoidm_ne : ∀ oidx, FrameReferencable cfg frame.index (Reference.OId oidx) → oidx ≠ yoid := by
      intro oidx hreachx heq
      subst heq
      have := FrameReferencable_owner_index_le cfg vcfg frame hreachx rid hyloc0 frame0 hframe0_mem hrid.symm
      exact absurd this (Nat.not_le.mpr hframe_lt_frame0)
    have escape := swap_corollary_escape vcfg vrcfg hyf hframeDMem hlocDown
    have main_claim : ∀ start', Relation.ReflTransGen (RefStep cfg') start' (Reference.OId oid) →
        Relation.ReflTransGen (RefStep cfg) start' (Reference.OId oid) ∨
          FrameReferencable cfg frameD.index (Reference.OId oid) := by
      intro start' hrtg'
      induction hrtg' using Relation.ReflTransGen.head_induction_on with
      | refl => left; exact Relation.ReflTransGen.refl
      | head hstep hrest ih =>
        rename_i a c
        rcases ih with ihchain | ihgoal
        · obtain ⟨oida, ha_eq⟩ := hstep.exists_oid_left
          subst ha_eq
          have hc_oid : ∃ oidc, c = Reference.OId oidc := by
            rcases hrest.cases_head with heq | ⟨d, hcd, _⟩
            · exact ⟨oid, heq⟩
            · exact hcd.exists_oid_left
          obtain ⟨oidc, hc_eq⟩ := hc_oid
          subst hc_eq
          by_cases haeq : oida = yoid
          · have hmemc : Reference.OId oidc ∈ Object.refs (obj.insert yf.field (Reference.RId xrid)) := by
              obtain ⟨objv, hobjAt, hcontains⟩ := hstep
              rw [haeq, hoidAtM] at hobjAt
              injection hobjAt with hobjAt_eq
              rw [← hobjAt_eq] at hcontains
              exact List.contains_iff_mem.mp hcontains
            rcases swap_corollary_object_insert_refs_mem hmemc with heqv | hmemold
            · exact absurd heqv (by simp)
            · left
              have hstep_cfg : RefStep cfg (Reference.OId oida) (Reference.OId oidc) := by
                rw [haeq]
                exact ⟨obj, hoidAtM_cfg, List.contains_iff_mem.mpr hmemold⟩
              exact ihchain.head hstep_cfg
          · left
            have hstep_cfg : RefStep cfg (Reference.OId oida) (Reference.OId oidc) := by
              obtain ⟨objv, hobjAt, hcontains⟩ := hstep
              have heqA : (Reference.OId oida).objAt? cfg = (Reference.OId oida).objAt? cfg' := by
                rw [hcfg']
                exact swap_corollary_region_stack_objAt_eq_of_ne vcfg (rid := rid) (yoid := yoid)
                  (region := region) (obj := obj) (field := yf.field) (newVal := Reference.RId xrid)
                  (frame0 := frame0) (newVarMap := frame0.varMap.insert x yfRef) (oid' := oida)
                  hframe0 hregion hobj haeq
              exact ⟨objv, heqA ▸ hobjAt, hcontains⟩
            exact ihchain.head hstep_cfg
        · right; exact ihgoal
    have hconcDown : FrameReferencable cfg frame.index (Reference.OId oid) := by
      rw [FrameReferencable_iff_reflTransGen] at hreach
      obtain ⟨start, hroot, hrtg⟩ := hreach
      rcases main_claim start hrtg with hchain | hgoal
      · rcases hroot with ⟨fr1, hfr1, hidx1, var, hlookup1⟩ | ⟨fr1, hfr1, hidx1, region1, hlookup1, hstart⟩
        · obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr1
          have hidx1n : fr1.index = n := by rw [← hfeq]
          by_cases hlast : n = cfg.stack.dropLast.length
          · have hfr1_varMap : fr1.varMap = frame0.varMap.insert x yfRef := by
              have hget' : cfg'.stack[n]? = some fr1.toFrame := by
                rw [show fr1.toFrame = cfg'.stack[n] from by rw [← hfeq]]
                exact List.getElem?_eq_getElem hn
              rw [hcfg'] at hget'
              dsimp only at hget'
              rw [hlast] at hget'
              simp only [List.getElem?_append_right (le_refl _), Nat.sub_self,
                List.getElem?_cons_zero] at hget'
              injection hget' with hget'_eq
              rw [← hget'_eq]
            by_cases hvareq : var = x
            · have hstarteq : start = yfRef := by
                have heq1 : fr1.varMap.lookup var = some start := hlookup1
                rw [hvareq, hfr1_varMap, AList.lookup_insert] at heq1
                injection heq1 with heq1'
                exact heq1'.symm
              have hres := escape start hstarteq hchain
              rwa [hidxD] at hres
            · have hlookup1_cfg : frame0.varMap.lookup var = some start := by
                have heq1 : fr1.varMap.lookup var = some start := hlookup1
                rw [hfr1_varMap, AList.lookup_insert_ne hvareq] at heq1
                exact heq1
              have hrootDown : FrameRoot cfg frameD'.index start :=
                Or.inl ⟨frame0, hframe0_mem, by rw [hidxD', ← hidx1, hidx1n, hlast, hidx00], var,
                  hlookup1_cfg⟩
              have hreachD' : FrameReferencable cfg frameD'.index (Reference.OId oid) :=
                (FrameReferencable_iff_reflTransGen cfg frameD'.index (Reference.OId oid)).mpr
                  ⟨start, hrootDown, hchain⟩
              have hres := vrcfg.cr3 frameD hframeDMem frameD' hframeD'Mem hltD oid hlocDown hreachD'
              rwa [hidxD] at hres
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
            have hrootDown : FrameRoot cfg frameD'.index start :=
              Or.inl ⟨fr1, hfr1Mem, by rw [hidxD', ← hidx1], var, hlookup1⟩
            have hreachD' : FrameReferencable cfg frameD'.index (Reference.OId oid) :=
              (FrameReferencable_iff_reflTransGen cfg frameD'.index (Reference.OId oid)).mpr
                ⟨start, hrootDown, hchain⟩
            have hres := vrcfg.cr3 frameD hframeDMem frameD' hframeD'Mem hltD oid hlocDown hreachD'
            rwa [hidxD] at hres
        · -- bridge root: bridgeObjectId is unaffected by an objMap-only region mutation
          obtain ⟨fr1D, hfr1DMem, hidx1D, hrid1D, _⟩ := swap_corollary_frame_transport_down h fr1 hfr1
          have hheap_eq := swap_corollary_region_heap_bridge_eq (rid := rid)
            (newRegion := { region with objMap := region.objMap.insert yoid (obj.insert yf.field (Reference.RId xrid)) })
            hregion rfl fr1D.regionId
          have hheap'_eq : cfg'.heap = cfg.heap.insert rid ({ region with objMap := region.objMap.insert yoid (obj.insert yf.field (Reference.RId xrid)) } : Region) := by
            rw [hcfg']
          have hlookup1' : (cfg.heap.insert rid ({ region with objMap := region.objMap.insert yoid (obj.insert yf.field (Reference.RId xrid)) } : Region)).lookup fr1D.regionId = some region1 := by
            rw [hrid1D, ← hheap'_eq]; exact hlookup1
          rw [hlookup1', Option.map_some] at hheap_eq
          obtain ⟨region1D, hregion1D, hbridge1D⟩ := Option.map_eq_some_iff.mp hheap_eq
          have hrootDown : FrameRoot cfg frameD'.index start :=
            Or.inr ⟨fr1D, hfr1DMem, by rw [hidxD', ← hidx1, hidx1D], region1D, hregion1D, by rw [hstart, hbridge1D]⟩
          have hreachD' : FrameReferencable cfg frameD'.index (Reference.OId oid) :=
            (FrameReferencable_iff_reflTransGen cfg frameD'.index (Reference.OId oid)).mpr
              ⟨start, hrootDown, hchain⟩
          have hres := vrcfg.cr3 frameD hframeDMem frameD' hframeD'Mem hltD oid hlocDown hreachD'
          rwa [hidxD] at hres
      · rwa [hidxD] at hgoal
    rw [FrameReferencable_iff_reflTransGen] at hconcDown
    obtain ⟨start2, hroot2, hrtg2⟩ := hconcDown
    have main_claim_up : ∀ target3 : Reference, Relation.ReflTransGen (RefStep cfg) start2 target3 →
        ∀ oid3, target3 = Reference.OId oid3 →
          FrameReferencable cfg frame.index (Reference.OId oid3) ∧
            Relation.ReflTransGen (RefStep cfg') start2 (Reference.OId oid3) := by
      intro target3 hrtg3
      induction hrtg3 with
      | refl =>
        intro oid3 heq3
        refine ⟨?_, by rw [← heq3]⟩
        rw [FrameReferencable_iff_reflTransGen, ← heq3]
        exact ⟨start2, hroot2, Relation.ReflTransGen.refl⟩
      | tail hprev hstep ih =>
        intro oid3 heq3
        obtain ⟨oidb, hb_eq⟩ := hstep.exists_oid_left
        obtain ⟨ihreach, ihrtg⟩ := ih oidb hb_eq
        have hbne : oidb ≠ yoid := hoidm_ne oidb ihreach
        have heqB : (Reference.OId oidb).objAt? cfg = (Reference.OId oidb).objAt? cfg' := by
          rw [hcfg']
          exact swap_corollary_region_stack_objAt_eq_of_ne vcfg (rid := rid) (yoid := yoid)
            (region := region) (obj := obj) (field := yf.field) (newVal := Reference.RId xrid)
            (frame0 := frame0) (newVarMap := frame0.varMap.insert x yfRef) (oid' := oidb)
            hframe0 hregion hobj hbne
        obtain ⟨objv, hobjAt, hcontains⟩ := hstep
        rw [hb_eq] at hobjAt
        rw [heq3] at hcontains
        refine ⟨FrameReferencable.step hobjAt hcontains ihreach, ihrtg.tail ⟨objv, ?_, hcontains⟩⟩
        rw [← heqB]; exact hobjAt
    have hup := main_claim_up (Reference.OId oid) hrtg2 oid rfl
    rw [FrameReferencable_iff_reflTransGen]
    refine ⟨start2, ?_, hup.2⟩
    rcases hroot2 with ⟨fr2, hfr2, hidx2, var, hlookup2⟩ | ⟨fr2, hfr2, hidx2, region2, hlookup2, hstart2⟩
    · have hne : fr2.index ≠ frame0.index := by rw [hidx2]; exact Nat.ne_of_lt hframe_lt_frame0
      obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr2
      have hidx2n : fr2.index = n := by rw [← hfeq]
      have hlast : n ≠ cfg.stack.dropLast.length := by rw [hidx2n] at hne; rwa [hidx00] at hne
      have hlt : n < cfg.stack.dropLast.length := by
        have hn' : n < cfg.stack.length := hn
        rw [show cfg.stack.length = cfg.stack.dropLast.length + 1 from by rw [stack_eq0]; simp] at hn'
        exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hn') hlast
      have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
        conv_lhs => rw [stack_eq0]
        rw [List.getElem?_append_left hlt]
      have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
        rw [hcfg']; dsimp only; rw [List.getElem?_append_left hlt]
      have hfr2_get : cfg.stack[n]? = some fr2.toFrame := by
        rw [show fr2.toFrame = cfg.stack[n] from by rw [← hfeq]]
        exact List.getElem?_eq_getElem hn
      have hcfg'n : cfg'.stack[n]? = some fr2.toFrame := by rw [e2, ← e1, hfr2_get]
      obtain ⟨h1, heq⟩ := List.getElem?_eq_some_iff.mp hcfg'n
      have hfr2Mem : fr2 ∈ cfg'.stackWithIndex := by
        unfold RuntimeConfig.stackWithIndex
        exact List.mem_mapIdx.mpr ⟨n, h1, by rw [heq, ← hidx2n]⟩
      exact Or.inl ⟨fr2, hfr2Mem, hidx2, var, hlookup2⟩
    · -- bridge root, up: bridgeObjectId unaffected by the objMap-only mutation
      obtain ⟨fr2U, hfr2UMem, hidx2U, hrid2U, _⟩ := swap_corollary_frame_transport_up h fr2 hfr2
      have hheap_eq := swap_corollary_region_heap_bridge_eq (rid := rid)
        (newRegion := { region with objMap := region.objMap.insert yoid (obj.insert yf.field (Reference.RId xrid)) })
        hregion rfl fr2U.regionId
      have hlookup2U : cfg.heap.lookup fr2U.regionId = some region2 := by rw [hrid2U]; exact hlookup2
      rw [hlookup2U, Option.map_some] at hheap_eq
      obtain ⟨region2', hregion2', hbridge2'⟩ := Option.map_eq_some_iff.mp hheap_eq.symm
      have hregion2'' : cfg'.heap.lookup fr2U.regionId = some region2' := by rw [hcfg']; exact hregion2'
      exact Or.inr ⟨fr2U, hfr2UMem, by rw [hidx2U, hidx2], region2', hregion2'', by rw [hstart2, hbridge2']⟩
  · -- SWAP-REGION-BRIDGE: the stack is completely untouched -- the exchange is entirely
    -- heap-side, between region yrid's `bridgeObjectId` (OLD value, region.bridgeObjectId) and the
    -- field yf.field of container yoid (OLD value yfRef = OId yfoid). NEW bridgeObjectId = yfoid;
    -- NEW field value = OId region.bridgeObjectId.
    have hswi_eq : cfg'.stackWithIndex = cfg.stackWithIndex := by
      unfold RuntimeConfig.stackWithIndex
      rw [show cfg'.stack = cfg.stack from by rw [hcfg']]
    have hyloc0 : (Reference.OId yoid).loc? cfg = some (Location.Rgn yrid) := by
      rw [← hyoid, ← hyrloc]; exact hyrl
    have hfield : obj.lookup yf.field = some yfRef :=
      swap_corollary_region_field_eq_yfRef (hyoid ▸ hyr) hyloc0 hregion hobj hyf
    have hlocEq0 := swap_corollary_region_loc_eq (rid := yrid) (yoid := yoid) (region := region)
      (newRegion := ({ region with bridgeObjectId := yfoid, objMap := region.objMap.insert yoid (obj.insert yf.field (Reference.OId region.bridgeObjectId)) } : Region))
      (obj := obj) (v := obj.insert yf.field (Reference.OId region.bridgeObjectId)) vcfg hregion hobj rfl oid
    rw [← hcfg'] at hlocEq0
    have hlocDown : (Reference.OId oid).loc? cfg = some (Location.Rgn frameD.regionId) := by
      rw [hridD, hlocEq0]; exact hloc
    have hoidAtM : (Reference.OId yoid).objAt? cfg' =
        some (obj.insert yf.field (Reference.OId region.bridgeObjectId)) := by
      rw [hcfg']
      exact swap_corollary_region_objAt_mutated vcfg (rid := yrid) (yoid := yoid) (region := region)
        (obj := obj) (field := yf.field) (newVal := Reference.OId region.bridgeObjectId) (newBridge := yfoid)
        hregion hobj hyloc0 rfl
    have hoidAtM_cfg : (Reference.OId yoid).objAt? cfg = some obj := by
      unfold Reference.objAt?
      dsimp only
      rw [hyloc0]
      dsimp only
      rw [hregion]
      exact hobj
    have hregion0 : cfg.heap.lookup frame0.regionId = some region := by rw [← hyridEq]; exact hregion
    have hxRoot : FrameRoot cfg frame0.index (Reference.OId region.bridgeObjectId) :=
      Or.inr ⟨frame0, hframe0_mem, rfl, region, hregion0, rfl⟩
    have hoidm_ne : ∀ oidx, FrameReferencable cfg frame.index (Reference.OId oidx) → oidx ≠ yoid := by
      intro oidx hreachx heq
      subst heq
      have := FrameReferencable_owner_index_le cfg vcfg frame hreachx yrid hyloc0 frame0 hframe0_mem hyridEq.symm
      exact absurd this (Nat.not_le.mpr hframe_lt_frame0)
    have escape := swap_corollary_escape vcfg vrcfg hyf hframeDMem hlocDown
    have main_claim : ∀ start', Relation.ReflTransGen (RefStep cfg') start' (Reference.OId oid) →
        Relation.ReflTransGen (RefStep cfg) start' (Reference.OId oid) ∨
          FrameReferencable cfg frameD.index (Reference.OId oid) := by
      intro start' hrtg'
      induction hrtg' using Relation.ReflTransGen.head_induction_on with
      | refl => left; exact Relation.ReflTransGen.refl
      | head hstep hrest ih =>
        rename_i a c
        rcases ih with ihchain | ihgoal
        · obtain ⟨oida, ha_eq⟩ := hstep.exists_oid_left
          subst ha_eq
          have hc_oid : ∃ oidc, c = Reference.OId oidc := by
            rcases hrest.cases_head with heq | ⟨d, hcd, _⟩
            · exact ⟨oid, heq⟩
            · exact hcd.exists_oid_left
          obtain ⟨oidc, hc_eq⟩ := hc_oid
          subst hc_eq
          by_cases haeq : oida = yoid
          · have hmemc : Reference.OId oidc ∈
                Object.refs (obj.insert yf.field (Reference.OId region.bridgeObjectId)) := by
              obtain ⟨objv, hobjAt, hcontains⟩ := hstep
              rw [haeq, hoidAtM] at hobjAt
              injection hobjAt with hobjAt_eq
              rw [← hobjAt_eq] at hcontains
              exact List.contains_iff_mem.mp hcontains
            rcases swap_corollary_object_insert_refs_mem hmemc with heqv | hmemold
            · right
              exact swap_corollary_root_escape vcfg vrcfg hxRoot hframe0_mem hframeDMem hlocDown heqv ihchain
            · left
              have hstep_cfg : RefStep cfg (Reference.OId oida) (Reference.OId oidc) := by
                rw [haeq]
                exact ⟨obj, hoidAtM_cfg, List.contains_iff_mem.mpr hmemold⟩
              exact ihchain.head hstep_cfg
          · left
            have hstep_cfg : RefStep cfg (Reference.OId oida) (Reference.OId oidc) := by
              obtain ⟨objv, hobjAt, hcontains⟩ := hstep
              have heqA : (Reference.OId oida).objAt? cfg = (Reference.OId oida).objAt? cfg' := by
                rw [hcfg']
                exact swap_corollary_region_objAt_eq_of_ne vcfg (rid := yrid) (yoid := yoid)
                  (region := region) (obj := obj) (field := yf.field)
                  (newVal := Reference.OId region.bridgeObjectId) (newBridge := yfoid) (oid' := oida)
                  hregion hobj haeq
              exact ⟨objv, heqA ▸ hobjAt, hcontains⟩
            exact ihchain.head hstep_cfg
        · right; exact ihgoal
    have hconcDown : FrameReferencable cfg frame.index (Reference.OId oid) := by
      rw [FrameReferencable_iff_reflTransGen] at hreach
      obtain ⟨start, hroot, hrtg⟩ := hreach
      rcases main_claim start hrtg with hchain | hgoal
      · rcases hroot with ⟨fr1, hfr1, hidx1, var, hlookup1⟩ | ⟨fr1, hfr1, hidx1, region1, hlookup1, hstart⟩
        · rw [hswi_eq] at hfr1
          have hrootDown : FrameRoot cfg frameD'.index start := Or.inl ⟨fr1, hfr1, by rw [hidxD', ← hidx1], var, hlookup1⟩
          have hreachD' : FrameReferencable cfg frameD'.index (Reference.OId oid) :=
            (FrameReferencable_iff_reflTransGen cfg frameD'.index (Reference.OId oid)).mpr
              ⟨start, hrootDown, hchain⟩
          have hres := vrcfg.cr3 frameD hframeDMem frameD' hframeD'Mem hltD oid hlocDown hreachD'
          rwa [hidxD] at hres
        · rw [hswi_eq] at hfr1
          by_cases hrideq : fr1.regionId = yrid
          · have hidx_eq := merge_corollary_regionId_unique_index vcfg.s1 hfr1 hframe0_mem (hrideq.trans hyridEq)
            have hfr1eq : fr1 = frame0 := swap_corollary_stackWithIndex_index_inj hfr1 hframe0_mem hidx_eq
            have hbridgeEq : region1.bridgeObjectId = yfoid := by
              have hlookup1' : cfg'.heap.lookup yrid = some ({ region with bridgeObjectId := yfoid, objMap := region.objMap.insert yoid (obj.insert yf.field (Reference.OId region.bridgeObjectId)) } : Region) := by
                rw [hcfg']
                exact AList.lookup_insert (a := yrid) (b := ({ region with bridgeObjectId := yfoid, objMap := region.objMap.insert yoid (obj.insert yf.field (Reference.OId region.bridgeObjectId)) } : Region)) cfg.heap
              rw [hrideq, hlookup1'] at hlookup1
              injection hlookup1 with hlookup1_eq
              rw [← hlookup1_eq]
            have hstarteq : start = yfRef := by rw [hstart, hbridgeEq]; exact hyfoid.symm
            have hres := escape start hstarteq hchain
            rwa [hidxD] at hres
          · have hlookup1_cfg : cfg.heap.lookup fr1.regionId = some region1 := by
              have heq : cfg'.heap.lookup fr1.regionId = cfg.heap.lookup fr1.regionId := by
                rw [hcfg']; exact AList.lookup_insert_ne hrideq
              rw [← heq]; exact hlookup1
            have hrootDown : FrameRoot cfg frameD'.index start :=
              Or.inr ⟨fr1, hfr1, by rw [hidxD', ← hidx1], region1, hlookup1_cfg, hstart⟩
            have hreachD' : FrameReferencable cfg frameD'.index (Reference.OId oid) :=
              (FrameReferencable_iff_reflTransGen cfg frameD'.index (Reference.OId oid)).mpr
                ⟨start, hrootDown, hchain⟩
            have hres := vrcfg.cr3 frameD hframeDMem frameD' hframeD'Mem hltD oid hlocDown hreachD'
            rwa [hidxD] at hres
      · rwa [hidxD] at hgoal
    rw [FrameReferencable_iff_reflTransGen] at hconcDown
    obtain ⟨start2, hroot2, hrtg2⟩ := hconcDown
    have main_claim_up : ∀ target3 : Reference, Relation.ReflTransGen (RefStep cfg) start2 target3 →
        ∀ oid3, target3 = Reference.OId oid3 →
          FrameReferencable cfg frame.index (Reference.OId oid3) ∧
            Relation.ReflTransGen (RefStep cfg') start2 (Reference.OId oid3) := by
      intro target3 hrtg3
      induction hrtg3 with
      | refl =>
        intro oid3 heq3
        refine ⟨?_, by rw [← heq3]⟩
        rw [FrameReferencable_iff_reflTransGen, ← heq3]
        exact ⟨start2, hroot2, Relation.ReflTransGen.refl⟩
      | tail hprev hstep ih =>
        intro oid3 heq3
        obtain ⟨oidb, hb_eq⟩ := hstep.exists_oid_left
        obtain ⟨ihreach, ihrtg⟩ := ih oidb hb_eq
        have hbne : oidb ≠ yoid := hoidm_ne oidb ihreach
        have heqB : (Reference.OId oidb).objAt? cfg = (Reference.OId oidb).objAt? cfg' := by
          rw [hcfg']
          exact swap_corollary_region_objAt_eq_of_ne vcfg (rid := yrid) (yoid := yoid)
            (region := region) (obj := obj) (field := yf.field)
            (newVal := Reference.OId region.bridgeObjectId) (newBridge := yfoid) (oid' := oidb)
            hregion hobj hbne
        obtain ⟨objv, hobjAt, hcontains⟩ := hstep
        rw [hb_eq] at hobjAt
        rw [heq3] at hcontains
        refine ⟨FrameReferencable.step hobjAt hcontains ihreach, ihrtg.tail ⟨objv, ?_, hcontains⟩⟩
        rw [← heqB]; exact hobjAt
    have hup := main_claim_up (Reference.OId oid) hrtg2 oid rfl
    rw [FrameReferencable_iff_reflTransGen]
    refine ⟨start2, ?_, hup.2⟩
    have hne : frame.index ≠ frame0.index := Nat.ne_of_lt hframe_lt_frame0
    rcases hroot2 with ⟨fr2, hfr2, hidx2, var, hlookup2⟩ | ⟨fr2, hfr2, hidx2, region2, hlookup2, hstart2⟩
    · have hfr2Mem' : fr2 ∈ cfg'.stackWithIndex := by rw [hswi_eq]; exact hfr2
      exact Or.inl ⟨fr2, hfr2Mem', hidx2, var, hlookup2⟩
    · have hfr2Mem' : fr2 ∈ cfg'.stackWithIndex := by rw [hswi_eq]; exact hfr2
      by_cases hrideq : fr2.regionId = yrid
      · exfalso
        have hidx_eq := merge_corollary_regionId_unique_index vcfg.s1 hfr2 hframe0_mem (hrideq.trans hyridEq)
        rw [hidx2] at hidx_eq
        exact hne hidx_eq
      · have hlookup2' : cfg'.heap.lookup fr2.regionId = some region2 := by
          rw [hcfg']; rw [AList.lookup_insert_ne hrideq]; exact hlookup2
        exact Or.inr ⟨fr2, hfr2Mem', hidx2, region2, hlookup2', hstart2⟩

theorem swap_reachable_valid : ValidReachableConfig cfg →
  swap x yf cfg = some cfg' →
  ValidReachableConfig cfg' := by
  intro vrcfg h
  exact { swap_valid vrcfg.toValidConfig h with cr3 := swap_cr3 vrcfg h }
