import Gc.Reachability.Referencable.Basic
import Gc.Reachability.Referencable.Lemmas

theorem fieldAsgn_cr3 : ValidReachableConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  CR3 cfg' := by
  intro vrcfg h
  have vcfg := vrcfg.toValidConfig
  have vcfg' := fieldAsgn_valid vcfg h
  obtain ⟨frame0, hframe0, hcase⟩ := fieldAsgn_cases h
  obtain ⟨stack_eq0, hidx00⟩ := fieldAsgn_corollary_stack_eq hframe0
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
  obtain ⟨frameD, hframeDMem, hidxD, hridD, _, _⟩ := fieldAsgn_corollary_frame_transport_down h frame hframeMem
  obtain ⟨frameD', hframeD'Mem, hidxD', hridD', _, _⟩ := fieldAsgn_corollary_frame_transport_down h frame' hframe'Mem
  have hltD : frameD.index < frameD'.index := by rw [hidxD, hidxD']; exact hlt
  have hD'_le_frame0 : frameD'.index ≤ frame0.index := hframe0_max frameD' hframeD'Mem
  have hD_lt_frame0 : frameD.index < frame0.index := lt_of_lt_of_le hltD hD'_le_frame0
  have hframe_lt_frame0 : frame.index < frame0.index := by rw [← hidxD]; exact hD_lt_frame0
  rcases hcase with
    ⟨oidm, oidy, obj, hxr, hyr, hlocm, hobjm, hcfg'⟩ |
    ⟨oidm, oidy, rid, region, obj, hxr, hyr, hlocm, hregion, hobjm, hyloc, hstatus, hfrid, hcfg'⟩
  · -- STACK branch
    have hlocEq0 :=
      fieldAsgn_corollary_stack_loc_eq (field := x.field) (yRef := Reference.OId oidy) hframe0 hobjm oid
    rw [← hcfg'] at hlocEq0
    have hlocDown : (Reference.OId oid).loc? cfg = some (Location.Rgn frameD.regionId) := by
      rw [hridD, hlocEq0]; exact hloc
    have hoidAtM := fieldAsgn_corollary_stack_objAt_mutated hframe0 hobjm hlocm hcfg'
    have hoidAtM_cfg : (Reference.OId oidm).objAt? cfg = some obj := by
      unfold Reference.objAt?
      dsimp only
      rw [hlocm]
      dsimp only
      have hframe0_mem : frame0 ∈ cfg.stackWithIndex := List.mem_of_getLast? hframe0
      rw [swap_corollary_stackWithIndex_find_eq hframe0_mem]
      exact hobjm
    have hoidm_ne : ∀ oidx, FrameReferencable cfg frame.index (Reference.OId oidx) → oidx ≠ oidm := by
      intro oidx hreachx heq
      subst heq
      have := FrameReferencable_stk_index_le cfg vcfg frame hreachx frame0.index hlocm
      exact absurd this (Nat.not_le.mpr hframe_lt_frame0)
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
          by_cases haeq : oida = oidm
          · by_cases hceq : oidc = oidy
            · -- ESCAPE: the mutated container's *new* field write is exactly the value read out
              -- of `yf` -- since that value was already resolvable pre-mutation, its own natural
              -- root gives an independent path to `oid` that doesn't depend on this hop at all.
              obtain ⟨frameY, hframeYMem, hrootY⟩ := resolveV_frameRoot hyr
              rw [hceq] at ihchain
              have hreachY : FrameReferencable cfg frameY.index (Reference.OId oid) := by
                rw [FrameReferencable_iff_reflTransGen]
                exact ⟨Reference.OId oidy, hrootY, ihchain⟩
              have hownerbound := FrameReferencable_owner_index_le cfg vcfg frameY hreachY frameD.regionId
                hlocDown frameD hframeDMem rfl
              by_cases heqidx : frameD.index = frameY.index
              · right
                have hFYeq : frameY = frameD :=
                  swap_corollary_stackWithIndex_index_inj hframeYMem hframeDMem heqidx.symm
                rw [← hFYeq]; exact hreachY
              · right
                have hltidx : frameD.index < frameY.index := lt_of_le_of_ne hownerbound heqidx
                exact vrcfg.cr3 frameD hframeDMem frameY hframeYMem hltidx oid hlocDown hreachY
            · left
              have hstep_cfg : RefStep cfg (Reference.OId oida) (Reference.OId oidc) := by
                rw [haeq]
                refine ⟨obj, hoidAtM_cfg, ?_⟩
                obtain ⟨objv, hobjAt, hcontains⟩ := hstep
                rw [haeq, hoidAtM] at hobjAt
                injection hobjAt with hobjAt_eq
                rw [← hobjAt_eq] at hcontains
                have hmem := List.contains_iff_mem.mp hcontains
                rcases fieldAsgn_corollary_object_insert_refs_mem hmem with heq | hmem'
                · injection heq with heq'; exact absurd heq' hceq
                · exact List.contains_iff_mem.mpr hmem'
              exact ihchain.head hstep_cfg
          · left
            have hstep_cfg : RefStep cfg (Reference.OId oida) (Reference.OId oidc) := by
              obtain ⟨objv, hobjAt, hcontains⟩ := hstep
              have heqA := fieldAsgn_corollary_stack_objAt_eq_of_ne
                (field := x.field) (yRef := Reference.OId oidy) (oid' := oida) hframe0 hobjm haeq
              rw [← hcfg'] at heqA
              exact ⟨objv, heqA ▸ hobjAt, hcontains⟩
            exact ihchain.head hstep_cfg
        · right; exact ihgoal
    have hconcDown : FrameReferencable cfg frame.index (Reference.OId oid) := by
      rw [FrameReferencable_iff_reflTransGen] at hreach
      obtain ⟨start, hroot, hrtg⟩ := hreach
      rcases main_claim start hrtg with hchain | hgoal
      · have hrootDown : FrameRoot cfg frame'.index start :=
          (fieldAsgn_corollary_frameRoot_iff h frame'.index start).mpr hroot
        have hreachD' : FrameReferencable cfg frameD'.index (Reference.OId oid) := by
          rw [hidxD']
          exact (FrameReferencable_iff_reflTransGen cfg frame'.index (Reference.OId oid)).mpr ⟨start, hrootDown, hchain⟩
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
        have hbne : oidb ≠ oidm := hoidm_ne oidb ihreach
        have heqB := fieldAsgn_corollary_stack_objAt_eq_of_ne
          (field := x.field) (yRef := Reference.OId oidy) (oid' := oidb) hframe0 hobjm hbne
        rw [← hcfg'] at heqB
        obtain ⟨objv, hobjAt, hcontains⟩ := hstep
        rw [hb_eq] at hobjAt
        rw [heq3] at hcontains
        refine ⟨FrameReferencable.step hobjAt hcontains ihreach, ihrtg.tail ⟨objv, ?_, hcontains⟩⟩
        rw [← heqB]; exact hobjAt
    have hup := main_claim_up (Reference.OId oid) hrtg2 oid rfl
    rw [FrameReferencable_iff_reflTransGen]
    exact ⟨start2, (fieldAsgn_corollary_frameRoot_iff h frame.index start2).mp hroot2, hup.2⟩
  · -- REGION branch
    have hlocEq0 :=
      fieldAsgn_corollary_region_loc_eq (field := x.field) (yRef := Reference.OId oidy) vcfg hregion hobjm oid
    rw [← hcfg'] at hlocEq0
    have hlocDown : (Reference.OId oid).loc? cfg = some (Location.Rgn frameD.regionId) := by
      rw [hridD, hlocEq0]; exact hloc
    have hoidAtM := fieldAsgn_corollary_region_objAt_mutated vcfg hregion hobjm hlocm hcfg'
    have hoidAtM_cfg : (Reference.OId oidm).objAt? cfg = some obj := by
      unfold Reference.objAt?
      dsimp only
      rw [hlocm]
      dsimp only
      rw [hregion]
      exact hobjm
    have hframe0_mem : frame0 ∈ cfg.stackWithIndex := List.mem_of_getLast? hframe0
    have hoidm_ne : ∀ oidx, FrameReferencable cfg frame.index (Reference.OId oidx) → oidx ≠ oidm := by
      intro oidx hreachx heq
      subst heq
      have := FrameReferencable_owner_index_le cfg vcfg frame hreachx rid hlocm frame0 hframe0_mem hfrid.symm
      exact absurd this (Nat.not_le.mpr hframe_lt_frame0)
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
          by_cases haeq : oida = oidm
          · by_cases hceq : oidc = oidy
            · -- ESCAPE
              obtain ⟨frameY, hframeYMem, hrootY⟩ := resolveV_frameRoot hyr
              rw [hceq] at ihchain
              have hreachY : FrameReferencable cfg frameY.index (Reference.OId oid) := by
                rw [FrameReferencable_iff_reflTransGen]
                exact ⟨Reference.OId oidy, hrootY, ihchain⟩
              have hownerbound := FrameReferencable_owner_index_le cfg vcfg frameY hreachY frameD.regionId
                hlocDown frameD hframeDMem rfl
              by_cases heqidx : frameD.index = frameY.index
              · right
                have hFYeq : frameY = frameD :=
                  swap_corollary_stackWithIndex_index_inj hframeYMem hframeDMem heqidx.symm
                rw [← hFYeq]; exact hreachY
              · right
                have hltidx : frameD.index < frameY.index := lt_of_le_of_ne hownerbound heqidx
                exact vrcfg.cr3 frameD hframeDMem frameY hframeYMem hltidx oid hlocDown hreachY
            · left
              have hstep_cfg : RefStep cfg (Reference.OId oida) (Reference.OId oidc) := by
                rw [haeq]
                refine ⟨obj, hoidAtM_cfg, ?_⟩
                obtain ⟨objv, hobjAt, hcontains⟩ := hstep
                rw [haeq, hoidAtM] at hobjAt
                injection hobjAt with hobjAt_eq
                rw [← hobjAt_eq] at hcontains
                have hmem := List.contains_iff_mem.mp hcontains
                rcases fieldAsgn_corollary_object_insert_refs_mem hmem with heq | hmem'
                · injection heq with heq'; exact absurd heq' hceq
                · exact List.contains_iff_mem.mpr hmem'
              exact ihchain.head hstep_cfg
          · left
            have hstep_cfg : RefStep cfg (Reference.OId oida) (Reference.OId oidc) := by
              obtain ⟨objv, hobjAt, hcontains⟩ := hstep
              have heqA := fieldAsgn_corollary_region_objAt_eq_of_ne vcfg
                (field := x.field) (yRef := Reference.OId oidy) (oid' := oida) hregion hobjm haeq
              rw [← hcfg'] at heqA
              exact ⟨objv, heqA ▸ hobjAt, hcontains⟩
            exact ihchain.head hstep_cfg
        · right; exact ihgoal
    have hconcDown : FrameReferencable cfg frame.index (Reference.OId oid) := by
      rw [FrameReferencable_iff_reflTransGen] at hreach
      obtain ⟨start, hroot, hrtg⟩ := hreach
      rcases main_claim start hrtg with hchain | hgoal
      · have hrootDown : FrameRoot cfg frame'.index start :=
          (fieldAsgn_corollary_frameRoot_iff h frame'.index start).mpr hroot
        have hreachD' : FrameReferencable cfg frameD'.index (Reference.OId oid) := by
          rw [hidxD']
          exact (FrameReferencable_iff_reflTransGen cfg frame'.index (Reference.OId oid)).mpr ⟨start, hrootDown, hchain⟩
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
        have hbne : oidb ≠ oidm := hoidm_ne oidb ihreach
        have heqB := fieldAsgn_corollary_region_objAt_eq_of_ne vcfg
          (field := x.field) (yRef := Reference.OId oidy) (oid' := oidb) hregion hobjm hbne
        rw [← hcfg'] at heqB
        obtain ⟨objv, hobjAt, hcontains⟩ := hstep
        rw [hb_eq] at hobjAt
        rw [heq3] at hcontains
        refine ⟨FrameReferencable.step hobjAt hcontains ihreach, ihrtg.tail ⟨objv, ?_, hcontains⟩⟩
        rw [← heqB]; exact hobjAt
    have hup := main_claim_up (Reference.OId oid) hrtg2 oid rfl
    rw [FrameReferencable_iff_reflTransGen]
    exact ⟨start2, (fieldAsgn_corollary_frameRoot_iff h frame.index start2).mp hroot2, hup.2⟩

theorem fieldAsgn_reachable_valid : ValidReachableConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  ValidReachableConfig cfg' := by
  intro vrcfg h
  exact { fieldAsgn_valid vrcfg.toValidConfig h with cr3 := fieldAsgn_cr3 vrcfg h }
