import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Theorems
import Gc.Model.Mutation

import Mathlib.Data.List.Infix

theorem swap_cases (h : swap x yf cfg = some cfg') :
    ∃ frame : FrameWithIndex, cfg.stackWithIndex.getLast? = some frame ∧
    ∃ yRef, resolveV yf.root cfg = some yRef ∧
    ∃ yRefLoc, yRef.loc? cfg = some yRefLoc ∧
    ∃ yfRef, resolveFA yf cfg = some yfRef ∧
    ∃ yfRefLoc, yfRef.loc? cfg = some yfRefLoc ∧
    ((-- SWAP-STACK
      ∃ yoid xRef obj,
        x ≠ frame.bridgeVar ∧
        yRef = Reference.OId yoid ∧
        yRefLoc = Location.Stk frame.index ∧
        frame.varMap.lookup x = some xRef ∧
        frame.objMap.lookup yoid = some obj ∧
        cfg' = { cfg with stack := cfg.stack.dropLast ++ [ { frame with
          varMap := frame.varMap.insert x yfRef,
          objMap := frame.objMap.insert yoid (obj.insert yf.field xRef)
        } ] }) ∨
     (-- SWAP-REGION-OBJECT
      ∃ yoid rid region obj xoid xrid,
        x ≠ frame.bridgeVar ∧
        yRef = Reference.OId yoid ∧
        yRefLoc = Location.Rgn rid ∧
        rid = frame.regionId ∧
        cfg.heap.lookup rid = some region ∧
        region.objMap.lookup yoid = some obj ∧
        frame.varMap.lookup x = some (Reference.OId xoid) ∧
        (Reference.OId xoid).loc? cfg = some (Location.Rgn xrid) ∧
        xrid = frame.regionId ∧
        region.status = Status.Open ∧
        cfg' = { cfg with
          stack := cfg.stack.dropLast ++ [ { frame with varMap := frame.varMap.insert x yfRef } ],
          heap := cfg.heap.insert rid { region with
            objMap := region.objMap.insert yoid (obj.insert yf.field (Reference.OId xoid)) }
        }) ∨
     (-- SWAP-REGION-REGION
      ∃ yoid rid region obj xrid,
        x ≠ frame.bridgeVar ∧
        yRef = Reference.OId yoid ∧
        yRefLoc = Location.Rgn rid ∧
        rid = frame.regionId ∧
        cfg.heap.lookup rid = some region ∧
        region.objMap.lookup yoid = some obj ∧
        frame.varMap.lookup x = some (Reference.RId xrid) ∧
        region.status = Status.Open ∧
        cfg' = { cfg with
          stack := cfg.stack.dropLast ++ [ { frame with varMap := frame.varMap.insert x yfRef } ],
          heap := cfg.heap.insert rid { region with
            objMap := region.objMap.insert yoid (obj.insert yf.field (Reference.RId xrid)) }
        }) ∨
     (-- SWAP-REGION-BRIDGE
      ∃ yoid yrid yfoid yfrid region obj,
        x = frame.bridgeVar ∧
        yRef = Reference.OId yoid ∧
        yRefLoc = Location.Rgn yrid ∧
        yfRef = Reference.OId yfoid ∧
        yfRefLoc = Location.Rgn yfrid ∧
        yrid = frame.regionId ∧
        yfrid = frame.regionId ∧
        cfg.heap.lookup yrid = some region ∧
        region.objMap.lookup yoid = some obj ∧
        cfg' = { cfg with
          heap := cfg.heap.insert yrid { region with
            bridgeObjectId := yfoid,
            objMap := region.objMap.insert yoid (obj.insert yf.field (Reference.OId region.bridgeObjectId)) }
        })) := by
  unfold swap at h
  cases hframe : cfg.stackWithIndex.getLast? with
  | none => rw [hframe] at h; contradiction
  | some frame =>
    rw [hframe] at h
    dsimp at h
    refine ⟨frame, rfl, ?_⟩
    cases hyr : resolveV yf.root cfg with
    | none => rw [hyr] at h; contradiction
    | some yRef =>
      rw [hyr] at h
      dsimp at h
      refine ⟨yRef, rfl, ?_⟩
      cases hyrl : yRef.loc? cfg with
      | none => rw [hyrl] at h; contradiction
      | some yRefLoc =>
        rw [hyrl] at h
        dsimp at h
        refine ⟨yRefLoc, rfl, ?_⟩
        cases hyf : resolveFA yf cfg with
        | none => rw [hyf] at h; contradiction
        | some yfRef =>
          rw [hyf] at h
          dsimp at h
          refine ⟨yfRef, rfl, ?_⟩
          cases hyfl : yfRef.loc? cfg with
          | none => rw [hyfl] at h; contradiction
          | some yfRefLoc =>
            rw [hyfl] at h
            dsimp at h
            refine ⟨yfRefLoc, rfl, ?_⟩
            by_cases hxb : (x != frame.bridgeVar) = true
            · rw [if_pos hxb] at h
              rw [bne_iff_ne] at hxb
              cases hxr : frame.varMap.lookup x with
              | none => rw [hxr] at h; contradiction
              | some xRef =>
                rw [hxr] at h
                dsimp at h
                cases yRef with
                | RId yrid0 => dsimp at h; contradiction
                | OId yoid =>
                  dsimp at h
                  cases yRefLoc with
                  | Stk fid =>
                    dsimp at h
                    by_cases hfid : (fid == frame.index) = true
                    · rw [if_pos hfid] at h
                      rw [beq_iff_eq] at hfid
                      cases hobj : frame.objMap.lookup yoid with
                      | none => rw [hobj] at h; contradiction
                      | some obj =>
                        rw [hobj] at h
                        dsimp at h
                        rw [Option.some_inj] at h
                        left
                        subst hfid
                        exact ⟨yoid, xRef, obj, hxb, rfl, rfl, rfl, hobj, h.symm⟩
                    · rw [if_neg hfid] at h; contradiction
                  | Rgn rid =>
                    dsimp at h
                    by_cases hrid : (rid == frame.regionId) = true
                    · rw [if_pos hrid] at h
                      rw [beq_iff_eq] at hrid
                      cases hregion : cfg.heap.lookup rid with
                      | none => rw [hregion] at h; contradiction
                      | some region =>
                        rw [hregion] at h
                        dsimp at h
                        cases hobj : region.objMap.lookup yoid with
                        | none => rw [hobj] at h; contradiction
                        | some obj =>
                          rw [hobj] at h
                          dsimp at h
                          cases xRef with
                          | OId xoid =>
                            dsimp at h
                            cases hxrl : (Reference.OId xoid).loc? cfg with
                            | none => rw [hxrl] at h; dsimp at h; contradiction
                            | some xRefLoc =>
                              rw [hxrl] at h
                              dsimp at h
                              cases xRefLoc with
                              | Stk fid' => dsimp at h; contradiction
                              | Rgn xrid =>
                                dsimp at h
                                by_cases hcond : xrid == frame.regionId ∧ region.status == Status.Open
                                · rw [if_pos hcond] at h
                                  obtain ⟨hxridEq0, hstatusEq0'⟩ := hcond
                                  rw [beq_iff_eq] at hxridEq0
                                  have hstatusEq0 : region.status = Status.Open := by
                                    cases hs : region.status with
                                    | Open => rfl
                                    | Closed => rw [hs] at hstatusEq0'; contradiction
                                  rw [Option.some_inj] at h
                                  right; left
                                  exact ⟨yoid, rid, region, obj, xoid, xrid, hxb, rfl, rfl, hrid, hregion, hobj,
                                    rfl, hxrl, hxridEq0, hstatusEq0, h.symm⟩
                                · rw [if_neg hcond] at h; contradiction
                          | RId xrid0 =>
                            dsimp at h
                            by_cases hstatus : region.status == Status.Open
                            · rw [if_pos hstatus] at h
                              have hstatusEq : region.status = Status.Open := by
                                cases hs : region.status with
                                | Open => rfl
                                | Closed => rw [hs] at hstatus; contradiction
                              rw [Option.some_inj] at h
                              right; right; left
                              exact ⟨yoid, rid, region, obj, xrid0, hxb, rfl, rfl, hrid, hregion, hobj, rfl,
                                hstatusEq, h.symm⟩
                            · rw [if_neg hstatus] at h; contradiction
                    · rw [if_neg hrid] at h; contradiction
            · rw [if_neg hxb] at h
              rw [Bool.not_eq_true] at hxb
              have hxb' : x = frame.bridgeVar := by
                by_contra hne
                have : (x != frame.bridgeVar) = true := by
                  rw [bne_iff_ne]; exact hne
                rw [this] at hxb; contradiction
              cases yRef with
              | RId yrid0 => dsimp at h; contradiction
              | OId yoid =>
                cases yRefLoc with
                | Stk fid => dsimp at h; contradiction
                | Rgn yrid =>
                  cases yfRef with
                  | RId yfrid0 => dsimp at h; contradiction
                  | OId yfoid =>
                    cases yfRefLoc with
                    | Stk fid' => dsimp at h; contradiction
                    | Rgn yfrid =>
                      dsimp at h
                      by_cases hcond2 : yrid == frame.regionId ∧ yfrid == frame.regionId
                      · rw [if_pos hcond2] at h
                        obtain ⟨hyridEq, hyfridEq⟩ := hcond2
                        rw [beq_iff_eq] at hyridEq hyfridEq
                        cases hregion : cfg.heap.lookup yrid with
                        | none => rw [hregion] at h; contradiction
                        | some region =>
                          rw [hregion] at h
                          dsimp at h
                          cases hobj : region.objMap.lookup yoid with
                          | none => rw [hobj] at h; contradiction
                          | some obj =>
                            rw [hobj] at h
                            dsimp at h
                            rw [Option.some_inj] at h
                            right; right; right
                            exact ⟨yoid, yrid, yfoid, yfrid, region, obj, hxb', rfl, rfl, rfl, rfl,
                              hyridEq, hyfridEq, hregion, hobj, h.symm⟩
                      · rw [if_neg hcond2] at h; contradiction

-- Relates the `stackWithIndex.getLast?` frame used by `swap_cases` back to `cfg.stack`'s own
-- decomposition, mirroring fieldAsgn_corollary_stack_eq/VarAsgn.lean's stack_eq construction.
theorem swap_corollary_stack_eq {cfg : RuntimeConfig} {frame : FrameWithIndex}
    (hframe : cfg.stackWithIndex.getLast? = some frame) :
    cfg.stack = cfg.stack.dropLast ++ [frame.toFrame] ∧ frame.index = cfg.stack.dropLast.length := by
  cases hlast : cfg.stack.getLast? with
  | none =>
    exfalso
    have hnil : cfg.stack = [] := List.getLast?_eq_none_iff.mp hlast
    unfold RuntimeConfig.stackWithIndex at hframe
    rw [hnil] at hframe
    simp at hframe
  | some lastF =>
    have stack_eq : cfg.stack = cfg.stack.dropLast ++ [lastF] :=
      (List.dropLast_append_getLast? lastF hlast).symm
    have stackWithIndex_eq :
        cfg.stackWithIndex =
          cfg.stack.dropLast.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) ++
            [({ lastF with index := cfg.stack.dropLast.length } : FrameWithIndex)] := by
      unfold RuntimeConfig.stackWithIndex
      conv_lhs => rw [stack_eq]
      rw [List.mapIdx_concat]
    rw [stackWithIndex_eq, List.getLast?_concat, Option.some_inj] at hframe
    subst hframe
    exact ⟨stack_eq, rfl⟩

theorem swap_S1 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  S1 cfg' := by
  intro vcfg h
  have s1 := vcfg.s1
  obtain ⟨frame, hframe, yRef, hyr, yRefLoc, hyrl, yfRef, hyf, yfRefLoc, hyfl, hcase⟩ := swap_cases h
  unfold S1
  obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
  have s1' : (cfg.stack.dropLast.map (fun frame => frame.regionId) ++ [frame.regionId]).Nodup := by
    have := s1
    unfold S1 at this
    rw [stack_eq, List.map_append] at this
    exact this
  rcases hcase with
    ⟨yoid, xRef, obj, hxb, hyoid, hyrloc, hxr, hobj, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xoid, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hxrl, hxrid, hstatus, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hstatus, hcfg'⟩ |
    ⟨yoid, yrid, yfoid, yfrid, region, obj, hxb, hyoid, hyrloc, hyfoid, hyfrloc, hyrid, hyfrid, hregion, hobj, hcfg'⟩
  · subst hcfg'
    dsimp
    rw [List.map_append]
    exact s1'
  · subst hcfg'
    dsimp
    rw [List.map_append]
    exact s1'
  · subst hcfg'
    dsimp
    rw [List.map_append]
    exact s1'
  · subst hcfg'
    dsimp
    exact s1

theorem swap_L1 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  L1 cfg' := by
  sorry

theorem swap_L2 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  L2 cfg' := by
  sorry

theorem swap_H1 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  H1 cfg' := by
  intro vcfg h
  have h1 := vcfg.h1
  obtain ⟨frame, hframe, yRef, hyr, yRefLoc, hyrl, yfRef, hyf, yfRefLoc, hyfl, hcase⟩ := swap_cases h
  unfold H1
  rcases hcase with
    ⟨yoid, xRef, obj, hxb, hyoid, hyrloc, hxr, hobj, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xoid, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hxrl, hxrid, hstatus, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hstatus, hcfg'⟩ |
    ⟨yoid, yrid, yfoid, yfrid, region, obj, hxb, hyoid, hyrloc, hyfoid, hyfrloc, hyrid, hyfrid, hregion, hobj, hcfg'⟩
  · subst hcfg'
    dsimp
    exact h1
  · subst hcfg'
    dsimp
    have region_mem : region ∈ cfg.heap.regions := by
      unfold Heap.regions
      exact List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hregion)
    intro region0 hregion0
    unfold Heap.regions at hregion0
    rw [AList.entries_insert, List.map_cons, List.mem_cons] at hregion0
    cases hregion0 with
    | inl heqregion =>
      subst heqregion
      dsimp
      exact (AList.mem_insert _).mpr (Or.inr (h1 region region_mem))
    | inr hkeraseregion =>
      apply h1
      unfold Heap.regions
      exact (List.Sublist.map _ (List.kerase_sublist rid cfg.heap.entries)).mem hkeraseregion
  · subst hcfg'
    dsimp
    have region_mem : region ∈ cfg.heap.regions := by
      unfold Heap.regions
      exact List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hregion)
    intro region0 hregion0
    unfold Heap.regions at hregion0
    rw [AList.entries_insert, List.map_cons, List.mem_cons] at hregion0
    cases hregion0 with
    | inl heqregion =>
      subst heqregion
      dsimp
      exact (AList.mem_insert _).mpr (Or.inr (h1 region region_mem))
    | inr hkeraseregion =>
      apply h1
      unfold Heap.regions
      exact (List.Sublist.map _ (List.kerase_sublist rid cfg.heap.entries)).mem hkeraseregion
  · subst hcfg'
    dsimp
    have region_mem : region ∈ cfg.heap.regions := by
      unfold Heap.regions
      exact List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hregion)
    have hyfrid_eq : yrid = yfrid := hyrid.trans hyfrid.symm
    have hyfoid_loc : (Reference.OId yfoid).loc? cfg = some (Location.Rgn yrid) := by
      rw [← hyfoid, hyfl, hyfrloc, hyfrid_eq]
    obtain ⟨region', hregion', hyfoid_mem'⟩ := (oid_loc_rgn_iff_in_heap vcfg).mp hyfoid_loc
    have region'_eq : region' = region := by rw [hregion] at hregion'; exact Option.some_inj.mp hregion'.symm
    have hyfoid_mem : yfoid ∈ region.objMap := region'_eq ▸ hyfoid_mem'
    intro region0 hregion0
    unfold Heap.regions at hregion0
    rw [AList.entries_insert, List.map_cons, List.mem_cons] at hregion0
    cases hregion0 with
    | inl heqregion =>
      subst heqregion
      dsimp
      exact (AList.mem_insert _).mpr (Or.inr hyfoid_mem)
    | inr hkeraseregion =>
      apply h1
      unfold Heap.regions
      exact (List.Sublist.map _ (List.kerase_sublist yrid cfg.heap.entries)).mem hkeraseregion

theorem swap_H2 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  H2 cfg' := by
  sorry

theorem swap_H3 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  H3 cfg' := by
  sorry

theorem swap_S2 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  S2 cfg' := by
  sorry

theorem swap_S3 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  S3 cfg' := by
  sorry

theorem swap_HS1 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  HS1 cfg' := by
  sorry

theorem swap_HS2 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  HS2 cfg' := by
  sorry

theorem swap_valid : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  ValidConfig cfg' := by
  intro vcfg h
  exact {
    l1 := swap_L1 vcfg h,
    l2 := swap_L2 vcfg h,
    h1 := swap_H1 vcfg h,
    h2 := swap_H2 vcfg h,
    h3 := swap_H3 vcfg h,
    s1 := swap_S1 vcfg h,
    s2 := swap_S2 vcfg h,
    s3 := swap_S3 vcfg h,
    hs1 := swap_HS1 vcfg h,
    hs2 := swap_HS2 vcfg h
  }
