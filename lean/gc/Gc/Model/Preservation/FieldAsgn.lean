import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Theorems
import Gc.Model.Mutation

import Mathlib.Data.List.Infix

theorem fieldAsgn_cases (h : fieldAsgn xf y cfg = some cfg') :
    ∃ frame : FrameWithIndex, cfg.stackWithIndex.getLast? = some frame ∧
      ((∃ oid oid_y obj,
          resolveV xf.root cfg = some (Reference.OId oid) ∧
          resolveV y cfg = some (Reference.OId oid_y) ∧
          (Reference.OId oid).loc? cfg = some (Location.Stk frame.index) ∧
          frame.objMap.lookup oid = some obj ∧
          cfg' = { cfg with stack := cfg.stack.dropLast ++
            [ { frame with objMap := frame.objMap.insert oid (obj.insert xf.field (Reference.OId oid_y)) } ] }) ∨
       (∃ oid oid_y rid region obj,
          resolveV xf.root cfg = some (Reference.OId oid) ∧
          resolveV y cfg = some (Reference.OId oid_y) ∧
          (Reference.OId oid).loc? cfg = some (Location.Rgn rid) ∧
          cfg.heap.lookup rid = some region ∧
          region.objMap.lookup oid = some obj ∧
          (Reference.OId oid_y).loc? cfg = some (Location.Rgn rid) ∧
          region.status = Status.Open ∧
          cfg' = { cfg with heap := cfg.heap.insert rid { region with
            objMap := region.objMap.insert oid (obj.insert xf.field (Reference.OId oid_y)) } })) := by
  unfold fieldAsgn at h
  cases hframe : cfg.stackWithIndex.getLast? with
  | none => rw [hframe] at h; contradiction
  | some frame =>
    rw [hframe] at h
    dsimp at h
    refine ⟨frame, rfl, ?_⟩
    cases hxr : resolveV xf.root cfg with
    | none => rw [hxr] at h; contradiction
    | some xRef =>
      rw [hxr] at h
      dsimp at h
      cases hyr : resolveV y cfg with
      | none => rw [hyr] at h; contradiction
      | some yRef =>
        rw [hyr] at h
        dsimp at h
        cases xRef with
        | RId rid0 => dsimp at h; contradiction
        | OId oid =>
          cases yRef with
          | RId rid1 => dsimp at h; contradiction
          | OId oid_y =>
            dsimp at h
            cases hloc : (Reference.OId oid).loc? cfg with
            | none => rw [hloc] at h; dsimp at h; contradiction
            | some loc =>
              rw [hloc] at h
              dsimp at h
              cases loc with
              | Stk fid =>
                dsimp at h
                by_cases hfid : (fid == frame.index) = true
                · rw [if_pos hfid] at h
                  rw [beq_iff_eq] at hfid
                  cases hobj : frame.objMap.lookup oid with
                  | none => rw [hobj] at h; contradiction
                  | some obj =>
                    rw [hobj] at h
                    dsimp at h
                    rw [Option.some_inj] at h
                    left
                    subst hfid
                    exact ⟨oid, oid_y, obj, rfl, rfl, hloc, hobj, h.symm⟩
                · rw [if_neg hfid] at h; contradiction
              | Rgn rid =>
                dsimp at h
                cases hregion : cfg.heap.lookup rid with
                | none => rw [hregion] at h; contradiction
                | some region =>
                  rw [hregion] at h
                  dsimp at h
                  cases hobj : region.objMap.lookup oid with
                  | none => rw [hobj] at h; contradiction
                  | some obj =>
                    rw [hobj] at h
                    dsimp at h
                    cases hyloc : (Reference.OId oid_y).loc? cfg with
                    | none => rw [hyloc] at h; dsimp at h; contradiction
                    | some yloc =>
                      rw [hyloc] at h
                      dsimp at h
                      cases yloc with
                      | Stk fid' => dsimp at h; contradiction
                      | Rgn rid' =>
                        dsimp at h
                        by_cases hcond : rid == rid' ∧ region.status == Status.Open
                        · rw [if_pos hcond] at h
                          obtain ⟨hridEq0, hstatusEq0'⟩ := hcond
                          rw [beq_iff_eq] at hridEq0
                          have hstatusEq0 : region.status = Status.Open := by
                            cases hs : region.status with
                            | Open => rfl
                            | Closed => rw [hs] at hstatusEq0'; contradiction
                          rw [Option.some_inj] at h
                          right
                          subst hridEq0
                          exact ⟨oid, oid_y, rid, region, obj, rfl, rfl, hloc, hregion, hobj, hyloc,
                            hstatusEq0, h.symm⟩
                        · rw [if_neg hcond] at h; contradiction

-- Relates the `stackWithIndex.getLast?` frame used by `fieldAsgn_cases` back to `cfg.stack`'s own
-- decomposition, mirroring the `stack_eq`/`stackWithIndex_eq` construction used throughout
-- VarAsgn.lean/MakeObjStack.lean, just starting from `stackWithIndex.getLast?` instead of `stack.getLast?`.
theorem fieldAsgn_corollary_stack_eq {cfg : RuntimeConfig} {frame : FrameWithIndex}
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

theorem fieldAsgn_L1 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  L1 cfg' := by
  sorry

theorem fieldAsgn_L2 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  L2 cfg' := by
  sorry

theorem fieldAsgn_S1 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  S1 cfg' := by
  intro vcfg h
  have s1 := vcfg.s1
  obtain ⟨frame, hframe, hcase⟩ := fieldAsgn_cases h
  unfold S1
  rcases hcase with
    ⟨oid, oid_y, obj, hxr, hyr, hloc, hobj, hcfg'⟩ |
    ⟨oid, oid_y, rid, region, obj, hxr, hyr, hloc, hregion, hobj, hyloc, hstatus, hcfg'⟩
  · subst hcfg'
    obtain ⟨stack_eq, _⟩ := fieldAsgn_corollary_stack_eq hframe
    have s1' : (cfg.stack.dropLast.map (fun frame => frame.regionId) ++ [frame.regionId]).Nodup := by
      have := s1
      unfold S1 at this
      rw [stack_eq, List.map_append] at this
      exact this
    dsimp
    rw [List.map_append]
    exact s1'
  · subst hcfg'
    dsimp
    exact s1

theorem fieldAsgn_H1 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  H1 cfg' := by
  intro vcfg h
  have h1 := vcfg.h1
  obtain ⟨frame, hframe, hcase⟩ := fieldAsgn_cases h
  unfold H1
  rcases hcase with
    ⟨oid, oid_y, obj, hxr, hyr, hloc, hobj, hcfg'⟩ |
    ⟨oid, oid_y, rid, region, obj, hxr, hyr, hloc, hregion, hobj, hyloc, hstatus, hcfg'⟩
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

theorem fieldAsgn_H2 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  H2 cfg' := by
  sorry

theorem fieldAsgn_H3 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  H3 cfg' := by
  sorry

theorem fieldAsgn_S2 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  S2 cfg' := by
  sorry

theorem fieldAsgn_S3 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  S3 cfg' := by
  sorry

theorem fieldAsgn_HS1 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  HS1 cfg' := by
  sorry

theorem fieldAsgn_HS2 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  HS2 cfg' := by
  sorry

theorem fieldAsgn_valid : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  ValidConfig cfg' := by
  intro vcfg h
  exact {
    l1 := fieldAsgn_L1 vcfg h,
    l2 := fieldAsgn_L2 vcfg h,
    h1 := fieldAsgn_H1 vcfg h,
    h2 := fieldAsgn_H2 vcfg h,
    h3 := fieldAsgn_H3 vcfg h,
    s1 := fieldAsgn_S1 vcfg h,
    s2 := fieldAsgn_S2 vcfg h,
    s3 := fieldAsgn_S3 vcfg h,
    hs1 := fieldAsgn_HS1 vcfg h,
    hs2 := fieldAsgn_HS2 vcfg h
  }
