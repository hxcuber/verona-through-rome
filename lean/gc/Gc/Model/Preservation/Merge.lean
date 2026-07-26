import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Theorems
import Gc.Model.Mutation

import Mathlib.Data.List.Infix

theorem merge_cases (h : merge x cfg = some cfg') :
    ∃ frame rid' region region',
      cfg.stack.getLast? = some frame ∧
      frame.varMap.lookup x = some (Reference.RId rid') ∧
      cfg.heap.lookup frame.regionId = some region ∧
      cfg.heap.lookup rid' = some region' ∧
      region'.status = Status.Closed ∧ region.status = Status.Open ∧
      cfg' = { cfg with
        heap := (cfg.heap.erase rid').insert frame.regionId { region with
          objMap := region.objMap.union region'.objMap },
        stack := cfg.stack.dropLast ++
          [ { frame with varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) } ]
      } := by
  unfold merge at h
  cases hframe : cfg.stack.getLast? with
  | none => rw [hframe] at h; contradiction
  | some frame =>
    rw [hframe] at h
    dsimp at h
    cases hxref : frame.varMap.lookup x with
    | none => rw [hxref] at h; contradiction
    | some xRef =>
      rw [hxref] at h
      dsimp at h
      cases xRef with
      | OId oid0 => dsimp at h; contradiction
      | RId rid' =>
        dsimp at h
        cases hregion : cfg.heap.lookup frame.regionId with
        | none => rw [hregion] at h; contradiction
        | some region =>
          rw [hregion] at h
          dsimp at h
          cases hregion' : cfg.heap.lookup rid' with
          | none => rw [hregion'] at h; contradiction
          | some region' =>
            rw [hregion'] at h
            dsimp at h
            by_cases hcond : region'.status = Status.Closed ∧ region.status = Status.Open
            · rw [if_pos hcond] at h
              rw [Option.some_inj] at h
              exact ⟨frame, rid', region, region', rfl, hxref, hregion, hregion', hcond.1, hcond.2, h.symm⟩
            · rw [if_neg hcond] at h; contradiction

-- `region`/`region'` can't be the same heap entry: the operation's own precondition requires
-- `region.status = Open` and `region'.status = Closed`, which are mutually exclusive.
theorem merge_corollary_rid_ne_regionId {cfg : RuntimeConfig} {frame : Frame} {rid' : RegionId}
    {region region' : Region} (hregion : cfg.heap.lookup frame.regionId = some region)
    (hregion' : cfg.heap.lookup rid' = some region')
    (hclosed : region'.status = Status.Closed) (hopen : region.status = Status.Open) :
    rid' ≠ frame.regionId := by
  intro heq
  rw [heq, hregion] at hregion'
  rw [Option.some_inj] at hregion'
  rw [hregion'] at hopen
  exact absurd (hopen.symm.trans hclosed) (by decide)

-- An object id can belong to at most one heap region's `objMap` (from `L1`'s global uniqueness).
theorem merge_corollary_region_unique
    {cfg : RuntimeConfig} {rid1 rid2 : RegionId} {region1 region2 : Region} {oid : ObjectId} :
  L1 cfg →
  (⟨rid1, region1⟩ : Sigma (fun _ : RegionId => Region)) ∈ cfg.heap.entries → oid ∈ region1.objMap.keys →
  (⟨rid2, region2⟩ : Sigma (fun _ : RegionId => Region)) ∈ cfg.heap.entries → oid ∈ region2.objMap.keys →
  rid1 = rid2 := by
  intro l1 mem1 in1 mem2 in2
  by_contra hne
  unfold L1 RuntimeConfig.objectIds at l1
  obtain ⟨_, heap_nodup, _⟩ := List.nodup_append.mp l1
  unfold Heap.objectIds at heap_nodup
  rw [List.nodup_flatten, List.pairwise_map] at heap_nodup
  obtain ⟨_, pairwise_disjoint⟩ := heap_nodup
  have hneq : (⟨rid1, region1⟩ : Sigma (fun _ : RegionId => Region)) ≠ ⟨rid2, region2⟩ := by
    intro heq
    exact hne (congrArg Sigma.fst heq)
  have disj := List.Pairwise.forall
    (R := fun (e1 e2 : Sigma (fun _ : RegionId => Region)) => List.Disjoint e1.2.objectIds e2.2.objectIds)
    (fun _ _ hd => List.disjoint_symm hd)
    pairwise_disjoint mem1 mem2 hneq
  unfold Region.objectIds at disj
  exact disj in1 in2

-- `region`'s and `region'`'s object ids are disjoint: both are distinct heap entries (via
-- `merge_corollary_rid_ne_regionId`), so `merge_corollary_region_unique` rules out any shared oid.
theorem merge_corollary_disjoint_keys {cfg : RuntimeConfig} {frame : Frame} {rid' : RegionId}
    {region region' : Region} (l1 : L1 cfg) (hregion : cfg.heap.lookup frame.regionId = some region)
    (hregion' : cfg.heap.lookup rid' = some region') (hne : rid' ≠ frame.regionId) :
    ∀ oid ∈ region.objMap.keys, oid ∉ region'.objMap.keys := by
  intro oid hoid hoid'
  exact hne.symm (merge_corollary_region_unique l1 (AList.lookup_mem_entries hregion) hoid
    (AList.lookup_mem_entries hregion') hoid')

-- Since `region`/`region'`'s objMap keys are disjoint, unioning them is a plain append at the
-- `entries` level (no `kunion`-induced reordering/erasure).
theorem merge_corollary_union_append {cfg : RuntimeConfig} {frame : Frame} {rid' : RegionId}
    {region region' : Region} (l1 : L1 cfg) (hregion : cfg.heap.lookup frame.regionId = some region)
    (hregion' : cfg.heap.lookup rid' = some region') (hne : rid' ≠ frame.regionId) :
    (region.objMap ∪ region'.objMap).entries = region.objMap.entries ++ region'.objMap.entries :=
  AList.union_eq_append_of_disjoint_keys (merge_corollary_disjoint_keys l1 hregion hregion' hne)

theorem merge_L1 : ValidConfig cfg →
  merge x cfg = some cfg' →
  L1 cfg' := by
  sorry

theorem merge_L2 : ValidConfig cfg →
  merge x cfg = some cfg' →
  L2 cfg' := by
  intro vcfg h
  have l2 := vcfg.l2
  obtain ⟨frame, rid', region, region', hframe, hxref, hregion, hregion', hclosed, hopen, hcfg'⟩ :=
    merge_cases h
  subst hcfg'
  unfold L2
  dsimp
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
    (List.dropLast_append_getLast? frame hframe).symm
  have frame_mem : frame ∈ cfg.stack := stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self _)
  intro frame'' hmem
  rw [List.mem_append, List.mem_singleton] at hmem
  obtain ⟨region0, hlookup0, hopen0⟩ :
      ∃ region0, cfg.heap.lookup frame''.regionId = some region0 ∧ region0.status = Status.Open := by
    cases hmem with
    | inl hdrop => exact l2 frame'' (List.mem_of_mem_dropLast hdrop)
    | inr heqframe => subst heqframe; exact l2 frame frame_mem
  by_cases heq1 : frame''.regionId = frame.regionId
  · refine ⟨{ region with objMap := region.objMap.union region'.objMap }, ?_, ?_⟩
    · rw [heq1, AList.lookup_insert]
    · dsimp; exact hopen
  · by_cases heq2 : frame''.regionId = rid'
    · exfalso
      rw [heq2, hregion'] at hlookup0
      rw [Option.some_inj] at hlookup0
      rw [hlookup0] at hclosed
      exact absurd (hopen0.symm.trans hclosed) (by decide)
    · refine ⟨region0, ?_, hopen0⟩
      rw [AList.lookup_insert_ne heq1, AList.lookup_erase_ne heq2]
      exact hlookup0

theorem merge_H1 : ValidConfig cfg →
  merge x cfg = some cfg' →
  H1 cfg' := by
  intro vcfg h
  have h1 := vcfg.h1
  obtain ⟨frame, rid', region, region', hframe, hxref, hregion, hregion', hclosed, hopen, hcfg'⟩ :=
    merge_cases h
  subst hcfg'
  unfold H1
  dsimp
  intro region0 hregion0
  unfold Heap.regions at hregion0
  rw [AList.entries_insert, List.map_cons, List.mem_cons] at hregion0
  rcases hregion0 with heq | hmem
  · subst heq
    dsimp only
    have hbmem : region.bridgeObjectId ∈ region.objMap :=
      h1 region (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hregion))
    exact AList.mem_union.mpr (Or.inl hbmem)
  · apply h1
    have hsub1 : List.Sublist (List.kerase frame.regionId (AList.erase rid' cfg.heap).entries)
        (AList.erase rid' cfg.heap).entries :=
      List.kerase_sublist frame.regionId (AList.erase rid' cfg.heap).entries
    have hsub2 : List.Sublist (AList.erase rid' cfg.heap).entries cfg.heap.entries :=
      List.kerase_sublist rid' cfg.heap.entries
    exact ((hsub1.trans hsub2).map (·.2)).mem hmem

theorem merge_H2 : ValidConfig cfg →
  merge x cfg = some cfg' →
  H2 cfg' := by
  sorry

theorem merge_H3 : ValidConfig cfg →
  merge x cfg = some cfg' →
  H3 cfg' := by
  sorry

theorem merge_S1 : ValidConfig cfg →
  merge x cfg = some cfg' →
  S1 cfg' := by
  intro vcfg h
  have s1 := vcfg.s1
  obtain ⟨frame, rid', region, region', hframe, hxref, hregion, hregion', hclosed, hopen, hcfg'⟩ :=
    merge_cases h
  subst hcfg'
  unfold S1
  dsimp
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
    (List.dropLast_append_getLast? frame hframe).symm
  have regionId_eq : (cfg.stack.dropLast ++
      [{ frame with varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) }]).map
      (fun f : Frame => f.regionId) = cfg.stack.map (fun f : Frame => f.regionId) := by
    conv_rhs => rw [stack_eq]
    rw [List.map_append, List.map_append]
    rfl
  rw [regionId_eq]
  exact s1

theorem merge_S2 : ValidConfig cfg →
  merge x cfg = some cfg' →
  S2 cfg' := by
  sorry

theorem merge_S3 : ValidConfig cfg →
  merge x cfg = some cfg' →
  S3 cfg' := by
  sorry

theorem merge_HS1 : ValidConfig cfg →
  merge x cfg = some cfg' →
  HS1 cfg' := by
  sorry

theorem merge_HS2 : ValidConfig cfg →
  merge x cfg = some cfg' →
  HS2 cfg' := by
  sorry

theorem merge_valid : ValidConfig cfg →
  merge x cfg = some cfg' →
  ValidConfig cfg' := by
  intro vcfg h
  exact {
    l1 := merge_L1 vcfg h,
    l2 := merge_L2 vcfg h,
    h1 := merge_H1 vcfg h,
    h2 := merge_H2 vcfg h,
    h3 := merge_H3 vcfg h,
    s1 := merge_S1 vcfg h,
    s2 := merge_S2 vcfg h,
    s3 := merge_S3 vcfg h,
    hs1 := merge_HS1 vcfg h,
    hs2 := merge_HS2 vcfg h
  }
