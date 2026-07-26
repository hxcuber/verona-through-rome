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

-- Generic AList fact: a successful `lookup` means the key is already present.
theorem merge_corollary_mem_keys_of_lookup {α : Type*} {β : α → Type*} [DecidableEq α]
    {l : AList β} {k : α} {v : β k} (hv : l.lookup k = some v) : k ∈ l.keys :=
  AList.mem_keys.mp (AList.lookup_isSome.mp (by rw [hv]; rfl))

-- Generic fact: replacing the value at an already-present `AList` key changes the refs-count by
-- exactly the delta of the one changed entry -- stated additively (rather than with subtraction) so
-- it holds unconditionally regardless of what the old/new values actually are.
theorem merge_corollary_alist_insert_count_eq {α : Type*} [DecidableEq α] {l : AList (fun _ : α => Reference)}
    {k : α} {v_old v_new t : Reference} (hlookup : l.lookup k = some v_old) :
    ((l.insert k v_new).entries.map (·.2)).count t + (if (v_old == t) = true then 1 else 0) =
    (l.entries.map (·.2)).count t + (if (v_new == t) = true then 1 else 0) := by
  obtain ⟨v0, l1e, l2e, hnotmem, heq, hkerase⟩ := List.exists_of_kerase (merge_corollary_mem_keys_of_lookup hlookup)
  have v0_eq : v0 = v_old := by
    have hmem_v0 : (⟨k, v0⟩ : Sigma (fun _ : α => Reference)) ∈ l.entries :=
      heq ▸ List.mem_append_right _ List.mem_cons_self
    have hmem_vold : (⟨k, v_old⟩ : Sigma (fun _ : α => Reference)) ∈ l.entries :=
      AList.mem_lookup_iff.mp (by rw [hlookup]; rfl)
    exact List.NodupKeys.eq_of_mk_mem (β := fun _ : α => Reference) l.nodupKeys hmem_v0 hmem_vold
  have hnew : (l.insert k v_new).entries.map (·.2) = v_new :: (l1e ++ l2e).map (·.2) := by
    rw [AList.entries_insert, hkerase, List.map_cons]
  have hold : l.entries.map (·.2) = l1e.map (·.2) ++ v_old :: l2e.map (·.2) := by
    rw [heq, v0_eq, List.map_append, List.map_cons]
  rw [hnew, hold, List.count_cons, List.map_append, List.count_append, List.count_append, List.count_cons]
  omega

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

-- `cfg.heap.entries` reorders (via `exists_of_kerase`, extracting `rid'` then `frame.regionId` from
-- what's left) into exactly `region`/`region'`'s pair plus the same "everything else" tail that
-- `cfg'.heap.entries` is built from (`kerase frame.regionId (kerase rid' cfg.heap.entries)`).
theorem merge_corollary_heap_entries_perm {cfg : RuntimeConfig} {frame : Frame} {rid' : RegionId}
    {region region' : Region} (hregion : cfg.heap.lookup frame.regionId = some region)
    (hregion' : cfg.heap.lookup rid' = some region') (hne : rid' ≠ frame.regionId) :
    cfg.heap.entries.Perm
      (⟨frame.regionId, region⟩ :: ⟨rid', region'⟩ ::
        List.kerase frame.regionId (List.kerase rid' cfg.heap.entries)) := by
  obtain ⟨b1, l1, l2, hnotmem1, heq1, hkerase1⟩ :=
    List.exists_of_kerase (a := rid') (List.mem_keys_of_mem (AList.lookup_mem_entries hregion'))
  have hb1 : b1 = region' :=
    List.NodupKeys.eq_of_mk_mem cfg.heap.nodupKeys (heq1 ▸ List.mem_append_right _ List.mem_cons_self)
      (AList.lookup_mem_entries hregion')
  rw [hb1] at heq1
  have hmem2 : frame.regionId ∈ (List.kerase rid' cfg.heap.entries).keys :=
    (List.mem_keys_kerase_of_ne hne.symm).mpr (List.mem_keys_of_mem (AList.lookup_mem_entries hregion))
  rw [hkerase1] at hmem2
  obtain ⟨b2, m1, m2, hnotmem2, heq2, hkerase2⟩ := List.exists_of_kerase (a := frame.regionId) hmem2
  have hb2 : b2 = region := by
    have hmem_l1l2 : (⟨frame.regionId, b2⟩ : Sigma (fun _ : RegionId => Region)) ∈ l1 ++ l2 :=
      heq2 ▸ List.mem_append_right _ List.mem_cons_self
    have hmem_cfg : (⟨frame.regionId, b2⟩ : Sigma (fun _ : RegionId => Region)) ∈ cfg.heap.entries := by
      rw [heq1]
      rcases List.mem_append.mp hmem_l1l2 with hl1 | hl2
      · exact List.mem_append_left _ hl1
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hl2)
    exact List.NodupKeys.eq_of_mk_mem cfg.heap.nodupKeys hmem_cfg (AList.lookup_mem_entries hregion)
  rw [hb2] at heq2
  rw [← hkerase1] at hkerase2
  rw [hkerase2]
  have step1 : cfg.heap.entries.Perm ((⟨rid', region'⟩ : Sigma (fun _ : RegionId => Region)) :: (l1 ++ l2)) := by
    rw [heq1]; exact List.perm_middle
  have step2 : (((⟨rid', region'⟩ : Sigma (fun _ : RegionId => Region)) :: (l1 ++ l2)).Perm
      ((⟨rid', region'⟩ : Sigma (fun _ : RegionId => Region)) :: (⟨frame.regionId, region⟩ :: (m1 ++ m2)))) := by
    apply List.Perm.cons
    rw [heq2]; exact List.perm_middle
  have step3 : (((⟨rid', region'⟩ : Sigma (fun _ : RegionId => Region)) ::
      ⟨frame.regionId, region⟩ :: (m1 ++ m2)).Perm
      ((⟨frame.regionId, region⟩ : Sigma (fun _ : RegionId => Region)) :: ⟨rid', region'⟩ :: (m1 ++ m2))) :=
    List.Perm.swap _ _ _
  exact step1.trans (step2.trans step3)

-- Nothing is created or destroyed by merging two regions' objMaps into one heap entry -- the merged
-- heap's `objectIds` is a permutation (reunioned into fewer heap keys, same underlying multiset) of
-- the original.
theorem merge_corollary_heap_objectIds_perm {cfg : RuntimeConfig} {frame : Frame} {rid' : RegionId}
    {region region' : Region} (l1 : L1 cfg) (hregion : cfg.heap.lookup frame.regionId = some region)
    (hregion' : cfg.heap.lookup rid' = some region') (hne : rid' ≠ frame.regionId) :
    (Heap.objectIds ((cfg.heap.erase rid').insert frame.regionId { region with
      objMap := region.objMap ∪ region'.objMap })).Perm cfg.heap.objectIds := by
  have entries_perm := merge_corollary_heap_entries_perm hregion hregion' hne
  have hunion : Region.objectIds { region with objMap := region.objMap ∪ region'.objMap } =
      region.objectIds ++ region'.objectIds := by
    show (region.objMap ∪ region'.objMap).keys = region.objMap.keys ++ region'.objMap.keys
    unfold AList.keys
    rw [merge_corollary_union_append l1 hregion hregion' hne, List.keys_append]
  unfold Heap.objectIds
  rw [AList.entries_insert]
  have hkerase_eq : (cfg.heap.erase rid').entries.kerase frame.regionId =
      List.kerase frame.regionId (List.kerase rid' cfg.heap.entries) := rfl
  rw [hkerase_eq, List.map_cons, List.flatten_cons, hunion, List.append_assoc]
  have step := (entries_perm.map (fun e => e.2.objectIds)).flatten
  rw [List.map_cons, List.map_cons, List.flatten_cons, List.flatten_cons] at step
  exact step.symm

-- Same idea, for `Heap.refs`: merging never creates or destroys a reference, only regroups them.
theorem merge_corollary_heap_refs_perm {cfg : RuntimeConfig} {frame : Frame} {rid' : RegionId}
    {region region' : Region} (l1 : L1 cfg) (hregion : cfg.heap.lookup frame.regionId = some region)
    (hregion' : cfg.heap.lookup rid' = some region') (hne : rid' ≠ frame.regionId) :
    (Heap.refs ((cfg.heap.erase rid').insert frame.regionId { region with
      objMap := region.objMap ∪ region'.objMap })).Perm cfg.heap.refs := by
  have entries_perm := merge_corollary_heap_entries_perm hregion hregion' hne
  have hunion : Region.refs { region with objMap := region.objMap ∪ region'.objMap } =
      region.refs ++ region'.refs := by
    unfold Region.refs
    rw [merge_corollary_union_append l1 hregion hregion' hne, List.map_append,
      List.bind_eq_flatMap, List.bind_eq_flatMap, List.bind_eq_flatMap, List.flatMap_append]
  have heap_refs_eq : ∀ h : Heap, h.refs = (h.entries.map (fun e => e.2.refs)).flatten := by
    intro h
    unfold Heap.refs
    rw [List.bind_eq_flatMap, List.flatMap_def, List.map_map]
    rfl
  rw [heap_refs_eq, heap_refs_eq]
  rw [AList.entries_insert]
  have hkerase_eq : (cfg.heap.erase rid').entries.kerase frame.regionId =
      List.kerase frame.regionId (List.kerase rid' cfg.heap.entries) := rfl
  rw [hkerase_eq, List.map_cons, List.flatten_cons, hunion, List.append_assoc]
  have step := (entries_perm.map (fun e => e.2.refs)).flatten
  rw [List.map_cons, List.map_cons, List.flatten_cons, List.flatten_cons] at step
  exact step.symm

theorem merge_L1 : ValidConfig cfg →
  merge x cfg = some cfg' →
  L1 cfg' := by
  intro vcfg h
  have l1 := vcfg.l1
  obtain ⟨frame, rid', region, region', hframe, hxref, hregion, hregion', hclosed, hopen, hcfg'⟩ :=
    merge_cases h
  subst hcfg'
  unfold L1 RuntimeConfig.objectIds
  dsimp
  have hne := merge_corollary_rid_ne_regionId hregion hregion' hclosed hopen
  have heap_perm := merge_corollary_heap_objectIds_perm l1 hregion hregion' hne
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
    (List.dropLast_append_getLast? frame hframe).symm
  have stack_objectIds_eq : Stack.objectIds (cfg.stack.dropLast ++
      [{ frame with varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) }]) =
      Stack.objectIds cfg.stack := by
    conv_rhs => rw [stack_eq]
    unfold Stack.objectIds
    rw [List.map_append, List.map_append]
    rfl
  rw [stack_objectIds_eq]
  have perm_full : (Stack.objectIds cfg.stack ++ cfg.heap.objectIds).Perm
      (Stack.objectIds cfg.stack ++ Heap.objectIds ((cfg.heap.erase rid').insert frame.regionId
        { region with objMap := region.objMap ∪ region'.objMap })) :=
    List.Perm.append_left (Stack.objectIds cfg.stack) heap_perm.symm
  exact perm_full.nodup l1

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
  intro vcfg h
  have l1 := vcfg.l1
  have h2 := vcfg.h2
  obtain ⟨frame, rid', region, region', hframe, hxref, hregion, hregion', hclosed, hopen, hcfg'⟩ :=
    merge_cases h
  subst hcfg'
  unfold H2
  dsimp
  have hne := merge_corollary_rid_ne_regionId hregion hregion' hclosed hopen
  have heap_perm' : (Heap.refs ((cfg.heap.erase rid').insert frame.regionId { region with
      objMap := AList.union region.objMap region'.objMap })).Perm cfg.heap.refs :=
    merge_corollary_heap_refs_perm l1 hregion hregion' hne
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
    (List.dropLast_append_getLast? frame hframe).symm
  intro rid
  rw [heap_perm'.count_eq]
  have hOId_ne : (Reference.OId region'.bridgeObjectId == Reference.RId rid) = false := rfl
  have varmap_le : ((frame.varMap.insert x (Reference.OId region'.bridgeObjectId)).entries.map (·.2)).count
      (Reference.RId rid) ≤ (frame.varMap.entries.map (·.2)).count (Reference.RId rid) := by
    have hcount := merge_corollary_alist_insert_count_eq
      (v_old := Reference.RId rid') (v_new := Reference.OId region'.bridgeObjectId) (t := Reference.RId rid) hxref
    rw [hOId_ne] at hcount
    simp only [Bool.false_eq_true, if_false, Nat.add_zero] at hcount
    omega
  have newFrame_refs_le : (Frame.refs { frame with
      varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) }).count (Reference.RId rid) ≤
      frame.refs.count (Reference.RId rid) := by
    unfold Frame.refs
    dsimp
    rw [List.count_append, List.count_append]
    exact Nat.add_le_add_left varmap_le _
  have stack_refs_le : (Stack.refs (cfg.stack.dropLast ++
      [{ frame with varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) }])).count
      (Reference.RId rid) ≤ cfg.stack.refs.count (Reference.RId rid) := by
    have split1 : Stack.refs (cfg.stack.dropLast ++
        [{ frame with varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) }]) =
        Stack.refs cfg.stack.dropLast ++ Frame.refs { frame with
          varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) } := by
      unfold Stack.refs
      rw [List.bind_eq_flatMap, List.bind_eq_flatMap, List.flatMap_id, List.flatMap_id,
        List.map_append, List.flatten_append, List.map_singleton, List.flatten_singleton]
    have split2 : Stack.refs cfg.stack = Stack.refs cfg.stack.dropLast ++ Frame.refs frame := by
      conv_lhs => rw [stack_eq]
      unfold Stack.refs
      rw [List.bind_eq_flatMap, List.bind_eq_flatMap, List.flatMap_id, List.flatMap_id,
        List.map_append, List.flatten_append, List.map_singleton, List.flatten_singleton]
    rw [split1, split2, List.count_append, List.count_append]
    exact Nat.add_le_add_left newFrame_refs_le _
  have h2rid := h2 rid
  omega

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
  intro vcfg h
  have l1 := vcfg.l1
  have h1 := vcfg.h1
  have hs1 := vcfg.hs1
  obtain ⟨frame, rid', region, region', hframe, hxref, hregion, hregion', hclosed, hopen, hcfg'⟩ :=
    merge_cases h
  subst hcfg'
  unfold HS1
  have hne := merge_corollary_rid_ne_regionId hregion hregion' hclosed hopen
  have heap_refs_perm' : (Heap.refs ((cfg.heap.erase rid').insert frame.regionId { region with
      objMap := AList.union region.objMap region'.objMap })).Perm cfg.heap.refs :=
    merge_corollary_heap_refs_perm l1 hregion hregion' hne
  have heap_ids_perm' : (Heap.objectIds ((cfg.heap.erase rid').insert frame.regionId { region with
      objMap := AList.union region.objMap region'.objMap })).Perm cfg.heap.objectIds :=
    merge_corollary_heap_objectIds_perm l1 hregion hregion' hne
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
    (List.dropLast_append_getLast? frame hframe).symm
  have stack_split1 : Stack.refs (cfg.stack.dropLast ++
      [{ frame with varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) }]) =
      Stack.refs cfg.stack.dropLast ++ Frame.refs { frame with
        varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) } := by
    unfold Stack.refs
    rw [List.bind_eq_flatMap, List.bind_eq_flatMap, List.flatMap_id, List.flatMap_id,
      List.map_append, List.flatten_append, List.map_singleton, List.flatten_singleton]
  have stack_split2 : Stack.refs cfg.stack = Stack.refs cfg.stack.dropLast ++ Frame.refs frame := by
    conv_lhs => rw [stack_eq]
    unfold Stack.refs
    rw [List.bind_eq_flatMap, List.bind_eq_flatMap, List.flatMap_id, List.flatMap_id,
      List.map_append, List.flatten_append, List.map_singleton, List.flatten_singleton]
  have newFrame_split : Frame.refs { frame with
      varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) } =
      (frame.objMap.entries.map (·.2) >>= Object.refs) ++
        (frame.varMap.insert x (Reference.OId region'.bridgeObjectId)).entries.map (·.2) := by
    unfold Frame.refs; rfl
  have frame_split : Frame.refs frame =
      (frame.objMap.entries.map (·.2) >>= Object.refs) ++ frame.varMap.entries.map (·.2) := by
    unfold Frame.refs; rfl
  have stack_objectIds_eq : Stack.objectIds (cfg.stack.dropLast ++
      [{ frame with varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) }]) =
      Stack.objectIds cfg.stack := by
    conv_rhs => rw [stack_eq]
    unfold Stack.objectIds
    rw [List.map_append, List.map_append]
    rfl
  have objectIds_perm : (Stack.objectIds (cfg.stack.dropLast ++
      [{ frame with varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) }]) ++
      Heap.objectIds ((cfg.heap.erase rid').insert frame.regionId { region with
        objMap := AList.union region.objMap region'.objMap })).Perm
      (Stack.objectIds cfg.stack ++ Heap.objectIds cfg.heap) := by
    rw [stack_objectIds_eq]
    exact List.Perm.append_left (Stack.objectIds cfg.stack) heap_ids_perm'
  -- `region'.bridgeObjectId` (the value the new varMap entry takes) was already an allocated id.
  have hbridge_mem : region'.bridgeObjectId ∈ cfg.objectIds := by
    have hbmem : region'.bridgeObjectId ∈ region'.objMap :=
      h1 region' (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hregion'))
    rw [AList.mem_keys] at hbmem
    unfold RuntimeConfig.objectIds
    exact List.mem_append_right _ (List.mem_flatten.mpr
      ⟨region'.objMap.keys, List.mem_map_of_mem (f := fun e => e.2.objectIds)
        (AList.lookup_mem_entries hregion'), hbmem⟩)
  intro oid href
  unfold RuntimeConfig.refs at href
  dsimp at href
  unfold RuntimeConfig.objectIds
  dsimp
  rw [List.mem_append] at href
  have hoid_cfg : oid ∈ cfg.objectIds := by
    rcases href with h1' | h1'
    · rw [stack_split1, List.mem_append] at h1'
      rcases h1' with h1' | h1'
      · exact hs1 oid (by
          unfold RuntimeConfig.refs
          exact List.mem_append_left _ (stack_split2 ▸ List.mem_append_left _ h1'))
      · rw [newFrame_split, List.mem_append] at h1'
        rcases h1' with h1' | h1'
        · exact hs1 oid (by
            unfold RuntimeConfig.refs
            exact List.mem_append_left _ (stack_split2 ▸ List.mem_append_right _ (frame_split ▸ List.mem_append_left _ h1')))
        · have hsub : List.Sublist (List.kerase x frame.varMap.entries) frame.varMap.entries :=
            List.kerase_sublist x frame.varMap.entries
          have hins := AList.entries_insert (a := x) (b := Reference.OId region'.bridgeObjectId) (s := frame.varMap)
          rw [hins, List.map_cons] at h1'
          rcases List.mem_cons.mp h1' with heq | h1'
          · rw [Reference.OId.injEq] at heq
            rw [heq]
            exact hbridge_mem
          · exact hs1 oid (by
              unfold RuntimeConfig.refs
              exact List.mem_append_left _ (stack_split2 ▸ List.mem_append_right _
                (frame_split ▸ List.mem_append_right _ ((hsub.map (·.2)).mem h1'))))
    · exact hs1 oid (by unfold RuntimeConfig.refs; exact List.mem_append_right _ (heap_refs_perm'.mem_iff.mp h1'))
  exact objectIds_perm.mem_iff.mpr hoid_cfg

theorem merge_HS2 : ValidConfig cfg →
  merge x cfg = some cfg' →
  HS2 cfg' := by
  intro vcfg h
  have l1 := vcfg.l1
  have h2 := vcfg.h2
  have hs2 := vcfg.hs2
  obtain ⟨frame, rid', region, region', hframe, hxref, hregion, hregion', hclosed, hopen, hcfg'⟩ :=
    merge_cases h
  subst hcfg'
  unfold HS2
  dsimp
  have hne := merge_corollary_rid_ne_regionId hregion hregion' hclosed hopen
  have heap_perm' : (Heap.refs ((cfg.heap.erase rid').insert frame.regionId { region with
      objMap := AList.union region.objMap region'.objMap })).Perm cfg.heap.refs :=
    merge_corollary_heap_refs_perm l1 hregion hregion' hne
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
    (List.dropLast_append_getLast? frame hframe).symm
  have stack_split1 : Stack.refs (cfg.stack.dropLast ++
      [{ frame with varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) }]) =
      Stack.refs cfg.stack.dropLast ++ Frame.refs { frame with
        varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) } := by
    unfold Stack.refs
    rw [List.bind_eq_flatMap, List.bind_eq_flatMap, List.flatMap_id, List.flatMap_id,
      List.map_append, List.flatten_append, List.map_singleton, List.flatten_singleton]
  have stack_split2 : Stack.refs cfg.stack = Stack.refs cfg.stack.dropLast ++ Frame.refs frame := by
    conv_lhs => rw [stack_eq]
    unfold Stack.refs
    rw [List.bind_eq_flatMap, List.bind_eq_flatMap, List.flatMap_id, List.flatMap_id,
      List.map_append, List.flatten_append, List.map_singleton, List.flatten_singleton]
  have newFrame_split : Frame.refs { frame with
      varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) } =
      (frame.objMap.entries.map (·.2) >>= Object.refs) ++
        (frame.varMap.insert x (Reference.OId region'.bridgeObjectId)).entries.map (·.2) := by
    unfold Frame.refs; rfl
  have frame_split : Frame.refs frame =
      (frame.objMap.entries.map (·.2) >>= Object.refs) ++ frame.varMap.entries.map (·.2) := by
    unfold Frame.refs; rfl
  -- x's own varMap entry was the unique occurrence of `RId rid'` anywhere in cfg.refs (via H2), so
  -- it no longer appears anywhere in cfg'.refs once that entry is overwritten.
  have hOId_ne : (Reference.OId region'.bridgeObjectId == Reference.RId rid') = false := rfl
  have hcount := merge_corollary_alist_insert_count_eq
    (v_old := Reference.RId rid') (v_new := Reference.OId region'.bridgeObjectId) (t := Reference.RId rid') hxref
  rw [hOId_ne] at hcount
  simp only [beq_self_eq_true, if_true, Bool.false_eq_true, if_false] at hcount
  have newFrame_count_eq : (Frame.refs { frame with
      varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) }).count (Reference.RId rid') + 1 =
      frame.refs.count (Reference.RId rid') := by
    rw [newFrame_split, frame_split, List.count_append, List.count_append]
    omega
  have stack_count_eq : (Stack.refs (cfg.stack.dropLast ++
      [{ frame with varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) }])).count
      (Reference.RId rid') + 1 = cfg.stack.refs.count (Reference.RId rid') := by
    rw [stack_split1, stack_split2, List.count_append, List.count_append]
    omega
  have h2rid' := h2 rid'
  have hzero : (Stack.refs (cfg.stack.dropLast ++
      [{ frame with varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) }])).count
      (Reference.RId rid') +
      (Heap.refs ((cfg.heap.erase rid').insert frame.regionId { region with
        objMap := AList.union region.objMap region'.objMap })).count (Reference.RId rid') = 0 := by
    rw [heap_perm'.count_eq]
    omega
  have hne_ref_zero : ∀ ref, ref = Reference.RId rid' →
      (Stack.refs (cfg.stack.dropLast ++
        [{ frame with varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) }])).count ref +
      (Heap.refs ((cfg.heap.erase rid').insert frame.regionId { region with
        objMap := AList.union region.objMap region'.objMap })).count ref = 0 := by
    intro ref href
    rw [href]
    exact hzero
  intro rid href
  unfold RuntimeConfig.refs at href
  dsimp at href
  by_cases hridrid' : rid = rid'
  · exfalso
    have hcontra := hne_ref_zero (Reference.RId rid) (by rw [hridrid'])
    have hpos : 0 < (Stack.refs (cfg.stack.dropLast ++
        [{ frame with varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) }])).count
        (Reference.RId rid) +
        (Heap.refs ((cfg.heap.erase rid').insert frame.regionId { region with
          objMap := AList.union region.objMap region'.objMap })).count (Reference.RId rid) := by
      rcases List.mem_append.mp href with h1 | h1
      · have := List.count_pos_iff.mpr h1
        omega
      · have := List.count_pos_iff.mpr h1
        omega
    omega
  · -- The stack/heap membership transports back to `cfg.refs` (either literally unchanged, or
    -- via `Perm` for the heap side), so HS2 on `cfg` gives the key, and `rid ≠ rid'` survives the erase.
    have href_cfg : Reference.RId rid ∈ cfg.refs := by
      unfold RuntimeConfig.refs
      rw [List.mem_append] at href ⊢
      rcases href with h1 | h1
      · left
        rw [stack_split1, List.mem_append] at h1
        rw [stack_split2, List.mem_append]
        rcases h1 with h1 | h1
        · exact Or.inl h1
        · right
          rw [newFrame_split, List.mem_append] at h1
          rw [frame_split, List.mem_append]
          rcases h1 with h1 | h1
          · exact Or.inl h1
          · right
            have hsub : List.Sublist (List.kerase x frame.varMap.entries) frame.varMap.entries :=
              List.kerase_sublist x frame.varMap.entries
            have hins := AList.entries_insert (a := x) (b := Reference.OId region'.bridgeObjectId) (s := frame.varMap)
            rw [hins, List.map_cons] at h1
            rcases List.mem_cons.mp h1 with heq | h1
            · exact absurd heq (by rintro ⟨⟩)
            · exact (hsub.map (·.2)).mem h1
      · exact Or.inr (heap_perm'.mem_iff.mp h1)
    have := hs2 rid href_cfg
    have hkey_mem : rid ∈ (cfg.heap.erase rid').keys := (AList.mem_erase).mpr ⟨hridrid', this⟩
    exact (AList.mem_insert _).mpr (Or.inr hkey_mem)

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
