module

public import Gc.Model.Mutation.Enter
public import Gc.Model.Preservation.Common

@[expose] public section

-- `enter` preserves every location.
private theorem enter_loc (vcfg : ValidConfig cfg) (h : enter xf a cfg = some cfg') (ref : Reference) :
    ref.loc? cfg' = ref.loc? cfg := by
  obtain ⟨rid, region, -, hlookup, -, rfl⟩ := enter_cases h
  cases ref with
  | RId r =>
    have := heap_insert_keys_mem (newRegion := { region with status := Status.Open })
      (AList.mem_keys_of_lookup_eq_some hlookup) r
    simp only [Reference.loc?, List.contains_iff_mem, this]
  | OId oid =>
    simp only [Reference.loc?, RuntimeConfig.stackWithIndex, List.mapIdx_concat, List.findRev?_eq_find?_reverse,
      List.reverse_append, List.reverse_singleton, List.singleton_append, List.find?_cons, AList.keys_empty,
      List.contains_nil]
    refine (loc_match_eq _ _).trans ?_
    rw [heap_status_update_find_fst (s := Status.Open) vcfg.l1 hlookup]
    exact (loc_match_eq _ _).symm

theorem enter_corollary_2 : ValidConfig cfg →
  enter xf a cfg = some cfg' →
  ∀ oid, (Reference.OId oid).loc? cfg = (Reference.OId oid).loc? cfg' :=
  fun vcfg h _ => (enter_loc vcfg h _).symm

-- The pushed frame is empty, so the stack's refs are unchanged.
private theorem enter_stack_refs (h : enter xf a cfg = some cfg') : cfg'.stack.refs = cfg.stack.refs := by
  obtain ⟨rid, region, -, -, -, rfl⟩ := enter_cases h
  simp [Stack.refs, Frame.refs]

private theorem enter_heap_refs_perm (h : enter xf a cfg = some cfg') : cfg'.heap.refs.Perm cfg.heap.refs := by
  obtain ⟨rid, region, -, hlookup, -, rfl⟩ := enter_cases h
  exact heap_insert_refs_perm (newRegion := { region with status := Status.Open }) hlookup rfl

private theorem enter_refs_mem (h : enter xf a cfg = some cfg') {r : Reference} (hr : r ∈ cfg'.refs) :
    r ∈ cfg.refs := by
  rw [RuntimeConfig.refs, enter_stack_refs h] at hr
  exact ((enter_heap_refs_perm h).append_left _).subset hr

private theorem enter_objectIds_perm (h : enter xf a cfg = some cfg') : cfg'.objectIds.Perm cfg.objectIds := by
  obtain ⟨rid, region, -, hlookup, -, rfl⟩ := enter_cases h
  have hs : Stack.objectIds (cfg.stack ++ [{ regionId := rid, bridgeVar := a, objMap := ∅, varMap := ∅ }]) =
      Stack.objectIds cfg.stack := by simp [Stack.objectIds, Frame.objectIds]
  rw [RuntimeConfig.objectIds, RuntimeConfig.objectIds]
  dsimp only
  rw [hs]
  exact (heap_insert_objectIds_perm (newRegion := { region with status := Status.Open }) hlookup
    (List.Perm.refl _)).append_left _

-- `enter` appends one ref-less frame to `stackWithIndex`.
private theorem enter_swi (h : enter xf a cfg = some cfg') :
    ∃ f : FrameWithIndex, cfg'.stackWithIndex = cfg.stackWithIndex ++ [f] ∧ f.refs = [] := by
  obtain ⟨rid, region, -, -, -, rfl⟩ := enter_cases h
  exact ⟨_, List.mapIdx_concat .., by simp [Frame.refs]⟩

-- L2: an on-stack frame's region is Open, so it is not the Closed region `enter` opens.
private theorem regionId_ne (vcfg : ValidConfig cfg) {frame : Frame} (hframe : frame ∈ cfg.stack)
    (hlookup : cfg.heap.lookup rid = some region) (hclosed : region.status = Status.Closed) :
    frame.regionId ≠ rid := by
  rintro rfl
  obtain ⟨r, hr, ho⟩ := vcfg.l2 frame hframe
  rw [hlookup, Option.some_inj] at hr
  subst hr
  rw [hclosed] at ho
  cases ho

theorem enter_L1 : ValidConfig cfg →
  enter xf a cfg = some cfg' →
  L1 cfg' := fun vcfg h => (enter_objectIds_perm h).nodup_iff.mpr vcfg.l1

theorem enter_L2 : ValidConfig cfg →
  enter xf a cfg = some cfg' →
  L2 cfg' := by
  intro vcfg h frame hframe
  obtain ⟨rid, region, -, hlookup, hclosed, rfl⟩ := enter_cases h
  rcases List.mem_append.mp hframe with hf | hf
  · obtain ⟨r, hr, ho⟩ := vcfg.l2 frame hf
    exact ⟨r, (AList.lookup_insert_ne (regionId_ne vcfg hf hlookup hclosed)).trans hr, ho⟩
  · rw [List.mem_singleton.mp hf]
    exact ⟨_, AList.lookup_insert _, rfl⟩

theorem enter_H1 : ValidConfig cfg →
  enter xf a cfg = some cfg' →
  H1 cfg' := by
  intro vcfg h region hregion
  obtain ⟨rid, region', -, hlookup, -, rfl⟩ := enter_cases h
  simp only [Heap.regions, AList.entries_insert, List.map_cons, List.mem_cons] at hregion
  rcases hregion with rfl | hregion
  · exact vcfg.h1 region' (List.mem_map_of_mem (AList.lookup_mem_entries hlookup))
  · exact vcfg.h1 region (((List.kerase_sublist _ _).map _).subset hregion)

theorem enter_H2 : ValidConfig cfg →
  enter xf a cfg = some cfg' →
  H2 cfg' := by
  intro vcfg h rid
  rw [enter_stack_refs h, (enter_heap_refs_perm h).count_eq]
  exact vcfg.h2 rid

theorem enter_H3 : ValidConfig cfg →
  enter xf a cfg = some cfg' →
  H3 cfg' := by
  intro vcfg h rid oid region hregion hoid
  rw [enter_loc vcfg h]
  obtain ⟨rid0, region0, -, hlookup, -, rfl⟩ := enter_cases h
  by_cases hr : rid = rid0
  · subst hr
    obtain rfl := Option.some_inj.mp ((AList.lookup_insert _).symm.trans hregion)
    exact vcfg.h3 rid oid region0 hlookup hoid
  · exact vcfg.h3 rid oid region ((AList.lookup_insert_ne hr).symm.trans hregion) hoid

theorem enter_S1 : ValidConfig cfg →
  enter xf a cfg = some cfg' →
  S1 cfg' := by
  intro vcfg h
  obtain ⟨rid, region, -, hlookup, hclosed, rfl⟩ := enter_cases h
  simp only [S1, List.map_append, List.map_singleton, List.nodup_append, List.nodup_singleton, List.mem_singleton,
    List.mem_map]
  refine ⟨vcfg.s1, trivial, ?_⟩
  rintro _ ⟨frame, hf, rfl⟩ _ rfl
  exact regionId_ne vcfg hf hlookup hclosed

theorem enter_S2 : ValidConfig cfg →
  enter xf a cfg = some cfg' →
  S2 cfg' := by
  intro vcfg h frame hframe ref href fid oid heq hloc
  obtain ⟨f, hswi, hf⟩ := enter_swi h
  rw [hswi, List.mem_append, List.mem_singleton] at hframe
  rcases hframe with hframe | rfl
  · exact vcfg.s2 frame hframe ref href fid oid heq (enter_loc vcfg h ref ▸ hloc)
  · simp [hf] at href

theorem enter_S3 : ValidConfig cfg →
  enter xf a cfg = some cfg' →
  S3 cfg' := by
  intro vcfg h frame hframe ref href rid oid heq hloc
  obtain ⟨f, hswi, hf⟩ := enter_swi h
  rw [hswi, List.mem_append, List.mem_singleton] at hframe
  rcases hframe with hframe | rfl
  · obtain ⟨f', hf', hrid, hidx⟩ := vcfg.s3 frame hframe ref href rid oid heq (enter_loc vcfg h ref ▸ hloc)
    exact ⟨f', hswi ▸ List.mem_append_left _ hf', hrid, hidx⟩
  · simp [hf] at href

theorem enter_HS1 : ValidConfig cfg →
  enter xf a cfg = some cfg' →
  HS1 cfg' := fun vcfg h oid hmem =>
  (enter_objectIds_perm h).symm.subset (vcfg.hs1 oid (enter_refs_mem h hmem))

theorem enter_HS2 : ValidConfig cfg →
  enter xf a cfg = some cfg' →
  HS2 cfg' := by
  intro vcfg h rid hmem
  have hold := vcfg.hs2 rid (enter_refs_mem h hmem)
  obtain ⟨rid0, region, -, hlookup, -, rfl⟩ := enter_cases h
  exact (heap_insert_keys_mem (AList.mem_keys_of_lookup_eq_some hlookup) rid).mpr hold

theorem enter_valid : ValidConfig cfg →
  enter xf a cfg = some cfg' →
  ValidConfig cfg' := by
  intro vcfg h
  exact {
    l1 := enter_L1 vcfg h,
    l2 := enter_L2 vcfg h,
    h1 := enter_H1 vcfg h,
    h2 := enter_H2 vcfg h,
    h3 := enter_H3 vcfg h,
    s1 := enter_S1 vcfg h,
    s2 := enter_S2 vcfg h,
    s3 := enter_S3 vcfg h,
    hs1 := enter_HS1 vcfg h,
    hs2 := enter_HS2 vcfg h
  }
