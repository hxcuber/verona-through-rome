module

public import Gc.Model.Mutation.Exit
public import Gc.Model.Preservation.Common

@[expose] public section

-- The last frame's objectIds split off the end of the stack's.
private theorem stack_objectIds_of_getLast? {stack : Stack} {frame : Frame} (hlast : stack.getLast? = some frame) :
    Stack.objectIds stack = Stack.objectIds stack.dropLast ++ frame.objMap.keys := by
  conv_lhs => rw [← List.dropLast_append_getLast? frame hlast]
  simp [Stack.objectIds, Frame.objectIds]

-- Dropping the last frame only shrinks a per-frame flattened list.
private theorem dropLast_bind_sublist {α : Type} (s : List Frame) (f : Frame → List α) :
    (s.dropLast.map f >>= id).Sublist (s.map f >>= id) := by
  simpa using ((List.dropLast_sublist s).map f).flatten_sublist

-- `exit` preserves every location, except that an oid in the popped frame loses its location.
theorem exit_loc {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg) (h : exit cfg = some cfg') (ref : Reference) :
    ref.loc? cfg' = ref.loc? cfg ∨ (ref.loc? cfg' = none ∧ ∃ fid, ref.loc? cfg = some (Location.Stk fid)) := by
  obtain ⟨frame', region', -, hlast, hlookup, -, hcfg'⟩ := exit_cases h
  have hheap : cfg'.heap = cfg.heap.insert frame'.regionId { region' with status := Status.Closed } := by
    rw [hcfg']
  cases ref with
  | RId r =>
    left
    have := heap_insert_keys_mem (newRegion := { region' with status := Status.Closed })
      (AList.mem_keys_of_lookup_eq_some hlookup) r
    simp only [Reference.loc?, hheap, List.contains_iff_mem, this]
  | OId oid =>
    have hswi' : cfg'.stackWithIndex =
        cfg.stack.dropLast.mapIdx (fun i f => ({ f with index := i } : FrameWithIndex)) := by
      rw [hcfg']; rfl
    have hS : cfg.stackWithIndex.findRev? (fun f => f.objMap.keys.contains oid) =
        if frame'.objMap.keys.contains oid then some { frame' with index := cfg.stack.dropLast.length }
        else cfg'.stackWithIndex.findRev? (fun f => f.objMap.keys.contains oid) := by
      have swi : cfg.stackWithIndex = cfg.stack.dropLast.mapIdx (fun i f => ({ f with index := i } : FrameWithIndex)) ++
          [{ frame' with index := cfg.stack.dropLast.length }] := by
        unfold RuntimeConfig.stackWithIndex
        conv_lhs => rw [← List.dropLast_append_getLast? frame' hlast]
        rw [List.mapIdx_concat]
      rw [swi, hswi']
      simp only [List.findRev?_eq_find?_reverse, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.find?_cons]
      cases frame'.objMap.keys.contains oid <;> rfl
    have hfst := heap_status_update_find_fst (s := Status.Closed) (oid := oid) vcfg.l1 hlookup
    rw [← hheap] at hfst
    by_cases hc : frame'.objMap.keys.contains oid
    · rw [ite_eq_left hc] at hS
      have hH := oid_in_stack_implies_not_in_heap vcfg hS
      rw [hH, Option.map_none, Option.map_eq_none_iff] at hfst
      have hS' : cfg'.stackWithIndex.findRev? (fun f => f.objMap.keys.contains oid) = none := by
        rw [hswi', List.findRev?_eq_find?_reverse, List.find?_eq_none]
        rintro _ hx hpx
        obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp (List.mem_reverse.mp hx)
        have hnd := (List.nodup_append.mp vcfg.l1).1
        rw [stack_objectIds_of_getLast? hlast, List.nodup_append] at hnd
        exact hnd.2.2 oid (List.mem_flatMap.mpr ⟨_, List.mem_map_of_mem (List.getElem_mem hn),
          List.contains_iff_mem.mp hpx⟩) oid (List.contains_iff_mem.mp hc) rfl
      right
      simp only [Reference.loc?]
      rw [hS, hH, hS', hfst]
      exact ⟨rfl, _, rfl⟩
    · rw [ite_eq_right hc] at hS
      left
      simp only [Reference.loc?]
      rw [hS]
      refine (loc_match_eq _ _).trans ?_
      rw [hfst]
      exact (loc_match_eq _ _).symm

theorem exit_corollary_1 :
  ValidConfig cfg →
  exit cfg = some cfg' →
  ∀ (ref : Reference), ref.loc? cfg = Location.Rgn rid ↔ ref.loc? cfg' = Location.Rgn rid := by
  intro vcfg h ref
  rcases exit_loc vcfg h ref with heq | ⟨hnone, fid, hstk⟩
  · rw [heq]
  · simp [hnone, hstk]

theorem exit_corollary_3 :
  ValidConfig cfg →
  exit cfg = some cfg' →
  ∀ (ref : Reference), ref.loc? cfg' = Location.Stk fid → ref.loc? cfg = Location.Stk fid := by
  intro vcfg h ref hloc
  rcases exit_loc vcfg h ref with heq | ⟨hnone, -⟩
  · rwa [← heq]
  · simp [hnone] at hloc

-- Every reference stored after `exit` was already stored before it.
theorem exit_refs_mem (h : exit cfg = some cfg') {r : Reference} (hr : r ∈ cfg'.refs) : r ∈ cfg.refs := by
  obtain ⟨frame', region', -, -, hlookup, -, rfl⟩ := exit_cases h
  rcases List.mem_append.mp hr with hs | hh
  · exact List.mem_append_left _ ((dropLast_bind_sublist cfg.stack Frame.refs).subset hs)
  · exact List.mem_append_right _ ((heap_insert_refs_perm (newRegion := { region' with status := Status.Closed })
      hlookup rfl).subset hh)

theorem exit_H1 : ValidConfig cfg →
  exit cfg = some cfg' →
  H1 cfg' := by
  intro vcfg h region hregion
  obtain ⟨frame', region', -, -, hlookup, -, rfl⟩ := exit_cases h
  simp only [Heap.regions, AList.entries_insert, List.map_cons, List.mem_cons] at hregion
  rcases hregion with rfl | hregion
  · exact vcfg.h1 region' (List.mem_map_of_mem (AList.lookup_mem_entries hlookup))
  · exact vcfg.h1 region (((List.kerase_sublist _ _).map _).subset hregion)

theorem exit_L1 : ValidConfig cfg →
  exit cfg = some cfg' →
  L1 cfg' := by
  intro vcfg h
  obtain ⟨frame', region', -, -, hlookup, -, rfl⟩ := exit_cases h
  have hperm := heap_insert_objectIds_perm (newRegion := { region' with status := Status.Closed }) hlookup
    (List.Perm.refl _)
  exact ((hperm.append_left _).nodup_iff.mpr vcfg.l1).sublist
    ((dropLast_bind_sublist cfg.stack Frame.objectIds).append_right _)

theorem exit_H2 : ValidConfig cfg →
  exit cfg = some cfg' →
  H2 cfg' := by
  intro vcfg h rid
  obtain ⟨frame', region', -, -, hlookup, -, rfl⟩ := exit_cases h
  have hs := (dropLast_bind_sublist cfg.stack Frame.refs).count_le (a := Reference.RId rid)
  have hh := (heap_insert_refs_perm (newRegion := { region' with status := Status.Closed }) hlookup rfl).count_eq
    (Reference.RId rid)
  exact (Nat.add_le_add hs hh.le).trans (vcfg.h2 rid)

theorem exit_H3 : ValidConfig cfg →
  exit cfg = some cfg' →
  H3 cfg' := by
  intro vcfg h rid oid region hregion hoid
  obtain ⟨frame', region', -, -, hlookup, -, rfl⟩ := exit_cases h
  obtain ⟨reg0, hm0, he⟩ := (heap_status_update_entries_mem_iff hlookup rid region.objMap).mp
    ⟨region, AList.mem_lookup_iff.mp hregion, rfl⟩
  refine (exit_corollary_1 vcfg h _).mp (vcfg.h3 rid oid reg0 (AList.mem_lookup_iff.mpr hm0) ?_)
  unfold Region.refs at hoid ⊢
  rwa [he]

theorem exit_L2 : ValidConfig cfg →
  exit cfg = some cfg' →
  L2 cfg' := by
  intro vcfg h frame hframe
  obtain ⟨frame', region', -, hlast, hlookup, -, rfl⟩ := exit_cases h
  have hs1 := vcfg.s1
  rw [S1, ← List.dropLast_append_getLast? frame' hlast, List.map_append, List.nodup_append] at hs1
  have hne : frame.regionId ≠ frame'.regionId :=
    hs1.2.2 _ (List.mem_map_of_mem hframe) _ (List.mem_map_of_mem (List.mem_singleton_self frame'))
  dsimp only
  rw [AList.lookup_insert_ne hne]
  exact vcfg.l2 frame (List.mem_of_mem_dropLast hframe)

theorem exit_S1 : ValidConfig cfg →
  exit cfg = some cfg' →
  S1 cfg' := by
  intro vcfg h
  obtain ⟨frame', region', -, -, -, -, rfl⟩ := exit_cases h
  exact vcfg.s1.sublist ((List.dropLast_sublist _).map _)

theorem exit_S2 : ValidConfig cfg →
  exit cfg = some cfg' →
  S2 cfg' := by
  intro vcfg h frame hframe ref href fid oid heq hloc
  obtain ⟨frame', region', -, -, -, -, rfl⟩ := exit_cases h
  exact vcfg.s2 frame (List.mem_of_mem_dropLast_mapIdx hframe) ref href fid oid heq
    (exit_corollary_3 vcfg h ref hloc)

theorem exit_S3 : ValidConfig cfg →
  exit cfg = some cfg' →
  S3 cfg' := by
  intro vcfg h frame hframe ref href rid oid heq hloc
  obtain ⟨frame', region', -, -, -, -, rfl⟩ := exit_cases h
  obtain ⟨f'', hf'', hrid, hidx⟩ := vcfg.s3 frame (List.mem_of_mem_dropLast_mapIdx hframe) ref href rid oid heq
    ((exit_corollary_1 vcfg h ref).mpr hloc)
  refine ⟨f'', ?_, hrid, hidx⟩
  obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp hframe
  obtain ⟨k, hk, rfl⟩ := List.mem_mapIdx.mp hf''
  exact List.mem_mapIdx.mpr ⟨k, lt_of_le_of_lt hidx hn, by simp [List.getElem_dropLast]⟩

theorem exit_HS1 : ValidConfig cfg →
  exit cfg = some cfg' →
  HS1 cfg' := by
  intro vcfg h oid hmem
  have hold := vcfg.hs1 oid (exit_refs_mem h hmem)
  obtain ⟨frame', region', -, hlast, hlookup, -, rfl⟩ := exit_cases h
  rw [RuntimeConfig.objectIds, stack_objectIds_of_getLast? hlast, List.mem_append, List.mem_append] at hold
  rcases hold with (hd | hf) | hh
  · exact List.mem_append_left _ hd
  · exfalso
    have hidx : cfg.stack[cfg.stack.dropLast.length]? = some frame' := by
      rw [List.length_dropLast, ← List.getLast?_eq_getElem?, hlast]
    have loc_eq : (Reference.OId oid).loc? cfg = some (.Stk cfg.stack.dropLast.length) :=
      (oid_loc_stk_iff_in_stack vcfg).mpr ⟨{ frame' with index := cfg.stack.dropLast.length },
        by rw [RuntimeConfig.stackWithIndex, List.getElem?_mapIdx, hidx]; rfl, AList.mem_keys.mp hf⟩
    rcases List.mem_append.mp hmem with hs | hh
    · simp only [Stack.refs, List.bind_eq_flatMap, List.flatMap_id, List.mem_flatten, List.mem_map] at hs
      obtain ⟨_, ⟨f, hfmem, rfl⟩, hoidf⟩ := hs
      obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hfmem
      exact Nat.not_le.mpr hn (vcfg.s2 ⟨cfg.stack.dropLast[n], n⟩
        (List.mem_of_mem_dropLast_mapIdx (List.mem_mapIdx.mpr ⟨n, hn, rfl⟩)) _ hoidf _ oid rfl loc_eq)
    · have hh' := (heap_insert_refs_perm (newRegion := { region' with status := Status.Closed }) hlookup rfl).subset hh
      simp only [Heap.refs, List.bind_eq_flatMap, List.mem_flatMap, List.mem_map] at hh'
      obtain ⟨_, ⟨⟨rid, reg⟩, hm, rfl⟩, hoid⟩ := hh'
      simpa [loc_eq] using vcfg.h3 rid oid reg (AList.mem_lookup_iff.mpr hm) hoid
  · exact List.mem_append_right _ ((heap_insert_objectIds_perm (newRegion := { region' with status := Status.Closed })
      hlookup (List.Perm.refl _)).symm.subset hh)

theorem exit_HS2 : ValidConfig cfg →
  exit cfg = some cfg' →
  HS2 cfg' := by
  intro vcfg h rid hmem
  have hold := vcfg.hs2 rid (exit_refs_mem h hmem)
  obtain ⟨frame', region', -, -, hlookup, -, rfl⟩ := exit_cases h
  exact (heap_insert_keys_mem (AList.mem_keys_of_lookup_eq_some hlookup) rid).mpr hold

theorem exit_valid : ValidConfig cfg → exit cfg = some cfg' → ValidConfig cfg' := by
  intro vcfg h
  exact {
    l1 := exit_L1 vcfg h,
    l2 := exit_L2 vcfg h,
    h1 := exit_H1 vcfg h,
    h2 := exit_H2 vcfg h,
    h3 := exit_H3 vcfg h,
    s1 := exit_S1 vcfg h,
    s2 := exit_S2 vcfg h,
    s3 := exit_S3 vcfg h,
    hs1 := exit_HS1 vcfg h,
    hs2 := exit_HS2 vcfg h
  }
