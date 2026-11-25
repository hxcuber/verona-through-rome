module

public import Gc.Model.Types
public import Gc.Model.Helpers
public import Gc.Model.Validity
public import Gc.Model.Theorems
public import Gc.Model.Mutation.Merge
public import Gc.Model.Preservation.Common

public import Mathlib.Data.List.Infix

@[expose] public section

-- `region` (Open) and `region'` (Closed) can't be the same heap entry.
theorem merge_corollary_rid_ne_regionId {cfg : RuntimeConfig} {frame : Frame} {rid' : RegionId}
    {region region' : Region} (hregion : cfg.heap.lookup frame.regionId = some region)
    (hregion' : cfg.heap.lookup rid' = some region')
    (hclosed : region'.status = Status.Closed) (hopen : region.status = Status.Open) :
    rid' ≠ frame.regionId := by
  rintro rfl
  rw [hregion, Option.some_inj] at hregion'
  subst hregion'
  rw [hclosed] at hopen
  cases hopen

-- Two distinct heap entries have disjoint objMap keys (via L1).
theorem merge_corollary_disjoint_keys {cfg : RuntimeConfig} {frame : Frame} {rid' : RegionId}
    {region region' : Region} (l1 : L1 cfg) (hregion : cfg.heap.lookup frame.regionId = some region)
    (hregion' : cfg.heap.lookup rid' = some region') (hne : rid' ≠ frame.regionId) :
    ∀ oid ∈ region.objMap.keys, oid ∉ region'.objMap.keys := fun _ hoid hoid' =>
  hne.symm (heap_region_unique l1 (AList.lookup_mem_entries hregion) hoid (AList.lookup_mem_entries hregion') hoid')

-- With disjoint keys, the merged objMap's entries are a plain append.
theorem merge_corollary_union_append {cfg : RuntimeConfig} {frame : Frame} {rid' : RegionId}
    {region region' : Region} (l1 : L1 cfg) (hregion : cfg.heap.lookup frame.regionId = some region)
    (hregion' : cfg.heap.lookup rid' = some region') (hne : rid' ≠ frame.regionId) :
    (region.objMap ∪ region'.objMap).entries = region.objMap.entries ++ region'.objMap.entries :=
  AList.union_eq_append_of_disjoint_keys (merge_corollary_disjoint_keys l1 hregion hregion' hne)

-- A present entry can be moved to the front of a NodupKeys list, leaving the `kerase` of its key.
private theorem perm_cons_kerase {α : Type*} {β : α → Type*} [DecidableEq α] {l : List (Sigma β)} {a : α}
    {b : β a} (nd : l.NodupKeys) (h : ⟨a, b⟩ ∈ l) : l.Perm (⟨a, b⟩ :: l.kerase a) := by
  obtain ⟨b0, l1, l2, -, rfl, hk⟩ := List.exists_of_kerase (List.mem_keys_of_mem h)
  obtain rfl := nd.eq_of_mk_mem h (List.mem_append_right _ List.mem_cons_self)
  rw [hk]
  exact List.perm_middle

-- `cfg.heap.entries` is `region`, `region'`, then the common tail that the merged heap is built from.
private theorem merge_heap_entries_perm {cfg : RuntimeConfig} {frame : Frame} {rid' : RegionId}
    {region region' : Region} (hregion : cfg.heap.lookup frame.regionId = some region)
    (hregion' : cfg.heap.lookup rid' = some region') (hne : rid' ≠ frame.regionId) :
    cfg.heap.entries.Perm (⟨frame.regionId, region⟩ :: ⟨rid', region'⟩ ::
      List.kerase frame.regionId (List.kerase rid' cfg.heap.entries)) :=
  ((perm_cons_kerase cfg.heap.nodupKeys (AList.lookup_mem_entries hregion')).trans
    ((perm_cons_kerase (cfg.heap.erase rid').nodupKeys
      (AList.lookup_mem_entries ((AList.lookup_erase_ne hne.symm).trans hregion))).cons _)).trans
    (List.Perm.swap _ _ _)

-- Any per-region list that splits over the merged region is permuted by the merge.
private theorem merge_heap_flatten_perm {cfg : RuntimeConfig} {frame : Frame} {rid' : RegionId}
    {region region' : Region} (hregion : cfg.heap.lookup frame.regionId = some region)
    (hregion' : cfg.heap.lookup rid' = some region') (hne : rid' ≠ frame.regionId) {α : Type}
    (f : Region → List α) (hf : f { region with objMap := region.objMap ∪ region'.objMap } = f region ++ f region') :
    (((cfg.heap.erase rid').insert frame.regionId { region with objMap := region.objMap ∪ region'.objMap }).entries.map
      (fun e => f e.2)).flatten.Perm (cfg.heap.entries.map (fun e => f e.2)).flatten := by
  have := ((merge_heap_entries_perm hregion hregion' hne).map (fun e => f e.2)).flatten
  simp only [List.map_cons, List.flatten_cons] at this
  rw [AList.entries_insert, List.map_cons, List.flatten_cons, hf, List.append_assoc]
  exact this.symm

-- Merging only regroups object ids across heap keys.
theorem merge_corollary_heap_objectIds_perm {cfg : RuntimeConfig} {frame : Frame} {rid' : RegionId}
    {region region' : Region} (l1 : L1 cfg) (hregion : cfg.heap.lookup frame.regionId = some region)
    (hregion' : cfg.heap.lookup rid' = some region') (hne : rid' ≠ frame.regionId) :
    (Heap.objectIds ((cfg.heap.erase rid').insert frame.regionId { region with
      objMap := region.objMap ∪ region'.objMap })).Perm cfg.heap.objectIds :=
  merge_heap_flatten_perm hregion hregion' hne Region.objectIds (by
    simp [Region.objectIds, merge_corollary_union_append l1 hregion hregion' hne, List.keys_append])

-- The merged region's refs are exactly `region`'s followed by `region'`'s.
private theorem merge_mergedRegion_refs {cfg : RuntimeConfig} {frame : Frame} {rid' : RegionId}
    {region region' : Region} (l1 : L1 cfg) (hregion : cfg.heap.lookup frame.regionId = some region)
    (hregion' : cfg.heap.lookup rid' = some region') (hne : rid' ≠ frame.regionId) :
    Region.refs { region with objMap := region.objMap.union region'.objMap } = region.refs ++ region'.refs := by
  show Region.refs { region with objMap := region.objMap ∪ region'.objMap } = _
  simp [Region.refs, merge_corollary_union_append l1 hregion hregion' hne]

-- Merging only regroups refs across heap keys.
private theorem merge_heap_refs_perm {cfg : RuntimeConfig} {frame : Frame} {rid' : RegionId}
    {region region' : Region} (l1 : L1 cfg) (hregion : cfg.heap.lookup frame.regionId = some region)
    (hregion' : cfg.heap.lookup rid' = some region') (hne : rid' ≠ frame.regionId) :
    (Heap.refs ((cfg.heap.erase rid').insert frame.regionId { region with
      objMap := region.objMap ∪ region'.objMap })).Perm cfg.heap.refs := by
  simpa [Heap.refs, List.flatMap_def, Function.comp_def] using
    merge_heap_flatten_perm hregion hregion' hne Region.refs (merge_mergedRegion_refs l1 hregion hregion' hne)

-- Lookups in the merged heap: the merge target holds the merged region and `rid'` is gone.
private theorem merge_lookup {heap : Heap} {rid rid' r : RegionId} {m : Region} :
    ((heap.erase rid').insert rid m).lookup r = if r = rid then some m else if r = rid' then none else heap.lookup r := by
  split_ifs with h1 h2
  · subst h1
    exact AList.lookup_insert _
  · subst h2
    rw [AList.lookup_insert_ne h1, AList.lookup_erase]
  · rw [AList.lookup_insert_ne h1, AList.lookup_erase_ne h2]

-- Updating the last frame's varMap keeps the stack's regionIds.
private theorem merge_stack_regionIds {cfg : RuntimeConfig} {frame : Frame} {x : VarName} {v : Reference}
    (hframe : cfg.stack.getLast? = some frame) :
    (cfg.stack.dropLast ++ [{ frame with varMap := frame.varMap.insert x v }]).map Frame.regionId =
      cfg.stack.map Frame.regionId := by
  conv_rhs => rw [← List.dropLast_append_getLast? frame hframe]
  simp

-- Updating the last frame's varMap keeps the stack's objectIds.
private theorem merge_stack_objectIds {cfg : RuntimeConfig} {frame : Frame} {x : VarName} {v : Reference}
    (hframe : cfg.stack.getLast? = some frame) :
    Stack.objectIds (cfg.stack.dropLast ++ [{ frame with varMap := frame.varMap.insert x v }]) =
      Stack.objectIds cfg.stack := by
  conv_rhs => rw [← List.dropLast_append_getLast? frame hframe]
  simp [Stack.objectIds, Frame.objectIds]

-- Merge only regroups object ids.
private theorem merge_objectIds_perm {cfg cfg' : RuntimeConfig} {frame : Frame} {x : VarName} {rid' : RegionId}
    {region region' : Region} (l1 : L1 cfg) (hframe : cfg.stack.getLast? = some frame)
    (hregion : cfg.heap.lookup frame.regionId = some region) (hregion' : cfg.heap.lookup rid' = some region')
    (hne : rid' ≠ frame.regionId)
    (hheap : cfg'.heap = (cfg.heap.erase rid').insert frame.regionId { region with objMap := region.objMap ∪ region'.objMap })
    (hstack : cfg'.stack = cfg.stack.dropLast ++ [{ frame with varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) }]) :
    cfg'.objectIds.Perm cfg.objectIds := by
  unfold RuntimeConfig.objectIds
  rw [hheap, hstack, merge_stack_objectIds hframe]
  exact (merge_corollary_heap_objectIds_perm l1 hregion hregion' hne).append_left _

theorem merge_L1 : ValidConfig cfg →
  merge x cfg = some cfg' →
  L1 cfg' := by
  intro vcfg h
  obtain ⟨frame, rid', region, region', hframe, -, hregion, hregion', hclosed, hopen, rfl⟩ := merge_cases h
  exact (merge_objectIds_perm vcfg.l1 hframe hregion hregion'
    (merge_corollary_rid_ne_regionId hregion hregion' hclosed hopen) rfl rfl).nodup_iff.mpr vcfg.l1

theorem merge_L2 : ValidConfig cfg →
  merge x cfg = some cfg' →
  L2 cfg' := by
  intro vcfg h
  obtain ⟨frame, rid', region, region', hframe, -, hregion, hregion', hclosed, hopen, rfl⟩ := merge_cases h
  intro f hf
  obtain ⟨f0, hf0, hrid⟩ := List.mem_map.mp
    (merge_stack_regionIds hframe ▸ List.mem_map_of_mem (f := Frame.regionId) hf)
  obtain ⟨r0, hl0, ho0⟩ := vcfg.l2 f0 hf0
  dsimp only
  rw [merge_lookup, ← hrid]
  split_ifs with h1 h2
  · exact ⟨_, rfl, hopen⟩
  · rw [h2, hregion', Option.some_inj] at hl0
    subst hl0
    rw [hclosed] at ho0
    cases ho0
  · exact ⟨r0, hl0, ho0⟩

theorem merge_H1 : ValidConfig cfg →
  merge x cfg = some cfg' →
  H1 cfg' := by
  intro vcfg h
  obtain ⟨frame, rid', region, region', hframe, -, hregion, hregion', -, -, rfl⟩ := merge_cases h
  intro r hr
  simp only [Heap.regions, AList.entries_insert, List.map_cons, List.mem_cons] at hr
  rcases hr with rfl | hr
  · exact AList.mem_union.mpr (Or.inl (vcfg.h1 region (List.mem_map_of_mem (AList.lookup_mem_entries hregion))))
  · exact vcfg.h1 r ((((List.kerase_sublist _ _).trans (List.kerase_sublist _ _)).map _).mem hr)

-- Merge only replaces `x`'s `RId rid'` by `OId region'.bridgeObjectId` among all refs.
private theorem merge_refs_count {cfg : RuntimeConfig} {frame : Frame} {x : VarName} {rid' : RegionId}
    {region region' : Region} (l1 : L1 cfg) (hframe : cfg.stack.getLast? = some frame)
    (hxref : frame.varMap.lookup x = some (Reference.RId rid'))
    (hregion : cfg.heap.lookup frame.regionId = some region) (hregion' : cfg.heap.lookup rid' = some region')
    (hne : rid' ≠ frame.regionId) (t : Reference) :
    (Stack.refs (cfg.stack.dropLast ++ [{ frame with varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) }])).count t +
      (Heap.refs ((cfg.heap.erase rid').insert frame.regionId { region with objMap := region.objMap.union region'.objMap })).count t +
      (if (Reference.RId rid' == t) = true then 1 else 0) =
    cfg.stack.refs.count t + cfg.heap.refs.count t + (if (Reference.OId region'.bridgeObjectId == t) = true then 1 else 0) := by
  have hc := alist_insert_count_eq (v_new := Reference.OId region'.bridgeObjectId) (t := t) hxref
  have hp : (Heap.refs ((cfg.heap.erase rid').insert frame.regionId { region with
      objMap := region.objMap.union region'.objMap })).count t = cfg.heap.refs.count t :=
    (merge_heap_refs_perm l1 hregion hregion' hne).count_eq t
  rw [hp]
  conv_rhs => rw [← List.dropLast_append_getLast? frame hframe]
  simp only [Stack.refs, Frame.refs, List.map_append, List.map_singleton, List.bind_eq_flatMap,
    List.flatMap_append, List.flatMap_singleton, id, List.count_append] at hc ⊢
  omega

theorem merge_H2 : ValidConfig cfg →
  merge x cfg = some cfg' →
  H2 cfg' := by
  intro vcfg h
  obtain ⟨frame, rid', region, region', hframe, hxref, hregion, hregion', hclosed, hopen, rfl⟩ := merge_cases h
  intro rid
  have hc := merge_refs_count vcfg.l1 hframe hxref hregion hregion'
    (merge_corollary_rid_ne_regionId hregion hregion' hclosed hopen) (Reference.RId rid)
  have := vcfg.h2 rid
  simp only [beq_iff_eq, reduceCtorEq, ite_false, Nat.add_zero] at hc
  dsimp only
  split_ifs at hc <;> omega

-- Both `stackWithIndex`es share every frame but the last.
private theorem merge_swi_split {cfg cfg' : RuntimeConfig} {frame newFrame : Frame}
    (hframe : cfg.stack.getLast? = some frame) (hstack : cfg'.stack = cfg.stack.dropLast ++ [newFrame]) :
    ∃ D, cfg.stackWithIndex = D ++ [({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex)] ∧
      cfg'.stackWithIndex = D ++ [({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex)] := by
  refine ⟨cfg.stack.dropLast.mapIdx (fun i f => ({ f with index := i } : FrameWithIndex)), ?_, ?_⟩
  · unfold RuntimeConfig.stackWithIndex
    conv_lhs => rw [← List.dropLast_append_getLast? frame hframe]
    rw [List.mapIdx_concat]
  · unfold RuntimeConfig.stackWithIndex
    rw [hstack, List.mapIdx_concat]

-- The stack-side search of `loc?` finds the same index before and after (objMaps are unchanged).
private theorem merge_findRev_index {cfg cfg' : RuntimeConfig} {frame newFrame : Frame}
    (hframe : cfg.stack.getLast? = some frame) (hstack : cfg'.stack = cfg.stack.dropLast ++ [newFrame])
    (hobjeq : newFrame.objMap = frame.objMap) (oid : ObjectId) :
    (cfg'.stackWithIndex.findRev? (fun f => f.objMap.keys.contains oid)).map FrameWithIndex.index =
      (cfg.stackWithIndex.findRev? (fun f => f.objMap.keys.contains oid)).map FrameWithIndex.index := by
  obtain ⟨D, h1, h2⟩ := merge_swi_split hframe hstack
  rw [h1, h2]
  simp only [List.findRev?_eq_find?_reverse, List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.find?_cons, hobjeq]
  cases frame.objMap.keys.contains oid <;> rfl

-- Each frame of the new `stackWithIndex` has an old counterpart, gaining at most the ref `v` in the last frame.
private theorem merge_swi_down {cfg cfg' : RuntimeConfig} {frame : Frame} {x : VarName} {v : Reference}
    (hframe : cfg.stack.getLast? = some frame)
    (hstack : cfg'.stack = cfg.stack.dropLast ++ [{ frame with varMap := frame.varMap.insert x v }])
    {f' : FrameWithIndex} (hf' : f' ∈ cfg'.stackWithIndex) :
    ∃ f ∈ cfg.stackWithIndex, f.index = f'.index ∧ f.regionId = f'.regionId ∧
      ∀ r ∈ f'.refs, r ∈ f.refs ∨ (r = v ∧ f'.regionId = frame.regionId) := by
  obtain ⟨D, h1, h2⟩ := merge_swi_split hframe hstack
  rw [h2, List.mem_append, List.mem_singleton] at hf'
  rcases hf' with hf' | rfl
  · exact ⟨f', h1 ▸ List.mem_append_left _ hf', rfl, rfl, fun r hr => Or.inl hr⟩
  · refine ⟨{ frame with index := cfg.stack.dropLast.length }, h1 ▸ List.mem_append_right _ (List.mem_singleton_self _),
      rfl, rfl, fun r hr => ?_⟩
    rcases frame_varMap_insert_refs_mem (frame := frame) (x := x) (v := v) hr with rfl | hr
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl hr

-- Each frame of the old `stackWithIndex` has a new counterpart with the same index and region.
private theorem merge_swi_up {cfg cfg' : RuntimeConfig} {frame : Frame} {x : VarName} {v : Reference}
    (hframe : cfg.stack.getLast? = some frame)
    (hstack : cfg'.stack = cfg.stack.dropLast ++ [{ frame with varMap := frame.varMap.insert x v }])
    {f : FrameWithIndex} (hf : f ∈ cfg.stackWithIndex) :
    ∃ f' ∈ cfg'.stackWithIndex, f'.index = f.index ∧ f'.regionId = f.regionId := by
  obtain ⟨D, h1, h2⟩ := merge_swi_split hframe hstack
  rw [h1, List.mem_append, List.mem_singleton] at hf
  rcases hf with hf | rfl
  · exact ⟨f, h2 ▸ List.mem_append_left _ hf, rfl, rfl⟩
  · exact ⟨{ frame with varMap := frame.varMap.insert x v, index := cfg.stack.dropLast.length },
      h2 ▸ List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl⟩

-- An oid held by some merged-heap region resolves there, provided the stack side misses it.
theorem merge_corollary_loc_of_mem {cfg : RuntimeConfig} {frame : Frame} {rid' : RegionId}
    {region region' : Region} (l1 : L1 cfg) (hregion : cfg.heap.lookup frame.regionId = some region)
    (hregion' : cfg.heap.lookup rid' = some region') (hne : rid' ≠ frame.regionId)
    {oid : ObjectId} {newFrame : Frame} (hobjeq : newFrame.objMap = frame.objMap)
    (hframe : cfg.stack.getLast? = some frame)
    (hstack_none : cfg.stackWithIndex.findRev? (fun f => f.objMap.keys.contains oid) = none)
    {rid0 : RegionId} {region0 : Region}
    (hlookup0 : ((cfg.heap.erase rid').insert frame.regionId { region with
      objMap := region.objMap ∪ region'.objMap }).lookup rid0 = some region0)
    (hoid0 : oid ∈ region0.objMap.keys) :
    (Reference.OId oid).loc? { cfg with
      stack := cfg.stack.dropLast ++ [newFrame],
      heap := (cfg.heap.erase rid').insert frame.regionId { region with objMap := region.objMap ∪ region'.objMap } } =
    some (Location.Rgn rid0) := by
  have hnd := (merge_corollary_heap_objectIds_perm l1 hregion hregion' hne).nodup_iff.mpr (List.nodup_append.mp l1).2.1
  have hmem := AList.lookup_mem_entries hlookup0
  have hs := merge_findRev_index (cfg' := { cfg with stack := cfg.stack.dropLast ++ [newFrame] }) hframe rfl hobjeq oid
  rw [hstack_none, Option.map_none, Option.map_eq_none_iff] at hs
  simp only [RuntimeConfig.stackWithIndex] at hs
  simp only [Reference.loc?, RuntimeConfig.stackWithIndex]
  rw [hs, List.find?_eq_some_of_unique (p := fun e => e.2.objMap.keys.contains oid) hmem (List.contains_iff_mem.mpr hoid0) fun _ hm hp =>
    List.eq_of_mem_flatten_map_nodup hnd hm hmem (List.contains_iff_mem.mp hp) hoid0]

-- A `Rgn` resolution means the stack side of the search missed.
theorem merge_corollary_loc_rgn_stack_none {cfg : RuntimeConfig} {oid : ObjectId} {rid : RegionId}
    (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn rid)) :
    cfg.stackWithIndex.findRev? (fun f => f.objMap.keys.contains oid) = none := by
  simp only [Reference.loc?] at hloc
  split at hloc <;> simp_all

-- A `Rgn` resolution exhibits the region holding the oid (no validity needed).
private theorem merge_loc_rgn_elim {cfg : RuntimeConfig} {oid : ObjectId} {rid0 : RegionId}
    (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn rid0)) :
    ∃ region0, cfg.heap.lookup rid0 = some region0 ∧ oid ∈ region0.objMap.keys := by
  simp only [Reference.loc?] at hloc
  split at hloc <;> simp at hloc
  rename_i rid1 region1 _ hfind
  subst hloc
  have hp := List.find?_some hfind
  exact ⟨region1, AList.mem_lookup_iff.mpr (List.mem_of_find?_eq_some hfind), List.contains_iff_mem.mp hp⟩

-- The heap side of `loc?` misses exactly when the oid isn't in the heap.
private theorem heap_find_none_iff {heap : Heap} {oid : ObjectId} :
    heap.entries.find? (fun e => e.2.objMap.keys.contains oid) = none ↔ oid ∉ heap.objectIds := by
  simp [List.find?_eq_none, Heap.objectIds, Region.objectIds, List.mem_flatten, AList.keys, Sigma.forall]

-- An oid on the stack after merge was on the stack, at the same index, before.
private theorem merge_loc_stk {cfg : RuntimeConfig} {frame : Frame} {rid' : RegionId}
    {region region' : Region} (l1 : L1 cfg) (hregion : cfg.heap.lookup frame.regionId = some region)
    (hregion' : cfg.heap.lookup rid' = some region') (hne : rid' ≠ frame.regionId)
    (hframe : cfg.stack.getLast? = some frame) {newFrame : Frame} {oid : ObjectId} {fid : Index}
    (h : (Reference.OId oid).loc? { cfg with
      heap := (cfg.heap.erase rid').insert frame.regionId { region with objMap := region.objMap ∪ region'.objMap },
      stack := cfg.stack.dropLast ++ [newFrame] } = some (Location.Stk fid))
    (hobjeq : newFrame.objMap = frame.objMap) :
    (Reference.OId oid).loc? cfg = some (Location.Stk fid) := by
  have hidx := merge_findRev_index (cfg' := { cfg with stack := cfg.stack.dropLast ++ [newFrame] }) hframe rfl hobjeq oid
  have hheap := (merge_corollary_heap_objectIds_perm l1 hregion hregion' hne).mem_iff (a := oid)
  simp only [Reference.loc?] at h ⊢
  split at h <;> simp at h
  rename_i f hf hn
  simp only [RuntimeConfig.stackWithIndex] at hidx hf ⊢
  rw [hf, Option.map_some] at hidx
  obtain ⟨g, hg, hgi⟩ := Option.map_eq_some_iff.mp hidx.symm
  rw [heap_find_none_iff, hheap, ← heap_find_none_iff] at hn
  rw [hg, hn]
  exact congrArg (some ∘ Location.Stk) (hgi.trans h)

theorem merge_H3 : ValidConfig cfg →
  merge x cfg = some cfg' →
  H3 cfg' := by
  intro vcfg h
  obtain ⟨frame, rid', region, region', hframe, -, hregion, hregion', hclosed, hopen, rfl⟩ := merge_cases h
  have hne := merge_corollary_rid_ne_regionId hregion hregion' hclosed hopen
  intro rid oid r0 hl0 href
  obtain ⟨rid1, r1, hl1, href1, hsub⟩ : ∃ rid1 r1, cfg.heap.lookup rid1 = some r1 ∧ Reference.OId oid ∈ r1.refs ∧
      (oid ∈ r1.objMap → oid ∈ r0.objMap) := by
    have hl0' := hl0
    rw [merge_lookup] at hl0'
    split_ifs at hl0' with h1 h2
    · cases hl0'
      rw [merge_mergedRegion_refs vcfg.l1 hregion hregion' hne, List.mem_append] at href
      rcases href with href | href
      · exact ⟨_, _, hregion, href, fun ho => AList.mem_union.mpr (Or.inl ho)⟩
      · exact ⟨_, _, hregion', href, fun ho => AList.mem_union.mpr (Or.inr ho)⟩
    · exact ⟨_, _, hl0', href, id⟩
  have hloc := vcfg.h3 _ _ _ hl1 href1
  obtain ⟨r2, hl2, ho2⟩ := (oid_loc_rgn_iff_in_heap vcfg).mp hloc
  rw [hl1, Option.some_inj] at hl2
  subst hl2
  exact merge_corollary_loc_of_mem vcfg.l1 hregion hregion' hne
    (newFrame := { frame with varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) }) rfl hframe
    (merge_corollary_loc_rgn_stack_none hloc) hl0 (AList.mem_keys.mpr (hsub ho2))

theorem merge_S1 : ValidConfig cfg →
  merge x cfg = some cfg' →
  S1 cfg' := by
  intro vcfg h
  obtain ⟨frame, -, -, -, hframe, -, -, -, -, -, rfl⟩ := merge_cases h
  unfold S1
  dsimp only
  rw [merge_stack_regionIds hframe]
  exact vcfg.s1

theorem merge_S2 : ValidConfig cfg →
  merge x cfg = some cfg' →
  S2 cfg' := by
  intro vcfg h
  obtain ⟨frame, rid', region, region', hframe, -, hregion, hregion', hclosed, hopen, rfl⟩ := merge_cases h
  have hne := merge_corollary_rid_ne_regionId hregion hregion' hclosed hopen
  rintro f' hf' _ href fid' oid rfl hloc
  have hloc0 := merge_loc_stk vcfg.l1 hregion hregion' hne hframe hloc rfl
  obtain ⟨f, hf, hidx, -, hrefs⟩ := merge_swi_down hframe rfl hf'
  rcases hrefs _ href with href | ⟨hb, -⟩
  · exact hidx ▸ vcfg.s2 f hf _ href fid' oid rfl hloc0
  · cases hb
    have := (oid_loc_rgn_iff_in_heap vcfg).mpr
      ⟨region', hregion', vcfg.h1 region' (List.mem_map_of_mem (AList.lookup_mem_entries hregion'))⟩
    rw [hloc0] at this
    cases this

theorem merge_S3 : ValidConfig cfg →
  merge x cfg = some cfg' →
  S3 cfg' := by
  intro vcfg h
  obtain ⟨frame, rid', region, region', hframe, -, hregion, hregion', hclosed, hopen, rfl⟩ := merge_cases h
  rintro f' hf' _ href rid0 oid rfl hloc
  obtain ⟨r0, hl0, ho0⟩ := merge_loc_rgn_elim hloc
  obtain ⟨f, hf, hidx, hrid, hrefs⟩ := merge_swi_down hframe rfl hf'
  rcases hrefs _ href with href | ⟨hb, hrid'⟩
  · obtain ⟨rid1, hloc1, hrid1⟩ : ∃ rid1, (Reference.OId oid).loc? cfg = some (Location.Rgn rid1) ∧
        (rid1 = rid0 ∨ rid1 = rid') := by
      rw [merge_lookup] at hl0
      split_ifs at hl0 with h1 h2
      · cases hl0
        rcases AList.mem_union.mp (AList.mem_keys.mp ho0) with ho | ho
        · exact ⟨_, (oid_loc_rgn_iff_in_heap vcfg).mpr ⟨_, hregion, ho⟩, Or.inl h1.symm⟩
        · exact ⟨_, (oid_loc_rgn_iff_in_heap vcfg).mpr ⟨_, hregion', ho⟩, Or.inr rfl⟩
      · exact ⟨_, (oid_loc_rgn_iff_in_heap vcfg).mpr ⟨_, hl0, AList.mem_keys.mp ho0⟩, Or.inl rfl⟩
    obtain ⟨g, hg, hgrid, hgidx⟩ := vcfg.s3 f hf _ href rid1 oid rfl hloc1
    rcases hrid1 with rfl | rfl
    · obtain ⟨g', hg', hi, hr⟩ := merge_swi_up hframe (hstack := rfl) hg
        (cfg' := { cfg with stack := cfg.stack.dropLast ++ [{ frame with varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) }] })
      exact ⟨g', hg', hr.trans hgrid, hi.trans_le (hgidx.trans_eq hidx)⟩
    · obtain ⟨r2, hl2, ho2⟩ := vcfg.l2 g.toFrame (by
        obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp hg
        exact List.getElem_mem hn)
      rw [hgrid, hregion', Option.some_inj] at hl2
      subst hl2
      rw [hclosed] at ho2
      cases ho2
  · cases hb
    have hfr : frame.regionId = rid0 := heap_region_unique (merge_L1 vcfg h)
      (AList.lookup_mem_entries (AList.lookup_insert _)) (AList.mem_keys.mpr (AList.mem_union.mpr
        (Or.inr (vcfg.h1 region' (List.mem_map_of_mem (AList.lookup_mem_entries hregion'))))))
      (AList.lookup_mem_entries hl0) ho0
    exact ⟨f', hf', hrid'.trans hfr, le_refl _⟩

theorem merge_HS1 : ValidConfig cfg →
  merge x cfg = some cfg' →
  HS1 cfg' := by
  intro vcfg h
  obtain ⟨frame, rid', region, region', hframe, hxref, hregion, hregion', hclosed, hopen, rfl⟩ := merge_cases h
  have hne := merge_corollary_rid_ne_regionId hregion hregion' hclosed hopen
  intro oid href
  refine (merge_objectIds_perm vcfg.l1 hframe hregion hregion' hne rfl rfl).mem_iff.mpr ?_
  by_cases hb : region'.bridgeObjectId = oid
  · subst hb
    exact List.mem_append_right _ (heap_objectIds_of_mem (AList.lookup_mem_entries hregion')
      (AList.mem_keys.mpr (vcfg.h1 region' (List.mem_map_of_mem (AList.lookup_mem_entries hregion')))))
  · have hc := merge_refs_count vcfg.l1 hframe hxref hregion hregion' hne (Reference.OId oid)
    have hpos := List.count_pos_iff.mpr href
    simp only [beq_iff_eq, reduceCtorEq, Reference.OId.injEq, hb, ite_false, Nat.add_zero] at hc
    simp only [RuntimeConfig.refs, List.count_append] at hpos
    exact vcfg.hs1 oid (List.count_pos_iff.mp (by simp only [RuntimeConfig.refs, List.count_append]; omega))

theorem merge_HS2 : ValidConfig cfg →
  merge x cfg = some cfg' →
  HS2 cfg' := by
  intro vcfg h
  obtain ⟨frame, rid', region, region', hframe, hxref, hregion, hregion', hclosed, hopen, rfl⟩ := merge_cases h
  have hne := merge_corollary_rid_ne_regionId hregion hregion' hclosed hopen
  intro rid href
  have hc := merge_refs_count vcfg.l1 hframe hxref hregion hregion' hne (Reference.RId rid)
  have hpos := List.count_pos_iff.mpr href
  have h2 := vcfg.h2 rid
  simp only [beq_iff_eq, reduceCtorEq, Reference.RId.injEq, ite_false, Nat.add_zero] at hc
  simp only [RuntimeConfig.refs, List.count_append] at hpos
  split_ifs at hc with hr
  · omega
  · have := vcfg.hs2 rid (List.count_pos_iff.mp (by simp only [RuntimeConfig.refs, List.count_append]; omega))
    exact (AList.mem_insert _).mpr (Or.inr (AList.mem_erase.mpr ⟨Ne.symm hr, this⟩))

theorem merge_valid : ValidConfig cfg →
  merge x cfg = some cfg' →
  ValidConfig cfg' := fun vcfg h =>
  ⟨merge_L1 vcfg h, merge_L2 vcfg h, merge_H1 vcfg h, merge_H2 vcfg h, merge_H3 vcfg h, merge_S1 vcfg h,
    merge_S2 vcfg h, merge_S3 vcfg h, merge_HS1 vcfg h, merge_HS2 vcfg h⟩
