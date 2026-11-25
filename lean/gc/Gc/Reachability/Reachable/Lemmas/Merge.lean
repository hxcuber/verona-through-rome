module

public import Gc.Reachability.Reachable.Lemmas.Common

@[expose] public section

-- In a valid config, `objAt?` finds `obj` iff some stack frame or heap region maps `oid` to it.
private theorem objAt_eq_some_iff {cfg : RuntimeConfig} (vcfg : ValidConfig cfg) {oid : ObjectId} {obj : Object} :
    (Reference.OId oid).objAt? cfg = some obj ↔
      (∃ f ∈ cfg.stackWithIndex, f.objMap.lookup oid = some obj) ∨
      ∃ rid region, cfg.heap.lookup rid = some region ∧ region.objMap.lookup oid = some obj := by
  constructor
  · intro h
    simp only [Reference.objAt?] at h
    split at h
    · obtain ⟨region, hlk, hobj⟩ := Option.bind_eq_some_iff.mp h
      exact .inr ⟨_, region, hlk, hobj⟩
    · obtain ⟨f, hfind, hobj⟩ := Option.bind_eq_some_iff.mp h
      exact .inl ⟨f, List.mem_of_find?_eq_some hfind, hobj⟩
    · simp at h
  · rintro (⟨f, hf, hobj⟩ | ⟨rid, region, hlk, hobj⟩)
    · have hloc := (oid_loc_stk_iff_in_stack vcfg).mpr
        ⟨f, stackWithIndex_mem_getElem_eq hf, AList.lookup_isSome.mp (Option.isSome_of_eq_some hobj)⟩
      simp [Reference.objAt?, hloc, stackWithIndex_find_index_eq_getElem, stackWithIndex_mem_getElem_eq hf, hobj]
    · have hloc := (oid_loc_rgn_iff_in_heap vcfg).mpr ⟨region, hlk, AList.lookup_isSome.mp (Option.isSome_of_eq_some hobj)⟩
      simp [Reference.objAt?, hloc, hlk, hobj]

-- Every frame's `objMap` is unaffected by merge (only the last frame's `varMap` changes).
private theorem merge_corollary_objMap_get_eq {cfg cfg' : RuntimeConfig} {x : VarName}
    (h : merge x cfg = some cfg') (n : ℕ) :
    (cfg.stack[n]?).map Frame.objMap = (cfg'.stack[n]?).map Frame.objMap := by
  obtain ⟨frame, -, -, -, hframe, -, -, -, -, -, rfl⟩ := merge_cases h
  exact stackWithIndex_objMap_get_eq_of_last_varMap_update hframe rfl n

-- `objAt?` is unconditionally preserved by merge (only relocates heap entries, never edits content).
private theorem merge_objAt_eq (vcfg : ValidConfig cfg) {x : VarName} {cfg' : RuntimeConfig}
    (h : merge x cfg = some cfg') (oid : ObjectId) :
    (Reference.OId oid).objAt? cfg = (Reference.OId oid).objAt? cfg' := by
  have hs := merge_corollary_objMap_get_eq h
  have vcfg' := merge_valid vcfg h
  ext obj
  rw [objAt_eq_some_iff vcfg, objAt_eq_some_iff vcfg']
  obtain ⟨frame, rid', region, region', hframe, -, hregion, hregion', hclosed, hopen, rfl⟩ := merge_cases h
  have hne := merge_corollary_rid_ne_regionId hregion hregion' hclosed hopen
  have hdisj := merge_corollary_disjoint_keys vcfg.l1 hregion hregion' hne
  refine or_congr ⟨fun ⟨f, hf, hobj⟩ => ?_, fun ⟨f, hf, hobj⟩ => ?_⟩ ⟨fun ⟨rid, r, hlk, hobj⟩ => ?_, fun ⟨rid, r, hlk, hobj⟩ => ?_⟩
  · obtain ⟨f0, hf0, -, heq⟩ := stackWithIndex_frame_transport_up_of_shape_eq hs f hf
    exact ⟨f0, hf0, by simpa [heq] using hobj⟩
  · obtain ⟨f0, hf0, -, heq⟩ := stackWithIndex_frame_transport_down_of_shape_eq hs f hf
    exact ⟨f0, hf0, by simpa [heq] using hobj⟩
  · have hmem : oid ∈ r.objMap := AList.lookup_isSome.mp (Option.isSome_of_eq_some hobj)
    by_cases h1 : rid = frame.regionId
    · subst h1
      rw [hregion, Option.some_inj] at hlk
      subst hlk
      exact ⟨_, _, AList.lookup_insert _, (AList.lookup_union_left hmem).trans hobj⟩
    by_cases h2 : rid = rid'
    · subst h2
      rw [hregion', Option.some_inj] at hlk
      subst hlk
      exact ⟨_, _, AList.lookup_insert _, (AList.lookup_union_right fun hc =>
        hdisj oid (AList.mem_keys.mpr hc) (AList.mem_keys.mpr hmem)).trans hobj⟩
    · exact ⟨rid, r, by rw [AList.lookup_insert_ne h1, AList.lookup_erase_ne h2]; exact hlk, hobj⟩
  · by_cases h1 : rid = frame.regionId
    · subst h1
      rw [AList.lookup_insert, Option.some_inj] at hlk
      subst hlk
      rcases AList.mem_lookup_union.mp hobj with hobj | ⟨-, hobj⟩
      · exact ⟨_, _, hregion, hobj⟩
      · exact ⟨_, _, hregion', hobj⟩
    · rw [AList.lookup_insert_ne h1] at hlk
      by_cases h2 : rid = rid'
      · rw [h2, AList.lookup_erase] at hlk
        cases hlk
      · exact ⟨rid, r, by rwa [AList.lookup_erase_ne h2] at hlk, hobj⟩

-- Every `ReachableStep` not sourced at `RId rid'` is preserved by merge (`objAt?` is unchanged, the active region stays Open).
private theorem merge_step_iff_of_ne {cfg cfg' : RuntimeConfig} {x : VarName} (vcfg : ValidConfig cfg)
    (h : merge x cfg = some cfg') {frame : Frame} {rid' : RegionId} {region region' : Region}
    (hregion : cfg.heap.lookup frame.regionId = some region) (hopen : region.status = Status.Open)
    (hcfg' : cfg' = { cfg with
      heap := (cfg.heap.erase rid').insert frame.regionId { region with objMap := region.objMap ∪ region'.objMap },
      stack := cfg.stack.dropLast ++
        [{ frame with varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) }] })
    {a : Reference} (hane : a ≠ Reference.RId rid') (b : Reference) :
    ReachableStep cfg a b ↔ ReachableStep cfg' a b := by
  cases a with
  | OId oid => rw [ReachableStep_oid_iff, ReachableStep_oid_iff, merge_objAt_eq vcfg h oid]
  | RId rid =>
    by_cases heq : rid = frame.regionId
    · subst heq
      have hlookup' : cfg'.heap.lookup frame.regionId =
          some { region with objMap := region.objMap ∪ region'.objMap } := by
        rw [hcfg']
        exact AList.lookup_insert _
      exact iff_of_false (open_rid_no_step hregion hopen) (open_rid_no_step hlookup' hopen)
    · have hne : rid ≠ rid' := fun hc => hane (hc ▸ rfl)
      rw [ReachableStep_rid_iff, ReachableStep_rid_iff, hcfg']
      simp only [AList.lookup_insert_ne heq, AList.lookup_erase_ne hne]

-- Reshapes `Stack.refs`/`Heap.refs` into plain `List.flatMap` form so `Gc.Model.Theorems`'s count lemmas apply directly.
theorem stack_refs_eq_flatMap (stack : Stack) : stack.refs = stack.flatMap Frame.refs := by
  unfold Stack.refs
  rw [List.bind_eq_flatMap, List.flatMap_id, List.flatMap_def]

theorem heap_refs_eq_flatMap (heap : Heap) :
    heap.refs = heap.entries.flatMap (fun e => e.2.refs) := by
  unfold Heap.refs
  rw [List.bind_eq_flatMap, List.flatMap_def, List.map_map, ← List.flatMap_def]
  rfl

-- `RId rid'` is never a `ReachableStep` target: `x`'s var slot is H2's one allowed occurrence.
private theorem merge_ridPrime_not_step_target (vcfg : ValidConfig cfg) {frame : Frame} {rid' : RegionId}
    (hframemem : frame ∈ cfg.stack) (hxref : frame.varMap.lookup x = some (Reference.RId rid'))
    (a : Reference) : ¬ ReachableStep cfg a (Reference.RId rid') := by
  intro hstep
  have h2 := vcfg.h2 rid'
  have hxs : 1 ≤ cfg.stack.refs.count (Reference.RId rid') :=
    List.count_pos_iff.mpr (stack_refs_mem hframemem (mem_frame_refs_of_mem_varMap hxref))
  cases a with
  | RId ridA =>
    obtain ⟨_, -, -, hbeq⟩ := hstep
    cases hbeq
  | OId oidA =>
    obtain ⟨obj, hobjAt, hcontains⟩ := hstep
    have hb := List.contains_iff_mem.mp hcontains
    simp only [Reference.objAt?] at hobjAt
    split at hobjAt
    · obtain ⟨regionR, hlookupR, hobj⟩ := Option.bind_eq_some_iff.mp hobjAt
      have := List.count_pos_iff.mpr (heap_refs_mem_of_lookup hlookupR (mem_region_refs_of_mem_objMap hobj hb))
      omega
    · obtain ⟨f, hfind, hobj⟩ := Option.bind_eq_some_iff.mp hobjAt
      obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp (List.mem_of_find?_eq_some hfind)
      have : 2 ≤ cfg.stack.refs.count (Reference.RId rid') := by
        rw [stack_refs_eq_flatMap]
        by_cases heqframe : cfg.stack[n] = frame
        · subst heqframe
          refine le_trans ?_ (List.count_le_count_flatMap_of_mem hframemem)
          have h1 : 1 ≤ (cfg.stack[n].objMap.entries.map (·.2) >>= Object.refs).count (Reference.RId rid') :=
            List.count_pos_iff.mpr (objMap_bind_refs_mem_of_lookup hobj hb)
          have h2 : 1 ≤ (cfg.stack[n].varMap.entries.map (·.2)).count (Reference.RId rid') :=
            List.count_pos_iff.mpr (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hxref))
          simp only [Frame.refs, List.count_append]
          omega
        · exact List.two_le_count_flatMap_of_ne heqframe (List.getElem_mem _) hframemem
            (mem_frame_refs_of_mem_objMap hobj hb) (mem_frame_refs_of_mem_varMap hxref)
      omega
    · simp at hobjAt

-- A `RId rid'`-rooted chain to `target ≠ RId rid'` exists iff a `region'.bridgeObjectId`-rooted one does.
theorem merge_ridPrime_reflTransGen_iff {rid' : RegionId} {region' : Region}
    (hregion' : cfg.heap.lookup rid' = some region') (hclosed : region'.status = Status.Closed)
    {target : Reference} (hne1 : target ≠ Reference.RId rid') :
    Relation.ReflTransGen (ReachableStep cfg) (Reference.RId rid') target ↔
    Relation.ReflTransGen (ReachableStep cfg) (Reference.OId region'.bridgeObjectId) target := by
  refine ⟨fun hrtg => ?_, .head ⟨region', hregion', hclosed, rfl⟩⟩
  rcases hrtg.cases_head with heq | ⟨c, ⟨region2, hlookup2, -, rfl⟩, hrest⟩
  · exact absurd heq.symm hne1
  · rw [hregion', Option.some_inj] at hlookup2
    exact hlookup2 ▸ hrest

-- `x`'s own var slot is the only stack occurrence of `RId rid'`: no other frame can hold it (H2).
private theorem merge_ridPrime_no_other_frame_var (vcfg : ValidConfig cfg) {frame : Frame} {rid' : RegionId}
    (hframemem : frame ∈ cfg.stack) (hxref : frame.varMap.lookup x = some (Reference.RId rid'))
    {frame0 : Frame} (hframe0mem : frame0 ∈ cfg.stack) (hridne : frame0.regionId ≠ frame.regionId)
    {var0 : VarName} : frame0.varMap.lookup var0 ≠ some (Reference.RId rid') := fun hvar0 => by
  have h2 := vcfg.h2 rid'
  have : 2 ≤ cfg.stack.refs.count (Reference.RId rid') := by
    rw [stack_refs_eq_flatMap]
    exact List.two_le_count_flatMap_of_ne (fun hc => hridne (by rw [hc])) hframe0mem hframemem
      (mem_frame_refs_of_mem_varMap hvar0) (mem_frame_refs_of_mem_varMap hxref)
  omega

-- Same idea, within a single frame: two distinct var slots can't both hold `RId rid'` either.
theorem merge_ridPrime_var_unique (vcfg : ValidConfig cfg) {frame : Frame} {rid' : RegionId}
    (hframemem : frame ∈ cfg.stack) (hxref : frame.varMap.lookup x = some (Reference.RId rid')) :
    ∀ {var0 : VarName}, var0 ≠ x → frame.varMap.lookup var0 ≠ some (Reference.RId rid') := by
  intro var0 hne hvar0
  have h2 := vcfg.h2 rid'
  have hcount2 : 2 ≤ (frame.varMap.entries.map (·.2)).count (Reference.RId rid') := by
    rw [List.map_eq_flatMap]
    exact List.two_le_count_flatMap_of_ne (fun hc => hne (congrArg Sigma.fst hc))
      (AList.lookup_mem_entries hvar0) (AList.lookup_mem_entries hxref)
      (List.mem_singleton_self _) (List.mem_singleton_self _)
  have hle := List.count_le_count_flatMap_of_mem (f := Frame.refs) (b := Reference.RId rid') hframemem
  rw [← stack_refs_eq_flatMap] at hle
  simp only [Frame.refs, List.count_append] at hle
  omega

-- No on-stack frame owns `rid'`: `L2` would force its region simultaneously Open and Closed.
theorem merge_regionId_ne_ridPrime (vcfg : ValidConfig cfg) {rid' : RegionId} {region' : Region}
    (hregion' : cfg.heap.lookup rid' = some region') (hclosed : region'.status = Status.Closed) :
    ∀ G0 : FrameWithIndex, G0 ∈ cfg.stackWithIndex → G0.regionId ≠ rid' :=
  fun _ hG0mem hc => closed_region_not_owned vcfg hregion' hclosed hG0mem hc

-- Frame membership below the last index transports unconditionally down from `cfg'` to `cfg` (`merge` never pushes/pops).
theorem merge_frame_transport_down {cfg cfg' : RuntimeConfig} {x : VarName} {frame : Frame} {rid' : RegionId}
    {region region' : Region}
    (hframe : cfg.stack.getLast? = some frame) (_hxref : frame.varMap.lookup x = some (Reference.RId rid'))
    (_hregion : cfg.heap.lookup frame.regionId = some region) (_hregion' : cfg.heap.lookup rid' = some region')
    (_hclosed : region'.status = Status.Closed) (_hopen : region.status = Status.Open)
    (hcfg' : cfg' = { cfg with
      heap := (cfg.heap.erase rid').insert frame.regionId { region with objMap := region.objMap ∪ region'.objMap },
      stack := cfg.stack.dropLast ++
        [{ frame with varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) }] })
    {fr : FrameWithIndex} (hfr : fr ∈ cfg'.stackWithIndex) (hltfr : fr.index < cfg.stack.dropLast.length) :
    fr ∈ cfg.stackWithIndex := by
  subst hcfg'
  simp only [RuntimeConfig.stackWithIndex, List.mapIdx_concat, List.mem_append, List.mem_singleton] at hfr
  rw [stackWithIndex_eq_of_getLast? hframe]
  rcases hfr with hfr | rfl
  · exact List.mem_append_left _ hfr
  · simp at hltfr

-- Mirror of `merge_frame_transport_down`, the other direction.
theorem merge_frame_transport_up {cfg cfg' : RuntimeConfig} {x : VarName} {frame : Frame} {rid' : RegionId}
    {region region' : Region}
    (hframe : cfg.stack.getLast? = some frame) (_hxref : frame.varMap.lookup x = some (Reference.RId rid'))
    (_hregion : cfg.heap.lookup frame.regionId = some region) (_hregion' : cfg.heap.lookup rid' = some region')
    (_hclosed : region'.status = Status.Closed) (_hopen : region.status = Status.Open)
    (hcfg' : cfg' = { cfg with
      heap := (cfg.heap.erase rid').insert frame.regionId { region with objMap := region.objMap ∪ region'.objMap },
      stack := cfg.stack.dropLast ++
        [{ frame with varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) }] })
    {fr : FrameWithIndex} (hfr : fr ∈ cfg.stackWithIndex) (hltfr : fr.index < cfg.stack.dropLast.length) :
    fr ∈ cfg'.stackWithIndex := by
  subst hcfg'
  rw [stackWithIndex_eq_of_getLast? hframe, List.mem_append, List.mem_singleton] at hfr
  simp only [RuntimeConfig.stackWithIndex, List.mapIdx_concat]
  rcases hfr with hfr | rfl
  · exact List.mem_append_left _ hfr
  · simp at hltfr

-- A chain whose start avoids `r`, and which `S` never steps into, transports along any step map valid away from `r`.
private theorem reflTransGen_transport_avoiding {α : Type*} {S T : α → α → Prop} {r : α}
    (hST : ∀ a, a ≠ r → ∀ b, S a b → T a b) (hnot : ∀ a, ¬ S a r) {start target : α} (hne : start ≠ r)
    (h : Relation.ReflTransGen S start target) : Relation.ReflTransGen T start target := by
  induction h with
  | refl => exact .refl
  | tail hprev hstep ih =>
    refine ih.tail (hST _ ?_ _ hstep)
    rcases hprev.cases_tail with rfl | ⟨c, -, hc⟩
    · exact hne
    · rintro rfl
      exact hnot _ hc

-- A `RId rid'`-avoiding `ReachableStep` chain transports unconditionally from `cfg'` back down to `cfg`.
theorem merge_chain_transport_down {cfg cfg' : RuntimeConfig} {x : VarName} (vcfg : ValidConfig cfg)
    {frame : Frame} {rid' : RegionId} {region region' : Region}
    (h : merge x cfg = some cfg')
    (hframe : cfg.stack.getLast? = some frame) (hxref : frame.varMap.lookup x = some (Reference.RId rid'))
    (hregion : cfg.heap.lookup frame.regionId = some region) (hregion' : cfg.heap.lookup rid' = some region')
    (hclosed : region'.status = Status.Closed) (hopen : region.status = Status.Open)
    (hcfg' : cfg' = { cfg with
      heap := (cfg.heap.erase rid').insert frame.regionId { region with objMap := region.objMap ∪ region'.objMap },
      stack := cfg.stack.dropLast ++
        [{ frame with varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) }] })
    {start target : Reference} (hstartne : start ≠ Reference.RId rid')
    (hrtg : Relation.ReflTransGen (ReachableStep cfg') start target) :
    Relation.ReflTransGen (ReachableStep cfg) start target := by
  have hiff := fun a (hane : a ≠ Reference.RId rid') => merge_step_iff_of_ne vcfg h hregion hopen hcfg' hane
  refine reflTransGen_transport_avoiding (fun a hane b => (hiff a hane b).mpr) (fun a hstep => ?_) hstartne hrtg
  by_cases hane : a = Reference.RId rid'
  · subst hane
    obtain ⟨_, hlookup2, -, -⟩ := hstep
    rw [hcfg'] at hlookup2
    simp [AList.lookup_insert_ne (merge_corollary_rid_ne_regionId hregion hregion' hclosed hopen)] at hlookup2
  · exact merge_ridPrime_not_step_target vcfg (List.mem_of_getLast? hframe) hxref a ((hiff a hane _).mpr hstep)

-- Merge leaves every suspended frame's `FrameReachable` set unchanged.
theorem merge_frame_reachable_iff {cfg cfg' : RuntimeConfig} {x : VarName} (vcfg : ValidConfig cfg)
    (h : merge x cfg = some cfg')
    {X : FrameWithIndex} (_hXmem : X ∈ cfg.stackWithIndex) (hXlt : X.index < cfg.stack.length - 1)
    (ref : Reference) : FrameReachable cfg X.index ref ↔ FrameReachable cfg' X.index ref := by
  obtain ⟨frame, rid', region, region', hframe, hxref, hregion, hregion', hclosed, hopen, hcfg'⟩ :=
    merge_cases h
  have hframemem := List.mem_of_getLast? hframe
  have hXlt' : X.index < cfg.stack.dropLast.length := by rwa [List.length_dropLast]
  have hlk : ∀ G0 ∈ cfg.stackWithIndex, G0.index = X.index →
      cfg'.heap.lookup G0.regionId = cfg.heap.lookup G0.regionId := fun G0 hG0 hidx => by
    rw [hcfg']
    exact (AList.lookup_insert_ne (regionId_ne_last_of_suspended vcfg hG0 (hidx ▸ hXlt) hframe)).trans
      (AList.lookup_erase_ne (closed_region_not_owned vcfg hregion' hclosed hG0 ·))
  have hdown := fun {G0} (hG0 : G0 ∈ cfg'.stackWithIndex) (hidx : G0.index = X.index) =>
    merge_frame_transport_down hframe hxref hregion hregion' hclosed hopen hcfg' hG0 (hidx ▸ hXlt')
  have hroot : ∀ start, FrameRoot cfg X.index start ↔ FrameRoot cfg' X.index start := fun start => by
    constructor
    · rintro (⟨G0, hG0, hidx, hvar⟩ | ⟨G0, hG0, hidx, region0, hlk0, hbridge0⟩)
      · exact .inl ⟨G0, merge_frame_transport_up hframe hxref hregion hregion' hclosed hopen hcfg' hG0
          (hidx ▸ hXlt'), hidx, hvar⟩
      · exact .inr ⟨G0, merge_frame_transport_up hframe hxref hregion hregion' hclosed hopen hcfg' hG0
          (hidx ▸ hXlt'), hidx, region0, (hlk G0 hG0 hidx).trans hlk0, hbridge0⟩
    · rintro (⟨G0, hG0, hidx, hvar⟩ | ⟨G0, hG0, hidx, region0, hlk0, hbridge0⟩)
      · exact .inl ⟨G0, hdown hG0 hidx, hidx, hvar⟩
      · exact .inr ⟨G0, hdown hG0 hidx, hidx, region0, (hlk G0 (hdown hG0 hidx) hidx).symm.trans hlk0, hbridge0⟩
  have hstartne : ∀ {start}, FrameRoot cfg X.index start → start ≠ Reference.RId rid' := by
    rintro _ (⟨G0, hG0, hidx, var, hvar⟩ | ⟨G0, -, -, region0, -, hbridge0⟩) rfl
    · obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp hG0
      exact merge_ridPrime_no_other_frame_var vcfg hframemem hxref (List.getElem_mem hn)
        (regionId_ne_last_of_suspended vcfg hG0 (hidx ▸ hXlt) hframe) hvar
    · cases hbridge0
  rw [FrameReachable_iff_reflTransGen, FrameReachable_iff_reflTransGen]
  constructor
  · rintro ⟨start, hr, hrtg⟩
    have hiff := fun a (hane : a ≠ Reference.RId rid') => merge_step_iff_of_ne vcfg h hregion hopen hcfg' hane
    exact ⟨start, (hroot start).mp hr, reflTransGen_transport_avoiding (fun a hane b => (hiff a hane b).mp)
      (merge_ridPrime_not_step_target vcfg hframemem hxref) (hstartne hr) hrtg⟩
  · rintro ⟨start, hr, hrtg⟩
    have hr0 := (hroot start).mpr hr
    exact ⟨start, hr0, merge_chain_transport_down vcfg h hframe hxref hregion hregion' hclosed hopen hcfg'
      (hstartne hr0) hrtg⟩

-- merge preserves the stack length.
theorem merge_length {cfg cfg' : RuntimeConfig} (h : merge x cfg = some cfg') :
    cfg'.stackWithIndex.length = cfg.stackWithIndex.length := by
  obtain ⟨A, -, -, -, hA, -, -, -, -, -, rfl⟩ := merge_cases h
  exact stackWithIndex_length_of_replace_last hA rfl

-- Anything reachable after merge is stack-reachable before it: only the merged frame's roots change, and `x`'s new value is one hop past `RId rid'`.
private theorem merge_reach_down {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg) (h : merge x cfg = some cfg')
    {fid : Index} {oid : ObjectId} (hfr : FrameReachable cfg' fid (.OId oid)) : StackReachable cfg (.OId oid) := by
  obtain ⟨start, hs, hc⟩ := (FrameReachable_iff_reflTransGen ..).mp hfr
  obtain ⟨A, rid', region1, region', hA, hxref, hregion1, hregion', hclosed, hopen, hcfg'⟩ := merge_cases h
  have hsw := stackWithIndex_eq_of_getLast? hA
  have hlastA : ({ A with index := cfg.stack.dropLast.length } : FrameWithIndex) ∈ cfg.stackWithIndex := by
    simp [hsw]
  have hdown := fun hne => merge_chain_transport_down vcfg h hA hxref hregion1 hregion' hclosed hopen hcfg' hne hc
  have hleft : ∀ G ∈ cfg.stack.dropLast.mapIdx (fun i f => ({ f with index := i } : FrameWithIndex)),
      FrameReachable cfg' G.index (.OId oid) → StackReachable cfg (.OId oid) := fun G hG hr => by
    have hGc : G ∈ cfg.stackWithIndex := hsw ▸ List.mem_append_left _ hG
    obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp hG
    exact ⟨_, hGc, (merge_frame_reachable_iff vcfg h hGc (by simp at hn ⊢; omega) _).mpr hr⟩
  rw [hcfg'] at hs
  rcases hs with ⟨G, hG, rfl, v, hv⟩ | ⟨G, hG, rfl, r, hr, rfl⟩ <;>
    rw [stackWithIndex_mk_append_singleton] at hG <;> rcases List.mem_append.mp hG with hG | hG
  · exact hleft G hG hfr
  · obtain rfl := List.mem_singleton.mp hG
    by_cases hvx : v = x
    · subst hvx
      simp only [AList.lookup_insert, Option.some.injEq] at hv
      subst hv
      exact StackReachable_of_root (.inl ⟨_, hlastA, rfl, _, hxref⟩)
        (.head ⟨region', hregion', hclosed, rfl⟩ (hdown (by simp)))
    · rw [AList.lookup_insert_ne hvx] at hv
      exact StackReachable_of_root (.inl ⟨_, hlastA, rfl, v, hv⟩)
        (hdown fun he => merge_ridPrime_var_unique vcfg (List.mem_of_getLast? hA) hxref hvx (he ▸ hv))
  · exact hleft G hG hfr
  · obtain rfl := List.mem_singleton.mp hG
    simp only [AList.lookup_insert, Option.some.injEq] at hr
    subst hr
    exact StackReachable_of_root (.inr ⟨_, hlastA, rfl, region1, hregion1, rfl⟩) (hdown (by simp))

-- For `oid` in a suspended frame `F`'s region, merge neither creates nor destroys its reachability from `F`.
theorem merge_suspended_reach {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : merge x cfg = some cfg') (hFR3 : FrameReachable_at_later_frame_implies_FrameReachable_at_frame cfg)
    {F : FrameWithIndex} (hF : F ∈ cfg.stackWithIndex) (hFlt : F.index < cfg.stackWithIndex.length - 1)
    {oid : ObjectId} (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn F.regionId)) :
    F ∈ cfg'.stackWithIndex ∧ (StackReachable cfg (.OId oid) → FrameReachable cfg' F.index (.OId oid)) ∧
    ∀ fid, FrameReachable cfg' fid (.OId oid) → StackReachable cfg (.OId oid) := by
  have hFlt' : F.index < cfg.stack.length - 1 := by simpa [RuntimeConfig.stackWithIndex] using hFlt
  obtain ⟨A, rid', region1, region', hA, hxref, hregion1, hregion', hclosed, hopen, hcfg'⟩ := merge_cases h
  exact ⟨merge_frame_transport_up hA hxref hregion1 hregion' hclosed hopen hcfg' hF (by simpa using hFlt'),
    fun hs => (merge_frame_reachable_iff vcfg h hF hFlt' _).mp (FrameReachable_of_StackReachable vcfg hFR3 hF hloc hs),
    fun _ => merge_reach_down vcfg h⟩
