import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Theorems

def L1 (cfg : RuntimeConfig) : Prop :=
  cfg.objectIds.Nodup

def L2 (cfg : RuntimeConfig) : Prop :=
  ∀ frame ∈ cfg.stack, ∃ region,
    cfg.heap.lookup frame.regionId = some region ∧
    region.status = Status.Open

def H1 (cfg : RuntimeConfig) : Prop :=
  ∀ region ∈ cfg.heap.regions,
    region.bridgeObjectId ∈ region.objMap

def H2 (cfg : RuntimeConfig) : Prop :=
  ∀ rid,
    (cfg.stack.refs.count (Reference.RId rid))
    + (cfg.heap.refs.count (Reference.RId rid)) ≤ 1

def H3 (cfg : RuntimeConfig) : Prop :=
  ∀ rid oid region,
    cfg.heap.lookup rid = some region →
    (Reference.OId oid) ∈ region.refs →
    (Reference.OId oid).loc? cfg = some (Location.Rgn rid)

def S1 (cfg : RuntimeConfig) : Prop :=
  (cfg.stack.map (λ frame => frame.regionId)).Nodup

def S2 (cfg : RuntimeConfig) : Prop :=
  ∀ frame ∈ cfg.stackWithIndex, ∀ ref ∈ frame.refs, ∀ fid' oid,
    ref = Reference.OId oid →
    ref.loc? cfg = some (Location.Stk fid') →
    fid' <= frame.index

def S3 (cfg : RuntimeConfig) : Prop :=
  ∀ frame ∈ cfg.stackWithIndex, ∀ ref ∈ frame.refs, ∀ rid' oid,
    ref = Reference.OId oid →
    ref.loc? cfg = some (Location.Rgn rid') →
    ∃ frame' ∈ cfg.stackWithIndex,
      frame'.regionId = rid' ∧ frame'.index <= frame.index

structure ValidConfig (cfg : RuntimeConfig) where
  l1 : L1 cfg
  l2 : L2 cfg
  h1 : H1 cfg
  h2 : H2 cfg
  h3 : H3 cfg
  s1 : S1 cfg
  s2 : S2 cfg
  s3 : S3 cfg

theorem oid_in_stack_implies_not_in_heap : ValidConfig cfg →
  cfg.stackWithIndex.findRev? (λ frame => frame.objMap.keys.contains oid) = some frame →
  cfg.heap.entries.find? (λ ⟨_, region⟩ => region.objMap.keys.contains oid) = none := by
  intro vcfg frame_in_stack
  have l1 := vcfg.l1
  rw [List.findRev?_eq_find?_reverse] at frame_in_stack
  have : (cfg.stackWithIndex.reverse.find? (λ f => f.objMap.keys.contains oid)).isSome := by
    unfold Option.isSome
    rw [frame_in_stack]
  obtain ⟨f, f_in_stackWithIndex, f_obj_contains⟩ := List.find?_isSome.mp this
  rw [List.mem_reverse] at f_in_stackWithIndex

  obtain ⟨n, n_le_length, f_eq⟩ := List.mem_mapIdx.mp f_in_stackWithIndex
  let g := f.toFrame
  have g_in_stack : g ∈ cfg.stack := by
    unfold g
    rw [← f_eq]
    dsimp
    apply List.mem_iff_getElem.mpr
    use n
    exact ⟨_, rfl⟩

  have oid_in_g_keys : oid ∈ g.objMap.keys := by
    unfold g
    exact List.contains_iff_mem.mp f_obj_contains

  have oid_in_stack : oid ∈ cfg.stack.objectIds := by
    unfold Stack.objectIds Frame.objectIds
    rw [List.bind_eq_flatMap, List.flatMap_id, List.mem_flatten]
    use g.objMap.keys
    constructor
    · apply List.mem_map_of_mem
      exact g_in_stack
    · exact oid_in_g_keys

  cases region_in_heap : List.find?
    (fun x => match x with | ⟨rid, region⟩ => (AList.keys region.objMap).contains oid)
    cfg.heap.entries
    with
  | none => exact rfl
  | some loc =>
    have : (cfg.heap.entries.find? (λ ⟨_, region⟩ => region.objMap.keys.contains oid)).isSome := by
      unfold Option.isSome
      rw [region_in_heap]
    obtain ⟨⟨rid, region⟩, region_in_entries, region_obj_contains⟩ := List.find?_isSome.mp this
    have oid_in_region : oid ∈ region.objMap.keys := by
      unfold AList.keys
      exact List.contains_iff_mem.mp region_obj_contains
    have oid_in_heap : oid ∈ cfg.heap.objectIds := by
      unfold Heap.objectIds Region.objectIds
      apply List.mem_flatten.mpr
      use region.objMap.keys
      constructor
      · replace region_in_entries := List.mem_map_of_mem (f := λ ⟨_, r⟩ => r.objMap.keys) region_in_entries
        dsimp at region_in_entries
        exact region_in_entries
      · exact oid_in_region

    unfold L1 RuntimeConfig.objectIds at l1
    obtain ⟨_, _, helper⟩ := List.nodup_append.mp l1
    replace helper := helper oid oid_in_stack oid oid_in_heap
    contradiction

theorem oid_in_heap_implies_not_in_stack : ValidConfig cfg →
  cfg.heap.entries.find? (λ ⟨_, region⟩ => region.objMap.keys.contains oid) = some ⟨rid, region⟩ →
  cfg.stackWithIndex.findRev? (λ frame => frame.objMap.keys.contains oid) = none := by
  intro vcfg region_in_heap
  have l1 := vcfg.l1
  have : (cfg.heap.entries.find? (λ ⟨_, region⟩ => region.objMap.keys.contains oid)).isSome := by
    unfold Option.isSome
    rw [region_in_heap]
  obtain ⟨⟨rid, region⟩, region_in_entries, region_obj_contains⟩ := List.find?_isSome.mp this
  have oid_in_region : oid ∈ region.objMap.keys := by
    unfold AList.keys
    exact List.contains_iff_mem.mp region_obj_contains
  have oid_in_heap : oid ∈ cfg.heap.objectIds := by
    unfold Heap.objectIds Region.objectIds
    apply List.mem_flatten.mpr
    use region.objMap.keys
    constructor
    · replace region_in_entries := List.mem_map_of_mem (f := λ ⟨_, r⟩ => r.objMap.keys) region_in_entries
      dsimp at region_in_entries
      exact region_in_entries
    · exact oid_in_region

  cases frame_in_stack : List.findRev?
    (fun frame => (AList.keys frame.objMap).contains oid)
    cfg.stackWithIndex
    with
  | none => exact rfl
  | some loc =>
    rw [List.findRev?_eq_find?_reverse] at frame_in_stack
    have : (cfg.stackWithIndex.reverse.find? (λ f => f.objMap.keys.contains oid)).isSome := by
      unfold Option.isSome
      rw [frame_in_stack]
    obtain ⟨f, f_in_stackWithIndex, f_obj_contains⟩ := List.find?_isSome.mp this
    rw [List.mem_reverse] at f_in_stackWithIndex

    obtain ⟨n, n_le_length, f_eq⟩ := List.mem_mapIdx.mp f_in_stackWithIndex
    let g := f.toFrame
    have g_in_stack : g ∈ cfg.stack := by
      unfold g
      rw [← f_eq]
      dsimp
      apply List.mem_iff_getElem.mpr
      use n
      exact ⟨_, rfl⟩

    have oid_in_g_keys : oid ∈ g.objMap.keys := by
      unfold g
      exact List.contains_iff_mem.mp f_obj_contains

    have oid_in_stack : oid ∈ cfg.stack.objectIds := by
      unfold Stack.objectIds Frame.objectIds
      rw [List.bind_eq_flatMap, List.flatMap_id, List.mem_flatten]
      use g.objMap.keys
      constructor
      · apply List.mem_map_of_mem
        exact g_in_stack
      · exact oid_in_g_keys
    unfold L1 RuntimeConfig.objectIds at l1
    obtain ⟨_, _, helper⟩ := List.nodup_append.mp l1
    replace helper := helper oid oid_in_stack oid oid_in_heap
    contradiction

theorem rid_loc_rgn_iff_in_heap : ValidConfig cfg →
  ((Reference.RId rid).loc? cfg = some (Location.Rgn rid) ↔
  ∃ region, cfg.heap.lookup rid = some region) := by
  intro vcfg
  constructor
  · intro loc_rid
    unfold Reference.loc? at loc_rid
    dsimp at loc_rid
    by_cases h : (AList.keys cfg.heap).contains rid
    · rw [List.contains_iff_mem] at h
      unfold AList.keys at h
      obtain ⟨region, pair_in_heap⟩ := List.mem_keys.mp h
      use region
      exact AList.mem_lookup_iff.mpr pair_in_heap
    · rw [if_neg h] at loc_rid
      contradiction
  · intro region_in_heap
    obtain ⟨region, pair_in_heap⟩ := region_in_heap
    unfold Reference.loc?
    dsimp
    apply Option.isSome_of_eq_some at pair_in_heap
    rw [AList.lookup_isSome, AList.mem_keys, ← List.contains_iff_mem] at pair_in_heap
    rw [if_pos pair_in_heap]

theorem oid_loc_rgn_iff_in_heap : ValidConfig cfg →
  ((Reference.OId oid).loc? cfg = some (Location.Rgn rid) ↔
  ∃ region, cfg.heap.lookup rid = some region ∧ oid ∈ region.objMap) := by
  intro vcfg
  constructor
  · intro loc_oid
    unfold Reference.loc? at loc_oid
    dsimp at loc_oid
    cases h : List.find? (fun x => (AList.keys x.snd.objMap).contains oid) cfg.heap.entries with
    | none =>
      rw [h] at loc_oid
      cases h' : List.findRev? (fun frame => (AList.keys frame.objMap).contains oid) cfg.stackWithIndex with
      | none =>
        rw [h'] at loc_oid
        dsimp at loc_oid
        contradiction
      | some frame =>
        rw [h'] at loc_oid
        dsimp at loc_oid
        rw [Option.some_inj] at loc_oid
        contradiction
    | some rid'region' =>
      obtain ⟨rid', region'⟩ := rid'region'
      have not_in_stack := oid_in_heap_implies_not_in_stack vcfg h
      rw [h, not_in_stack] at loc_oid
      dsimp at loc_oid
      rw [Option.some_inj, Location.Rgn.injEq] at loc_oid
      subst rid
      use region'
      obtain ⟨region'_contains_oid, n, n_lt_length, get_n, _⟩ := List.find?_eq_some_iff_getElem.mp h
      dsimp at region'_contains_oid
      rw [List.contains_iff_mem, ← AList.mem_keys] at region'_contains_oid
      apply List.mem_of_getElem at get_n
      rw [← AList.mem_lookup_iff] at get_n
      exact ⟨get_n, region'_contains_oid⟩
  · intro region_in_heap
    obtain ⟨region, rid_lookup_region, oid_in_region⟩ := region_in_heap
    unfold Reference.loc?
    dsimp
    have : List.find? (fun x => (AList.keys x.snd.objMap).contains oid) cfg.heap.entries = some ⟨rid, region⟩ := by
      apply List.find?_eq_some_iff_getElem.mpr
      dsimp
      rw [AList.mem_keys, ← List.contains_iff_mem] at oid_in_region
      constructor
      · exact oid_in_region
      · rw [← Option.mem_def, AList.mem_lookup_iff] at rid_lookup_region
        have rid_lookup_region_dupe := rid_lookup_region
        rw [List.mem_iff_getElem] at rid_lookup_region
        obtain ⟨n, n_lt_length, get_n⟩ := rid_lookup_region
        use n
        use n_lt_length
        constructor
        · exact get_n
        · intro j j_lt_n
          have l1 := vcfg.l1
          by_contra hcon
          rw [Bool.not_eq_true, Bool.not_eq_false'] at hcon
          unfold L1 RuntimeConfig.objectIds at l1
          obtain ⟨_, heap_nodup, _⟩ := List.nodup_append.mp l1
          unfold Heap.objectIds at heap_nodup
          rw [List.nodup_flatten, List.pairwise_map] at heap_nodup
          obtain ⟨_, pairwise_disjoint⟩ := heap_nodup
          have j_lt_length : j < cfg.heap.entries.length := lt_trans j_lt_n n_lt_length
          have disj := List.Pairwise.rel_get_of_lt pairwise_disjoint
            (a := ⟨j, j_lt_length⟩) (b := ⟨n, n_lt_length⟩) j_lt_n
          simp only [List.get_eq_getElem] at disj
          rw [get_n] at disj
          unfold Region.objectIds at disj
          exact disj (List.contains_iff_mem.mp hcon) (List.contains_iff_mem.mp oid_in_region)
    have not_in_stack := oid_in_heap_implies_not_in_stack vcfg this
    rw [this, not_in_stack]

theorem oid_loc_stk_iff_in_stack : ValidConfig cfg →
  ((Reference.OId oid).loc? cfg = some (Location.Stk fid) ↔
  ∃ frame, cfg.stackWithIndex[fid]? = some frame ∧ oid ∈ frame.objMap) := by
  intro vcfg
  constructor
  · intro loc_oid
    unfold Reference.loc? at loc_oid
    dsimp at loc_oid
    cases h1 : cfg.stackWithIndex.findRev? (fun frame => (AList.keys frame.objMap).contains oid) with
    | none =>
      rw [h1] at loc_oid
      cases h2 : List.find? (fun x => (AList.keys x.snd.objMap).contains oid) cfg.heap.entries with
      | none =>
        rw [h2] at loc_oid
        dsimp at loc_oid
        contradiction
      | some rid_region =>
        obtain ⟨rid', region'⟩ := rid_region
        rw [h2] at loc_oid
        dsimp at loc_oid
        rw [Option.some_inj] at loc_oid
        contradiction
    | some frame0 =>
      rw [h1] at loc_oid
      cases h2 : List.find? (fun x => (AList.keys x.snd.objMap).contains oid) cfg.heap.entries with
      | none =>
        rw [h2] at loc_oid
        dsimp at loc_oid
        rw [Option.some_inj, Location.Stk.injEq] at loc_oid
        rw [List.findRev?_eq_find?_reverse] at h1
        have mem_rev : frame0 ∈ cfg.stackWithIndex := List.mem_reverse.mp (List.mem_of_find?_eq_some h1)
        have pred_true := List.find?_some h1
        obtain ⟨n, n_lt_length, f_eq⟩ := List.mem_mapIdx.mp mem_rev
        have idx_eq : frame0.index = n := by rw [← f_eq]
        refine ⟨frame0, ?_, ?_⟩
        · unfold RuntimeConfig.stackWithIndex
          rw [← loc_oid, idx_eq, List.getElem?_mapIdx, List.getElem?_eq_getElem n_lt_length]
          dsimp
          rw [f_eq]
        · rw [AList.mem_keys, ← List.contains_iff_mem]
          exact pred_true
      | some rid_region =>
        obtain ⟨rid', region'⟩ := rid_region
        rw [h2] at loc_oid
        dsimp at loc_oid
        contradiction
  · intro frame_in_stack
    obtain ⟨frame, stk_lookup_frame, oid_in_frame⟩ := frame_in_stack
    have l1 := vcfg.l1
    unfold L1 RuntimeConfig.objectIds at l1
    obtain ⟨stack_nodup, _, _⟩ := List.nodup_append.mp l1
    unfold Stack.objectIds at stack_nodup
    rw [List.bind_eq_flatMap, List.flatMap_id, List.nodup_flatten, List.pairwise_map] at stack_nodup
    obtain ⟨_, stack_pairwise_disjoint⟩ := stack_nodup
    rw [AList.mem_keys, ← List.contains_iff_mem] at oid_in_frame
    unfold RuntimeConfig.stackWithIndex at stk_lookup_frame
    rw [List.getElem?_mapIdx, Option.map_eq_some_iff] at stk_lookup_frame
    obtain ⟨stackFrame, hfid, hframe_eq⟩ := stk_lookup_frame
    obtain ⟨fid_lt_length, stackFrame_eq⟩ := List.getElem?_eq_some_iff.mp hfid
    have frame_eq : ({cfg.stack[fid] with index := fid} : FrameWithIndex) = frame :=
      stackFrame_eq ▸ hframe_eq
    have idx_eq_fid : frame.index = fid := by rw [← frame_eq]
    have frame_objMap_eq : frame.objMap = cfg.stack[fid].objMap := by rw [← frame_eq]
    have h1_eq : cfg.stackWithIndex.findRev? (fun f => (AList.keys f.objMap).contains oid) = some frame := by
      rw [List.findRev?_eq_find?_reverse]
      apply List.find?_eq_some_of_unique
      · rw [List.mem_reverse]
        unfold RuntimeConfig.stackWithIndex
        exact List.mem_mapIdx.mpr ⟨fid, fid_lt_length, frame_eq⟩
      · exact oid_in_frame
      · intro frame' frame'_mem frame'_pred
        rw [List.mem_reverse] at frame'_mem
        unfold RuntimeConfig.stackWithIndex at frame'_mem
        obtain ⟨n', n'_lt_length, f'_eq⟩ := List.mem_mapIdx.mp frame'_mem
        have oid_in_n' : oid ∈ Frame.objectIds cfg.stack[n'] := by
          unfold Frame.objectIds
          have frame'_objMap_eq : frame'.objMap = cfg.stack[n'].objMap := by rw [← f'_eq]
          rw [← frame'_objMap_eq]
          exact List.contains_iff_mem.mp frame'_pred
        have oid_in_fid : oid ∈ Frame.objectIds cfg.stack[fid] := by
          unfold Frame.objectIds
          rw [← frame_objMap_eq]
          exact List.contains_iff_mem.mp oid_in_frame
        have idx_eq : n' = fid := by
          by_contra hne
          rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
          · have disj := List.Pairwise.rel_get_of_lt stack_pairwise_disjoint
              (a := ⟨n', n'_lt_length⟩) (b := ⟨fid, fid_lt_length⟩) hlt
            simp only [List.get_eq_getElem] at disj
            exact disj oid_in_n' oid_in_fid
          · have disj := List.Pairwise.rel_get_of_lt stack_pairwise_disjoint
              (a := ⟨fid, fid_lt_length⟩) (b := ⟨n', n'_lt_length⟩) hgt
            simp only [List.get_eq_getElem] at disj
            exact disj oid_in_fid oid_in_n'
        rw [← f'_eq]
        subst idx_eq
        exact frame_eq
    unfold Reference.loc?
    dsimp
    rw [h1_eq]
    have not_in_heap := oid_in_stack_implies_not_in_heap vcfg h1_eq
    rw [not_in_heap]
    dsimp
    rw [idx_eq_fid]
