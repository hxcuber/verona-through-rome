module

public import Gc.Reachability.Reachable.Lemmas.Common

@[expose] public section

-- `loc?` agrees between `cfg`/`cfg'` for any oid other than the freshly-allocated one.
theorem makeObjStack_loc_eq_of_ne {cfg cfg' : RuntimeConfig} (h : makeObjStack x cfg = some cfg')
    {oid : ObjectId} (hne : oid ≠ cfg.freshObjectId) :
    (Reference.OId oid).loc? cfg = (Reference.OId oid).loc? cfg' := by
  obtain ⟨lastFrame, hlast, rfl⟩ := makeObjStack_cases h
  refine loc_eq_of_find_map_eq ?_ rfl
  rw [stackWithIndex_eq_of_getLast? hlast, stackWithIndex_mk_append_singleton]
  have hkeq : (lastFrame.objMap.insert cfg.freshObjectId ∅).keys.contains oid = lastFrame.objMap.keys.contains oid := by
    simp [AList.keys_insert, hne]
  simp only [List.findRev?_eq_find?_reverse, List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.find?_cons, hkeq]
  split <;> rfl

-- `objAt?` agrees between `cfg`/`cfg'` for any oid other than the freshly-allocated one.
theorem makeObjStack_objAt_eq_of_ne {cfg cfg' : RuntimeConfig} (h : makeObjStack x cfg = some cfg')
    {oid : ObjectId} (hne : oid ≠ cfg.freshObjectId) :
    (Reference.OId oid).objAt? cfg = (Reference.OId oid).objAt? cfg' := by
  have hlocEq := makeObjStack_loc_eq_of_ne h hne
  obtain ⟨lastFrame, hlast, rfl⟩ := makeObjStack_cases h
  unfold Reference.objAt?
  dsimp only
  rw [hlocEq]
  rcases (Reference.OId oid).loc? _ with _ | _ | fid
  · rfl
  · rfl
  dsimp only
  rw [stackWithIndex_find_index_eq_getElem, stackWithIndex_find_index_eq_getElem,
    stackWithIndex_eq_of_getLast? hlast, stackWithIndex_mk_append_singleton]
  simp only [List.getElem?_append, List.getElem?_singleton]
  split_ifs <;> simp [AList.lookup_insert_ne hne]

-- No heap region holds the fresh object id.
private theorem fresh_heap_find_none (cfg : RuntimeConfig) :
    cfg.heap.entries.find? (fun (e : Sigma (fun _ : RegionId => Region)) =>
      e.snd.objMap.keys.contains cfg.freshObjectId) = none :=
  List.find?_eq_none.mpr fun _ he hc => cfg.freshObjectId_not_mem
    (List.mem_append_right _ (heap_objectIds_of_mem he (by simpa using hc)))

-- A fresh object id never resolves to any location (it isn't allocated yet).
theorem freshObjectId_loc_none {cfg : RuntimeConfig} :
    (Reference.OId cfg.freshObjectId).loc? cfg = none := by
  have hs : cfg.stackWithIndex.findRev? (fun f => f.objMap.keys.contains cfg.freshObjectId) = none := by
    refine List.findRev?_eq_find?_reverse ▸ List.find?_eq_none.mpr fun f hf hc => ?_
    obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp (List.mem_reverse.mp hf)
    exact freshObjectId_not_mem_frame (List.getElem_mem hn) (by simpa using hc)
  unfold Reference.loc?
  simp only [hs, fresh_heap_find_none]

-- A fresh object id never resolves anywhere (it isn't allocated yet).
theorem freshObjectId_objAt_none {cfg : RuntimeConfig} :
    (Reference.OId cfg.freshObjectId).objAt? cfg = none := by
  unfold Reference.objAt?
  dsimp only
  rw [freshObjectId_loc_none]

-- The freshly-allocated object resolves to its own (empty) content in cfg'.
private theorem makeObjStack_fresh_objAt_cfg' {cfg cfg' : RuntimeConfig} (h : makeObjStack x cfg = some cfg') :
    (Reference.OId cfg.freshObjectId).objAt? cfg' = some (∅ : Object) := by
  obtain ⟨lastFrame, hlast, rfl⟩ := makeObjStack_cases h
  have hloc : (Reference.OId cfg.freshObjectId).loc? { cfg with stack := cfg.stack.dropLast ++ [{ lastFrame with
      varMap := lastFrame.varMap.insert x (Reference.OId cfg.freshObjectId),
      objMap := lastFrame.objMap.insert cfg.freshObjectId ∅ }] } =
      some (Location.Stk cfg.stack.dropLast.length) := by
    unfold Reference.loc?
    dsimp only
    rw [fresh_heap_find_none]
    simp [stackWithIndex_mk_append_singleton, List.findRev?_eq_find?_reverse,
      AList.keys_insert]
  unfold Reference.objAt?
  dsimp only
  rw [hloc]
  dsimp only
  rw [stackWithIndex_find_index_eq_getElem, stackWithIndex_mk_append_singleton]
  simp

-- `ReachableStep` agrees unconditionally: the fresh id has no out-edges on either side and `makeObjStack` never touches the heap.
theorem makeObjStack_step_eq {cfg cfg' : RuntimeConfig} (h : makeObjStack x cfg = some cfg') :
    ReachableStep cfg = ReachableStep cfg' := by
  funext a b
  apply propext
  rcases a with rid | oid
  · obtain ⟨lastFrame, hlast, rfl⟩ := makeObjStack_cases h
    rw [ReachableStep_rid_iff, ReachableStep_rid_iff]
  by_cases hne : oid = cfg.freshObjectId
  · subst hne
    simp [ReachableStep_oid_iff, freshObjectId_objAt_none, makeObjStack_fresh_objAt_cfg' h, Object.refs]
  · rw [ReachableStep_oid_iff, ReachableStep_oid_iff, makeObjStack_objAt_eq_of_ne h hne]

-- Every `cfg'.stackWithIndex` member is either an unchanged pre-existing frame or the modified last frame.
theorem makeObjStack_frame_cases {cfg cfg' : RuntimeConfig} {lastFrame : Frame} {x : VarName}
    (hlast : cfg.stack.getLast? = some lastFrame)
    (hcfg' : cfg' = { cfg with
      stack := cfg.stack.dropLast ++ [{ lastFrame with
        varMap := lastFrame.varMap.insert x (Reference.OId cfg.freshObjectId),
        objMap := lastFrame.objMap.insert cfg.freshObjectId ∅ }] })
    {frame : FrameWithIndex} (hframe : frame ∈ cfg'.stackWithIndex) :
    (frame ∈ cfg.stackWithIndex ∧ frame.index < cfg.stack.length - 1) ∨
    (frame.regionId = lastFrame.regionId ∧ frame.bridgeVar = lastFrame.bridgeVar ∧
      frame.varMap = lastFrame.varMap.insert x (Reference.OId cfg.freshObjectId) ∧
      frame.objMap = lastFrame.objMap.insert cfg.freshObjectId ∅ ∧
      frame.index = cfg.stack.dropLast.length) := by
  subst hcfg'
  rw [stackWithIndex_mk_append_singleton] at hframe
  rcases List.mem_append.mp hframe with hmem | hmem
  · refine .inl ⟨stackWithIndex_eq_of_getLast? hlast ▸ List.mem_append_left _ hmem, ?_⟩
    obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp hmem
    simpa using hn
  · rw [List.mem_singleton.mp hmem]
    exact .inr ⟨rfl, rfl, rfl, rfl, rfl⟩

-- A pre-existing frame below the last index survives `makeObjStack` unchanged, at the same index.
theorem makeObjStack_frame_mem_up {cfg cfg' : RuntimeConfig} (h : makeObjStack x cfg = some cfg')
    {frame : FrameWithIndex} (hframe : frame ∈ cfg.stackWithIndex) (hlt : frame.index < cfg.stack.length - 1) :
    frame ∈ cfg'.stackWithIndex := by
  obtain ⟨lastFrame, hlast, rfl⟩ := makeObjStack_cases h
  rw [stackWithIndex_eq_of_getLast? hlast] at hframe
  rw [stackWithIndex_mk_append_singleton]
  rcases List.mem_append.mp hframe with hmem | hmem
  · exact List.mem_append_left _ hmem
  · rw [List.mem_singleton.mp hmem, List.length_dropLast] at hlt
    exact absurd hlt (lt_irrefl _)

-- `FrameRoot` at an index below the last frame agrees between `cfg`/`cfg'`.
private theorem makeObjStack_root_iff {cfg cfg' : RuntimeConfig} (h : makeObjStack x cfg = some cfg')
    {i : Index} (hi : i < cfg.stack.length - 1) (start : Reference) :
    FrameRoot cfg i start ↔ FrameRoot cfg' i start := by
  have hdown : ∀ {f : FrameWithIndex}, f ∈ cfg'.stackWithIndex → f.index = i → f ∈ cfg.stackWithIndex :=
    fun hf hfi => by
      obtain ⟨lastFrame, hlast, hcfg'⟩ := makeObjStack_cases h
      rcases makeObjStack_frame_cases hlast hcfg' hf with ⟨hm, -⟩ | ⟨-, -, -, -, hidx⟩
      · exact hm
      · rw [← hfi, hidx, List.length_dropLast] at hi
        exact absurd hi (lt_irrefl _)
  obtain ⟨lastFrame, hlast, rfl⟩ := makeObjStack_cases h
  constructor
  · rintro (⟨f, hf, hfi, hv⟩ | ⟨f, hf, hfi, hr⟩)
    · exact .inl ⟨f, makeObjStack_frame_mem_up h hf (hfi ▸ hi), hfi, hv⟩
    · exact .inr ⟨f, makeObjStack_frame_mem_up h hf (hfi ▸ hi), hfi, hr⟩
  · rintro (⟨f, hf, hfi, hv⟩ | ⟨f, hf, hfi, hr⟩)
    · exact .inl ⟨f, hdown hf hfi, hfi, hv⟩
    · exact .inr ⟨f, hdown hf hfi, hfi, hr⟩

-- `FrameReachable` agrees below the last frame (content is literally untouched there).
theorem makeObjStack_frame_reachable_iff {cfg cfg' : RuntimeConfig} (h : makeObjStack x cfg = some cfg')
    {X : FrameWithIndex} (_hXmem : X ∈ cfg.stackWithIndex) (hXlt : X.index < cfg.stack.length - 1)
    (ref : Reference) : FrameReachable cfg X.index ref ↔ FrameReachable cfg' X.index ref := by
  simp only [FrameReachable_iff_reflTransGen, makeObjStack_step_eq h, makeObjStack_root_iff h hXlt]

-- A fresh object id never resolves into any region (it isn't allocated yet).
theorem freshObjectId_loc_ne_rgn {cfg : RuntimeConfig} {rid : RegionId} :
    (Reference.OId cfg.freshObjectId).loc? cfg ≠ some (Location.Rgn rid) := by
  simp [freshObjectId_loc_none]

-- A `cfg'` frame root is either the fresh object (via `x`) or already a `cfg` root.
private theorem makeObjStack_root_down {cfg cfg' : RuntimeConfig} (h : makeObjStack x cfg = some cfg')
    {fid : Index} {start : Reference} (hr : FrameRoot cfg' fid start) :
    start = .OId cfg.freshObjectId ∨ FrameRoot cfg fid start := by
  obtain ⟨L, hL, rfl⟩ := makeObjStack_cases h
  have hLm := stackWithIndex_getLast_mem hL
  rcases hr with ⟨S, hS, rfl, v, hv⟩ | ⟨S, hS, rfl, region, hl, rfl⟩ <;>
    rcases makeObjStack_frame_cases hL rfl hS with ⟨hS, -⟩ | ⟨hrid, -, hvm, -, hi⟩
  · exact .inr (.inl ⟨S, hS, rfl, v, hv⟩)
  · rw [hvm] at hv
    by_cases hvx : v = x
    · subst hvx
      simp at hv
      exact .inl hv.symm
    · rw [AList.lookup_insert_ne hvx] at hv
      exact .inr (.inl ⟨_, hLm, by simp [hi], v, hv⟩)
  · exact .inr (.inr ⟨S, hS, rfl, region, hl, rfl⟩)
  · exact .inr (.inr ⟨_, hLm, by simp [hi], region, hrid ▸ hl, rfl⟩)

-- Reachability of a non-fresh object from any `cfg'` frame is stack-reachability in `cfg`.
private theorem makeObjStack_reach_down {cfg cfg' : RuntimeConfig} (h : makeObjStack x cfg = some cfg')
    {oid : ObjectId} (hne : oid ≠ cfg.freshObjectId) {fid : Index} (hr : FrameReachable cfg' fid (.OId oid)) :
    StackReachable cfg (.OId oid) := by
  obtain ⟨start, hs, hc⟩ := (FrameReachable_iff_reflTransGen ..).mp hr
  rw [← makeObjStack_step_eq h] at hc
  rcases makeObjStack_root_down h hs with rfl | hs
  · rcases hc.cases_head with he | ⟨c, ⟨obj, ho, -⟩, -⟩
    · exact absurd (Reference.OId.inj he).symm hne
    · simp [freshObjectId_objAt_none] at ho
  · exact StackReachable_of_root hs hc

-- For `oid` in a suspended frame `F`'s region, makeObjStack neither creates nor destroys its reachability from `F`.
theorem makeObjStack_suspended_reach {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeObjStack x cfg = some cfg') (hFR3 : FrameReachable_at_later_frame_implies_FrameReachable_at_frame cfg)
    {F : FrameWithIndex} (hF : F ∈ cfg.stackWithIndex) (hFlt : F.index < cfg.stackWithIndex.length - 1)
    {oid : ObjectId} (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn F.regionId)) :
    F ∈ cfg'.stackWithIndex ∧ (StackReachable cfg (.OId oid) → FrameReachable cfg' F.index (.OId oid)) ∧
    ∀ fid, FrameReachable cfg' fid (.OId oid) → StackReachable cfg (.OId oid) := by
  have hFlt' : F.index < cfg.stack.length - 1 := by simpa [RuntimeConfig.stackWithIndex] using hFlt
  exact ⟨makeObjStack_frame_mem_up h hF hFlt', fun hs => (makeObjStack_frame_reachable_iff h hF hFlt' _).mp
    (FrameReachable_of_StackReachable vcfg hFR3 hF hloc hs), fun _ => makeObjStack_reach_down h (fun he => freshObjectId_loc_ne_rgn (he ▸ hloc))⟩
