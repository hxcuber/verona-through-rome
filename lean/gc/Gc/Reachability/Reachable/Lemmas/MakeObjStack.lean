import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Mutation.Mutation
import Gc.Model.Preservation
import Gc.Reachability.Reachable.Semantics
import Gc.Reachability.Reachable.Lemmas.Common

-- The freshly-allocated object id is never already present in the last frame's own objMap.
theorem makeObjStack_fresh_not_in_last {cfg : RuntimeConfig} {lastFrame : Frame}
    (hlast : cfg.stack.getLast? = some lastFrame) : cfg.freshObjectId ∉ lastFrame.objMap.keys := by
  intro hmem
  apply cfg.freshObjectId_not_mem
  unfold RuntimeConfig.objectIds
  rw [List.mem_append]
  left
  unfold Stack.objectIds
  rw [List.bind_eq_flatMap, List.mem_flatMap]
  have hmemStack : lastFrame ∈ cfg.stack := by
    have hne : cfg.stack ≠ [] := by intro hnil; rw [hnil] at hlast; simp at hlast
    rw [List.getLast?_eq_getLast_of_ne_nil hne, Option.some_inj] at hlast
    rw [← hlast]
    exact List.getLast_mem hne
  exact ⟨lastFrame.objectIds, List.mem_map_of_mem hmemStack, hmem⟩

-- `loc?` agrees between `cfg`/`cfg'` for any oid other than the freshly-allocated one.
theorem makeObjStack_loc_eq_of_ne {cfg cfg' : RuntimeConfig} (h : makeObjStack x cfg = some cfg')
    {oid : ObjectId} (hne : oid ≠ cfg.freshObjectId) :
    (Reference.OId oid).loc? cfg = (Reference.OId oid).loc? cfg' := by
  obtain ⟨lastFrame, hlast, hcfg'⟩ := makeObjStack_cases h
  have hfreshNotIn : cfg.freshObjectId ∉ lastFrame.objMap.keys := makeObjStack_fresh_not_in_last hlast
  have hkeq : (lastFrame.objMap.insert cfg.freshObjectId ∅).keys.contains oid = lastFrame.objMap.keys.contains oid := by
    rw [AList.keys_insert, List.erase_of_not_mem hfreshNotIn]
    simp only [List.contains_cons]
    have : (oid == cfg.freshObjectId) = false := by simpa using hne
    rw [this]
    simp
  have hne' : cfg.stack ≠ [] := by intro hnil; rw [hnil] at hlast; simp at hlast
  have hstackEq : cfg.stack = cfg.stack.dropLast ++ [lastFrame] := by
    rw [List.getLast?_eq_getLast_of_ne_nil hne', Option.some_inj] at hlast
    rw [← hlast]
    exact (List.dropLast_append_getLast hne').symm
  set newLastWI : FrameWithIndex := { lastFrame with
      varMap := lastFrame.varMap.insert x (Reference.OId cfg.freshObjectId),
      objMap := lastFrame.objMap.insert cfg.freshObjectId ∅,
      index := cfg.stack.dropLast.length } with hnewLastWI_def
  set oldLastWI : FrameWithIndex := { lastFrame with index := cfg.stack.dropLast.length } with holdLastWI_def
  set revTail : List FrameWithIndex :=
      (List.mapIdx (fun idx frame => ({ toFrame := frame, index := idx } : FrameWithIndex))
        cfg.stack.dropLast).reverse with hrevTail_def
  set pred : FrameWithIndex → Bool := fun frame => frame.objMap.keys.contains oid with hpred_def
  have hstackFindEq :
      (List.find? pred (newLastWI :: revTail)).map FrameWithIndex.index =
      (List.find? pred (oldLastWI :: revTail)).map FrameWithIndex.index := by
    have hnewval : pred newLastWI = pred oldLastWI := by
      rw [hnewLastWI_def, holdLastWI_def, hpred_def]
      exact hkeq
    cases hval : pred oldLastWI with
    | true =>
      have h1 : List.find? pred (newLastWI :: revTail) = some newLastWI :=
        List.find?_cons_of_pos (hnewval.trans hval)
      have h2 : List.find? pred (oldLastWI :: revTail) = some oldLastWI :=
        List.find?_cons_of_pos hval
      rw [h1, h2]
      rfl
    | false =>
      have h1 : List.find? pred (newLastWI :: revTail) = List.find? pred revTail :=
        List.find?_cons_of_neg (by rw [hnewval, hval]; decide)
      have h2 : List.find? pred (oldLastWI :: revTail) = List.find? pred revTail :=
        List.find?_cons_of_neg (by rw [hval]; decide)
      rw [h1, h2]
  unfold Reference.loc?
  dsimp only
  subst hcfg'
  unfold RuntimeConfig.stackWithIndex
  dsimp only
  conv_lhs => rw [hstackEq]
  rw [List.mapIdx_concat, List.mapIdx_concat]
  rw [List.findRev?_eq_find?_reverse, List.findRev?_eq_find?_reverse]
  rw [List.reverse_append, List.reverse_append, List.reverse_singleton, List.reverse_singleton]
  rw [List.singleton_append, List.singleton_append]
  cases hval1 : List.find? pred (oldLastWI :: revTail) with
  | none =>
    have hval2 : List.find? pred (newLastWI :: revTail) = none := by
      have := hstackFindEq
      rw [hval1] at this
      cases hval3 : List.find? pred (newLastWI :: revTail) with
      | none => rfl
      | some fr => rw [hval3] at this; simp at this
    rw [hval2]
  | some fr1 =>
    have hval2 : ∃ fr2, List.find? pred (newLastWI :: revTail) = some fr2 ∧ fr2.index = fr1.index := by
      have := hstackFindEq
      rw [hval1] at this
      cases hval3 : List.find? pred (newLastWI :: revTail) with
      | none => rw [hval3] at this; simp at this
      | some fr2 => rw [hval3] at this; simp at this; exact ⟨fr2, rfl, this⟩
    obtain ⟨fr2, hfr2, hidxeq⟩ := hval2
    rw [hfr2]
    cases cfg.heap.entries.find? (fun (e : Sigma (fun _ : RegionId => Region)) => e.snd.objMap.keys.contains oid) with
    | none => dsimp only; rw [hidxeq]
    | some _ => dsimp only

-- `objAt?` agrees between `cfg`/`cfg'` for any oid other than the freshly-allocated one.
theorem makeObjStack_objAt_eq_of_ne {cfg cfg' : RuntimeConfig} (h : makeObjStack x cfg = some cfg')
    {oid : ObjectId} (hne : oid ≠ cfg.freshObjectId) :
    (Reference.OId oid).objAt? cfg = (Reference.OId oid).objAt? cfg' := by
  obtain ⟨lastFrame, hlast, hcfg'⟩ := makeObjStack_cases h
  have hlocEq := makeObjStack_loc_eq_of_ne h hne
  unfold Reference.objAt?
  dsimp only
  rw [hlocEq]
  cases hloc' : (Reference.OId oid).loc? cfg' with
  | none => rfl
  | some loc =>
    cases loc with
    | Rgn rid0 => dsimp only; subst hcfg'; rfl
    | Stk fid0 =>
      dsimp only
      rw [stackWithIndex_find_index_eq_getElem, stackWithIndex_find_index_eq_getElem]
      have hne' : cfg.stack ≠ [] := by intro hnil; rw [hnil] at hlast; simp at hlast
      have hstackEq : cfg.stack = cfg.stack.dropLast ++ [lastFrame] := by
        rw [List.getLast?_eq_getLast_of_ne_nil hne', Option.some_inj] at hlast
        rw [← hlast]; exact (List.dropLast_append_getLast hne').symm
      have hgetCfg : cfg.stackWithIndex[fid0]? =
          (cfg.stack[fid0]?).map (fun f => ({ toFrame := f, index := fid0 } : FrameWithIndex)) := by
        unfold RuntimeConfig.stackWithIndex; rw [List.getElem?_mapIdx]
      have hgetCfg' : cfg'.stackWithIndex[fid0]? =
          (cfg'.stack[fid0]?).map (fun f => ({ toFrame := f, index := fid0 } : FrameWithIndex)) := by
        unfold RuntimeConfig.stackWithIndex; rw [List.getElem?_mapIdx]
      rw [hgetCfg, hgetCfg']
      by_cases hfid : fid0 < cfg.stack.dropLast.length
      · have h1 : cfg.stack[fid0]? = cfg.stack.dropLast[fid0]? := by
          conv_lhs => rw [hstackEq]
          rw [List.getElem?_append_left hfid]
        have h2 : cfg'.stack[fid0]? = cfg.stack.dropLast[fid0]? := by
          rw [hcfg']; dsimp only
          rw [List.getElem?_append_left hfid]
        rw [h1, h2]
      · push_neg at hfid
        set newLastFrame : Frame := { regionId := lastFrame.regionId, bridgeVar := lastFrame.bridgeVar, objMap := lastFrame.objMap.insert cfg.freshObjectId ∅, varMap := lastFrame.varMap.insert x (Reference.OId cfg.freshObjectId) } with hnewLastFrame_def
        have h1 : cfg.stack[fid0]? = [lastFrame][fid0 - cfg.stack.dropLast.length]? := by
          conv_lhs => rw [hstackEq]
          rw [List.getElem?_append_right hfid]
        have h2 : cfg'.stack[fid0]? = [newLastFrame][fid0 - cfg.stack.dropLast.length]? := by
          rw [hcfg']; dsimp only
          rw [List.getElem?_append_right hfid]
        rw [h1, h2]
        cases hidx : fid0 - cfg.stack.dropLast.length with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.map_some]
          rw [hnewLastFrame_def]
          dsimp only [Option.bind]
          rw [AList.lookup_insert_ne hne]
        | succ n => rfl

-- A fresh object id never resolves to any location (it isn't allocated yet).
theorem freshObjectId_loc_none {cfg : RuntimeConfig} :
    (Reference.OId cfg.freshObjectId).loc? cfg = none := by
  have hnotmem := cfg.freshObjectId_not_mem
  unfold RuntimeConfig.objectIds at hnotmem
  rw [List.mem_append] at hnotmem
  push_neg at hnotmem
  obtain ⟨hnotStack, hnotHeap⟩ := hnotmem
  unfold Reference.loc?
  dsimp only
  cases hh : cfg.stackWithIndex.findRev? (fun frame => frame.objMap.keys.contains cfg.freshObjectId) with
  | some frame =>
    exfalso
    apply hnotStack
    unfold Stack.objectIds
    rw [List.bind_eq_flatMap, List.mem_flatMap]
    rw [List.findRev?_eq_find?_reverse] at hh
    have hcontains := List.find?_some hh
    have hmem : frame ∈ cfg.stackWithIndex := List.mem_reverse.mp (List.mem_of_find?_eq_some hh)
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hmem
    have hmemStack : cfg.stack[n] ∈ cfg.stack := List.getElem_mem hn
    have hfeq2 : frame.objMap = cfg.stack[n].objMap := congrArg (·.objMap) hfeq.symm
    refine ⟨cfg.stack[n].objectIds, List.mem_map_of_mem hmemStack, ?_⟩
    unfold Frame.objectIds
    rw [← hfeq2]
    exact List.contains_iff_mem.mp hcontains
  | none =>
    cases hh2 : cfg.heap.entries.find? (fun (e : Sigma (fun _ : RegionId => Region)) => e.snd.objMap.keys.contains cfg.freshObjectId) with
    | none => rfl
    | some regionEntry =>
      exfalso
      apply hnotHeap
      unfold Heap.objectIds
      rw [List.mem_flatten]
      have hcontains := List.find?_some hh2
      refine ⟨regionEntry.snd.objectIds, List.mem_map_of_mem (List.mem_of_find?_eq_some hh2), ?_⟩
      unfold Region.objectIds
      exact List.contains_iff_mem.mp hcontains

-- A fresh object id never resolves anywhere (it isn't allocated yet).
theorem freshObjectId_objAt_none {cfg : RuntimeConfig} :
    (Reference.OId cfg.freshObjectId).objAt? cfg = none := by
  unfold Reference.objAt?
  dsimp only
  rw [freshObjectId_loc_none]

-- The freshly-allocated object resolves to its own (empty) content in cfg'.
theorem makeObjStack_fresh_objAt_cfg' {cfg cfg' : RuntimeConfig} (h : makeObjStack x cfg = some cfg') :
    (Reference.OId cfg.freshObjectId).objAt? cfg' = some (∅ : Object) := by
  obtain ⟨lastFrame, hlast, hcfg'⟩ := makeObjStack_cases h
  have hnotmem := cfg.freshObjectId_not_mem
  unfold RuntimeConfig.objectIds at hnotmem
  rw [List.mem_append] at hnotmem
  push_neg at hnotmem
  obtain ⟨-, hnotHeap⟩ := hnotmem
  have hne' : cfg.stack ≠ [] := by intro hnil; rw [hnil] at hlast; simp at hlast
  have hstackEq : cfg.stack = cfg.stack.dropLast ++ [lastFrame] := by
    rw [List.getLast?_eq_getLast_of_ne_nil hne', Option.some_inj] at hlast
    rw [← hlast]; exact (List.dropLast_append_getLast hne').symm
  have hheapNone : cfg.heap.entries.find?
      (fun (e : Sigma (fun _ : RegionId => Region)) => e.snd.objMap.keys.contains cfg.freshObjectId) = none := by
    rw [List.find?_eq_none]
    intro entry hentry hcontra
    apply hnotHeap
    unfold Heap.objectIds
    rw [List.mem_flatten]
    refine ⟨entry.snd.objectIds, List.mem_map_of_mem hentry, ?_⟩
    unfold Region.objectIds
    exact List.contains_iff_mem.mp hcontra
  have hcontainsNew : (lastFrame.objMap.insert cfg.freshObjectId ∅).keys.contains cfg.freshObjectId = true := by
    rw [AList.keys_insert]
    simp
  set dropLastLen : Nat := cfg.stack.dropLast.length with hdropLastLen_def
  set newLastFrame : Frame := { regionId := lastFrame.regionId, bridgeVar := lastFrame.bridgeVar, objMap := lastFrame.objMap.insert cfg.freshObjectId ∅, varMap := lastFrame.varMap.insert x (Reference.OId cfg.freshObjectId) } with hnewLastFrame_def
  have hloc' : (Reference.OId cfg.freshObjectId).loc? cfg' = some (Location.Stk dropLastLen) := by
    unfold Reference.loc?
    dsimp only
    rw [hcfg']
    dsimp only
    rw [hheapNone]
    unfold RuntimeConfig.stackWithIndex
    dsimp only
    rw [List.mapIdx_concat, List.findRev?_eq_find?_reverse, List.reverse_append,
      List.reverse_singleton, List.singleton_append]
    have hcontainsNew' : newLastFrame.objMap.keys.contains cfg.freshObjectId = true := hcontainsNew
    have hfindEq : List.find? (fun (frame : FrameWithIndex) => frame.objMap.keys.contains cfg.freshObjectId)
        (({ toFrame := newLastFrame, index := dropLastLen } : FrameWithIndex) ::
          (List.mapIdx (fun idx frame => ({ toFrame := frame, index := idx } : FrameWithIndex)) cfg.stack.dropLast).reverse) =
        some { toFrame := newLastFrame, index := dropLastLen } :=
      List.find?_cons_of_pos hcontainsNew'
    rw [hfindEq]
  unfold Reference.objAt?
  dsimp only
  rw [hloc']
  dsimp only
  have hmemNew : ({ toFrame := newLastFrame, index := dropLastLen } : FrameWithIndex) ∈ cfg'.stackWithIndex := by
    rw [hcfg']
    unfold RuntimeConfig.stackWithIndex
    dsimp only
    apply List.mem_mapIdx.mpr
    refine ⟨dropLastLen, by rw [hdropLastLen_def]; simp, ?_⟩
    dsimp only
    rw [List.getElem_append_right (by rw [hdropLastLen_def])]
    simp [hdropLastLen_def]
  have hfind : cfg'.stackWithIndex.find? (fun frame => frame.index == dropLastLen) =
      some { toFrame := newLastFrame, index := dropLastLen } :=
    swap_corollary_stackWithIndex_find_eq hmemNew
  rw [hfind]
  have hlookupNew : newLastFrame.objMap.lookup cfg.freshObjectId = some (∅ : Object) := by
    rw [hnewLastFrame_def]
    dsimp only
    rw [AList.lookup_insert]
  exact hlookupNew

-- `ReachableStep` agrees for every oid: a hop from the fresh id is vacuous both sides (unresolved in `cfg`, empty object in `cfg'`).
theorem makeObjStack_oid_step_iff {cfg cfg' : RuntimeConfig} (h : makeObjStack x cfg = some cfg')
    (oid : ObjectId) (b : Reference) :
    ReachableStep cfg (Reference.OId oid) b ↔ ReachableStep cfg' (Reference.OId oid) b := by
  by_cases hne : oid = cfg.freshObjectId
  · subst hne
    constructor
    · intro hstep
      rw [ReachableStep_oid_iff] at hstep
      obtain ⟨obj, hobjAt, -⟩ := hstep
      rw [freshObjectId_objAt_none] at hobjAt
      exact absurd hobjAt (by simp)
    · intro hstep
      rw [ReachableStep_oid_iff] at hstep
      obtain ⟨obj, hobjAt, hcontains⟩ := hstep
      rw [makeObjStack_fresh_objAt_cfg' h] at hobjAt
      injection hobjAt with hobjAt
      rw [← hobjAt] at hcontains
      simp [Object.refs] at hcontains
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
  have hne' : cfg.stack ≠ [] := by intro hnil; rw [hnil] at hlast; simp at hlast
  have hstackEq : cfg.stack = cfg.stack.dropLast ++ [lastFrame] := by
    rw [List.getLast?_eq_getLast_of_ne_nil hne', Option.some_inj] at hlast
    rw [← hlast]; exact (List.dropLast_append_getLast hne').symm
  unfold RuntimeConfig.stackWithIndex at hframe
  rw [hcfg'] at hframe
  dsimp only at hframe
  rw [List.mapIdx_concat] at hframe
  rcases List.mem_append.mp hframe with hmem | hmem
  · left
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hmem
    have hidx : frame.index = n := by rw [← hfeq]
    have hmem' : frame ∈ cfg.stackWithIndex := by
      unfold RuntimeConfig.stackWithIndex
      conv_lhs => rw [hstackEq]
      rw [List.mapIdx_concat]
      exact List.mem_append_left _ hmem
    refine ⟨hmem', ?_⟩
    rw [hidx, ← List.length_dropLast]
    exact hn
  · right
    rw [List.mem_singleton] at hmem
    subst hmem
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

-- A pre-existing frame below the last index survives `makeObjStack` unchanged, at the same index.
theorem makeObjStack_frame_mem_up {cfg cfg' : RuntimeConfig} (h : makeObjStack x cfg = some cfg')
    {frame : FrameWithIndex} (hframe : frame ∈ cfg.stackWithIndex) (hlt : frame.index < cfg.stack.length - 1) :
    frame ∈ cfg'.stackWithIndex := by
  obtain ⟨lastFrame, hlast, hcfg'⟩ := makeObjStack_cases h
  unfold RuntimeConfig.stackWithIndex at hframe ⊢
  rw [hcfg']
  dsimp only
  obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hframe
  have hidx : frame.index = n := by rw [← hfeq]
  have hnlt : n < cfg.stack.dropLast.length := by rw [List.length_dropLast]; rw [hidx] at hlt; exact hlt
  apply List.mem_mapIdx.mpr
  refine ⟨n, ?_, ?_⟩
  · rw [List.length_append]; omega
  · rw [List.getElem_append_left hnlt, List.getElem_dropLast hnlt]
    exact hfeq

-- `ReachableStep` agrees unconditionally: `makeObjStack` never touches the heap, so `RId`-sourced steps agree trivially too.
theorem makeObjStack_step_eq {cfg cfg' : RuntimeConfig} (h : makeObjStack x cfg = some cfg') :
    ReachableStep cfg = ReachableStep cfg' := by
  obtain ⟨lastFrame, hlast, hcfg'⟩ := makeObjStack_cases h
  funext a b
  apply propext
  cases a with
  | OId oid => exact makeObjStack_oid_step_iff h oid b
  | RId rid =>
    rw [ReachableStep_rid_iff, ReachableStep_rid_iff]
    rw [hcfg']

-- `FrameReachable` agrees below the last frame (content is literally untouched there).
theorem makeObjStack_frame_reachable_iff {cfg cfg' : RuntimeConfig} (h : makeObjStack x cfg = some cfg')
    {X : FrameWithIndex} (_hXmem : X ∈ cfg.stackWithIndex) (hXlt : X.index < cfg.stack.length - 1)
    (ref : Reference) : FrameReachable cfg X.index ref ↔ FrameReachable cfg' X.index ref := by
  obtain ⟨lastFrame, hlast, hcfg'⟩ := makeObjStack_cases h
  rw [FrameReachable_iff_reflTransGen, FrameReachable_iff_reflTransGen, makeObjStack_step_eq h]
  constructor
  · rintro ⟨start, hroot, hrtg⟩
    refine ⟨start, ?_, hrtg⟩
    rcases hroot with ⟨Xf, hXfmem, hXfidx, var, hvar⟩ | ⟨Xf, hXfmem, hXfidx, region, hlookup, hbridge⟩
    · exact Or.inl ⟨Xf, makeObjStack_frame_mem_up h hXfmem (hXfidx ▸ hXlt), hXfidx, var, hvar⟩
    · have hlookup' : cfg'.heap.lookup Xf.regionId = some region := by rw [hcfg']; exact hlookup
      exact Or.inr ⟨Xf, makeObjStack_frame_mem_up h hXfmem (hXfidx ▸ hXlt), hXfidx, region, hlookup', hbridge⟩
  · rintro ⟨start, hroot, hrtg⟩
    refine ⟨start, ?_, hrtg⟩
    rcases hroot with ⟨Xf, hXfmem, hXfidx, var, hvar⟩ | ⟨Xf, hXfmem, hXfidx, region, hlookup, hbridge⟩
    · rcases makeObjStack_frame_cases hlast hcfg' hXfmem with ⟨hXfmemcfg, -⟩ | ⟨-, -, -, -, hXfidx2⟩
      · exact Or.inl ⟨Xf, hXfmemcfg, hXfidx, var, hvar⟩
      · exfalso
        have hXeq : X.index = cfg.stack.dropLast.length := by rw [← hXfidx, hXfidx2]
        rw [hXeq, List.length_dropLast] at hXlt
        exact absurd hXlt (lt_irrefl _)
    · rcases makeObjStack_frame_cases hlast hcfg' hXfmem with ⟨hXfmemcfg, -⟩ | ⟨-, -, -, -, hXfidx2⟩
      · have hlookup' : cfg.heap.lookup Xf.regionId = some region := by rw [hcfg'] at hlookup; exact hlookup
        exact Or.inr ⟨Xf, hXfmemcfg, hXfidx, region, hlookup', hbridge⟩
      · exfalso
        have hXeq : X.index = cfg.stack.dropLast.length := by rw [← hXfidx, hXfidx2]
        rw [hXeq, List.length_dropLast] at hXlt
        exact absurd hXlt (lt_irrefl _)


-- A fresh object id never resolves into any region (it isn't allocated yet).
theorem freshObjectId_loc_ne_rgn {cfg : RuntimeConfig} {rid : RegionId} :
    (Reference.OId cfg.freshObjectId).loc? cfg ≠ some (Location.Rgn rid) := by
  rw [freshObjectId_loc_none]
  simp

-- The stack's own last frame, reindexed as a `FrameWithIndex`, is a member of `stackWithIndex`.
theorem stackWithIndex_getLast_mem {cfg : RuntimeConfig} {lastFrame : Frame}
    (hlast : cfg.stack.getLast? = some lastFrame) :
    ({ lastFrame with index := cfg.stack.length - 1 } : FrameWithIndex) ∈ cfg.stackWithIndex := by
  have hne : cfg.stack ≠ [] := by intro hnil; rw [hnil] at hlast; simp at hlast
  have hlen1 : 1 ≤ cfg.stack.length := List.length_pos_of_ne_nil hne
  have hget : cfg.stack[cfg.stack.length - 1] = lastFrame := by
    rw [List.getLast?_eq_getLast_of_ne_nil hne, Option.some_inj] at hlast
    rw [← hlast, List.getLast_eq_getElem hne]
  unfold RuntimeConfig.stackWithIndex
  apply List.mem_mapIdx.mpr
  refine ⟨cfg.stack.length - 1, by omega, ?_⟩
  rw [hget]
