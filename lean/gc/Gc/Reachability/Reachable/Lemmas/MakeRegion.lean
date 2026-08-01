import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Mutation.Mutation
import Gc.Model.Preservation
import Gc.Reachability.Reachable.Semantics
import Gc.Reachability.Reachable.Basic
import Gc.Reachability.Reachable.Lemmas.Common
import Gc.Reachability.Reachable.Lemmas.MakeObjStack
import Gc.Reachability.Reachable.Lemmas.Merge

-- ===== makeRegion =====

-- A step sourced at the freshly-allocated region id is always impossible (the region doesn't exist yet, so `deref?`'s heap lookup guard fails).
theorem freshRegionId_no_step {cfg : RuntimeConfig} {b : Reference} :
    ¬ ReachableStep cfg (Reference.RId cfg.freshRegionId) b := by
  rw [ReachableStep_rid_iff]
  rintro ⟨region, hlookup, -, -⟩
  apply RuntimeConfig.freshRegionId_not_mem cfg
  rw [← AList.mem_keys, ← AList.lookup_isSome, hlookup]
  simp

-- The freshly-created region's bridge object resolves into the heap at the fresh region id (never onto the stack).
theorem makeRegion_corollary_loc_fresh {cfg cfg' : RuntimeConfig} {x : VarName}
    (h : makeRegion x cfg = some cfg') :
    (Reference.OId cfg.freshObjectId).loc? cfg' = some (Location.Rgn cfg.freshRegionId) := by
  obtain ⟨frame, hlast, hcfg'⟩ := makeRegion_cases h
  have fresh_not_in_any_frame : ∀ f ∈ cfg.stack, cfg.freshObjectId ∉ f.objMap.keys := by
    intro f hf hmem
    apply RuntimeConfig.freshObjectId_not_mem cfg
    unfold RuntimeConfig.objectIds Stack.objectIds Frame.objectIds
    rw [List.bind_eq_flatMap, List.flatMap_id, List.mem_append, List.mem_flatten]
    exact Or.inl ⟨f.objMap.keys, List.mem_map_of_mem hf, hmem⟩
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
    (List.dropLast_append_getLast? frame hlast).symm
  have frame_mem : frame ∈ cfg.stack := stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self frame)
  set newFrame : Frame :=
    { regionId := frame.regionId, bridgeVar := frame.bridgeVar, objMap := frame.objMap,
      varMap := frame.varMap.insert x (Reference.RId cfg.freshRegionId) } with newFrame_def
  set newRegionVal : Region :=
    { bridgeObjectId := cfg.freshObjectId, objMap := (∅ : ObjMap).insert cfg.freshObjectId ∅,
      status := Status.Closed } with newRegionVal_def
  have dropLast_h1_none :
      List.find? (fun f => (AList.keys f.objMap).contains cfg.freshObjectId)
        (List.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex))
          cfg.stack.dropLast).reverse = none := by
    rw [List.find?_eq_none]
    intro f hf
    rw [List.mem_reverse] at hf
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hf
    intro hc
    apply fresh_not_in_any_frame cfg.stack.dropLast[n]
      (List.mem_of_mem_dropLast (List.mem_iff_getElem.mpr ⟨n, hn, rfl⟩))
    rw [← hfeq] at hc
    dsimp at hc
    exact List.contains_iff_mem.mp hc
  have h1_none :
      cfg'.stackWithIndex.findRev?
        (fun f => (AList.keys f.objMap).contains cfg.freshObjectId) = none := by
    rw [hcfg']
    unfold RuntimeConfig.stackWithIndex
    dsimp
    rw [List.mapIdx_concat, List.findRev?_eq_find?_reverse, List.reverse_append,
      List.reverse_singleton, List.singleton_append]
    have hnewFrame_false : ¬ (AList.keys ({ newFrame with
          index := cfg.stack.dropLast.length } : FrameWithIndex).objMap).contains
        cfg.freshObjectId = true := by
      dsimp
      intro hc
      exact fresh_not_in_any_frame frame frame_mem (List.contains_iff_mem.mp hc)
    have find_eq :
        List.find? (fun f => (AList.keys f.objMap).contains cfg.freshObjectId)
          (({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex) ::
            (List.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex))
              cfg.stack.dropLast).reverse) =
        List.find? (fun f => (AList.keys f.objMap).contains cfg.freshObjectId)
          (List.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex))
            cfg.stack.dropLast).reverse :=
      List.find?_cons_of_neg hnewFrame_false
    rw [find_eq, dropLast_h1_none]
  have h2_some :
      cfg'.heap.entries.find?
        (fun p => (AList.keys p.snd.objMap).contains cfg.freshObjectId) =
      some (⟨cfg.freshRegionId, newRegionVal⟩ : Sigma (fun _ : RegionId => Region)) := by
    rw [hcfg']
    dsimp
    rw [List.kerase_of_notMem_keys (RuntimeConfig.freshRegionId_not_mem cfg)]
    have hpos : (AList.keys newRegionVal.objMap).contains cfg.freshObjectId = true := by
      rw [newRegionVal_def]
      dsimp
      simp
    exact List.find?_cons_of_pos hpos
  unfold Reference.loc?
  dsimp
  rw [h1_none, h2_some]

-- `objAt?` agrees between `cfg`/`cfg'` for `oid ≠ freshObjectId`: fresh heap key insert, unconditional stack side (only `varMap` changes).
theorem makeRegion_objAt_eq_of_ne {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeRegion x cfg = some cfg') {oid : ObjectId} (hne : oid ≠ cfg.freshObjectId) :
    (Reference.OId oid).objAt? cfg = (Reference.OId oid).objAt? cfg' := by
  obtain ⟨frame, hlast, hcfg'⟩ := makeRegion_cases h
  have hlocEq := makeRegion_corollary_loc_eq vcfg h oid hne
  unfold Reference.objAt?
  dsimp only
  rw [hlocEq]
  cases hloc' : (Reference.OId oid).loc? cfg' with
  | none => rfl
  | some loc =>
    cases loc with
    | Rgn rid0 =>
      dsimp only
      have hlocCfg : (Reference.OId oid).loc? cfg = some (Location.Rgn rid0) := by rw [hlocEq]; exact hloc'
      obtain ⟨regionR, hlookupR, -⟩ := (oid_loc_rgn_iff_in_heap vcfg).mp hlocCfg
      have hne' : rid0 ≠ cfg.freshRegionId := by
        intro heq
        apply RuntimeConfig.freshRegionId_not_mem cfg
        rw [← AList.mem_keys, ← AList.lookup_isSome, ← heq, hlookupR]
        simp
      have hlookup' : cfg'.heap.lookup rid0 = cfg.heap.lookup rid0 := by
        rw [hcfg']; dsimp only; rw [AList.lookup_insert_ne hne']
      rw [hlookup']
    | Stk fid0 =>
      dsimp only
      rw [stackWithIndex_find_index_eq_getElem, stackWithIndex_find_index_eq_getElem]
      have hshape := stackWithIndex_objMap_get_eq_of_last_varMap_update (cfg' := cfg') hlast (by rw [hcfg'])
      have hgetCfg : cfg.stackWithIndex[fid0]? =
          (cfg.stack[fid0]?).map (fun f => ({ toFrame := f, index := fid0 } : FrameWithIndex)) := by
        unfold RuntimeConfig.stackWithIndex; rw [List.getElem?_mapIdx]
      have hgetCfg' : cfg'.stackWithIndex[fid0]? =
          (cfg'.stack[fid0]?).map (fun f => ({ toFrame := f, index := fid0 } : FrameWithIndex)) := by
        unfold RuntimeConfig.stackWithIndex; rw [List.getElem?_mapIdx]
      rw [hgetCfg, hgetCfg']
      cases hc : cfg.stack[fid0]? with
      | none =>
        have hc' : cfg'.stack[fid0]? = none := by
          have hs := hshape fid0; rw [hc] at hs; simpa using hs.symm
        rw [hc']
      | some fA =>
        cases hc' : cfg'.stack[fid0]? with
        | none => have hs := hshape fid0; rw [hc, hc'] at hs; simp at hs
        | some fB =>
          have hobjmapEq : fA.objMap = fB.objMap := by
            have hs := hshape fid0; rw [hc, hc'] at hs; simpa using hs
          simp only [Option.map_some]
          dsimp only [Option.bind]
          rw [hobjmapEq]

-- The freshly-allocated object resolves to its own (empty) content in cfg'.
theorem makeRegion_fresh_objAt_cfg' {cfg cfg' : RuntimeConfig} {x : VarName}
    (h : makeRegion x cfg = some cfg') :
    (Reference.OId cfg.freshObjectId).objAt? cfg' = some (∅ : Object) := by
  have hlocFresh := makeRegion_corollary_loc_fresh h
  unfold Reference.objAt?
  dsimp only
  rw [hlocFresh]
  dsimp only
  obtain ⟨frame, hlast, hcfg'⟩ := makeRegion_cases h
  have hlookup' : cfg'.heap.lookup cfg.freshRegionId = some ({ bridgeObjectId := cfg.freshObjectId, objMap := (∅ : ObjMap).insert cfg.freshObjectId ∅, status := Status.Closed } : Region) := by
    rw [hcfg']; dsimp only; rw [AList.lookup_insert]
  rw [hlookup']
  dsimp only [Option.bind]
  rw [AList.lookup_insert]

-- `ReachableStep` agrees for every `OId`-sourced step: unconditional for `oid ≠ freshObjectId`, vacuous for the fresh id itself (empty object, no refs).
theorem makeRegion_oid_step_iff {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeRegion x cfg = some cfg') (oid : ObjectId) (b : Reference) :
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
      rw [makeRegion_fresh_objAt_cfg' h] at hobjAt
      injection hobjAt with hobjAt
      rw [← hobjAt] at hcontains
      simp [Object.refs] at hcontains
  · rw [ReachableStep_oid_iff, ReachableStep_oid_iff, makeRegion_objAt_eq_of_ne vcfg h hne]

-- `ReachableStep` agrees for every `RId`-sourced step whose source isn't the freshly-allocated region itself.
theorem makeRegion_rid_step_iff_of_ne {cfg cfg' : RuntimeConfig}
    (h : makeRegion x cfg = some cfg') {rid : RegionId} (hne : rid ≠ cfg.freshRegionId) (b : Reference) :
    ReachableStep cfg (Reference.RId rid) b ↔ ReachableStep cfg' (Reference.RId rid) b := by
  obtain ⟨frame, hlast, hcfg'⟩ := makeRegion_cases h
  have hlookup' : cfg'.heap.lookup rid = cfg.heap.lookup rid := by
    rw [hcfg']; dsimp only; rw [AList.lookup_insert_ne hne]
  rw [ReachableStep_rid_iff, ReachableStep_rid_iff, hlookup']

-- `ReachableStep` agrees for every source that isn't the freshly-allocated region reference itself.
theorem makeRegion_step_iff_of_ne {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeRegion x cfg = some cfg') {a : Reference} (hane : a ≠ Reference.RId cfg.freshRegionId)
    (b : Reference) : ReachableStep cfg a b ↔ ReachableStep cfg' a b := by
  cases a with
  | OId oid => exact makeRegion_oid_step_iff vcfg h oid b
  | RId rid =>
    have hne : rid ≠ cfg.freshRegionId := fun heq => hane (by rw [heq])
    exact makeRegion_rid_step_iff_of_ne h hne b

-- `RId cfg.freshRegionId` is never a `ReachableStep cfg'` target: `RId`-sourced steps only ever land on an `OId`, and it's written only into a `varMap`, which no `ReachableStep_oid_iff` field step ever reads.
theorem makeRegion_freshRid_not_target {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeRegion x cfg = some cfg') {a : Reference} :
    ¬ ReachableStep cfg' a (Reference.RId cfg.freshRegionId) := by
  intro hstep
  cases a with
  | RId ridA =>
    rw [ReachableStep_rid_iff] at hstep
    obtain ⟨regionA, hlookupA, -, hbeq⟩ := hstep
    simp at hbeq
  | OId oidA =>
    have hstepCfg : ReachableStep cfg (Reference.OId oidA) (Reference.RId cfg.freshRegionId) :=
      (makeRegion_oid_step_iff vcfg h oidA (Reference.RId cfg.freshRegionId)).mpr hstep
    rw [ReachableStep_oid_iff] at hstepCfg
    obtain ⟨obj, hobjAt, hcontains⟩ := hstepCfg
    unfold Reference.objAt? at hobjAt
    dsimp only at hobjAt
    cases hloc' : (Reference.OId oidA).loc? cfg with
    | none => rw [hloc'] at hobjAt; simp at hobjAt
    | some loc =>
      rw [hloc'] at hobjAt
      cases loc with
      | Rgn ridR =>
        dsimp only at hobjAt
        cases hlookupR : cfg.heap.lookup ridR with
        | none => rw [hlookupR] at hobjAt; simp at hobjAt
        | some regionR =>
          rw [hlookupR] at hobjAt
          have hmemrefs : Reference.RId cfg.freshRegionId ∈ regionR.refs :=
            mem_region_refs_of_mem_objMap hobjAt (List.contains_iff_mem.mp hcontains)
          have hmemHeap : Reference.RId cfg.freshRegionId ∈ cfg.heap.refs := by
            rw [heap_refs_eq_flatMap, List.mem_flatMap]
            exact ⟨⟨ridR, regionR⟩, AList.lookup_mem_entries hlookupR, hmemrefs⟩
          have hmemCfg : Reference.RId cfg.freshRegionId ∈ cfg.refs := List.mem_append_right _ hmemHeap
          exact RuntimeConfig.freshRegionId_not_mem cfg (vcfg.hs2 cfg.freshRegionId hmemCfg)
      | Stk fidR =>
        dsimp only at hobjAt
        cases hfind : cfg.stackWithIndex.find? (fun f => f.index == fidR) with
        | none => rw [hfind] at hobjAt; simp at hobjAt
        | some someFrame =>
          rw [hfind] at hobjAt
          have hmemrefs : Reference.RId cfg.freshRegionId ∈ someFrame.refs :=
            mem_frame_refs_of_mem_objMap hobjAt (List.contains_iff_mem.mp hcontains)
          have hmemSWI : someFrame ∈ cfg.stackWithIndex := List.mem_of_find?_eq_some hfind
          have hmemstack0 : someFrame.toFrame ∈ cfg.stack := by
            obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hmemSWI
            rw [← hfeq]; exact List.getElem_mem hn
          have hmemStack : Reference.RId cfg.freshRegionId ∈ cfg.stack.refs := by
            rw [stack_refs_eq_flatMap, List.mem_flatMap]
            exact ⟨someFrame.toFrame, hmemstack0, hmemrefs⟩
          have hmemCfg : Reference.RId cfg.freshRegionId ∈ cfg.refs := List.mem_append_left _ hmemStack
          exact RuntimeConfig.freshRegionId_not_mem cfg (vcfg.hs2 cfg.freshRegionId hmemCfg)

-- A `cfg`-chain transports unconditionally into `cfg'`: `RId cfg.freshRegionId` can't source a `ReachableStep cfg` (it doesn't exist yet), so every hop qualifies for `makeRegion_step_iff_of_ne`.
theorem makeRegion_reflTransGen_transport_up {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeRegion x cfg = some cfg') {start target : Reference}
    (hrtg : Relation.ReflTransGen (ReachableStep cfg) start target) :
    Relation.ReflTransGen (ReachableStep cfg') start target := by
  induction hrtg with
  | refl => exact Relation.ReflTransGen.refl
  | tail hprev hstep ih =>
    rename_i b c
    have hbne : b ≠ Reference.RId cfg.freshRegionId := by
      intro heq; rw [heq] at hstep; exact freshRegionId_no_step hstep
    exact ih.tail ((makeRegion_step_iff_of_ne vcfg h hbne c).mp hstep)

-- A `cfg'`-chain rooted away from the fresh region transports back into `cfg`: `makeRegion_freshRid_not_target` keeps every node off `RId cfg.freshRegionId`, so every hop qualifies too.
theorem makeRegion_reflTransGen_transport_down {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeRegion x cfg = some cfg') {start : Reference} (hstartne : start ≠ Reference.RId cfg.freshRegionId) :
    ∀ {target : Reference}, Relation.ReflTransGen (ReachableStep cfg') start target →
      target ≠ Reference.RId cfg.freshRegionId ∧ Relation.ReflTransGen (ReachableStep cfg) start target := by
  intro target hrtg
  induction hrtg with
  | refl => exact ⟨hstartne, Relation.ReflTransGen.refl⟩
  | tail hprev hstep ih =>
    rename_i b c
    obtain ⟨hbne, ihrtg⟩ := ih
    have hcne : c ≠ Reference.RId cfg.freshRegionId := by
      intro heq; rw [heq] at hstep; exact makeRegion_freshRid_not_target vcfg h hstep
    exact ⟨hcne, ihrtg.tail ((makeRegion_step_iff_of_ne vcfg h hbne c).mpr hstep)⟩

-- Every `cfg'.stackWithIndex` member is either an unchanged pre-existing frame or the last frame with `varMap` updated.
theorem makeRegion_frame_cases {cfg cfg' : RuntimeConfig} {x : VarName}
    (h : makeRegion x cfg = some cfg')
    {frame : FrameWithIndex} (hframe : frame ∈ cfg'.stackWithIndex) :
    (frame ∈ cfg.stackWithIndex ∧ frame.index < cfg.stack.length - 1) ∨
    (∃ lastFrame, cfg.stack.getLast? = some lastFrame ∧
      frame.regionId = lastFrame.regionId ∧ frame.bridgeVar = lastFrame.bridgeVar ∧
      frame.objMap = lastFrame.objMap ∧
      frame.varMap = lastFrame.varMap.insert x (Reference.RId cfg.freshRegionId) ∧
      frame.index = cfg.stack.dropLast.length) := by
  obtain ⟨lastFrame, hlast, hcfg'⟩ := makeRegion_cases h
  have hstack' : cfg'.stack = cfg.stack.dropLast ++ [{ lastFrame with
      varMap := lastFrame.varMap.insert x (Reference.RId cfg.freshRegionId) }] := by rw [hcfg']
  have hstackEq : cfg.stack = cfg.stack.dropLast ++ [lastFrame] :=
    (List.dropLast_append_getLast? lastFrame hlast).symm
  unfold RuntimeConfig.stackWithIndex at hframe
  rw [hstack'] at hframe
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
    exact ⟨lastFrame, hlast, rfl, rfl, rfl, rfl, rfl⟩

-- A pre-existing frame with index strictly below the last one survives `makeRegion` unchanged, at the same index.
theorem makeRegion_frame_mem_up {cfg cfg' : RuntimeConfig} {x : VarName}
    (h : makeRegion x cfg = some cfg')
    {frame : FrameWithIndex} (hframe : frame ∈ cfg.stackWithIndex) (hlt : frame.index < cfg.stack.length - 1) :
    frame ∈ cfg'.stackWithIndex := by
  obtain ⟨lastFrame, hlast, hcfg'⟩ := makeRegion_cases h
  have hstack' : cfg'.stack = cfg.stack.dropLast ++ [{ lastFrame with
      varMap := lastFrame.varMap.insert x (Reference.RId cfg.freshRegionId) }] := by rw [hcfg']
  unfold RuntimeConfig.stackWithIndex at hframe ⊢
  rw [hstack']
  obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hframe
  have hidx : frame.index = n := by rw [← hfeq]
  have hnlt : n < cfg.stack.dropLast.length := by rw [List.length_dropLast]; rw [hidx] at hlt; exact hlt
  apply List.mem_mapIdx.mpr
  refine ⟨n, ?_, ?_⟩
  · rw [List.length_append]; omega
  · rw [List.getElem_append_left hnlt, List.getElem_dropLast hnlt]
    exact hfeq

-- `FrameReachable` agrees below the last frame; unlike `makeObjRegion`, no S1 uniqueness argument is needed since the heap change is a fresh key insert.
theorem makeRegion_frame_reachable_iff {cfg cfg' : RuntimeConfig} {x : VarName} (vcfg : ValidConfig cfg)
    (h : makeRegion x cfg = some cfg')
    {X : FrameWithIndex} (_hXmem : X ∈ cfg.stackWithIndex) (hXlt : X.index < cfg.stack.length - 1)
    (ref : Reference) : FrameReachable cfg X.index ref ↔ FrameReachable cfg' X.index ref := by
  obtain ⟨lastFrame, hlast, hcfg'⟩ := makeRegion_cases h
  rw [FrameReachable_iff_reflTransGen, FrameReachable_iff_reflTransGen]
  constructor
  · rintro ⟨start, hroot, hrtg⟩
    refine ⟨start, ?_, makeRegion_reflTransGen_transport_up vcfg h hrtg⟩
    rcases hroot with ⟨Xf, hXfmem, hXfidx, var, hvar⟩ | ⟨Xf, hXfmem, hXfidx, regionX, hlookup, hbridge⟩
    · exact Or.inl ⟨Xf, makeRegion_frame_mem_up h hXfmem (hXfidx ▸ hXlt), hXfidx, var, hvar⟩
    · have hXfne : Xf.regionId ≠ cfg.freshRegionId := by
        intro heq
        apply RuntimeConfig.freshRegionId_not_mem cfg
        rw [← AList.mem_keys, ← AList.lookup_isSome, ← heq, hlookup]
        simp
      have hlookup' : cfg'.heap.lookup Xf.regionId = some regionX := by
        rw [hcfg']; dsimp only; rw [AList.lookup_insert_ne hXfne]; exact hlookup
      exact Or.inr ⟨Xf, makeRegion_frame_mem_up h hXfmem (hXfidx ▸ hXlt), hXfidx, regionX, hlookup', hbridge⟩
  · rintro ⟨start, hroot, hrtg⟩
    have hstartne : start ≠ Reference.RId cfg.freshRegionId := by
      rcases hroot with ⟨Xf, hXfmem, hXfidx, var, hvar⟩ | ⟨Xf, hXfmem, hXfidx, regionX, hlookup, hbridge⟩
      · rcases makeRegion_frame_cases h hXfmem with ⟨hXfmemcfg, -⟩ | ⟨lf, hlf, -, -, -, -, hXfidx2⟩
        · intro heq
          rw [heq] at hvar
          have hmemrefs : Reference.RId cfg.freshRegionId ∈ Xf.refs := mem_frame_refs_of_mem_varMap hvar
          have hmemstack0 : Xf.toFrame ∈ cfg.stack := by
            obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hXfmemcfg
            rw [← hfeq]; exact List.getElem_mem hn
          have hmemStack : Reference.RId cfg.freshRegionId ∈ cfg.stack.refs := by
            rw [stack_refs_eq_flatMap, List.mem_flatMap]
            exact ⟨Xf.toFrame, hmemstack0, hmemrefs⟩
          have hmemCfg : Reference.RId cfg.freshRegionId ∈ cfg.refs := List.mem_append_left _ hmemStack
          exact RuntimeConfig.freshRegionId_not_mem cfg (vcfg.hs2 cfg.freshRegionId hmemCfg)
        · exfalso
          have hXeq : X.index = cfg.stack.dropLast.length := by rw [← hXfidx, hXfidx2]
          rw [hXeq, List.length_dropLast] at hXlt
          exact absurd hXlt (lt_irrefl _)
      · rw [hbridge]; simp
    obtain ⟨-, hrtgCfg⟩ := makeRegion_reflTransGen_transport_down vcfg h hstartne hrtg
    refine ⟨start, ?_, hrtgCfg⟩
    rcases hroot with ⟨Xf, hXfmem, hXfidx, var, hvar⟩ | ⟨Xf, hXfmem, hXfidx, regionX, hlookup, hbridge⟩
    · rcases makeRegion_frame_cases h hXfmem with ⟨hXfmemcfg, -⟩ | ⟨lf, hlf, -, -, -, -, hXfidx2⟩
      · exact Or.inl ⟨Xf, hXfmemcfg, hXfidx, var, hvar⟩
      · exfalso
        have hXeq : X.index = cfg.stack.dropLast.length := by rw [← hXfidx, hXfidx2]
        rw [hXeq, List.length_dropLast] at hXlt
        exact absurd hXlt (lt_irrefl _)
    · rcases makeRegion_frame_cases h hXfmem with ⟨hXfmemcfg, hXflt⟩ | ⟨lf, hlf, -, -, -, -, hXfidx2⟩
      · obtain ⟨regionCfg, hlookupCfg, -⟩ := l2_of_stackWithIndex vcfg hXfmemcfg
        have hXfne : Xf.regionId ≠ cfg.freshRegionId := by
          intro heq
          apply RuntimeConfig.freshRegionId_not_mem cfg
          rw [← AList.mem_keys, ← AList.lookup_isSome, ← heq, hlookupCfg]
          simp
        have hlookupcfg : cfg.heap.lookup Xf.regionId = some regionX := by
          rw [hcfg'] at hlookup; dsimp only at hlookup
          rw [AList.lookup_insert_ne hXfne] at hlookup; exact hlookup
        exact Or.inr ⟨Xf, hXfmemcfg, hXfidx, regionX, hlookupcfg, hbridge⟩
      · exfalso
        have hXeq : X.index = cfg.stack.dropLast.length := by rw [← hXfidx, hXfidx2]
        rw [hXeq, List.length_dropLast] at hXlt
        exact absurd hXlt (lt_irrefl _)
