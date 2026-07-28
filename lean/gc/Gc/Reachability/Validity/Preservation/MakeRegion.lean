import Gc.Model.Mutation.MakeRegion
import Gc.Model.Preservation.MakeRegion
import Gc.Model.Preservation.Common
import Gc.Reachability.Validity.Reachable
import Gc.Reachability.Corollaries

private theorem makeRegion_corollary_mem_keys_of_lookup {rid : RegionId} {region : Region} {heap : Heap}
    (hlookup : heap.lookup rid = some region) : rid ∈ heap.keys :=
  AList.mem_keys.mp (AList.lookup_isSome.mp (by rw [hlookup]; rfl))

-- Every frame's `objMap` is completely unaffected by makeRegion (only the last frame's `varMap`
-- gains `x ↦ RId freshRegionId`, and the heap gains a brand-new key) -- so the per-position
-- `objMap` is unconditionally the same in cfg and cfg', at every index. Thin wrapper around
-- `Gc.Model.Preservation.Common`'s generic `stackWithIndex_objMap_get_eq_of_last_varMap_update`
-- (see `merge_corollary_objMap_get_eq`'s comment for why the same generic lemma applies here
-- despite a different value being inserted into `varMap`).
private theorem makeRegion_corollary_objMap_get_eq {cfg cfg' : RuntimeConfig} {x : VarName}
    (h : makeRegion x cfg = some cfg') (n : ℕ) :
    (cfg.stack[n]?).map Frame.objMap = (cfg'.stack[n]?).map Frame.objMap := by
  obtain ⟨frame, hframeLast, hcfg'⟩ := makeRegion_cases h
  have hstack' : cfg'.stack = cfg.stack.dropLast ++
      [({ regionId := frame.regionId, bridgeVar := frame.bridgeVar, objMap := frame.objMap,
          varMap := AList.insert x (Reference.RId cfg.freshRegionId) frame.varMap } : Frame)] := by
    rw [hcfg']
  exact stackWithIndex_objMap_get_eq_of_last_varMap_update hframeLast hstack' n

-- The freshly-created object always resolves into the brand-new region (never onto the stack,
-- since no frame's objMap ever changes, and never into any pre-existing region).
private theorem makeRegion_corollary_loc_fresh {cfg cfg' : RuntimeConfig} {x : VarName}
    (h : makeRegion x cfg = some cfg') :
    (Reference.OId cfg.freshObjectId).loc? cfg' = some (Location.Rgn cfg.freshRegionId) := by
  obtain ⟨frame, hframeLast, hcfg'⟩ := makeRegion_cases h
  set newRegion : Region :=
    { bridgeObjectId := cfg.freshObjectId, objMap := AList.insert cfg.freshObjectId ∅ ∅,
      status := Status.Closed } with newRegion_def
  set newFrame : Frame :=
    { regionId := frame.regionId, bridgeVar := frame.bridgeVar, objMap := frame.objMap,
      varMap := AList.insert x (Reference.RId cfg.freshRegionId) frame.varMap } with newFrame_def
  have fresh_not_in_any_frame : ∀ f ∈ cfg.stack, cfg.freshObjectId ∉ f.objMap.keys := by
    intro f hf hmem
    apply RuntimeConfig.freshObjectId_not_mem cfg
    unfold RuntimeConfig.objectIds Stack.objectIds Frame.objectIds
    rw [List.bind_eq_flatMap, List.flatMap_id, List.mem_append, List.mem_flatten]
    exact Or.inl ⟨f.objMap.keys, List.mem_map_of_mem hf, hmem⟩
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
    (List.dropLast_append_getLast? frame hframeLast).symm
  have frame_mem : frame ∈ cfg.stack := stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self frame)
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
      cfg'.stackWithIndex.findRev? (fun f => (AList.keys f.objMap).contains cfg.freshObjectId) = none := by
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
      cfg'.heap.entries.find? (fun p => (AList.keys p.snd.objMap).contains cfg.freshObjectId) =
      some (⟨cfg.freshRegionId, newRegion⟩ : Sigma (fun _ : RegionId => Region)) := by
    rw [hcfg', newRegion_def]
    dsimp only
    rw [AList.entries_insert_of_notMem (RuntimeConfig.freshRegionId_not_mem cfg)]
    apply List.find?_cons_of_pos
    simp
  unfold Reference.loc?
  dsimp only
  rw [h1_none, h2_some]

-- The freshly-created object's own content: an empty object.
private theorem makeRegion_corollary_objAt_fresh {cfg cfg' : RuntimeConfig} {x : VarName}
    (h : makeRegion x cfg = some cfg') :
    (Reference.OId cfg.freshObjectId).objAt? cfg' = some (∅ : Object) := by
  obtain ⟨frame, hframeLast, hcfg'⟩ := makeRegion_cases h
  unfold Reference.objAt?
  dsimp only
  rw [makeRegion_corollary_loc_fresh h]
  dsimp only
  rw [hcfg']
  dsimp only
  rw [AList.lookup_insert]
  exact AList.lookup_insert (a := cfg.freshObjectId) (b := (∅ : Object)) (∅ : ObjMap)

-- For any oid other than the freshly-allocated one, `objAt?` is unaffected. Stack side:
-- unconditional (no frame's objMap ever changes). Heap side: unconditional too, since the new
-- heap key is genuinely fresh -- an already-allocated oid's own region key can never coincide
-- with it.
private theorem makeRegion_corollary_objAt_eq_of_ne_fresh (vcfg : ValidConfig cfg) (vcfg' : ValidConfig cfg')
    {x : VarName} {oid : ObjectId}
    (h : makeRegion x cfg = some cfg') (hne : oid ≠ cfg.freshObjectId) :
    (Reference.OId oid).objAt? cfg = (Reference.OId oid).objAt? cfg' := by
  have hlocEq := makeRegion_corollary_loc_eq vcfg h oid hne
  obtain ⟨frame, hframeLast, hcfg'⟩ := makeRegion_cases h
  cases hloc : (Reference.OId oid).loc? cfg with
  | none =>
    unfold Reference.objAt?
    dsimp only
    rw [hloc, ← hlocEq, hloc]
  | some loc =>
    have hloc' : (Reference.OId oid).loc? cfg' = some loc := by rw [← hlocEq]; exact hloc
    cases loc with
    | Stk fid0 =>
      obtain ⟨frame0, hframe0, hmem0⟩ := (oid_loc_stk_iff_in_stack vcfg).mp hloc
      obtain ⟨frame0', hframe0', hmem0'⟩ := (oid_loc_stk_iff_in_stack vcfg').mp hloc'
      obtain ⟨sf0, hsf0, hsf0_eq⟩ : ∃ sf, cfg.stack[fid0]? = some sf ∧ frame0 = { sf with index := fid0 } := by
        have h' := hframe0
        unfold RuntimeConfig.stackWithIndex at h'
        rw [List.getElem?_mapIdx, Option.map_eq_some_iff] at h'
        obtain ⟨sf, hsf, hsf_eq⟩ := h'
        exact ⟨sf, hsf, hsf_eq.symm⟩
      obtain ⟨sf0', hsf0', hsf0'_eq⟩ : ∃ sf, cfg'.stack[fid0]? = some sf ∧ frame0' = { sf with index := fid0 } := by
        have h' := hframe0'
        unfold RuntimeConfig.stackWithIndex at h'
        rw [List.getElem?_mapIdx, Option.map_eq_some_iff] at h'
        obtain ⟨sf, hsf, hsf_eq⟩ := h'
        exact ⟨sf, hsf, hsf_eq.symm⟩
      have hmem0mem : frame0 ∈ cfg.stackWithIndex := List.mem_of_getElem? hframe0
      have hmem0mem' : frame0' ∈ cfg'.stackWithIndex := List.mem_of_getElem? hframe0'
      have hidx0 : frame0.index = fid0 := by rw [hsf0_eq]
      have hidx0' : frame0'.index = fid0 := by rw [hsf0'_eq]
      have hfind0 : cfg.stackWithIndex.find? (fun f => f.index == fid0) = some frame0 := by
        rw [← hidx0]; exact swap_corollary_stackWithIndex_find_eq hmem0mem
      have hfind0' : cfg'.stackWithIndex.find? (fun f => f.index == fid0) = some frame0' := by
        rw [← hidx0']; exact swap_corollary_stackWithIndex_find_eq hmem0mem'
      have hobjMap0 : frame0.objMap = frame0'.objMap := by
        have hmapeq1 := makeRegion_corollary_objMap_get_eq h fid0
        rw [hsf0, hsf0'] at hmapeq1
        simp only [Option.map_some] at hmapeq1
        rw [hsf0_eq, hsf0'_eq]
        dsimp only
        injection hmapeq1
      unfold Reference.objAt?
      dsimp only
      rw [hloc, hloc']
      dsimp only
      rw [hfind0, hfind0']
      exact congrArg (AList.lookup oid) hobjMap0
    | Rgn rid0 =>
      obtain ⟨region0, hlookup0, hmem0⟩ := (oid_loc_rgn_iff_in_heap vcfg).mp hloc
      have hridne : rid0 ≠ cfg.freshRegionId := by
        intro hc
        rw [hc] at hlookup0
        exact RuntimeConfig.freshRegionId_not_mem cfg (makeRegion_corollary_mem_keys_of_lookup hlookup0)
      unfold Reference.objAt?
      dsimp only
      rw [hloc, hloc']
      dsimp only
      have hlookup'' : cfg'.heap.lookup rid0 = cfg.heap.lookup rid0 := by
        rw [hcfg']
        dsimp only
        exact AList.lookup_insert_ne hridne
      rw [hlookup'']

-- `RefStep` is completely unaffected between cfg and cfg': the only new content is the freshly
-- allocated (isolated) object.
theorem makeRegion_corollary_refStep_iff (vcfg : ValidConfig cfg) (vcfg' : ValidConfig cfg')
    {x : VarName} (h : makeRegion x cfg = some cfg') :
    ∀ a b, RefStep cfg a b ↔ RefStep cfg' a b := by
  intro a b
  constructor
  · rintro ⟨obj, hobjAt, hcontains⟩
    obtain ⟨oid, rfl⟩ : ∃ oid, a = Reference.OId oid := by
      cases a with
      | OId oid => exact ⟨oid, rfl⟩
      | RId _ => unfold Reference.objAt? at hobjAt; simp at hobjAt
    have hne : oid ≠ cfg.freshObjectId := by
      intro heq
      subst heq
      unfold Reference.objAt? at hobjAt
      dsimp only at hobjAt
      cases hloc0 : (Reference.OId cfg.freshObjectId).loc? cfg with
      | none => rw [hloc0] at hobjAt; simp at hobjAt
      | some loc0 =>
        exfalso
        apply RuntimeConfig.freshObjectId_not_mem cfg
        cases loc0 with
        | Rgn rid0 =>
          obtain ⟨region0, hlookup0, hmem0⟩ := (oid_loc_rgn_iff_in_heap vcfg).mp hloc0
          unfold RuntimeConfig.objectIds
          apply List.mem_append_right
          exact heap_objectIds_of_mem (AList.mem_lookup_iff.mp (Option.mem_def.mpr hlookup0))
            (AList.mem_keys.mpr hmem0)
        | Stk fid0 =>
          obtain ⟨frame0, hframe0, hmem0⟩ := (oid_loc_stk_iff_in_stack vcfg).mp hloc0
          obtain ⟨sf0, hsf0, hsf0_eq⟩ : ∃ sf, cfg.stack[fid0]? = some sf ∧ frame0 = { sf with index := fid0 } := by
            have h' := hframe0
            unfold RuntimeConfig.stackWithIndex at h'
            rw [List.getElem?_mapIdx, Option.map_eq_some_iff] at h'
            obtain ⟨sf, hsf, hsf_eq⟩ := h'
            exact ⟨sf, hsf, hsf_eq.symm⟩
          unfold RuntimeConfig.objectIds Stack.objectIds Frame.objectIds
          rw [List.bind_eq_flatMap, List.flatMap_id, List.mem_append, List.mem_flatten]
          left
          refine ⟨frame0.objMap.keys, ?_, AList.mem_keys.mpr hmem0⟩
          rw [hsf0_eq]
          dsimp only
          exact List.mem_map_of_mem (List.mem_of_getElem? hsf0)
    exact ⟨obj, (makeRegion_corollary_objAt_eq_of_ne_fresh vcfg vcfg' h hne).symm.trans hobjAt, hcontains⟩
  · rintro ⟨obj, hobjAt', hcontains⟩
    obtain ⟨oid, rfl⟩ : ∃ oid, a = Reference.OId oid := by
      cases a with
      | OId oid => exact ⟨oid, rfl⟩
      | RId _ => unfold Reference.objAt? at hobjAt'; simp at hobjAt'
    have hne : oid ≠ cfg.freshObjectId := by
      intro heq
      subst heq
      rw [makeRegion_corollary_objAt_fresh h] at hobjAt'
      injection hobjAt' with hobj_eq
      rw [← hobj_eq] at hcontains
      simp [Object.refs] at hcontains
    exact ⟨obj, (makeRegion_corollary_objAt_eq_of_ne_fresh vcfg vcfg' h hne).trans hobjAt', hcontains⟩

-- A `RefStep`'s source in cfg' is never the freshly-allocated object (empty, no outgoing edges).
private theorem makeRegion_corollary_refStep_source_ne_fresh_cfg' {cfg cfg' : RuntimeConfig} {x : VarName}
    (h : makeRegion x cfg = some cfg') {a b : Reference} (hstep : RefStep cfg' a b) :
    a ≠ Reference.OId cfg.freshObjectId := by
  intro heq
  subst heq
  obtain ⟨obj, hobjAt, hcontains⟩ := hstep
  rw [makeRegion_corollary_objAt_fresh h] at hobjAt
  injection hobjAt with hobj_eq
  rw [← hobj_eq] at hcontains
  simp [Object.refs] at hcontains

-- Given a frame on cfg'.stackWithIndex whose root value is `OId start_oid`, transport its
-- `FrameRoot` witness down to cfg: the var-disjunct's witness frame is either an untouched
-- (non-last) position (identical record) or the last position, where the *only* changed slot
-- (`x ↦ RId freshRegionId`) can never supply an `OId`-shaped value at all (constructor
-- mismatch, no freshness argument needed); the bridge-disjunct's heap key can never be the new
-- region's key, since that key belongs to no on-stack frame at all.
private theorem makeRegion_corollary_frameRoot_down {cfg cfg' : RuntimeConfig} {x : VarName}
    (vcfg : ValidConfig cfg) (h : makeRegion x cfg = some cfg')
    {fid : Index} {start_oid : ObjectId}
    (hroot : FrameRoot cfg' fid (Reference.OId start_oid)) :
    FrameRoot cfg fid (Reference.OId start_oid) := by
  obtain ⟨frame1, hframe1Last, hcfg'⟩ := makeRegion_cases h
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame1] := (List.dropLast_append_getLast? frame1 hframe1Last).symm
  set newFrame1 : Frame :=
    { regionId := frame1.regionId, bridgeVar := frame1.bridgeVar, objMap := frame1.objMap,
      varMap := AList.insert x (Reference.RId cfg.freshRegionId) frame1.varMap } with newFrame1_def
  unfold FrameRoot
  unfold FrameRoot at hroot
  rcases hroot with ⟨fr, hfr, hidx, var, hlookup⟩ | ⟨fr, hfr, hidx, region, hlookup, hstart⟩
  · obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr
    have hidx_n : fr.index = n := by rw [← hfeq]
    have hidx_fid : fid = n := by rw [← hidx, hidx_n]
    by_cases hlastpos : n = cfg.stack.dropLast.length
    · have hnewFr_mem : ({ newFrame1 with index := n } : FrameWithIndex) ∈ cfg'.stackWithIndex := by
        rw [hcfg']
        unfold RuntimeConfig.stackWithIndex
        rw [List.mapIdx_concat, ← hlastpos]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      have hfr_eq : fr = { newFrame1 with index := n } :=
        swap_corollary_stackWithIndex_index_inj hfr hnewFr_mem hidx_n
      rw [hfr_eq] at hlookup
      dsimp only at hlookup
      by_cases hvarx : var = x
      · exfalso
        subst hvarx
        rw [AList.lookup_insert (a := var) (b := (Reference.RId cfg.freshRegionId)) frame1.varMap] at hlookup
        simp at hlookup
      · rw [AList.lookup_insert_ne hvarx] at hlookup
        left
        refine ⟨{ frame1 with index := n }, ?_, hidx_fid.symm, var, hlookup⟩
        unfold RuntimeConfig.stackWithIndex
        conv_lhs => rw [stack_eq]
        rw [List.mapIdx_concat, ← hlastpos]
        exact List.mem_append_right _ (List.mem_singleton_self _)
    · have hlt : n < cfg.stack.dropLast.length := by
        have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq]; simp
        have hlen' : cfg'.stack.length = cfg.stack.dropLast.length + 1 := by rw [hcfg']; simp
        have hn' : n < cfg'.stack.length := hn
        rw [hlen'] at hn'
        exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hn') hlastpos
      have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
        conv_lhs => rw [stack_eq]
        rw [List.getElem?_append_left hlt]
      have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
        rw [hcfg']; dsimp only
        rw [List.getElem?_append_left hlt]
      have hfr_get? : cfg'.stack[n]? = some fr.toFrame := by
        rw [show fr.toFrame = cfg'.stack[n] from by rw [← hfeq]]
        exact List.getElem?_eq_getElem hn
      have hcfgn : cfg.stack[n]? = some fr.toFrame := by rw [e1, ← e2, hfr_get?]
      obtain ⟨h1, heq⟩ := List.getElem?_eq_some_iff.mp hcfgn
      left
      refine ⟨fr, ?_, hidx, var, hlookup⟩
      unfold RuntimeConfig.stackWithIndex
      exact List.mem_mapIdx.mpr ⟨n, h1, by rw [heq, ← hidx_n]⟩
  · -- bridge disjunct: the new heap key belongs to no on-stack frame's regionId, so `fr`'s own
    -- region lookup is unaffected regardless of position.
    right
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr
    have hidx_n : fr.index = n := by rw [← hfeq]
    have hidx_fid : fid = n := by rw [← hidx, hidx_n]
    have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq]; simp
    have hlen' : cfg'.stack.length = cfg.stack.dropLast.length + 1 := by rw [hcfg']; simp
    have hn' : n < cfg.stack.length := by rw [hlen]; rw [hlen'] at hn; exact hn
    have hridne : fr.regionId ≠ cfg.freshRegionId := by
      intro hc
      obtain ⟨region0, hlookup0, _⟩ := vcfg.l2 cfg.stack[n] (List.getElem_mem hn')
      have hfr_regionId0 : cfg.stack[n].regionId = fr.regionId := by
        by_cases hlp : n = cfg.stack.dropLast.length
        · have hnewFr_mem : ({ newFrame1 with index := n } : FrameWithIndex) ∈ cfg'.stackWithIndex := by
            rw [hcfg']
            unfold RuntimeConfig.stackWithIndex
            rw [List.mapIdx_concat, ← hlp]
            exact List.mem_append_right _ (List.mem_singleton_self _)
          have hfr_eq : fr = { newFrame1 with index := n } :=
            swap_corollary_stackWithIndex_index_inj hfr hnewFr_mem hidx_n
          have hget? : cfg.stack[n]? = some frame1 := by
            conv_lhs => rw [stack_eq, hlp]
            simp
          have e1 : cfg.stack[n] = frame1 := (List.getElem?_eq_some_iff.mp hget?).2
          rw [e1, hfr_eq]
        · have hlt : n < cfg.stack.dropLast.length := by omega
          have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
            conv_lhs => rw [stack_eq]
            rw [List.getElem?_append_left hlt]
          have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
            rw [hcfg']; dsimp only
            rw [List.getElem?_append_left hlt]
          have hfr_get? : cfg'.stack[n]? = some fr.toFrame := by
            rw [show fr.toFrame = cfg'.stack[n] from by rw [← hfeq]]
            exact List.getElem?_eq_getElem hn
          have hcfgn : cfg.stack[n]? = some fr.toFrame := by rw [e1, ← e2, hfr_get?]
          obtain ⟨_, heq⟩ := List.getElem?_eq_some_iff.mp hcfgn
          rw [heq]
      rw [hfr_regionId0, hc] at hlookup0
      exact RuntimeConfig.freshRegionId_not_mem cfg (makeRegion_corollary_mem_keys_of_lookup hlookup0)
    have hlookup'' : cfg'.heap.lookup fr.regionId = cfg.heap.lookup fr.regionId := by
      rw [hcfg']
      dsimp only
      exact AList.lookup_insert_ne hridne
    by_cases hlastpos : n = cfg.stack.dropLast.length
    · have hnewFr_mem : ({ newFrame1 with index := n } : FrameWithIndex) ∈ cfg'.stackWithIndex := by
        rw [hcfg']
        unfold RuntimeConfig.stackWithIndex
        rw [List.mapIdx_concat, ← hlastpos]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      have hfr_eq : fr = { newFrame1 with index := n } :=
        swap_corollary_stackWithIndex_index_inj hfr hnewFr_mem hidx_n
      have hfr_regionId : fr.regionId = frame1.regionId := by rw [hfr_eq]
      have hlast1_mem : ({ frame1 with index := n } : FrameWithIndex) ∈ cfg.stackWithIndex := by
        unfold RuntimeConfig.stackWithIndex
        conv_lhs => rw [stack_eq]
        rw [List.mapIdx_concat, ← hlastpos]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      refine ⟨{ frame1 with index := n }, hlast1_mem, hidx_fid.symm, region, ?_, hstart⟩
      rw [← hfr_regionId, ← hlookup'']
      exact hlookup
    · have hlt : n < cfg.stack.dropLast.length := by
        have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq]; simp
        have hlen' : cfg'.stack.length = cfg.stack.dropLast.length + 1 := by rw [hcfg']; simp
        have hn' : n < cfg'.stack.length := hn
        rw [hlen'] at hn'
        exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hn') hlastpos
      have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
        conv_lhs => rw [stack_eq]
        rw [List.getElem?_append_left hlt]
      have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
        rw [hcfg']; dsimp only
        rw [List.getElem?_append_left hlt]
      have hfr_get? : cfg'.stack[n]? = some fr.toFrame := by
        rw [show fr.toFrame = cfg'.stack[n] from by rw [← hfeq]]
        exact List.getElem?_eq_getElem hn
      have hcfgn : cfg.stack[n]? = some fr.toFrame := by rw [e1, ← e2, hfr_get?]
      obtain ⟨h1, heq⟩ := List.getElem?_eq_some_iff.mp hcfgn
      refine ⟨fr, ?_, hidx, region, ?_, hstart⟩
      · unfold RuntimeConfig.stackWithIndex
        exact List.mem_mapIdx.mpr ⟨n, h1, by rw [heq, ← hidx_n]⟩
      · rw [← hlookup'']; exact hlookup

-- `FrameReachable` is completely unaffected at any position strictly before the mutated (last)
-- one -- the frame-transport argument `makeRegion_cr3` already builds inline for itself
-- (`frame_transport_down`/`_up`/its own `FrameRoot` iff), packaged here as its own reusable
-- theorem since CR5 (`Gc/Reachability/Validity/CR5.lean`) needs exactly this fact, not CR3's
-- later-frame-implies-earlier-frame shape. Mirrors `makeObjStack`/`makeObjRegion`'s own
-- `_corollary_frameReachable_iff_of_lt`.
theorem makeRegion_corollary_frameReachable_iff_of_lt (vcfg : ValidConfig cfg) (vcfg' : ValidConfig cfg')
    (h : makeRegion x cfg = some cfg')
    {fid : Index} (hfid : fid < cfg.stack.dropLast.length) (ref : Reference) :
    FrameReachable cfg fid ref ↔ FrameReachable cfg' fid ref := by
  obtain ⟨frame1, hframe1Last, hcfg'⟩ := makeRegion_cases h
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame1] := (List.dropLast_append_getLast? frame1 hframe1Last).symm
  have frame_transport_down : ∀ fr : FrameWithIndex, fr ∈ cfg'.stackWithIndex →
      fr.index < cfg.stack.dropLast.length → fr ∈ cfg.stackWithIndex := by
    intro fr hfr hltfr
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr
    have hidx_n : fr.index = n := by rw [← hfeq]
    have hlt : n < cfg.stack.dropLast.length := by rw [← hidx_n]; exact hltfr
    have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
      conv_lhs => rw [stack_eq]
      rw [List.getElem?_append_left hlt]
    have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
      rw [hcfg']; dsimp only
      rw [List.getElem?_append_left hlt]
    have hfr_get? : cfg'.stack[n]? = some fr.toFrame := by
      rw [show fr.toFrame = cfg'.stack[n] from by rw [← hfeq]]
      exact List.getElem?_eq_getElem hn
    have hcfgn : cfg.stack[n]? = some fr.toFrame := by rw [e1, ← e2, hfr_get?]
    obtain ⟨h1, heq⟩ := List.getElem?_eq_some_iff.mp hcfgn
    unfold RuntimeConfig.stackWithIndex
    exact List.mem_mapIdx.mpr ⟨n, h1, by rw [heq, ← hidx_n]⟩
  have frame_transport_up : ∀ fr : FrameWithIndex, fr ∈ cfg.stackWithIndex →
      fr.index < cfg.stack.dropLast.length → fr ∈ cfg'.stackWithIndex := by
    intro fr hfr hltfr
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr
    have hidx_n : fr.index = n := by rw [← hfeq]
    have hlt : n < cfg.stack.dropLast.length := by rw [← hidx_n]; exact hltfr
    have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
      conv_lhs => rw [stack_eq]
      rw [List.getElem?_append_left hlt]
    have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
      rw [hcfg']; dsimp only
      rw [List.getElem?_append_left hlt]
    have hfr_get? : cfg.stack[n]? = some fr.toFrame := by
      rw [show fr.toFrame = cfg.stack[n] from by rw [← hfeq]]
      exact List.getElem?_eq_getElem hn
    have hcfg'n : cfg'.stack[n]? = some fr.toFrame := by rw [e2, ← e1, hfr_get?]
    obtain ⟨h1, heq⟩ := List.getElem?_eq_some_iff.mp hcfg'n
    unfold RuntimeConfig.stackWithIndex
    exact List.mem_mapIdx.mpr ⟨n, h1, by rw [heq, ← hidx_n]⟩
  have hheap_eq_at : ∀ rid, rid ≠ cfg.freshRegionId → cfg'.heap.lookup rid = cfg.heap.lookup rid := by
    intro rid hrid
    rw [hcfg']; dsimp only; exact AList.lookup_insert_ne hrid
  have hfrRootIff : ∀ start, FrameRoot cfg fid start ↔ FrameRoot cfg' fid start := by
    intro start
    unfold FrameRoot
    constructor
    · rintro (⟨fr, hfr, hidx, var, hlookup⟩ | ⟨fr, hfr, hidx, region, hlookup, hstart⟩)
      · exact Or.inl ⟨fr, frame_transport_up fr hfr (hidx ▸ hfid), hidx, var, hlookup⟩
      · have hridne : fr.regionId ≠ cfg.freshRegionId := by
          intro hc
          rw [hc] at hlookup
          exact RuntimeConfig.freshRegionId_not_mem cfg (makeRegion_corollary_mem_keys_of_lookup hlookup)
        exact Or.inr ⟨fr, frame_transport_up fr hfr (hidx ▸ hfid), hidx, region,
          by rw [hheap_eq_at fr.regionId hridne]; exact hlookup, hstart⟩
    · rintro (⟨fr, hfr, hidx, var, hlookup⟩ | ⟨fr, hfr, hidx, region, hlookup, hstart⟩)
      · exact Or.inl ⟨fr, frame_transport_down fr hfr (hidx ▸ hfid), hidx, var, hlookup⟩
      · have hridne : fr.regionId ≠ cfg.freshRegionId := by
          intro hc
          have hfrCfg : fr ∈ cfg.stackWithIndex := frame_transport_down fr hfr (hidx ▸ hfid)
          obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfrCfg
          have hregeq : cfg.stack[n].regionId = fr.regionId := by rw [← hfeq]
          obtain ⟨region0, hlookup0, _⟩ := vcfg.l2 cfg.stack[n] (List.getElem_mem hn)
          rw [hregeq, hc] at hlookup0
          exact RuntimeConfig.freshRegionId_not_mem cfg (makeRegion_corollary_mem_keys_of_lookup hlookup0)
        exact Or.inr ⟨fr, frame_transport_down fr hfr (hidx ▸ hfid), hidx, region,
          by rw [← hheap_eq_at fr.regionId hridne]; exact hlookup, hstart⟩
  rw [FrameReachable_iff_reflTransGen, FrameReachable_iff_reflTransGen]
  constructor
  · rintro ⟨start, hroot, hrtg⟩
    exact ⟨start, (hfrRootIff start).mp hroot,
      hrtg.mono (fun a b hab => (makeRegion_corollary_refStep_iff vcfg vcfg' h a b).mp hab)⟩
  · rintro ⟨start, hroot, hrtg⟩
    exact ⟨start, (hfrRootIff start).mpr hroot,
      hrtg.mono (fun a b hab => (makeRegion_corollary_refStep_iff vcfg vcfg' h a b).mpr hab)⟩

theorem makeRegion_cr3 : ValidReachableConfig cfg →
  makeRegion x cfg = some cfg' →
  CR3 cfg' := by
  intro vrcfg h
  have vcfg := vrcfg.toValidConfig
  have vcfg' := makeRegion_valid vcfg h
  obtain ⟨frame1, hframe1Last, hcfg'⟩ := makeRegion_cases h
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame1] := (List.dropLast_append_getLast? frame1 hframe1Last).symm
  set newFrame1 : Frame :=
    { regionId := frame1.regionId, bridgeVar := frame1.bridgeVar, objMap := frame1.objMap,
      varMap := AList.insert x (Reference.RId cfg.freshRegionId) frame1.varMap } with newFrame1_def
  have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq]; simp
  have hlen' : cfg'.stack.length = cfg.stack.dropLast.length + 1 := by rw [hcfg']; simp
  -- Non-last-position frame transport, both directions (only the last frame's varMap differs).
  have frame_transport_down : ∀ fr : FrameWithIndex, fr ∈ cfg'.stackWithIndex →
      fr.index < cfg.stack.dropLast.length → fr ∈ cfg.stackWithIndex := by
    intro fr hfr hltfr
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr
    have hidx_n : fr.index = n := by rw [← hfeq]
    have hlt : n < cfg.stack.dropLast.length := by rw [← hidx_n]; exact hltfr
    have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
      conv_lhs => rw [stack_eq]
      rw [List.getElem?_append_left hlt]
    have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
      rw [hcfg']; dsimp only
      rw [List.getElem?_append_left hlt]
    have hfr_get? : cfg'.stack[n]? = some fr.toFrame := by
      rw [show fr.toFrame = cfg'.stack[n] from by rw [← hfeq]]
      exact List.getElem?_eq_getElem hn
    have hcfgn : cfg.stack[n]? = some fr.toFrame := by rw [e1, ← e2, hfr_get?]
    obtain ⟨h1, heq⟩ := List.getElem?_eq_some_iff.mp hcfgn
    unfold RuntimeConfig.stackWithIndex
    exact List.mem_mapIdx.mpr ⟨n, h1, by rw [heq, ← hidx_n]⟩
  have frame_transport_up : ∀ fr : FrameWithIndex, fr ∈ cfg.stackWithIndex →
      fr.index < cfg.stack.dropLast.length → fr ∈ cfg'.stackWithIndex := by
    intro fr hfr hltfr
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr
    have hidx_n : fr.index = n := by rw [← hfeq]
    have hlt : n < cfg.stack.dropLast.length := by rw [← hidx_n]; exact hltfr
    have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
      conv_lhs => rw [stack_eq]
      rw [List.getElem?_append_left hlt]
    have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
      rw [hcfg']; dsimp only
      rw [List.getElem?_append_left hlt]
    have hfr_get? : cfg.stack[n]? = some fr.toFrame := by
      rw [show fr.toFrame = cfg.stack[n] from by rw [← hfeq]]
      exact List.getElem?_eq_getElem hn
    have hcfg'n : cfg'.stack[n]? = some fr.toFrame := by rw [e2, ← e1, hfr_get?]
    obtain ⟨h1, heq⟩ := List.getElem?_eq_some_iff.mp hcfg'n
    unfold RuntimeConfig.stackWithIndex
    exact List.mem_mapIdx.mpr ⟨n, h1, by rw [heq, ← hidx_n]⟩
  have hheap_eq_at : ∀ rid, rid ≠ cfg.freshRegionId → cfg'.heap.lookup rid = cfg.heap.lookup rid := by
    intro rid hrid
    rw [hcfg']; dsimp only; exact AList.lookup_insert_ne hrid
  have frameRoot_iff_nonlast : ∀ fid : Index, fid < cfg.stack.dropLast.length →
      ∀ start, FrameRoot cfg fid start ↔ FrameRoot cfg' fid start := by
    intro fid hfid start
    unfold FrameRoot
    constructor
    · rintro (⟨fr, hfr, hidx, var, hlookup⟩ | ⟨fr, hfr, hidx, region, hlookup, hstart⟩)
      · exact Or.inl ⟨fr, frame_transport_up fr hfr (hidx ▸ hfid), hidx, var, hlookup⟩
      · have hridne : fr.regionId ≠ cfg.freshRegionId := by
          intro hc
          rw [hc] at hlookup
          exact RuntimeConfig.freshRegionId_not_mem cfg (makeRegion_corollary_mem_keys_of_lookup hlookup)
        exact Or.inr ⟨fr, frame_transport_up fr hfr (hidx ▸ hfid), hidx, region,
          by rw [hheap_eq_at fr.regionId hridne]; exact hlookup, hstart⟩
    · rintro (⟨fr, hfr, hidx, var, hlookup⟩ | ⟨fr, hfr, hidx, region, hlookup, hstart⟩)
      · exact Or.inl ⟨fr, frame_transport_down fr hfr (hidx ▸ hfid), hidx, var, hlookup⟩
      · have hridne : fr.regionId ≠ cfg.freshRegionId := by
          intro hc
          have hfrCfg : fr ∈ cfg.stackWithIndex := frame_transport_down fr hfr (hidx ▸ hfid)
          obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfrCfg
          have hregeq : cfg.stack[n].regionId = fr.regionId := by rw [← hfeq]
          obtain ⟨region0, hlookup0, _⟩ := vcfg.l2 cfg.stack[n] (List.getElem_mem hn)
          rw [hregeq, hc] at hlookup0
          exact RuntimeConfig.freshRegionId_not_mem cfg (makeRegion_corollary_mem_keys_of_lookup hlookup0)
        exact Or.inr ⟨fr, frame_transport_down fr hfr (hidx ▸ hfid), hidx, region,
          by rw [← hheap_eq_at fr.regionId hridne]; exact hlookup, hstart⟩
  unfold CR3
  intro frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  -- `frame` can never be the mutated (last, highest-index) position (same index-ordering
  -- argument as makeObjStack/makeObjRegion).
  have hidx_lt : ∀ fr : FrameWithIndex, fr ∈ cfg'.stackWithIndex → fr.index < cfg'.stack.length := by
    intro fr hfr
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr
    have : fr.index = n := by rw [← hfeq]
    rw [this]; exact hn
  have hframe'_lt : frame'.index < cfg'.stack.length := hidx_lt frame' hframe'Mem
  have hframe_lt_dropLast : frame.index < cfg.stack.dropLast.length := by
    have hframe'_lt2 : frame'.index < cfg.stack.dropLast.length + 1 := by rw [← hlen']; exact hframe'_lt
    exact Nat.lt_of_lt_of_le hlt (Nat.le_of_lt_succ hframe'_lt2)
  have hframeMemCfg : frame ∈ cfg.stackWithIndex := frame_transport_down frame hframeMem hframe_lt_dropLast
  -- `frame.regionId` is never the fresh region: no stack frame's regionId ever changes under
  -- makeRegion, and the fresh region isn't the regionId of any pre-existing frame.
  have hframe_ridne : frame.regionId ≠ cfg.freshRegionId := by
    intro hc
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hframeMemCfg
    have hregeq : cfg.stack[n].regionId = frame.regionId := by rw [← hfeq]
    obtain ⟨region, hlookup, _⟩ := vcfg.l2 cfg.stack[n] (List.getElem_mem hn)
    rw [hregeq, hc] at hlookup
    exact RuntimeConfig.freshRegionId_not_mem cfg (makeRegion_corollary_mem_keys_of_lookup hlookup)
  -- Hence `oid` can never be the freshly-allocated object (which resolves into the fresh region).
  have hoid_ne_fresh : oid ≠ cfg.freshObjectId := by
    intro heq
    rw [heq, makeRegion_corollary_loc_fresh h] at hloc
    injection hloc with hloc'
    injection hloc' with hloc''
    exact hframe_ridne hloc''.symm
  have hlocDown : (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) := by
    rw [makeRegion_corollary_loc_eq vcfg h oid hoid_ne_fresh]; exact hloc
  by_cases hframe'Last : frame'.index = cfg.stack.dropLast.length
  · -- Last position: trace the reachability chain's root back through the mutation.
    rw [FrameReachable_iff_reflTransGen] at hreach
    obtain ⟨start, hroot, hrtg⟩ := hreach
    have hstart_oid : ∃ start_oid, start = Reference.OId start_oid := by
      rcases hrtg.cases_head with heq0 | ⟨c, hstep0, _⟩
      · exact ⟨oid, heq0⟩
      · exact hstep0.exists_oid_left
    obtain ⟨start_oid, hstart_eq⟩ := hstart_oid
    rw [hstart_eq] at hroot hrtg
    have hroot_down : FrameRoot cfg frame'.index (Reference.OId start_oid) :=
      makeRegion_corollary_frameRoot_down vcfg h hroot
    have hrtg_down : Relation.ReflTransGen (RefStep cfg) (Reference.OId start_oid) (Reference.OId oid) :=
      hrtg.mono (fun a b hab => (makeRegion_corollary_refStep_iff vcfg vcfg' h a b).mpr hab)
    have hreachDown : FrameReachable cfg frame'.index (Reference.OId oid) :=
      (FrameReachable_iff_reflTransGen cfg frame'.index (Reference.OId oid)).mpr
        ⟨Reference.OId start_oid, hroot_down, hrtg_down⟩
    have hframe1_get : cfg.stack[cfg.stack.dropLast.length]? = some frame1 := by
      conv_lhs => rw [stack_eq]
      simp
    have hlast1_mem :
        ({ frame1 with index := cfg.stack.dropLast.length } : FrameWithIndex) ∈ cfg.stackWithIndex := by
      obtain ⟨hh1, hheq⟩ := List.getElem?_eq_some_iff.mp hframe1_get
      unfold RuntimeConfig.stackWithIndex
      exact List.mem_mapIdx.mpr ⟨cfg.stack.dropLast.length, hh1, by rw [hheq]⟩
    have hlt' : frame.index < ({ frame1 with index := cfg.stack.dropLast.length } : FrameWithIndex).index := by
      dsimp only; rw [← hframe'Last]; exact hlt
    have hreachDown' :
        FrameReachable cfg ({ frame1 with index := cfg.stack.dropLast.length } : FrameWithIndex).index
          (Reference.OId oid) := by
      dsimp only; rw [← hframe'Last]; exact hreachDown
    have hconcDown : FrameReachable cfg frame.index (Reference.OId oid) :=
      vrcfg.cr3 frame hframeMemCfg { frame1 with index := cfg.stack.dropLast.length } hlast1_mem
        hlt' oid hlocDown hreachDown'
    rw [FrameReachable_iff_reflTransGen] at hconcDown ⊢
    obtain ⟨start2, hroot2, hrtg2⟩ := hconcDown
    exact ⟨start2, (frameRoot_iff_nonlast frame.index hframe_lt_dropLast start2).mp hroot2,
      hrtg2.mono (fun a b hab => (makeRegion_corollary_refStep_iff vcfg vcfg' h a b).mp hab)⟩
  · -- Non-last position: transport everything down to `cfg`, apply `vrcfg.cr3`, transport back up.
    have hframe'_lt_dropLast : frame'.index < cfg.stack.dropLast.length := by
      have hframe'_lt2 : frame'.index < cfg.stack.dropLast.length + 1 := by
        rw [← hlen']; exact hframe'_lt
      exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hframe'_lt2) hframe'Last
    have hframe'MemCfg : frame' ∈ cfg.stackWithIndex :=
      frame_transport_down frame' hframe'Mem hframe'_lt_dropLast
    have hreachDown : FrameReachable cfg frame'.index (Reference.OId oid) := by
      rw [FrameReachable_iff_reflTransGen] at hreach ⊢
      obtain ⟨start, hroot, hrtg⟩ := hreach
      exact ⟨start, (frameRoot_iff_nonlast frame'.index hframe'_lt_dropLast start).mpr hroot,
        hrtg.mono (fun a b hab => (makeRegion_corollary_refStep_iff vcfg vcfg' h a b).mpr hab)⟩
    have hconcDown : FrameReachable cfg frame.index (Reference.OId oid) :=
      vrcfg.cr3 frame hframeMemCfg frame' hframe'MemCfg hlt oid hlocDown hreachDown
    rw [FrameReachable_iff_reflTransGen] at hconcDown ⊢
    obtain ⟨start2, hroot2, hrtg2⟩ := hconcDown
    exact ⟨start2, (frameRoot_iff_nonlast frame.index hframe_lt_dropLast start2).mp hroot2,
      hrtg2.mono (fun a b hab => (makeRegion_corollary_refStep_iff vcfg vcfg' h a b).mp hab)⟩

theorem makeRegion_reachable_valid : ValidReachableConfig cfg →
  makeRegion x cfg = some cfg' →
  ValidReachableConfig cfg' := by
  intro vrcfg h
  exact { makeRegion_valid vrcfg.toValidConfig h with cr3 := makeRegion_cr3 vrcfg h }
