import Gc.Model.Mutation.MakeObjRegion
import Gc.Model.Preservation.MakeObjRegion
import Gc.Model.Preservation.Common
import Gc.Reachability.Referencable.Basic

-- Every frame's `objMap` is completely unaffected by makeObjRegion (only the last frame's
-- `varMap` changes, and only the mutated region's `objMap` in the heap changes) -- so the
-- per-position `objMap` is unconditionally the same in cfg and cfg', at every index. Thin wrapper
-- around `Gc.Model.Preservation.Common`'s generic `stackWithIndex_objMap_get_eq_of_last_varMap_
-- update` (see `merge_corollary_objMap_get_eq`'s comment for why the same generic lemma applies
-- here despite a different value being inserted into `varMap`).
theorem makeObjRegion_corollary_objMap_get_eq {cfg cfg' : RuntimeConfig} {x : VarName}
    (h : makeObjRegion x cfg = some cfg') (n : ℕ) :
    (cfg.stack[n]?).map Frame.objMap = (cfg'.stack[n]?).map Frame.objMap := by
  obtain ⟨frame, region, hframeLast, hheapLookup, hregionOpen, hcfg'⟩ := makeObjRegion_cases h
  have hstack' : cfg'.stack = cfg.stack.dropLast ++
      [({ regionId := frame.regionId, bridgeVar := frame.bridgeVar, objMap := frame.objMap,
          varMap := AList.insert x (Reference.OId cfg.freshObjectId) frame.varMap } : Frame)] := by
    rw [hcfg']
  exact stackWithIndex_objMap_get_eq_of_last_varMap_update hframeLast hstack' n

-- The freshly-created object always resolves into the heap, at the current top frame's own
-- region (never onto the stack, since no frame's objMap ever changes). It's graph-isolated
-- (empty object), reused for the `RefStep`-source-never-fresh corollary below.
theorem makeObjRegion_corollary_objAt_fresh (vcfg : ValidConfig cfg)
    {cfg' : RuntimeConfig} {x : VarName} (h : makeObjRegion x cfg = some cfg') :
    (Reference.OId cfg.freshObjectId).objAt? cfg' = some (∅ : Object) := by
  obtain ⟨frame, hlast, hlocfresh⟩ := makeObjRegion_corollary_loc_fresh vcfg h
  obtain ⟨frame2, region, hframeLast2, hheapLookup, hregionOpen, hcfg'⟩ := makeObjRegion_cases h
  have hframe_eq : frame = frame2 := by rw [hlast] at hframeLast2; injection hframeLast2
  unfold Reference.objAt?
  dsimp only
  rw [hlocfresh]
  dsimp only
  rw [hcfg']
  dsimp only
  rw [hframe_eq, AList.lookup_insert]
  exact AList.lookup_insert (a := cfg.freshObjectId) (b := (∅ : Object)) region.objMap

-- For any oid other than the freshly-allocated one, `objAt?` (not just `loc?`) is unaffected.
-- Stack side: unconditional, since no frame's objMap ever changes. Heap side: the mutated
-- region's objMap only gains the fresh key, so any *other* key's lookup value is untouched.
theorem makeObjRegion_corollary_objAt_eq_of_ne_fresh (vcfg : ValidConfig cfg) (vcfg' : ValidConfig cfg')
    {x : VarName} {oid : ObjectId}
    (h : makeObjRegion x cfg = some cfg') (hne : oid ≠ cfg.freshObjectId) :
    (Reference.OId oid).objAt? cfg = (Reference.OId oid).objAt? cfg' := by
  have hlocEq := makeObjRegion_corollary_loc_eq vcfg h oid hne
  obtain ⟨frame, region, hframeLast, hheapLookup, hregionOpen, hcfg'⟩ := makeObjRegion_cases h
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
        have hmapeq1 := makeObjRegion_corollary_objMap_get_eq h fid0
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
      unfold Reference.objAt?
      dsimp only
      rw [hloc, hloc']
      dsimp only
      by_cases hrideq : rid0 = frame.regionId
      · subst hrideq
        have hlookup2 : cfg'.heap.lookup frame.regionId =
            some { region with objMap := AList.insert cfg.freshObjectId ∅ region.objMap } := by
          rw [hcfg']; dsimp only
          exact AList.lookup_insert (a := frame.regionId)
            (b := { region with objMap := AList.insert cfg.freshObjectId ∅ region.objMap }) cfg.heap
        rw [hheapLookup, hlookup2]
        exact (AList.lookup_insert_ne hne).symm
      · have hlookup'' : cfg'.heap.lookup rid0 = cfg.heap.lookup rid0 := by
          rw [hcfg']
          dsimp only
          exact AList.lookup_insert_ne hrideq
        rw [hlookup'']

-- `RefStep` is completely unaffected between cfg and cfg': the only new content is the freshly
-- allocated (isolated) object.
theorem makeObjRegion_corollary_refStep_iff (vcfg : ValidConfig cfg) (vcfg' : ValidConfig cfg')
    {x : VarName} (h : makeObjRegion x cfg = some cfg') :
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
    exact ⟨obj, (makeObjRegion_corollary_objAt_eq_of_ne_fresh vcfg vcfg' h hne).symm.trans hobjAt, hcontains⟩
  · rintro ⟨obj, hobjAt', hcontains⟩
    obtain ⟨oid, rfl⟩ : ∃ oid, a = Reference.OId oid := by
      cases a with
      | OId oid => exact ⟨oid, rfl⟩
      | RId _ => unfold Reference.objAt? at hobjAt'; simp at hobjAt'
    have hne : oid ≠ cfg.freshObjectId := by
      intro heq
      subst heq
      rw [makeObjRegion_corollary_objAt_fresh vcfg h] at hobjAt'
      injection hobjAt' with hobj_eq
      rw [← hobj_eq] at hcontains
      simp [Object.refs] at hcontains
    exact ⟨obj, (makeObjRegion_corollary_objAt_eq_of_ne_fresh vcfg vcfg' h hne).trans hobjAt', hcontains⟩

-- A `RefStep`'s source in cfg' is never the freshly-allocated object (empty, no outgoing edges).
theorem makeObjRegion_corollary_refStep_source_ne_fresh_cfg' (vcfg : ValidConfig cfg)
    {cfg' : RuntimeConfig} {x : VarName} (h : makeObjRegion x cfg = some cfg')
    {a b : Reference} (hstep : RefStep cfg' a b) :
    a ≠ Reference.OId cfg.freshObjectId := by
  intro heq
  subst heq
  obtain ⟨obj, hobjAt, hcontains⟩ := hstep
  rw [makeObjRegion_corollary_objAt_fresh vcfg h] at hobjAt
  injection hobjAt with hobj_eq
  rw [← hobj_eq] at hcontains
  simp [Object.refs] at hcontains

-- Given a frame on cfg'.stackWithIndex whose root value is a known-non-fresh oid, transport its
-- `FrameRoot` witness down to cfg: the var-disjunct's witness frame is either an untouched
-- (non-last) position (identical record) or the last position, where the *only* changed slot
-- (`x ↦ fresh`) can't be the one supplying a non-fresh value; the bridge-disjunct only ever reads
-- `bridgeObjectId`, which is untouched by makeObjRegion at every heap key.
theorem makeObjRegion_corollary_frameRoot_down {cfg cfg' : RuntimeConfig} {x : VarName}
    (vcfg : ValidConfig cfg) (h : makeObjRegion x cfg = some cfg')
    {fid : Index} {start_oid : ObjectId} (hne : start_oid ≠ cfg.freshObjectId)
    (hroot : FrameRoot cfg' fid (Reference.OId start_oid)) :
    FrameRoot cfg fid (Reference.OId start_oid) := by
  obtain ⟨frame1, region1, hframe1Last, hheapLookup1, hregion1Open, hcfg'⟩ := makeObjRegion_cases h
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame1] := (List.dropLast_append_getLast? frame1 hframe1Last).symm
  set newFrame1 : Frame :=
    { regionId := frame1.regionId, bridgeVar := frame1.bridgeVar, objMap := frame1.objMap,
      varMap := AList.insert x (Reference.OId cfg.freshObjectId) frame1.varMap } with newFrame1_def
  set newRegion1 : Region :=
    { region1 with objMap := AList.insert cfg.freshObjectId ∅ region1.objMap } with newRegion1_def
  have hheap_eq : cfg'.heap.lookup frame1.regionId = some newRegion1 := by
    rw [hcfg']; dsimp only
    exact AList.lookup_insert (a := frame1.regionId) (b := newRegion1) cfg.heap
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
        rw [AList.lookup_insert (a := var) (b := (Reference.OId cfg.freshObjectId)) frame1.varMap] at hlookup
        injection hlookup with hlookup_eq
        injection hlookup_eq with hlookup_eq2
        exact hne hlookup_eq2.symm
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
  · -- bridge disjunct: only `.index`/`.regionId` and `bridgeObjectId` are read -- `regionId` is
    -- never touched by makeObjRegion (even at the last position), so a same-index cfg-side
    -- witness frame always exists, and `bridgeObjectId` is unaffected at every heap key.
    right
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr
    have hidx_n : fr.index = n := by rw [← hfeq]
    have hidx_fid : fid = n := by rw [← hidx, hidx_n]
    have hframe1_get : cfg.stack[cfg.stack.dropLast.length]? = some frame1 := by
      conv_lhs => rw [stack_eq]
      simp
    have hlast1_mem : ({ frame1 with index := cfg.stack.dropLast.length } : FrameWithIndex) ∈
        cfg.stackWithIndex := by
      obtain ⟨hh1, hheq⟩ := List.getElem?_eq_some_iff.mp hframe1_get
      unfold RuntimeConfig.stackWithIndex
      exact List.mem_mapIdx.mpr ⟨cfg.stack.dropLast.length, hh1, by rw [hheq]⟩
    by_cases hlastpos : n = cfg.stack.dropLast.length
    · have hnewFr_mem : ({ newFrame1 with index := n } : FrameWithIndex) ∈ cfg'.stackWithIndex := by
        rw [hcfg']
        unfold RuntimeConfig.stackWithIndex
        rw [List.mapIdx_concat, ← hlastpos]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      have hfr_eq : fr = { newFrame1 with index := n } :=
        swap_corollary_stackWithIndex_index_inj hfr hnewFr_mem hidx_n
      have hfr_regionId : fr.regionId = frame1.regionId := by rw [hfr_eq]
      have hlast1_mem' : ({ frame1 with index := n } : FrameWithIndex) ∈ cfg.stackWithIndex := by
        rw [hlastpos]; exact hlast1_mem
      rw [hfr_regionId, hheap_eq] at hlookup
      injection hlookup with hlookup_eq
      -- hlookup_eq : {region1 with objMap := insert fresh ∅ region1.objMap} = region --
      -- bridgeObjectId is untouched by that update, so region1 itself (the *old* record) is a
      -- valid cfg-side witness for the same bridgeObjectId.
      have hstart' : Reference.OId start_oid = Reference.OId region1.bridgeObjectId := by
        rw [hstart, ← hlookup_eq]
      exact ⟨{ frame1 with index := n }, hlast1_mem', hidx_fid.symm, region1, hheapLookup1, hstart'⟩
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
      have hmem : fr ∈ cfg.stackWithIndex := by
        unfold RuntimeConfig.stackWithIndex
        exact List.mem_mapIdx.mpr ⟨n, h1, by rw [heq, ← hidx_n]⟩
      have hridne : fr.regionId ≠ frame1.regionId := by
        intro hc
        have hidxeq := merge_corollary_regionId_unique_index vcfg.s1 hmem hlast1_mem hc
        rw [hidx_n] at hidxeq
        dsimp only at hidxeq
        exact hlastpos hidxeq
      have hlookup'' : cfg'.heap.lookup fr.regionId = cfg.heap.lookup fr.regionId := by
        rw [hcfg']; dsimp only; exact AList.lookup_insert_ne hridne
      refine ⟨fr, hmem, hidx, region, ?_, hstart⟩
      rw [hlookup''] at hlookup
      exact hlookup

-- `FrameReferencable` is completely unaffected at any position strictly before the mutated (last)
-- one -- the frame-transport argument `makeObjRegion_cr3` already builds inline for itself
-- (`frame_transport_down`/`_up`/its own `FrameRoot` iff), packaged here as its own reusable
-- theorem since CR5 (`Gc/Reachability/Referencable/CR5/*.lean`) needs exactly this fact, not CR3's
-- later-frame-implies-earlier-frame shape. Mirrors `makeObjStack_corollary_frameReferencable_iff_of_lt`.
theorem makeObjRegion_corollary_frameReferencable_iff_of_lt (vcfg : ValidConfig cfg) (vcfg' : ValidConfig cfg')
    (h : makeObjRegion x cfg = some cfg')
    {fid : Index} (hfid : fid < cfg.stack.dropLast.length) (ref : Reference) :
    FrameReferencable cfg fid ref ↔ FrameReferencable cfg' fid ref := by
  obtain ⟨frame1, region1, hframe1Last, hheapLookup1, hregion1Open, hcfg'⟩ := makeObjRegion_cases h
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame1] := (List.dropLast_append_getLast? frame1 hframe1Last).symm
  set newRegion1 : Region :=
    { region1 with objMap := AList.insert cfg.freshObjectId ∅ region1.objMap } with newRegion1_def
  have hheap_eq : cfg'.heap.lookup frame1.regionId = some newRegion1 := by
    rw [hcfg']; dsimp only
    exact AList.lookup_insert (a := frame1.regionId) (b := newRegion1) cfg.heap
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
  have hheap_eq_at : ∀ rid, rid ≠ frame1.regionId → cfg'.heap.lookup rid = cfg.heap.lookup rid := by
    intro rid hrid
    rw [hcfg']; dsimp only; exact AList.lookup_insert_ne hrid
  have hfrRootIff : ∀ start, FrameRoot cfg fid start ↔ FrameRoot cfg' fid start := by
    intro start
    unfold FrameRoot
    constructor
    · rintro (⟨fr, hfr, hidx, var, hlookup⟩ | ⟨fr, hfr, hidx, region, hlookup, hstart⟩)
      · exact Or.inl ⟨fr, frame_transport_up fr hfr (hidx ▸ hfid), hidx, var, hlookup⟩
      · right
        by_cases hrideq : fr.regionId = frame1.regionId
        · rw [hrideq, hheapLookup1] at hlookup
          injection hlookup with hlookup_eq
          refine ⟨fr, frame_transport_up fr hfr (hidx ▸ hfid), hidx, newRegion1, ?_, ?_⟩
          · rw [hrideq]; exact hheap_eq
          · rw [hstart, ← hlookup_eq]
        · refine ⟨fr, frame_transport_up fr hfr (hidx ▸ hfid), hidx, region, ?_, hstart⟩
          rw [hheap_eq_at fr.regionId hrideq]; exact hlookup
    · rintro (⟨fr, hfr, hidx, var, hlookup⟩ | ⟨fr, hfr, hidx, region, hlookup, hstart⟩)
      · exact Or.inl ⟨fr, frame_transport_down fr hfr (hidx ▸ hfid), hidx, var, hlookup⟩
      · right
        by_cases hrideq : fr.regionId = frame1.regionId
        · rw [hrideq, hheap_eq] at hlookup
          injection hlookup with hlookup_eq
          refine ⟨fr, frame_transport_down fr hfr (hidx ▸ hfid), hidx, region1, ?_, ?_⟩
          · rw [hrideq]; exact hheapLookup1
          · rw [hstart, ← hlookup_eq]
        · refine ⟨fr, frame_transport_down fr hfr (hidx ▸ hfid), hidx, region, ?_, hstart⟩
          rw [← hheap_eq_at fr.regionId hrideq]; exact hlookup
  rw [FrameReferencable_iff_reflTransGen, FrameReferencable_iff_reflTransGen]
  constructor
  · rintro ⟨start, hroot, hrtg⟩
    exact ⟨start, (hfrRootIff start).mp hroot,
      hrtg.mono (fun a b hab => (makeObjRegion_corollary_refStep_iff vcfg vcfg' h a b).mp hab)⟩
  · rintro ⟨start, hroot, hrtg⟩
    exact ⟨start, (hfrRootIff start).mpr hroot,
      hrtg.mono (fun a b hab => (makeObjRegion_corollary_refStep_iff vcfg vcfg' h a b).mpr hab)⟩

