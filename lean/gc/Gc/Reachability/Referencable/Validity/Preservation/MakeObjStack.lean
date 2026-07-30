import Gc.Model.Mutation.MakeObjStack
import Gc.Model.Preservation.MakeObjStack
import Gc.Model.Preservation.Common
import Gc.Reachability.Referencable.Validity.Reachable

-- makeObjStack only ever inserts a *fresh* key into the last frame's own objMap, so for any
-- oid ≠ freshObjectId, `loc?` is completely unaffected. Adapts the same `loc_eq_of_ne_fresh`-style
-- local lemma already proved (twice, inline) inside Gc/Model/Preservation/MakeObjStack.lean's own
-- S2/S3 proofs, exposed here for reuse.
private theorem makeObjStack_corollary_loc_eq_of_ne_fresh {cfg cfg' : RuntimeConfig} {x : VarName}
    {oid : ObjectId} (h : makeObjStack x cfg = some cfg') (hne : oid ≠ cfg.freshObjectId) :
    (Reference.OId oid).loc? cfg = (Reference.OId oid).loc? cfg' := by
  obtain ⟨frame, hframe, hcfg'⟩ := makeObjStack_cases h
  have hfresh := RuntimeConfig.freshObjectId_not_mem cfg
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] := (List.dropLast_append_getLast? frame hframe).symm
  have frame_mem : frame ∈ cfg.stack := stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self frame)
  have fresh_not_in_frame : cfg.freshObjectId ∉ frame.objMap.keys := by
    intro hc
    apply hfresh
    unfold RuntimeConfig.objectIds Stack.objectIds Frame.objectIds
    rw [List.bind_eq_flatMap, List.flatMap_id, List.mem_append, List.mem_flatten]
    exact Or.inl ⟨frame.objMap.keys, List.mem_map_of_mem frame_mem, hc⟩
  set newFrame : Frame :=
    { regionId := frame.regionId, bridgeVar := frame.bridgeVar,
      objMap := AList.insert cfg.freshObjectId ∅ frame.objMap,
      varMap := AList.insert x (Reference.OId cfg.freshObjectId) frame.varMap } with newFrame_def
  have hcfg'2 : cfg' = { cfg with stack := cfg.stack.dropLast ++ [newFrame] } := by
    rw [hcfg', newFrame_def]
  have newFrame_keys_eq : (AList.keys newFrame.objMap).contains oid = (AList.keys frame.objMap).contains oid := by
    rw [newFrame_def]; dsimp
    rw [AList.keys_insert, List.erase_of_not_mem fresh_not_in_frame]
    simp [hne]
  unfold Reference.loc?
  dsimp only
  by_cases hb : (AList.keys frame.objMap).contains oid
  · have h1_cfg : cfg.stackWithIndex.findRev? (fun frame => (AList.keys frame.objMap).contains oid) =
        some ({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex) := by
      unfold RuntimeConfig.stackWithIndex
      conv_lhs => rw [stack_eq]
      rw [List.mapIdx_concat, List.findRev?_eq_find?_reverse, List.reverse_append, List.reverse_singleton,
        List.singleton_append]
      exact List.find?_cons_of_pos hb
    have h1_cfg' :
        (RuntimeConfig.stackWithIndex cfg').findRev? (fun frame => (AList.keys frame.objMap).contains oid) =
        some ({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex) := by
      rw [hcfg'2]
      unfold RuntimeConfig.stackWithIndex
      dsimp
      rw [List.mapIdx_concat, List.findRev?_eq_find?_reverse, List.reverse_append, List.reverse_singleton,
        List.singleton_append]
      apply List.find?_cons_of_pos
      rw [newFrame_keys_eq]; exact hb
    have hheap_eq : cfg'.heap = cfg.heap := by rw [hcfg'2]
    rw [h1_cfg, h1_cfg', hheap_eq]
    cases cfg.heap.entries.find? (fun x => x.snd.objMap.keys.contains oid) with
    | none => rfl
    | some _ => rfl
  · have h1_eq : cfg.stackWithIndex.findRev? (fun frame => (AList.keys frame.objMap).contains oid) =
        (RuntimeConfig.stackWithIndex cfg').findRev? (fun frame => (AList.keys frame.objMap).contains oid) := by
      rw [hcfg'2]
      unfold RuntimeConfig.stackWithIndex
      dsimp
      conv_lhs => rw [stack_eq]
      rw [List.mapIdx_concat, List.mapIdx_concat, List.findRev?_eq_find?_reverse, List.findRev?_eq_find?_reverse,
        List.reverse_append, List.reverse_append, List.reverse_singleton, List.reverse_singleton,
        List.singleton_append, List.singleton_append]
      have hbL : ¬ (AList.keys ({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex).objMap).contains
          oid = true := hb
      have hbR : ¬ (AList.keys ({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex).objMap).contains
          oid = true := by rw [newFrame_keys_eq]; exact hb
      have find_eqL :
          List.find? (fun frame => (AList.keys frame.objMap).contains oid)
            (({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex) ::
              (List.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) cfg.stack.dropLast).reverse) =
          List.find? (fun frame => (AList.keys frame.objMap).contains oid)
            (List.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) cfg.stack.dropLast).reverse :=
        List.find?_cons_of_neg hbL
      have find_eqR :
          List.find? (fun frame => (AList.keys frame.objMap).contains oid)
            (({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex) ::
              (List.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) cfg.stack.dropLast).reverse) =
          List.find? (fun frame => (AList.keys frame.objMap).contains oid)
            (List.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) cfg.stack.dropLast).reverse :=
        List.find?_cons_of_neg hbR
      rw [find_eqL, find_eqR]
    have hheap_eq : cfg'.heap = cfg.heap := by rw [hcfg'2]
    rw [h1_eq, hheap_eq]

-- Same fact, at the `objAt?` level: the heap is untouched entirely (Rgn case trivial), and for
-- Stk the found frame is either an untouched earlier position (identical record) or the last
-- position, whose objMap only differs at the fresh key (irrelevant since oid ≠ fresh).
private theorem makeObjStack_corollary_objAt_eq_of_ne_fresh (vcfg : ValidConfig cfg) (vcfg' : ValidConfig cfg')
    {oid : ObjectId} (h : makeObjStack x cfg = some cfg') (hne : oid ≠ cfg.freshObjectId) :
    (Reference.OId oid).objAt? cfg = (Reference.OId oid).objAt? cfg' := by
  have hlocEq := makeObjStack_corollary_loc_eq_of_ne_fresh h hne
  cases hloc : (Reference.OId oid).loc? cfg with
  | none =>
    unfold Reference.objAt?
    dsimp only
    rw [hloc, ← hlocEq, hloc]
  | some loc =>
    have hloc' : (Reference.OId oid).loc? cfg' = some loc := by rw [← hlocEq]; exact hloc
    cases loc with
    | Rgn rid0 =>
      unfold Reference.objAt?
      dsimp only
      rw [hloc, hloc']
      dsimp only
      obtain ⟨frame, hframe, hcfg'⟩ := makeObjStack_cases h
      have hheap_eq : cfg'.heap = cfg.heap := by rw [hcfg']
      rw [hheap_eq]
    | Stk fid0 =>
      obtain ⟨frame0, hframe0, hmem0⟩ := (oid_loc_stk_iff_in_stack vcfg).mp hloc
      obtain ⟨frame0', hframe0', hmem0'⟩ := (oid_loc_stk_iff_in_stack vcfg').mp hloc'
      obtain ⟨stackFrame0, hstackFrame0, hframe0_eq⟩ :
          ∃ sf, cfg.stack[fid0]? = some sf ∧ frame0 = { sf with index := fid0 } := by
        have h' := hframe0
        unfold RuntimeConfig.stackWithIndex at h'
        rw [List.getElem?_mapIdx, Option.map_eq_some_iff] at h'
        obtain ⟨sf, hsf, hsf_eq⟩ := h'
        exact ⟨sf, hsf, hsf_eq.symm⟩
      obtain ⟨stackFrame0', hstackFrame0', hframe0'_eq⟩ :
          ∃ sf, cfg'.stack[fid0]? = some sf ∧ frame0' = { sf with index := fid0 } := by
        have h' := hframe0'
        unfold RuntimeConfig.stackWithIndex at h'
        rw [List.getElem?_mapIdx, Option.map_eq_some_iff] at h'
        obtain ⟨sf, hsf, hsf_eq⟩ := h'
        exact ⟨sf, hsf, hsf_eq.symm⟩
      obtain ⟨frame, hframe, hcfg'⟩ := makeObjStack_cases h
      have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] := (List.dropLast_append_getLast? frame hframe).symm
      set newFrame : Frame :=
        { regionId := frame.regionId, bridgeVar := frame.bridgeVar,
          objMap := AList.insert cfg.freshObjectId ∅ frame.objMap,
          varMap := AList.insert x (Reference.OId cfg.freshObjectId) frame.varMap } with newFrame_def
      have hcfg'2 : cfg' = { cfg with stack := cfg.stack.dropLast ++ [newFrame] } := by
        rw [hcfg', newFrame_def]
      have hlast_cfg : cfg.stack[cfg.stack.dropLast.length]? = some frame := by
        conv_lhs => rw [stack_eq]
        simp
      have hlast_cfg' : cfg'.stack[cfg.stack.dropLast.length]? = some newFrame := by
        rw [hcfg'2]
        dsimp only
        simp
      have hmem0mem : frame0 ∈ cfg.stackWithIndex := List.mem_of_getElem? hframe0
      have hmem0mem' : frame0' ∈ cfg'.stackWithIndex := List.mem_of_getElem? hframe0'
      have hidx0 : frame0.index = fid0 := stackWithIndex_getElem_index_eq hframe0
      have hidx0' : frame0'.index = fid0 := stackWithIndex_getElem_index_eq hframe0'
      have hfind0 : cfg.stackWithIndex.find? (fun f => f.index == fid0) = some frame0 := by
        rw [← hidx0]; exact swap_corollary_stackWithIndex_find_eq hmem0mem
      have hfind0' : cfg'.stackWithIndex.find? (fun f => f.index == fid0) = some frame0' := by
        rw [← hidx0']; exact swap_corollary_stackWithIndex_find_eq hmem0mem'
      unfold Reference.objAt?
      dsimp only
      rw [hloc, hloc']
      dsimp only
      rw [hfind0, hfind0']
      by_cases hlastpos : fid0 = cfg.stack.dropLast.length
      · subst hlastpos
        rw [hlast_cfg] at hstackFrame0
        rw [hlast_cfg'] at hstackFrame0'
        injection hstackFrame0 with hstackFrame0_eq
        injection hstackFrame0' with hstackFrame0'_eq
        rw [hframe0_eq, hframe0'_eq, ← hstackFrame0_eq, ← hstackFrame0'_eq]
        exact (AList.lookup_insert_ne hne).symm
      · have hlt0 : fid0 < cfg.stack.dropLast.length := by
          have hlt := (List.getElem?_eq_some_iff.mp hstackFrame0).1
          have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by
            rw [stack_eq]; simp
          rw [hlen] at hlt
          exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hlt) hlastpos
        have hcfg'stack_eq : cfg'.stack[fid0]? = cfg.stack.dropLast[fid0]? := by
          rw [hcfg'2]
          dsimp only
          rw [List.getElem?_append_left hlt0]
        have hcfgstack_eq : cfg.stack[fid0]? = cfg.stack.dropLast[fid0]? := by
          conv_lhs => rw [stack_eq]
          rw [List.getElem?_append_left hlt0]
        rw [hcfgstack_eq] at hstackFrame0
        rw [hcfg'stack_eq] at hstackFrame0'
        rw [hstackFrame0] at hstackFrame0'
        injection hstackFrame0' with hstackFrame0'_eq
        rw [hframe0_eq, hframe0'_eq, hstackFrame0'_eq]

-- The freshly-allocated object always resolves on the stack (never in a region): its container
-- is the last frame's own (unchanged) index.
private theorem makeObjStack_corollary_loc_fresh {cfg cfg' : RuntimeConfig} {x : VarName}
    (h : makeObjStack x cfg = some cfg') :
    (Reference.OId cfg.freshObjectId).loc? cfg' = some (Location.Stk cfg.stack.dropLast.length) := by
  obtain ⟨frame, hframe, hcfg'⟩ := makeObjStack_cases h
  set newFrame : Frame :=
    { regionId := frame.regionId, bridgeVar := frame.bridgeVar,
      objMap := AList.insert cfg.freshObjectId ∅ frame.objMap,
      varMap := AList.insert x (Reference.OId cfg.freshObjectId) frame.varMap } with newFrame_def
  have hcfg'2 : cfg' = { cfg with stack := cfg.stack.dropLast ++ [newFrame] } := by
    rw [hcfg', newFrame_def]
  have hcontains : (AList.keys newFrame.objMap).contains cfg.freshObjectId = true := by
    rw [newFrame_def]
    dsimp only
    rw [AList.keys_insert, List.contains_iff_mem]
    exact List.mem_cons_self
  have hfresh_not_heap : cfg.freshObjectId ∉ cfg.heap.objectIds := by
    have hfresh := RuntimeConfig.freshObjectId_not_mem cfg
    unfold RuntimeConfig.objectIds at hfresh
    intro hc
    exact hfresh (List.mem_append_right _ hc)
  have hheap_none : cfg'.heap.entries.find? (fun x => x.snd.objMap.keys.contains cfg.freshObjectId) = none := by
    rw [List.find?_eq_none]
    intro pr hpr
    rw [hcfg'2] at hpr
    dsimp only at hpr
    intro hcon
    apply hfresh_not_heap
    unfold Heap.objectIds
    apply List.mem_flatten.mpr
    refine ⟨pr.2.objectIds, List.mem_map_of_mem (f := (·.2.objectIds)) hpr, ?_⟩
    unfold Region.objectIds
    exact List.contains_iff_mem.mp hcon
  unfold Reference.loc?
  dsimp only
  have h1_cfg' :
      (RuntimeConfig.stackWithIndex cfg').findRev? (fun frame => (AList.keys frame.objMap).contains cfg.freshObjectId) =
      some ({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex) := by
    rw [hcfg'2]
    unfold RuntimeConfig.stackWithIndex
    dsimp
    rw [List.mapIdx_concat, List.findRev?_eq_find?_reverse, List.reverse_append, List.reverse_singleton,
      List.singleton_append]
    exact List.find?_cons_of_pos hcontains
  rw [h1_cfg', hheap_none]

-- The freshly-allocated object's own content: an empty object, so it has no outgoing RefStep
-- edges at all in cfg'.
private theorem makeObjStack_corollary_objAt_fresh {cfg cfg' : RuntimeConfig} {x : VarName}
    (h : makeObjStack x cfg = some cfg') :
    (Reference.OId cfg.freshObjectId).objAt? cfg' = some (∅ : Object) := by
  obtain ⟨frame, hframe, hcfg'⟩ := makeObjStack_cases h
  set newFrame : Frame :=
    { regionId := frame.regionId, bridgeVar := frame.bridgeVar,
      objMap := AList.insert cfg.freshObjectId ∅ frame.objMap,
      varMap := AList.insert x (Reference.OId cfg.freshObjectId) frame.varMap } with newFrame_def
  have hcfg'2 : cfg' = { cfg with stack := cfg.stack.dropLast ++ [newFrame] } := by
    rw [hcfg', newFrame_def]
  unfold Reference.objAt?
  dsimp only
  rw [makeObjStack_corollary_loc_fresh h]
  dsimp only
  have hmem : ({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex) ∈ cfg'.stackWithIndex := by
    rw [hcfg'2]
    unfold RuntimeConfig.stackWithIndex
    dsimp only
    rw [List.mapIdx_concat]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hfind := swap_corollary_stackWithIndex_find_eq hmem
  dsimp only at hfind
  rw [hfind]
  rw [newFrame_def]
  exact AList.lookup_insert (a := cfg.freshObjectId) (b := (∅ : Object)) frame.objMap

-- `RefStep` is completely unaffected between cfg and cfg': the only new content is the freshly
-- allocated (isolated, no incoming or outgoing edges) object, so its presence never changes
-- whether any *other* RefStep holds.
private theorem makeObjStack_corollary_refStep_iff (vcfg : ValidConfig cfg) (vcfg' : ValidConfig cfg')
    (h : makeObjStack x cfg = some cfg') :
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
    exact ⟨obj, (makeObjStack_corollary_objAt_eq_of_ne_fresh vcfg vcfg' h hne).symm.trans hobjAt, hcontains⟩
  · rintro ⟨obj, hobjAt', hcontains⟩
    obtain ⟨oid, rfl⟩ : ∃ oid, a = Reference.OId oid := by
      cases a with
      | OId oid => exact ⟨oid, rfl⟩
      | RId _ => unfold Reference.objAt? at hobjAt'; simp at hobjAt'
    have hne : oid ≠ cfg.freshObjectId := by
      intro heq
      subst heq
      rw [makeObjStack_corollary_objAt_fresh h] at hobjAt'
      injection hobjAt' with hobj_eq
      rw [← hobj_eq] at hcontains
      simp [Object.refs] at hcontains
    exact ⟨obj, (makeObjStack_corollary_objAt_eq_of_ne_fresh vcfg vcfg' h hne).trans hobjAt', hcontains⟩

-- A `RefStep`'s source is never the freshly-allocated object (its object is empty, contributing
-- no outgoing edges) -- true in *either* config, uniformly, since `objAt?` at `freshObjectId` is
-- `none` in cfg and `some ∅` in cfg', and both give an immediately-false `.refs.contains`.
private theorem makeObjStack_corollary_refStep_source_ne_fresh_cfg' {cfg cfg' : RuntimeConfig} {x : VarName}
    (h : makeObjStack x cfg = some cfg') {a b : Reference} (hstep : RefStep cfg' a b) :
    a ≠ Reference.OId cfg.freshObjectId := by
  intro heq
  subst heq
  obtain ⟨obj, hobjAt, hcontains⟩ := hstep
  rw [makeObjStack_corollary_objAt_fresh h] at hobjAt
  injection hobjAt with hobj_eq
  rw [← hobj_eq] at hcontains
  simp [Object.refs] at hcontains

-- Given a frame on cfg'.stackWithIndex whose root value is a known-non-fresh oid, transport its
-- `FrameRoot` witness down to cfg: the var-disjunct's witness frame is either an untouched
-- (non-last) position (identical record) or the last position, where the *only* changed slot
-- (`x ↦ fresh`) can't be the one supplying a non-fresh value; the bridge-disjunct is unconditional
-- since the heap (hence every region's bridgeObjectId) is untouched entirely.
private theorem makeObjStack_corollary_frameRoot_down {cfg cfg' : RuntimeConfig} {x : VarName}
    (h : makeObjStack x cfg = some cfg')
    {fid : Index} {start_oid : ObjectId} (hne : start_oid ≠ cfg.freshObjectId)
    (hroot : FrameRoot cfg' fid (Reference.OId start_oid)) :
    FrameRoot cfg fid (Reference.OId start_oid) := by
  obtain ⟨frame, hframe, hcfg'⟩ := makeObjStack_cases h
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] := (List.dropLast_append_getLast? frame hframe).symm
  set newFrame : Frame :=
    { regionId := frame.regionId, bridgeVar := frame.bridgeVar,
      objMap := AList.insert cfg.freshObjectId ∅ frame.objMap,
      varMap := AList.insert x (Reference.OId cfg.freshObjectId) frame.varMap } with newFrame_def
  have hcfg'2 : cfg' = { cfg with stack := cfg.stack.dropLast ++ [newFrame] } := by
    rw [hcfg', newFrame_def]
  have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq]; simp
  have hlen' : cfg'.stack.length = cfg.stack.dropLast.length + 1 := by rw [hcfg'2]; simp
  -- regionId agrees position-by-position between cfg and cfg', for both the untouched (non-last)
  -- frames and the mutated last frame (regionId isn't one of the fields makeObjStack changes).
  -- Stated via `[n]?` (Option-valued) throughout to dodge the dependent-proof `rw` failures that a
  -- raw `[n]'h`-indexed version hits when `hcfg'2` is rewritten under it.
  have hregionId_eq : ∀ n : ℕ, (cfg.stack[n]?).map Frame.regionId = (cfg'.stack[n]?).map Frame.regionId := by
    intro n
    by_cases hlp : n = cfg.stack.dropLast.length
    · have e1 : cfg.stack[n]? = some frame := by
        conv_lhs => rw [stack_eq, hlp]
        simp
      have e2 : cfg'.stack[n]? = some newFrame := by
        rw [hcfg'2]; dsimp only; rw [hlp]
        simp
      rw [e1, e2]
      simp [newFrame_def]
    · by_cases hlt : n < cfg.stack.dropLast.length
      · have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
          conv_lhs => rw [stack_eq]
          rw [List.getElem?_append_left hlt]
        have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
          rw [hcfg'2]; dsimp only
          rw [List.getElem?_append_left hlt]
        rw [e1, e2]
      · have e1 : cfg.stack[n]? = none := List.getElem?_eq_none (by omega)
        have e2 : cfg'.stack[n]? = none := List.getElem?_eq_none (by omega)
        rw [e1, e2]
  unfold FrameRoot
  unfold FrameRoot at hroot
  rcases hroot with ⟨fr, hfr, hidx, var, hlookup⟩ | ⟨fr, hfr, hidx, region, hlookup, hstart⟩
  · obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr
    have hidx_n : fr.index = n := by rw [← hfeq]
    have hidx_fid : fid = n := by rw [← hidx, hidx_n]
    by_cases hlastpos : n = cfg.stack.dropLast.length
    · -- last position: fr = {newFrame with index := n}
      have hnewFr_mem : ({ newFrame with index := n } : FrameWithIndex) ∈ cfg'.stackWithIndex := by
        rw [hcfg'2]
        unfold RuntimeConfig.stackWithIndex
        rw [List.mapIdx_concat, ← hlastpos]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      have hfr_eq : fr = { newFrame with index := n } :=
        swap_corollary_stackWithIndex_index_inj hfr hnewFr_mem hidx_n
      rw [hfr_eq] at hlookup
      dsimp only at hlookup
      by_cases hvarx : var = x
      · exfalso
        subst hvarx
        rw [AList.lookup_insert (a := var) (b := (Reference.OId cfg.freshObjectId)) frame.varMap] at hlookup
        injection hlookup with hlookup_eq
        injection hlookup_eq with hlookup_eq2
        exact hne hlookup_eq2.symm
      · rw [AList.lookup_insert_ne hvarx] at hlookup
        left
        refine ⟨{ frame with index := n }, ?_, hidx_fid.symm, var, hlookup⟩
        unfold RuntimeConfig.stackWithIndex
        conv_lhs => rw [stack_eq]
        rw [List.mapIdx_concat, ← hlastpos]
        exact List.mem_append_right _ (List.mem_singleton_self _)
    · -- non-last position: fr ∈ cfg.stackWithIndex too, same record
      have hlt : n < cfg.stack.dropLast.length := by omega
      have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
        conv_lhs => rw [stack_eq]
        rw [List.getElem?_append_left hlt]
      have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
        rw [hcfg'2]; dsimp only
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
  · -- bridge disjunct: heap is untouched, and regionId is unchanged at every position (last or
    -- not), so this transports directly regardless of whether fr sits at the mutated position.
    right
    have hheap_eq : cfg'.heap = cfg.heap := by rw [hcfg']
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr
    have hidx_n : fr.index = n := by rw [← hfeq]
    have hidx_fid : fid = n := by rw [← hidx, hidx_n]
    have hfr_get? : cfg'.stack[n]? = some fr.toFrame := by
      rw [show fr.toFrame = cfg'.stack[n] from by rw [← hfeq]]
      exact List.getElem?_eq_getElem hn
    have hmapeq : (cfg.stack[n]?).map Frame.regionId = some fr.regionId := by
      rw [hregionId_eq n, hfr_get?]
      rfl
    obtain ⟨cfgFrame, hcfgFrame, hcfgFrame_regionId⟩ := Option.map_eq_some_iff.mp hmapeq
    obtain ⟨h1, heq⟩ := List.getElem?_eq_some_iff.mp hcfgFrame
    have hlookup2 : cfg.heap.lookup cfgFrame.regionId = some region := by
      rw [hcfgFrame_regionId, ← hheap_eq]; exact hlookup
    refine ⟨{ cfgFrame with index := n }, ?_, hidx_fid.symm, region, hlookup2, hstart⟩
    unfold RuntimeConfig.stackWithIndex
    exact List.mem_mapIdx.mpr ⟨n, h1, by rw [heq]⟩

-- `FrameReferencable` is completely unaffected at any position strictly before the mutated (last)
-- one -- the frame-transport argument `makeObjStack_cr3` already builds inline for itself
-- (`frame_transport_down`/`_up`/its own `FrameRoot` iff), packaged here as its own reusable
-- theorem since CR5 (`Gc/Reachability/Referencable/Validity/CR5.lean`) needs exactly this fact, not CR3's
-- later-frame-implies-earlier-frame shape.
theorem makeObjStack_corollary_frameReferencable_iff_of_lt (vcfg : ValidConfig cfg) (vcfg' : ValidConfig cfg')
    (h : makeObjStack x cfg = some cfg')
    {fid : Index} (hfid : fid < cfg.stack.dropLast.length) (ref : Reference) :
    FrameReferencable cfg fid ref ↔ FrameReferencable cfg' fid ref := by
  obtain ⟨frame1, hframe1, hcfg'⟩ := makeObjStack_cases h
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame1] :=
    (List.dropLast_append_getLast? frame1 hframe1).symm
  set newFrame1 : Frame :=
    { regionId := frame1.regionId, bridgeVar := frame1.bridgeVar,
      objMap := AList.insert cfg.freshObjectId ∅ frame1.objMap,
      varMap := AList.insert x (Reference.OId cfg.freshObjectId) frame1.varMap } with newFrame1_def
  have hcfg'2 : cfg' = { cfg with stack := cfg.stack.dropLast ++ [newFrame1] } := by
    rw [hcfg', newFrame1_def]
  have hheap_eq : cfg'.heap = cfg.heap := by rw [hcfg'2]
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
      rw [hcfg'2]; dsimp only
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
      rw [hcfg'2]; dsimp only
      rw [List.getElem?_append_left hlt]
    have hfr_get? : cfg.stack[n]? = some fr.toFrame := by
      rw [show fr.toFrame = cfg.stack[n] from by rw [← hfeq]]
      exact List.getElem?_eq_getElem hn
    have hcfg'n : cfg'.stack[n]? = some fr.toFrame := by rw [e2, ← e1, hfr_get?]
    obtain ⟨h1, heq⟩ := List.getElem?_eq_some_iff.mp hcfg'n
    unfold RuntimeConfig.stackWithIndex
    exact List.mem_mapIdx.mpr ⟨n, h1, by rw [heq, ← hidx_n]⟩
  have hfrRootIff : ∀ start, FrameRoot cfg fid start ↔ FrameRoot cfg' fid start := by
    intro start
    unfold FrameRoot
    constructor
    · rintro (⟨fr, hfr, hidx, var, hlookup⟩ | ⟨fr, hfr, hidx, region, hlookup, hstart⟩)
      · exact Or.inl ⟨fr, frame_transport_up fr hfr (hidx ▸ hfid), hidx, var, hlookup⟩
      · exact Or.inr ⟨fr, frame_transport_up fr hfr (hidx ▸ hfid), hidx, region,
          hheap_eq ▸ hlookup, hstart⟩
    · rintro (⟨fr, hfr, hidx, var, hlookup⟩ | ⟨fr, hfr, hidx, region, hlookup, hstart⟩)
      · exact Or.inl ⟨fr, frame_transport_down fr hfr (hidx ▸ hfid), hidx, var, hlookup⟩
      · exact Or.inr ⟨fr, frame_transport_down fr hfr (hidx ▸ hfid), hidx, region,
          hheap_eq ▸ hlookup, hstart⟩
  rw [FrameReferencable_iff_reflTransGen, FrameReferencable_iff_reflTransGen]
  constructor
  · rintro ⟨start, hroot, hrtg⟩
    exact ⟨start, (hfrRootIff start).mp hroot,
      hrtg.mono (fun a b hab => (makeObjStack_corollary_refStep_iff vcfg vcfg' h a b).mp hab)⟩
  · rintro ⟨start, hroot, hrtg⟩
    exact ⟨start, (hfrRootIff start).mpr hroot,
      hrtg.mono (fun a b hab => (makeObjStack_corollary_refStep_iff vcfg vcfg' h a b).mpr hab)⟩

theorem makeObjStack_cr3 : ValidReachableConfig cfg →
  makeObjStack x cfg = some cfg' →
  CR3 cfg' := by
  intro vrcfg h
  have vcfg := vrcfg.toValidConfig
  have vcfg' := makeObjStack_valid vcfg h
  obtain ⟨frame1, hframe1, hcfg'⟩ := makeObjStack_cases h
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame1] :=
    (List.dropLast_append_getLast? frame1 hframe1).symm
  set newFrame1 : Frame :=
    { regionId := frame1.regionId, bridgeVar := frame1.bridgeVar,
      objMap := AList.insert cfg.freshObjectId ∅ frame1.objMap,
      varMap := AList.insert x (Reference.OId cfg.freshObjectId) frame1.varMap } with newFrame1_def
  have hcfg'2 : cfg' = { cfg with stack := cfg.stack.dropLast ++ [newFrame1] } := by
    rw [hcfg', newFrame1_def]
  have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq]; simp
  have hlen' : cfg'.stack.length = cfg.stack.dropLast.length + 1 := by rw [hcfg'2]; simp
  have hheap_eq : cfg'.heap = cfg.heap := by rw [hcfg'2]
  -- Position-by-position "downward" and "upward" frame transport for non-last positions: those
  -- frames are literally the same record in cfg and cfg', so membership transports either way.
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
      rw [hcfg'2]; dsimp only
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
      rw [hcfg'2]; dsimp only
      rw [List.getElem?_append_left hlt]
    have hfr_get? : cfg.stack[n]? = some fr.toFrame := by
      rw [show fr.toFrame = cfg.stack[n] from by rw [← hfeq]]
      exact List.getElem?_eq_getElem hn
    have hcfg'n : cfg'.stack[n]? = some fr.toFrame := by rw [e2, ← e1, hfr_get?]
    obtain ⟨h1, heq⟩ := List.getElem?_eq_some_iff.mp hcfg'n
    unfold RuntimeConfig.stackWithIndex
    exact List.mem_mapIdx.mpr ⟨n, h1, by rw [heq, ← hidx_n]⟩
  have frameRoot_iff_nonlast : ∀ fid : Index, fid < cfg.stack.dropLast.length →
      ∀ start, FrameRoot cfg fid start ↔ FrameRoot cfg' fid start := by
    intro fid hfid start
    unfold FrameRoot
    constructor
    · rintro (⟨fr, hfr, hidx, var, hlookup⟩ | ⟨fr, hfr, hidx, region, hlookup, hstart⟩)
      · exact Or.inl ⟨fr, frame_transport_up fr hfr (hidx ▸ hfid), hidx, var, hlookup⟩
      · exact Or.inr ⟨fr, frame_transport_up fr hfr (hidx ▸ hfid), hidx, region,
          hheap_eq ▸ hlookup, hstart⟩
    · rintro (⟨fr, hfr, hidx, var, hlookup⟩ | ⟨fr, hfr, hidx, region, hlookup, hstart⟩)
      · exact Or.inl ⟨fr, frame_transport_down fr hfr (hidx ▸ hfid), hidx, var, hlookup⟩
      · exact Or.inr ⟨fr, frame_transport_down fr hfr (hidx ▸ hfid), hidx, region,
          hheap_eq ▸ hlookup, hstart⟩
  unfold CR3
  intro frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  -- `oid ≠ freshObjectId` (the fresh object resolves `Stk`, not `Rgn`), so `loc?` transports to
  -- cfg unconditionally.
  have hoid_ne_fresh : oid ≠ cfg.freshObjectId := by
    intro heq
    rw [heq, makeObjStack_corollary_loc_fresh h] at hloc
    simp at hloc
  have hlocDown : (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) := by
    rw [makeObjStack_corollary_loc_eq_of_ne_fresh h hoid_ne_fresh]; exact hloc
  -- `frame` (the region's owner) can never be the mutated (last, highest-index) position: it
  -- needs a strictly-later frame `frame'`, but no index exceeds the (unchanged) stack length.
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
  -- Is `frame'` itself at the mutated (last) position, or not?
  by_cases hframe'Last : frame'.index = cfg.stack.dropLast.length
  · -- Last position: trace the reachability chain's root back through the mutation.
    rw [FrameReferencable_iff_reflTransGen] at hreach
    obtain ⟨start, hroot, hrtg⟩ := hreach
    have hstart_oid : ∃ start_oid, start = Reference.OId start_oid := by
      rcases hrtg.cases_head with heq0 | ⟨c, hstep0, _⟩
      · exact ⟨oid, heq0⟩
      · exact hstep0.exists_oid_left
    obtain ⟨start_oid, hstart_eq⟩ := hstart_oid
    have hstart_ne_fresh : start_oid ≠ cfg.freshObjectId := by
      rcases hrtg.cases_head with heq0 | ⟨c, hstep0, _⟩
      · rw [hstart_eq] at heq0
        injection heq0 with heq0'
        rw [heq0']; exact hoid_ne_fresh
      · rw [hstart_eq] at hstep0
        intro hc
        exact makeObjStack_corollary_refStep_source_ne_fresh_cfg' h hstep0 (by rw [hc])
    rw [hstart_eq] at hroot hrtg
    have hroot_down : FrameRoot cfg frame'.index (Reference.OId start_oid) :=
      makeObjStack_corollary_frameRoot_down h hstart_ne_fresh hroot
    have hrtg_down : Relation.ReflTransGen (RefStep cfg) (Reference.OId start_oid) (Reference.OId oid) :=
      hrtg.mono (fun a b hab => (makeObjStack_corollary_refStep_iff vcfg vcfg' h a b).mpr hab)
    have hreachDown : FrameReferencable cfg frame'.index (Reference.OId oid) :=
      (FrameReferencable_iff_reflTransGen cfg frame'.index (Reference.OId oid)).mpr
        ⟨Reference.OId start_oid, hroot_down, hrtg_down⟩
    have hframe1_get : cfg.stack[cfg.stack.dropLast.length]? = some frame1 := by
      conv_lhs => rw [stack_eq]
      simp
    have hframe1WI_mem :
        ({ frame1 with index := cfg.stack.dropLast.length } : FrameWithIndex) ∈ cfg.stackWithIndex := by
      obtain ⟨h1, heq⟩ := List.getElem?_eq_some_iff.mp hframe1_get
      unfold RuntimeConfig.stackWithIndex
      exact List.mem_mapIdx.mpr ⟨cfg.stack.dropLast.length, h1, by rw [heq]⟩
    have hlt' : frame.index < ({ frame1 with index := cfg.stack.dropLast.length } : FrameWithIndex).index := by
      dsimp only; rw [← hframe'Last]; exact hlt
    have hreachDown' :
        FrameReferencable cfg ({ frame1 with index := cfg.stack.dropLast.length } : FrameWithIndex).index
          (Reference.OId oid) := by
      dsimp only; rw [← hframe'Last]; exact hreachDown
    have hconcDown : FrameReferencable cfg frame.index (Reference.OId oid) :=
      vrcfg.cr3 frame hframeMemCfg { frame1 with index := cfg.stack.dropLast.length } hframe1WI_mem
        hlt' oid hlocDown hreachDown'
    rw [FrameReferencable_iff_reflTransGen] at hconcDown ⊢
    obtain ⟨start2, hroot2, hrtg2⟩ := hconcDown
    exact ⟨start2, (frameRoot_iff_nonlast frame.index hframe_lt_dropLast start2).mp hroot2,
      hrtg2.mono (fun a b hab => (makeObjStack_corollary_refStep_iff vcfg vcfg' h a b).mp hab)⟩
  · -- Non-last position: transport everything down to `cfg`, apply `vrcfg.cr3`, transport back up.
    have hframe'_lt_dropLast : frame'.index < cfg.stack.dropLast.length := by
      have hframe'_lt2 : frame'.index < cfg.stack.dropLast.length + 1 := by
        rw [← hlen']; exact hframe'_lt
      exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hframe'_lt2) hframe'Last
    have hframe'MemCfg : frame' ∈ cfg.stackWithIndex :=
      frame_transport_down frame' hframe'Mem hframe'_lt_dropLast
    have hreachDown : FrameReferencable cfg frame'.index (Reference.OId oid) := by
      rw [FrameReferencable_iff_reflTransGen] at hreach ⊢
      obtain ⟨start, hroot, hrtg⟩ := hreach
      exact ⟨start, (frameRoot_iff_nonlast frame'.index hframe'_lt_dropLast start).mpr hroot,
        hrtg.mono (fun a b hab => (makeObjStack_corollary_refStep_iff vcfg vcfg' h a b).mpr hab)⟩
    have hconcDown : FrameReferencable cfg frame.index (Reference.OId oid) :=
      vrcfg.cr3 frame hframeMemCfg frame' hframe'MemCfg hlt oid hlocDown hreachDown
    rw [FrameReferencable_iff_reflTransGen] at hconcDown ⊢
    obtain ⟨start2, hroot2, hrtg2⟩ := hconcDown
    exact ⟨start2, (frameRoot_iff_nonlast frame.index hframe_lt_dropLast start2).mp hroot2,
      hrtg2.mono (fun a b hab => (makeObjStack_corollary_refStep_iff vcfg vcfg' h a b).mp hab)⟩

theorem makeObjStack_reachable_valid : ValidReachableConfig cfg →
  makeObjStack x cfg = some cfg' →
  ValidReachableConfig cfg' := by
  intro vrcfg h
  exact { makeObjStack_valid vrcfg.toValidConfig h with cr3 := makeObjStack_cr3 vrcfg h }
