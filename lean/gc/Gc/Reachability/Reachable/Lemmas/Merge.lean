import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Mutation.Mutation
import Gc.Model.Preservation
import Gc.Reachability.Reachable.Semantics
import Gc.Reachability.Reachable.Basic
import Gc.Reachability.Reachable.Lemmas.Common

-- ===== merge =====

-- An allocated object id always resolves somewhere (never `none`); reproven here since this layer can't import `Gc.Reachability.Referencable`.
theorem loc_ne_none_of_mem_objectIds (cfg : RuntimeConfig) (hvalid : ValidConfig cfg) (oid : ObjectId)
    (hmem : oid ∈ cfg.objectIds) : (Reference.OId oid).loc? cfg ≠ none := by
  unfold RuntimeConfig.objectIds at hmem
  rw [List.mem_append] at hmem
  unfold Reference.loc?
  dsimp only
  cases hs : cfg.stackWithIndex.findRev? (fun frame => frame.objMap.keys.contains oid) with
  | some frame => rw [oid_in_stack_implies_not_in_heap hvalid hs]; simp
  | none =>
    cases hh : cfg.heap.entries.find? (fun x => x.snd.objMap.keys.contains oid) with
    | some pr => simp
    | none =>
      simp only [ne_eq, not_true_eq_false]
      rcases hmem with hmem_stack | hmem_heap
      · unfold Stack.objectIds at hmem_stack
        rw [List.bind_eq_flatMap, List.flatMap_id, List.mem_flatten] at hmem_stack
        obtain ⟨keys, hkeys_mem, hoid_mem⟩ := hmem_stack
        obtain ⟨frame0, hframe0_mem, hframe0_eq⟩ := List.mem_map.mp hkeys_mem
        unfold Frame.objectIds at hframe0_eq
        rw [← hframe0_eq] at hoid_mem
        obtain ⟨n, hn, hn_eq⟩ := List.mem_iff_getElem.mp hframe0_mem
        have hlen : n < cfg.stackWithIndex.length := by
          unfold RuntimeConfig.stackWithIndex; rwa [List.length_mapIdx]
        have hget : cfg.stackWithIndex[n].objMap = frame0.objMap := by
          unfold RuntimeConfig.stackWithIndex
          rw [List.getElem_mapIdx, hn_eq]
        have hmemW := List.getElem_mem hlen
        have hcontains : cfg.stackWithIndex[n].objMap.keys.contains oid = true := by
          rw [hget]; exact List.contains_iff_mem.mpr (AList.mem_keys.mpr hoid_mem)
        rw [List.findRev?_eq_find?_reverse] at hs
        exact List.find?_eq_none.mp hs cfg.stackWithIndex[n] (List.mem_reverse.mpr hmemW) hcontains
      · unfold Heap.objectIds at hmem_heap
        rw [List.mem_flatten] at hmem_heap
        obtain ⟨keys, hkeys_mem, hoid_mem⟩ := hmem_heap
        obtain ⟨pr, hpr_mem, hpr_eq⟩ := List.mem_map.mp hkeys_mem
        unfold Region.objectIds at hpr_eq
        rw [← hpr_eq] at hoid_mem
        have hcontains : pr.2.objMap.keys.contains oid = true :=
          List.contains_iff_mem.mpr (AList.mem_keys.mpr hoid_mem)
        exact List.find?_eq_none.mp hh pr hpr_mem hcontains

-- merge relocates objects between heap keys but never creates/destroys any object id (mirrors `merge_L1`).
theorem merge_objectIds_perm (vcfg : ValidConfig cfg) {x : VarName} {cfg' : RuntimeConfig}
    (h : merge x cfg = some cfg') : cfg'.objectIds.Perm cfg.objectIds := by
  have l1 := vcfg.l1
  obtain ⟨frame, rid', region, region', hframe, hxref, hregion, hregion', hclosed, hopen, hcfg'⟩ :=
    merge_cases h
  subst hcfg'
  have hne := merge_corollary_rid_ne_regionId hregion hregion' hclosed hopen
  have heap_perm := merge_corollary_heap_objectIds_perm l1 hregion hregion' hne
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
    (List.dropLast_append_getLast? frame hframe).symm
  unfold RuntimeConfig.objectIds
  dsimp only
  have stack_objectIds_eq : Stack.objectIds (cfg.stack.dropLast ++
      [{ frame with varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) }]) =
      Stack.objectIds cfg.stack := by
    conv_rhs => rw [stack_eq]
    unfold Stack.objectIds
    rw [List.map_append, List.map_append]
    rfl
  rw [stack_objectIds_eq]
  exact List.Perm.append_left (Stack.objectIds cfg.stack) heap_perm

-- Every frame's `objMap` is unaffected by merge (only the last frame's `varMap` changes); wraps `stackWithIndex_objMap_get_eq_of_last_varMap_update`.
theorem merge_corollary_objMap_get_eq {cfg cfg' : RuntimeConfig} {x : VarName}
    (h : merge x cfg = some cfg') (n : ℕ) :
    (cfg.stack[n]?).map Frame.objMap = (cfg'.stack[n]?).map Frame.objMap := by
  obtain ⟨frame, rid', region, region', hframe, hxref, hregion, hregion', hclosed, hopen, hcfg'⟩ :=
    merge_cases h
  have hstack' : cfg'.stack = cfg.stack.dropLast ++
      [({ regionId := frame.regionId, bridgeVar := frame.bridgeVar, objMap := frame.objMap,
          varMap := AList.insert x (Reference.OId region'.bridgeObjectId) frame.varMap } : Frame)] := by
    rw [hcfg']
  exact stackWithIndex_objMap_get_eq_of_last_varMap_update hframe hstack' n

-- On disjoint keys, `.lookup` on the union agrees with `.lookup` on whichever side has the key.
theorem merge_corollary_union_lookup_left {region region' : Region} {oid : ObjectId}
    (hoid : oid ∈ region.objMap.keys)
    (heq : (region.objMap ∪ region'.objMap).entries = region.objMap.entries ++ region'.objMap.entries) :
    (region.objMap ∪ region'.objMap).lookup oid = region.objMap.lookup oid := by
  unfold AList.lookup
  rw [heq, List.dlookup_append]
  cases hv : List.dlookup oid region.objMap.entries with
  | none =>
    exfalso
    have : region.objMap.lookup oid = none := by unfold AList.lookup; rw [hv]
    rw [AList.lookup_eq_none] at this
    exact this hoid
  | some v => rfl

theorem merge_corollary_union_lookup_right {region region' : Region} {oid : ObjectId}
    (hoid : oid ∈ region'.objMap.keys)
    (hdisj : ∀ o ∈ region.objMap.keys, o ∉ region'.objMap.keys)
    (heq : (region.objMap ∪ region'.objMap).entries = region.objMap.entries ++ region'.objMap.entries) :
    (region.objMap ∪ region'.objMap).lookup oid = region'.objMap.lookup oid := by
  unfold AList.lookup
  rw [heq, List.dlookup_append]
  have hnone : List.dlookup oid region.objMap.entries = none := by
    have : region.objMap.lookup oid = none := by
      rw [AList.lookup_eq_none]
      intro hc
      exact hdisj oid hc hoid
    unfold AList.lookup at this
    exact this
  rw [hnone]
  rfl

-- `objAt?` is unconditionally preserved by merge (only relocates heap entries, never edits content); ported from Referencable's private `merge_corollary_objAt_eq`.
theorem merge_objAt_eq (vcfg : ValidConfig cfg) {x : VarName} {cfg' : RuntimeConfig}
    (h : merge x cfg = some cfg') (oid : ObjectId) :
    (Reference.OId oid).objAt? cfg = (Reference.OId oid).objAt? cfg' := by
  have vcfg' := merge_valid vcfg h
  have l1 := vcfg.l1
  obtain ⟨frame, rid', region, region', hframe, hxref, hregion, hregion', hclosed, hopen, hcfg'⟩ :=
    merge_cases h
  have hne := merge_corollary_rid_ne_regionId hregion hregion' hclosed hopen
  have hdisj := merge_corollary_disjoint_keys l1 hregion hregion' hne
  have hunion_append := merge_corollary_union_append l1 hregion hregion' hne
  have hobjeq : ({ frame with varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) } :
      Frame).objMap = frame.objMap := rfl
  cases hloc : (Reference.OId oid).loc? cfg with
  | none =>
    have hloc' : (Reference.OId oid).loc? cfg' = none := by
      by_contra hc
      have hmem' : oid ∈ cfg'.objectIds := by
        rcases Option.ne_none_iff_exists'.mp hc with ⟨loc', hloc'eq⟩
        cases loc' with
        | Stk fid0 =>
          obtain ⟨frame0, hframe0, hmem0⟩ := (oid_loc_stk_iff_in_stack vcfg').mp hloc'eq
          obtain ⟨sf0, hsf0, hsf0_eq⟩ : ∃ sf, cfg'.stack[fid0]? = some sf ∧ frame0 = { sf with index := fid0 } := by
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
        | Rgn rid0 =>
          obtain ⟨region0, hlookup0, hmem0⟩ := (oid_loc_rgn_iff_in_heap vcfg').mp hloc'eq
          unfold RuntimeConfig.objectIds
          apply List.mem_append_right
          exact heap_objectIds_of_mem (AList.lookup_mem_entries hlookup0) (AList.mem_keys.mpr hmem0)
      have hmem : oid ∈ cfg.objectIds := (merge_objectIds_perm vcfg h).mem_iff.mp hmem'
      exact loc_ne_none_of_mem_objectIds cfg vcfg oid hmem hloc
    unfold Reference.objAt?
    dsimp only
    rw [hloc, hloc']
  | some loc =>
    cases loc with
    | Stk fid0 =>
      obtain ⟨frame0, hframe0, hmem0⟩ := (oid_loc_stk_iff_in_stack vcfg).mp hloc
      obtain ⟨sf0, hsf0, hsf0_eq⟩ : ∃ sf, cfg.stack[fid0]? = some sf ∧ frame0 = { sf with index := fid0 } := by
        have h' := hframe0
        unfold RuntimeConfig.stackWithIndex at h'
        rw [List.getElem?_mapIdx, Option.map_eq_some_iff] at h'
        obtain ⟨sf, hsf, hsf_eq⟩ := h'
        exact ⟨sf, hsf, hsf_eq.symm⟩
      have hmapeq1 := merge_corollary_objMap_get_eq h fid0
      rw [hsf0] at hmapeq1
      obtain ⟨sf0', hsf0', hsf0'_objMap⟩ := Option.map_eq_some_iff.mp hmapeq1.symm
      have hsf0_objMap_eq : sf0.objMap = frame0.objMap := by rw [hsf0_eq]
      have hmem0' : oid ∈ ({ sf0' with index := fid0 } : FrameWithIndex).objMap := by
        show oid ∈ sf0'.objMap
        rw [hsf0'_objMap, hsf0_objMap_eq]
        exact hmem0
      have hcfg'_swi : cfg'.stackWithIndex[fid0]? = some ({ sf0' with index := fid0 } : FrameWithIndex) := by
        unfold RuntimeConfig.stackWithIndex
        rw [List.getElem?_mapIdx, hsf0']
        rfl
      have hloc' : (Reference.OId oid).loc? cfg' = some (Location.Stk fid0) :=
        (oid_loc_stk_iff_in_stack vcfg').mpr ⟨{ sf0' with index := fid0 }, hcfg'_swi, hmem0'⟩
      have hmem0mem : frame0 ∈ cfg.stackWithIndex := List.mem_of_getElem? hframe0
      have hmem0mem' : ({ sf0' with index := fid0 } : FrameWithIndex) ∈ cfg'.stackWithIndex := by
        obtain ⟨hn, heq⟩ := List.getElem?_eq_some_iff.mp hsf0'
        unfold RuntimeConfig.stackWithIndex
        exact List.mem_mapIdx.mpr ⟨fid0, hn, by rw [heq]⟩
      have hidx0 : frame0.index = fid0 := by rw [hsf0_eq]
      have hfind0 : cfg.stackWithIndex.find? (fun f => f.index == fid0) = some frame0 := by
        rw [← hidx0]; exact swap_corollary_stackWithIndex_find_eq hmem0mem
      have hfind0' : cfg'.stackWithIndex.find? (fun f => f.index == fid0) = some { sf0' with index := fid0 } :=
        swap_corollary_stackWithIndex_find_eq hmem0mem'
      have hobjMap0 : frame0.objMap = ({ sf0' with index := fid0 } : FrameWithIndex).objMap := by
        show frame0.objMap = sf0'.objMap
        rw [← hsf0_objMap_eq, hsf0'_objMap]
      unfold Reference.objAt?
      dsimp only
      rw [hloc, hloc']
      dsimp only
      rw [hfind0, hfind0']
      exact congrArg (AList.lookup oid) hobjMap0
    | Rgn rid0 =>
      obtain ⟨region0, hlookup0, hmem0⟩ := (oid_loc_rgn_iff_in_heap vcfg).mp hloc
      have hstack_none : cfg.stackWithIndex.findRev? (fun f => f.objMap.keys.contains oid) = none :=
        merge_corollary_loc_rgn_stack_none hloc
      by_cases heqr : rid0 = frame.regionId
      · subst heqr
        rw [hregion, Option.some_inj] at hlookup0
        subst hlookup0
        have hoid0' : oid ∈ ({ region with objMap := region.objMap ∪ region'.objMap } : Region).objMap.keys :=
          AList.mem_union.mpr (Or.inl hmem0)
        have hloc' : (Reference.OId oid).loc? cfg' = some (Location.Rgn frame.regionId) := by
          rw [hcfg']
          exact merge_corollary_loc_of_mem l1 hregion hregion' hne hobjeq hframe hstack_none
            (AList.lookup_insert (a := frame.regionId)
              (b := { region with objMap := region.objMap ∪ region'.objMap }) (s := cfg.heap.erase rid')) hoid0'
        unfold Reference.objAt?
        dsimp only
        rw [hloc, hloc']
        dsimp only
        rw [hregion, hcfg']
        dsimp only
        rw [AList.lookup_insert]
        exact (merge_corollary_union_lookup_left (AList.mem_keys.mp hmem0) hunion_append).symm
      · by_cases hrid' : rid0 = rid'
        · subst hrid'
          rw [hregion', Option.some_inj] at hlookup0
          subst hlookup0
          have hoid0' : oid ∈ ({ region with objMap := region.objMap ∪ region'.objMap } : Region).objMap.keys :=
            AList.mem_union.mpr (Or.inr hmem0)
          have hloc' : (Reference.OId oid).loc? cfg' = some (Location.Rgn frame.regionId) := by
            rw [hcfg']
            exact merge_corollary_loc_of_mem l1 hregion hregion' hne hobjeq hframe hstack_none
              (AList.lookup_insert (a := frame.regionId)
                (b := { region with objMap := region.objMap ∪ region'.objMap }) (s := cfg.heap.erase rid0)) hoid0'
          unfold Reference.objAt?
          dsimp only
          rw [hloc, hloc']
          dsimp only
          rw [hregion', hcfg']
          dsimp only
          rw [AList.lookup_insert]
          exact (merge_corollary_union_lookup_right (AList.mem_keys.mp hmem0) hdisj hunion_append).symm
        · have hlookup_cfg' : cfg'.heap.lookup rid0 = cfg.heap.lookup rid0 := by
            rw [hcfg']
            dsimp only
            exact AList.lookup_insert_ne heqr |>.trans (AList.lookup_erase_ne hrid')
          have hloc' : (Reference.OId oid).loc? cfg' = some (Location.Rgn rid0) :=
            (oid_loc_rgn_iff_in_heap vcfg').mpr ⟨region0, by rw [hlookup_cfg']; exact hlookup0, hmem0⟩
          unfold Reference.objAt?
          dsimp only
          rw [hloc, hloc']
          dsimp only
          rw [hlookup_cfg']

-- ReachableStep from an `OId` is unconditionally preserved by merge (direct corollary of `merge_objAt_eq`).
theorem merge_oid_step_iff (vcfg : ValidConfig cfg) {x : VarName} {cfg' : RuntimeConfig}
    (h : merge x cfg = some cfg') (oid : ObjectId) (b : Reference) :
    ReachableStep cfg (Reference.OId oid) b ↔ ReachableStep cfg' (Reference.OId oid) b := by
  rw [ReachableStep_oid_iff, ReachableStep_oid_iff, merge_objAt_eq vcfg h oid]

-- `ReachableStep` from `RId rid ≠ rid'` is unconditional: untouched by merge's insert/erase, and the active region stays Open.
theorem merge_rid_step_iff_of_ne {cfg cfg' : RuntimeConfig} {x : VarName} {frame : Frame} {rid' : RegionId}
    {region region' : Region}
    (_hframe : cfg.stack.getLast? = some frame) (_hxref : frame.varMap.lookup x = some (Reference.RId rid'))
    (hregion : cfg.heap.lookup frame.regionId = some region) (_hregion' : cfg.heap.lookup rid' = some region')
    (_hclosed : region'.status = Status.Closed) (hopen : region.status = Status.Open)
    (hcfg' : cfg' = { cfg with
      heap := (cfg.heap.erase rid').insert frame.regionId { region with objMap := region.objMap ∪ region'.objMap },
      stack := cfg.stack.dropLast ++
        [{ frame with varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) }] }) :
    ∀ {rid : RegionId}, rid ≠ rid' → ∀ (b : Reference),
    ReachableStep cfg (Reference.RId rid) b ↔ ReachableStep cfg' (Reference.RId rid) b := by
  intro rid hne b
  by_cases heq : rid = frame.regionId
  · subst heq
    have hlookup' : cfg'.heap.lookup frame.regionId =
        some { region with objMap := region.objMap ∪ region'.objMap } := by
      rw [hcfg']; dsimp only; rw [AList.lookup_insert]
    exact iff_of_false (open_rid_no_step hregion hopen) (open_rid_no_step hlookup' hopen)
  · have hlookup_eq : cfg'.heap.lookup rid = cfg.heap.lookup rid := by
      rw [hcfg']; dsimp only
      rw [AList.lookup_insert_ne heq, AList.lookup_erase_ne hne]
    rw [ReachableStep_rid_iff, ReachableStep_rid_iff, hlookup_eq]

-- Reshapes `Stack.refs`/`Heap.refs` into plain `List.flatMap` form so `Gc.Model.Theorems`'s count lemmas apply directly.
theorem stack_refs_eq_flatMap (stack : Stack) : stack.refs = stack.flatMap Frame.refs := by
  unfold Stack.refs
  rw [List.bind_eq_flatMap, List.flatMap_id, List.flatMap_def]

theorem heap_refs_eq_flatMap (heap : Heap) :
    heap.refs = heap.entries.flatMap (fun e => e.2.refs) := by
  unfold Heap.refs
  rw [List.bind_eq_flatMap, List.flatMap_def, List.map_map, ← List.flatMap_def]
  rfl

-- `RId rid'` is never a `ReachableStep` target: `x`'s varMap entry is H2's one allowed occurrence, so it can only ever be a chain's root, never a later hop.
theorem merge_ridPrime_not_step_target (vcfg : ValidConfig cfg) {frame : Frame} {rid' : RegionId}
    (hframemem : frame ∈ cfg.stack) (hxref : frame.varMap.lookup x = some (Reference.RId rid')) :
    ∀ (a : Reference), ¬ ReachableStep cfg a (Reference.RId rid') := by
  intro a hstep
  have h2 := vcfg.h2 rid'
  cases a with
  | RId ridA =>
    rw [ReachableStep_rid_iff] at hstep
    obtain ⟨regionA, hlookupA, -, hbeq⟩ := hstep
    simp at hbeq
  | OId oidA =>
    rw [ReachableStep_oid_iff] at hstep
    obtain ⟨obj, hobjAt, hcontains⟩ := hstep
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
          have hmemrefs : Reference.RId rid' ∈ regionR.refs :=
            mem_region_refs_of_mem_objMap hobjAt (List.contains_iff_mem.mp hcontains)
          have hcount_heap : 1 ≤ cfg.heap.refs.count (Reference.RId rid') := by
            rw [heap_refs_eq_flatMap]
            apply List.count_pos_iff.mpr
            rw [List.mem_flatMap]
            exact ⟨⟨ridR, regionR⟩, AList.lookup_mem_entries hlookupR, hmemrefs⟩
          have hcount_stack : 1 ≤ cfg.stack.refs.count (Reference.RId rid') := by
            rw [stack_refs_eq_flatMap]
            apply List.count_pos_iff.mpr
            rw [List.mem_flatMap]
            exact ⟨frame, hframemem, mem_frame_refs_of_mem_varMap hxref⟩
          omega
      | Stk fidR =>
        dsimp only at hobjAt
        cases hfind : cfg.stackWithIndex.find? (fun f => f.index == fidR) with
        | none => rw [hfind] at hobjAt; simp at hobjAt
        | some someFrame =>
          rw [hfind] at hobjAt
          have hmemSWI : someFrame ∈ cfg.stackWithIndex := List.mem_of_find?_eq_some hfind
          have hmemstack : someFrame.toFrame ∈ cfg.stack := by
            obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hmemSWI
            rw [← hfeq]; exact List.getElem_mem hn
          have hmemrefs : Reference.RId rid' ∈ someFrame.refs :=
            mem_frame_refs_of_mem_objMap hobjAt (List.contains_iff_mem.mp hcontains)
          by_cases heqframe : someFrame.toFrame = frame
          · have hmemrefs' : Reference.RId rid' ∈ frame.refs := heqframe ▸ hmemrefs
            have hcount_frame : 2 ≤ frame.refs.count (Reference.RId rid') := by
              unfold Frame.refs
              rw [List.count_append]
              have hobjmem : Reference.RId rid' ∈ (frame.objMap.entries.map (·.2) >>= Object.refs) := by
                have : someFrame.objMap.entries.map (·.2) >>= Object.refs =
                    frame.objMap.entries.map (·.2) >>= Object.refs := by rw [heqframe]
                rw [← this, List.bind_eq_flatMap, List.mem_flatMap]
                exact ⟨obj, List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hobjAt),
                  List.contains_iff_mem.mp hcontains⟩
              have hvarmem : Reference.RId rid' ∈ (frame.varMap.entries.map (·.2)) :=
                List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hxref)
              have h1 : 1 ≤ (frame.objMap.entries.map (·.2) >>= Object.refs).count (Reference.RId rid') :=
                List.count_pos_iff.mpr hobjmem
              have h1' : 1 ≤ (frame.varMap.entries.map (·.2)).count (Reference.RId rid') :=
                List.count_pos_iff.mpr hvarmem
              omega
            have hcount_stack : 2 ≤ cfg.stack.refs.count (Reference.RId rid') := by
              rw [stack_refs_eq_flatMap]
              exact le_trans hcount_frame (List.count_le_count_flatMap_of_mem hframemem)
            omega
          · have hcount_stack : 2 ≤ cfg.stack.refs.count (Reference.RId rid') := by
              rw [stack_refs_eq_flatMap]
              exact List.two_le_count_flatMap_of_ne (f := Frame.refs) heqframe hmemstack hframemem
                hmemrefs (mem_frame_refs_of_mem_varMap hxref)
            omega

-- `RId rid'`'s single outgoing `ReachableStep` always lands on its own bridge object.
theorem merge_ridPrime_step_bridge {rid' : RegionId} {region' : Region}
    (hregion' : cfg.heap.lookup rid' = some region') (hclosed : region'.status = Status.Closed) :
    ReachableStep cfg (Reference.RId rid') (Reference.OId region'.bridgeObjectId) := by
  rw [ReachableStep_rid_iff]
  exact ⟨region', hregion', hclosed, rfl⟩

-- Chain-level version: a `RId rid'`-rooted chain to `target` exists iff a (one-hop-shorter) `region'.bridgeObjectId`-rooted one does.
theorem merge_ridPrime_reflTransGen_iff {rid' : RegionId} {region' : Region}
    (hregion' : cfg.heap.lookup rid' = some region') (hclosed : region'.status = Status.Closed)
    {target : Reference} (hne1 : target ≠ Reference.RId rid') :
    Relation.ReflTransGen (ReachableStep cfg) (Reference.RId rid') target ↔
    Relation.ReflTransGen (ReachableStep cfg) (Reference.OId region'.bridgeObjectId) target := by
  constructor
  · intro hrtg
    rcases hrtg.cases_head with heq | ⟨c, hstep, hrest⟩
    · exact absurd heq.symm hne1
    · rw [ReachableStep_rid_iff] at hstep
      obtain ⟨region2, hlookup2, -, hbeq⟩ := hstep
      rw [hregion'] at hlookup2
      injection hlookup2 with hlookup2eq
      rw [hbeq, ← hlookup2eq] at hrest
      exact hrest
  · intro hrtg
    exact Relation.ReflTransGen.head (merge_ridPrime_step_bridge hregion' hclosed) hrtg

-- `x`'s own varMap entry is the only occurrence of `RId rid'` on the stack: no other frame can hold it too, or H2's count bound would be exceeded.
theorem merge_ridPrime_no_other_frame_var (vcfg : ValidConfig cfg) {frame : Frame} {rid' : RegionId}
    (hframemem : frame ∈ cfg.stack) (hxref : frame.varMap.lookup x = some (Reference.RId rid')) :
    ∀ {frame0 : Frame}, frame0 ∈ cfg.stack → frame0.regionId ≠ frame.regionId →
    ∀ {var0 : VarName}, frame0.varMap.lookup var0 ≠ some (Reference.RId rid') := by
  intro frame0 hframe0mem hridne var0 hvar0
  have h2 := vcfg.h2 rid'
  have hne : frame0 ≠ frame := fun hc => hridne (by rw [hc])
  have hmemrefs0 : Reference.RId rid' ∈ frame0.refs := mem_frame_refs_of_mem_varMap hvar0
  have hmemrefsF : Reference.RId rid' ∈ frame.refs := mem_frame_refs_of_mem_varMap hxref
  have hcount2 : 2 ≤ cfg.stack.refs.count (Reference.RId rid') := by
    rw [stack_refs_eq_flatMap]
    exact List.two_le_count_flatMap_of_ne hne hframe0mem hframemem hmemrefs0 hmemrefsF
  omega

-- Same idea, within a single frame: two distinct var slots can't both hold `RId rid'` either.
theorem merge_ridPrime_var_unique (vcfg : ValidConfig cfg) {frame : Frame} {rid' : RegionId}
    (hframemem : frame ∈ cfg.stack) (hxref : frame.varMap.lookup x = some (Reference.RId rid')) :
    ∀ {var0 : VarName}, var0 ≠ x → frame.varMap.lookup var0 ≠ some (Reference.RId rid') := by
  intro var0 hne hvar0
  have h2 := vcfg.h2 rid'
  have hmemX : (⟨x, Reference.RId rid'⟩ : Sigma (fun _ : VarName => Reference)) ∈ frame.varMap.entries :=
    AList.lookup_mem_entries hxref
  have hmemV : (⟨var0, Reference.RId rid'⟩ : Sigma (fun _ : VarName => Reference)) ∈ frame.varMap.entries :=
    AList.lookup_mem_entries hvar0
  have hneSig : (⟨x, Reference.RId rid'⟩ : Sigma (fun _ : VarName => Reference)) ≠ ⟨var0, Reference.RId rid'⟩ :=
    fun hc => hne (congrArg Sigma.fst hc).symm
  have hflatMapEq : frame.varMap.entries.flatMap (fun e => [e.2]) = frame.varMap.entries.map (·.2) := by
    induction frame.varMap.entries with
    | nil => rfl
    | cons a as ih => simp [List.flatMap_cons, ih]
  have hcount2 : 2 ≤ (frame.varMap.entries.map (·.2)).count (Reference.RId rid') := by
    rw [← hflatMapEq]
    exact List.two_le_count_flatMap_of_ne hneSig hmemX hmemV (List.mem_singleton_self _) (List.mem_singleton_self _)
  have hle1 : (frame.varMap.entries.map (·.2)).count (Reference.RId rid') ≤ frame.refs.count (Reference.RId rid') := by
    unfold Frame.refs; rw [List.count_append]; omega
  have hle2 : frame.refs.count (Reference.RId rid') ≤ cfg.stack.refs.count (Reference.RId rid') := by
    rw [stack_refs_eq_flatMap]
    exact List.count_le_count_flatMap_of_mem hframemem
  omega

-- No on-stack frame owns `rid'`: `L2` would force its region simultaneously Open and Closed.
theorem merge_regionId_ne_ridPrime (vcfg : ValidConfig cfg) {rid' : RegionId} {region' : Region}
    (hregion' : cfg.heap.lookup rid' = some region') (hclosed : region'.status = Status.Closed) :
    ∀ G0 : FrameWithIndex, G0 ∈ cfg.stackWithIndex → G0.regionId ≠ rid' := by
  intro G0 hG0mem hc
  obtain ⟨region0, hlk0, hopen0⟩ := l2_of_stackWithIndex vcfg hG0mem
  rw [hc, hregion'] at hlk0
  injection hlk0 with hlk0eq
  rw [← hlk0eq] at hopen0
  exact absurd (hopen0.symm.trans hclosed) (by decide)

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
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] := (List.dropLast_append_getLast? frame hframe).symm
  obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr
  have hidx_n : fr.index = n := by rw [← hfeq]
  have hlt2 : n < cfg.stack.dropLast.length := by rw [← hidx_n]; exact hltfr
  have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
    conv_lhs => rw [stack_eq]
    rw [List.getElem?_append_left hlt2]
  have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
    rw [hcfg']; dsimp only; rw [List.getElem?_append_left hlt2]
  have hfr_get? : cfg'.stack[n]? = some fr.toFrame := by
    rw [show fr.toFrame = cfg'.stack[n] from by rw [← hfeq]]
    exact List.getElem?_eq_getElem hn
  have hcfgn : cfg.stack[n]? = some fr.toFrame := by rw [e1, ← e2, hfr_get?]
  obtain ⟨h1, heq⟩ := List.getElem?_eq_some_iff.mp hcfgn
  unfold RuntimeConfig.stackWithIndex
  exact List.mem_mapIdx.mpr ⟨n, h1, by rw [heq, ← hidx_n]⟩

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
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] := (List.dropLast_append_getLast? frame hframe).symm
  obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr
  have hidx_n : fr.index = n := by rw [← hfeq]
  have hlt2 : n < cfg.stack.dropLast.length := by rw [← hidx_n]; exact hltfr
  have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
    conv_lhs => rw [stack_eq]
    rw [List.getElem?_append_left hlt2]
  have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
    rw [hcfg']; dsimp only; rw [List.getElem?_append_left hlt2]
  have hfr_get? : cfg.stack[n]? = some fr.toFrame := by
    rw [show fr.toFrame = cfg.stack[n] from by rw [← hfeq]]
    exact List.getElem?_eq_getElem hn
  have hcfg'n : cfg'.stack[n]? = some fr.toFrame := by rw [e2, ← e1, hfr_get?]
  obtain ⟨h1, heq⟩ := List.getElem?_eq_some_iff.mp hcfg'n
  unfold RuntimeConfig.stackWithIndex
  exact List.mem_mapIdx.mpr ⟨n, h1, by rw [heq, ← hidx_n]⟩

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
  have hframemem : frame ∈ cfg.stack := by
    rw [(List.dropLast_append_getLast? frame hframe).symm]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hstepIffOfNe : ∀ a : Reference, a ≠ Reference.RId rid' → ∀ b, ReachableStep cfg a b ↔ ReachableStep cfg' a b := by
    intro a hane b
    cases a with
    | OId oid0 => exact merge_oid_step_iff vcfg h oid0 b
    | RId rid0 =>
      have hne0 : rid0 ≠ rid' := fun hc => hane (by rw [hc])
      exact merge_rid_step_iff_of_ne hframe hxref hregion hregion' hclosed hopen hcfg' hne0 b
  have hnotTarget : ∀ a, ¬ ReachableStep cfg a (Reference.RId rid') :=
    merge_ridPrime_not_step_target vcfg hframemem hxref
  have hneRidFrame1 : rid' ≠ frame.regionId := merge_corollary_rid_ne_regionId hregion hregion' hclosed hopen
  have hnotTargetCfg' : ∀ a, ¬ ReachableStep cfg' a (Reference.RId rid') := by
    intro a hstep
    by_cases hane : a = Reference.RId rid'
    · subst hane
      rw [ReachableStep_rid_iff] at hstep
      obtain ⟨region2, hlookup2, -, -⟩ := hstep
      have hnone : cfg'.heap.lookup rid' = none := by
        rw [hcfg']; dsimp only
        rw [AList.lookup_insert_ne hneRidFrame1, AList.lookup_erase]
      rw [hnone] at hlookup2
      exact absurd hlookup2 (by simp)
    · exact hnotTarget a ((hstepIffOfNe a hane (Reference.RId rid')).mpr hstep)
  have hchainAvoidsCfg' : ∀ {start target : Reference}, start ≠ Reference.RId rid' →
      Relation.ReflTransGen (ReachableStep cfg') start target → target ≠ Reference.RId rid' := by
    intro start target hstartne hrtg
    induction hrtg with
    | refl => exact hstartne
    | tail _ hstep _ => intro hc; rw [hc] at hstep; exact hnotTargetCfg' _ hstep
  induction hrtg with
  | refl => exact Relation.ReflTransGen.refl
  | tail hprev hstep ih =>
    rename_i prev cur
    exact Relation.ReflTransGen.tail ih
      ((hstepIffOfNe prev (hchainAvoidsCfg' hstartne hprev) cur).mpr hstep)

-- The `merge` analogue of `makeObjRegion_frame_reachable_iff`/`varAsgn_frame_reachable_iff`.
theorem merge_frame_reachable_iff {cfg cfg' : RuntimeConfig} {x : VarName} (vcfg : ValidConfig cfg)
    (h : merge x cfg = some cfg')
    {X : FrameWithIndex} (_hXmem : X ∈ cfg.stackWithIndex) (hXlt : X.index < cfg.stack.length - 1)
    (ref : Reference) : FrameReachable cfg X.index ref ↔ FrameReachable cfg' X.index ref := by
  obtain ⟨frame, rid', region, region', hframe, hxref, hregion, hregion', hclosed, hopen, hcfg'⟩ :=
    merge_cases h
  have hframemem : frame ∈ cfg.stack := by
    rw [(List.dropLast_append_getLast? frame hframe).symm]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hXlt' : X.index < cfg.stack.dropLast.length := by rw [List.length_dropLast]; exact hXlt
  have hridNe1 := merge_regionId_ne_ridPrime vcfg hregion' hclosed
  have hridNeFrame1 : ∀ G0 : FrameWithIndex, G0 ∈ cfg.stackWithIndex →
      G0.index < cfg.stack.dropLast.length → G0.regionId ≠ frame.regionId := by
    intro G0 hG0mem hG0lt hc
    have hlast1_mem : ({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex) ∈ cfg.stackWithIndex := by
      have hframe1_get : cfg.stack[cfg.stack.dropLast.length]? = some frame := by
        conv_lhs => rw [(List.dropLast_append_getLast? frame hframe).symm]; simp
      obtain ⟨hh1, hheq⟩ := List.getElem?_eq_some_iff.mp hframe1_get
      unfold RuntimeConfig.stackWithIndex
      exact List.mem_mapIdx.mpr ⟨cfg.stack.dropLast.length, hh1, by rw [hheq]⟩
    have hidxeq := merge_corollary_regionId_unique_index vcfg.s1 hG0mem hlast1_mem hc
    exact absurd hidxeq (Nat.ne_of_lt hG0lt)
  have hchainTransportUp : ∀ {start target : Reference}, start ≠ Reference.RId rid' →
      Relation.ReflTransGen (ReachableStep cfg) start target →
      Relation.ReflTransGen (ReachableStep cfg') start target := by
    have hstepIffOfNe : ∀ a : Reference, a ≠ Reference.RId rid' → ∀ b, ReachableStep cfg a b ↔ ReachableStep cfg' a b := by
      intro a hane b
      cases a with
      | OId oid0 => exact merge_oid_step_iff vcfg h oid0 b
      | RId rid0 =>
        have hne0 : rid0 ≠ rid' := fun hc => hane (by rw [hc])
        exact merge_rid_step_iff_of_ne hframe hxref hregion hregion' hclosed hopen hcfg' hne0 b
    have hnotTarget : ∀ a, ¬ ReachableStep cfg a (Reference.RId rid') :=
      merge_ridPrime_not_step_target vcfg hframemem hxref
    have hchainAvoids : ∀ {start target : Reference}, start ≠ Reference.RId rid' →
        Relation.ReflTransGen (ReachableStep cfg) start target → target ≠ Reference.RId rid' := by
      intro start target hstartne hrtg
      induction hrtg with
      | refl => exact hstartne
      | tail _ hstep _ => intro hc; rw [hc] at hstep; exact hnotTarget _ hstep
    intro start target hstartne hrtg
    induction hrtg with
    | refl => exact Relation.ReflTransGen.refl
    | tail hprev hstep ih =>
      rename_i prev cur
      exact Relation.ReflTransGen.tail ih ((hstepIffOfNe prev (hchainAvoids hstartne hprev) cur).mp hstep)
  have hframeRootIffNe : ∀ {fid : Index}, fid < cfg.stack.dropLast.length → ∀ (start : Reference),
      FrameRoot cfg fid start ↔ FrameRoot cfg' fid start := by
    intro fid hfidlt start
    constructor
    · rintro (⟨G0, hG0mem, hG0idx, var, hvar⟩ | ⟨G0, hG0mem, hG0idx, region0, hlk0, hbridge0⟩)
      · have hG0lt : G0.index < cfg.stack.dropLast.length := hG0idx ▸ hfidlt
        exact Or.inl ⟨G0, merge_frame_transport_up hframe hxref hregion hregion' hclosed hopen hcfg' hG0mem hG0lt,
          hG0idx, var, hvar⟩
      · have hG0lt : G0.index < cfg.stack.dropLast.length := hG0idx ▸ hfidlt
        have hlk0' : cfg'.heap.lookup G0.regionId = some region0 := by
          rw [hcfg']; dsimp only
          rw [AList.lookup_insert_ne (hridNeFrame1 G0 hG0mem hG0lt), AList.lookup_erase_ne (hridNe1 G0 hG0mem)]
          exact hlk0
        exact Or.inr ⟨G0, merge_frame_transport_up hframe hxref hregion hregion' hclosed hopen hcfg' hG0mem hG0lt,
          hG0idx, region0, hlk0', hbridge0⟩
    · rintro (⟨G0, hG0mem, hG0idx, var, hvar⟩ | ⟨G0, hG0mem, hG0idx, region0, hlk0, hbridge0⟩)
      · have hG0lt : G0.index < cfg.stack.dropLast.length := hG0idx ▸ hfidlt
        exact Or.inl ⟨G0, merge_frame_transport_down hframe hxref hregion hregion' hclosed hopen hcfg' hG0mem hG0lt,
          hG0idx, var, hvar⟩
      · have hG0lt : G0.index < cfg.stack.dropLast.length := hG0idx ▸ hfidlt
        have hG0memCfg := merge_frame_transport_down hframe hxref hregion hregion' hclosed hopen hcfg' hG0mem hG0lt
        have hlk0' : cfg.heap.lookup G0.regionId = some region0 := by
          rw [hcfg'] at hlk0; dsimp only at hlk0
          rw [AList.lookup_insert_ne (hridNeFrame1 G0 hG0memCfg hG0lt),
            AList.lookup_erase_ne (hridNe1 G0 hG0memCfg)] at hlk0
          exact hlk0
        exact Or.inr ⟨G0, hG0memCfg, hG0idx, region0, hlk0', hbridge0⟩
  rw [FrameReachable_iff_reflTransGen, FrameReachable_iff_reflTransGen]
  constructor
  · rintro ⟨start, hroot, hrtg⟩
    have hstartne : start ≠ Reference.RId rid' := by
      rintro rfl
      rcases hroot with ⟨G0, hG0mem, hG0idx, var, hvar⟩ | ⟨G0, hG0mem, hG0idx, region0, hlk0, hbridge0⟩
      · have hG0lt : G0.index < cfg.stack.dropLast.length := hG0idx ▸ hXlt'
        have hG0memStack : G0.toFrame ∈ cfg.stack := by
          obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hG0mem
          rw [← hfeq]; exact List.getElem_mem hn
        exact merge_ridPrime_no_other_frame_var vcfg hframemem hxref hG0memStack
          (hridNeFrame1 G0 hG0mem hG0lt) hvar
      · exact absurd hbridge0 (by simp)
    exact ⟨start, (hframeRootIffNe hXlt' start).mp hroot, hchainTransportUp hstartne hrtg⟩
  · rintro ⟨start, hroot, hrtg⟩
    have hstartne : start ≠ Reference.RId rid' := by
      rintro rfl
      rcases hroot with ⟨G0, hG0mem, hG0idx, var, hvar⟩ | ⟨G0, hG0mem, hG0idx, region0, hlk0, hbridge0⟩
      · have hG0lt : G0.index < cfg.stack.dropLast.length := hG0idx ▸ hXlt'
        have hG0memCfg := merge_frame_transport_down hframe hxref hregion hregion' hclosed hopen hcfg' hG0mem hG0lt
        have hG0memStack : G0.toFrame ∈ cfg.stack := by
          obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hG0memCfg
          rw [← hfeq]; exact List.getElem_mem hn
        exact merge_ridPrime_no_other_frame_var vcfg hframemem hxref hG0memStack
          (hridNeFrame1 G0 hG0memCfg hG0lt) hvar
      · exact absurd hbridge0 (by simp)
    exact ⟨start, (hframeRootIffNe hXlt' start).mpr hroot,
      merge_chain_transport_down vcfg h hframe hxref hregion hregion' hclosed hopen hcfg' hstartne hrtg⟩
