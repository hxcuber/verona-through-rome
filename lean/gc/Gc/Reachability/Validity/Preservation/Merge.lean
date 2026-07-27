import Gc.Model.Mutation.Merge
import Gc.Model.Preservation.Merge
import Gc.Model.Preservation.Swap
import Gc.Model.Preservation.Exit
import Gc.Reachability.Validity.Reachable
import Gc.Reachability.Corollaries

-- Every on-stack frame's region is Open (L2), but `rid'` (the region being merged away) is
-- Closed -- so no on-stack frame (in particular, no frame reachable via `vcfg.l2`) can ever own
-- `rid'`. General fact, reusable at any position.
private theorem merge_corollary_frame_ne_rid' (vcfg : ValidConfig cfg) {rid' : RegionId} {region' : Region}
    (hregion' : cfg.heap.lookup rid' = some region') (hclosed : region'.status = Status.Closed)
    {frame : Frame} (hframe : frame ∈ cfg.stack) : frame.regionId ≠ rid' := by
  intro hc
  obtain ⟨region2, hlookup2, hopen2⟩ := vcfg.l2 frame hframe
  rw [hc, hregion', Option.some_inj] at hlookup2
  rw [← hlookup2] at hopen2
  exact absurd (hopen2.symm.trans hclosed) (by decide)

-- Every frame's `objMap` is completely unaffected by merge (only the last frame's `varMap`
-- changes, reassigning `x`). So the per-position `objMap` is unconditionally the same in cfg
-- and cfg', at every index.
private theorem merge_corollary_objMap_get_eq {cfg cfg' : RuntimeConfig} {x : VarName}
    (h : merge x cfg = some cfg') (n : ℕ) :
    (cfg.stack[n]?).map Frame.objMap = (cfg'.stack[n]?).map Frame.objMap := by
  obtain ⟨frame, rid', region, region', hframe, hxref, hregion, hregion', hclosed, hopen, hcfg'⟩ :=
    merge_cases h
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] := (List.dropLast_append_getLast? frame hframe).symm
  set newFrame : Frame :=
    { regionId := frame.regionId, bridgeVar := frame.bridgeVar, objMap := frame.objMap,
      varMap := AList.insert x (Reference.OId region'.bridgeObjectId) frame.varMap } with newFrame_def
  by_cases hlp : n = cfg.stack.dropLast.length
  · have e1 : cfg.stack[n]? = some frame := by
      conv_lhs => rw [stack_eq, hlp]
      simp
    have e2 : cfg'.stack[n]? = some newFrame := by
      rw [hcfg', newFrame_def]; dsimp only; rw [hlp]
      simp
    rw [e1, e2]
    rfl
  · by_cases hlt : n < cfg.stack.dropLast.length
    · have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
        conv_lhs => rw [stack_eq]
        rw [List.getElem?_append_left hlt]
      have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
        rw [hcfg']; dsimp only
        rw [List.getElem?_append_left hlt]
      rw [e1, e2]
    · have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq]; simp
      have hlen' : cfg'.stack.length = cfg.stack.dropLast.length + 1 := by rw [hcfg']; simp
      have e1 : cfg.stack[n]? = none := List.getElem?_eq_none (by omega)
      have e2 : cfg'.stack[n]? = none := List.getElem?_eq_none (by omega)
      rw [e1, e2]

-- On disjoint keys, `.lookup` on the union agrees with `.lookup` on whichever side actually
-- contains the key.
private theorem merge_corollary_union_lookup_left {region region' : Region} {oid : ObjectId}
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

private theorem merge_corollary_union_lookup_right {region region' : Region} {oid : ObjectId}
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

-- `cfg'.objectIds` is a permutation of `cfg.objectIds`: merge relocates entries between heap keys
-- but never creates or destroys any (mirrors the argument already inlined in `merge_L1`'s own
-- proof, exposed here as a standalone corollary).
private theorem merge_corollary_objectIds_perm (vcfg : ValidConfig cfg) {x : VarName} {cfg' : RuntimeConfig}
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

-- `objAt?` is fully unconditionally preserved by merge, for every reference: merge only ever
-- relocates existing heap entries between keys (or leaves the stack's objMap content alone), it
-- never creates, destroys, or edits any object's own content.
private theorem merge_corollary_objAt_eq (vcfg : ValidConfig cfg) {x : VarName} {cfg' : RuntimeConfig}
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
      have hmem : oid ∈ cfg.objectIds := (merge_corollary_objectIds_perm vcfg h).mem_iff.mp hmem'
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

-- `RefStep` is fully unconditionally preserved (a direct corollary of `objAt_eq`'s unconditional
-- content preservation).
private theorem merge_corollary_refStep_iff (vcfg : ValidConfig cfg) {x : VarName} {cfg' : RuntimeConfig}
    (h : merge x cfg = some cfg') : ∀ a b, RefStep cfg a b ↔ RefStep cfg' a b := by
  intro a b
  cases a with
  | RId _ =>
    constructor
    · rintro ⟨obj, hobjAt, _⟩; unfold Reference.objAt? at hobjAt; simp at hobjAt
    · rintro ⟨obj, hobjAt, _⟩; unfold Reference.objAt? at hobjAt; simp at hobjAt
  | OId oid =>
    constructor
    · rintro ⟨obj, hobjAt, hcontains⟩
      exact ⟨obj, (merge_corollary_objAt_eq vcfg h oid).symm.trans hobjAt, hcontains⟩
    · rintro ⟨obj, hobjAt, hcontains⟩
      exact ⟨obj, (merge_corollary_objAt_eq vcfg h oid).trans hobjAt, hcontains⟩

-- Given a frame on cfg'.stackWithIndex whose root value is a known OId `start_oid` other than
-- `region'.bridgeObjectId`, transport its `FrameRoot` witness down to cfg: the var-disjunct's
-- witness frame is either an untouched (non-last) position (identical record) or the last
-- position, where the *only* changed slot (`x ↦ OId region'.bridgeObjectId`) is excluded by
-- `hne`; the bridge-disjunct is unconditional -- `region.bridgeObjectId` (the only heap key that
-- genuinely changes content) is itself untouched by the merge, and no on-stack frame can own
-- `rid'` (erased) in cfg' at all (by L2 applied to cfg').
private theorem merge_corollary_frameRoot_down (vcfg' : ValidConfig cfg')
    {x : VarName} {rid' : RegionId} {frame1 : Frame} {region1 region' : Region}
    (hframe1Last : cfg.stack.getLast? = some frame1)
    (hregion1 : cfg.heap.lookup frame1.regionId = some region1)
    (_hregion' : cfg.heap.lookup rid' = some region')
    (hcfg' : cfg' = { cfg with
      heap := (cfg.heap.erase rid').insert frame1.regionId { region1 with
        objMap := region1.objMap.union region'.objMap },
      stack := cfg.stack.dropLast ++
        [ { frame1 with varMap := frame1.varMap.insert x (Reference.OId region'.bridgeObjectId) } ] })
    {fid : Index} {start_oid : ObjectId}
    (hne : start_oid ≠ region'.bridgeObjectId)
    (hroot : FrameRoot cfg' fid (Reference.OId start_oid)) :
    FrameRoot cfg fid (Reference.OId start_oid) := by
  set newFrame1 : Frame :=
    { regionId := frame1.regionId, bridgeVar := frame1.bridgeVar, objMap := frame1.objMap,
      varMap := AList.insert x (Reference.OId region'.bridgeObjectId) frame1.varMap } with newFrame1_def
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame1] :=
    (List.dropLast_append_getLast? frame1 hframe1Last).symm
  unfold FrameRoot
  unfold FrameRoot at hroot
  rcases hroot with ⟨fr, hfr, hidx, var, hlookup⟩ | ⟨fr, hfr, hidx, region0, hlookup, hstart⟩
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
        rw [AList.lookup_insert (a := var) (b := (Reference.OId region'.bridgeObjectId)) frame1.varMap] at hlookup
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
  · right
    by_cases heqr : fr.regionId = frame1.regionId
    · -- `fr` shares `frame1`'s regionId. `{newFrame1 with index := dropLast.length}` is the
      -- *unique* cfg'-side frame owning that regionId (S1-uniqueness on cfg'), so `fr` must
      -- literally *be* it -- letting us transport down to `frame1`'s own (untouched) record.
      have hnewFr1_mem : ({ newFrame1 with index := cfg.stack.dropLast.length } : FrameWithIndex) ∈
          cfg'.stackWithIndex := by
        rw [hcfg']
        unfold RuntimeConfig.stackWithIndex
        rw [List.mapIdx_concat]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      have hridF : fr.regionId = ({ newFrame1 with index := cfg.stack.dropLast.length } :
          FrameWithIndex).regionId := by
        show fr.regionId = newFrame1.regionId
        rw [heqr, newFrame1_def]
      have hidxeq := merge_corollary_regionId_unique_index vcfg'.s1 hfr hnewFr1_mem hridF
      have hfr_eq : fr = { newFrame1 with index := cfg.stack.dropLast.length } :=
        swap_corollary_stackWithIndex_index_inj hfr hnewFr1_mem hidxeq
      have hframe1_get : cfg.stack[cfg.stack.dropLast.length]? = some frame1 := by
        conv_lhs => rw [stack_eq]
        simp
      have hlast1_mem : ({ frame1 with index := cfg.stack.dropLast.length } : FrameWithIndex) ∈
          cfg.stackWithIndex := by
        obtain ⟨hh1, hheq⟩ := List.getElem?_eq_some_iff.mp hframe1_get
        unfold RuntimeConfig.stackWithIndex
        exact List.mem_mapIdx.mpr ⟨cfg.stack.dropLast.length, hh1, by rw [hheq]⟩
      have hregion0_eq : region0 = { region1 with objMap := region1.objMap ∪ region'.objMap } := by
        rw [heqr, hcfg'] at hlookup
        dsimp only at hlookup
        rw [AList.lookup_insert] at hlookup
        injection hlookup with hlookup_eq
        exact hlookup_eq.symm
      have hstart' : Reference.OId start_oid = Reference.OId region1.bridgeObjectId := by
        rw [hstart, hregion0_eq]
      refine ⟨{ frame1 with index := cfg.stack.dropLast.length }, hlast1_mem, ?_, region1, hregion1, hstart'⟩
      rw [← hidx, hfr_eq]
    · have hridne_rid' : fr.regionId ≠ rid' := by
        intro hc
        obtain ⟨region2, hlookup2, _⟩ := vcfg'.l2 fr.toFrame (by
          obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr
          rw [← hfeq]
          exact List.getElem_mem hn)
        rw [hc, hcfg'] at hlookup2
        dsimp only at hlookup2
        rw [AList.lookup_insert_ne (by rw [← hc]; exact heqr), AList.lookup_erase] at hlookup2
        contradiction
      have hlookup'' : cfg.heap.lookup fr.regionId = cfg'.heap.lookup fr.regionId := by
        rw [hcfg']
        dsimp only
        rw [AList.lookup_insert_ne heqr, AList.lookup_erase_ne hridne_rid']
      obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr
      have hidx_n : fr.index = n := by rw [← hfeq]
      have hlt : n < cfg.stack.dropLast.length := by
        have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq]; simp
        have hlen' : cfg'.stack.length = cfg.stack.dropLast.length + 1 := by rw [hcfg']; simp
        have hn' : n < cfg'.stack.length := hn
        rw [hlen'] at hn'
        apply Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hn')
        intro hc
        apply heqr
        have hnewFr1_mem : ({ newFrame1 with index := n } : FrameWithIndex) ∈ cfg'.stackWithIndex := by
          rw [hcfg']
          unfold RuntimeConfig.stackWithIndex
          rw [List.mapIdx_concat, ← hc]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        have hfr_eq : fr = { newFrame1 with index := n } :=
          swap_corollary_stackWithIndex_index_inj hfr hnewFr1_mem hidx_n
        rw [hfr_eq]
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
      have hfr_untouched : fr ∈ cfg.stackWithIndex := by
        unfold RuntimeConfig.stackWithIndex
        obtain ⟨h1, heq⟩ := List.getElem?_eq_some_iff.mp hcfgn
        exact List.mem_mapIdx.mpr ⟨n, h1, by rw [heq, ← hidx_n]⟩
      exact ⟨fr, hfr_untouched, hidx, region0, by rw [hlookup'']; exact hlookup, hstart⟩

theorem merge_cr3 : ValidReachableConfig cfg →
  merge x cfg = some cfg' →
  CR3 cfg' := by
  intro vrcfg h
  have vcfg := vrcfg.toValidConfig
  have vcfg' := merge_valid vcfg h
  obtain ⟨frame1, rid', region1, region', hframe1Last, hxref1, hregion1, hregion', hclosed1, hopen1, hcfg'⟩ :=
    merge_cases h
  have hne_rid'_frame1 := merge_corollary_rid_ne_regionId hregion1 hregion' hclosed1 hopen1
  set newFrame1 : Frame :=
    { regionId := frame1.regionId, bridgeVar := frame1.bridgeVar, objMap := frame1.objMap,
      varMap := AList.insert x (Reference.OId region'.bridgeObjectId) frame1.varMap } with newFrame1_def
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame1] :=
    (List.dropLast_append_getLast? frame1 hframe1Last).symm
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
  have hframe1_get : cfg.stack[cfg.stack.dropLast.length]? = some frame1 := by
    conv_lhs => rw [stack_eq]
    simp
  have hlast1_mem : ({ frame1 with index := cfg.stack.dropLast.length } : FrameWithIndex) ∈ cfg.stackWithIndex := by
    obtain ⟨hh1, hheq⟩ := List.getElem?_eq_some_iff.mp hframe1_get
    unfold RuntimeConfig.stackWithIndex
    exact List.mem_mapIdx.mpr ⟨cfg.stack.dropLast.length, hh1, by rw [hheq]⟩
  unfold CR3
  intro frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  -- `frame` can never be the mutated (last, highest-index) position (index-ordering argument).
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
  -- `frame.regionId` is never `frame1.regionId` (S1-uniqueness: frame ≠ frame1, different index)
  -- nor `rid'` (L2: `frame` is on-stack, so its region is Open, but `rid'`'s region is Closed).
  have hframe_ridne_frame1 : frame.regionId ≠ frame1.regionId := by
    intro hc
    have hidxeq := merge_corollary_regionId_unique_index vcfg.s1 hframeMemCfg hlast1_mem hc
    dsimp only at hidxeq
    exact Nat.lt_irrefl _ (hidxeq ▸ hframe_lt_dropLast)
  have hframe_ridne_rid' : frame.regionId ≠ rid' := by
    apply merge_corollary_frame_ne_rid' vcfg hregion' hclosed1 (frame := frame.toFrame)
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hframeMemCfg
    have hget : cfg.stack[n]? = some frame.toFrame := by rw [← hfeq]; exact List.getElem?_eq_getElem hn
    exact List.mem_of_getElem? hget
  have hheap_eq_frame : cfg'.heap.lookup frame.regionId = cfg.heap.lookup frame.regionId := by
    rw [hcfg']; dsimp only
    rw [AList.lookup_insert_ne hframe_ridne_frame1, AList.lookup_erase_ne hframe_ridne_rid']
  have hlocDown : (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) := by
    obtain ⟨region0, hlookup0, hmem0⟩ := (oid_loc_rgn_iff_in_heap vcfg').mp hloc
    exact (oid_loc_rgn_iff_in_heap vcfg).mpr ⟨region0, by rw [← hheap_eq_frame]; exact hlookup0, hmem0⟩
  -- Vacuousness: no chain from `region'`'s bridge object can ever reach `oid` -- if it did, since
  -- `RefStep` transports unconditionally, the same chain exists in `cfg`, giving
  -- `RegionReachable cfg rid' oid`, hence `oid.loc? cfg = Rgn rid'` -- contradicting `hlocDown`
  -- (which pins it at `frame.regionId ≠ rid'`).
  have hno_chain_from_region' :
      ¬ Relation.ReflTransGen (RefStep cfg') (Reference.OId region'.bridgeObjectId) (Reference.OId oid) := by
    intro hchain
    have hchain_cfg : Relation.ReflTransGen (RefStep cfg) (Reference.OId region'.bridgeObjectId) (Reference.OId oid) :=
      hchain.mono (fun a b hab => (merge_corollary_refStep_iff vcfg h a b).mpr hab)
    have hregReach : RegionReachable cfg rid' (Reference.OId oid) :=
      (RegionReachable_iff_reflTransGen cfg rid' (Reference.OId oid)).mpr ⟨region', hregion', hchain_cfg⟩
    have hloc_rid' := RegionReachable_stays_in_region vcfg hregReach
    rw [hlocDown, Option.some_inj, Location.Rgn.injEq] at hloc_rid'
    exact hframe_ridne_rid' hloc_rid'
  -- `frame`'s own (untouched) position transports `FrameRoot` upward unconditionally: its record
  -- and its own region's heap entry are both completely unaffected by the merge.
  have frameRoot_up_frame : ∀ start, FrameRoot cfg frame.index start → FrameRoot cfg' frame.index start := by
    intro start hroot
    unfold FrameRoot at hroot ⊢
    rcases hroot with ⟨fr0, hfr0, hidx0, var, hlookup0⟩ | ⟨fr0, hfr0, hidx0, region0, hlookup0, hstart0⟩
    · have hfr0_eq : fr0 = frame := swap_corollary_stackWithIndex_index_inj hfr0 hframeMemCfg hidx0
      exact Or.inl ⟨fr0, frame_transport_up fr0 hfr0 (hidx0 ▸ hframe_lt_dropLast), hidx0, var, hlookup0⟩
    · have hfr0_eq : fr0 = frame := swap_corollary_stackWithIndex_index_inj hfr0 hframeMemCfg hidx0
      right
      refine ⟨fr0, frame_transport_up fr0 hfr0 (hidx0 ▸ hframe_lt_dropLast), hidx0, region0, ?_, hstart0⟩
      rw [hcfg']
      dsimp only
      rw [AList.lookup_insert_ne (by rw [hfr0_eq]; exact hframe_ridne_frame1),
        AList.lookup_erase_ne (by rw [hfr0_eq]; exact hframe_ridne_rid')]
      exact hlookup0
  -- Trace `hreach`'s chain root: it's always `OId`-shaped, and (by the vacuousness fact above)
  -- never `region'.bridgeObjectId`, so it transports down via `frameRoot_down` regardless of
  -- whether `frame'` itself is the mutated (last) position.
  rw [FrameReachable_iff_reflTransGen] at hreach
  obtain ⟨start, hroot, hrtg⟩ := hreach
  have hstart_oid : ∃ start_oid, start = Reference.OId start_oid := by
    rcases hrtg.cases_head with heq0 | ⟨c, hstep0, _⟩
    · exact ⟨oid, heq0⟩
    · exact hstep0.exists_oid_left
  obtain ⟨start_oid, hstart_eq⟩ := hstart_oid
  rw [hstart_eq] at hroot hrtg
  have hne_start : start_oid ≠ region'.bridgeObjectId := by
    intro hc
    subst hc
    exact hno_chain_from_region' hrtg
  have hroot_down : FrameRoot cfg frame'.index (Reference.OId start_oid) :=
    merge_corollary_frameRoot_down vcfg' hframe1Last hregion1 hregion' hcfg' hne_start hroot
  have hrtg_down : Relation.ReflTransGen (RefStep cfg) (Reference.OId start_oid) (Reference.OId oid) :=
    hrtg.mono (fun a b hab => (merge_corollary_refStep_iff vcfg h a b).mpr hab)
  have hreachDown : FrameReachable cfg frame'.index (Reference.OId oid) :=
    (FrameReachable_iff_reflTransGen cfg frame'.index (Reference.OId oid)).mpr
      ⟨Reference.OId start_oid, hroot_down, hrtg_down⟩
  -- Construct the cfg-side witness for `frame'` (last vs non-last), apply `vrcfg.cr3`, transport
  -- the conclusion back up through `frame`'s own untouched position.
  by_cases hframe'Last : frame'.index = cfg.stack.dropLast.length
  · have hlt' : frame.index < ({ frame1 with index := cfg.stack.dropLast.length } : FrameWithIndex).index := by
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
    exact ⟨start2, frameRoot_up_frame start2 hroot2,
      hrtg2.mono (fun a b hab => (merge_corollary_refStep_iff vcfg h a b).mp hab)⟩
  · have hframe'_lt_dropLast : frame'.index < cfg.stack.dropLast.length := by
      have hframe'_lt2 : frame'.index < cfg.stack.dropLast.length + 1 := by
        rw [← hlen']; exact hframe'_lt
      exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hframe'_lt2) hframe'Last
    have hframe'MemCfg : frame' ∈ cfg.stackWithIndex :=
      frame_transport_down frame' hframe'Mem hframe'_lt_dropLast
    have hconcDown : FrameReachable cfg frame.index (Reference.OId oid) :=
      vrcfg.cr3 frame hframeMemCfg frame' hframe'MemCfg hlt oid hlocDown hreachDown
    rw [FrameReachable_iff_reflTransGen] at hconcDown ⊢
    obtain ⟨start2, hroot2, hrtg2⟩ := hconcDown
    exact ⟨start2, frameRoot_up_frame start2 hroot2,
      hrtg2.mono (fun a b hab => (merge_corollary_refStep_iff vcfg h a b).mp hab)⟩

theorem merge_reachable_valid : ValidReachableConfig cfg →
  merge x cfg = some cfg' →
  ValidReachableConfig cfg' := by
  intro vrcfg h
  exact { merge_valid vrcfg.toValidConfig h with cr3 := merge_cr3 vrcfg h }
