import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Theorems
import Gc.Model.Mutation.VarAsgn

import Mathlib.Data.List.Infix

-- The bridge-var branch's `heap.insert` at an already-present key never changes the key *set*
-- (only reorders `entries`, moving the mutated region to the front).
theorem varAsgn_corollary_bridge_heap_keys_mem {cfg : RuntimeConfig} {rid oid : ObjectId} {region : Region}
    (hregion : cfg.heap.lookup rid = some region) (rid' : RegionId) :
    rid' ∈ (cfg.heap.insert rid { region with bridgeObjectId := oid }).keys ↔ rid' ∈ cfg.heap.keys := by
  have hridmem : rid ∈ cfg.heap.keys := List.mem_keys_of_mem (AList.lookup_mem_entries hregion)
  rw [← AList.mem_keys, AList.mem_insert, AList.mem_keys]
  exact or_iff_right_of_imp (fun h => h ▸ hridmem)

-- The bridge-var branch never touches any region's `objMap`, so `heap.objectIds` is a permutation
-- (not a literal equality: `AList.insert` at an existing key reorders `entries`) of the original.
theorem varAsgn_corollary_bridge_heap_objectIds_perm {cfg : RuntimeConfig} {rid oid : ObjectId} {region : Region}
    (hregion : cfg.heap.lookup rid = some region) :
    (Heap.objectIds (cfg.heap.insert rid { region with bridgeObjectId := oid })).Perm cfg.heap.objectIds := by
  obtain ⟨region2, l1e, l2e, hnotmem, heq, hkerase⟩ :=
    List.exists_of_kerase (List.mem_keys_of_mem (AList.lookup_mem_entries hregion))
  have region2_eq : region2 = region :=
    List.NodupKeys.eq_of_mk_mem cfg.heap.nodupKeys
      (heq ▸ List.mem_append_right _ List.mem_cons_self) (AList.lookup_mem_entries hregion)
  rw [← region2_eq]
  have cfg_eq : Heap.objectIds cfg.heap =
      List.flatten (l1e.map (fun e => e.2.objectIds)) ++
        (region2.objectIds ++ List.flatten (l2e.map (fun e => e.2.objectIds))) := by
    unfold Heap.objectIds
    rw [heq, List.map_append, List.map_cons, List.flatten_append, List.flatten_cons]
  have cfg'_eq : Heap.objectIds (cfg.heap.insert rid { region2 with bridgeObjectId := oid }) =
      region2.objectIds ++
        (List.flatten (l1e.map (fun e => e.2.objectIds)) ++ List.flatten (l2e.map (fun e => e.2.objectIds))) := by
    unfold Heap.objectIds
    rw [AList.entries_insert, hkerase, List.map_cons, List.flatten_cons, List.map_append, List.flatten_append]
    rfl
  rw [cfg_eq, cfg'_eq]
  set LA := List.flatten (l1e.map (fun e => e.2.objectIds))
  set LB := List.flatten (l2e.map (fun e => e.2.objectIds))
  have swap_perm : (region2.objectIds ++ (LA ++ LB)).Perm (LA ++ (region2.objectIds ++ LB)) := by
    rw [← List.append_assoc, ← List.append_assoc]
    exact (List.perm_append_comm).append_right LB
  exact swap_perm

-- The fresh-var branch's precondition `resolveV xf cfg = none` in particular means the *last* frame's
-- varMap doesn't already contain xf (findRev? would immediately hit it otherwise, since it's the last
-- element and findRev? checks it first). Used to justify treating the varMap insert as a fresh cons.
theorem varAsgn_corollary_fresh_not_in_frame {cfg : RuntimeConfig} {frame : Frame} {xf : VarName}
    (hframe : cfg.stack.getLast? = some frame) (hresolve : resolveV xf cfg = none) :
    xf ∉ frame.varMap.keys := by
  intro hmem
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
    (List.dropLast_append_getLast? frame hframe).symm
  have hcontains : frame.varMap.keys.contains xf = true := List.contains_iff_mem.mpr hmem
  have h1 : cfg.stackWithIndex.findRev?
      (fun f => f.varMap.keys.contains xf ∨ f.bridgeVar == xf) =
      some ({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex) := by
    unfold RuntimeConfig.stackWithIndex
    conv_lhs => rw [stack_eq]
    rw [List.mapIdx_concat, List.findRev?_eq_find?_reverse, List.reverse_append, List.reverse_singleton,
      List.singleton_append]
    exact List.find?_cons_of_pos (decide_eq_true_iff.mpr (Or.inl hcontains))
  have hisSome : (frame.varMap.lookup xf).isSome := AList.lookup_isSome.mpr (AList.mem_keys.mpr hmem)
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hisSome
  unfold resolveV at hresolve
  dsimp at hresolve
  rw [h1] at hresolve
  dsimp at hresolve
  rw [hv] at hresolve
  dsimp at hresolve
  contradiction

-- Mirrors varAsgn_corollary_bridge_heap_objectIds_perm but for `.refs`: bridgeObjectId isn't read
-- by Region.refs (only objMap is), so the mutated region's own `.refs` value is literally unchanged.
theorem varAsgn_corollary_bridge_heap_refs_perm {cfg : RuntimeConfig} {rid oid : ObjectId} {region : Region}
    (hregion : cfg.heap.lookup rid = some region) :
    (Heap.refs (cfg.heap.insert rid { region with bridgeObjectId := oid })).Perm cfg.heap.refs := by
  obtain ⟨region2, l1e, l2e, hnotmem, heq, hkerase⟩ :=
    List.exists_of_kerase (List.mem_keys_of_mem (AList.lookup_mem_entries hregion))
  have region2_eq : region2 = region :=
    List.NodupKeys.eq_of_mk_mem cfg.heap.nodupKeys
      (heq ▸ List.mem_append_right _ List.mem_cons_self) (AList.lookup_mem_entries hregion)
  rw [← region2_eq]
  have cfg_eq : Heap.refs cfg.heap =
      (l1e.map (·.2) >>= Region.refs) ++ (region2.refs ++ (l2e.map (·.2) >>= Region.refs)) := by
    unfold Heap.refs
    rw [heq, List.map_append, List.map_cons]
    simp [List.bind_eq_flatMap]
  have cfg'_eq : Heap.refs (cfg.heap.insert rid { region2 with bridgeObjectId := oid }) =
      region2.refs ++ ((l1e.map (·.2) >>= Region.refs) ++ (l2e.map (·.2) >>= Region.refs)) := by
    unfold Heap.refs
    rw [AList.entries_insert, hkerase, List.map_cons, List.map_append]
    simp only [List.bind_eq_flatMap, List.flatMap_cons, List.flatMap_append]
    rfl
  rw [cfg_eq, cfg'_eq]
  set LA := l1e.map (·.2) >>= Region.refs
  set LB := l2e.map (·.2) >>= Region.refs
  have swap_perm : (region2.refs ++ (LA ++ LB)).Perm (LA ++ (region2.refs ++ LB)) := by
    rw [← List.append_assoc, ← List.append_assoc]
    exact (List.perm_append_comm).append_right LB
  exact swap_perm

-- A successful `resolveFA` retrieves a field value from some already-live object (in the stack or
-- the heap), so the resolved reference is genuinely a member of `cfg.refs` -- not a freshly
-- allocated value. Used by HS1's fresh-var branch, where the newly-inserted varMap value is exactly
-- this resolved reference.
theorem varAsgn_corollary_yfRef_mem_refs {cfg : RuntimeConfig} {y : FieldAccess} {oid : ObjectId}
    (hyf : resolveFA y cfg = some (Reference.OId oid)) :
    Reference.OId oid ∈ cfg.refs := by
  unfold resolveFA at hyf
  cases hrv : resolveV y.root cfg with
  | none => rw [hrv] at hyf; contradiction
  | some ref0 =>
    rw [hrv] at hyf
    dsimp at hyf
    cases ref0 with
    | RId rid0 => dsimp at hyf; contradiction
    | OId oid0 =>
      dsimp at hyf
      cases hloc0 : (Reference.OId oid0).loc? cfg with
      | none => rw [hloc0] at hyf; dsimp at hyf; contradiction
      | some loc0 =>
        rw [hloc0] at hyf
        dsimp at hyf
        cases loc0 with
        | Stk fid0 =>
          dsimp at hyf
          cases hframe0 : cfg.stackWithIndex.find? (fun frame => frame.index == fid0) with
          | none => rw [hframe0] at hyf; dsimp at hyf; contradiction
          | some frame0 =>
            rw [hframe0] at hyf
            dsimp at hyf
            cases hobj0 : frame0.objMap.lookup oid0 with
            | none => rw [hobj0] at hyf; dsimp at hyf; contradiction
            | some obj0 =>
              rw [hobj0] at hyf
              dsimp at hyf
              have hmem_obj : Reference.OId oid ∈ Object.refs obj0 := by
                unfold Object.refs
                exact List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hyf)
              have hmem_frame0 : Reference.OId oid ∈ frame0.refs := by
                unfold Frame.refs
                apply List.mem_append_left
                rw [List.bind_eq_flatMap, List.mem_flatMap]
                exact ⟨obj0, List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hobj0), hmem_obj⟩
              have hmem_stack0 : frame0 ∈ cfg.stackWithIndex := List.mem_of_find?_eq_some hframe0
              obtain ⟨n0, n0_lt_len, f0_eq⟩ := List.mem_mapIdx.mp hmem_stack0
              apply List.mem_append_left
              unfold Stack.refs
              rw [List.bind_eq_flatMap, List.flatMap_id, List.mem_flatten]
              refine ⟨frame0.refs, ?_, hmem_frame0⟩
              rw [List.mem_map]
              refine ⟨cfg.stack[n0], List.mem_iff_getElem.mpr ⟨n0, n0_lt_len, rfl⟩, ?_⟩
              rw [← f0_eq]
        | Rgn rid0 =>
          dsimp at hyf
          cases hregion0 : cfg.heap.lookup rid0 with
          | none => rw [hregion0] at hyf; dsimp at hyf; contradiction
          | some region0 =>
            rw [hregion0] at hyf
            dsimp at hyf
            cases hobj0 : region0.objMap.lookup oid0 with
            | none => rw [hobj0] at hyf; dsimp at hyf; contradiction
            | some obj0 =>
              rw [hobj0] at hyf
              dsimp at hyf
              have hmem_obj : Reference.OId oid ∈ Object.refs obj0 := by
                unfold Object.refs
                exact List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hyf)
              have hmem_region0 : Reference.OId oid ∈ Region.refs region0 := by
                unfold Region.refs
                rw [List.bind_eq_flatMap, List.mem_flatMap]
                exact ⟨obj0, List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hobj0), hmem_obj⟩
              apply List.mem_append_right
              unfold Heap.refs
              rw [List.bind_eq_flatMap, List.mem_flatMap]
              exact ⟨region0, List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hregion0), hmem_region0⟩

-- The fresh-var branch never touches any objMap (stack or heap), so `Reference.loc?` is
-- *unconditionally* unchanged for every oid' -- unlike makeObjStack/makeObjRegion, which had to
-- exclude the freshly-allocated id, varAsgn never allocates a new id at all.
theorem varAsgn_corollary_fresh_loc_eq {cfg : RuntimeConfig} {frame : Frame} {xf : VarName} {oid : ObjectId}
    (hframe : cfg.stack.getLast? = some frame) (oid' : ObjectId) :
    (Reference.OId oid').loc? cfg =
      (Reference.OId oid').loc? { cfg with
        stack := cfg.stack.dropLast ++ [{ frame with varMap := frame.varMap.insert xf (Reference.OId oid) }] } := by
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
    (List.dropLast_append_getLast? frame hframe).symm
  set newFrame : Frame := { frame with varMap := frame.varMap.insert xf (Reference.OId oid) } with newFrame_def
  unfold Reference.loc?
  dsimp
  by_cases hb : (AList.keys frame.objMap).contains oid'
  · have h1_cfg : cfg.stackWithIndex.findRev? (fun f => (AList.keys f.objMap).contains oid') =
        some ({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex) := by
      unfold RuntimeConfig.stackWithIndex
      conv_lhs => rw [stack_eq]
      rw [List.mapIdx_concat, List.findRev?_eq_find?_reverse, List.reverse_append, List.reverse_singleton,
        List.singleton_append]
      exact List.find?_cons_of_pos hb
    have h1_cfg' :
        (RuntimeConfig.stackWithIndex { stack := cfg.stack.dropLast ++ [newFrame], heap := cfg.heap }).findRev?
          (fun f => (AList.keys f.objMap).contains oid') =
        some ({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex) := by
      unfold RuntimeConfig.stackWithIndex
      dsimp
      rw [List.mapIdx_concat, List.findRev?_eq_find?_reverse, List.reverse_append, List.reverse_singleton,
        List.singleton_append]
      exact List.find?_cons_of_pos hb
    rw [h1_cfg, h1_cfg']
    cases List.find? (fun x => (AList.keys x.snd.objMap).contains oid') cfg.heap.entries with
    | none => rfl
    | some _ => rfl
  · have h1_eq : cfg.stackWithIndex.findRev? (fun f => (AList.keys f.objMap).contains oid') =
        (RuntimeConfig.stackWithIndex { stack := cfg.stack.dropLast ++ [newFrame], heap := cfg.heap }).findRev?
          (fun f => (AList.keys f.objMap).contains oid') := by
      unfold RuntimeConfig.stackWithIndex
      dsimp
      conv_lhs => rw [stack_eq]
      rw [List.mapIdx_concat, List.mapIdx_concat, List.findRev?_eq_find?_reverse, List.findRev?_eq_find?_reverse,
        List.reverse_append, List.reverse_append, List.reverse_singleton, List.reverse_singleton,
        List.singleton_append, List.singleton_append]
      have hbL : ¬ (AList.keys ({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex).objMap).contains
          oid' = true := hb
      have hbR : ¬ (AList.keys ({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex).objMap).contains
          oid' = true := hb
      have find_eqL :
          List.find? (fun f => (AList.keys f.objMap).contains oid')
            (({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex) ::
              (List.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) cfg.stack.dropLast).reverse) =
          List.find? (fun f => (AList.keys f.objMap).contains oid')
            (List.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) cfg.stack.dropLast).reverse :=
        List.find?_cons_of_neg hbL
      have find_eqR :
          List.find? (fun f => (AList.keys f.objMap).contains oid')
            (({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex) ::
              (List.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) cfg.stack.dropLast).reverse) =
          List.find? (fun f => (AList.keys f.objMap).contains oid')
            (List.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) cfg.stack.dropLast).reverse :=
        List.find?_cons_of_neg hbR
      rw [find_eqL, find_eqR]
    rw [h1_eq]

-- An oid can be found in at most one region's objMap (stated over bare L1, so it's usable on cfg
-- before cfg''s own validity is established). Mirrors enter_corollary_1/makeObjRegion_corollary_region_unique.
theorem varAsgn_corollary_region_unique
    {cfg : RuntimeConfig} {rid1 rid2 : RegionId} {region1 region2 : Region} {oid : ObjectId} :
  L1 cfg →
  (⟨rid1, region1⟩ : Sigma (fun _ : RegionId => Region)) ∈ cfg.heap.entries → oid ∈ region1.objMap.keys →
  (⟨rid2, region2⟩ : Sigma (fun _ : RegionId => Region)) ∈ cfg.heap.entries → oid ∈ region2.objMap.keys →
  rid1 = rid2 := by
  intro l1 mem1 in1 mem2 in2
  by_contra hne
  unfold L1 RuntimeConfig.objectIds at l1
  obtain ⟨_, heap_nodup, _⟩ := List.nodup_append.mp l1
  unfold Heap.objectIds at heap_nodup
  rw [List.nodup_flatten, List.pairwise_map] at heap_nodup
  obtain ⟨_, pairwise_disjoint⟩ := heap_nodup
  have hneq : (⟨rid1, region1⟩ : Sigma (fun _ : RegionId => Region)) ≠ ⟨rid2, region2⟩ := by
    intro heq
    exact hne (congrArg Sigma.fst heq)
  have disj := List.Pairwise.forall
    (R := fun (e1 e2 : Sigma (fun _ : RegionId => Region)) => List.Disjoint e1.2.objectIds e2.2.objectIds)
    (fun _ _ hd => List.disjoint_symm hd)
    pairwise_disjoint mem1 mem2 hneq
  unfold Region.objectIds at disj
  exact disj in1 in2

-- Reference.loc?'s (h1, h2)-match for OId factors through Option.map, so equal cfg's need only
-- agree on the *projected* index/rid, not the full FrameWithIndex/heap-entry value. Mirrors
-- makeObjRegion_corollary_loc_match_eq.
theorem varAsgn_corollary_loc_match_eq (o1 : Option FrameWithIndex)
    (o2 : Option (Sigma (fun _ : RegionId => Region))) :
    (match o1, o2 with
      | some f, none => some (Location.Stk f.index)
      | none, some ⟨rid, _⟩ => some (Location.Rgn rid)
      | _, _ => none) =
    (match o1.map FrameWithIndex.index, o2.map Sigma.fst with
      | some n, none => some (Location.Stk n)
      | none, some r => some (Location.Rgn r)
      | _, _ => none) := by
  cases o1 <;> cases o2 <;> rfl

-- The bridge-var branch never touches the stack, so `Reference.loc?`'s stack side is literally
-- unchanged; the heap side genuinely reorders (the mutated region's entry moves to the front via
-- the AList.insert kerase), so it needs region-uniqueness to show find? still lands on the same
-- region. Unconditional in oid' -- unlike makeObjStack/makeObjRegion, no id is freshly allocated here.
theorem varAsgn_corollary_bridge_loc_eq {cfg : RuntimeConfig} {rid oid : ObjectId} {region : Region}
    (vcfg : ValidConfig cfg) (hregion : cfg.heap.lookup rid = some region) (oid' : ObjectId) :
    (Reference.OId oid').loc? cfg =
      (Reference.OId oid').loc? { cfg with heap := cfg.heap.insert rid { region with bridgeObjectId := oid } } := by
  have l1 := vcfg.l1
  unfold Reference.loc?
  dsimp
  have heap_h2_map_eq :
      (cfg.heap.entries.find? (fun p => (AList.keys p.snd.objMap).contains oid')).map Sigma.fst =
      ((AList.insert rid { region with bridgeObjectId := oid } cfg.heap).entries.find?
        (fun p => (AList.keys p.snd.objMap).contains oid')).map Sigma.fst := by
    obtain ⟨region2, l1e, l2e, hnotmem, heq, hkerase⟩ :=
      List.exists_of_kerase (List.mem_keys_of_mem (AList.lookup_mem_entries hregion))
    have region2_eq : region2 = region :=
      List.NodupKeys.eq_of_mk_mem cfg.heap.nodupKeys
        (heq ▸ List.mem_append_right _ List.mem_cons_self) (AList.lookup_mem_entries hregion)
    rw [region2_eq] at heq
    rw [AList.entries_insert, hkerase]
    have region_mem_cfg : (⟨rid, region⟩ : Sigma (fun _ : RegionId => Region)) ∈ cfg.heap.entries :=
      heq ▸ List.mem_append_right _ List.mem_cons_self
    by_cases hb2 : (AList.keys region.objMap).contains oid'
    · have find_eqR2 :
          List.find? (fun p => (AList.keys p.snd.objMap).contains oid')
            ((⟨rid, { region with bridgeObjectId := oid }⟩ : Sigma (fun _ : RegionId => Region)) :: (l1e ++ l2e)) =
          some (⟨rid, { region with bridgeObjectId := oid }⟩ : Sigma (fun _ : RegionId => Region)) :=
        List.find?_cons_of_pos hb2
      rw [find_eqR2]
      have find_eqL :
          cfg.heap.entries.find? (fun p => (AList.keys p.snd.objMap).contains oid') =
          some (⟨rid, region⟩ : Sigma (fun _ : RegionId => Region)) := by
        apply List.find?_eq_some_of_unique region_mem_cfg hb2
        intro y hy hpy
        obtain ⟨rid_y, region_y⟩ := y
        have rid_y_eq : rid_y = rid :=
          varAsgn_corollary_region_unique l1 hy (List.contains_iff_mem.mp hpy)
            region_mem_cfg (List.contains_iff_mem.mp hb2)
        subst rid_y_eq
        have region_y_eq : region_y = region :=
          List.NodupKeys.eq_of_mk_mem cfg.heap.nodupKeys hy region_mem_cfg
        rw [region_y_eq]
      rw [find_eqL]
      rfl
    · have find_eqR2 :
          List.find? (fun p => (AList.keys p.snd.objMap).contains oid')
            ((⟨rid, { region with bridgeObjectId := oid }⟩ : Sigma (fun _ : RegionId => Region)) :: (l1e ++ l2e)) =
          List.find? (fun p => (AList.keys p.snd.objMap).contains oid') (l1e ++ l2e) :=
        List.find?_cons_of_neg hb2
      rw [find_eqR2]
      have find_eqL :
          cfg.heap.entries.find? (fun p => (AList.keys p.snd.objMap).contains oid') =
          List.find? (fun p => (AList.keys p.snd.objMap).contains oid') (l1e ++ l2e) := by
        rw [heq]
        clear region_mem_cfg heq hkerase hnotmem find_eqR2
        induction l1e with
        | nil =>
          dsimp
          exact List.find?_cons_of_neg hb2
        | cons a as ih =>
          dsimp
          by_cases hpa : (AList.keys a.snd.objMap).contains oid'
          · have find_eqA :
                List.find? (fun p => (AList.keys p.snd.objMap).contains oid')
                  (a :: (as ++ (⟨rid, region⟩ : Sigma (fun _ : RegionId => Region)) :: l2e)) =
                some a := List.find?_cons_of_pos hpa
            have find_eqB :
                List.find? (fun p => (AList.keys p.snd.objMap).contains oid') (a :: (as ++ l2e)) =
                some a := List.find?_cons_of_pos hpa
            rw [find_eqA, find_eqB]
          · have find_eqA :
                List.find? (fun p => (AList.keys p.snd.objMap).contains oid')
                  (a :: (as ++ (⟨rid, region⟩ : Sigma (fun _ : RegionId => Region)) :: l2e)) =
                List.find? (fun p => (AList.keys p.snd.objMap).contains oid')
                  (as ++ (⟨rid, region⟩ : Sigma (fun _ : RegionId => Region)) :: l2e) :=
              List.find?_cons_of_neg hpa
            have find_eqB :
                List.find? (fun p => (AList.keys p.snd.objMap).contains oid') (a :: (as ++ l2e)) =
                List.find? (fun p => (AList.keys p.snd.objMap).contains oid') (as ++ l2e) :=
              List.find?_cons_of_neg hpa
            rw [find_eqA, find_eqB]
            exact ih
      rw [find_eqL]
  have step1 := varAsgn_corollary_loc_match_eq
    (cfg.stackWithIndex.findRev? (fun f => (AList.keys f.objMap).contains oid'))
    (cfg.heap.entries.find? (fun p => (AList.keys p.snd.objMap).contains oid'))
  have step2 := varAsgn_corollary_loc_match_eq
    (cfg.stackWithIndex.findRev? (fun f => (AList.keys f.objMap).contains oid'))
    ((AList.insert rid { region with bridgeObjectId := oid } cfg.heap).entries.find?
      (fun p => (AList.keys p.snd.objMap).contains oid'))
  rw [heap_h2_map_eq] at step1
  exact step1.trans step2.symm

-- Combines the two branch-specific loc_eq corollaries: unconditionally (no fresh-id exception,
-- since varAsgn never allocates a new object), `Reference.loc?` is preserved for every oid'.
theorem varAsgn_corollary_loc_eq : ValidConfig cfg →
  varAsgn xf y cfg = some cfg' →
  ∀ oid', (Reference.OId oid').loc? cfg = (Reference.OId oid').loc? cfg' := by
  intro vcfg h oid'
  obtain ⟨frame, hframe, hcase⟩ := varAsgn_cases h
  rcases hcase with ⟨oid, rid, region, hyf, hxb, hloc, hridEq, hregion, hcfg'⟩ | ⟨oid, hyf, hxb, hresolve, hcfg'⟩
  · subst hcfg'
    exact varAsgn_corollary_bridge_loc_eq vcfg hregion oid'
  · subst hcfg'
    exact varAsgn_corollary_fresh_loc_eq hframe oid'

-- If `resolveV` finds oid0 (as a variable value or a bridge value) and oid0 resolves into a heap
-- region rid0, that region already has an owning ancestor frame currently on the stack. Needed for
-- S3's fresh-var branch: the value being newly stored in the stack was already a valid stack-rooted
-- reference before the mutation, so its region-ownership witness already existed in cfg.
theorem varAsgn_corollary_resolveV_loc_ancestor {cfg : RuntimeConfig} {var : VarName} {oid0 : ObjectId}
    (vcfg : ValidConfig cfg) (hrv : resolveV var cfg = some (Reference.OId oid0)) (rid0 : RegionId)
    (hloc0 : (Reference.OId oid0).loc? cfg = some (Location.Rgn rid0)) :
    ∃ frame'' ∈ cfg.stackWithIndex, frame''.regionId = rid0 ∧ frame''.index < cfg.stack.length := by
  unfold resolveV at hrv
  cases hfV : cfg.stackWithIndex.findRev? (fun frame => frame.varMap.keys.contains var ∨ frame.bridgeVar == var) with
  | none => rw [hfV] at hrv; contradiction
  | some frameV =>
    rw [hfV] at hrv
    dsimp at hrv
    have hframeV_mem : frameV ∈ cfg.stackWithIndex := by
      rw [List.findRev?_eq_find?_reverse] at hfV
      exact List.mem_reverse.mp (List.mem_of_find?_eq_some hfV)
    have hframeV_lt : frameV.index < cfg.stack.length := by
      unfold RuntimeConfig.stackWithIndex at hframeV_mem
      obtain ⟨n, hn, heqn⟩ := List.mem_mapIdx.mp hframeV_mem
      rw [← heqn]
      exact hn
    cases hlookupV : frameV.varMap.lookup var with
    | some refV =>
      rw [hlookupV] at hrv
      dsimp at hrv
      rw [Option.some_inj] at hrv
      have hmemV : refV ∈ frameV.refs := by
        unfold Frame.refs
        exact List.mem_append_right _ (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hlookupV))
      rw [hrv] at hmemV
      obtain ⟨frame'', hmem'', hregion'', hidx''⟩ :=
        vcfg.s3 frameV hframeV_mem (Reference.OId oid0) hmemV rid0 oid0 rfl hloc0
      exact ⟨frame'', hmem'', hregion'', lt_of_le_of_lt hidx'' hframeV_lt⟩
    | none =>
      rw [hlookupV] at hrv
      dsimp at hrv
      by_cases hbv : frameV.bridgeVar == var
      · rw [if_pos hbv] at hrv
        cases hregionV : cfg.heap.lookup frameV.regionId with
        | none => rw [hregionV] at hrv; dsimp at hrv; contradiction
        | some regionV =>
          rw [hregionV] at hrv
          dsimp at hrv
          rw [Option.some_inj, Reference.OId.injEq] at hrv
          have h1 := vcfg.h1
          have hmemBridge : regionV.bridgeObjectId ∈ regionV.objMap :=
            h1 regionV (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hregionV))
          have hlocBridge : (Reference.OId regionV.bridgeObjectId).loc? cfg =
              some (Location.Rgn frameV.regionId) :=
            (oid_loc_rgn_iff_in_heap vcfg).mpr ⟨regionV, hregionV, hmemBridge⟩
          rw [hrv, hloc0, Option.some_inj, Location.Rgn.injEq] at hlocBridge
          exact ⟨frameV, hframeV_mem, hlocBridge.symm, hframeV_lt⟩
      · rw [if_neg hbv] at hrv; contradiction

-- A successful `resolveFA` retrieving a heap-located reference already has an owning ancestor
-- frame on the stack -- combines the Stk-root case (direct s3 application) and the Rgn-root case
-- (via H3 identifying the target region with the root's own region, then
-- varAsgn_corollary_resolveV_loc_ancestor for the root). Needed by S3's fresh-var branch.
theorem varAsgn_corollary_yfRef_ancestor {cfg : RuntimeConfig} {y : FieldAccess} {oid : ObjectId}
    (vcfg : ValidConfig cfg) (hyf : resolveFA y cfg = some (Reference.OId oid)) (rid' : RegionId)
    (hlocEq : (Reference.OId oid).loc? cfg = some (Location.Rgn rid')) :
    ∃ frame'' ∈ cfg.stackWithIndex, frame''.regionId = rid' ∧ frame''.index < cfg.stack.length := by
  unfold resolveFA at hyf
  cases hrv : resolveV y.root cfg with
  | none => rw [hrv] at hyf; contradiction
  | some ref0 =>
    rw [hrv] at hyf
    dsimp at hyf
    cases ref0 with
    | RId rid0 => dsimp at hyf; contradiction
    | OId oid0 =>
      dsimp at hyf
      cases hloc0 : (Reference.OId oid0).loc? cfg with
      | none => rw [hloc0] at hyf; dsimp at hyf; contradiction
      | some loc0 =>
        rw [hloc0] at hyf
        dsimp at hyf
        cases loc0 with
        | Stk fid0 =>
          dsimp at hyf
          cases hframe0 : cfg.stackWithIndex.find? (fun frame => frame.index == fid0) with
          | none => rw [hframe0] at hyf; dsimp at hyf; contradiction
          | some frame0 =>
            rw [hframe0] at hyf
            dsimp at hyf
            cases hobj0 : frame0.objMap.lookup oid0 with
            | none => rw [hobj0] at hyf; dsimp at hyf; contradiction
            | some obj0 =>
              rw [hobj0] at hyf
              dsimp at hyf
              have hmem_obj : Reference.OId oid ∈ Object.refs obj0 := by
                unfold Object.refs
                exact List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hyf)
              have hmem_frame0 : Reference.OId oid ∈ frame0.refs := by
                unfold Frame.refs
                apply List.mem_append_left
                rw [List.bind_eq_flatMap, List.mem_flatMap]
                exact ⟨obj0, List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hobj0), hmem_obj⟩
              have hmem_stack0 : frame0 ∈ cfg.stackWithIndex := List.mem_of_find?_eq_some hframe0
              have hframe0_lt : frame0.index < cfg.stack.length := by
                unfold RuntimeConfig.stackWithIndex at hmem_stack0
                obtain ⟨n, hn, heqn⟩ := List.mem_mapIdx.mp hmem_stack0
                rw [← heqn]; exact hn
              obtain ⟨frame'', hmem'', hregion'', hidx''⟩ :=
                vcfg.s3 frame0 hmem_stack0 (Reference.OId oid) hmem_frame0 rid' oid rfl hlocEq
              exact ⟨frame'', hmem'', hregion'', lt_of_le_of_lt hidx'' hframe0_lt⟩
        | Rgn rid0 =>
          dsimp at hyf
          cases hregion0 : cfg.heap.lookup rid0 with
          | none => rw [hregion0] at hyf; dsimp at hyf; contradiction
          | some region0 =>
            rw [hregion0] at hyf
            dsimp at hyf
            cases hobj0 : region0.objMap.lookup oid0 with
            | none => rw [hobj0] at hyf; dsimp at hyf; contradiction
            | some obj0 =>
              rw [hobj0] at hyf
              dsimp at hyf
              have hmem_obj : Reference.OId oid ∈ Object.refs obj0 := by
                unfold Object.refs
                exact List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hyf)
              have hmem_region0 : Reference.OId oid ∈ Region.refs region0 := by
                unfold Region.refs
                rw [List.bind_eq_flatMap, List.mem_flatMap]
                exact ⟨obj0, List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hobj0), hmem_obj⟩
              have h3fact := vcfg.h3 rid0 oid region0 hregion0 hmem_region0
              rw [hlocEq, Option.some_inj, Location.Rgn.injEq] at h3fact
              obtain ⟨frame'', hmem'', hregion'', hidx''⟩ :=
                varAsgn_corollary_resolveV_loc_ancestor vcfg hrv rid0 hloc0
              exact ⟨frame'', hmem'', h3fact ▸ hregion'', hidx''⟩

theorem varAsgn_L1 : ValidConfig cfg →
  varAsgn xf y cfg = some cfg' →
  L1 cfg' := by
  intro vcfg h
  have l1 := vcfg.l1
  obtain ⟨frame, hframe, hcase⟩ := varAsgn_cases h
  unfold L1
  rcases hcase with ⟨oid, rid, region, hyf, hxb, hloc, hridEq, hregion, hcfg'⟩ | ⟨oid, hyf, hxb, hresolve, hcfg'⟩
  · subst hcfg'
    have perm := varAsgn_corollary_bridge_heap_objectIds_perm (oid := oid) hregion
    have objectIds_perm : ({ cfg with heap := cfg.heap.insert rid { region with bridgeObjectId := oid } } :
        RuntimeConfig).objectIds.Perm cfg.objectIds := by
      unfold RuntimeConfig.objectIds
      dsimp
      exact List.Perm.append_left cfg.stack.objectIds perm
    exact l1.perm objectIds_perm.symm
  · subst hcfg'
    have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
      (List.dropLast_append_getLast? frame hframe).symm
    have stack_objectIds_eq :
        Stack.objectIds (cfg.stack.dropLast ++
          [{ frame with varMap := frame.varMap.insert xf (Reference.OId oid) }]) =
        cfg.stack.objectIds := by
      conv_rhs => rw [stack_eq]
      unfold Stack.objectIds
      simp [Frame.objectIds]
    unfold RuntimeConfig.objectIds
    dsimp
    rw [stack_objectIds_eq]
    exact l1

theorem varAsgn_L2 : ValidConfig cfg →
  varAsgn xf y cfg = some cfg' →
  L2 cfg' := by
  intro vcfg h
  have l2 := vcfg.l2
  obtain ⟨frame, hframe, hcase⟩ := varAsgn_cases h
  unfold L2
  rcases hcase with ⟨oid, rid, region, hyf, hxb, hloc, hridEq, hregion, hcfg'⟩ | ⟨oid, hyf, hxb, hresolve, hcfg'⟩
  · subst hcfg'
    dsimp
    intro frame'' hmem
    obtain ⟨region0, hlookup0, hopen0⟩ := l2 frame'' hmem
    by_cases heq : frame''.regionId = rid
    · rw [heq] at hlookup0
      rw [hregion, Option.some_inj] at hlookup0
      refine ⟨{ region with bridgeObjectId := oid }, ?_, ?_⟩
      · rw [heq, AList.lookup_insert]
      · dsimp; rw [hlookup0]; exact hopen0
    · refine ⟨region0, ?_, hopen0⟩
      rw [AList.lookup_insert_ne heq]
      exact hlookup0
  · subst hcfg'
    dsimp
    have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
      (List.dropLast_append_getLast? frame hframe).symm
    have frame_mem : frame ∈ cfg.stack := stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self frame)
    intro frame'' hmem
    rw [List.mem_append, List.mem_singleton] at hmem
    cases hmem with
    | inl hdrop => exact l2 frame'' (List.mem_of_mem_dropLast hdrop)
    | inr heqframe => subst heqframe; exact l2 frame frame_mem

theorem varAsgn_H1 : ValidConfig cfg →
  varAsgn xf y cfg = some cfg' →
  H1 cfg' := by
  intro vcfg h
  have h1 := vcfg.h1
  obtain ⟨frame, hframe, hcase⟩ := varAsgn_cases h
  unfold H1
  rcases hcase with ⟨oid, rid, region, hyf, hxb, hloc, hridEq, hregion, hcfg'⟩ | ⟨oid, hyf, hxb, hresolve, hcfg'⟩
  · subst hcfg'
    dsimp
    have oid_in_region : oid ∈ region.objMap := by
      obtain ⟨region', hlookup', hmem'⟩ := (oid_loc_rgn_iff_in_heap vcfg).mp hloc
      rw [hregion, Option.some_inj] at hlookup'
      rw [hlookup']
      exact hmem'
    intro region0 hregion0
    unfold Heap.regions at hregion0
    rw [AList.entries_insert, List.map_cons, List.mem_cons] at hregion0
    cases hregion0 with
    | inl heqregion =>
      subst heqregion
      exact oid_in_region
    | inr hkeraseregion =>
      apply h1
      unfold Heap.regions
      exact (List.Sublist.map _ (List.kerase_sublist rid cfg.heap.entries)).mem hkeraseregion
  · subst hcfg'
    dsimp
    exact h1

theorem varAsgn_H2 : ValidConfig cfg →
  varAsgn xf y cfg = some cfg' →
  H2 cfg' := by
  intro vcfg h
  have h2 := vcfg.h2
  obtain ⟨frame, hframe, hcase⟩ := varAsgn_cases h
  unfold H2
  rcases hcase with ⟨oid, rid, region, hyf, hxb, hloc, hridEq, hregion, hcfg'⟩ | ⟨oid, hyf, hxb, hresolve, hcfg'⟩
  · subst hcfg'
    intro rid'
    have refs_perm := varAsgn_corollary_bridge_heap_refs_perm (oid := oid) hregion
    dsimp
    rw [refs_perm.count_eq]
    exact h2 rid'
  · subst hcfg'
    intro rid'
    dsimp
    have fresh_not_in_frame : xf ∉ frame.varMap.keys :=
      varAsgn_corollary_fresh_not_in_frame hframe hresolve
    have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
      (List.dropLast_append_getLast? frame hframe).symm
    set newFrame : Frame := { frame with varMap := frame.varMap.insert xf (Reference.OId oid) } with newFrame_def
    have newFrame_refs_le :
        newFrame.refs.count (Reference.RId rid') ≤ frame.refs.count (Reference.RId rid') := by
      rw [newFrame_def]
      unfold Frame.refs
      dsimp
      rw [List.kerase_of_notMem_keys fresh_not_in_frame, List.count_append, List.count_append]
      have hne : (Reference.OId oid == Reference.RId rid') = false := rfl
      have varMap_le :
          (Reference.OId oid :: frame.varMap.entries.map (·.2)).count (Reference.RId rid') ≤
          (frame.varMap.entries.map (·.2)).count (Reference.RId rid') := by
        rw [List.count_cons, hne]
        dsimp
        exact le_refl _
      exact Nat.add_le_add_left varMap_le _
    have stack_refs_le :
        (Stack.refs (cfg.stack.dropLast ++ [newFrame])).count (Reference.RId rid') ≤
        cfg.stack.refs.count (Reference.RId rid') := by
      have split1 : Stack.refs (cfg.stack.dropLast ++ [newFrame]) =
          Stack.refs cfg.stack.dropLast ++ newFrame.refs := by
        unfold Stack.refs
        rw [List.bind_eq_flatMap, List.bind_eq_flatMap, List.flatMap_id, List.flatMap_id,
          List.map_append, List.flatten_append]
        simp
      have split2 : cfg.stack.refs = Stack.refs cfg.stack.dropLast ++ frame.refs := by
        conv_lhs => rw [stack_eq]
        unfold Stack.refs
        rw [List.bind_eq_flatMap, List.bind_eq_flatMap, List.flatMap_id, List.flatMap_id,
          List.map_append, List.flatten_append]
        simp
      rw [split1, split2, List.count_append, List.count_append]
      exact Nat.add_le_add_left newFrame_refs_le _
    exact Nat.le_trans (Nat.add_le_add_right stack_refs_le _) (h2 rid')

theorem varAsgn_H3 : ValidConfig cfg →
  varAsgn xf y cfg = some cfg' →
  H3 cfg' := by
  intro vcfg h
  have h3 := vcfg.h3
  have loc_eq := varAsgn_corollary_loc_eq vcfg h
  obtain ⟨frame, hframe, hcase⟩ := varAsgn_cases h
  unfold H3
  rcases hcase with ⟨oid, rid, region, hyf, hxb, hloc, hridEq, hregion, hcfg'⟩ | ⟨oid, hyf, hxb, hresolve, hcfg'⟩
  · subst hcfg'
    intro rid0 oid0 region0 hlookup0 href0
    by_cases hrideq : rid0 = rid
    · subst hrideq
      rw [AList.lookup_insert, Option.some_inj] at hlookup0
      subst hlookup0
      have h3fact := h3 rid0 oid0 region hregion href0
      rw [← loc_eq oid0]
      exact h3fact
    · rw [AList.lookup_insert_ne hrideq] at hlookup0
      have h3fact := h3 rid0 oid0 region0 hlookup0 href0
      rw [← loc_eq oid0]
      exact h3fact
  · subst hcfg'
    intro rid0 oid0 region0 hlookup0 href0
    have h3fact := h3 rid0 oid0 region0 hlookup0 href0
    rw [← loc_eq oid0]
    exact h3fact

theorem varAsgn_S1 : ValidConfig cfg →
  varAsgn xf y cfg = some cfg' →
  S1 cfg' := by
  intro vcfg h
  have s1 := vcfg.s1
  obtain ⟨frame, hframe, hcase⟩ := varAsgn_cases h
  unfold S1
  rcases hcase with ⟨oid, rid, region, hyf, hxb, hloc, hridEq, hregion, hcfg'⟩ | ⟨oid, hyf, hxb, hresolve, hcfg'⟩
  · subst hcfg'
    exact s1
  · subst hcfg'
    dsimp
    have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
      (List.dropLast_append_getLast? frame hframe).symm
    have regionId_eq : (cfg.stack.dropLast ++
        [{ frame with varMap := frame.varMap.insert xf (Reference.OId oid) }]).map (fun f : Frame => f.regionId) =
        cfg.stack.map (fun f : Frame => f.regionId) := by
      conv_rhs => rw [stack_eq]
      rw [List.map_append, List.map_append]
      rfl
    rw [regionId_eq]
    exact s1

theorem varAsgn_S2 : ValidConfig cfg →
  varAsgn xf y cfg = some cfg' →
  S2 cfg' := by
  intro vcfg h
  have s2 := vcfg.s2
  have loc_eq := varAsgn_corollary_loc_eq vcfg h
  obtain ⟨frame, hframe, hcase⟩ := varAsgn_cases h
  unfold S2
  rcases hcase with ⟨oid, rid, region, hyf, hxb, hloc, hridEq, hregion, hcfg'⟩ | ⟨oid, hyf, hxb, hresolve, hcfg'⟩
  · subst hcfg'
    intro frame' hframe' ref href fid' oid0 hrefeq hlocEq
    subst hrefeq
    have hlocEq_cfg : (Reference.OId oid0).loc? cfg = some (Location.Stk fid') := by
      rw [loc_eq oid0]; exact hlocEq
    exact s2 frame' hframe' (Reference.OId oid0) href fid' oid0 rfl hlocEq_cfg
  · subst hcfg'
    have fresh_not_in_frame : xf ∉ frame.varMap.keys :=
      varAsgn_corollary_fresh_not_in_frame hframe hresolve
    have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
      (List.dropLast_append_getLast? frame hframe).symm
    have frame_mem : frame ∈ cfg.stack := stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self frame)
    set newFrame : Frame := { frame with varMap := frame.varMap.insert xf (Reference.OId oid) } with newFrame_def
    have newFrame_refs_mem : ∀ ref, ref ∈ newFrame.refs → ref = Reference.OId oid ∨ ref ∈ frame.refs := by
      intro ref href
      rw [newFrame_def] at href
      unfold Frame.refs at href
      dsimp at href
      rw [List.kerase_of_notMem_keys fresh_not_in_frame, List.mem_append] at href
      rcases href with hobjmap | hvarmap
      · right; unfold Frame.refs; exact List.mem_append_left _ hobjmap
      · rw [List.mem_cons] at hvarmap
        rcases hvarmap with heq | horig
        · left; exact heq
        · right; unfold Frame.refs; exact List.mem_append_right _ horig
    have stackWithIndex_eq_cfg :
        cfg.stackWithIndex =
          cfg.stack.dropLast.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) ++
            [({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex)] := by
      unfold RuntimeConfig.stackWithIndex
      conv_lhs => rw [stack_eq]
      rw [List.mapIdx_concat]
    have stackWithIndex_eq :
        (RuntimeConfig.stackWithIndex { stack := cfg.stack.dropLast ++ [newFrame], heap := cfg.heap }) =
          cfg.stack.dropLast.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) ++
            [({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex)] := by
      unfold RuntimeConfig.stackWithIndex
      dsimp
      rw [List.mapIdx_concat]
    intro frame' hframe' ref href fid' oid0 hrefeq hlocEq
    subst hrefeq
    rw [stackWithIndex_eq, List.mem_append, List.mem_singleton] at hframe'
    rcases hframe' with hold | hnew
    · have hframe'_in_cfg : frame' ∈ cfg.stackWithIndex := by
        rw [stackWithIndex_eq_cfg]
        exact List.mem_append_left _ hold
      have hlocEq_cfg : (Reference.OId oid0).loc? cfg = some (Location.Stk fid') := by
        rw [loc_eq oid0]; exact hlocEq
      exact s2 frame' hframe'_in_cfg (Reference.OId oid0) href fid' oid0 rfl hlocEq_cfg
    · subst hnew
      dsimp at href
      have hlocEq_cfg : (Reference.OId oid0).loc? cfg = some (Location.Stk fid') := by
        rw [loc_eq oid0]; exact hlocEq
      rcases newFrame_refs_mem _ href with hfreq | horig
      · obtain ⟨frameW, hlookupW, _⟩ := (oid_loc_stk_iff_in_stack vcfg).mp hlocEq_cfg
        have hlt := (List.getElem?_eq_some_iff.mp hlookupW).1
        have hstacklen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by
          conv_lhs => rw [stack_eq]
          rw [List.length_append, List.length_singleton]
        have hlen : cfg.stackWithIndex.length = cfg.stack.dropLast.length + 1 := by
          unfold RuntimeConfig.stackWithIndex
          rw [List.length_mapIdx, hstacklen]
        rw [hlen] at hlt
        dsimp
        exact Nat.le_of_lt_succ hlt
      · have hframe_in_cfg :
            ({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex) ∈ cfg.stackWithIndex := by
          rw [stackWithIndex_eq_cfg]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        exact s2 _ hframe_in_cfg (Reference.OId oid0) horig fid' oid0 rfl hlocEq_cfg

theorem varAsgn_S3 : ValidConfig cfg →
  varAsgn xf y cfg = some cfg' →
  S3 cfg' := by
  intro vcfg h
  have s3 := vcfg.s3
  have loc_eq := varAsgn_corollary_loc_eq vcfg h
  obtain ⟨frame, hframe, hcase⟩ := varAsgn_cases h
  unfold S3
  rcases hcase with ⟨oid, rid, region, hyf, hxb, hloc, hridEq, hregion, hcfg'⟩ | ⟨oid, hyf, hxb, hresolve, hcfg'⟩
  · subst hcfg'
    intro frame' hframe' ref href fid' oid0 hrefeq hlocEq
    subst hrefeq
    have hlocEq_cfg : (Reference.OId oid0).loc? cfg = some (Location.Rgn fid') := by
      rw [loc_eq oid0]; exact hlocEq
    exact s3 frame' hframe' (Reference.OId oid0) href fid' oid0 rfl hlocEq_cfg
  · subst hcfg'
    have fresh_not_in_frame : xf ∉ frame.varMap.keys :=
      varAsgn_corollary_fresh_not_in_frame hframe hresolve
    have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
      (List.dropLast_append_getLast? frame hframe).symm
    have frame_mem : frame ∈ cfg.stack := stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self frame)
    set newFrame : Frame := { frame with varMap := frame.varMap.insert xf (Reference.OId oid) } with newFrame_def
    have newFrame_refs_mem : ∀ ref, ref ∈ newFrame.refs → ref = Reference.OId oid ∨ ref ∈ frame.refs := by
      intro ref href
      rw [newFrame_def] at href
      unfold Frame.refs at href
      dsimp at href
      rw [List.kerase_of_notMem_keys fresh_not_in_frame, List.mem_append] at href
      rcases href with hobjmap | hvarmap
      · right; unfold Frame.refs; exact List.mem_append_left _ hobjmap
      · rw [List.mem_cons] at hvarmap
        rcases hvarmap with heq | horig
        · left; exact heq
        · right; unfold Frame.refs; exact List.mem_append_right _ horig
    have stackWithIndex_eq_cfg :
        cfg.stackWithIndex =
          cfg.stack.dropLast.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) ++
            [({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex)] := by
      unfold RuntimeConfig.stackWithIndex
      conv_lhs => rw [stack_eq]
      rw [List.mapIdx_concat]
    have stackWithIndex_eq :
        (RuntimeConfig.stackWithIndex { stack := cfg.stack.dropLast ++ [newFrame], heap := cfg.heap }) =
          cfg.stack.dropLast.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) ++
            [({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex)] := by
      unfold RuntimeConfig.stackWithIndex
      dsimp
      rw [List.mapIdx_concat]
    have transport : ∀ frame3 : FrameWithIndex, frame3 ∈ cfg.stackWithIndex →
        ∃ frame4 ∈ (RuntimeConfig.stackWithIndex { stack := cfg.stack.dropLast ++ [newFrame], heap := cfg.heap }),
          frame4.regionId = frame3.regionId ∧ frame4.index = frame3.index := by
      intro frame3 hmem3
      rw [stackWithIndex_eq_cfg, List.mem_append, List.mem_singleton] at hmem3
      rcases hmem3 with hd | hl
      · exact ⟨frame3, by rw [stackWithIndex_eq]; exact List.mem_append_left _ hd, rfl, rfl⟩
      · refine ⟨{ newFrame with index := cfg.stack.dropLast.length }, ?_, ?_, ?_⟩
        · rw [stackWithIndex_eq]; exact List.mem_append_right _ (List.mem_singleton_self _)
        · rw [hl]
        · rw [hl]
    have hstacklen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by
      conv_lhs => rw [stack_eq]
      rw [List.length_append, List.length_singleton]
    intro frame' hframe' ref href rid' oid0 hrefeq hlocEq
    subst hrefeq
    have hlocEq_cfg : (Reference.OId oid0).loc? cfg = some (Location.Rgn rid') := by
      rw [loc_eq oid0]; exact hlocEq
    rw [stackWithIndex_eq, List.mem_append, List.mem_singleton] at hframe'
    rcases hframe' with hold | hnew
    · have hframe'_in_cfg : frame' ∈ cfg.stackWithIndex := by
        rw [stackWithIndex_eq_cfg]
        exact List.mem_append_left _ hold
      obtain ⟨frame'', hmem'', hregion'', hidx''⟩ :=
        s3 frame' hframe'_in_cfg (Reference.OId oid0) href rid' oid0 rfl hlocEq_cfg
      obtain ⟨frame4, hmem4, hregion4, hidx4⟩ := transport frame'' hmem''
      exact ⟨frame4, hmem4, hregion4.trans hregion'', (le_of_eq hidx4).trans hidx''⟩
    · subst hnew
      dsimp at href
      rcases newFrame_refs_mem _ href with hfreq | horig
      · rw [hfreq] at hlocEq_cfg
        obtain ⟨frame'', hmem'', hregion'', hidx''⟩ :=
          varAsgn_corollary_yfRef_ancestor vcfg hyf rid' hlocEq_cfg
        obtain ⟨frame4, hmem4, hregion4, hidx4⟩ := transport frame'' hmem''
        refine ⟨frame4, hmem4, hregion4.trans hregion'', ?_⟩
        dsimp
        rw [hidx4]
        rw [hstacklen] at hidx''
        exact Nat.le_of_lt_succ hidx''
      · have hframe_in_cfg :
            ({ frame with index := cfg.stack.dropLast.length } : FrameWithIndex) ∈ cfg.stackWithIndex := by
          rw [stackWithIndex_eq_cfg]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        obtain ⟨frame'', hmem'', hregion'', hidx''⟩ :=
          s3 _ hframe_in_cfg (Reference.OId oid0) horig rid' oid0 rfl hlocEq_cfg
        obtain ⟨frame4, hmem4, hregion4, hidx4⟩ := transport frame'' hmem''
        exact ⟨frame4, hmem4, hregion4.trans hregion'', (le_of_eq hidx4).trans hidx''⟩

theorem varAsgn_HS1 : ValidConfig cfg →
  varAsgn xf y cfg = some cfg' →
  HS1 cfg' := by
  intro vcfg h
  have hs1 := vcfg.hs1
  obtain ⟨frame, hframe, hcase⟩ := varAsgn_cases h
  unfold HS1
  rcases hcase with ⟨oid, rid, region, hyf, hxb, hloc, hridEq, hregion, hcfg'⟩ | ⟨oid, hyf, hxb, hresolve, hcfg'⟩
  · subst hcfg'
    have objectIds_perm := varAsgn_corollary_bridge_heap_objectIds_perm (oid := oid) hregion
    have refs_perm := varAsgn_corollary_bridge_heap_refs_perm (oid := oid) hregion
    have full_objectIds_perm :
        ({ cfg with heap := cfg.heap.insert rid { region with bridgeObjectId := oid } } :
          RuntimeConfig).objectIds.Perm cfg.objectIds := by
      unfold RuntimeConfig.objectIds
      dsimp
      exact List.Perm.append_left cfg.stack.objectIds objectIds_perm
    intro oid'' hmem
    rw [full_objectIds_perm.mem_iff]
    unfold RuntimeConfig.refs at hmem
    dsimp at hmem
    rw [List.mem_append] at hmem
    rcases hmem with hstack | hheap
    · exact hs1 oid'' (List.mem_append_left _ hstack)
    · exact hs1 oid'' (List.mem_append_right _ (refs_perm.mem_iff.mp hheap))
  · subst hcfg'
    have fresh_not_in_frame : xf ∉ frame.varMap.keys :=
      varAsgn_corollary_fresh_not_in_frame hframe hresolve
    have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
      (List.dropLast_append_getLast? frame hframe).symm
    have frame_mem : frame ∈ cfg.stack := stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self frame)
    set newFrame : Frame := { frame with varMap := frame.varMap.insert xf (Reference.OId oid) } with newFrame_def
    have newFrame_refs_mem : ∀ ref, ref ∈ newFrame.refs → ref = Reference.OId oid ∨ ref ∈ frame.refs := by
      intro ref href
      rw [newFrame_def] at href
      unfold Frame.refs at href
      dsimp at href
      rw [List.kerase_of_notMem_keys fresh_not_in_frame, List.mem_append] at href
      rcases href with hobjmap | hvarmap
      · right; unfold Frame.refs; exact List.mem_append_left _ hobjmap
      · rw [List.mem_cons] at hvarmap
        rcases hvarmap with heq | horig
        · left; exact heq
        · right; unfold Frame.refs; exact List.mem_append_right _ horig
    have stack_objectIds_eq :
        Stack.objectIds (cfg.stack.dropLast ++ [newFrame]) = cfg.stack.objectIds := by
      conv_rhs => rw [stack_eq]
      unfold Stack.objectIds
      simp [Frame.objectIds, newFrame_def]
    have stack_refs_append : ∀ (l : Stack) (f : Frame), Stack.refs (l ++ [f]) = Stack.refs l ++ f.refs := by
      intro l f
      unfold Stack.refs
      rw [List.bind_eq_flatMap, List.bind_eq_flatMap, List.flatMap_id, List.flatMap_id,
        List.map_append, List.flatten_append]
      simp
    have dropLast_refs_to_cfg_refs : ∀ ref, ref ∈ Stack.refs cfg.stack.dropLast → ref ∈ cfg.refs := by
      intro ref href
      apply List.mem_append_left
      rw [stack_eq, stack_refs_append]
      exact List.mem_append_left _ href
    have frame_refs_to_cfg_refs : ∀ ref, ref ∈ frame.refs → ref ∈ cfg.refs := by
      intro ref href
      apply List.mem_append_left
      rw [stack_eq, stack_refs_append]
      exact List.mem_append_right _ href
    intro oid'' hmem
    unfold RuntimeConfig.objectIds
    dsimp
    rw [stack_objectIds_eq]
    unfold RuntimeConfig.refs at hmem
    dsimp at hmem
    rw [List.mem_append, stack_refs_append, List.mem_append] at hmem
    rcases hmem with (hdrop | hnew) | hheap
    · exact hs1 oid'' (dropLast_refs_to_cfg_refs _ hdrop)
    · rcases newFrame_refs_mem _ hnew with hfreq | horig
      · rw [Reference.OId.injEq] at hfreq
        rw [hfreq]
        exact hs1 oid (varAsgn_corollary_yfRef_mem_refs hyf)
      · exact hs1 oid'' (frame_refs_to_cfg_refs _ horig)
    · exact hs1 oid'' (List.mem_append_right _ hheap)

theorem varAsgn_HS2 : ValidConfig cfg →
  varAsgn xf y cfg = some cfg' →
  HS2 cfg' := by
  intro vcfg h
  have hs2 := vcfg.hs2
  obtain ⟨frame, hframe, hcase⟩ := varAsgn_cases h
  unfold HS2
  rcases hcase with ⟨oid, rid, region, hyf, hxb, hloc, hridEq, hregion, hcfg'⟩ | ⟨oid, hyf, hxb, hresolve, hcfg'⟩
  · subst hcfg'
    intro rid'' hmem
    have keys_mem := varAsgn_corollary_bridge_heap_keys_mem (oid := oid) hregion
    have refs_perm := varAsgn_corollary_bridge_heap_refs_perm (oid := oid) hregion
    rw [keys_mem]
    unfold RuntimeConfig.refs at hmem
    dsimp at hmem
    rw [List.mem_append] at hmem
    rcases hmem with hstack | hheap
    · exact hs2 rid'' (List.mem_append_left _ hstack)
    · exact hs2 rid'' (List.mem_append_right _ (refs_perm.mem_iff.mp hheap))
  · subst hcfg'
    dsimp
    have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
      (List.dropLast_append_getLast? frame hframe).symm
    have frame_mem : frame ∈ cfg.stack := stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self frame)
    have fresh_not_in_frame : xf ∉ frame.varMap.keys :=
      varAsgn_corollary_fresh_not_in_frame hframe hresolve
    set newFrame : Frame := { frame with varMap := frame.varMap.insert xf (Reference.OId oid) } with newFrame_def
    have newFrame_refs_mem : ∀ ref, ref ∈ newFrame.refs → ref = Reference.OId oid ∨ ref ∈ frame.refs := by
      intro ref href
      rw [newFrame_def] at href
      unfold Frame.refs at href
      dsimp at href
      rw [List.kerase_of_notMem_keys fresh_not_in_frame, List.mem_append] at href
      rcases href with hobjmap | hvarmap
      · right; unfold Frame.refs; exact List.mem_append_left _ hobjmap
      · rw [List.mem_cons] at hvarmap
        rcases hvarmap with heq | horig
        · left; exact heq
        · right; unfold Frame.refs; exact List.mem_append_right _ horig
    have stack_refs_append : ∀ (l : Stack) (f : Frame), Stack.refs (l ++ [f]) = Stack.refs l ++ f.refs := by
      intro l f
      unfold Stack.refs
      rw [List.bind_eq_flatMap, List.bind_eq_flatMap, List.flatMap_id, List.flatMap_id,
        List.map_append, List.flatten_append]
      simp
    intro rid'' hmem
    unfold RuntimeConfig.refs at hmem
    dsimp at hmem
    rw [List.mem_append, stack_refs_append, List.mem_append] at hmem
    rcases hmem with (hdrop | hnew) | hheap
    · exact hs2 rid'' (List.mem_append_left _ (by
        rw [stack_eq, stack_refs_append]; exact List.mem_append_left _ hdrop))
    · rcases newFrame_refs_mem _ hnew with hfreq | horig
      · exact absurd hfreq (by simp)
      · exact hs2 rid'' (List.mem_append_left _ (by
          rw [stack_eq, stack_refs_append]; exact List.mem_append_right _ horig))
    · exact hs2 rid'' (List.mem_append_right _ hheap)

theorem varAsgn_valid : ValidConfig cfg →
  varAsgn xf y cfg = some cfg' →
  ValidConfig cfg' := by
  intro vcfg h
  exact {
    l1 := varAsgn_L1 vcfg h,
    l2 := varAsgn_L2 vcfg h,
    h1 := varAsgn_H1 vcfg h,
    h2 := varAsgn_H2 vcfg h,
    h3 := varAsgn_H3 vcfg h,
    s1 := varAsgn_S1 vcfg h,
    s2 := varAsgn_S2 vcfg h,
    s3 := varAsgn_S3 vcfg h,
    hs1 := varAsgn_HS1 vcfg h,
    hs2 := varAsgn_HS2 vcfg h
  }
