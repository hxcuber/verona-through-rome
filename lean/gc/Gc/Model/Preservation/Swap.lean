import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Theorems
import Gc.Model.Mutation

import Mathlib.Data.List.Infix

theorem swap_cases (h : swap x yf cfg = some cfg') :
    ∃ frame : FrameWithIndex, cfg.stackWithIndex.getLast? = some frame ∧
    ∃ yRef, resolveV yf.root cfg = some yRef ∧
    ∃ yRefLoc, yRef.loc? cfg = some yRefLoc ∧
    ∃ yfRef, resolveFA yf cfg = some yfRef ∧
    ∃ yfRefLoc, yfRef.loc? cfg = some yfRefLoc ∧
    ((-- SWAP-STACK
      ∃ yoid xRef obj,
        x ≠ frame.bridgeVar ∧
        yRef = Reference.OId yoid ∧
        yRefLoc = Location.Stk frame.index ∧
        frame.varMap.lookup x = some xRef ∧
        frame.objMap.lookup yoid = some obj ∧
        cfg' = { cfg with stack := cfg.stack.dropLast ++ [ { frame with
          varMap := frame.varMap.insert x yfRef,
          objMap := frame.objMap.insert yoid (obj.insert yf.field xRef)
        } ] }) ∨
     (-- SWAP-REGION-OBJECT
      ∃ yoid rid region obj xoid xrid,
        x ≠ frame.bridgeVar ∧
        yRef = Reference.OId yoid ∧
        yRefLoc = Location.Rgn rid ∧
        rid = frame.regionId ∧
        cfg.heap.lookup rid = some region ∧
        region.objMap.lookup yoid = some obj ∧
        frame.varMap.lookup x = some (Reference.OId xoid) ∧
        (Reference.OId xoid).loc? cfg = some (Location.Rgn xrid) ∧
        xrid = frame.regionId ∧
        region.status = Status.Open ∧
        cfg' = { cfg with
          stack := cfg.stack.dropLast ++ [ { frame with varMap := frame.varMap.insert x yfRef } ],
          heap := cfg.heap.insert rid { region with
            objMap := region.objMap.insert yoid (obj.insert yf.field (Reference.OId xoid)) }
        }) ∨
     (-- SWAP-REGION-REGION
      ∃ yoid rid region obj xrid,
        x ≠ frame.bridgeVar ∧
        yRef = Reference.OId yoid ∧
        yRefLoc = Location.Rgn rid ∧
        rid = frame.regionId ∧
        cfg.heap.lookup rid = some region ∧
        region.objMap.lookup yoid = some obj ∧
        frame.varMap.lookup x = some (Reference.RId xrid) ∧
        region.status = Status.Open ∧
        cfg' = { cfg with
          stack := cfg.stack.dropLast ++ [ { frame with varMap := frame.varMap.insert x yfRef } ],
          heap := cfg.heap.insert rid { region with
            objMap := region.objMap.insert yoid (obj.insert yf.field (Reference.RId xrid)) }
        }) ∨
     (-- SWAP-REGION-BRIDGE
      ∃ yoid yrid yfoid yfrid region obj,
        x = frame.bridgeVar ∧
        yRef = Reference.OId yoid ∧
        yRefLoc = Location.Rgn yrid ∧
        yfRef = Reference.OId yfoid ∧
        yfRefLoc = Location.Rgn yfrid ∧
        yrid = frame.regionId ∧
        yfrid = frame.regionId ∧
        cfg.heap.lookup yrid = some region ∧
        region.objMap.lookup yoid = some obj ∧
        cfg' = { cfg with
          heap := cfg.heap.insert yrid { region with
            bridgeObjectId := yfoid,
            objMap := region.objMap.insert yoid (obj.insert yf.field (Reference.OId region.bridgeObjectId)) }
        })) := by
  unfold swap at h
  cases hframe : cfg.stackWithIndex.getLast? with
  | none => rw [hframe] at h; contradiction
  | some frame =>
    rw [hframe] at h
    dsimp at h
    refine ⟨frame, rfl, ?_⟩
    cases hyr : resolveV yf.root cfg with
    | none => rw [hyr] at h; contradiction
    | some yRef =>
      rw [hyr] at h
      dsimp at h
      refine ⟨yRef, rfl, ?_⟩
      cases hyrl : yRef.loc? cfg with
      | none => rw [hyrl] at h; contradiction
      | some yRefLoc =>
        rw [hyrl] at h
        dsimp at h
        refine ⟨yRefLoc, rfl, ?_⟩
        cases hyf : resolveFA yf cfg with
        | none => rw [hyf] at h; contradiction
        | some yfRef =>
          rw [hyf] at h
          dsimp at h
          refine ⟨yfRef, rfl, ?_⟩
          cases hyfl : yfRef.loc? cfg with
          | none => rw [hyfl] at h; contradiction
          | some yfRefLoc =>
            rw [hyfl] at h
            dsimp at h
            refine ⟨yfRefLoc, rfl, ?_⟩
            by_cases hxb : (x != frame.bridgeVar) = true
            · rw [if_pos hxb] at h
              rw [bne_iff_ne] at hxb
              cases hxr : frame.varMap.lookup x with
              | none => rw [hxr] at h; contradiction
              | some xRef =>
                rw [hxr] at h
                dsimp at h
                cases yRef with
                | RId yrid0 => dsimp at h; contradiction
                | OId yoid =>
                  dsimp at h
                  cases yRefLoc with
                  | Stk fid =>
                    dsimp at h
                    by_cases hfid : (fid == frame.index) = true
                    · rw [if_pos hfid] at h
                      rw [beq_iff_eq] at hfid
                      cases hobj : frame.objMap.lookup yoid with
                      | none => rw [hobj] at h; contradiction
                      | some obj =>
                        rw [hobj] at h
                        dsimp at h
                        rw [Option.some_inj] at h
                        left
                        subst hfid
                        exact ⟨yoid, xRef, obj, hxb, rfl, rfl, rfl, hobj, h.symm⟩
                    · rw [if_neg hfid] at h; contradiction
                  | Rgn rid =>
                    dsimp at h
                    by_cases hrid : (rid == frame.regionId) = true
                    · rw [if_pos hrid] at h
                      rw [beq_iff_eq] at hrid
                      cases hregion : cfg.heap.lookup rid with
                      | none => rw [hregion] at h; contradiction
                      | some region =>
                        rw [hregion] at h
                        dsimp at h
                        cases hobj : region.objMap.lookup yoid with
                        | none => rw [hobj] at h; contradiction
                        | some obj =>
                          rw [hobj] at h
                          dsimp at h
                          cases xRef with
                          | OId xoid =>
                            dsimp at h
                            cases hxrl : (Reference.OId xoid).loc? cfg with
                            | none => rw [hxrl] at h; dsimp at h; contradiction
                            | some xRefLoc =>
                              rw [hxrl] at h
                              dsimp at h
                              cases xRefLoc with
                              | Stk fid' => dsimp at h; contradiction
                              | Rgn xrid =>
                                dsimp at h
                                by_cases hcond : xrid == frame.regionId ∧ region.status == Status.Open
                                · rw [if_pos hcond] at h
                                  obtain ⟨hxridEq0, hstatusEq0'⟩ := hcond
                                  rw [beq_iff_eq] at hxridEq0
                                  have hstatusEq0 : region.status = Status.Open := by
                                    cases hs : region.status with
                                    | Open => rfl
                                    | Closed => rw [hs] at hstatusEq0'; contradiction
                                  rw [Option.some_inj] at h
                                  right; left
                                  exact ⟨yoid, rid, region, obj, xoid, xrid, hxb, rfl, rfl, hrid, hregion, hobj,
                                    rfl, hxrl, hxridEq0, hstatusEq0, h.symm⟩
                                · rw [if_neg hcond] at h; contradiction
                          | RId xrid0 =>
                            dsimp at h
                            by_cases hstatus : region.status == Status.Open
                            · rw [if_pos hstatus] at h
                              have hstatusEq : region.status = Status.Open := by
                                cases hs : region.status with
                                | Open => rfl
                                | Closed => rw [hs] at hstatus; contradiction
                              rw [Option.some_inj] at h
                              right; right; left
                              exact ⟨yoid, rid, region, obj, xrid0, hxb, rfl, rfl, hrid, hregion, hobj, rfl,
                                hstatusEq, h.symm⟩
                            · rw [if_neg hstatus] at h; contradiction
                    · rw [if_neg hrid] at h; contradiction
            · rw [if_neg hxb] at h
              rw [Bool.not_eq_true] at hxb
              have hxb' : x = frame.bridgeVar := by
                by_contra hne
                have : (x != frame.bridgeVar) = true := by
                  rw [bne_iff_ne]; exact hne
                rw [this] at hxb; contradiction
              cases yRef with
              | RId yrid0 => dsimp at h; contradiction
              | OId yoid =>
                cases yRefLoc with
                | Stk fid => dsimp at h; contradiction
                | Rgn yrid =>
                  cases yfRef with
                  | RId yfrid0 => dsimp at h; contradiction
                  | OId yfoid =>
                    cases yfRefLoc with
                    | Stk fid' => dsimp at h; contradiction
                    | Rgn yfrid =>
                      dsimp at h
                      by_cases hcond2 : yrid == frame.regionId ∧ yfrid == frame.regionId
                      · rw [if_pos hcond2] at h
                        obtain ⟨hyridEq, hyfridEq⟩ := hcond2
                        rw [beq_iff_eq] at hyridEq hyfridEq
                        cases hregion : cfg.heap.lookup yrid with
                        | none => rw [hregion] at h; contradiction
                        | some region =>
                          rw [hregion] at h
                          dsimp at h
                          cases hobj : region.objMap.lookup yoid with
                          | none => rw [hobj] at h; contradiction
                          | some obj =>
                            rw [hobj] at h
                            dsimp at h
                            rw [Option.some_inj] at h
                            right; right; right
                            exact ⟨yoid, yrid, yfoid, yfrid, region, obj, hxb', rfl, rfl, rfl, rfl,
                              hyridEq, hyfridEq, hregion, hobj, h.symm⟩
                      · rw [if_neg hcond2] at h; contradiction

-- Relates the `stackWithIndex.getLast?` frame used by `swap_cases` back to `cfg.stack`'s own
-- decomposition, mirroring fieldAsgn_corollary_stack_eq/VarAsgn.lean's stack_eq construction.
theorem swap_corollary_stack_eq {cfg : RuntimeConfig} {frame : FrameWithIndex}
    (hframe : cfg.stackWithIndex.getLast? = some frame) :
    cfg.stack = cfg.stack.dropLast ++ [frame.toFrame] ∧ frame.index = cfg.stack.dropLast.length := by
  cases hlast : cfg.stack.getLast? with
  | none =>
    exfalso
    have hnil : cfg.stack = [] := List.getLast?_eq_none_iff.mp hlast
    unfold RuntimeConfig.stackWithIndex at hframe
    rw [hnil] at hframe
    simp at hframe
  | some lastF =>
    have stack_eq : cfg.stack = cfg.stack.dropLast ++ [lastF] :=
      (List.dropLast_append_getLast? lastF hlast).symm
    have stackWithIndex_eq :
        cfg.stackWithIndex =
          cfg.stack.dropLast.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) ++
            [({ lastF with index := cfg.stack.dropLast.length } : FrameWithIndex)] := by
      unfold RuntimeConfig.stackWithIndex
      conv_lhs => rw [stack_eq]
      rw [List.mapIdx_concat]
    rw [stackWithIndex_eq, List.getLast?_concat, Option.some_inj] at hframe
    subst hframe
    exact ⟨stack_eq, rfl⟩

theorem swap_S1 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  S1 cfg' := by
  intro vcfg h
  have s1 := vcfg.s1
  obtain ⟨frame, hframe, yRef, hyr, yRefLoc, hyrl, yfRef, hyf, yfRefLoc, hyfl, hcase⟩ := swap_cases h
  unfold S1
  obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
  have s1' : (cfg.stack.dropLast.map (fun frame => frame.regionId) ++ [frame.regionId]).Nodup := by
    have := s1
    unfold S1 at this
    rw [stack_eq, List.map_append] at this
    exact this
  rcases hcase with
    ⟨yoid, xRef, obj, hxb, hyoid, hyrloc, hxr, hobj, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xoid, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hxrl, hxrid, hstatus, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hstatus, hcfg'⟩ |
    ⟨yoid, yrid, yfoid, yfrid, region, obj, hxb, hyoid, hyrloc, hyfoid, hyfrloc, hyrid, hyfrid, hregion, hobj, hcfg'⟩
  · subst hcfg'
    dsimp
    rw [List.map_append]
    exact s1'
  · subst hcfg'
    dsimp
    rw [List.map_append]
    exact s1'
  · subst hcfg'
    dsimp
    rw [List.map_append]
    exact s1'
  · subst hcfg'
    dsimp
    exact s1

-- Generic AList fact (no domain dependency): replacing the value at an already-present key
-- reorders `entries` but only *permutes* `.keys`, never changes the key set. Used at both
-- nesting levels in this file (frame.objMap/region.objMap insert at the already-present `yoid`,
-- and the analogous facts for varMap-level operations aren't needed since swap never allocates).
theorem swap_corollary_insert_keys_perm {α : Type*} {β : α → Type*} [DecidableEq α]
    {l : AList β} {k : α} {v : β k} (hk : k ∈ l.keys) :
    (l.insert k v).keys.Perm l.keys := by
  obtain ⟨v0, l1e, l2e, hnotmem, heq, hkerase⟩ := List.exists_of_kerase hk
  unfold AList.keys
  rw [AList.entries_insert, hkerase]
  conv_rhs => rw [heq]
  rw [List.keys_cons, List.keys_append, List.keys_append, List.keys_cons]
  exact List.perm_middle.symm

-- Generic AList fact: a successful `lookup` means the key is already present.
theorem swap_corollary_mem_keys_of_lookup {α : Type*} {β : α → Type*} [DecidableEq α]
    {l : AList β} {k : α} {v : β k} (hv : l.lookup k = some v) : k ∈ l.keys :=
  AList.mem_keys.mp (AList.lookup_isSome.mp (by rw [hv]; rfl))

-- The region-touching branches' `heap.insert` at an already-present key, where the newly-inserted
-- region's objMap key set is only known up to a `Perm` of the old region's (the region's objMap
-- genuinely changes, not just a scalar field) -- composes the outer heap-entries reorder with the
-- inner region-level permutation. Mirrors fieldAsgn_corollary_region_heap_objectIds_perm.
theorem swap_corollary_region_heap_objectIds_perm {cfg : RuntimeConfig} {rid : RegionId}
    {region newRegion : Region} (hregion : cfg.heap.lookup rid = some region)
    (hperm : newRegion.objMap.keys.Perm region.objMap.keys) :
    (Heap.objectIds (cfg.heap.insert rid newRegion)).Perm cfg.heap.objectIds := by
  obtain ⟨region2, l1e, l2e, hnotmem, heq, hkerase⟩ :=
    List.exists_of_kerase (swap_corollary_mem_keys_of_lookup hregion)
  have region2_eq : region2 = region :=
    List.NodupKeys.eq_of_mk_mem cfg.heap.nodupKeys
      (heq ▸ List.mem_append_right _ List.mem_cons_self) (AList.mem_lookup_iff.mp (by rw [hregion]; rfl))
  have cfg_eq : Heap.objectIds cfg.heap =
      List.flatten (l1e.map (fun e => e.2.objectIds)) ++
        (region.objectIds ++ List.flatten (l2e.map (fun e => e.2.objectIds))) := by
    unfold Heap.objectIds
    rw [heq, ← region2_eq, List.map_append, List.map_cons, List.flatten_append, List.flatten_cons]
  have cfg'_eq : Heap.objectIds (cfg.heap.insert rid newRegion) =
      newRegion.objectIds ++
        (List.flatten (l1e.map (fun e => e.2.objectIds)) ++ List.flatten (l2e.map (fun e => e.2.objectIds))) := by
    unfold Heap.objectIds
    rw [AList.entries_insert, hkerase, List.map_cons, List.flatten_cons, List.map_append, List.flatten_append]
  rw [cfg_eq, cfg'_eq]
  set LA := List.flatten (l1e.map (fun e => e.2.objectIds))
  set LB := List.flatten (l2e.map (fun e => e.2.objectIds))
  have swap_perm : (region.objectIds ++ (LA ++ LB)).Perm (LA ++ (region.objectIds ++ LB)) := by
    rw [← List.append_assoc, ← List.append_assoc]
    exact (List.perm_append_comm).append_right LB
  exact (hperm.append_right (LA ++ LB)).trans swap_perm

-- Generic fact used for the stack-mutation branches: `Stack.objectIds` distributes over `++ [f]`.
theorem swap_corollary_stack_objectIds_append (l : Stack) (f : Frame) :
    Stack.objectIds (l ++ [f]) = Stack.objectIds l ++ f.objectIds := by
  unfold Stack.objectIds
  rw [List.bind_eq_flatMap, List.bind_eq_flatMap, List.flatMap_id, List.flatMap_id,
    List.map_append, List.flatten_append]
  simp

theorem swap_L1 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  L1 cfg' := by
  intro vcfg h
  have l1 := vcfg.l1
  obtain ⟨frame, hframe, yRef, hyr, yRefLoc, hyrl, yfRef, hyf, yfRefLoc, hyfl, hcase⟩ := swap_cases h
  unfold L1
  rcases hcase with
    ⟨yoid, xRef, obj, hxb, hyoid, hyrloc, hxr, hobj, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xoid, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hxrl, hxrid, hstatus, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hstatus, hcfg'⟩ |
    ⟨yoid, yrid, yfoid, yfrid, region, obj, hxb, hyoid, hyrloc, hyfoid, hyfrloc, hyrid, hyfrid, hregion, hobj, hcfg'⟩
  · subst hcfg'
    obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
    have hoidmem : yoid ∈ frame.objMap.keys := swap_corollary_mem_keys_of_lookup hobj
    have frame_perm := swap_corollary_insert_keys_perm (l := frame.objMap) (v := obj.insert yf.field xRef) hoidmem
    unfold RuntimeConfig.objectIds
    dsimp
    rw [swap_corollary_stack_objectIds_append]
    have cfg_stack_eq : Stack.objectIds cfg.stack = Stack.objectIds cfg.stack.dropLast ++ frame.objMap.keys := by
      conv_lhs => rw [stack_eq]
      rw [swap_corollary_stack_objectIds_append]
      rfl
    have perm2 :=
      (List.Perm.append_left (Stack.objectIds cfg.stack.dropLast) frame_perm).append_right cfg.heap.objectIds
    rw [← cfg_stack_eq] at perm2
    exact l1.perm perm2.symm
  · subst hcfg'
    obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
    have hoidmem : yoid ∈ region.objMap.keys := swap_corollary_mem_keys_of_lookup hobj
    have region_perm := swap_corollary_insert_keys_perm (l := region.objMap) (v := obj.insert yf.field (Reference.OId xoid)) hoidmem
    have heap_perm := swap_corollary_region_heap_objectIds_perm
      (newRegion := { region with objMap := AList.insert yoid (obj.insert yf.field (Reference.OId xoid)) region.objMap })
      hregion region_perm
    unfold RuntimeConfig.objectIds
    dsimp
    have cfg'_stack_eq : Stack.objectIds
        (cfg.stack.dropLast ++ [({ frame with varMap := frame.varMap.insert x yfRef } : Frame)]) =
        Stack.objectIds cfg.stack := by
      rw [swap_corollary_stack_objectIds_append]
      conv_rhs => rw [stack_eq]
      rw [swap_corollary_stack_objectIds_append]
      rfl
    rw [cfg'_stack_eq]
    exact l1.perm (List.Perm.append_left cfg.stack.objectIds heap_perm).symm
  · subst hcfg'
    obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
    have hoidmem : yoid ∈ region.objMap.keys := swap_corollary_mem_keys_of_lookup hobj
    have region_perm := swap_corollary_insert_keys_perm (l := region.objMap) (v := obj.insert yf.field (Reference.RId xrid)) hoidmem
    have heap_perm := swap_corollary_region_heap_objectIds_perm
      (newRegion := { region with objMap := AList.insert yoid (obj.insert yf.field (Reference.RId xrid)) region.objMap })
      hregion region_perm
    unfold RuntimeConfig.objectIds
    dsimp
    have cfg'_stack_eq : Stack.objectIds
        (cfg.stack.dropLast ++ [({ frame with varMap := frame.varMap.insert x yfRef } : Frame)]) =
        Stack.objectIds cfg.stack := by
      rw [swap_corollary_stack_objectIds_append]
      conv_rhs => rw [stack_eq]
      rw [swap_corollary_stack_objectIds_append]
      rfl
    rw [cfg'_stack_eq]
    exact l1.perm (List.Perm.append_left cfg.stack.objectIds heap_perm).symm
  · subst hcfg'
    have hoidmem : yoid ∈ region.objMap.keys := swap_corollary_mem_keys_of_lookup hobj
    have region_perm := swap_corollary_insert_keys_perm
      (l := region.objMap) (v := obj.insert yf.field (Reference.OId region.bridgeObjectId)) hoidmem
    have heap_perm := swap_corollary_region_heap_objectIds_perm
      (newRegion := { region with
        bridgeObjectId := yfoid,
        objMap := AList.insert yoid (obj.insert yf.field (Reference.OId region.bridgeObjectId)) region.objMap })
      hregion region_perm
    unfold RuntimeConfig.objectIds
    dsimp
    exact l1.perm (List.Perm.append_left cfg.stack.objectIds heap_perm).symm

theorem swap_L2 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  L2 cfg' := by
  intro vcfg h
  have l2 := vcfg.l2
  obtain ⟨frame, hframe, yRef, hyr, yRefLoc, hyrl, yfRef, hyf, yfRefLoc, hyfl, hcase⟩ := swap_cases h
  unfold L2
  rcases hcase with
    ⟨yoid, xRef, obj, hxb, hyoid, hyrloc, hxr, hobj, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xoid, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hxrl, hxrid, hstatus, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hstatus, hcfg'⟩ |
    ⟨yoid, yrid, yfoid, yfrid, region, obj, hxb, hyoid, hyrloc, hyfoid, hyfrloc, hyrid, hyfrid, hregion, hobj, hcfg'⟩
  · subst hcfg'
    obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
    have frame_mem : frame.toFrame ∈ cfg.stack :=
      stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self _)
    dsimp
    intro frame'' hmem
    rw [List.mem_append, List.mem_singleton] at hmem
    cases hmem with
    | inl hdrop => exact l2 frame'' (List.mem_of_mem_dropLast hdrop)
    | inr heqframe => subst heqframe; exact l2 frame.toFrame frame_mem
  · subst hcfg'
    obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
    have frame_mem : frame.toFrame ∈ cfg.stack :=
      stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self _)
    dsimp
    intro frame'' hmem
    rw [List.mem_append, List.mem_singleton] at hmem
    obtain ⟨region0, hlookup0, hopen0⟩ :
        ∃ region0, cfg.heap.lookup frame''.regionId = some region0 ∧ region0.status = Status.Open := by
      cases hmem with
      | inl hdrop => exact l2 frame'' (List.mem_of_mem_dropLast hdrop)
      | inr heqframe => subst heqframe; exact l2 frame.toFrame frame_mem
    by_cases heq : frame''.regionId = rid
    · rw [heq] at hlookup0
      rw [hregion, Option.some_inj] at hlookup0
      refine ⟨{ region with
          objMap := AList.insert yoid (AList.insert yf.field (Reference.OId xoid) obj) region.objMap }, ?_, ?_⟩
      · rw [heq, AList.lookup_insert]
      · dsimp; exact hstatus
    · refine ⟨region0, ?_, hopen0⟩
      rw [AList.lookup_insert_ne heq]
      exact hlookup0
  · subst hcfg'
    obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
    have frame_mem : frame.toFrame ∈ cfg.stack :=
      stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self _)
    dsimp
    intro frame'' hmem
    rw [List.mem_append, List.mem_singleton] at hmem
    obtain ⟨region0, hlookup0, hopen0⟩ :
        ∃ region0, cfg.heap.lookup frame''.regionId = some region0 ∧ region0.status = Status.Open := by
      cases hmem with
      | inl hdrop => exact l2 frame'' (List.mem_of_mem_dropLast hdrop)
      | inr heqframe => subst heqframe; exact l2 frame.toFrame frame_mem
    by_cases heq : frame''.regionId = rid
    · rw [heq] at hlookup0
      rw [hregion, Option.some_inj] at hlookup0
      refine ⟨{ region with
          objMap := AList.insert yoid (AList.insert yf.field (Reference.RId xrid) obj) region.objMap }, ?_, ?_⟩
      · rw [heq, AList.lookup_insert]
      · dsimp; exact hstatus
    · refine ⟨region0, ?_, hopen0⟩
      rw [AList.lookup_insert_ne heq]
      exact hlookup0
  · subst hcfg'
    dsimp
    intro frame'' hmem
    obtain ⟨region0, hlookup0, hopen0⟩ := l2 frame'' hmem
    by_cases heq : frame''.regionId = yrid
    · rw [heq] at hlookup0
      rw [hregion, Option.some_inj] at hlookup0
      refine ⟨{ region with
          bridgeObjectId := yfoid,
          objMap := AList.insert yoid (AList.insert yf.field (Reference.OId region.bridgeObjectId) obj) region.objMap
        }, ?_, ?_⟩
      · rw [heq, AList.lookup_insert]
      · dsimp; rw [hlookup0]; exact hopen0
    · refine ⟨region0, ?_, hopen0⟩
      rw [AList.lookup_insert_ne heq]
      exact hlookup0

theorem swap_H1 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  H1 cfg' := by
  intro vcfg h
  have h1 := vcfg.h1
  obtain ⟨frame, hframe, yRef, hyr, yRefLoc, hyrl, yfRef, hyf, yfRefLoc, hyfl, hcase⟩ := swap_cases h
  unfold H1
  rcases hcase with
    ⟨yoid, xRef, obj, hxb, hyoid, hyrloc, hxr, hobj, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xoid, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hxrl, hxrid, hstatus, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hstatus, hcfg'⟩ |
    ⟨yoid, yrid, yfoid, yfrid, region, obj, hxb, hyoid, hyrloc, hyfoid, hyfrloc, hyrid, hyfrid, hregion, hobj, hcfg'⟩
  · subst hcfg'
    dsimp
    exact h1
  · subst hcfg'
    dsimp
    have region_mem : region ∈ cfg.heap.regions := by
      unfold Heap.regions
      exact List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hregion)
    intro region0 hregion0
    unfold Heap.regions at hregion0
    rw [AList.entries_insert, List.map_cons, List.mem_cons] at hregion0
    cases hregion0 with
    | inl heqregion =>
      subst heqregion
      dsimp
      exact (AList.mem_insert _).mpr (Or.inr (h1 region region_mem))
    | inr hkeraseregion =>
      apply h1
      unfold Heap.regions
      exact (List.Sublist.map _ (List.kerase_sublist rid cfg.heap.entries)).mem hkeraseregion
  · subst hcfg'
    dsimp
    have region_mem : region ∈ cfg.heap.regions := by
      unfold Heap.regions
      exact List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hregion)
    intro region0 hregion0
    unfold Heap.regions at hregion0
    rw [AList.entries_insert, List.map_cons, List.mem_cons] at hregion0
    cases hregion0 with
    | inl heqregion =>
      subst heqregion
      dsimp
      exact (AList.mem_insert _).mpr (Or.inr (h1 region region_mem))
    | inr hkeraseregion =>
      apply h1
      unfold Heap.regions
      exact (List.Sublist.map _ (List.kerase_sublist rid cfg.heap.entries)).mem hkeraseregion
  · subst hcfg'
    dsimp
    have region_mem : region ∈ cfg.heap.regions := by
      unfold Heap.regions
      exact List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hregion)
    have hyfrid_eq : yrid = yfrid := hyrid.trans hyfrid.symm
    have hyfoid_loc : (Reference.OId yfoid).loc? cfg = some (Location.Rgn yrid) := by
      rw [← hyfoid, hyfl, hyfrloc, hyfrid_eq]
    obtain ⟨region', hregion', hyfoid_mem'⟩ := (oid_loc_rgn_iff_in_heap vcfg).mp hyfoid_loc
    have region'_eq : region' = region := by rw [hregion] at hregion'; exact Option.some_inj.mp hregion'.symm
    have hyfoid_mem : yfoid ∈ region.objMap := region'_eq ▸ hyfoid_mem'
    intro region0 hregion0
    unfold Heap.regions at hregion0
    rw [AList.entries_insert, List.map_cons, List.mem_cons] at hregion0
    cases hregion0 with
    | inl heqregion =>
      subst heqregion
      dsimp
      exact (AList.mem_insert _).mpr (Or.inr hyfoid_mem)
    | inr hkeraseregion =>
      apply h1
      unfold Heap.regions
      exact (List.Sublist.map _ (List.kerase_sublist yrid cfg.heap.entries)).mem hkeraseregion

-- Two elements of `cfg.stackWithIndex` with the same `.index` are the same element -- `.index` is
-- assigned to be the element's own position by `mapIdx`, so equal indices means equal positions.
theorem swap_corollary_stackWithIndex_index_inj {cfg : RuntimeConfig} {f1 f2 : FrameWithIndex}
    (h1 : f1 ∈ cfg.stackWithIndex) (h2 : f2 ∈ cfg.stackWithIndex) (heq : f1.index = f2.index) :
    f1 = f2 := by
  unfold RuntimeConfig.stackWithIndex at h1 h2
  obtain ⟨n1, hn1, e1⟩ := List.mem_mapIdx.mp h1
  obtain ⟨n2, hn2, e2⟩ := List.mem_mapIdx.mp h2
  have hi1 : f1.index = n1 := by rw [← e1]
  have hi2 : f2.index = n2 := by rw [← e2]
  have hn : n1 = n2 := by rw [hi1, hi2] at heq; exact heq
  subst hn
  rw [← e1, ← e2]

-- resolveFA's own `.find? (index==fid)` step recovers exactly the frame already known to have
-- that index, via the index-injectivity fact above plus the generic find?-uniqueness lemma.
theorem swap_corollary_stackWithIndex_find_eq {cfg : RuntimeConfig} {frame : FrameWithIndex}
    (hmem : frame ∈ cfg.stackWithIndex) :
    cfg.stackWithIndex.find? (fun f => f.index == frame.index) = some frame := by
  apply List.find?_eq_some_of_unique hmem (by simp)
  intro f' hf'_mem hf'_pred
  rw [beq_iff_eq] at hf'_pred
  exact swap_corollary_stackWithIndex_index_inj hf'_mem hmem hf'_pred

-- Traces resolveFA's own computation to show it agrees with the already-known
-- frame.objMap.lookup yoid = some obj (the SWAP-STACK case's own derivation, independent of
-- resolveFA's internal one) -- establishing that the field being overwritten by the swap held
-- exactly `yfRef` beforehand, i.e. this genuinely IS an exchange of two live values, not merely an
-- overwrite of an unknown old one.
theorem swap_corollary_stack_field_eq_yfRef {cfg : RuntimeConfig} {frame : FrameWithIndex} {yoid : ObjectId}
    {obj : Object} {yf : FieldAccess} {yfRef : Reference}
    (hframe_mem : frame ∈ cfg.stackWithIndex)
    (hyr : resolveV yf.root cfg = some (Reference.OId yoid))
    (hyrl : (Reference.OId yoid).loc? cfg = some (Location.Stk frame.index))
    (hobj : frame.objMap.lookup yoid = some obj)
    (hyf : resolveFA yf cfg = some yfRef) :
    obj.lookup yf.field = some yfRef := by
  unfold resolveFA at hyf
  rw [hyr] at hyf
  dsimp at hyf
  rw [hyrl] at hyf
  dsimp at hyf
  rw [swap_corollary_stackWithIndex_find_eq hframe_mem] at hyf
  dsimp at hyf
  rw [hobj] at hyf
  dsimp at hyf
  exact hyf

-- Region-side analogue: resolveFA's internal heap/region lookups are literally the same function
-- calls as the ones already performed by the region-branch cases, so no uniqueness argument is
-- needed here (unlike the stack case's `.find?`).
theorem swap_corollary_region_field_eq_yfRef {cfg : RuntimeConfig} {yoid : ObjectId} {rid : RegionId}
    {region : Region} {obj : Object} {yf : FieldAccess} {yfRef : Reference}
    (hyr : resolveV yf.root cfg = some (Reference.OId yoid))
    (hyrl : (Reference.OId yoid).loc? cfg = some (Location.Rgn rid))
    (hregion : cfg.heap.lookup rid = some region)
    (hobj : region.objMap.lookup yoid = some obj)
    (hyf : resolveFA yf cfg = some yfRef) :
    obj.lookup yf.field = some yfRef := by
  unfold resolveFA at hyf
  rw [hyr] at hyf
  dsimp at hyf
  rw [hyrl] at hyf
  dsimp at hyf
  rw [hregion] at hyf
  dsimp at hyf
  rw [hobj] at hyf
  dsimp at hyf
  exact hyf

-- Generic AList fact (Reference-valued, α-indexed): membership after inserting at a key is either
-- the newly-written value or a pre-existing one. Covers both VarMap and Object (`Object := VarMap`).
theorem swap_corollary_alist_insert_refs_mem {α : Type*} [DecidableEq α] {l : AList (fun _ : α => Reference)}
    {k : α} {v r : Reference} (hr : r ∈ (l.insert k v).entries.map (·.2)) :
    r = v ∨ r ∈ l.entries.map (·.2) := by
  by_cases hk : k ∈ l
  · obtain ⟨v0, l1e, l2e, hnotmem, heq, hkerase⟩ := List.exists_of_kerase (AList.mem_keys.mp hk)
    rw [AList.entries_insert, hkerase, List.map_cons, List.mem_cons] at hr
    rw [heq, List.map_append, List.map_cons, List.mem_append, List.mem_cons]
    dsimp only at hr ⊢
    rw [List.map_append, List.mem_append] at hr
    tauto
  · rw [AList.entries_insert_of_notMem hk, List.map_cons, List.mem_cons] at hr
    dsimp only at hr
    tauto

-- Once an object is already stored at some key of an ObjMap, its own refs already contribute to
-- the ObjMap-level bind-refs.
theorem swap_corollary_objMap_bind_refs_mem_of_lookup {m : ObjMap} {oid : ObjectId} {obj : Object}
    {r : Reference} (hobj : m.lookup oid = some obj) (hr : r ∈ Object.refs obj) :
    r ∈ (m.entries.map (·.2) >>= Object.refs) := by
  have hmem : (⟨oid, obj⟩ : Sigma (fun _ : ObjectId => Object)) ∈ m.entries :=
    AList.mem_lookup_iff.mp (by rw [hobj]; rfl)
  rw [List.bind_eq_flatMap, List.mem_flatMap]
  exact ⟨obj, List.mem_map_of_mem (f := (·.2)) hmem, hr⟩

-- Membership after inserting at an ObjMap key: either from the newly-written object, or already present.
theorem swap_corollary_objMap_insert_bind_refs_mem {m : ObjMap} {oid : ObjectId} {v : Object} {r : Reference}
    (hr : r ∈ ((m.insert oid v).entries.map (·.2) >>= Object.refs)) :
    r ∈ Object.refs v ∨ r ∈ (m.entries.map (·.2) >>= Object.refs) := by
  by_cases hoid : oid ∈ m
  · obtain ⟨v0, l1e, l2e, hnotmem, heq, hkerase⟩ := List.exists_of_kerase (AList.mem_keys.mp hoid)
    rw [AList.entries_insert, hkerase, List.map_cons, List.bind_eq_flatMap, List.flatMap_cons,
      ← List.bind_eq_flatMap, List.mem_append, List.map_append, List.bind_eq_flatMap, List.flatMap_append,
      ← List.bind_eq_flatMap, List.mem_append] at hr
    rw [heq, List.map_append, List.map_cons, List.bind_eq_flatMap, List.flatMap_append, List.flatMap_cons,
      ← List.bind_eq_flatMap, ← List.bind_eq_flatMap, List.mem_append, List.mem_append]
    tauto
  · rw [AList.entries_insert_of_notMem hoid, List.map_cons, List.bind_eq_flatMap, List.flatMap_cons,
      ← List.bind_eq_flatMap, List.mem_append] at hr
    tauto

-- Once a region is already stored at some key of a heap, its own refs already contribute to Heap.refs.
theorem swap_corollary_heap_refs_mem_of_lookup {cfg : RuntimeConfig} {rid : RegionId} {region : Region}
    {r : Reference} (hregion : cfg.heap.lookup rid = some region) (hr : r ∈ Region.refs region) :
    r ∈ Heap.refs cfg.heap := by
  have hmem : (⟨rid, region⟩ : Sigma (fun _ : RegionId => Region)) ∈ cfg.heap.entries :=
    AList.mem_lookup_iff.mp (by rw [hregion]; rfl)
  unfold Heap.refs
  rw [List.bind_eq_flatMap, List.mem_flatMap]
  exact ⟨region, List.mem_map_of_mem (f := (·.2)) hmem, hr⟩

-- Membership after inserting at a heap key: either from the newly-written region, or already present.
theorem swap_corollary_heap_insert_refs_mem {cfg : RuntimeConfig} {rid : RegionId} {newRegion : Region}
    {r : Reference} (hrid : rid ∈ cfg.heap.keys) (hr : r ∈ Heap.refs (cfg.heap.insert rid newRegion)) :
    r ∈ Region.refs newRegion ∨ r ∈ Heap.refs cfg.heap := by
  unfold Heap.refs at hr ⊢
  obtain ⟨v0, l1e, l2e, hnotmem, heq, hkerase⟩ := List.exists_of_kerase hrid
  rw [AList.entries_insert, hkerase, List.map_cons, List.bind_eq_flatMap, List.flatMap_cons,
    ← List.bind_eq_flatMap, List.mem_append, List.map_append, List.bind_eq_flatMap, List.flatMap_append,
    ← List.bind_eq_flatMap, List.mem_append] at hr
  rw [heq, List.map_append, List.map_cons, List.bind_eq_flatMap, List.flatMap_append, List.flatMap_cons,
    ← List.bind_eq_flatMap, ← List.bind_eq_flatMap, List.mem_append, List.mem_append]
  tauto

-- Heap key set is unchanged by inserting at an already-present key.
theorem swap_corollary_heap_insert_keys_mem {cfg : RuntimeConfig} {rid : RegionId} {newRegion : Region}
    (hridmem : rid ∈ cfg.heap.keys) (rid' : RegionId) :
    rid' ∈ (cfg.heap.insert rid newRegion).keys ↔ rid' ∈ cfg.heap.keys := by
  rw [← AList.mem_keys, AList.mem_insert, AList.mem_keys]
  exact or_iff_right_of_imp (fun heq => heq ▸ hridmem)

-- Generic fact used for the stack-mutation branches: `Stack.refs` distributes over `++ [f]`.
theorem swap_corollary_stack_refs_append (l : Stack) (f : Frame) :
    Stack.refs (l ++ [f]) = Stack.refs l ++ f.refs := by
  unfold Stack.refs
  rw [List.bind_eq_flatMap, List.bind_eq_flatMap, List.flatMap_id, List.flatMap_id,
    List.map_append, List.flatten_append]
  simp

-- A reference already present in some frame's own refs is already present in the whole stack's refs.
theorem swap_corollary_frame_refs_mem_stack {stack : Stack} {frame : Frame} {r : Reference}
    (hmem : frame ∈ stack) (hr : r ∈ Frame.refs frame) : r ∈ Stack.refs stack := by
  unfold Stack.refs
  rw [List.bind_eq_flatMap, List.flatMap_id, List.mem_flatten]
  exact ⟨Frame.refs frame, List.mem_map_of_mem hmem, hr⟩

-- Generic AList fact (Reference-valued): replacing the value at an already-present key changes
-- the count of any target `t` by exactly (v_new==t?1:0) - (v_old==t?1:0), captured additively (to
-- avoid Nat subtraction) as an equation relating the two counts via the two `==` conditions. This
-- is what makes `swap` provably an *exchange* rather than a plain overwrite: applying this once
-- for each of the two slots being swapped, the two `if`-terms cancel out exactly when combined.
theorem swap_corollary_alist_insert_count_eq {α : Type*} [DecidableEq α] {l : AList (fun _ : α => Reference)}
    {k : α} {v_old v_new t : Reference} (hlookup : l.lookup k = some v_old) :
    ((l.insert k v_new).entries.map (·.2)).count t + (if (v_old == t) = true then 1 else 0) =
    (l.entries.map (·.2)).count t + (if (v_new == t) = true then 1 else 0) := by
  obtain ⟨v0, l1e, l2e, hnotmem, heq, hkerase⟩ := List.exists_of_kerase (swap_corollary_mem_keys_of_lookup hlookup)
  have v0_eq : v0 = v_old := by
    have hmem_v0 : (⟨k, v0⟩ : Sigma (fun _ : α => Reference)) ∈ l.entries :=
      heq ▸ List.mem_append_right _ List.mem_cons_self
    have hmem_vold : (⟨k, v_old⟩ : Sigma (fun _ : α => Reference)) ∈ l.entries :=
      AList.mem_lookup_iff.mp (by rw [hlookup]; rfl)
    exact List.NodupKeys.eq_of_mk_mem (β := fun _ : α => Reference) l.nodupKeys hmem_v0 hmem_vold
  have hnew : (l.insert k v_new).entries.map (·.2) = v_new :: (l1e ++ l2e).map (·.2) := by
    rw [AList.entries_insert, hkerase, List.map_cons]
  have hold : l.entries.map (·.2) = l1e.map (·.2) ++ v_old :: l2e.map (·.2) := by
    rw [heq, v0_eq, List.map_append, List.map_cons]
  rw [hnew, hold, List.count_cons, List.map_append, List.count_append, List.count_append, List.count_cons]
  omega

-- Container-level analogue, one level up: replacing the value at an already-present ObjMap key
-- changes the whole bind-refs count by exactly the delta of the object's own count -- a genuine
-- identity for *any* replacement value (not just ones related to the old one), since both sides
-- reduce to "other objects' count + old/new object's own count".
theorem swap_corollary_objMap_insert_bind_count_eq {m : ObjMap} {oid : ObjectId} {obj v : Object} {t : Reference}
    (hobj : m.lookup oid = some obj) :
    ((m.insert oid v).entries.map (·.2) >>= Object.refs).count t + (Object.refs obj).count t =
    (m.entries.map (·.2) >>= Object.refs).count t + (Object.refs v).count t := by
  obtain ⟨v0, l1e, l2e, hnotmem, heq, hkerase⟩ := List.exists_of_kerase (swap_corollary_mem_keys_of_lookup hobj)
  have v0_eq : v0 = obj := by
    have hmem_v0 : (⟨oid, v0⟩ : Sigma (fun _ : ObjectId => Object)) ∈ m.entries :=
      heq ▸ List.mem_append_right _ List.mem_cons_self
    have hmem_obj : (⟨oid, obj⟩ : Sigma (fun _ : ObjectId => Object)) ∈ m.entries :=
      AList.mem_lookup_iff.mp (by rw [hobj]; rfl)
    exact List.NodupKeys.eq_of_mk_mem (β := fun _ : ObjectId => Object) m.nodupKeys hmem_v0 hmem_obj
  have hnewbind : (m.insert oid v).entries.map (·.2) >>= Object.refs =
      Object.refs v ++ ((l1e ++ l2e).map (·.2) >>= Object.refs) := by
    rw [AList.entries_insert, hkerase, List.map_cons, List.bind_eq_flatMap, List.flatMap_cons,
      ← List.bind_eq_flatMap]
  have holdbind : m.entries.map (·.2) >>= Object.refs =
      (l1e.map (·.2) >>= Object.refs) ++ (Object.refs obj ++ (l2e.map (·.2) >>= Object.refs)) := by
    rw [heq, v0_eq, List.map_append, List.map_cons, List.bind_eq_flatMap, List.flatMap_append,
      List.flatMap_cons, ← List.bind_eq_flatMap, ← List.bind_eq_flatMap]
  have splitbind : ((l1e ++ l2e).map (·.2) >>= Object.refs).count t =
      (l1e.map (·.2) >>= Object.refs).count t + (l2e.map (·.2) >>= Object.refs).count t := by
    rw [List.map_append, List.bind_eq_flatMap, List.flatMap_append, ← List.bind_eq_flatMap,
      ← List.bind_eq_flatMap, List.count_append]
  rw [hnewbind, holdbind, List.count_append, List.count_append, List.count_append]
  omega

-- Heap-level analogue of the above (Heap of Regions instead of ObjMap of Objects).
theorem swap_corollary_heap_insert_bind_count_eq {cfg : RuntimeConfig} {rid : RegionId}
    {region newRegion : Region} {t : Reference} (hregion : cfg.heap.lookup rid = some region) :
    (Heap.refs (cfg.heap.insert rid newRegion)).count t + (Region.refs region).count t =
    (Heap.refs cfg.heap).count t + (Region.refs newRegion).count t := by
  obtain ⟨v0, l1e, l2e, hnotmem, heq, hkerase⟩ :=
    List.exists_of_kerase (swap_corollary_mem_keys_of_lookup hregion)
  have v0_eq : v0 = region := by
    have hmem_v0 : (⟨rid, v0⟩ : Sigma (fun _ : RegionId => Region)) ∈ cfg.heap.entries :=
      heq ▸ List.mem_append_right _ List.mem_cons_self
    have hmem_region : (⟨rid, region⟩ : Sigma (fun _ : RegionId => Region)) ∈ cfg.heap.entries :=
      AList.mem_lookup_iff.mp (by rw [hregion]; rfl)
    exact List.NodupKeys.eq_of_mk_mem (β := fun _ : RegionId => Region) cfg.heap.nodupKeys hmem_v0 hmem_region
  unfold Heap.refs
  have hnewbind : (cfg.heap.insert rid newRegion).entries.map (·.2) >>= Region.refs =
      Region.refs newRegion ++ ((l1e ++ l2e).map (·.2) >>= Region.refs) := by
    rw [AList.entries_insert, hkerase, List.map_cons, List.bind_eq_flatMap, List.flatMap_cons,
      ← List.bind_eq_flatMap]
  have holdbind : cfg.heap.entries.map (·.2) >>= Region.refs =
      (l1e.map (·.2) >>= Region.refs) ++ (Region.refs region ++ (l2e.map (·.2) >>= Region.refs)) := by
    rw [heq, v0_eq, List.map_append, List.map_cons, List.bind_eq_flatMap, List.flatMap_append,
      List.flatMap_cons, ← List.bind_eq_flatMap, ← List.bind_eq_flatMap]
  have splitbind : ((l1e ++ l2e).map (·.2) >>= Region.refs).count t =
      (l1e.map (·.2) >>= Region.refs).count t + (l2e.map (·.2) >>= Region.refs).count t := by
    rw [List.map_append, List.bind_eq_flatMap, List.flatMap_append, ← List.bind_eq_flatMap,
      ← List.bind_eq_flatMap, List.count_append]
  rw [hnewbind, holdbind, List.count_append, List.count_append, List.count_append]
  omega

theorem swap_H2 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  H2 cfg' := by
  sorry

theorem swap_H3 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  H3 cfg' := by
  sorry

theorem swap_S2 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  S2 cfg' := by
  sorry

theorem swap_S3 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  S3 cfg' := by
  sorry

theorem swap_HS1 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  HS1 cfg' := by
  intro vcfg h
  have hs1 := vcfg.hs1
  have h1 := vcfg.h1
  obtain ⟨frame, hframe, yRef, hyr, yRefLoc, hyrl, yfRef, hyf, yfRefLoc, hyfl, hcase⟩ := swap_cases h
  have frame_mem : frame ∈ cfg.stackWithIndex := List.mem_of_getLast? hframe
  unfold HS1
  rcases hcase with
    ⟨yoid, xRef, obj, hxb, hyoid, hyrloc, hxr, hobj, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xoid, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hxrl, hxrid, hstatus, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hstatus, hcfg'⟩ |
    ⟨yoid, yrid, yfoid, yfrid, region, obj, hxb, hyoid, hyrloc, hyfoid, hyfrloc, hyrid, hyfrid, hregion, hobj, hcfg'⟩
  · -- SWAP-STACK
    subst hcfg'
    have hfield : obj.lookup yf.field = some yfRef :=
      swap_corollary_stack_field_eq_yfRef frame_mem (hyoid ▸ hyr) (hyoid ▸ hyrloc ▸ hyrl) hobj hyf
    obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
    have frame_toFrame_mem : frame.toFrame ∈ cfg.stack :=
      stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self _)
    have hxRef_mem : xRef ∈ cfg.refs := List.mem_append_left _
      (swap_corollary_frame_refs_mem_stack frame_toFrame_mem
        (List.mem_append_right _ (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hxr))))
    have hyfRef_mem : yfRef ∈ cfg.refs := List.mem_append_left _
      (swap_corollary_frame_refs_mem_stack frame_toFrame_mem
        (List.mem_append_left _ (swap_corollary_objMap_bind_refs_mem_of_lookup hobj
          (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hfield)))))
    have hdrop_refs : ∀ r, r ∈ Stack.refs cfg.stack.dropLast → r ∈ cfg.refs := by
      intro r hr
      apply List.mem_append_left
      rw [stack_eq, swap_corollary_stack_refs_append]
      exact List.mem_append_left _ hr
    have hframe_refs : ∀ r, r ∈ Frame.refs frame.toFrame → r ∈ cfg.refs := by
      intro r hr
      apply List.mem_append_left
      rw [stack_eq, swap_corollary_stack_refs_append]
      exact List.mem_append_right _ hr
    have hstack_split : Stack.objectIds cfg.stack = Stack.objectIds cfg.stack.dropLast ++ frame.objMap.keys := by
      conv_lhs => rw [stack_eq]
      rw [swap_corollary_stack_objectIds_append]
      rfl
    set newFrame : Frame := { frame with
        varMap := frame.varMap.insert x yfRef,
        objMap := frame.objMap.insert yoid (obj.insert yf.field xRef) } with newFrame_def
    have hobjIds_of_old : ∀ oid0, oid0 ∈ cfg.objectIds → oid0 ∈
        RuntimeConfig.objectIds { stack := cfg.stack.dropLast ++ [newFrame], heap := cfg.heap } := by
      intro oid0 hoid0
      unfold RuntimeConfig.objectIds at hoid0 ⊢
      dsimp
      rw [hstack_split, List.mem_append, List.mem_append] at hoid0
      rw [swap_corollary_stack_objectIds_append, List.mem_append, List.mem_append]
      rcases hoid0 with (hoid0 | hoid0) | hoid0
      · exact Or.inl (Or.inl hoid0)
      · left; right
        unfold Frame.objectIds
        show oid0 ∈ AList.keys (frame.objMap.insert yoid (obj.insert yf.field xRef))
        rw [← AList.mem_keys, AList.mem_insert]
        exact Or.inr (AList.mem_keys.mpr hoid0)
      · exact Or.inr hoid0
    intro oid0 hr
    unfold RuntimeConfig.refs at hr
    dsimp at hr
    rw [swap_corollary_stack_refs_append, List.mem_append, List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · exact hobjIds_of_old oid0 (hs1 oid0 (hdrop_refs _ hr))
    · unfold Frame.refs at hr
      dsimp at hr
      rw [List.mem_append] at hr
      rcases hr with hr | hr
      · rcases swap_corollary_objMap_insert_bind_refs_mem hr with hr' | hr'
        · rcases swap_corollary_alist_insert_refs_mem hr' with hr'' | hr''
          · exact hobjIds_of_old oid0 (hs1 oid0 (hr'' ▸ hxRef_mem))
          · exact hobjIds_of_old oid0 (hs1 oid0 (hframe_refs _ (List.mem_append_left _
              (swap_corollary_objMap_bind_refs_mem_of_lookup hobj hr''))))
        · exact hobjIds_of_old oid0 (hs1 oid0 (hframe_refs _ (List.mem_append_left _ hr')))
      · rcases swap_corollary_alist_insert_refs_mem hr with hr' | hr'
        · exact hobjIds_of_old oid0 (hs1 oid0 (hr' ▸ hyfRef_mem))
        · exact hobjIds_of_old oid0 (hs1 oid0 (hframe_refs _ (List.mem_append_right _ hr')))
    · exact hobjIds_of_old oid0 (hs1 oid0 (List.mem_append_right _ hr))
  · -- SWAP-REGION-OBJECT
    subst hcfg'
    have hfield : obj.lookup yf.field = some yfRef :=
      swap_corollary_region_field_eq_yfRef (hyoid ▸ hyr) (hyoid ▸ hyrloc ▸ hyrl) hregion hobj hyf
    obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
    have frame_toFrame_mem : frame.toFrame ∈ cfg.stack :=
      stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self _)
    have hxoidRef_mem : Reference.OId xoid ∈ cfg.refs := List.mem_append_left _
      (swap_corollary_frame_refs_mem_stack frame_toFrame_mem
        (List.mem_append_right _ (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hxr))))
    have hyfRef_mem : yfRef ∈ cfg.refs := List.mem_append_right _
      (swap_corollary_heap_refs_mem_of_lookup hregion
        (swap_corollary_objMap_bind_refs_mem_of_lookup hobj
          (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hfield))))
    have hdrop_refs : ∀ r, r ∈ Stack.refs cfg.stack.dropLast → r ∈ cfg.refs := by
      intro r hr
      apply List.mem_append_left
      rw [stack_eq, swap_corollary_stack_refs_append]
      exact List.mem_append_left _ hr
    have hframe_refs : ∀ r, r ∈ Frame.refs frame.toFrame → r ∈ cfg.refs := by
      intro r hr
      apply List.mem_append_left
      rw [stack_eq, swap_corollary_stack_refs_append]
      exact List.mem_append_right _ hr
    set newFrame : Frame := { frame with varMap := frame.varMap.insert x yfRef } with newFrame_def
    set newRegion : Region := { region with
        objMap := AList.insert yoid (obj.insert yf.field (Reference.OId xoid)) region.objMap } with newRegion_def
    have region_perm := swap_corollary_insert_keys_perm (l := region.objMap)
      (v := obj.insert yf.field (Reference.OId xoid)) (swap_corollary_mem_keys_of_lookup hobj)
    have heap_perm := swap_corollary_region_heap_objectIds_perm (newRegion := newRegion) hregion region_perm
    have hstack_eq : Stack.objectIds (cfg.stack.dropLast ++ [newFrame]) = Stack.objectIds cfg.stack := by
      rw [swap_corollary_stack_objectIds_append]
      conv_rhs => rw [stack_eq]
      rw [swap_corollary_stack_objectIds_append]
      rfl
    have hobjIds_of_old : ∀ oid0, oid0 ∈ cfg.objectIds → oid0 ∈
        RuntimeConfig.objectIds { stack := cfg.stack.dropLast ++ [newFrame], heap := cfg.heap.insert rid newRegion } := by
      intro oid0 hoid0
      unfold RuntimeConfig.objectIds at hoid0 ⊢
      dsimp
      rw [hstack_eq]
      rw [List.mem_append] at hoid0 ⊢
      rcases hoid0 with hoid0 | hoid0
      · exact Or.inl hoid0
      · exact Or.inr (heap_perm.mem_iff.mpr hoid0)
    intro oid0 hr
    unfold RuntimeConfig.refs at hr
    dsimp at hr
    rw [swap_corollary_stack_refs_append, List.mem_append, List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · exact hobjIds_of_old oid0 (hs1 oid0 (hdrop_refs _ hr))
    · unfold Frame.refs at hr
      dsimp at hr
      rw [List.mem_append] at hr
      rcases hr with hr | hr
      · exact hobjIds_of_old oid0 (hs1 oid0 (hframe_refs _ (List.mem_append_left _ hr)))
      · rcases swap_corollary_alist_insert_refs_mem hr with hr' | hr'
        · exact hobjIds_of_old oid0 (hs1 oid0 (hr' ▸ hyfRef_mem))
        · exact hobjIds_of_old oid0 (hs1 oid0 (hframe_refs _ (List.mem_append_right _ hr')))
    · rcases swap_corollary_heap_insert_refs_mem (swap_corollary_mem_keys_of_lookup hregion) hr with hr' | hr'
      · unfold Region.refs at hr'
        dsimp at hr'
        rcases swap_corollary_objMap_insert_bind_refs_mem hr' with hr'' | hr''
        · rcases swap_corollary_alist_insert_refs_mem hr'' with hr''' | hr'''
          · exact hobjIds_of_old oid0 (hs1 oid0 (hr''' ▸ hxoidRef_mem))
          · exact hobjIds_of_old oid0 (hs1 oid0 (List.mem_append_right _
              (swap_corollary_heap_refs_mem_of_lookup hregion
                (swap_corollary_objMap_bind_refs_mem_of_lookup hobj hr'''))))
        · exact hobjIds_of_old oid0 (hs1 oid0 (List.mem_append_right _
            (swap_corollary_heap_refs_mem_of_lookup hregion hr'')))
      · exact hobjIds_of_old oid0 (hs1 oid0 (List.mem_append_right _ hr'))
  · -- SWAP-REGION-REGION
    subst hcfg'
    have hfield : obj.lookup yf.field = some yfRef :=
      swap_corollary_region_field_eq_yfRef (hyoid ▸ hyr) (hyoid ▸ hyrloc ▸ hyrl) hregion hobj hyf
    obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
    have frame_toFrame_mem : frame.toFrame ∈ cfg.stack :=
      stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self _)
    have hxridRef_mem : Reference.RId xrid ∈ cfg.refs := List.mem_append_left _
      (swap_corollary_frame_refs_mem_stack frame_toFrame_mem
        (List.mem_append_right _ (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hxr))))
    have hyfRef_mem : yfRef ∈ cfg.refs := List.mem_append_right _
      (swap_corollary_heap_refs_mem_of_lookup hregion
        (swap_corollary_objMap_bind_refs_mem_of_lookup hobj
          (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hfield))))
    have hdrop_refs : ∀ r, r ∈ Stack.refs cfg.stack.dropLast → r ∈ cfg.refs := by
      intro r hr
      apply List.mem_append_left
      rw [stack_eq, swap_corollary_stack_refs_append]
      exact List.mem_append_left _ hr
    have hframe_refs : ∀ r, r ∈ Frame.refs frame.toFrame → r ∈ cfg.refs := by
      intro r hr
      apply List.mem_append_left
      rw [stack_eq, swap_corollary_stack_refs_append]
      exact List.mem_append_right _ hr
    set newFrame : Frame := { frame with varMap := frame.varMap.insert x yfRef } with newFrame_def
    set newRegion : Region := { region with
        objMap := AList.insert yoid (obj.insert yf.field (Reference.RId xrid)) region.objMap } with newRegion_def
    have region_perm := swap_corollary_insert_keys_perm (l := region.objMap)
      (v := obj.insert yf.field (Reference.RId xrid)) (swap_corollary_mem_keys_of_lookup hobj)
    have heap_perm := swap_corollary_region_heap_objectIds_perm (newRegion := newRegion) hregion region_perm
    have hstack_eq : Stack.objectIds (cfg.stack.dropLast ++ [newFrame]) = Stack.objectIds cfg.stack := by
      rw [swap_corollary_stack_objectIds_append]
      conv_rhs => rw [stack_eq]
      rw [swap_corollary_stack_objectIds_append]
      rfl
    have hobjIds_of_old : ∀ oid0, oid0 ∈ cfg.objectIds → oid0 ∈
        RuntimeConfig.objectIds { stack := cfg.stack.dropLast ++ [newFrame], heap := cfg.heap.insert rid newRegion } := by
      intro oid0 hoid0
      unfold RuntimeConfig.objectIds at hoid0 ⊢
      dsimp
      rw [hstack_eq]
      rw [List.mem_append] at hoid0 ⊢
      rcases hoid0 with hoid0 | hoid0
      · exact Or.inl hoid0
      · exact Or.inr (heap_perm.mem_iff.mpr hoid0)
    intro oid0 hr
    unfold RuntimeConfig.refs at hr
    dsimp at hr
    rw [swap_corollary_stack_refs_append, List.mem_append, List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · exact hobjIds_of_old oid0 (hs1 oid0 (hdrop_refs _ hr))
    · unfold Frame.refs at hr
      dsimp at hr
      rw [List.mem_append] at hr
      rcases hr with hr | hr
      · exact hobjIds_of_old oid0 (hs1 oid0 (hframe_refs _ (List.mem_append_left _ hr)))
      · rcases swap_corollary_alist_insert_refs_mem hr with hr' | hr'
        · exact hobjIds_of_old oid0 (hs1 oid0 (hr' ▸ hyfRef_mem))
        · exact hobjIds_of_old oid0 (hs1 oid0 (hframe_refs _ (List.mem_append_right _ hr')))
    · rcases swap_corollary_heap_insert_refs_mem (swap_corollary_mem_keys_of_lookup hregion) hr with hr' | hr'
      · unfold Region.refs at hr'
        dsimp at hr'
        rcases swap_corollary_objMap_insert_bind_refs_mem hr' with hr'' | hr''
        · rcases swap_corollary_alist_insert_refs_mem hr'' with hr''' | hr'''
          · exact hobjIds_of_old oid0 (hs1 oid0 (hr''' ▸ hxridRef_mem))
          · exact hobjIds_of_old oid0 (hs1 oid0 (List.mem_append_right _
              (swap_corollary_heap_refs_mem_of_lookup hregion
                (swap_corollary_objMap_bind_refs_mem_of_lookup hobj hr'''))))
        · exact hobjIds_of_old oid0 (hs1 oid0 (List.mem_append_right _
            (swap_corollary_heap_refs_mem_of_lookup hregion hr'')))
      · exact hobjIds_of_old oid0 (hs1 oid0 (List.mem_append_right _ hr'))
  · -- SWAP-REGION-BRIDGE: the one branch that writes a genuinely "new" ref value (the old
    -- bridgeObjectId, now wrapped as a field value) -- handled via H1 instead of HS1/refs-tracing,
    -- since nothing guarantees a bridge object's own id was previously referenced as a *value*.
    subst hcfg'
    have hfield : obj.lookup yf.field = some yfRef :=
      swap_corollary_region_field_eq_yfRef (hyoid ▸ hyr) (hyoid ▸ hyrloc ▸ hyrl) hregion hobj hyf
    have region_mem : region ∈ cfg.heap.regions := by
      unfold Heap.regions
      exact List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hregion)
    have hbridge_mem : region.bridgeObjectId ∈ region.objMap := h1 region region_mem
    set newRegion : Region := { region with
        bridgeObjectId := yfoid,
        objMap := AList.insert yoid (obj.insert yf.field (Reference.OId region.bridgeObjectId)) region.objMap
      } with newRegion_def
    have region_perm := swap_corollary_insert_keys_perm (l := region.objMap)
      (v := obj.insert yf.field (Reference.OId region.bridgeObjectId))
      (swap_corollary_mem_keys_of_lookup hobj)
    have heap_perm := swap_corollary_region_heap_objectIds_perm (newRegion := newRegion) hregion region_perm
    have hobjIds_of_old : ∀ oid0, oid0 ∈ cfg.objectIds → oid0 ∈
        RuntimeConfig.objectIds { stack := cfg.stack, heap := cfg.heap.insert yrid newRegion } := by
      intro oid0 hoid0
      unfold RuntimeConfig.objectIds at hoid0 ⊢
      dsimp
      rw [List.mem_append] at hoid0 ⊢
      rcases hoid0 with hoid0 | hoid0
      · exact Or.inl hoid0
      · exact Or.inr (heap_perm.mem_iff.mpr hoid0)
    have hbridge_objIds : region.bridgeObjectId ∈
        RuntimeConfig.objectIds { stack := cfg.stack, heap := cfg.heap.insert yrid newRegion } := by
      apply hobjIds_of_old
      unfold RuntimeConfig.objectIds
      apply List.mem_append_right
      unfold Heap.objectIds
      rw [List.mem_flatten]
      refine ⟨region.objMap.keys, ?_, AList.mem_keys.mp hbridge_mem⟩
      exact List.mem_map_of_mem (f := fun e : Sigma (fun _ : RegionId => Region) => e.2.objectIds)
        (AList.lookup_mem_entries hregion)
    intro oid0 hr
    unfold RuntimeConfig.refs at hr
    dsimp at hr
    rw [List.mem_append] at hr
    rcases hr with hr | hr
    · exact hobjIds_of_old oid0 (hs1 oid0 (List.mem_append_left _ hr))
    · rcases swap_corollary_heap_insert_refs_mem (swap_corollary_mem_keys_of_lookup hregion) hr with hr' | hr'
      · unfold Region.refs at hr'
        dsimp at hr'
        rcases swap_corollary_objMap_insert_bind_refs_mem hr' with hr'' | hr''
        · rcases swap_corollary_alist_insert_refs_mem hr'' with hr''' | hr'''
          · rw [Reference.OId.injEq] at hr'''
            exact hr''' ▸ hbridge_objIds
          · exact hobjIds_of_old oid0 (hs1 oid0 (List.mem_append_right _
              (swap_corollary_heap_refs_mem_of_lookup hregion
                (swap_corollary_objMap_bind_refs_mem_of_lookup hobj hr'''))))
        · exact hobjIds_of_old oid0 (hs1 oid0 (List.mem_append_right _
            (swap_corollary_heap_refs_mem_of_lookup hregion hr'')))
      · exact hobjIds_of_old oid0 (hs1 oid0 (List.mem_append_right _ hr'))

theorem swap_HS2 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  HS2 cfg' := by
  intro vcfg h
  have hs2 := vcfg.hs2
  obtain ⟨frame, hframe, yRef, hyr, yRefLoc, hyrl, yfRef, hyf, yfRefLoc, hyfl, hcase⟩ := swap_cases h
  have frame_mem : frame ∈ cfg.stackWithIndex := List.mem_of_getLast? hframe
  unfold HS2
  rcases hcase with
    ⟨yoid, xRef, obj, hxb, hyoid, hyrloc, hxr, hobj, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xoid, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hxrl, hxrid, hstatus, hcfg'⟩ |
    ⟨yoid, rid, region, obj, xrid, hxb, hyoid, hyrloc, hrid, hregion, hobj, hxr, hstatus, hcfg'⟩ |
    ⟨yoid, yrid, yfoid, yfrid, region, obj, hxb, hyoid, hyrloc, hyfoid, hyfrloc, hyrid, hyfrid, hregion, hobj, hcfg'⟩
  · -- SWAP-STACK: heap untouched, transport refs through the mutated last frame
    subst hcfg'
    have hfield : obj.lookup yf.field = some yfRef :=
      swap_corollary_stack_field_eq_yfRef frame_mem (hyoid ▸ hyr) (hyoid ▸ hyrloc ▸ hyrl) hobj hyf
    obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
    have frame_toFrame_mem : frame.toFrame ∈ cfg.stack :=
      stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self _)
    have hxRef_mem : xRef ∈ cfg.refs := List.mem_append_left _
      (swap_corollary_frame_refs_mem_stack frame_toFrame_mem
        (List.mem_append_right _ (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hxr))))
    have hyfRef_mem : yfRef ∈ cfg.refs := List.mem_append_left _
      (swap_corollary_frame_refs_mem_stack frame_toFrame_mem
        (List.mem_append_left _ (swap_corollary_objMap_bind_refs_mem_of_lookup hobj
          (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hfield)))))
    have hdrop_refs : ∀ r, r ∈ Stack.refs cfg.stack.dropLast → r ∈ cfg.refs := by
      intro r hr
      apply List.mem_append_left
      rw [stack_eq, swap_corollary_stack_refs_append]
      exact List.mem_append_left _ hr
    have hframe_refs : ∀ r, r ∈ Frame.refs frame.toFrame → r ∈ cfg.refs := by
      intro r hr
      apply List.mem_append_left
      rw [stack_eq, swap_corollary_stack_refs_append]
      exact List.mem_append_right _ hr
    intro rid' hr
    dsimp at hr ⊢
    unfold RuntimeConfig.refs at hr
    dsimp at hr
    rw [swap_corollary_stack_refs_append, List.mem_append, List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · exact hs2 rid' (hdrop_refs _ hr)
    · unfold Frame.refs at hr
      dsimp at hr
      rw [List.mem_append] at hr
      rcases hr with hr | hr
      · rcases swap_corollary_objMap_insert_bind_refs_mem hr with hr' | hr'
        · rcases swap_corollary_alist_insert_refs_mem hr' with hr'' | hr''
          · exact hs2 rid' (hr'' ▸ hxRef_mem)
          · exact hs2 rid' (hframe_refs _ (List.mem_append_left _
              (swap_corollary_objMap_bind_refs_mem_of_lookup hobj hr'')))
        · exact hs2 rid' (hframe_refs _ (List.mem_append_left _ hr'))
      · rcases swap_corollary_alist_insert_refs_mem hr with hr' | hr'
        · exact hs2 rid' (hr' ▸ hyfRef_mem)
        · exact hs2 rid' (hframe_refs _ (List.mem_append_right _ hr'))
    · exact hs2 rid' (List.mem_append_right _ hr)
  · -- SWAP-REGION-OBJECT
    subst hcfg'
    have hfield : obj.lookup yf.field = some yfRef :=
      swap_corollary_region_field_eq_yfRef (hyoid ▸ hyr) (hyoid ▸ hyrloc ▸ hyrl) hregion hobj hyf
    obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
    have frame_toFrame_mem : frame.toFrame ∈ cfg.stack :=
      stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self _)
    have hridmem : rid ∈ cfg.heap.keys := swap_corollary_mem_keys_of_lookup hregion
    have hxoidRef_mem : Reference.OId xoid ∈ cfg.refs := List.mem_append_left _
      (swap_corollary_frame_refs_mem_stack frame_toFrame_mem
        (List.mem_append_right _ (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hxr))))
    have hyfRef_mem : yfRef ∈ cfg.refs := List.mem_append_right _
      (swap_corollary_heap_refs_mem_of_lookup hregion
        (swap_corollary_objMap_bind_refs_mem_of_lookup hobj
          (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hfield))))
    have hdrop_refs : ∀ r, r ∈ Stack.refs cfg.stack.dropLast → r ∈ cfg.refs := by
      intro r hr
      apply List.mem_append_left
      rw [stack_eq, swap_corollary_stack_refs_append]
      exact List.mem_append_left _ hr
    have hframe_refs : ∀ r, r ∈ Frame.refs frame.toFrame → r ∈ cfg.refs := by
      intro r hr
      apply List.mem_append_left
      rw [stack_eq, swap_corollary_stack_refs_append]
      exact List.mem_append_right _ hr
    intro rid' hr
    dsimp at hr ⊢
    rw [swap_corollary_heap_insert_keys_mem hridmem]
    unfold RuntimeConfig.refs at hr
    dsimp at hr
    rw [swap_corollary_stack_refs_append, List.mem_append, List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · exact hs2 rid' (hdrop_refs _ hr)
    · unfold Frame.refs at hr
      dsimp at hr
      rw [List.mem_append] at hr
      rcases hr with hr | hr
      · exact hs2 rid' (hframe_refs _ (List.mem_append_left _ hr))
      · rcases swap_corollary_alist_insert_refs_mem hr with hr' | hr'
        · exact hs2 rid' (hr' ▸ hyfRef_mem)
        · exact hs2 rid' (hframe_refs _ (List.mem_append_right _ hr'))
    · rcases swap_corollary_heap_insert_refs_mem hridmem hr with hr' | hr'
      · unfold Region.refs at hr'
        dsimp at hr'
        rcases swap_corollary_objMap_insert_bind_refs_mem hr' with hr'' | hr''
        · rcases swap_corollary_alist_insert_refs_mem hr'' with hr''' | hr'''
          · exact hs2 rid' (hr''' ▸ hxoidRef_mem)
          · exact hs2 rid' (List.mem_append_right _
              (swap_corollary_heap_refs_mem_of_lookup hregion
                (swap_corollary_objMap_bind_refs_mem_of_lookup hobj hr''')))
        · exact hs2 rid' (List.mem_append_right _ (swap_corollary_heap_refs_mem_of_lookup hregion hr''))
      · exact hs2 rid' (List.mem_append_right _ hr')
  · -- SWAP-REGION-REGION
    subst hcfg'
    have hfield : obj.lookup yf.field = some yfRef :=
      swap_corollary_region_field_eq_yfRef (hyoid ▸ hyr) (hyoid ▸ hyrloc ▸ hyrl) hregion hobj hyf
    obtain ⟨stack_eq, _⟩ := swap_corollary_stack_eq hframe
    have frame_toFrame_mem : frame.toFrame ∈ cfg.stack :=
      stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self _)
    have hridmem : rid ∈ cfg.heap.keys := swap_corollary_mem_keys_of_lookup hregion
    have hxridRef_mem : Reference.RId xrid ∈ cfg.refs := List.mem_append_left _
      (swap_corollary_frame_refs_mem_stack frame_toFrame_mem
        (List.mem_append_right _ (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hxr))))
    have hyfRef_mem : yfRef ∈ cfg.refs := List.mem_append_right _
      (swap_corollary_heap_refs_mem_of_lookup hregion
        (swap_corollary_objMap_bind_refs_mem_of_lookup hobj
          (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hfield))))
    have hdrop_refs : ∀ r, r ∈ Stack.refs cfg.stack.dropLast → r ∈ cfg.refs := by
      intro r hr
      apply List.mem_append_left
      rw [stack_eq, swap_corollary_stack_refs_append]
      exact List.mem_append_left _ hr
    have hframe_refs : ∀ r, r ∈ Frame.refs frame.toFrame → r ∈ cfg.refs := by
      intro r hr
      apply List.mem_append_left
      rw [stack_eq, swap_corollary_stack_refs_append]
      exact List.mem_append_right _ hr
    intro rid' hr
    dsimp at hr ⊢
    rw [swap_corollary_heap_insert_keys_mem hridmem]
    unfold RuntimeConfig.refs at hr
    dsimp at hr
    rw [swap_corollary_stack_refs_append, List.mem_append, List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · exact hs2 rid' (hdrop_refs _ hr)
    · unfold Frame.refs at hr
      dsimp at hr
      rw [List.mem_append] at hr
      rcases hr with hr | hr
      · exact hs2 rid' (hframe_refs _ (List.mem_append_left _ hr))
      · rcases swap_corollary_alist_insert_refs_mem hr with hr' | hr'
        · exact hs2 rid' (hr' ▸ hyfRef_mem)
        · exact hs2 rid' (hframe_refs _ (List.mem_append_right _ hr'))
    · rcases swap_corollary_heap_insert_refs_mem hridmem hr with hr' | hr'
      · unfold Region.refs at hr'
        dsimp at hr'
        rcases swap_corollary_objMap_insert_bind_refs_mem hr' with hr'' | hr''
        · rcases swap_corollary_alist_insert_refs_mem hr'' with hr''' | hr'''
          · exact hs2 rid' (hr''' ▸ hxridRef_mem)
          · exact hs2 rid' (List.mem_append_right _
              (swap_corollary_heap_refs_mem_of_lookup hregion
                (swap_corollary_objMap_bind_refs_mem_of_lookup hobj hr''')))
        · exact hs2 rid' (List.mem_append_right _ (swap_corollary_heap_refs_mem_of_lookup hregion hr''))
      · exact hs2 rid' (List.mem_append_right _ hr')
  · -- SWAP-REGION-BRIDGE: stack untouched, only the heap's region at yrid changes
    subst hcfg'
    have hfield : obj.lookup yf.field = some yfRef :=
      swap_corollary_region_field_eq_yfRef (hyoid ▸ hyr) (hyoid ▸ hyrloc ▸ hyrl) hregion hobj hyf
    have hridmem : yrid ∈ cfg.heap.keys := swap_corollary_mem_keys_of_lookup hregion
    intro rid' hr
    dsimp at hr ⊢
    rw [swap_corollary_heap_insert_keys_mem hridmem]
    unfold RuntimeConfig.refs at hr
    dsimp at hr
    rw [List.mem_append] at hr
    rcases hr with hr | hr
    · exact hs2 rid' (List.mem_append_left _ hr)
    · rcases swap_corollary_heap_insert_refs_mem hridmem hr with hr' | hr'
      · unfold Region.refs at hr'
        dsimp at hr'
        rcases swap_corollary_objMap_insert_bind_refs_mem hr' with hr'' | hr''
        · rcases swap_corollary_alist_insert_refs_mem hr'' with hr''' | hr'''
          · exact absurd hr''' (by simp)
          · exact hs2 rid' (List.mem_append_right _
              (swap_corollary_heap_refs_mem_of_lookup hregion
                (swap_corollary_objMap_bind_refs_mem_of_lookup hobj hr''')))
        · exact hs2 rid' (List.mem_append_right _ (swap_corollary_heap_refs_mem_of_lookup hregion hr''))
      · exact hs2 rid' (List.mem_append_right _ hr')

theorem swap_valid : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  ValidConfig cfg' := by
  intro vcfg h
  exact {
    l1 := swap_L1 vcfg h,
    l2 := swap_L2 vcfg h,
    h1 := swap_H1 vcfg h,
    h2 := swap_H2 vcfg h,
    h3 := swap_H3 vcfg h,
    s1 := swap_S1 vcfg h,
    s2 := swap_S2 vcfg h,
    s3 := swap_S3 vcfg h,
    hs1 := swap_HS1 vcfg h,
    hs2 := swap_HS2 vcfg h
  }
