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
  sorry

theorem swap_HS2 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  HS2 cfg' := by
  sorry

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
