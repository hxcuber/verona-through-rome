import Gc.Model.Mutation.VarAsgn
import Gc.Model.Preservation.VarAsgn
import Gc.Model.Preservation.Common
import Gc.Reachability.Referencable.Basic
import Gc.Reachability.Referencable.Lemmas.Common

-- varAsgn never touches any `objMap` anywhere -- the BRIDGE branch only replaces a heap region's
-- `bridgeObjectId` (a scalar field), and the FRESH-VAR branch only replaces the last frame's
-- `varMap`. So at every stack position, `objMap` is literally unchanged.
theorem varAsgn_corollary_stack_objMap_eq (h : varAsgn xf y cfg = some cfg') (n : ℕ) :
    (cfg.stack[n]?).map Frame.objMap = (cfg'.stack[n]?).map Frame.objMap := by
  obtain ⟨frame, hframe, hcase⟩ := varAsgn_cases h
  rcases hcase with
    ⟨oid, rid, region, hyf, hxb, hloc, hridEq, hregion, hcfg'⟩ | ⟨oid, hyf, hxb, hresolve, hcfg'⟩
  · rw [hcfg']
  · obtain ⟨stack_eq, hidxeq⟩ :=
      (⟨(List.dropLast_append_getLast? frame hframe).symm,
        rfl⟩ : cfg.stack = cfg.stack.dropLast ++ [frame] ∧ cfg.stack.dropLast.length = cfg.stack.dropLast.length)
    set newFrame : Frame := { frame with varMap := frame.varMap.insert xf (Reference.OId oid) } with newFrame_def
    have hcfg'2 : cfg' = { cfg with stack := cfg.stack.dropLast ++ [newFrame] } := by rw [hcfg', newFrame_def]
    by_cases hlp : n = cfg.stack.dropLast.length
    · have e1 : cfg.stack[n]? = some frame := by conv_lhs => rw [stack_eq, hlp]; simp
      have e2 : cfg'.stack[n]? = some newFrame := by rw [hcfg'2]; dsimp only; rw [hlp]; simp
      rw [e1, e2]; rfl
    · by_cases hlt : n < cfg.stack.dropLast.length
      · have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
          conv_lhs => rw [stack_eq]
          rw [List.getElem?_append_left hlt]
        have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
          rw [hcfg'2]; dsimp only; rw [List.getElem?_append_left hlt]
        rw [e1, e2]
      · have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq]; simp
        have hlen' : cfg'.stack.length = cfg.stack.dropLast.length + 1 := by rw [hcfg'2]; simp
        have e1 : cfg.stack[n]? = none := List.getElem?_eq_none (by omega)
        have e2 : cfg'.stack[n]? = none := List.getElem?_eq_none (by omega)
        rw [e1, e2]

-- varAsgn never touches a frame's `regionId`/`bridgeVar` anywhere -- the BRIDGE branch doesn't
-- touch `cfg.stack` at all, and the FRESH-VAR branch only replaces the last frame's `varMap`. So
-- at every stack position, this pair is literally unchanged (mirrors
-- fieldAsgn_corollary_stack_shape_eq, just projecting a narrower pair since varMap, unlike
-- fieldAsgn's untouched objMap, is exactly what genuinely changes here).
theorem varAsgn_corollary_stack_shape_eq (h : varAsgn xf y cfg = some cfg') (n : ℕ) :
    (cfg.stack[n]?).map (fun f => (f.regionId, f.bridgeVar)) =
    (cfg'.stack[n]?).map (fun f => (f.regionId, f.bridgeVar)) := by
  obtain ⟨frame, hframe, hcase⟩ := varAsgn_cases h
  rcases hcase with
    ⟨oid, rid, region, hyf, hxb, hloc, hridEq, hregion, hcfg'⟩ | ⟨oid, hyf, hxb, hresolve, hcfg'⟩
  · rw [hcfg']
  · have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] := (List.dropLast_append_getLast? frame hframe).symm
    set newFrame : Frame := { frame with varMap := frame.varMap.insert xf (Reference.OId oid) } with newFrame_def
    have hcfg'2 : cfg' = { cfg with stack := cfg.stack.dropLast ++ [newFrame] } := by rw [hcfg', newFrame_def]
    by_cases hlp : n = cfg.stack.dropLast.length
    · have e1 : cfg.stack[n]? = some frame := by conv_lhs => rw [stack_eq, hlp]; simp
      have e2 : cfg'.stack[n]? = some newFrame := by rw [hcfg'2]; dsimp only; rw [hlp]; simp
      rw [e1, e2]; rfl
    · by_cases hlt : n < cfg.stack.dropLast.length
      · have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
          conv_lhs => rw [stack_eq]
          rw [List.getElem?_append_left hlt]
        have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
          rw [hcfg'2]; dsimp only; rw [List.getElem?_append_left hlt]
        rw [e1, e2]
      · have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq]; simp
        have hlen' : cfg'.stack.length = cfg.stack.dropLast.length + 1 := by rw [hcfg'2]; simp
        have e1 : cfg.stack[n]? = none := List.getElem?_eq_none (by omega)
        have e2 : cfg'.stack[n]? = none := List.getElem?_eq_none (by omega)
        rw [e1, e2]

-- Frame membership in cfg'.stackWithIndex transports down to cfg with the SAME index and
-- regionId/bridgeVar (though possibly a different varMap, if varAsgn's FRESH-VAR branch mutated
-- exactly that position) -- everything CR3 itself ever reads off a frame (never its varMap). Thin
-- wrapper around `Gc.Model.Preservation.Common`'s generic `stackWithIndex_frame_transport_down_
-- of_shape_eq`, instantiated at `proj := fun f => (f.regionId, f.bridgeVar)` and destructuring its
-- `Prod`-valued conclusion back into the two named fields below.
theorem varAsgn_corollary_frame_transport_down (h : varAsgn xf y cfg = some cfg')
    (fr : FrameWithIndex) (hfr : fr ∈ cfg'.stackWithIndex) :
    ∃ fr0 : FrameWithIndex, fr0 ∈ cfg.stackWithIndex ∧ fr0.index = fr.index ∧
      fr0.regionId = fr.regionId ∧ fr0.bridgeVar = fr.bridgeVar := by
  obtain ⟨fr0, hmem, hidx, hproj⟩ :=
    stackWithIndex_frame_transport_down_of_shape_eq (proj := fun f => (f.regionId, f.bridgeVar))
      (varAsgn_corollary_stack_shape_eq h) fr hfr
  injection hproj with hrid hbv
  exact ⟨fr0, hmem, hidx, hrid, hbv⟩

-- Mirrors varAsgn_corollary_frame_transport_down, transporting membership the other way (also a
-- thin wrapper, around `stackWithIndex_frame_transport_up_of_shape_eq`).
theorem varAsgn_corollary_frame_transport_up (h : varAsgn xf y cfg = some cfg')
    (fr : FrameWithIndex) (hfr : fr ∈ cfg.stackWithIndex) :
    ∃ fr0 : FrameWithIndex, fr0 ∈ cfg'.stackWithIndex ∧ fr0.index = fr.index ∧
      fr0.regionId = fr.regionId ∧ fr0.bridgeVar = fr.bridgeVar := by
  obtain ⟨fr0, hmem, hidx, hproj⟩ :=
    stackWithIndex_frame_transport_up_of_shape_eq (proj := fun f => (f.regionId, f.bridgeVar))
      (varAsgn_corollary_stack_shape_eq h) fr hfr
  injection hproj with hrid hbv
  exact ⟨fr0, hmem, hidx, hrid, hbv⟩

-- Mirrors the above for the heap: the FRESH-VAR branch doesn't touch `cfg.heap` at all, and the
-- BRIDGE branch only replaces `bridgeObjectId` at one already-present key (never `objMap`).
theorem varAsgn_corollary_heap_objMap_eq (h : varAsgn xf y cfg = some cfg') (rid0 : RegionId) :
    (cfg.heap.lookup rid0).map Region.objMap = (cfg'.heap.lookup rid0).map Region.objMap := by
  obtain ⟨frame, hframe, hcase⟩ := varAsgn_cases h
  rcases hcase with
    ⟨oid, rid, region, hyf, hxb, hloc, hridEq, hregion, hcfg'⟩ | ⟨oid, hyf, hxb, hresolve, hcfg'⟩
  · rw [hcfg']
    dsimp only
    by_cases hrideq : rid0 = rid
    · subst hrideq
      rw [hregion, AList.lookup_insert]
      rfl
    · rw [AList.lookup_insert_ne hrideq]
  · rw [hcfg']

-- `Reference.objAt?` is completely unaffected by varAsgn, for *every* reference (not just some
-- exception): `loc?` is already unconditionally unchanged (`varAsgn_corollary_loc_eq`), and
-- neither branch ever touches an `objMap`, so whichever frame/region `loc?` resolves into has
-- identical content in both configs.
theorem varAsgn_corollary_objAt_eq (vcfg : ValidConfig cfg) (vcfg' : ValidConfig cfg')
    (h : varAsgn xf y cfg = some cfg') (ref : Reference) : ref.objAt? cfg = ref.objAt? cfg' := by
  cases ref with
  | RId rid0 => rfl
  | OId oid' =>
    have hlocEq := varAsgn_corollary_loc_eq vcfg h oid'
    cases hloc : (Reference.OId oid').loc? cfg with
    | none =>
      unfold Reference.objAt?
      dsimp only
      rw [hloc, ← hlocEq, hloc]
    | some loc =>
      have hloc2 : (Reference.OId oid').loc? cfg' = some loc := by rw [← hlocEq]; exact hloc
      cases loc with
      | Rgn rid0 =>
        unfold Reference.objAt?
        dsimp only
        rw [hloc, hloc2]
        dsimp only
        have hmapEq := varAsgn_corollary_heap_objMap_eq h rid0
        cases hlookup : cfg.heap.lookup rid0 with
        | none =>
          have hlookup2 : cfg'.heap.lookup rid0 = none := by
            rw [hlookup] at hmapEq
            exact Option.map_eq_none_iff.mp hmapEq.symm
          rw [hlookup2]
        | some region0 =>
          rw [hlookup, Option.map_some] at hmapEq
          obtain ⟨region0', hlookup2, hobjEq⟩ := Option.map_eq_some_iff.mp hmapEq.symm
          rw [hlookup2]
          show region0.objMap.lookup oid' = region0'.objMap.lookup oid'
          rw [hobjEq]
      | Stk fid0 =>
        unfold Reference.objAt?
        dsimp only
        rw [hloc, hloc2]
        dsimp only
        have hmapEq := varAsgn_corollary_stack_objMap_eq h fid0
        obtain ⟨frameA, hframeA, _⟩ := (oid_loc_stk_iff_in_stack vcfg).mp hloc
        obtain ⟨frameB, hframeB, _⟩ := (oid_loc_stk_iff_in_stack vcfg').mp hloc2
        obtain ⟨sfA, hsfA, hsfA_eq⟩ : ∃ sf, cfg.stack[fid0]? = some sf ∧ frameA = { sf with index := fid0 } := by
          have h' := hframeA
          unfold RuntimeConfig.stackWithIndex at h'
          rw [List.getElem?_mapIdx, Option.map_eq_some_iff] at h'
          obtain ⟨sf, hsf, hsf_eq⟩ := h'
          exact ⟨sf, hsf, hsf_eq.symm⟩
        obtain ⟨sfB, hsfB, hsfB_eq⟩ : ∃ sf, cfg'.stack[fid0]? = some sf ∧ frameB = { sf with index := fid0 } := by
          have h' := hframeB
          unfold RuntimeConfig.stackWithIndex at h'
          rw [List.getElem?_mapIdx, Option.map_eq_some_iff] at h'
          obtain ⟨sf, hsf, hsf_eq⟩ := h'
          exact ⟨sf, hsf, hsf_eq.symm⟩
        have hidxA : frameA.index = fid0 := by rw [hsfA_eq]
        have hidxB : frameB.index = fid0 := by rw [hsfB_eq]
        have hmemA : frameA ∈ cfg.stackWithIndex := List.mem_of_getElem? hframeA
        have hmemB : frameB ∈ cfg'.stackWithIndex := List.mem_of_getElem? hframeB
        have hfindA : cfg.stackWithIndex.find? (fun f => f.index == fid0) = some frameA := by
          rw [← hidxA]; exact swap_corollary_stackWithIndex_find_eq hmemA
        have hfindB : cfg'.stackWithIndex.find? (fun f => f.index == fid0) = some frameB := by
          rw [← hidxB]; exact swap_corollary_stackWithIndex_find_eq hmemB
        rw [hfindA, hfindB]
        rw [hsfA_eq, hsfB_eq]
        rw [hsfA, Option.map_some] at hmapEq
        obtain ⟨sfB', hsfB', hobjEq⟩ := Option.map_eq_some_iff.mp hmapEq.symm
        rw [hsfB] at hsfB'
        injection hsfB' with hsfB'_eq
        show sfA.objMap.lookup oid' = sfB.objMap.lookup oid'
        rw [hsfB'_eq, hobjEq]

