import Gc.Model.Mutation.VarAsgn
import Gc.Model.Preservation.VarAsgn
import Gc.Model.Preservation.Common
import Gc.Reachability.Referencable.Validity.Reachable
import Gc.Reachability.Referencable.Corollaries.Common

-- varAsgn never touches any `objMap` anywhere -- the BRIDGE branch only replaces a heap region's
-- `bridgeObjectId` (a scalar field), and the FRESH-VAR branch only replaces the last frame's
-- `varMap`. So at every stack position, `objMap` is literally unchanged.
private theorem varAsgn_corollary_stack_objMap_eq (h : varAsgn xf y cfg = some cfg') (n : ℕ) :
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
private theorem varAsgn_corollary_stack_shape_eq (h : varAsgn xf y cfg = some cfg') (n : ℕ) :
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
private theorem varAsgn_corollary_frame_transport_down (h : varAsgn xf y cfg = some cfg')
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
private theorem varAsgn_corollary_frame_transport_up (h : varAsgn xf y cfg = some cfg')
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
private theorem varAsgn_corollary_heap_objMap_eq (h : varAsgn xf y cfg = some cfg') (rid0 : RegionId) :
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

theorem varAsgn_cr3 : ValidReachableConfig cfg →
  varAsgn xf y cfg = some cfg' →
  CR3 cfg' := by
  intro vrcfg h
  have vcfg := vrcfg.toValidConfig
  have vcfg' := varAsgn_valid vcfg h
  have hRefStepIff : ∀ a b, RefStep cfg a b ↔ RefStep cfg' a b := by
    intro a b
    unfold RefStep
    rw [varAsgn_corollary_objAt_eq vcfg vcfg' h a]
  obtain ⟨frame0, hframe0, hcase⟩ := varAsgn_cases h
  have stack_eq0 : cfg.stack = cfg.stack.dropLast ++ [frame0] :=
    (List.dropLast_append_getLast? frame0 hframe0).symm
  set frame0W : FrameWithIndex := { frame0 with index := cfg.stack.dropLast.length } with frame0W_def
  have hframe0W_mem : frame0W ∈ cfg.stackWithIndex := by
    unfold RuntimeConfig.stackWithIndex
    rw [stack_eq0, List.mapIdx_concat]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hframe0_max : ∀ fr : FrameWithIndex, fr ∈ cfg.stackWithIndex → fr.index ≤ frame0W.index := by
    intro fr hfr
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr
    have hidxfr : fr.index = n := by rw [← hfeq]
    have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq0]; simp
    rw [hlen] at hn
    rw [hidxfr]
    exact Nat.le_of_lt_succ hn
  unfold CR3
  intro frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  obtain ⟨frameD, hframeDMem, hidxD, hridD, _⟩ := varAsgn_corollary_frame_transport_down h frame hframeMem
  obtain ⟨frameD', hframeD'Mem, hidxD', hridD', hbvD'⟩ :=
    varAsgn_corollary_frame_transport_down h frame' hframe'Mem
  have hltD : frameD.index < frameD'.index := by rw [hidxD, hidxD']; exact hlt
  have hD'_le_frame0 : frameD'.index ≤ frame0W.index := hframe0_max frameD' hframeD'Mem
  have hD_lt_frame0 : frameD.index < frame0W.index := lt_of_lt_of_le hltD hD'_le_frame0
  have hlocDown : (Reference.OId oid).loc? cfg = some (Location.Rgn frameD.regionId) := by
    rw [hridD, varAsgn_corollary_loc_eq vcfg h oid]; exact hloc
  rw [FrameReferencable_iff_reflTransGen] at hreach
  obtain ⟨start, hroot, hrtg⟩ := hreach
  have hrtgDown : Relation.ReflTransGen (RefStep cfg) start (Reference.OId oid) :=
    hrtg.mono (fun a b hab => (hRefStepIff a b).mpr hab)
  have escape : ∀ oidw : ObjectId, resolveFA y cfg = some (Reference.OId oidw) →
      start = Reference.OId oidw →
      FrameReferencable cfg frameD.index (Reference.OId oid) := by
    intro oidw hyf hstarteq
    have hrtgDownW : Relation.ReflTransGen (RefStep cfg) (Reference.OId oidw) (Reference.OId oid) := by
      rw [← hstarteq]; exact hrtgDown
    obtain ⟨frameY, hframeYMem, hreachYw⟩ := resolveFA_frameReach hyf
    have hreachY : FrameReferencable cfg frameY.index (Reference.OId oid) := by
      rw [FrameReferencable_iff_reflTransGen] at hreachYw ⊢
      obtain ⟨startY, hrootY, hrtgY⟩ := hreachYw
      exact ⟨startY, hrootY, hrtgY.trans hrtgDownW⟩
    have hownerbound := FrameReferencable_owner_index_le cfg vcfg frameY hreachY frameD.regionId
      hlocDown frameD hframeDMem rfl
    by_cases heqidx : frameD.index = frameY.index
    · have hFYeq : frameY = frameD := swap_corollary_stackWithIndex_index_inj hframeYMem hframeDMem heqidx.symm
      rw [← hFYeq]; exact hreachY
    · have hltidx : frameD.index < frameY.index := lt_of_le_of_ne hownerbound heqidx
      exact vrcfg.cr3 frameD hframeDMem frameY hframeYMem hltidx oid hlocDown hreachY
  have hconcDown : FrameReferencable cfg frameD.index (Reference.OId oid) := by
    rcases hcase with
      ⟨oidw, ridw, regionw, hyf, hxb, hlocw, hridEqw, hregionw, hcfg'⟩ | ⟨oidw, hyf, hxb, hresolve, hcfg'⟩
    · -- BRIDGE branch: cfg'.stack = cfg.stack literally, so FrameRoot's var disjunct is
      -- unconditionally unaffected; the bridge disjunct changes only frame0's own region's
      -- bridgeObjectId (old value -> oidw).
      have hswi_eq : cfg'.stackWithIndex = cfg.stackWithIndex := by
        unfold RuntimeConfig.stackWithIndex; rw [show cfg'.stack = cfg.stack from by rw [hcfg']]
      rcases hroot with ⟨fr1, hfr1, hidx1, var, hlookup1⟩ | ⟨fr1, hfr1, hidx1, region1, hlookup1, hstart⟩
      · rw [hswi_eq] at hfr1
        have hrootDown : FrameRoot cfg frameD'.index start := Or.inl ⟨fr1, hfr1, by rw [hidxD', ← hidx1], var, hlookup1⟩
        have hreachD' : FrameReferencable cfg frameD'.index (Reference.OId oid) :=
          (FrameReferencable_iff_reflTransGen cfg frameD'.index (Reference.OId oid)).mpr ⟨start, hrootDown, hrtgDown⟩
        exact vrcfg.cr3 frameD hframeDMem frameD' hframeD'Mem hltD oid hlocDown hreachD'
      · rw [hswi_eq] at hfr1
        by_cases hrideq : fr1.regionId = ridw
        · have hridEqw' : frame0W.regionId = ridw := hridEqw
          have hidx_eq := merge_corollary_regionId_unique_index vcfg.s1 hfr1 hframe0W_mem (hrideq.trans hridEqw'.symm)
          have hfr1eq : fr1 = frame0W := swap_corollary_stackWithIndex_index_inj hfr1 hframe0W_mem hidx_eq
          have hbridgeEq : region1.bridgeObjectId = oidw := by
            have hlookup1' : cfg'.heap.lookup ridw =
                some ({ bridgeObjectId := oidw, objMap := regionw.objMap, status := regionw.status } : Region) := by
              rw [hcfg']; exact AList.lookup_insert (a := ridw)
                (b := ({ bridgeObjectId := oidw, objMap := regionw.objMap, status := regionw.status } : Region)) cfg.heap
            rw [hrideq, hlookup1'] at hlookup1
            injection hlookup1 with hlookup1_eq
            rw [← hlookup1_eq]
          have hstarteq : start = Reference.OId oidw := by rw [hstart, hbridgeEq]
          exact escape oidw hyf hstarteq
        · have hlookup1_cfg : cfg.heap.lookup fr1.regionId = some region1 := by
            have heq : cfg'.heap.lookup fr1.regionId = cfg.heap.lookup fr1.regionId := by
              rw [hcfg']; exact AList.lookup_insert_ne hrideq
            rw [← heq]; exact hlookup1
          have hrootDown : FrameRoot cfg frameD'.index start :=
            Or.inr ⟨fr1, hfr1, by rw [hidxD', ← hidx1], region1, hlookup1_cfg, hstart⟩
          have hreachD' : FrameReferencable cfg frameD'.index (Reference.OId oid) :=
            (FrameReferencable_iff_reflTransGen cfg frameD'.index (Reference.OId oid)).mpr ⟨start, hrootDown, hrtgDown⟩
          exact vrcfg.cr3 frameD hframeDMem frameD' hframeD'Mem hltD oid hlocDown hreachD'
    · -- FRESH-VAR branch: heap is untouched entirely, and only frame0's own varMap gains one new
      -- key (`xf`, previously unbound per `hresolve`); every other position (and every bridge
      -- root, at every position) is unaffected.
      have hswi_bridge_ok : ∀ fr1 : FrameWithIndex, fr1 ∈ cfg'.stackWithIndex →
          ∃ fr1D : FrameWithIndex, fr1D ∈ cfg.stackWithIndex ∧ fr1D.index = fr1.index ∧ fr1D.regionId = fr1.regionId :=
        fun fr1 hfr1 => by
          obtain ⟨fr1D, hfr1DMem, hidx1D, hrid1D, _⟩ := varAsgn_corollary_frame_transport_down h fr1 hfr1
          exact ⟨fr1D, hfr1DMem, hidx1D, hrid1D⟩
      have hheap_eq : cfg'.heap = cfg.heap := by rw [hcfg']
      rcases hroot with ⟨fr1, hfr1, hidx1, var, hlookup1⟩ | ⟨fr1, hfr1, hidx1, region1, hlookup1, hstart⟩
      · obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr1
        have hidx1n : fr1.index = n := by rw [← hfeq]
        by_cases hlast : n = cfg.stack.dropLast.length
        · -- fr1 sits at frame0's own (mutated) position: either an OLD var (transports directly
          -- via `AList.lookup_insert_ne`), or exactly the newly-inserted `xf`.
          have hfr1_varMap : fr1.varMap = frame0.varMap.insert xf (Reference.OId oidw) := by
            have hget' : cfg'.stack[n]? = some fr1.toFrame := by
              rw [show fr1.toFrame = cfg'.stack[n] from by rw [← hfeq]]
              exact List.getElem?_eq_getElem hn
            rw [hcfg'] at hget'
            dsimp only at hget'
            rw [hlast] at hget'
            simp only [List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero] at hget'
            injection hget' with hget'_eq
            rw [← hget'_eq]
          by_cases hvareq : var = xf
          · have hstarteq : start = Reference.OId oidw := by
              have heq1 : fr1.varMap.lookup var = some start := hlookup1
              rw [hvareq, hfr1_varMap, AList.lookup_insert] at heq1
              injection heq1 with heq1'
              exact heq1'.symm
            exact escape oidw hyf hstarteq
          · have hlookup1_cfg : frame0.varMap.lookup var = some start := by
              have heq1 : fr1.varMap.lookup var = some start := hlookup1
              rw [hfr1_varMap, AList.lookup_insert_ne hvareq] at heq1
              exact heq1
            have hrootDown : FrameRoot cfg frameD'.index start :=
              Or.inl ⟨frame0W, hframe0W_mem, by rw [hidxD', ← hidx1, hidx1n, frame0W_def, hlast], var,
                hlookup1_cfg⟩
            have hreachD' : FrameReferencable cfg frameD'.index (Reference.OId oid) :=
              (FrameReferencable_iff_reflTransGen cfg frameD'.index (Reference.OId oid)).mpr ⟨start, hrootDown, hrtgDown⟩
            exact vrcfg.cr3 frameD hframeDMem frameD' hframeD'Mem hltD oid hlocDown hreachD'
        · have hlt : n < cfg.stack.dropLast.length := by
            have hlen' : cfg'.stack.length = cfg.stack.dropLast.length + 1 := by rw [hcfg']; simp
            have hn' : n < cfg'.stack.length := hn
            rw [hlen'] at hn'
            exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hn') hlast
          have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
            conv_lhs => rw [stack_eq0]
            rw [List.getElem?_append_left hlt]
          have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
            rw [hcfg']; dsimp only; rw [List.getElem?_append_left hlt]
          have hfr1_get : cfg'.stack[n]? = some fr1.toFrame := by
            rw [show fr1.toFrame = cfg'.stack[n] from by rw [← hfeq]]
            exact List.getElem?_eq_getElem hn
          have hcfgn : cfg.stack[n]? = some fr1.toFrame := by rw [e1, ← e2, hfr1_get]
          obtain ⟨h1, heq⟩ := List.getElem?_eq_some_iff.mp hcfgn
          have hfr1Mem : fr1 ∈ cfg.stackWithIndex := by
            unfold RuntimeConfig.stackWithIndex
            exact List.mem_mapIdx.mpr ⟨n, h1, by rw [heq, ← hidx1n]⟩
          have hrootDown : FrameRoot cfg frameD'.index start := Or.inl ⟨fr1, hfr1Mem, by rw [hidxD', ← hidx1], var, hlookup1⟩
          have hreachD' : FrameReferencable cfg frameD'.index (Reference.OId oid) :=
            (FrameReferencable_iff_reflTransGen cfg frameD'.index (Reference.OId oid)).mpr ⟨start, hrootDown, hrtgDown⟩
          exact vrcfg.cr3 frameD hframeDMem frameD' hframeD'Mem hltD oid hlocDown hreachD'
      · obtain ⟨fr1D, hfr1DMem, hidx1D, hrid1D⟩ := hswi_bridge_ok fr1 hfr1
        have hlookup1_cfg : cfg.heap.lookup fr1D.regionId = some region1 := by
          rw [hrid1D, ← hheap_eq]; exact hlookup1
        have hrootDown : FrameRoot cfg frameD'.index start :=
          Or.inr ⟨fr1D, hfr1DMem, by rw [hidxD', ← hidx1, hidx1D], region1, hlookup1_cfg, hstart⟩
        have hreachD' : FrameReferencable cfg frameD'.index (Reference.OId oid) :=
          (FrameReferencable_iff_reflTransGen cfg frameD'.index (Reference.OId oid)).mpr ⟨start, hrootDown, hrtgDown⟩
        exact vrcfg.cr3 frameD hframeDMem frameD' hframeD'Mem hltD oid hlocDown hreachD'
  -- Final UP transport: `frame` (the CR3-quantified suspended-region owner) is never frame0
  -- (index/regionId untouched everywhere), so its own root set and every RefStep hop are
  -- unconditionally unaffected by the mutation.
  have hframe_lt_frame0 : frameD.index < frame0W.index := hD_lt_frame0
  rw [FrameReferencable_iff_reflTransGen] at hconcDown
  obtain ⟨start2, hroot2, hrtg2⟩ := hconcDown
  have hrootUp : FrameRoot cfg' frameD.index start2 := by
    have hne : frameD.index ≠ frame0W.index := Nat.ne_of_lt hframe_lt_frame0
    rcases hroot2 with ⟨fr2, hfr2, hidx2, var, hlookup2⟩ | ⟨fr2, hfr2, hidx2, region2, hlookup2, hstart2⟩
    · rw [← hidx2] at hne
      obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr2
      have hidx2n : fr2.index = n := by rw [← hfeq]
      have hlast : n ≠ cfg.stack.dropLast.length := by rw [hidx2n] at hne; exact hne
      have hlt : n < cfg.stack.dropLast.length := by
        have hn' : n < cfg.stack.length := hn
        rw [show cfg.stack.length = cfg.stack.dropLast.length + 1 from by rw [stack_eq0]; simp] at hn'
        exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hn') hlast
      have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
        conv_lhs => rw [stack_eq0]
        rw [List.getElem?_append_left hlt]
      have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
        rcases hcase with
          ⟨oidw, ridw, regionw, hyf, hxb, hlocw, hridEqw, hregionw, hcfg'⟩ | ⟨oidw, hyf, hxb, hresolve, hcfg'⟩
        · rw [hcfg']; exact e1
        · rw [hcfg']; dsimp only; rw [List.getElem?_append_left hlt]
      have hfr2_get : cfg.stack[n]? = some fr2.toFrame := by
        rw [show fr2.toFrame = cfg.stack[n] from by rw [← hfeq]]
        exact List.getElem?_eq_getElem hn
      have hcfg'n : cfg'.stack[n]? = some fr2.toFrame := by rw [e2, ← e1, hfr2_get]
      obtain ⟨h1, heq⟩ := List.getElem?_eq_some_iff.mp hcfg'n
      have hfr2Mem : fr2 ∈ cfg'.stackWithIndex := by
        unfold RuntimeConfig.stackWithIndex
        exact List.mem_mapIdx.mpr ⟨n, h1, by rw [heq, ← hidx2n]⟩
      exact Or.inl ⟨fr2, hfr2Mem, hidx2, var, hlookup2⟩
    · rcases hcase with
        ⟨oidw, ridw, regionw, hyf, hxb, hlocw, hridEqw, hregionw, hcfg'⟩ | ⟨oidw, hyf, hxb, hresolve, hcfg'⟩
      · have hswi_eq2 : cfg'.stackWithIndex = cfg.stackWithIndex := by
          unfold RuntimeConfig.stackWithIndex; rw [show cfg'.stack = cfg.stack from by rw [hcfg']]
        have hfr2Mem' : fr2 ∈ cfg'.stackWithIndex := by rw [hswi_eq2]; exact hfr2
        by_cases hrideq : fr2.regionId = ridw
        · exfalso
          have hridEqw' : frame0W.regionId = ridw := hridEqw
          have hidx_eq := merge_corollary_regionId_unique_index vcfg.s1 hfr2 hframe0W_mem (hrideq.trans hridEqw'.symm)
          rw [hidx2] at hidx_eq
          exact hne hidx_eq
        · have hlookup2' : cfg'.heap.lookup fr2.regionId = some region2 := by
            rw [hcfg']; rw [AList.lookup_insert_ne hrideq]; exact hlookup2
          exact Or.inr ⟨fr2, hfr2Mem', hidx2, region2, hlookup2', hstart2⟩
      · have hheap_eq : cfg'.heap = cfg.heap := by rw [hcfg']
        obtain ⟨fr2D', hfr2D'Mem, hidx2D', hrid2D', _⟩ := varAsgn_corollary_frame_transport_up h fr2 hfr2
        refine Or.inr ⟨fr2D', hfr2D'Mem, ?_, region2, ?_, hstart2⟩
        · rw [hidx2D', hidx2]
        · rw [hrid2D', hheap_eq]; exact hlookup2
  have hrtg2Up : Relation.ReflTransGen (RefStep cfg') start2 (Reference.OId oid) :=
    hrtg2.mono (fun a b hab => (hRefStepIff a b).mp hab)
  rw [FrameReferencable_iff_reflTransGen, ← hidxD]
  exact ⟨start2, hrootUp, hrtg2Up⟩

theorem varAsgn_reachable_valid : ValidReachableConfig cfg →
  varAsgn xf y cfg = some cfg' →
  ValidReachableConfig cfg' := by
  intro vrcfg h
  exact { varAsgn_valid vrcfg.toValidConfig h with cr3 := varAsgn_cr3 vrcfg h }
