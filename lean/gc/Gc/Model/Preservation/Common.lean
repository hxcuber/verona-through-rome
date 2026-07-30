import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Theorems

import Mathlib.Data.List.Infix

-- Generic, non-operation-specific facts reused across several `Preservation` files (both the
-- `Gc/Model/Preservation/*.lean` layer and `Gc/Reachability/Referencable/Validity/Preservation/*.lean`'s CR3
-- layer). Each of these originally lived in whichever operation's own file first needed it
-- (`heap_objectIds_of_mem` in `Exit.lean`, the `stackWithIndex` pair in `Swap.lean`,
-- `regionId_unique_index` in `Merge.lean`), which meant unrelated operations had to import that
-- operation's entire preservation file just to borrow one generic lemma. Consolidated here once
-- all 9 `Mutation.lean` operations' CR3 proofs were done and it was clear which facts are actually
-- shared (see CLAUDE.md's "Next planned step" section for the full rationale). Names kept
-- unchanged from their original per-operation files to avoid a mass rename across every call site.

-- A `heap.entries` membership witnessing `oid` inside some region's `objMap` puts `oid` in the
-- heap's own flattened `objectIds`.
theorem heap_objectIds_of_mem {heap : Heap} :
  (⟨rid, region⟩ : Sigma (fun _ : RegionId => Region)) ∈ heap.entries → oid ∈ region.objMap.keys →
  oid ∈ heap.objectIds := by
  intro mem in_region
  unfold Heap.objectIds
  apply List.mem_flatten.mpr
  refine ⟨region.objectIds, List.mem_map_of_mem (f := λ e => e.2.objectIds) mem, ?_⟩
  unfold Region.objectIds
  exact in_region

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

-- `S1`'s regionId-uniqueness at the `FrameWithIndex` level: two stack frames sharing a `regionId`
-- must be the *same* frame (same index).
theorem merge_corollary_regionId_unique_index {cfg : RuntimeConfig} (s1 : S1 cfg)
    {frameZ frameW : FrameWithIndex} (hZ : frameZ ∈ cfg.stackWithIndex) (hW : frameW ∈ cfg.stackWithIndex)
    (heq : frameZ.regionId = frameW.regionId) : frameZ.index = frameW.index := by
  unfold RuntimeConfig.stackWithIndex at hZ hW
  obtain ⟨nZ, hnZ, hZeq⟩ := List.mem_mapIdx.mp hZ
  obtain ⟨nW, hnW, hWeq⟩ := List.mem_mapIdx.mp hW
  have hZidx : frameZ.index = nZ := by rw [← hZeq]
  have hWidx : frameW.index = nW := by rw [← hWeq]
  have hZregion : frameZ.regionId = cfg.stack[nZ].regionId := by rw [← hZeq]
  have hWregion : frameW.regionId = cfg.stack[nW].regionId := by rw [← hWeq]
  unfold S1 at s1
  have hnZ' : nZ < (cfg.stack.map (fun f => f.regionId)).length := by rwa [List.length_map]
  have hnW' : nW < (cfg.stack.map (fun f => f.regionId)).length := by rwa [List.length_map]
  have hgetZ : (cfg.stack.map (fun f => f.regionId))[nZ] = frameZ.regionId := by
    rw [List.getElem_map]; rw [hZregion]
  have hgetW : (cfg.stack.map (fun f => f.regionId))[nW] = frameW.regionId := by
    rw [List.getElem_map]; rw [hWregion]
  have : nZ = nW := by
    apply (List.Nodup.getElem_inj_iff s1 (hi := hnZ') (hj := hnW')).mp
    rw [hgetZ, hgetW, heq]
  rw [hZidx, hWidx, this]

-- The `.index` field of an element found by direct `stackWithIndex[fid]?` lookup always equals
-- the lookup index itself -- `.index` is assigned to be the element's own `mapIdx` position, so an
-- `[fid]?`-indexed lookup and the element's own `.index` necessarily agree. Fully generic (no
-- mutation/`ValidConfig` involved at all) -- previously three byte-for-byte-identical private
-- copies (`enter`/`exit`/`makeObjStack_corollary_getElem_index_eq`).
theorem stackWithIndex_getElem_index_eq {cfg : RuntimeConfig} {fid : Index} {frame : FrameWithIndex}
    (h : cfg.stackWithIndex[fid]? = some frame) : frame.index = fid := by
  unfold RuntimeConfig.stackWithIndex at h
  rw [List.getElem?_mapIdx, Option.map_eq_some_iff] at h
  obtain ⟨stackFrame, hfid, hframe_eq⟩ := h
  obtain ⟨fid_lt_length, stackFrame_eq⟩ := List.getElem?_eq_some_iff.mp hfid
  have frame_eq : ({cfg.stack[fid] with index := fid} : FrameWithIndex) = frame :=
    stackFrame_eq ▸ hframe_eq
  rw [← frame_eq]

-- If cfg/cfg' agree (as an `Option`-valued `Frame`-projection `proj`) at every stack position, any
-- `cfg'.stackWithIndex` membership transports down to a `cfg.stackWithIndex` member with the same
-- `.index` and the same `proj`-value. Fully generic over `proj` (e.g. `fun f => (f.regionId,
-- f.bridgeVar)`, or with `Frame.objMap`/`Frame.varMap` projected away entirely) -- previously
-- reconstructed per-operation as `varAsgn_corollary_frame_transport_down`/
-- `fieldAsgn_corollary_frame_transport_down`/`swap_corollary_frame_transport_down` (the `varAsgn`/
-- `swap` versions were byte-for-byte identical; `fieldAsgn`'s differed only in `proj`'s arity).
theorem stackWithIndex_frame_transport_down_of_shape_eq {cfg cfg' : RuntimeConfig} {α : Type*}
    {proj : Frame → α} (hshape : ∀ n : ℕ, (cfg.stack[n]?).map proj = (cfg'.stack[n]?).map proj)
    (fr : FrameWithIndex) (hfr : fr ∈ cfg'.stackWithIndex) :
    ∃ fr0 : FrameWithIndex, fr0 ∈ cfg.stackWithIndex ∧ fr0.index = fr.index ∧
      proj fr0.toFrame = proj fr.toFrame := by
  obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr
  have hidx_n : fr.index = n := by rw [← hfeq]
  have hget' : cfg'.stack[n]? = some fr.toFrame := by
    rw [show fr.toFrame = cfg'.stack[n] from by rw [← hfeq]]
    exact List.getElem?_eq_getElem hn
  have hmap_eq := hshape n
  rw [hget', Option.map_some] at hmap_eq
  obtain ⟨frameX, hframeX, hridX⟩ := Option.map_eq_some_iff.mp hmap_eq
  obtain ⟨hh1, heq⟩ := List.getElem?_eq_some_iff.mp hframeX
  refine ⟨{ frameX with index := n }, ?_, ?_, ?_⟩
  · unfold RuntimeConfig.stackWithIndex
    exact List.mem_mapIdx.mpr ⟨n, hh1, by rw [heq]⟩
  · rw [hidx_n]
  · exact hridX

-- Mirrors `stackWithIndex_frame_transport_down_of_shape_eq`, transporting membership the other way
-- (`cfg.stackWithIndex` member down to `cfg'.stackWithIndex`).
theorem stackWithIndex_frame_transport_up_of_shape_eq {cfg cfg' : RuntimeConfig} {α : Type*}
    {proj : Frame → α} (hshape : ∀ n : ℕ, (cfg.stack[n]?).map proj = (cfg'.stack[n]?).map proj)
    (fr : FrameWithIndex) (hfr : fr ∈ cfg.stackWithIndex) :
    ∃ fr0 : FrameWithIndex, fr0 ∈ cfg'.stackWithIndex ∧ fr0.index = fr.index ∧
      proj fr0.toFrame = proj fr.toFrame := by
  obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hfr
  have hidx_n : fr.index = n := by rw [← hfeq]
  have hget : cfg.stack[n]? = some fr.toFrame := by
    rw [show fr.toFrame = cfg.stack[n] from by rw [← hfeq]]
    exact List.getElem?_eq_getElem hn
  have hmap_eq := hshape n
  rw [hget, Option.map_some] at hmap_eq
  obtain ⟨frameX, hframeX, hridX⟩ := Option.map_eq_some_iff.mp hmap_eq.symm
  obtain ⟨hh1, heq⟩ := List.getElem?_eq_some_iff.mp hframeX
  refine ⟨{ frameX with index := n }, ?_, ?_, ?_⟩
  · unfold RuntimeConfig.stackWithIndex
    exact List.mem_mapIdx.mpr ⟨n, hh1, by rw [heq]⟩
  · rw [hidx_n]
  · exact hridX

-- If `cfg'` is `cfg` with its **last** frame's `varMap` replaced (everything else about that frame
-- -- `regionId`/`bridgeVar`/`objMap` -- untouched, and every other frame untouched), then `objMap`
-- is unaffected at every stack position. Fully generic over the new `varMap` value -- previously
-- reconstructed identically three times (`merge`/`makeObjRegion`/`makeRegion_corollary_
-- objMap_get_eq`), differing only in *which* reference got inserted (a fact this lemma's conclusion
-- never even mentions).
theorem stackWithIndex_objMap_get_eq_of_last_varMap_update {cfg cfg' : RuntimeConfig} {frame : Frame}
    {newVarMap : VarMap} (hframeLast : cfg.stack.getLast? = some frame)
    (hstack' : cfg'.stack = cfg.stack.dropLast ++
      [({ regionId := frame.regionId, bridgeVar := frame.bridgeVar, objMap := frame.objMap,
          varMap := newVarMap } : Frame)]) (n : ℕ) :
    (cfg.stack[n]?).map Frame.objMap = (cfg'.stack[n]?).map Frame.objMap := by
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
    (List.dropLast_append_getLast? frame hframeLast).symm
  set newFrame : Frame :=
    { regionId := frame.regionId, bridgeVar := frame.bridgeVar, objMap := frame.objMap,
      varMap := newVarMap } with newFrame_def
  by_cases hlp : n = cfg.stack.dropLast.length
  · have e1 : cfg.stack[n]? = some frame := by
      conv_lhs => rw [stack_eq, hlp]
      simp
    have e2 : cfg'.stack[n]? = some newFrame := by
      rw [hstack']; rw [hlp]
      simp
    rw [e1, e2]
    rfl
  · by_cases hlt : n < cfg.stack.dropLast.length
    · have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
        conv_lhs => rw [stack_eq]
        rw [List.getElem?_append_left hlt]
      have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
        rw [hstack']; rw [List.getElem?_append_left hlt]
      rw [e1, e2]
    · have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq]; simp
      have hlen' : cfg'.stack.length = cfg.stack.dropLast.length + 1 := by rw [hstack']; simp
      have e1 : cfg.stack[n]? = none := List.getElem?_eq_none (by omega)
      have e2 : cfg'.stack[n]? = none := List.getElem?_eq_none (by omega)
      rw [e1, e2]
