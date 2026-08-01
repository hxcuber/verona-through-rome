import Gc.Reachability.Referencable.Basic
import Gc.Reachability.Referencable.Lemmas

theorem makeObjRegion_cr3 : ValidReachableConfig cfg →
  makeObjRegion x cfg = some cfg' →
  CR3 cfg' := by
  intro vrcfg h
  have vcfg := vrcfg.toValidConfig
  have vcfg' := makeObjRegion_valid vcfg h
  obtain ⟨frame1, region1, hframe1Last, hheapLookup1, hregion1Open, hcfg'⟩ := makeObjRegion_cases h
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame1] := (List.dropLast_append_getLast? frame1 hframe1Last).symm
  set newFrame1 : Frame :=
    { regionId := frame1.regionId, bridgeVar := frame1.bridgeVar, objMap := frame1.objMap,
      varMap := AList.insert x (Reference.OId cfg.freshObjectId) frame1.varMap } with newFrame1_def
  set newRegion1 : Region :=
    { region1 with objMap := AList.insert cfg.freshObjectId ∅ region1.objMap } with newRegion1_def
  have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq]; simp
  have hlen' : cfg'.stack.length = cfg.stack.dropLast.length + 1 := by rw [hcfg']; simp
  have hheap_eq : cfg'.heap.lookup frame1.regionId = some newRegion1 := by
    rw [hcfg']; dsimp only
    exact AList.lookup_insert (a := frame1.regionId) (b := newRegion1) cfg.heap
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
  have hheap_eq_at : ∀ rid, rid ≠ frame1.regionId → cfg'.heap.lookup rid = cfg.heap.lookup rid := by
    intro rid hrid
    rw [hcfg']; dsimp only; exact AList.lookup_insert_ne hrid
  have frameRoot_iff_nonlast : ∀ fid : Index, fid < cfg.stack.dropLast.length →
      ∀ start, FrameRoot cfg fid start ↔ FrameRoot cfg' fid start := by
    intro fid hfid start
    unfold FrameRoot
    constructor
    · rintro (⟨fr, hfr, hidx, var, hlookup⟩ | ⟨fr, hfr, hidx, region, hlookup, hstart⟩)
      · exact Or.inl ⟨fr, frame_transport_up fr hfr (hidx ▸ hfid), hidx, var, hlookup⟩
      · right
        by_cases hrideq : fr.regionId = frame1.regionId
        · -- fr is the region-owning frame: region = region1 (old), and bridgeObjectId is
          -- preserved by the mutation, so newRegion1 is the matching cfg'-side witness.
          rw [hrideq, hheapLookup1] at hlookup
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
  unfold CR3
  intro frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  -- `frame` can never be the mutated (last, highest-index) position (same index-ordering argument
  -- as makeObjStack: no index exceeds the unchanged stack length).
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
  have hframe1_get : cfg.stack[cfg.stack.dropLast.length]? = some frame1 := by
    conv_lhs => rw [stack_eq]
    simp
  have hlast1_mem :
      ({ frame1 with index := cfg.stack.dropLast.length } : FrameWithIndex) ∈ cfg.stackWithIndex := by
    obtain ⟨hh1, hheq⟩ := List.getElem?_eq_some_iff.mp hframe1_get
    unfold RuntimeConfig.stackWithIndex
    exact List.mem_mapIdx.mpr ⟨cfg.stack.dropLast.length, hh1, by rw [hheq]⟩
  -- `oid` can never be the freshly-allocated object: if it were, `hloc` would force `frame` to
  -- share `frame1`'s regionId (S1-uniqueness), hence share `frame1`'s (highest possible) index --
  -- contradicting `hframe_lt_dropLast`.
  have hoid_ne_fresh : oid ≠ cfg.freshObjectId := by
    intro heq
    rw [heq] at hloc
    obtain ⟨frame0, hlast0, hlocfresh0⟩ := makeObjRegion_corollary_loc_fresh vcfg h
    rw [hlocfresh0] at hloc
    injection hloc with hloc'
    injection hloc' with hloc''
    have hframe1eq : frame0 = frame1 := by rw [hlast0] at hframe1Last; injection hframe1Last
    have hridF : frame.regionId = ({ frame1 with index := cfg.stack.dropLast.length } : FrameWithIndex).regionId := by
      show frame.regionId = frame1.regionId
      rw [← hloc'', hframe1eq]
    have hidxeq := merge_corollary_regionId_unique_index vcfg.s1 hframeMemCfg hlast1_mem hridF
    dsimp only at hidxeq
    exact Nat.lt_irrefl _ (hidxeq ▸ hframe_lt_dropLast)
  have hlocDown : (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) := by
    rw [makeObjRegion_corollary_loc_eq vcfg h oid hoid_ne_fresh]; exact hloc
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
        exact makeObjRegion_corollary_refStep_source_ne_fresh_cfg' vcfg h hstep0 (by rw [hc])
    rw [hstart_eq] at hroot hrtg
    have hroot_down : FrameRoot cfg frame'.index (Reference.OId start_oid) :=
      makeObjRegion_corollary_frameRoot_down vcfg h hstart_ne_fresh hroot
    have hrtg_down : Relation.ReflTransGen (RefStep cfg) (Reference.OId start_oid) (Reference.OId oid) :=
      hrtg.mono (fun a b hab => (makeObjRegion_corollary_refStep_iff vcfg vcfg' h a b).mpr hab)
    have hreachDown : FrameReferencable cfg frame'.index (Reference.OId oid) :=
      (FrameReferencable_iff_reflTransGen cfg frame'.index (Reference.OId oid)).mpr
        ⟨Reference.OId start_oid, hroot_down, hrtg_down⟩
    have hlt' : frame.index < ({ frame1 with index := cfg.stack.dropLast.length } : FrameWithIndex).index := by
      dsimp only; rw [← hframe'Last]; exact hlt
    have hreachDown' :
        FrameReferencable cfg ({ frame1 with index := cfg.stack.dropLast.length } : FrameWithIndex).index
          (Reference.OId oid) := by
      dsimp only; rw [← hframe'Last]; exact hreachDown
    have hconcDown : FrameReferencable cfg frame.index (Reference.OId oid) :=
      vrcfg.cr3 frame hframeMemCfg { frame1 with index := cfg.stack.dropLast.length } hlast1_mem
        hlt' oid hlocDown hreachDown'
    rw [FrameReferencable_iff_reflTransGen] at hconcDown ⊢
    obtain ⟨start2, hroot2, hrtg2⟩ := hconcDown
    exact ⟨start2, (frameRoot_iff_nonlast frame.index hframe_lt_dropLast start2).mp hroot2,
      hrtg2.mono (fun a b hab => (makeObjRegion_corollary_refStep_iff vcfg vcfg' h a b).mp hab)⟩
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
        hrtg.mono (fun a b hab => (makeObjRegion_corollary_refStep_iff vcfg vcfg' h a b).mpr hab)⟩
    have hconcDown : FrameReferencable cfg frame.index (Reference.OId oid) :=
      vrcfg.cr3 frame hframeMemCfg frame' hframe'MemCfg hlt oid hlocDown hreachDown
    rw [FrameReferencable_iff_reflTransGen] at hconcDown ⊢
    obtain ⟨start2, hroot2, hrtg2⟩ := hconcDown
    exact ⟨start2, (frameRoot_iff_nonlast frame.index hframe_lt_dropLast start2).mp hroot2,
      hrtg2.mono (fun a b hab => (makeObjRegion_corollary_refStep_iff vcfg vcfg' h a b).mp hab)⟩

theorem makeObjRegion_reachable_valid : ValidReachableConfig cfg →
  makeObjRegion x cfg = some cfg' →
  ValidReachableConfig cfg' := by
  intro vrcfg h
  exact { makeObjRegion_valid vrcfg.toValidConfig h with cr3 := makeObjRegion_cr3 vrcfg h }
