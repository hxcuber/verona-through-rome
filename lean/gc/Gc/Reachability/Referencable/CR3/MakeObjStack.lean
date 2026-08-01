import Gc.Reachability.Referencable.Basic
import Gc.Reachability.Referencable.Lemmas

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
