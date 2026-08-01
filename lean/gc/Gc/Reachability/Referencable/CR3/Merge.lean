import Gc.Reachability.Referencable.Basic
import Gc.Reachability.Referencable.Lemmas

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
  -- `RegionReferencable cfg rid' oid`, hence `oid.loc? cfg = Rgn rid'` -- contradicting `hlocDown`
  -- (which pins it at `frame.regionId ≠ rid'`).
  have hno_chain_from_region' :
      ¬ Relation.ReflTransGen (RefStep cfg') (Reference.OId region'.bridgeObjectId) (Reference.OId oid) := by
    intro hchain
    have hchain_cfg : Relation.ReflTransGen (RefStep cfg) (Reference.OId region'.bridgeObjectId) (Reference.OId oid) :=
      hchain.mono (fun a b hab => (merge_corollary_refStep_iff vcfg h a b).mpr hab)
    have hregReach : RegionReferencable cfg rid' (Reference.OId oid) :=
      (RegionReferencable_iff_reflTransGen cfg rid' (Reference.OId oid)).mpr ⟨region', hregion', hchain_cfg⟩
    have hloc_rid' := RegionReferencable_stays_in_region vcfg hregReach
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
  rw [FrameReferencable_iff_reflTransGen] at hreach
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
  have hreachDown : FrameReferencable cfg frame'.index (Reference.OId oid) :=
    (FrameReferencable_iff_reflTransGen cfg frame'.index (Reference.OId oid)).mpr
      ⟨Reference.OId start_oid, hroot_down, hrtg_down⟩
  -- Construct the cfg-side witness for `frame'` (last vs non-last), apply `vrcfg.cr3`, transport
  -- the conclusion back up through `frame`'s own untouched position.
  by_cases hframe'Last : frame'.index = cfg.stack.dropLast.length
  · have hlt' : frame.index < ({ frame1 with index := cfg.stack.dropLast.length } : FrameWithIndex).index := by
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
    exact ⟨start2, frameRoot_up_frame start2 hroot2,
      hrtg2.mono (fun a b hab => (merge_corollary_refStep_iff vcfg h a b).mp hab)⟩
  · have hframe'_lt_dropLast : frame'.index < cfg.stack.dropLast.length := by
      have hframe'_lt2 : frame'.index < cfg.stack.dropLast.length + 1 := by
        rw [← hlen']; exact hframe'_lt
      exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hframe'_lt2) hframe'Last
    have hframe'MemCfg : frame' ∈ cfg.stackWithIndex :=
      frame_transport_down frame' hframe'Mem hframe'_lt_dropLast
    have hconcDown : FrameReferencable cfg frame.index (Reference.OId oid) :=
      vrcfg.cr3 frame hframeMemCfg frame' hframe'MemCfg hlt oid hlocDown hreachDown
    rw [FrameReferencable_iff_reflTransGen] at hconcDown ⊢
    obtain ⟨start2, hroot2, hrtg2⟩ := hconcDown
    exact ⟨start2, frameRoot_up_frame start2 hroot2,
      hrtg2.mono (fun a b hab => (merge_corollary_refStep_iff vcfg h a b).mp hab)⟩

theorem merge_reachable_valid : ValidReachableConfig cfg →
  merge x cfg = some cfg' →
  ValidReachableConfig cfg' := by
  intro vrcfg h
  exact { merge_valid vrcfg.toValidConfig h with cr3 := merge_cr3 vrcfg h }
