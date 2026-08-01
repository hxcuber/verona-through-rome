import Gc.Reachability.Referencable.Basic
import Gc.Reachability.Referencable.Lemmas

theorem enter_cr3 : ValidReachableConfig cfg →
  enter xf a cfg = some cfg' →
  CR3 cfg' := by
  intro vrcfg h
  have vcfg := vrcfg.toValidConfig
  have vcfg' := enter_valid vcfg h
  obtain ⟨rid, region, _, hlookupRid, hclosed, hcfg'⟩ := enter_cases h
  unfold CR3
  intro frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  -- `frame` is always an old frame: nothing in cfg'.stackWithIndex has index > cfg.stack.length,
  -- so `frame.index < frame'.index` rules out `frame` being the newly-pushed one.
  have hframeCases := enter_corollary_stackWithIndex_cases rid region hcfg' frame hframeMem
  have hframe'Cases := enter_corollary_stackWithIndex_cases rid region hcfg' frame' hframe'Mem
  have hframeOld : frame ∈ cfg.stackWithIndex := by
    rcases hframeCases with hold | hnew
    · exact hold
    · exfalso
      rcases hframe'Cases with hold' | hnew'
      · have hcontra := hlt.trans (enter_corollary_mem_index_lt hold')
        rw [hnew] at hcontra
        exact absurd hcontra (lt_irrefl _)
      · rw [hnew, hnew'] at hlt
        exact absurd hlt (lt_irrefl _)
  clear hframeCases
  -- `frame'` is either an old frame, or exactly the newly-pushed one.
  rcases hframe'Cases with hframe'Old | hframe'New
  · -- Old/old case: transport everything down to `cfg`, apply `vrcfg.cr3`, transport back up.
    have hlocDown : (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) := by
      rw [enter_corollary_2 vcfg h oid]; exact hloc
    have hreachDown : FrameReferencable cfg frame'.index (Reference.OId oid) :=
      (enter_corollary_frameReferencable_iff vcfg vcfg' h frame' hframe'Old (Reference.OId oid)).mpr hreach
    have hconcDown : FrameReferencable cfg frame.index (Reference.OId oid) :=
      vrcfg.cr3 frame hframeOld frame' hframe'Old hlt oid hlocDown hreachDown
    exact (enter_corollary_frameReferencable_iff vcfg vcfg' h frame hframeOld (Reference.OId oid)).mp hconcDown
  · -- `frame'` is the fresh, empty frame: its only possible root is its own region's bridge
    -- object, giving `RegionReferencable cfg' rid oid`, forcing `oid`'s region to be `rid` --
    -- contradicting `frame.regionId ≠ rid` (frame is old) together with `hloc`'s region `frame.regionId`.
    exfalso
    rw [FrameReferencable_iff_reflTransGen] at hreach
    obtain ⟨start, hroot, hrtg⟩ := hreach
    have hnewFrameWI : ({ regionId := rid, bridgeVar := a, objMap := ∅, varMap := ∅, index := cfg.stack.length } :
        FrameWithIndex) ∈ cfg'.stackWithIndex := by
      rw [hcfg']
      unfold RuntimeConfig.stackWithIndex
      dsimp only
      rw [List.mapIdx_concat]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    have hframe'eq : frame' = { regionId := rid, bridgeVar := a, objMap := ∅, varMap := ∅, index := cfg.stack.length } :=
      swap_corollary_stackWithIndex_index_inj hframe'Mem hnewFrameWI (by rw [hframe'New])
    unfold FrameRoot at hroot
    rw [hframe'eq] at hroot
    dsimp only at hroot
    rcases hroot with ⟨frame1, hframe1, hidx1, var, hlookup1⟩ | ⟨frame1, hframe1, hidx1, region1, hlookup1, hstart⟩
    · have heq1 : frame1 = { regionId := rid, bridgeVar := a, objMap := ∅, varMap := ∅, index := cfg.stack.length } :=
        swap_corollary_stackWithIndex_index_inj hframe1 hnewFrameWI hidx1
      rw [heq1] at hlookup1
      dsimp only at hlookup1
      exact absurd hlookup1 (by simp)
    · have heq1 : frame1 = { regionId := rid, bridgeVar := a, objMap := ∅, varMap := ∅, index := cfg.stack.length } :=
        swap_corollary_stackWithIndex_index_inj hframe1 hnewFrameWI hidx1
      rw [heq1] at hlookup1
      dsimp only at hlookup1
      rw [hcfg'] at hlookup1
      dsimp only at hlookup1
      rw [AList.lookup_insert] at hlookup1
      injection hlookup1 with hregion1_eq
      have hstart_eq : start = Reference.OId region.bridgeObjectId := by rw [hstart, ← hregion1_eq]
      have hlookup1open : cfg'.heap.lookup rid = some { region with status := Status.Open } := by
        rw [hcfg']; dsimp only; rw [AList.lookup_insert]
      rw [hstart_eq] at hrtg
      have hoidReach : RegionReferencable cfg' rid (Reference.OId oid) :=
        (RegionReferencable_iff_reflTransGen cfg' rid (Reference.OId oid)).mpr
          ⟨{ region with status := Status.Open }, hlookup1open, hrtg⟩
      have hoidLoc := RegionReferencable_stays_in_region vcfg' hoidReach
      rw [hoidLoc, Option.some.injEq, Location.Rgn.injEq] at hloc
      exact enter_corollary_regionId_ne vcfg rid region hclosed hlookupRid frame hframeOld hloc.symm

theorem enter_reachable_valid : ValidReachableConfig cfg →
  enter xf a cfg = some cfg' →
  ValidReachableConfig cfg' := by
  intro vrcfg h
  exact { enter_valid vrcfg.toValidConfig h with cr3 := enter_cr3 vrcfg h }
