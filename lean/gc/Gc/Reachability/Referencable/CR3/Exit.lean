import Gc.Reachability.Referencable.Basic
import Gc.Reachability.Referencable.Lemmas

theorem exit_cr3 : ValidReachableConfig cfg →
  exit cfg = some cfg' →
  CR3 cfg' := by
  intro vrcfg h
  have vcfg := vrcfg.toValidConfig
  have vcfg' := exit_valid vcfg h
  obtain ⟨poppedFrame, region, hlen, hlast, hlookupPopped, hopenPopped, hcfg'⟩ := exit_cases h
  unfold CR3
  intro frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  have hframeOld : frame ∈ cfg.stackWithIndex := exit_corollary_frame_old hlast (by rw [hcfg']) frame hframeMem
  have hframe'Old : frame' ∈ cfg.stackWithIndex := exit_corollary_frame_old hlast (by rw [hcfg']) frame' hframe'Mem
  have hlocDown : (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) :=
    (exit_corollary_1 vcfg h (Reference.OId oid)).mpr hloc
  have hreachDown : FrameReferencable cfg frame'.index (Reference.OId oid) :=
    (exit_corollary_frameReferencable_iff vcfg vcfg' h frame' hframe'Mem (Reference.OId oid)).mpr hreach
  have hconcDown : FrameReferencable cfg frame.index (Reference.OId oid) :=
    vrcfg.cr3 frame hframeOld frame' hframe'Old hlt oid hlocDown hreachDown
  exact (exit_corollary_frameReferencable_iff vcfg vcfg' h frame hframeMem (Reference.OId oid)).mp hconcDown

theorem exit_reachable_valid : ValidReachableConfig cfg →
  exit cfg = some cfg' →
  ValidReachableConfig cfg' := by
  intro vrcfg h
  exact { exit_valid vrcfg.toValidConfig h with cr3 := exit_cr3 vrcfg h }
