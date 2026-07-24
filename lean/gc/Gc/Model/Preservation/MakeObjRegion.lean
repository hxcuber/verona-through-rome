import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Theorems
import Gc.Model.Mutation

theorem makeObjRegion_L1 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  L1 cfg' := by
  sorry

theorem makeObjRegion_L2 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  L2 cfg' := by
  sorry

theorem makeObjRegion_H1 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  H1 cfg' := by
  sorry

theorem makeObjRegion_H2 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  H2 cfg' := by
  sorry

theorem makeObjRegion_H3 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  H3 cfg' := by
  sorry

theorem makeObjRegion_S1 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  S1 cfg' := by
  sorry

theorem makeObjRegion_S2 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  S2 cfg' := by
  sorry

theorem makeObjRegion_S3 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  S3 cfg' := by
  sorry

theorem makeObjRegion_HS1 : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  HS1 cfg' := by
  sorry

theorem makeObjRegion_valid : ValidConfig cfg →
  makeObjRegion x cfg = some cfg' →
  ValidConfig cfg' := by
  intro vcfg h
  exact {
    l1 := makeObjRegion_L1 vcfg h,
    l2 := makeObjRegion_L2 vcfg h,
    h1 := makeObjRegion_H1 vcfg h,
    h2 := makeObjRegion_H2 vcfg h,
    h3 := makeObjRegion_H3 vcfg h,
    s1 := makeObjRegion_S1 vcfg h,
    s2 := makeObjRegion_S2 vcfg h,
    s3 := makeObjRegion_S3 vcfg h,
    hs1 := makeObjRegion_HS1 vcfg h
  }
