import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Theorems
import Gc.Model.Mutation

theorem makeRegion_L1 : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  L1 cfg' := by
  sorry

theorem makeRegion_L2 : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  L2 cfg' := by
  sorry

theorem makeRegion_H1 : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  H1 cfg' := by
  sorry

theorem makeRegion_H2 : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  H2 cfg' := by
  sorry

theorem makeRegion_H3 : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  H3 cfg' := by
  sorry

theorem makeRegion_S1 : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  S1 cfg' := by
  sorry

theorem makeRegion_S2 : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  S2 cfg' := by
  sorry

theorem makeRegion_S3 : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  S3 cfg' := by
  sorry

theorem makeRegion_HS1 : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  HS1 cfg' := by
  sorry

theorem makeRegion_valid : ValidConfig cfg →
  makeRegion x cfg = some cfg' →
  ValidConfig cfg' := by
  intro vcfg h
  exact {
    l1 := makeRegion_L1 vcfg h,
    l2 := makeRegion_L2 vcfg h,
    h1 := makeRegion_H1 vcfg h,
    h2 := makeRegion_H2 vcfg h,
    h3 := makeRegion_H3 vcfg h,
    s1 := makeRegion_S1 vcfg h,
    s2 := makeRegion_S2 vcfg h,
    s3 := makeRegion_S3 vcfg h,
    hs1 := makeRegion_HS1 vcfg h
  }
