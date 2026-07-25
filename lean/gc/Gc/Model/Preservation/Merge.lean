import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Theorems
import Gc.Model.Mutation

theorem merge_L1 : ValidConfig cfg →
  merge x cfg = some cfg' →
  L1 cfg' := by
  sorry

theorem merge_L2 : ValidConfig cfg →
  merge x cfg = some cfg' →
  L2 cfg' := by
  sorry

theorem merge_H1 : ValidConfig cfg →
  merge x cfg = some cfg' →
  H1 cfg' := by
  sorry

theorem merge_H2 : ValidConfig cfg →
  merge x cfg = some cfg' →
  H2 cfg' := by
  sorry

theorem merge_H3 : ValidConfig cfg →
  merge x cfg = some cfg' →
  H3 cfg' := by
  sorry

theorem merge_S1 : ValidConfig cfg →
  merge x cfg = some cfg' →
  S1 cfg' := by
  sorry

theorem merge_S2 : ValidConfig cfg →
  merge x cfg = some cfg' →
  S2 cfg' := by
  sorry

theorem merge_S3 : ValidConfig cfg →
  merge x cfg = some cfg' →
  S3 cfg' := by
  sorry

theorem merge_HS1 : ValidConfig cfg →
  merge x cfg = some cfg' →
  HS1 cfg' := by
  sorry

theorem merge_HS2 : ValidConfig cfg →
  merge x cfg = some cfg' →
  HS2 cfg' := by
  sorry

theorem merge_valid : ValidConfig cfg →
  merge x cfg = some cfg' →
  ValidConfig cfg' := by
  intro vcfg h
  exact {
    l1 := merge_L1 vcfg h,
    l2 := merge_L2 vcfg h,
    h1 := merge_H1 vcfg h,
    h2 := merge_H2 vcfg h,
    h3 := merge_H3 vcfg h,
    s1 := merge_S1 vcfg h,
    s2 := merge_S2 vcfg h,
    s3 := merge_S3 vcfg h,
    hs1 := merge_HS1 vcfg h,
    hs2 := merge_HS2 vcfg h
  }
