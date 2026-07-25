import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Theorems
import Gc.Model.Mutation

theorem swap_L1 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  L1 cfg' := by
  sorry

theorem swap_L2 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  L2 cfg' := by
  sorry

theorem swap_H1 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  H1 cfg' := by
  sorry

theorem swap_H2 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  H2 cfg' := by
  sorry

theorem swap_H3 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  H3 cfg' := by
  sorry

theorem swap_S1 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  S1 cfg' := by
  sorry

theorem swap_S2 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  S2 cfg' := by
  sorry

theorem swap_S3 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  S3 cfg' := by
  sorry

theorem swap_HS1 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  HS1 cfg' := by
  sorry

theorem swap_HS2 : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  HS2 cfg' := by
  sorry

theorem swap_valid : ValidConfig cfg →
  swap x yf cfg = some cfg' →
  ValidConfig cfg' := by
  intro vcfg h
  exact {
    l1 := swap_L1 vcfg h,
    l2 := swap_L2 vcfg h,
    h1 := swap_H1 vcfg h,
    h2 := swap_H2 vcfg h,
    h3 := swap_H3 vcfg h,
    s1 := swap_S1 vcfg h,
    s2 := swap_S2 vcfg h,
    s3 := swap_S3 vcfg h,
    hs1 := swap_HS1 vcfg h,
    hs2 := swap_HS2 vcfg h
  }
