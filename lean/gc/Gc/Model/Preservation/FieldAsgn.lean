import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Theorems
import Gc.Model.Mutation

theorem fieldAsgn_L1 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  L1 cfg' := by
  sorry

theorem fieldAsgn_L2 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  L2 cfg' := by
  sorry

theorem fieldAsgn_H1 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  H1 cfg' := by
  sorry

theorem fieldAsgn_H2 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  H2 cfg' := by
  sorry

theorem fieldAsgn_H3 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  H3 cfg' := by
  sorry

theorem fieldAsgn_S1 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  S1 cfg' := by
  sorry

theorem fieldAsgn_S2 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  S2 cfg' := by
  sorry

theorem fieldAsgn_S3 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  S3 cfg' := by
  sorry

theorem fieldAsgn_HS1 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  HS1 cfg' := by
  sorry

theorem fieldAsgn_HS2 : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  HS2 cfg' := by
  sorry

theorem fieldAsgn_valid : ValidConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  ValidConfig cfg' := by
  intro vcfg h
  exact {
    l1 := fieldAsgn_L1 vcfg h,
    l2 := fieldAsgn_L2 vcfg h,
    h1 := fieldAsgn_H1 vcfg h,
    h2 := fieldAsgn_H2 vcfg h,
    h3 := fieldAsgn_H3 vcfg h,
    s1 := fieldAsgn_S1 vcfg h,
    s2 := fieldAsgn_S2 vcfg h,
    s3 := fieldAsgn_S3 vcfg h,
    hs1 := fieldAsgn_HS1 vcfg h,
    hs2 := fieldAsgn_HS2 vcfg h
  }
