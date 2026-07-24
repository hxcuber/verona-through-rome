import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Theorems
import Gc.Model.Mutation

theorem varAsgn_L1 : ValidConfig cfg →
  varAsgn xf y cfg = some cfg' →
  L1 cfg' := by
  sorry

theorem varAsgn_L2 : ValidConfig cfg →
  varAsgn xf y cfg = some cfg' →
  L2 cfg' := by
  sorry

theorem varAsgn_H1 : ValidConfig cfg →
  varAsgn xf y cfg = some cfg' →
  H1 cfg' := by
  sorry

theorem varAsgn_H2 : ValidConfig cfg →
  varAsgn xf y cfg = some cfg' →
  H2 cfg' := by
  sorry

theorem varAsgn_H3 : ValidConfig cfg →
  varAsgn xf y cfg = some cfg' →
  H3 cfg' := by
  sorry

theorem varAsgn_S1 : ValidConfig cfg →
  varAsgn xf y cfg = some cfg' →
  S1 cfg' := by
  sorry

theorem varAsgn_S2 : ValidConfig cfg →
  varAsgn xf y cfg = some cfg' →
  S2 cfg' := by
  sorry

theorem varAsgn_S3 : ValidConfig cfg →
  varAsgn xf y cfg = some cfg' →
  S3 cfg' := by
  sorry

theorem varAsgn_valid : ValidConfig cfg →
  varAsgn xf y cfg = some cfg' →
  ValidConfig cfg' := by
  intro vcfg h
  exact {
    l1 := varAsgn_L1 vcfg h,
    l2 := varAsgn_L2 vcfg h,
    h1 := varAsgn_H1 vcfg h,
    h2 := varAsgn_H2 vcfg h,
    h3 := varAsgn_H3 vcfg h,
    s1 := varAsgn_S1 vcfg h,
    s2 := varAsgn_S2 vcfg h,
    s3 := varAsgn_S3 vcfg h
  }
