import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Theorems
import Gc.Model.Mutation

theorem makeObjStack_L1 : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  L1 cfg' := by
  sorry

theorem makeObjStack_L2 : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  L2 cfg' := by
  sorry

theorem makeObjStack_H1 : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  H1 cfg' := by
  sorry

theorem makeObjStack_H2 : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  H2 cfg' := by
  sorry

theorem makeObjStack_H3 : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  H3 cfg' := by
  sorry

theorem makeObjStack_S1 : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  S1 cfg' := by
  sorry

theorem makeObjStack_S2 : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  S2 cfg' := by
  sorry

theorem makeObjStack_S3 : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  S3 cfg' := by
  sorry

theorem makeObjStack_valid : ValidConfig cfg →
  makeObjStack x cfg = some cfg' →
  ValidConfig cfg' := by
  intro vcfg h
  exact {
    l1 := makeObjStack_L1 vcfg h,
    l2 := makeObjStack_L2 vcfg h,
    h1 := makeObjStack_H1 vcfg h,
    h2 := makeObjStack_H2 vcfg h,
    h3 := makeObjStack_H3 vcfg h,
    s1 := makeObjStack_S1 vcfg h,
    s2 := makeObjStack_S2 vcfg h,
    s3 := makeObjStack_S3 vcfg h
  }
