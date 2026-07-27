import Gc.Model.Mutation
import Gc.Model.Preservation.FieldAsgn
import Gc.Reachability.Validity.Reachable

theorem fieldAsgn_cr3 : ValidReachableConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  CR3 cfg' := by
  sorry

theorem fieldAsgn_reachable_valid : ValidReachableConfig cfg →
  fieldAsgn x yf cfg = some cfg' →
  ValidReachableConfig cfg' := by
  intro vrcfg h
  exact { fieldAsgn_valid vrcfg.toValidConfig h with cr3 := fieldAsgn_cr3 vrcfg h }
