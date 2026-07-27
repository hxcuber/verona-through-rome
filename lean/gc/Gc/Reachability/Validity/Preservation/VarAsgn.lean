import Gc.Model.Mutation
import Gc.Model.Preservation.VarAsgn
import Gc.Reachability.Validity.Reachable

theorem varAsgn_cr3 : ValidReachableConfig cfg →
  varAsgn xf y cfg = some cfg' →
  CR3 cfg' := by
  sorry

theorem varAsgn_reachable_valid : ValidReachableConfig cfg →
  varAsgn xf y cfg = some cfg' →
  ValidReachableConfig cfg' := by
  intro vrcfg h
  exact { varAsgn_valid vrcfg.toValidConfig h with cr3 := varAsgn_cr3 vrcfg h }
