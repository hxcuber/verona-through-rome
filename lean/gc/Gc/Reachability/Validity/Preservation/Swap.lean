import Gc.Model.Mutation
import Gc.Model.Preservation.Swap
import Gc.Reachability.Validity.Reachable

theorem swap_cr3 : ValidReachableConfig cfg →
  swap x yf cfg = some cfg' →
  CR3 cfg' := by
  sorry

theorem swap_reachable_valid : ValidReachableConfig cfg →
  swap x yf cfg = some cfg' →
  ValidReachableConfig cfg' := by
  intro vrcfg h
  exact { swap_valid vrcfg.toValidConfig h with cr3 := swap_cr3 vrcfg h }
