import Gc.Model.Mutation
import Gc.Model.Preservation.Exit
import Gc.Reachability.Validity.Reachable

theorem exit_cr3 : ValidReachableConfig cfg →
  exit cfg = some cfg' →
  CR3 cfg' := by
  sorry

theorem exit_reachable_valid : ValidReachableConfig cfg →
  exit cfg = some cfg' →
  ValidReachableConfig cfg' := by
  intro vrcfg h
  exact { exit_valid vrcfg.toValidConfig h with cr3 := exit_cr3 vrcfg h }
