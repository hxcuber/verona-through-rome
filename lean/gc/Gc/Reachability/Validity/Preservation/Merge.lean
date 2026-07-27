import Gc.Model.Mutation
import Gc.Model.Preservation.Merge
import Gc.Reachability.Validity.Reachable

theorem merge_cr3 : ValidReachableConfig cfg →
  merge x cfg = some cfg' →
  CR3 cfg' := by
  sorry

theorem merge_reachable_valid : ValidReachableConfig cfg →
  merge x cfg = some cfg' →
  ValidReachableConfig cfg' := by
  intro vrcfg h
  exact { merge_valid vrcfg.toValidConfig h with cr3 := merge_cr3 vrcfg h }
