import Gc.Model.Mutation
import Gc.Model.Preservation.Enter
import Gc.Reachability.Validity.Reachable

theorem enter_cr3 : ValidReachableConfig cfg →
  enter xf a cfg = some cfg' →
  CR3 cfg' := by
  sorry

theorem enter_reachable_valid : ValidReachableConfig cfg →
  enter xf a cfg = some cfg' →
  ValidReachableConfig cfg' := by
  intro vrcfg h
  exact { enter_valid vrcfg.toValidConfig h with cr3 := enter_cr3 vrcfg h }
