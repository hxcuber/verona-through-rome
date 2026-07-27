import Gc.Model.Mutation
import Gc.Model.Preservation.MakeRegion
import Gc.Reachability.Validity.Reachable

theorem makeRegion_cr3 : ValidReachableConfig cfg →
  makeRegion x cfg = some cfg' →
  CR3 cfg' := by
  sorry

theorem makeRegion_reachable_valid : ValidReachableConfig cfg →
  makeRegion x cfg = some cfg' →
  ValidReachableConfig cfg' := by
  intro vrcfg h
  exact { makeRegion_valid vrcfg.toValidConfig h with cr3 := makeRegion_cr3 vrcfg h }
