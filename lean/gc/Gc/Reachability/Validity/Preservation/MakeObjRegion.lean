import Gc.Model.Mutation
import Gc.Model.Preservation.MakeObjRegion
import Gc.Reachability.Validity.Reachable

theorem makeObjRegion_cr3 : ValidReachableConfig cfg →
  makeObjRegion x cfg = some cfg' →
  CR3 cfg' := by
  sorry

theorem makeObjRegion_reachable_valid : ValidReachableConfig cfg →
  makeObjRegion x cfg = some cfg' →
  ValidReachableConfig cfg' := by
  intro vrcfg h
  exact { makeObjRegion_valid vrcfg.toValidConfig h with cr3 := makeObjRegion_cr3 vrcfg h }
