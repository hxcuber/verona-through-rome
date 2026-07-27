import Gc.Model.Mutation.MakeObjStack
import Gc.Model.Preservation.MakeObjStack
import Gc.Reachability.Validity.Reachable

theorem makeObjStack_cr3 : ValidReachableConfig cfg →
  makeObjStack x cfg = some cfg' →
  CR3 cfg' := by
  sorry

theorem makeObjStack_reachable_valid : ValidReachableConfig cfg →
  makeObjStack x cfg = some cfg' →
  ValidReachableConfig cfg' := by
  intro vrcfg h
  exact { makeObjStack_valid vrcfg.toValidConfig h with cr3 := makeObjStack_cr3 vrcfg h }
