import Gc.Reachability.Validity.Preservation.Enter
import Gc.Reachability.Validity.Preservation.Exit
import Gc.Reachability.Validity.Preservation.FieldAsgn
import Gc.Reachability.Validity.Preservation.MakeObjRegion
import Gc.Reachability.Validity.Preservation.MakeObjStack
import Gc.Reachability.Validity.Preservation.MakeRegion
import Gc.Reachability.Validity.Preservation.Merge
import Gc.Reachability.Validity.Preservation.Swap
import Gc.Reachability.Validity.Preservation.VarAsgn
import Gc.Model.Preservation
import Gc.Reachability.Validity.Reachable

-- `Reachability`-layer analogue of `Gc.Model.Preservation`'s `allPreserve_ValidConfig`: every
-- operation preserves `ValidReachableConfig` (`ValidConfig` plus CR3), not just `ValidConfig`.
def allPreserve_ValidReachableConfig : AllPreserve ValidReachableConfig := by
  intro cmd cfg cfg' hstep hvalid
  simp [step] at hstep
  cases cmd with
  | enter xf bridgeVar => exact enter_reachable_valid hvalid hstep
  | exit               => exact exit_reachable_valid hvalid hstep
  | fieldAsgn xf y     => exact fieldAsgn_reachable_valid hvalid hstep
  | makeObjRegion x    => exact makeObjRegion_reachable_valid hvalid hstep
  | makeObjStack x     => exact makeObjStack_reachable_valid hvalid hstep
  | makeRegion x       => exact makeRegion_reachable_valid hvalid hstep
  | merge x            => exact merge_reachable_valid hvalid hstep
  | swap x yf          => exact swap_reachable_valid hvalid hstep
  | varAsgn x yf       => exact varAsgn_reachable_valid hvalid hstep
