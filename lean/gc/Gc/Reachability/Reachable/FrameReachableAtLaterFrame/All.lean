import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Mutation.Mutation
import Gc.Model.Mutation.Stmt
import Gc.Model.Preservation
import Gc.Reachability.Reachable.Semantics
import Gc.Reachability.Reachable.Basic
import Gc.Reachability.Reachable.Lemmas
import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.Enter
import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.Exit
import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.MakeObjStack
import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.MakeObjRegion
import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.MakeRegion
import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.Merge
import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.VarAsgn
import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.FieldAsgn
import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.Swap

theorem frameReachableAtLaterFrame_step_all (cmd : Stmt) :
    FrameReachableAtLaterFrame_step cmd := by
  cases cmd with
  | enter xf bridgeVar => exact frameReachableAtLaterFrame_step_enter xf bridgeVar
  | exit => exact frameReachableAtLaterFrame_step_exit
  | fieldAsgn xf y => exact frameReachableAtLaterFrame_step_fieldAsgn xf y
  | makeObjRegion x => exact frameReachableAtLaterFrame_step_makeObjRegion x
  | makeObjStack x => exact frameReachableAtLaterFrame_step_makeObjStack x
  | makeRegion x => exact frameReachableAtLaterFrame_step_makeRegion x
  | merge x => exact frameReachableAtLaterFrame_step_merge x
  | swap x yf => exact frameReachableAtLaterFrame_step_swap x yf
  | varAsgn x yf => exact frameReachableAtLaterFrame_step_varAsgn x yf

