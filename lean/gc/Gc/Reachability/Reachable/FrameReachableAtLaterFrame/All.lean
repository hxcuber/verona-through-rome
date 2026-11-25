module

public import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.Enter
public import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.Exit
public import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.MakeObjStack
public import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.MakeObjRegion
public import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.MakeRegion
public import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.Merge
public import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.VarAsgn
public import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.FieldAsgn
public import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.Swap

@[expose] public section

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

