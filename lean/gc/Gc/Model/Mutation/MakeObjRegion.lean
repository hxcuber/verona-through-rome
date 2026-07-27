import Gc.Model.Helpers
import Gc.Model.Types

def makeObjRegion (x : VarName) (cfg : RuntimeConfig) : Option (RuntimeConfig) := do
  let frame ← cfg.stack.getLast?
  let region ← cfg.heap.lookup frame.regionId
  let newObjId := cfg.freshObjectId
  if region.status == Status.Open then
    some { cfg with
      stack := cfg.stack.dropLast ++ [ { frame with
        varMap := frame.varMap.insert x (Reference.OId newObjId)
      } ],
      heap := cfg.heap.insert frame.regionId { region with
        objMap := region.objMap.insert newObjId ∅
      }
    }
  else
    none

theorem makeObjRegion_cases {cfg cfg' : RuntimeConfig} (h : makeObjRegion x cfg = some cfg') :
    ∃ frame region, cfg.stack.getLast? = some frame ∧ cfg.heap.lookup frame.regionId = some region ∧
      region.status = Status.Open ∧
      cfg' = { cfg with
        stack := cfg.stack.dropLast ++ [ { frame with
          varMap := frame.varMap.insert x (Reference.OId cfg.freshObjectId) } ],
        heap := cfg.heap.insert frame.regionId { region with
          objMap := region.objMap.insert cfg.freshObjectId ∅ } } := by
  unfold makeObjRegion at h
  cases hframe : cfg.stack.getLast? with
  | none => rw [hframe] at h; contradiction
  | some frame =>
    rw [hframe] at h
    dsimp at h
    cases hregion : cfg.heap.lookup frame.regionId with
    | none => rw [hregion] at h; contradiction
    | some region =>
      rw [hregion] at h
      dsimp at h
      cases hstatus : region.status with
      | Closed => rw [hstatus] at h; contradiction
      | Open =>
        rw [hstatus] at h
        rw [if_pos (by rfl)] at h
        rw [← hstatus] at h
        rw [Option.some_inj] at h
        refine ⟨frame, region, ?_, ?_, ?_, h.symm⟩ <;> first | rfl | assumption
