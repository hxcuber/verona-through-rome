import Gc.Model.Helpers
import Gc.Model.Types

def exit (cfg : RuntimeConfig) : Option (RuntimeConfig) := do
  if cfg.stack.length >= 2 then
    let frame ← cfg.stack.getLast?
    let region ← cfg.heap.lookup frame.regionId
    if region.status == Status.Open then
      some { cfg with
        stack := cfg.stack.dropLast,
        heap := cfg.heap.insert frame.regionId { region with status := Status.Closed }
      }
    else
      none
  else
    none

theorem exit_cases {cfg cfg' : RuntimeConfig} (h : exit cfg = some cfg') :
    ∃ poppedFrame region, cfg.stack.length ≥ 2 ∧ cfg.stack.getLast? = some poppedFrame ∧
      cfg.heap.lookup poppedFrame.regionId = some region ∧ region.status = Status.Open ∧
      cfg' = { cfg with
        stack := cfg.stack.dropLast,
        heap := cfg.heap.insert poppedFrame.regionId { region with status := Status.Closed } } := by
  unfold exit at h
  by_cases hlen : cfg.stack.length ≥ 2
  · rw [if_pos hlen] at h
    cases hlast : cfg.stack.getLast? with
    | none => rw [hlast] at h; contradiction
    | some poppedFrame =>
      rw [hlast] at h
      dsimp at h
      cases hlookup : cfg.heap.lookup poppedFrame.regionId with
      | none => rw [hlookup] at h; contradiction
      | some region =>
        rw [hlookup] at h
        dsimp at h
        cases hstatus : region.status with
        | Closed => rw [hstatus] at h; contradiction
        | Open =>
          rw [hstatus] at h
          rw [if_pos (by rfl)] at h
          rw [Option.some_inj] at h
          refine ⟨poppedFrame, region, hlen, ?_, ?_, ?_, h.symm⟩ <;> first | rfl | assumption
  · rw [if_neg hlen] at h; contradiction
