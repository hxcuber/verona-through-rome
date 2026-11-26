module

public import Gc.Model.Helpers

@[expose] public section

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
  · rcases hlast : cfg.stack.getLast? with _ | f
    · simp_all
    · rcases hl : cfg.heap.lookup f.regionId with _ | region
      · simp_all
      · cases hs : region.status <;> simp_all
        exact absurd h.1 (by decide)
  · simp_all
