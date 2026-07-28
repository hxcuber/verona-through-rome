import Gc.Scratch

/-!
report.pdf CR5: "Activity in an active region and frame cannot affect the stack-reachability
of objects within suspended regions."

Unlike CR1-CR4 (`Gc/Reachability/Corollaries.lean`) and CR3's `ValidConfig`-style invariant
(`Gc/Reachability/Validity/Reachable.lean`), CR5 isn't a property of a single config -- it's a
claim about *change over a run of the operational semantics*: as long as some frame stays
suspended (never becomes the active/last frame) across a sequence of `Mutation.lean` operations,
its frame-reachable set never changes across that whole sequence, no matter how long it is or
what happens inside the active frame/region.

The real report.pdf claim is over an arbitrary-length *run* of operations, but for now this file
only tackles the single-step layer:
- `CR5_step`: one `Mutation.lean` operation's worth of the claim, proved once per `Stmt` case
  (mirrors the `Validity/Preservation/*.lean` per-operation pattern already used for CR3).
- `cr5_step_all`: dispatches to the 9 per-operation cases.
The multi-step generalization (a `List Stmt` trace, chaining `CR5_step` via `Iff.trans` as long
as the frame of interest stays suspended at every intermediate config) is sketched in a comment
block at the end of the file -- deliberately not live code yet, since it follows for free once
`cr5_step_all` has no `sorry`s left, and isn't the current focus.

`enter`/`exit` are not special-cased here despite changing *which* frame counts as active: the
suspension hypothesis is evaluated pre-step, so `CR5_step` only ever makes a claim about frames
that were *already* suspended before the operation runs. `enter_corollary_regionId_ne` (an
already-on-stack frame's region can never be the entered/closed one) and S2/S3 (nothing earlier
can reference into what `exit` pops) are exactly why this should hold uniformly for all 9 cases --
`enter_corollary_frameReachable_iff`/`exit_corollary_frameReachable_iff` in the corresponding
`Validity/Preservation` files already prove almost exactly this fact for those two operations
(currently `private`, so `cr5_step_enter`/`cr5_step_exit` will need their own copies or those
made public).
-/

-- `i` is suspended in `cfg`: it names an on-stack frame that is not the active (last) one.
def Suspended (cfg : RuntimeConfig) (i : Index) : Prop :=
  ∃ frame ∈ cfg.stackWithIndex, frame.index = i ∧
    ∃ active, cfg.stackWithIndex.getLast? = some active ∧ i < active.index

-- Single-step CR5: one `Mutation.lean` operation, applied to a valid+reachable config, cannot
-- change frame-reachability at any index that was already suspended beforehand.
def CR5_step (cmd : Stmt) : Prop :=
  ∀ cfg cfg' : RuntimeConfig, ValidReachableConfig cfg → step cmd cfg = some cfg' →
    ∀ i, Suspended cfg i → ∀ ref, FrameReachable cfg i ref ↔ FrameReachable cfg' i ref

theorem cr5_step_enter (xf : FieldAccess) (a : VarName) : CR5_step (Stmt.enter xf a) := by
  intro cfg cfg' vrcfg h i hsusp ref
  obtain ⟨frame0, hframe0, hidx, _⟩ := hsusp
  subst hidx
  have vcfg := vrcfg.toValidConfig
  have vcfg' := enter_valid vcfg h
  exact enter_corollary_frameReachable_iff vcfg vcfg' h frame0 hframe0 ref

theorem cr5_step_exit : CR5_step Stmt.exit := by
  sorry

theorem cr5_step_fieldAsgn (xf : FieldAccess) (y : VarName) : CR5_step (Stmt.fieldAsgn xf y) := by
  sorry

theorem cr5_step_makeObjRegion (x : VarName) : CR5_step (Stmt.makeObjRegion x) := by
  sorry

theorem cr5_step_makeObjStack (x : VarName) : CR5_step (Stmt.makeObjStack x) := by
  sorry

theorem cr5_step_makeRegion (x : VarName) : CR5_step (Stmt.makeRegion x) := by
  sorry

theorem cr5_step_merge (x : VarName) : CR5_step (Stmt.merge x) := by
  sorry

theorem cr5_step_swap (x : VarName) (yf : FieldAccess) : CR5_step (Stmt.swap x yf) := by
  sorry

theorem cr5_step_varAsgn (x : VarName) (yf : FieldAccess) : CR5_step (Stmt.varAsgn x yf) := by
  sorry

-- Every operation satisfies CR5_step -- the layer-1 statement, in full generality.
theorem cr5_step_all : ∀ cmd, CR5_step cmd := by
  intro cmd
  cases cmd with
  | enter xf a => exact cr5_step_enter xf a
  | exit => exact cr5_step_exit
  | fieldAsgn xf y => exact cr5_step_fieldAsgn xf y
  | makeObjRegion x => exact cr5_step_makeObjRegion x
  | makeObjStack x => exact cr5_step_makeObjStack x
  | makeRegion x => exact cr5_step_makeRegion x
  | merge x => exact cr5_step_merge x
  | swap x yf => exact cr5_step_swap x yf
  | varAsgn x yf => exact cr5_step_varAsgn x yf

-- Deferred until the single-step case (above) is actually filled in -- only `Suspended`/
-- `CR5_step`/`cr5_step_all` are live for now. This layer was: a trace of operations
-- (`Run : List Stmt → RuntimeConfig → Option RuntimeConfig`, folding `step` left to right), a
-- "stays suspended at every intermediate config" predicate (`AllSuspended`), and the actual
-- report.pdf CR5 statement chaining `cr5_step_all` along the trace via `Iff.trans` (a
-- straightforward induction once `cr5_step_all` has no `sorry`s left -- no further
-- per-operation work needed). Kept here as prose so it's easy to resurrect.
--
-- def Run : List Stmt → RuntimeConfig → Option RuntimeConfig
--   | [], cfg => some cfg
--   | cmd :: rest, cfg => (step cmd cfg).bind (Run rest)
--
-- def AllSuspended : List Stmt → RuntimeConfig → Index → Prop
--   | [], cfg, i => Suspended cfg i
--   | cmd :: rest, cfg, i =>
--       Suspended cfg i ∧ ∃ cfg', step cmd cfg = some cfg' ∧ AllSuspended rest cfg' i
--
-- theorem CR5 : ∀ (cmds : List Stmt) (cfg cfg' : RuntimeConfig) (i : Index),
--     ValidReachableConfig cfg → Run cmds cfg = some cfg' → AllSuspended cmds cfg i →
--     ∀ ref, FrameReachable cfg i ref ↔ FrameReachable cfg' i ref := by
--   intro cmds
--   induction cmds with
--   | nil =>
--     intro cfg cfg' i _ hrun _ ref
--     unfold Run at hrun
--     injection hrun with hcfgeq
--     rw [hcfgeq]
--   | cons cmd rest ih =>
--     intro cfg cfg' i hvalid hrun hsusp ref
--     obtain ⟨hsusp0, cfg1, hstep, hsuspRest⟩ := hsusp
--     unfold Run at hrun
--     rw [hstep] at hrun
--     dsimp only [Option.bind] at hrun
--     have hvalid1 : ValidReachableConfig cfg1 :=
--       allPreserve_ValidReachableConfig cmd cfg cfg1 hstep hvalid
--     have hiff1 := cr5_step_all cmd cfg cfg1 hvalid hstep i hsusp0 ref
--     have hiff2 := ih cfg1 cfg' i hvalid1 hrun hsuspRest ref
--     exact hiff1.trans hiff2
