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

-- `Suspended`'s existential witness for "active" always denotes the actual last element of
-- `cfg.stackWithIndex`, whose own `.index` is exactly `length - 1` (`mapIdx` assigns indices as
-- list positions). Used throughout below to connect `Suspended` to the more concrete
-- `< length - 1`/`< dropLast.length` bounds the per-operation corollaries are stated in terms of.
theorem Suspended_lt_length_sub_one {cfg : RuntimeConfig} {i : Index} (hsusp : Suspended cfg i) :
    i < cfg.stackWithIndex.length - 1 := by
  obtain ⟨frame, hframe, hidx, active, hactive, hlt⟩ := hsusp
  cases hls : cfg.stack.getLast? with
  | none =>
    exfalso
    have hnil : cfg.stack = [] := List.getLast?_eq_none_iff.mp hls
    have : cfg.stackWithIndex = [] := by unfold RuntimeConfig.stackWithIndex; rw [hnil]; rfl
    rw [this] at hactive
    exact absurd hactive (by simp)
  | some lastFrame =>
    have stack_eq : cfg.stack = cfg.stack.dropLast ++ [lastFrame] :=
      (List.dropLast_append_getLast? lastFrame hls).symm
    have hgetLast : cfg.stackWithIndex.getLast? =
        some ({ lastFrame with index := cfg.stack.dropLast.length } : FrameWithIndex) := by
      unfold RuntimeConfig.stackWithIndex
      conv_lhs => rw [stack_eq, List.mapIdx_concat]
      exact List.getLast?_concat
    rw [hgetLast] at hactive
    injection hactive with hactiveeq
    have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq]; simp
    have hlenWI : cfg.stackWithIndex.length = cfg.stack.length := by
      unfold RuntimeConfig.stackWithIndex; rw [List.length_mapIdx]
    rw [← hactiveeq] at hlt
    rw [hlenWI, hlen]
    simpa using hlt

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
  intro cfg cfg' vrcfg h i hsusp ref
  obtain ⟨frame, hframe, hidx, active, hactive, hlt⟩ := hsusp
  have vcfg := vrcfg.toValidConfig
  have vcfg' := exit_valid vcfg h
  obtain ⟨poppedFrame, region, hlen, hlast, hlookupPopped, hopenPopped, hcfg'⟩ := exit_cases h
  have hstackeq := exit_corollary_stackWithIndex_eq hlast
  have hgetLast : cfg.stackWithIndex.getLast? =
      some ({ poppedFrame with index := cfg.stack.dropLast.length } : FrameWithIndex) := by
    rw [hstackeq]
    exact List.getLast?_concat
  rw [hgetLast] at hactive
  injection hactive with hactiveeq
  subst hactiveeq
  dsimp only at hlt
  rw [hstackeq] at hframe
  rw [List.mem_append] at hframe
  rcases hframe with hold | hpop
  · have hframe0' : frame ∈ cfg'.stackWithIndex := by
      rw [hcfg']
      unfold RuntimeConfig.stackWithIndex
      dsimp only
      exact hold
    subst hidx
    exact exit_corollary_frameReachable_iff vcfg vcfg' h frame hframe0' ref
  · exfalso
    rw [List.mem_singleton] at hpop
    rw [hpop] at hidx
    dsimp only at hidx
    rw [hidx] at hlt
    exact lt_irrefl _ hlt

theorem cr5_step_fieldAsgn (xf : FieldAccess) (y : VarName) : CR5_step (Stmt.fieldAsgn xf y) := by
  sorry

theorem cr5_step_makeObjRegion (x : VarName) : CR5_step (Stmt.makeObjRegion x) := by
  intro cfg cfg' vrcfg h i hsusp ref
  have vcfg := vrcfg.toValidConfig
  have vcfg' := makeObjRegion_valid vcfg h
  have hlt := Suspended_lt_length_sub_one hsusp
  obtain ⟨frame1, region1, hframe1Last, hheapLookup1, hregion1Open, hcfg'⟩ := makeObjRegion_cases h
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame1] :=
    (List.dropLast_append_getLast? frame1 hframe1Last).symm
  have hlenWI : cfg.stackWithIndex.length = cfg.stack.length := by
    unfold RuntimeConfig.stackWithIndex; rw [List.length_mapIdx]
  have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq]; simp
  have hidlt : i < cfg.stack.dropLast.length := by
    rw [hlenWI, hlen] at hlt
    simpa using hlt
  exact makeObjRegion_corollary_frameReachable_iff_of_lt vcfg vcfg' h hidlt ref

theorem cr5_step_makeObjStack (x : VarName) : CR5_step (Stmt.makeObjStack x) := by
  intro cfg cfg' vrcfg h i hsusp ref
  have vcfg := vrcfg.toValidConfig
  have vcfg' := makeObjStack_valid vcfg h
  have hlt := Suspended_lt_length_sub_one hsusp
  obtain ⟨frame1, hframe1, hcfg'⟩ := makeObjStack_cases h
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame1] :=
    (List.dropLast_append_getLast? frame1 hframe1).symm
  have hlenWI : cfg.stackWithIndex.length = cfg.stack.length := by
    unfold RuntimeConfig.stackWithIndex; rw [List.length_mapIdx]
  have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq]; simp
  have hidlt : i < cfg.stack.dropLast.length := by
    rw [hlenWI, hlen] at hlt
    simpa using hlt
  exact makeObjStack_corollary_frameReachable_iff_of_lt vcfg vcfg' h hidlt ref

theorem cr5_step_makeRegion (x : VarName) : CR5_step (Stmt.makeRegion x) := by
  intro cfg cfg' vrcfg h i hsusp ref
  have vcfg := vrcfg.toValidConfig
  have vcfg' := makeRegion_valid vcfg h
  have hlt := Suspended_lt_length_sub_one hsusp
  obtain ⟨frame1, hframe1Last, hcfg'⟩ := makeRegion_cases h
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame1] :=
    (List.dropLast_append_getLast? frame1 hframe1Last).symm
  have hlenWI : cfg.stackWithIndex.length = cfg.stack.length := by
    unfold RuntimeConfig.stackWithIndex; rw [List.length_mapIdx]
  have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq]; simp
  have hidlt : i < cfg.stack.dropLast.length := by
    rw [hlenWI, hlen] at hlt
    simpa using hlt
  exact makeRegion_corollary_frameReachable_iff_of_lt vcfg vcfg' h hidlt ref

theorem cr5_step_merge (x : VarName) : CR5_step (Stmt.merge x) := by
  sorry

theorem cr5_step_swap (x : VarName) (yf : FieldAccess) : CR5_step (Stmt.swap x yf) := by
  sorry

theorem cr5_step_varAsgn (x : VarName) (yf : FieldAccess) : CR5_step (Stmt.varAsgn x yf) := by
  intro cfg cfg' vrcfg h i hsusp ref
  obtain ⟨frame, hframe, hidx, active, hactive, hlt⟩ := hsusp
  have vcfg := vrcfg.toValidConfig
  have vcfg' := varAsgn_valid vcfg h
  have hRefStepIff : ∀ a b, RefStep cfg a b ↔ RefStep cfg' a b := by
    intro a b
    unfold RefStep
    rw [varAsgn_corollary_objAt_eq vcfg vcfg' h a]
  obtain ⟨frame0, hframe0, hcase⟩ := varAsgn_cases h
  have stack_eq0 : cfg.stack = cfg.stack.dropLast ++ [frame0] :=
    (List.dropLast_append_getLast? frame0 hframe0).symm
  set frame0W : FrameWithIndex := { frame0 with index := cfg.stack.dropLast.length } with frame0W_def
  have hgetLast : cfg.stackWithIndex.getLast? = some frame0W := by
    unfold RuntimeConfig.stackWithIndex
    rw [stack_eq0, List.mapIdx_concat]
    exact List.getLast?_concat
  rw [hgetLast] at hactive
  injection hactive with hactiveeq
  subst hactiveeq
  -- `frame` sits strictly before `frame0W` (the mutated/active frame), so it comes from the
  -- untouched `dropLast` part of the stack -- the same literal record on both sides.
  obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hframe
  have hidxn : frame.index = n := by rw [← hfeq]
  have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq0]; simp
  have hnlt : n < cfg.stack.dropLast.length := by
    rw [← hidxn, hidx]
    exact hlt
  have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
    conv_lhs => rw [stack_eq0]
    rw [List.getElem?_append_left hnlt]
  have hcfgn : cfg.stack[n]? = some frame.toFrame := by
    rw [show frame.toFrame = cfg.stack[n] from by rw [← hfeq]]
    exact List.getElem?_eq_getElem hn
  have hdropn : cfg.stack.dropLast[n]? = some frame.toFrame := by rw [← e1]; exact hcfgn
  have hcfg'n : cfg'.stack[n]? = some frame.toFrame := by
    rcases hcase with
      ⟨oid, rid, region, hyf, hxb, hloc, hridEq, hregion, hcfg'⟩ | ⟨oid, hyf, hxb, hresolve, hcfg'⟩
    · rw [hcfg']; dsimp only; exact hcfgn
    · rw [hcfg']
      dsimp only
      rw [List.getElem?_append_left hnlt]
      exact hdropn
  obtain ⟨h1, heq⟩ := List.getElem?_eq_some_iff.mp hcfg'n
  have hframe' : frame ∈ cfg'.stackWithIndex := by
    unfold RuntimeConfig.stackWithIndex
    exact List.mem_mapIdx.mpr ⟨n, h1, by rw [heq, ← hidxn]⟩
  have hframe0W_mem : frame0W ∈ cfg.stackWithIndex := by
    unfold RuntimeConfig.stackWithIndex
    rw [stack_eq0, List.mapIdx_concat]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hridNe : frame.regionId ≠ frame0.regionId := by
    intro heqrid
    have heqrid' : frame.regionId = frame0W.regionId := heqrid
    have hidxeq := merge_corollary_regionId_unique_index vcfg.s1 hframe hframe0W_mem heqrid'
    rw [hidx] at hidxeq
    exact absurd hidxeq (Nat.ne_of_lt hlt)
  have hheapEq : cfg'.heap.lookup frame.regionId = cfg.heap.lookup frame.regionId := by
    rcases hcase with
      ⟨oid, rid, region, hyf, hxb, hloc, hridEq, hregion, hcfg'⟩ | ⟨oid, hyf, hxb, hresolve, hcfg'⟩
    · rw [hcfg']
      dsimp only
      rw [hridEq] at hridNe
      exact AList.lookup_insert_ne hridNe
    · rw [hcfg']
  have hfrRootIff : ∀ start, FrameRoot cfg i start ↔ FrameRoot cfg' i start := by
    intro start
    unfold FrameRoot
    constructor
    · rintro (⟨fr1, hfr1, hidx1, var, hlookup1⟩ | ⟨fr1, hfr1, hidx1, region1, hlookup1, hstart⟩)
      · have heq1 : fr1 = frame := swap_corollary_stackWithIndex_index_inj hfr1 hframe (hidx1.trans hidx.symm)
        rw [heq1] at hlookup1
        exact Or.inl ⟨frame, hframe', hidx, var, hlookup1⟩
      · have heq1 : fr1 = frame := swap_corollary_stackWithIndex_index_inj hfr1 hframe (hidx1.trans hidx.symm)
        rw [heq1] at hlookup1
        exact Or.inr ⟨frame, hframe', hidx, region1, by rw [hheapEq]; exact hlookup1, hstart⟩
    · rintro (⟨fr1, hfr1, hidx1, var, hlookup1⟩ | ⟨fr1, hfr1, hidx1, region1, hlookup1, hstart⟩)
      · have heq1 : fr1 = frame := swap_corollary_stackWithIndex_index_inj hfr1 hframe' (hidx1.trans hidx.symm)
        rw [heq1] at hlookup1
        exact Or.inl ⟨frame, hframe, hidx, var, hlookup1⟩
      · have heq1 : fr1 = frame := swap_corollary_stackWithIndex_index_inj hfr1 hframe' (hidx1.trans hidx.symm)
        rw [heq1] at hlookup1
        exact Or.inr ⟨frame, hframe, hidx, region1, by rw [← hheapEq]; exact hlookup1, hstart⟩
  rw [FrameReachable_iff_reflTransGen, FrameReachable_iff_reflTransGen]
  constructor
  · rintro ⟨start, hroot, hrtg⟩
    exact ⟨start, (hfrRootIff start).mp hroot, hrtg.mono (fun a b hab => (hRefStepIff a b).mp hab)⟩
  · rintro ⟨start, hroot, hrtg⟩
    exact ⟨start, (hfrRootIff start).mpr hroot, hrtg.mono (fun a b hab => (hRefStepIff a b).mpr hab)⟩

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
