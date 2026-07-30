import Gc.Model.Mutation.Stmt
import Gc.Reachability.Referencable.Validity.Preservation

/-!
report.pdf CR5: "Activity in an active region and frame cannot affect the stack-reachability
of objects within suspended regions."

Unlike CR1-CR4 (`Gc/Reachability/Referencable/Corollaries/{CR1,CR2,CR4}.lean`) and CR3's `ValidConfig`-style
invariant (`Gc/Reachability/Referencable/Validity/Reachable.lean`), CR5 isn't a property of a single config --
it's a claim about *change over a run of the operational semantics*: as long as some frame stays
suspended (never becomes the active/last frame) across a sequence of `Mutation.lean` operations,
its frame-reachable set never changes across that whole sequence, no matter how long it is or
what happens inside the active frame/region.

`CR5_step` is the actual report.pdf statement (in `StackReferencable` form, restricted to references
already `FrameReferencable` from the suspended frame -- an unrestricted version is false, see
`cr5_step_of_helper`'s own comment). It's proved via a helper, `CR5_helper_step`, which is the
easier-to-prove-per-operation `FrameReferencable` form (mirrors the `Validity/Preservation/*.lean`
per-operation pattern already used for CR3):
- `cr5_step_of_helper`: upgrades a `CR5_helper_step` fact into the real `CR5_step` fact.
- `cr5_step_enter` .. `cr5_step_varAsgn`: the 9 per-operation proofs. Each proves the
  `CR5_helper_step` fact internally (unnamed) and closes with `cr5_step_of_helper` -- there's no
  separately-named per-operation `CR5_helper_step` fact anymore (traded away deliberately for a
  cleaner public API; see `cr5_step_all`'s own comment for what that costs the multi-step
  generalization below).
- `cr5_step_all`: dispatches the 9 proofs above to all `Stmt` cases.

The real report.pdf claim is over an arbitrary-length *run* of operations, but this file only
tackles the single-step layer for now -- the multi-step generalization (a `List Stmt` trace,
chaining single-step facts along it as long as the frame of interest stays suspended at every
intermediate config) isn't started yet.

`enter`/`exit` are not special-cased here despite changing *which* frame counts as active: the
suspension hypothesis is evaluated pre-step, so `CR5_helper_step` only ever makes a claim about
frames that were *already* suspended before the operation runs. `enter_corollary_regionId_ne` (an
already-on-stack frame's region can never be the entered/closed one) and S2/S3 (nothing earlier
can reference into what `exit` pops) are exactly why this should hold uniformly for all 9 cases --
`enter_corollary_frameReferencable_iff`/`exit_corollary_frameReferencable_iff` in the corresponding
`Validity/Preservation` files already prove almost exactly this fact for those two operations
(currently `private`, so `cr5_step_enter`/`cr5_step_exit` will need their own
copies or those made public).
-/

-- `i` is suspended in `cfg`: it names an on-stack frame that is not the active (last) one.
def Suspended (cfg : RuntimeConfig) (i : Index) : Prop :=
  ∃ frame ∈ cfg.stackWithIndex, frame.index = i ∧ i < cfg.stackWithIndex.length - 1

-- Helper for `CR5_step` below: one `Mutation.lean` operation, applied to a valid+reachable
-- config, cannot change *frame*-reachability at any index that was already suspended beforehand.
-- Easier to prove per-operation than `CR5_step` itself (see `cr5_step_of_helper`).
def CR5_helper_step (cmd : Stmt) : Prop :=
  ∀ cfg cfg' : RuntimeConfig, ValidReachableConfig cfg → step cmd cfg = some cfg' →
    ∀ i, Suspended cfg i → ∀ ref, FrameReferencable cfg i ref ↔ FrameReferencable cfg' i ref

-- report.pdf CR5, in `StackReferencable` form: restricted to references already `FrameReferencable`
-- from the suspended frame in `cfg` (an *unrestricted* `∀ ref, StackReferencable cfg ref ↔
-- StackReferencable cfg' ref` is false -- e.g. `makeObjStack` can make a brand-new object
-- `StackReferencable` in `cfg'` via the active frame's own fresh var, without it ever having been
-- reachable, from anywhere, in `cfg`; that has nothing to do with any suspended region).
def CR5_step (cmd : Stmt) : Prop :=
  ∀ cfg cfg' : RuntimeConfig, ValidReachableConfig cfg → step cmd cfg = some cfg' →
    ∀ i, Suspended cfg i → ∀ ref, FrameReferencable cfg i ref →
    (StackReferencable cfg ref ↔ StackReferencable cfg' ref)

-- Upgrades `CR5_helper_step` into the real `CR5_step`: once `ref` is already `FrameReferencable`
-- from the suspended frame, `StackReferencable cfg ref` is trivially witnessed by that same frame,
-- and `StackReferencable cfg' ref` falls out of the helper's `FrameReferencable cfg' i ref` fact by
-- unfolding `FrameRoot` for a witness frame -- no `CR4`/`RegionReferencable` machinery needed at all.
theorem cr5_step_of_helper (cmd : Stmt) : CR5_helper_step cmd → CR5_step cmd := by
  intro h cfg cfg' vrcfg hstep i hsusp ref hfr
  have hiff := h cfg cfg' vrcfg hstep i hsusp ref
  obtain ⟨frame, hframe, hidx, _⟩ := hsusp
  constructor
  · intro _
    have hfr' : FrameReferencable cfg' i ref := hiff.mp hfr
    obtain ⟨start, hroot, _⟩ := (FrameReferencable_iff_reflTransGen cfg' i ref).mp hfr'
    rcases hroot with ⟨frame', hframe'mem, hidx', _⟩ | ⟨frame', hframe'mem, hidx', _⟩
    · exact ⟨frame', hframe'mem, by rw [hidx']; exact hfr'⟩
    · exact ⟨frame', hframe'mem, by rw [hidx']; exact hfr'⟩
  · intro _
    exact ⟨frame, hframe, by rw [hidx]; exact hfr⟩

theorem cr5_step_enter (xf : FieldAccess) (a : VarName) : CR5_step (Stmt.enter xf a) := by
  apply cr5_step_of_helper
  intro cfg cfg' vrcfg h i hsusp ref
  obtain ⟨frame0, hframe0, hidx, _⟩ := hsusp
  subst hidx
  have vcfg := vrcfg.toValidConfig
  have vcfg' := enter_valid vcfg h
  exact enter_corollary_frameReferencable_iff vcfg vcfg' h frame0 hframe0 ref

theorem cr5_step_exit : CR5_step Stmt.exit := by
  apply cr5_step_of_helper
  intro cfg cfg' vrcfg h i hsusp ref
  obtain ⟨frame, hframe, hidx, hlt⟩ := hsusp
  have vcfg := vrcfg.toValidConfig
  have vcfg' := exit_valid vcfg h
  obtain ⟨poppedFrame, region, hlen2, hlast, hlookupPopped, hopenPopped, hcfg'⟩ := exit_cases h
  have hstackeq := exit_corollary_stackWithIndex_eq hlast
  have hlenWI : cfg.stackWithIndex.length = cfg.stack.length := by
    unfold RuntimeConfig.stackWithIndex; rw [List.length_mapIdx]
  have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by
    have stack_eq : cfg.stack = cfg.stack.dropLast ++ [poppedFrame] :=
      (List.dropLast_append_getLast? poppedFrame hlast).symm
    rw [stack_eq]; simp
  have hidlt : i < cfg.stack.dropLast.length := by
    rw [hlenWI, hlen] at hlt
    simpa using hlt
  rw [hstackeq] at hframe
  rw [List.mem_append] at hframe
  rcases hframe with hold | hpop
  · have hframe0' : frame ∈ cfg'.stackWithIndex := by
      rw [hcfg']
      unfold RuntimeConfig.stackWithIndex
      dsimp only
      exact hold
    subst hidx
    exact exit_corollary_frameReferencable_iff vcfg vcfg' h frame hframe0' ref
  · exfalso
    rw [List.mem_singleton] at hpop
    rw [hpop] at hidx
    dsimp only at hidx
    rw [hidx] at hidlt
    exact lt_irrefl _ hidlt

theorem cr5_step_fieldAsgn (xf : FieldAccess) (y : VarName) : CR5_step (Stmt.fieldAsgn xf y) := by
  apply cr5_step_of_helper
  intro cfg cfg' vrcfg h i hsusp ref
  obtain ⟨frame, hframe, hidx, hlt⟩ := hsusp
  have vcfg := vrcfg.toValidConfig
  have vcfg' := fieldAsgn_valid vcfg h
  obtain ⟨frame0, hframe0, _⟩ := fieldAsgn_cases h
  obtain ⟨stack_eq0, hidx00⟩ := fieldAsgn_corollary_stack_eq hframe0
  have hlenWI : cfg.stackWithIndex.length = cfg.stack.length := by
    unfold RuntimeConfig.stackWithIndex; rw [List.length_mapIdx]
  have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq0]; simp
  have hidlt : i < cfg.stack.dropLast.length := by
    rw [hlenWI, hlen] at hlt
    simpa using hlt
  have hframelt : frame.index < cfg.stack.dropLast.length := by rw [hidx]; exact hidlt
  have hres := fieldAsgn_corollary_frameReferencable_iff_of_lt vcfg vcfg' h frame hframelt ref
  rwa [hidx] at hres

theorem cr5_step_makeObjRegion (x : VarName) : CR5_step (Stmt.makeObjRegion x) := by
  apply cr5_step_of_helper
  intro cfg cfg' vrcfg h i hsusp ref
  have vcfg := vrcfg.toValidConfig
  have vcfg' := makeObjRegion_valid vcfg h
  obtain ⟨_, _, _, hlt⟩ := hsusp
  obtain ⟨frame1, region1, hframe1Last, hheapLookup1, hregion1Open, hcfg'⟩ := makeObjRegion_cases h
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame1] :=
    (List.dropLast_append_getLast? frame1 hframe1Last).symm
  have hlenWI : cfg.stackWithIndex.length = cfg.stack.length := by
    unfold RuntimeConfig.stackWithIndex; rw [List.length_mapIdx]
  have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq]; simp
  have hidlt : i < cfg.stack.dropLast.length := by
    rw [hlenWI, hlen] at hlt
    simpa using hlt
  exact makeObjRegion_corollary_frameReferencable_iff_of_lt vcfg vcfg' h hidlt ref

theorem cr5_step_makeObjStack (x : VarName) : CR5_step (Stmt.makeObjStack x) := by
  apply cr5_step_of_helper
  intro cfg cfg' vrcfg h i hsusp ref
  have vcfg := vrcfg.toValidConfig
  have vcfg' := makeObjStack_valid vcfg h
  obtain ⟨_, _, _, hlt⟩ := hsusp
  obtain ⟨frame1, hframe1, hcfg'⟩ := makeObjStack_cases h
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame1] :=
    (List.dropLast_append_getLast? frame1 hframe1).symm
  have hlenWI : cfg.stackWithIndex.length = cfg.stack.length := by
    unfold RuntimeConfig.stackWithIndex; rw [List.length_mapIdx]
  have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq]; simp
  have hidlt : i < cfg.stack.dropLast.length := by
    rw [hlenWI, hlen] at hlt
    simpa using hlt
  exact makeObjStack_corollary_frameReferencable_iff_of_lt vcfg vcfg' h hidlt ref

theorem cr5_step_makeRegion (x : VarName) : CR5_step (Stmt.makeRegion x) := by
  apply cr5_step_of_helper
  intro cfg cfg' vrcfg h i hsusp ref
  have vcfg := vrcfg.toValidConfig
  have vcfg' := makeRegion_valid vcfg h
  obtain ⟨_, _, _, hlt⟩ := hsusp
  obtain ⟨frame1, hframe1Last, hcfg'⟩ := makeRegion_cases h
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame1] :=
    (List.dropLast_append_getLast? frame1 hframe1Last).symm
  have hlenWI : cfg.stackWithIndex.length = cfg.stack.length := by
    unfold RuntimeConfig.stackWithIndex; rw [List.length_mapIdx]
  have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq]; simp
  have hidlt : i < cfg.stack.dropLast.length := by
    rw [hlenWI, hlen] at hlt
    simpa using hlt
  exact makeRegion_corollary_frameReferencable_iff_of_lt vcfg vcfg' h hidlt ref

theorem cr5_step_merge (x : VarName) : CR5_step (Stmt.merge x) := by
  apply cr5_step_of_helper
  intro cfg cfg' vrcfg h i hsusp ref
  have vcfg := vrcfg.toValidConfig
  obtain ⟨_, _, _, hlt⟩ := hsusp
  obtain ⟨frame1, rid', region1, region', hframe1Last, hxref1, hregion1, hregion', hclosed1, hopen1, hcfg'⟩ :=
    merge_cases h
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame1] :=
    (List.dropLast_append_getLast? frame1 hframe1Last).symm
  have hlenWI : cfg.stackWithIndex.length = cfg.stack.length := by
    unfold RuntimeConfig.stackWithIndex; rw [List.length_mapIdx]
  have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq]; simp
  have hidlt : i < cfg.stack.dropLast.length := by
    rw [hlenWI, hlen] at hlt
    simpa using hlt
  exact merge_corollary_frameReferencable_iff_of_lt vcfg h hidlt ref

theorem cr5_step_swap (x : VarName) (yf : FieldAccess) : CR5_step (Stmt.swap x yf) := by
  apply cr5_step_of_helper
  intro cfg cfg' vrcfg h i hsusp ref
  obtain ⟨frame, hframe, hidx, hlt⟩ := hsusp
  have vcfg := vrcfg.toValidConfig
  have vcfg' := swap_valid vcfg h
  obtain ⟨frame0, hframe0, _, _, _, _, _, _, _, _, _⟩ := swap_cases h
  obtain ⟨stack_eq0, hidx00⟩ := swap_corollary_stack_eq hframe0
  have hlenWI : cfg.stackWithIndex.length = cfg.stack.length := by
    unfold RuntimeConfig.stackWithIndex; rw [List.length_mapIdx]
  have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq0]; simp
  have hidlt : i < cfg.stack.dropLast.length := by
    rw [hlenWI, hlen] at hlt
    simpa using hlt
  have hframelt : frame.index < cfg.stack.dropLast.length := by rw [hidx]; exact hidlt
  have hres := swap_corollary_frameReferencable_iff_of_lt vcfg vcfg' h frame hframelt ref
  rwa [hidx] at hres

theorem cr5_step_varAsgn (x : VarName) (yf : FieldAccess) : CR5_step (Stmt.varAsgn x yf) := by
  apply cr5_step_of_helper
  intro cfg cfg' vrcfg h i hsusp ref
  obtain ⟨frame, hframe, hidx, hlt⟩ := hsusp
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
  have hlenWI : cfg.stackWithIndex.length = cfg.stack.length := by
    unfold RuntimeConfig.stackWithIndex; rw [List.length_mapIdx]
  have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq0]; simp
  have hidlt : i < cfg.stack.dropLast.length := by
    rw [hlenWI, hlen] at hlt
    simpa using hlt
  -- `frame` sits strictly before `frame0W` (the mutated/active frame), so it comes from the
  -- untouched `dropLast` part of the stack -- the same literal record on both sides.
  obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hframe
  have hidxn : frame.index = n := by rw [← hfeq]
  have hnlt : n < cfg.stack.dropLast.length := by
    rw [← hidxn, hidx]
    exact hidlt
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
    exact absurd hidxeq (Nat.ne_of_lt hidlt)
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
  rw [FrameReferencable_iff_reflTransGen, FrameReferencable_iff_reflTransGen]
  constructor
  · rintro ⟨start, hroot, hrtg⟩
    exact ⟨start, (hfrRootIff start).mp hroot, hrtg.mono (fun a b hab => (hRefStepIff a b).mp hab)⟩
  · rintro ⟨start, hroot, hrtg⟩
    exact ⟨start, (hfrRootIff start).mpr hroot, hrtg.mono (fun a b hab => (hRefStepIff a b).mpr hab)⟩

-- Every operation satisfies CR5_step -- the layer-1 statement, in full generality. Each of the 9
-- cases already closes with `cr5_step_of_helper` internally (see each proof's own `apply
-- cr5_step_of_helper` first line), so there's no separately-named `CR5_helper_step` dispatcher
-- anymore -- if a future multi-step generalization ends up needing that iff-chaining form again,
-- it'll have to be re-derived (each op's proof still proves it internally, just not under a name).
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
