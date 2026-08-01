# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project

Final year project (Imperial College, 2025-26): a Lean 4 formalization of a Verona/Reggio-style
region-based memory management model (stack + heap of regions, bridge objects, region open/closed
status) and, building on top of that, reachability definitions intended to support proving garbage
collection safety guarantees.

Repo layout:
- `lean/gc/` — the actual Lean 4 project (everything below refers to paths relative to this directory).
- `lean/gc/README.md` — raw meeting notes / design-decision log, not user docs. Useful for *why* the
  model is shaped the way it is (e.g. why `RegionId` is kept separate from `BridgeObjectId`, why a
  stack frame owns its own `objMap` for temporaries, why there's a single combined heap rather than
  separate open/closed/frozen heaps).
- `report.pdf`, `slides.pdf` — the written FYP report and presentation slides (binary, not source).

## Commands

All commands below assume `cd lean/gc`.

- **Build/check a single file**: `lake build Gc.Model.Theorems` (dotted module path mirrors the file
  path, e.g. `Gc/Model/Preservation/Swap.lean` → `Gc.Model.Preservation.Swap`).
- **`lake build` (bare, no target) succeeds end to end**, including `Gc`, `Main`, and the `gc`
  executable, with zero `sorry`s anywhere under `Gc/`. Note: `Gc/Reachability/Reachable/` is not yet
  imported from `Gc.lean`, so it is *not* covered by the bare build — check it via qualified-name
  builds (e.g. `lake build Gc.Reachability.Reachable.Scratch`) or the Lean LSP tools. Prefer building
  the specific module(s) you're touching by qualified name for faster iteration.
- Toolchain is pinned via `lean-toolchain` (`leanprover/lean4:v4.29.0-rc6`) and dependencies via
  `lake-manifest.json`; the main dependency is `mathlib`. First builds after a fresh clone can be slow
  because of mathlib — subsequent builds reuse `.lake/build`.

## Workflow

Do all iteration on this project through the `/lean4` skills (`/lean4:prove`, `/lean4:draft`,
`/lean4:refactor`, `/lean4:golf`, `/lean4:review`, `/lean4:checkpoint`, etc.) and the Lean LSP MCP
tools (`lean_goal`, `lean_diagnostic_messages`, `lean_multi_attempt`, `lean_verify`, ...) rather than
shelling out to `lake build`/`grep` and hand-simulating goal states. The LSP tools are faster (no
full-file recompile per check), give exact goal states instead of guessed ones, and are what this
repo's whole proof-engineering convention (per-file corollaries, `lean_goal`-confirmed case splits,
axiom checks via `lean_verify`) already assumes. Fall back to raw `lake build`/`grep` only when
there's a concrete reason the LSP path doesn't work (e.g. checking the *whole-project* build after a
cross-file change, or the LSP server is unresponsive/stale) — and say so explicitly when you do.

## Architecture

The proof development has three layers under `Gc/`.

### `Gc/Model/` — the runtime model and its operational semantics (complete, zero `sorry`)

- `Types.lean` — the core data model: `RegionId`/`ObjectId`/`BridgeObjectId`, `Reference` (`RId`/`OId`),
  `VarMap`/`ObjMap` (as `AList`s), `Region` (bridge object + objects + open/closed `Status`), `Frame`
  (a stack frame: its region, bridge var, local var map and local obj map), `Stack`, `Heap`,
  `RuntimeConfig` (`stack` + `heap`), and `Location` (`Rgn`/`Stk`).
- `Helpers.lean` — projections and derived queries over the model: collecting `refs`/`objectIds` from
  frames/regions/heap/stack, `freshObjectId`, resolving where a `Reference` lives (`Reference.loc?`),
  and resolving variable/field-access expressions against a config (`resolveV`, `resolveFA`). Also has
  `RuntimeConfig.freshObjectId_not_mem` (`cfg.freshObjectId ∉ cfg.objectIds`), proved via two small
  generic lemmas in `Theorems.lean` (`List.le_foldl_max_self`, `List.mem_le_foldl_max`) about
  `List.foldl max`.
- `Validity.lean` — defines `ValidConfig` as a bundle of **9** named invariants: `L1`/`L2` (global,
  e.g. object-id uniqueness, stack regions are Open), `H1`/`H2`/`H3` (heap-shape invariants, e.g. a
  region's bridge object is in its own objMap, at most one external ref to a region, region-internal
  refs resolve back into that region), `S1`/`S2`/`S3` (stack-shape invariants, e.g. no two frames share
  a region, no reference from an earlier frame into a strictly later frame/region), and `HS1` ("no
  dangling pointers" — every `Reference.OId oid` stored anywhere in `cfg.refs` has `oid ∈
  cfg.objectIds`; see the comment above its definition for the full rationale — `H2`/`H3`/`S2`/`S3`
  alone are vacuous for a stored ref that doesn't yet resolve to anything, so nothing else rules out a
  stale reference coincidentally colliding with a freshly allocated id later on). Also has lemmas
  relating an id's `loc?` to where it actually sits in the stack/heap (`oid_loc_rgn_iff_in_heap`,
  `oid_loc_stk_iff_in_stack`).
- `Mutation/` — the operational semantics, one file per operation (`Enter`, `Exit`, `FieldAsgn`,
  `MakeObjRegion`, `MakeObjStack`, `MakeRegion`, `Merge`, `Swap`, `VarAsgn`); `Mutation.lean` is a
  9-line aggregator importing all nine. Each `Mutation/<Op>.lean` defines the operation itself
  (`varAsgn`, `fieldAsgn`, `swap`, `enter`, `exit`, `makeObjStack`, `makeObjRegion`, `makeRegion`,
  `merge` — each takes a `RuntimeConfig` and returns `Option RuntimeConfig`, `none` meaning the
  transition is stuck/illegal, e.g. an out-of-region write) **and** a public `<op>_cases` lemma
  unpacking the `do`-block into its explicit disjunction-of-∃-bundles branches — reused by both
  `Gc/Model/Preservation/<Op>.lean` and `Gc/Reachability/Referencable/Validity/Preservation/<Op>.lean`.
- `Mutation/Stmt.lean` — reifies a single operation as data: `inductive Stmt` (one constructor per
  operation, carrying its arguments) plus `step : Stmt → RuntimeConfig → Option RuntimeConfig`
  dispatching to the real operation. Lets later layers state "for all 9 operations" claims by
  quantifying over `Stmt` instead of writing 9 separate theorems.
- `Start.lean` — `RuntimeConfig.start` (the initial configuration: one root region, one root frame) and
  a proof that it satisfies `ValidConfig`.
- `Preservation/*.lean` — one file per `Mutation` operation. Each proves that the operation preserves
  `ValidConfig` by discharging the 9 sub-invariants (`<op>_L1` … `<op>_S3`, plus `<op>_HS1`)
  individually and then combining them into a single `<op>_valid : ValidConfig cfg → op ... cfg = some
  cfg' → ValidConfig cfg'`. **This is the recurring proof-engineering pattern in the repo** — a new
  mutation operation is expected to get its own `Preservation/<Op>.lean` following this same shape.
- `Preservation.lean` — aggregator: imports all 9 `Preservation/*.lean` files plus `Mutation/Stmt.lean`
  and defines `StepPreserves`/`AllPreserve` (a property `P` of configs preserved no matter which `Stmt`
  ran) and `allPreserve_ValidConfig : AllPreserve ValidConfig`, dispatching to the 9 `<op>_valid` proofs
  via `cases cmd with` on `Stmt`.
- `Preservation/Common.lean` — generic, non-operation-specific facts factored out of individual
  operation files once they were needed by more than one: `heap_objectIds_of_mem`,
  `swap_corollary_stackWithIndex_index_inj`/`_find_eq`, `merge_corollary_regionId_unique_index`,
  `stackWithIndex_getElem_index_eq`, `stackWithIndex_frame_transport_down_of_shape_eq`/`_up_of_shape_eq`,
  `stackWithIndex_objMap_get_eq_of_last_varMap_update`. Names were kept identical to wherever they were
  originally defined, so check here first before re-deriving a stack/heap transport fact from scratch.
- `Theorems.lean` — generic `List`/`AList` lemmas (not domain-specific) used as a small helper library
  by the `Preservation` proofs (e.g. `List.find?_eq_some_of_unique`, `List.kunion_eq_append_of_disjoint_keys`,
  `List.two_le_count_flatMap_of_ne`, `List.count_le_count_flatMap_of_mem`).

Each `<op>_valid` proof only needs `ValidConfig cfg`, i.e. it is a *single-config* invariant — no
per-operation proof here reasons about reachability chains.

### `Gc/Reachability/Referencable/` — reachability/liveness over `RefStep` (complete, zero `sorry`)

`RefStep` (defined in `Semantics.lean`) stops dead the moment a chain hits a region reference (`RId`) —
it never crosses a region boundary. This is what report.pdf's own reachability notion formalizes.

- `Semantics.lean` — `RefStep` (`a` steps to `b` when `b` is a field value of the object `a` currently
  resolves to, via `Reference.objAt?`) and `RefStep.exists_oid_left`; `RegionReachable` (reachable from
  a region's bridge object, staying inside the region), `StackReachable`/`FrameReachable` (reachable
  from stack variables, optionally scoped to one frame's stack-index), and `FrameRoot` (the two ways a
  `FrameReachable` chain can start: a stack var's value, or a frame's own region's bridge object). Also
  proves `RegionReachable_iff_reflTransGen`/`FrameReachable_iff_reflTransGen`, converting the inductive
  props to `Relation.ReflTransGen (RefStep cfg) start ref` form — the representation almost every
  CR1–CR5 proof actually works with.
- `Path.lean` — a thin `Path`/`ValidPath` wrapper (`path.refs : List Reference`, valid when consecutive
  refs are linked by `RefStep`) used specifically by the CR2 proof, which needs to reason about *every*
  element of a chain (via `List.IsChain` induction), not just its endpoints.
- `Corollaries/` — the reusable, non-operation-specific reachability lemmas, split into
  `Corollaries/{Common,CR1,CR2,CR4}.lean` (each downstream file imports exactly what it needs).
  - **`Common.lean`**: `RegionReachable_stays_in_region` (H3-driven: once a chain resolves into a
    region, it never leaves), `ReflTransGen_rgn_confined` (the region-chain analogue of CR2, rooted at
    an arbitrary point), `FrameRoot_upper_bound`/`RefStep_upper_bound_step`/`ReflTransGen_upper_bound`
    (the S2/S3-driven upper-index-bound argument behind CR2), `FrameReachable_owner_index_le`/
    `_stk_index_le` (packaged wrappers: anything reached along a `FrameReachable cfg frameY.index _`
    chain has owner/slot index `≤ frameY.index` — the workhorses several `<op>_cr3`/`CR5_step` proofs
    call for their "already visible from some no-later frame" argument), and
    `resolveV_frameRoot`/`resolveFA_frameReach` (a shared pair used across `FieldAsgn`/`VarAsgn`/`Swap`).
  - **`CR1.lean`**: if a region has an associated (on-stack) frame, everything region-reachable in it is
    also frame-reachable from that frame.
  - **`CR2.lean`**: a path rooted at frame F, ending at an object in F's own region, never passes
    through any *other* frame's stack slot. Built from the S2/S3-driven upper/lower index bounds in
    `Common.lean`, combined via `le_antisymm`.
  - **`CR4.lean`**: an object living in a region owned by (on-stack) frame `frame` is stack-wide
    reachable (`StackReachable`) iff it's already reachable from `frame` alone (`FrameReachable cfg
    frame.index _`). Covers both an in-region object and a region reference (`RId`) one field-hop
    beyond an in-region object — the `RId` case leans on `H2`'s global uniqueness of a region
    reference's storage location to trace the chain back to the in-region object.
- `Invariants.lean` — cross-config properties about reachability being preserved for suspended regions
  and earlier frames across a transition; definitions only, no proofs (superseded in practice by
  `CR5_step` below).
- `Guarantees.lean` — empty (placeholder for the eventual GC-safety theorems).
- `Validity/` — `CR3`, a `ValidConfig`-style invariant *specifically* about reachability:

  ```
  def CR3 (cfg : RuntimeConfig) : Prop :=
    ∀ frame ∈ cfg.stackWithIndex, ∀ frame' ∈ cfg.stackWithIndex,
      frame.index < frame'.index →
      ∀ oid, (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) →
      FrameReachable cfg frame'.index (Reference.OId oid) →
      FrameReachable cfg frame.index (Reference.OId oid)
  ```

  ("if an object lives in a suspended region owned by an earlier frame F, and is frame-reachable from
  some later frame F', it's already frame-reachable from F itself" — report.pdf CR3). Unlike L1–HS2,
  CR3 isn't provable from a `ValidConfig` snapshot alone — it's proved to hold at `RuntimeConfig.start`
  (`Validity/Start.lean`) and preserved by every `Mutation.lean` operation
  (`Validity/Preservation/*.lean`), mirroring `Gc/Model/Preservation/*.lean`'s per-operation pattern.
  `ValidReachableConfig cfg extends ValidConfig cfg` with a `cr3` field. All 9 operations proved, zero
  `sorry`; `Validity/Preservation.lean` aggregates them (`allPreserve_ValidReachableConfig`).

  Also has `CR5.lean` (report.pdf CR5: "activity in an active region and frame cannot affect the
  stack-reachability of objects within suspended regions"), formalized as a per-operation single-step
  fact (mirroring how CR3 itself is proved):

  ```
  def Suspended (cfg : RuntimeConfig) (i : Index) : Prop :=
    ∃ frame ∈ cfg.stackWithIndex, frame.index = i ∧ i < cfg.stackWithIndex.length - 1

  def CR5_step (cmd : Stmt) : Prop :=
    ∀ cfg cfg' : RuntimeConfig, ValidReachableConfig cfg → step cmd cfg = some cfg' →
      ∀ i, Suspended cfg i → ∀ ref, FrameReachable cfg i ref →
      (StackReachable cfg ref ↔ StackReachable cfg' ref)
  ```

  `CR5_step` is deliberately *restricted* to references already `FrameReachable` from the suspended
  frame — an unrestricted `∀ ref, StackReachable cfg ref ↔ StackReachable cfg' ref` is false (e.g.
  `makeObjStack` can make a brand-new object `StackReachable` in `cfg'` via the active frame's own
  fresh var, with no connection to any suspended region). `cr5_step_of_helper` upgrades a simpler
  `CR5_helper_step` (`FrameReachable cfg i ref ↔ FrameReachable cfg' i ref`) into the restricted
  `StackReachable` form for free, since once `ref` is already `FrameReachable` from the suspended
  frame, `StackReachable cfg ref` is trivially witnessed and `StackReachable cfg' ref` falls out of
  unfolding `FrameRoot`. All 9 operations proved, zero `sorry`, dispatched by `cr5_step_all`.

  Multi-step CR5 (chaining `CR5_step` over an arbitrary-length trace, the actual report.pdf claim
  rather than just one operation) is not currently being pursued.

### `Gc/Reachability/Reachable/` — sibling reachability layer over `deref?` (complete, zero `sorry`)

A folder alongside `Referencable/`. Not yet imported from `Gc.lean`, so it isn't built by a bare `lake
build` — check it via qualified-name builds (`lake build Gc.Reachability.Reachable.Scratch`) or the
Lean LSP tools. This layer deliberately does **not** import anything from `Gc.Reachability.Referencable`
(explicit user instruction) — its own `Semantics.lean` restates `deref?`/`ReachableStep` fresh rather
than reusing `Referencable`'s `RefStep`, even though the two are almost the same shape. The reason it
exists as a sibling rather than living inside `Referencable/`: `Reachable/`'s `deref?` is deliberately
*stronger* than `Referencable/`'s `objAt?` — an `RId` step is allowed to continue into a **Closed**
region's own bridge object, so a chain can cross a region boundary that `Referencable/` would stop at.
See `Gc/Reachability/Reachable/Corollaries.lean`'s own header comment for the precise phrasing. See also
[[project_region_object_reachability_seam]] (memory) on why `RegionReachable`/`FrameReachable` never
cross an `RId` boundary within one relation.

- `Semantics.lean` — `Reference.deref?` (the `OId` branch is exactly `Referencable`'s `objAt?` restated
  via `do`-notation; the new content is the `RId` branch, which steps into a `Closed` region's bridge
  object, `none` if `Open`), `ReachableStep` (`a` steps to `b` via `deref?`, not `objAt?`),
  `RegionReachable`/`FrameReachable`/`StackReachable`/`FrameRoot` (same shape as
  `Referencable/Semantics.lean`'s, built on `ReachableStep`), and
  `RegionReachable_iff_reflTransGen`/`FrameReachable_iff_reflTransGen`.
- `Corollaries.lean` — `deref?_oid_eq_objAt?`/`ReachableStep_rid_iff`/`ReachableStep_oid_iff` (unfolding
  lemmas for the two `ReachableStep` sources), `RegionReachable_implies_FrameRechable`, and:
  - `FrameReachable_at_later_frame_implies_FrameReachable_at_frame cfg` — a CR3-style property (same
    shape as `Referencable`'s report.pdf `CR3`, restated over this layer's own `FrameReachable`). Used as
    an explicit hypothesis by `StackReachable_invariant_for_suspended_region_objects` below; its own
    single-step preservation across every mutation is proved separately, in `Scratch2.lean` (not yet
    proved to hold at `RuntimeConfig.start`, nor bundled into a `ValidReachableConfig`-style invariant
    the way `Referencable/`'s `CR3` is).
  - `StackReachable_invariant_for_suspended_region_objects cmd` — the layer's headline claim: for a
    `ValidConfig cfg`, a mutation `cmd`, and a frame `frame` whose region is *suspended* (index strictly
    below the active/last frame's) and holds some `oid`, `StackReachable cfg (OId oid) ↔ StackReachable
    cfg' (OId oid)` — "liveness of objects in suspended regions is invariant to activity in an active
    region" (the user's own reformulation of report.pdf Section 5 paragraph 4's claim; deliberately
    drops the paper's "as long as the active region remains active" qualifier, judged unnecessary for
    this single-step, per-operation formulation).
- `Lemmas.lean` — a growing, per-operation reusable lemma toolkit (mirrors `Referencable/Validity/
  Preservation/*.lean`'s per-op corollary convention, but kept in one file since the eventual per-op
  split isn't decided yet). Holds general machinery (`SafeRef`/`predecessor_safe`/
  `safe_reflTransGen_transport` — a backward, H3/L2-driven chase; `stackWithIndex_find_index_eq_getElem`,
  `stackWithIndex_getLast_mem` — generic `stackWithIndex`↔`getLast?`/index facts) and per-operation
  corollaries proving the `loc?`/`objAt?`/`ReachableStep` agreement facts and frame-membership
  transports each op's proof needs.
- `Scratch.lean` — one `stackReachable_invariant_<op>` theorem per `Stmt` constructor (all 9 proved,
  zero `sorry`), plus a `stackReachable_invariant_all` dispatcher (`cases cmd with ...`) mirroring
  `Referencable/Validity/Preservation.lean`'s `allPreserve_ValidConfig` pattern. Despite the name, this
  file holds genuine, load-bearing proof content, not throwaway exploration — kept as one file rather
  than split per-op since the layer is still mid-draft architecturally.
- `Scratch2.lean` — one `frameReachableAtLaterFrame_step_<op>` theorem per `Stmt` constructor (all 9
  proved, zero `sorry`), plus a `frameReachableAtLaterFrame_step_all` dispatcher; proves
  `FrameReachableAtLaterFrame_step cmd`, i.e. single-step preservation of
  `FrameReachable_at_later_frame_implies_FrameReachable_at_frame` (see the `Corollaries.lean` bullet
  above). Unlike `Scratch.lean`'s property (which only needs *some* witness frame reaching `oid`), this
  one needs reachability specifically from the given earlier frame, so `varAsgn`/`fieldAsgn`/`swap` each
  need a genuine index-bound "escape" argument (frame.index ≤ frameY.index for whatever frame the
  reachability chain actually rooted from, via `fieldAsgn_region_container_confined` — fully generic
  despite the name) rather than just transport. `merge`'s proof rebuilds its own local transport toolkit
  here rather than sharing one with `Scratch.lean`'s `merge` proof, unlike every other op (which shares a
  single `<op>_frame_reachable_iff` in `Lemmas.lean`) — a known duplication, not yet cleaned up.

## Proof-engineering gotchas (recurring across this codebase's proof style)

These keep resurfacing across files in all three layers above; check here before re-deriving a
workaround from scratch.

- **`rw [find?_cons_of_pos/neg h]` fails via higher-order-unification ambiguity** when `h`'s type is an
  unreduced lambda application (Lean infers the wrong split of predicate/argument from `h`'s type
  alone). Fix: state the target `find?` equality as its own fully-concrete-typed `have` first (proved
  via `exact`/plain term application from `h`, not `rw`), then `rw` with that `have` instead of `h`
  directly.
- **Multi-line record literals inside a `have`'s/theorem's type** (e.g. a new `Frame`/`Region`/
  `RuntimeConfig` literal split across lines) repeatedly hit a hard parser error ("unexpected
  identifier; expected '}'") unrelated to the math. Fix: `set newFrame : Frame := { ... } with
  newFrame_def` once, right after its dependencies are established, then refer to `newFrame`
  everywhere afterward (`set` also retroactively abstracts existing goal occurrences of the literal).
  Alternatively collapse the literal onto one line with an explicit type ascription.
- **`cases h : e with` generalizes *every* occurrence of `e`**, including inside a goal's own
  `∃`-conjuncts or hypotheses introduced earlier — not just the term you meant to case on. Fix: use
  `rfl` in place of the naively-expected hypothesis where an existential conjunct got silently
  rewritten to a reflexive equation, or avoid a blanket `subst`/`cases` and instead `rw [h] at
  <specific hypothesis>` targeted precisely.
- **A lemma stated with `match ... with` syntax cannot be applied via `rw`/`simp`**, even when the
  goal's `match` expression is alpha-equivalent to the lemma's LHS — each *occurrence* of `match`
  syntax compiles to its own distinct auxiliary `match_1`/`match_2` definition, and `rw`/`simp` match on
  that syntactic head, not up to defeq. Fix: apply the lemma as a **term**, not a rewrite rule — build
  intermediate `have`s for each side, `rw` any needed equalities *inside* those (safe, no `match`
  involved), then close via `.trans`/`exact` (which check by full defeq).
- **`X ▸ h` can fail on `n + 1` vs `.succ` display-form mismatches**, even when the underlying types are
  defeq. Fix: use `rw [X] at h` (or `rw [X] at h ⊢`) followed by a separate closing tactic, rather than
  a one-shot `▸` term.
- **`omega` occasionally fails on visibly-sufficient `Nat` constraints** ("No usable constraints found")
  despite all the needed facts being literally in context, and can succeed moments later via
  `lean_multi_attempt` on the identical goal — treat as LSP/omega-state flakiness, not a real proof gap.
  Work around with an explicit lemma application (e.g. `Nat.le_of_lt_succ`, `Nat.not_le.mpr`) instead of
  retrying `omega` in place.
- **`AList.insert` at an already-present key reorders `.entries`** (via the underlying `kinsert`/
  `kerase`), unlike inserting at a genuinely fresh key (`AList.entries_insert_of_notMem`, no reorder).
  Build a `List.Perm` fact via `List.exists_of_kerase` + `NodupKeys.eq_of_mk_mem`-style reasoning when a
  proof needs to survive an existing-key insert.
- **`Stack.objectIds`/`Stack.refs` don't resolve via dot notation on a bare `List Frame`** — e.g.
  `cfg.stack.dropLast.objectIds` fails ("environment does not contain `List.objectIds`") because
  `List.dropLast`'s return type is bare `List Frame`, not the `Stack` alias. Write these as prefix
  applications instead, `Stack.objectIds cfg.stack.dropLast`, whenever the receiver came from a `List`
  op like `dropLast`/`++`.
- **Mixing `=` and `~` (`List.Perm`) steps in one `calc` block doesn't parse** in this project. Build
  `List.Perm` arguments as a flat sequence of separately-named `have`s instead, chained via explicit
  `▸`/`.trans`.
- **`AList.mem_insert.mpr` doesn't resolve as dot notation** — call it as `(AList.mem_insert _).mpr
  (...)`.
- **`Status` derives `BEq`/`DecidableEq` but not `LawfulBEq`**, so `beq_iff_eq` fails to synthesize on
  it — case-split on `region.status` directly instead.
- **After `rw [hne]` turns an `ite` condition into `false = true`, `split_ifs <;> omega` doesn't
  discharge it** — `omega` doesn't inspect `Bool`-equality hypotheses. Eliminate the always-false branch
  explicitly first, e.g. `rw [if_neg (by decide)]`.
- **A `rw [...]` list with the same-shaped lemma appearing twice can silently rewrite the wrong
  occurrence** (e.g. two `List.count_append`s). Split into separately-named `have`s per side instead of
  one combined `rw` list.
- **A record literal `{ x with ... }` inside a standalone `have`'s type elaborates at `x`'s own
  declared type**, not the context's expected type (e.g. yields `FrameWithIndex` instead of `Frame`).
  Fix with an explicit ascription: `({ x with ... } : Frame)`.
- **Passing a replacement record (e.g. `newFrame`/`newRegion`) as an *implicit* argument, relying on
  unification to recover it from a hypothesis, can silently mis-unify** to a trivial/wrong value,
  sometimes surfacing as a confusing type mismatch several lines later rather than at the call site.
  Make such arguments **explicit** (or pass via named `(newVal := ...)`) instead.
- **`subst heq` (from a freshly-`intro`'d variable equated to an outer one) can eliminate the *outer*
  variable instead of the fresh one**, silently renaming it out of scope for later code (surfaces as an
  "unknown identifier" several lines later, not at the `subst` site). Use `rw [heq] at <specific
  hypothesis>` instead of a blanket `subst`.
- **`AList.lookup_insert`'s underlying `AList` argument sometimes needs to be supplied explicitly**
  (e.g. `AList.lookup_insert cfg.heap`) when it can't be inferred purely from the expected-type
  unification context.
- **`induction ... using Relation.ReflTransGen.head_induction_on` bloats its motive** if a hypothesis
  mentioning the chain's start point is already in scope when the induction starts. Generalize the
  chain's start point away first (state the induction over an explicit `∀ a b, ...` rather than the
  fixed endpoints already in context).

### Proving technique for CR3/CR5-style "suspended region unaffected by active-frame mutation" claims

The recurring shape across `<op>_cr3`, `CR5_step`, and `stackReachable_invariant_<op>`: if the mutated
operation is purely *additive* or only touches the active (last) frame's own `varMap`/scalar fields
(never `objMap` content), the step relation (`RefStep`/`ReachableStep`) is provably pointwise-equal or
equal-up-to-a-fresh-id between `cfg`/`cfg'`, so no per-hop induction is needed — only the *root set*
needs transporting. When an operation genuinely edits an existing object's field content
(`FieldAsgn`/`Swap`), the step relation itself changes for the mutated container, and the proof needs a
per-hop induction (`Relation.ReflTransGen.head_induction_on`) with an "escape" branch for the one hop
that uses the newly-written edge — closed either via an owner-index bound (`FrameReachable_owner_index_le`
et al., showing the mutated/active container can never be reached from an already-suspended root) or by
tracing the newly-written value's own independent root (`resolveV_frameRoot`/`resolveFA_frameReach`).

## Comment style

Lean comments (`--`) in this repo must be single-line only. Do not write multi-line/wrapped comment
blocks above declarations, even for non-obvious rationale — keep each comment to one line, or omit it.
