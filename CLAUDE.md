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
  executable, with zero `sorry`s anywhere under `Gc/` (verified project-wide as of 2026-07-29). The
  original broken `Gc/Reachability/Reachability.lean` (a fuel-based computational reachability walk that
  pattern-matched on wrong `Location` constructor names — `Location.Stack`/`Location.Region` instead of
  the real `Location.Stk`/`Location.Rgn` — and never built) was deleted outright rather than just excluded
  from the build; the inductive `FrameReachable`/`RefStep` machinery in `Gc/Reachability/Referencable/Semantics.lean`
  made it redundant. `Main.lean`'s undefined `hello` (leftover from the `lake new` template) was replaced
  with a plain greeting. Still prefer building the specific module(s) you're touching by qualified name
  for faster iteration, e.g. `lake build Gc.Model.Theorems`.
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

The proof development has two layers under `Gc/`:

### `Gc/Model/` — the runtime model and its operational semantics (mature/primary layer)

- `Types.lean` — the core data model: `RegionId`/`ObjectId`/`BridgeObjectId`, `Reference` (`RId`/`OId`),
  `VarMap`/`ObjMap` (as `AList`s), `Region` (bridge object + objects + open/closed `Status`), `Frame`
  (a stack frame: its region, bridge var, local var map and local obj map), `Stack`, `Heap`,
  `RuntimeConfig` (`stack` + `heap`), and `Location` (`Rgn`/`Stk`).
- `Helpers.lean` — projections and derived queries over the model: collecting `refs`/`objectIds` from
  frames/regions/heap/stack, `freshObjectId`, resolving where a `Reference` lives (`Reference.loc?`),
  and resolving variable/field-access expressions against a config (`resolveV`, `resolveFA`). Also has
  `RuntimeConfig.freshObjectId_not_mem` (added 2026-07-25): `cfg.freshObjectId ∉ cfg.objectIds`, proved
  via two small generic lemmas in `Theorems.lean` (`List.le_foldl_max_self`, `List.mem_le_foldl_max`)
  about `List.foldl max`. This required adding `import Gc.Model.Theorems` to `Helpers.lean` (no cycle:
  `Theorems.lean` still doesn't import anything domain-specific).
- `Validity.lean` — defines `ValidConfig` as a bundle of **9** named invariants: `L1`/`L2` (global,
  e.g. object-id uniqueness, stack regions are Open), `H1`/`H2`/`H3` (heap-shape invariants, e.g. a
  region's bridge object is in its own objMap, at most one external ref to a region, region-internal
  refs resolve back into that region), `S1`/`S2`/`S3` (stack-shape invariants, e.g. no two frames share
  a region, no reference from an earlier frame into a strictly later frame/region), and **`HS1`** (added
  2026-07-25: "no dangling pointers" — every `Reference.OId oid` stored anywhere in `cfg.refs` has
  `oid ∈ cfg.objectIds`; see the comment directly above its definition in `Validity.lean` for the full
  rationale). Also has lemmas relating an id's `loc?` to where it actually sits in the stack/heap.
  **Why `HS1` was added**: while planning `MakeObjStack.lean`'s `S2`/`S3` proofs, the original 8
  invariants turned out insufficient to prove them from `ValidConfig cfg` alone — none of `H2`/`H3`/`S2`/
  `S3` say anything about a stored `OId`/`RId` ref that *doesn't yet* resolve to anything (they're all
  `ref.loc? cfg = some _ → ...`, vacuous otherwise), so nothing ruled out a stale/dangling reference
  value coincidentally colliding with a *freshly allocated* id later on. `HS1` closes that gap. Adding a
  9th field to `ValidConfig` meant every existing `<op>_valid` constructor across `Preservation/*.lean`
  needed an `hs1 := ...` field — see per-file notes below for what each got.
- `Mutation/` — the operational semantics, one file per operation (`Enter`, `Exit`, `FieldAsgn`,
  `MakeObjRegion`, `MakeObjStack`, `MakeRegion`, `Merge`, `Swap`, `VarAsgn`; split out of a single
  `Mutation.lean` file at some point before 2026-07-25 — `Mutation.lean` itself is now just a 9-line
  aggregator importing all nine). Each `Mutation/<Op>.lean` defines the operation itself (`varAsgn`,
  `fieldAsgn`, `swap`, `enter`, `exit`, `makeObjStack`, `makeObjRegion`, `makeRegion`, `merge` — each
  takes a `RuntimeConfig` and returns `Option RuntimeConfig`, `none` meaning the transition is
  stuck/illegal, e.g. an out-of-region write) **and** a public `<op>_cases` lemma unpacking the `do`-block
  into its explicit disjunction-of-∃-bundles branches. This case-split lemma used to be reproven ad hoc
  inside each `Preservation/<Op>.lean` file (see the per-file gotchas below, e.g. `merge_cases`); it now
  lives once alongside the operation and is reused by both `Gc/Model/Preservation/<Op>.lean` and
  `Gc/Reachability/Referencable/Validity/Preservation/<Op>.lean`.
- `Mutation/Stmt.lean` — reifies a single operation as data: `inductive Stmt` (one constructor per
  operation, carrying its arguments) plus `step : Stmt → RuntimeConfig → Option RuntimeConfig`
  dispatching to the real operation. Lets later layers state "for all 9 operations" claims by quantifying
  over `Stmt` instead of writing 9 separate theorems — used by `Preservation.lean` below and by
  `Gc/Reachability/Referencable/Validity/Preservation.lean`/`Validity/CR5.lean`.
- `Start.lean` — `RuntimeConfig.start` (the initial configuration: one root region, one root frame) and
  a proof that it satisfies `ValidConfig`.
- `Preservation/*.lean` — one file per `Mutation` operation. Each proves that the operation preserves
  `ValidConfig` by discharging the 9 sub-invariants (`<op>_L1` … `<op>_S3`, plus `<op>_HS1`) individually
  and then combining them into a single `<op>_valid : ValidConfig cfg → op ... cfg = some cfg' →
  ValidConfig cfg'`. **This is the recurring proof-engineering pattern in the repo** — a new mutation
  operation is expected to get its own `Preservation/<Op>.lean` following this same shape.
- `Preservation.lean` — aggregator: imports all 9 `Preservation/*.lean` files plus `Mutation/Stmt.lean`
  and defines `StepPreserves`/`AllPreserve` (a property `P` of configs preserved no matter which `Stmt`
  ran) and `allPreserve_ValidConfig : AllPreserve ValidConfig`, dispatching to the 9 `<op>_valid` proofs
  via `cases cmd with` on `Stmt`.
- `Theorems.lean` — generic `List`/`AList` lemmas (not domain-specific) used as a small helper library
  by the `Preservation` proofs.

### `Gc/Reachability/Referencable/` — reachability/liveness definitions (now substantially built out)

**Note**: this whole layer used to live directly under `Gc/Reachability/`; it was moved into a
`Referencable/` subfolder (2026-07-30, mechanical rename — file contents/module logic unchanged,
only the `Gc.Reachability.*` module path grew a `.Referencable` segment) to make room for a sibling
`Gc/Reachability/Reachable/` folder (see its own bullet at the end of this section) that will hold a
different reachability notion.

- `Semantics.lean` — `RefStep` (`a` steps to `b` when `b` is a field value of the object `a` currently
  resolves to, via `Reference.objAt?`) and its `RefStep.exists_oid_left` lemma (moved here from
  `Gc/Model/Helpers.lean` on 2026-07-29 — reachability-specific, not a core model helper, so it now
  sits next to the inductive props defined in terms of it), `RegionReachable` (reachable from a region's
  bridge object, staying inside the region), `StackReachable`/`FrameReachable` (reachable from stack
  variables, optionally scoped to one frame's stack-index), and `FrameRoot` (the two ways a
  `FrameReachable` chain can start: a stack var's value, or a frame's own region's bridge object). Also
  proves `RegionReachable_iff_reflTransGen`/`FrameReachable_iff_reflTransGen`, converting the inductive
  props to `Relation.ReflTransGen (RefStep cfg) start ref` form — the representation almost every
  CR1–CR3 proof actually works with.
- `Path.lean` — a thin `Path`/`ValidPath` wrapper (`path.refs : List Reference`, valid when consecutive
  refs are linked by `RefStep`) used specifically by the CR2 proof, which needs to reason about *every*
  element of a chain (via `List.IsChain` induction), not just its endpoints. Imports
  `Gc.Reachability.Referencable.Semantics` for `RefStep` (picked up 2026-07-29 when `RefStep` moved out of
  `Gc/Model/Helpers.lean`).
- `Corollaries/` — the reusable, non-operation-specific reachability lemmas. Originally a single
  ~1000-line `Corollaries.lean`; **split 2026-07-29** into `Corollaries/{Common,CR1,CR2,CR4}.lean`
  (mirroring the `Model/Preservation/Common.lean` consolidation pattern) once it had grown into a
  grab-bag mixing generic machinery with CR-specific proofs — each `Validity/Preservation/*.lean` file's
  import now points at exactly what it needs (three of the nine needed nothing from it at all). In the
  same 2026-07-29 session, headline theorems were renamed to bare `CR1`/`CR2`/`CR4` (dropping
  descriptive suffixes) to match report.pdf's own numbering — the same rename applied to `CR5'`→`CR5`,
  see `Validity/CR5.lean` below.
  - **`Common.lean`**: reusable `ReflTransGen`-flavored machinery not specific to any one CR —
    `RegionReachable_stays_in_region` (H3-driven: once a chain resolves into a region, it never leaves),
    `ReflTransGen_rgn_confined` (the same fact restated for an arbitrary `ReflTransGen` chain rather
    than a `RegionReachable` one — the `RefStep`-chain analogue of CR2, but for regions rather than
    stack slots, and rooted at an arbitrary point rather than a `FrameRoot`), `FrameRoot_upper_bound`/
    `RefStep_upper_bound_step`/`ReflTransGen_upper_bound` (the S2/S3-driven upper-index-bound argument
    behind CR2, in both `Path`/`IsChain` and `ReflTransGen` form), `FrameReachable_owner_index_le`/
    `_stk_index_le` (packaged wrappers: anything reached along a `FrameReachable cfg frameY.index _`
    chain has owner/slot index `≤ frameY.index` — the actual workhorses several `<op>_cr3`/`CR5_step`
    proofs call for their "already visible from some no-later frame" argument), and
    `resolveV_frameRoot`/`resolveFA_frameReach` (promoted 2026-07-28 from three byte-for-byte-identical
    `private` copies inside `FieldAsgn.lean`/`VarAsgn.lean`/`Swap.lean`'s CR3 files into one shared
    public pair).
  - **`CR1.lean`** (bare `CR1`, renamed from `RegionReachable_implies_FrameReachable`): if a region has
    an associated (on-stack) frame, everything region-reachable in it is also frame-reachable from that
    frame.
  - **`CR2.lean`** (bare `CR2`, renamed from `Path_from_frame_to_own_region_stays_in_frame`): a path
    rooted at frame F, ending at an object in F's own region, never passes through any *other* frame's
    stack slot. Built from the S2/S3-driven upper/lower index bounds now in `Common.lean`, combined via
    `le_antisymm`.
  - **`CR4.lean`** (bare `CR4`, renamed from `StackReachable_iff_FrameReachable`; drafted 2026-07-28,
    generalized 2026-07-29). Packages CR3 into a single iff — an object living in a region owned by
    (on-stack) frame `frame` is stack-wide reachable (`StackReachable`) iff it's already reachable from
    `frame` alone (`FrameReachable cfg frame.index _`). Drafted by the user as a rough skeleton (one
    sorry, unfinished backward direction); the sorry (`frame.index < frame'.index`, asserted
    unconditionally) was actually false as stated, since the witness frame `frame'` could coincide with
    `frame` itself. Fixed by getting `frame.index ≤ frame'.index` from `FrameReachable_owner_index_le`
    first, then a `.lt_or_eq` split: the strict case invokes CR3 directly, the equality case collapses
    `frame' = frame` via `stackWithIndex` index-uniqueness (`swap_corollary_stackWithIndex_index_inj`,
    from `Gc.Model.Preservation.Common`). Takes an explicit `_hframesus` hypothesis the proof doesn't
    actually need (CR3 is already vacuously satisfied whenever `frame` is the last frame), kept only to
    stay faithful to report.pdf's own CR4 statement. **Generalized 2026-07-29** from `ref :
    Reference.OId oid` specifically to an arbitrary `ref : Reference` with hypothesis `RegionReachable
    cfg frame.regionId ref` — now covers both the original in-region-object case and a new case where
    `ref` is a region reference (`RId`) one field-hop beyond an in-region object. The `RId` case leans
    on `H2`'s global uniqueness of a region reference's storage location to trace the chain back to the
    same in-region object, then reuses the original object-case argument plus one more `RefStep`; needed
    two new small generic list lemmas in `Model/Theorems.lean` (`List.two_le_count_flatMap_of_ne`,
    `List.count_le_count_flatMap_of_mem`).
- `Invariants.lean` — cross-config properties about reachability being preserved for suspended regions
  and earlier frames across a transition (currently just definitions/comments, no proofs yet). Its two
  draft defs (`suspended_regions_maintain_frame_reachability`/`_region_reachability`) were the seed for
  `CR5_step` in `Validity/CR5.lean` (see below).
- `Guarantees.lean` — currently an empty file (placeholder for the eventual GC-safety theorems).
- `Validity/` — a `ValidConfig`-style invariant *specifically* about reachability (`CR3`, see below),
  plus its own `Preservation/*.lean` mirroring `Gc/Model/Preservation/*.lean`'s per-operation pattern,
  and a `Preservation.lean` aggregator (`allPreserve_ValidReachableConfig`, the `Reachability`-layer
  analogue of `Gc/Model/Preservation.lean`'s `allPreserve_ValidConfig`). Also has `CR5.lean` (see its
  own "Current known state" section below) — not yet folded into the `Preservation/` split, since the
  user is deliberately undecided on final architecture for this layer.

Note: an earlier `Gc/Reachability/Reachability.lean` (a fuel-based *computational* reachability walk,
`Region.reachableRefs`/`RuntimeConfig.stackReachableRefs`, rather than the inductive props above) used
to exist here but pattern-matched on wrong `Location` constructor names and never built; it has since
been **deleted entirely** (not just excluded from the build) — see the Commands section above.

### `Gc/Reachability/Reachable/` — new sibling reachability layer (added 2026-07-30, now under active development)

A folder alongside `Referencable/`, added at the same time as the `Reachability/`→
`Reachability/Referencable/` move above. Not yet imported from `Gc.lean`, so none of it is built by a
bare `lake build` until it's wired in — check it via qualified-name builds
(`lake build Gc.Reachability.Reachable.Scratch`) or the Lean LSP tools. Per explicit user instruction,
this whole layer deliberately does **not** import anything from `Gc.Reachability.Referencable` — its
own `Semantics.lean` restates `deref?`/`ReachableStep` fresh rather than reusing `Referencable`'s
`RefStep`, even though the two are almost the same shape. The point of the layer, and the reason it
exists as a sibling rather than living inside `Referencable/`: report.pdf's own reachability notion is
actually about **reference chains**, which stop dead the moment they hit a region reference (`RId`) —
that's what `Referencable/`'s `RefStep`/`objAt?` formalizes. `Reachable/`'s `deref?` is deliberately
*stronger*: an `RId` step is allowed to continue into a **Closed** region's own bridge object, so a
chain can cross a region boundary that `Referencable/` would stop at. See
`Gc/Reachability/Reachable/Corollaries.lean`'s own header comment for the precise phrasing.

- `Semantics.lean` — `Reference.deref?` (the `OId` branch is exactly `Referencable`'s `objAt?`
  restated via `do`-notation — see `deref?_oid_eq_objAt?` in `Corollaries.lean`; the new content is the
  `RId` branch, which steps into a `Closed` region's bridge object, `none` if `Open`), `ReachableStep`
  (`a` steps to `b` via `deref?`, not `objAt?`), `RegionReachable`/`FrameReachable`/`StackReachable`/
  `FrameRoot` (same shape as `Referencable/Semantics.lean`'s, just built on the new `ReachableStep`), and
  `RegionReachable_iff_reflTransGen`/`FrameReachable_iff_reflTransGen` (converting to
  `Relation.ReflTransGen (ReachableStep cfg) start ref` form, the representation the proofs below
  actually work with).
- `Corollaries.lean` — `deref?_oid_eq_objAt?`/`ReachableStep_rid_iff`/`ReachableStep_oid_iff` (unfolding
  lemmas for the two `ReachableStep` sources), `RegionReachable_implies_FrameRechable`, and the two defs
  this whole layer's current work centers on:
  - `FrameReachable_at_later_frame_implies_FrameReachable_at_frame cfg` — a CR3-style hypothesis (same
    shape as `Referencable`'s report.pdf `CR3`, restated over this layer's own `FrameReachable`), taken
    as an explicit hypothesis on the theorem below rather than proved — **its own preservation across a
    mutation isn't proved yet**, deliberately deferred per user direction.
  - `StackReachable_invariant_for_suspended_region_objects cmd` — the actual claim under proof: for a
    `ValidConfig cfg`, a mutation `cmd`, and a frame `frame` whose region is *suspended* (index strictly
    below the active/last frame's) and holds some `oid` (`oid.loc? cfg = Rgn frame.regionId`),
    `StackReachable cfg (OId oid) ↔ StackReachable cfg' (OId oid)` — i.e. "liveness of objects in
    suspended regions is invariant to activity in an active region." This is the user's own
    reformulation of report.pdf Section 5 paragraph 4's claim; deliberately **drops** the paper's own
    qualifier "as long as the active region remains active" (discussed at length and judged unnecessary
    for this single-step formulation — the invariant is stated per-operation, so there's no later point
    at which "the active region" could have already stopped being active).
- `Lemmas.lean` — a growing, per-operation reusable lemma toolkit (mirrors `Referencable/Validity/
  Preservation/*.lean`'s per-op corollary convention, but all in one file rather than split, since this
  layer is still being actively drafted and the eventual per-op split isn't decided yet). Holds both
  general machinery (`SafeRef`/`predecessor_safe`/`safe_reflTransGen_transport` — a backward,
  H3/L2-driven chase used by `enter`'s proof; `stackWithIndex_find_index_eq_getElem`,
  `stackWithIndex_getLast_mem` — generic `stackWithIndex`↔`getLast?`/index facts reused across ops) and
  per-operation corollaries (`enter_*`, `exit_*`, `makeObjStack_*`, `freshObjectId_*`) proving the
  `loc?`/`objAt?`/`ReachableStep` agreement facts and frame-membership transports each op's proof needs.
- `Scratch.lean` — one `stackReachable_invariant_<op>` theorem per `Stmt` constructor (skeletons
  drafted for all 9; proved so far: `enter`, `exit`, `makeObjStack` — see "Current known state" below),
  plus a `stackReachable_invariant_all` dispatcher (`cases cmd with ...`) mirroring
  `Referencable/Validity/Preservation.lean`'s `allPreserve_ValidConfig` pattern. Despite the name, this
  file (like the old, now-deleted `Gc/Scratch.lean`) holds genuine, load-bearing proof content, not
  throwaway exploration — kept as one file rather than split per-op since the whole layer is still
  mid-draft.

## Current known state (check before assuming something works)

Per-operation status of the `Preservation/*.lean` proofs (verified by building each module directly,
not by reading file contents alone):

- **`Exit.lean`** — **fully proved, builds cleanly, zero `sorry`** (as of 2026-07-25, now including
  `exit_HS1`). All 9 invariants (`exit_L1` … the `S1`/`S2`/`S3` analogues, misleadingly named
  `exit_S2`/`exit_S3`/`exit_S4` in the file, plus `exit_HS1`) plus all 3 corollaries (`exit_corollary_1`,
  `exit_corollary_2`, `exit_corollary_3`) have real, fully written proofs. `exit_HS1` was the hardest of
  the three `HS1` proofs done this session (`start`/`enter`/`exit`) because `exit` *removes* a frame:
  unlike `enter`/`makeObjStack` (purely additive, so old refs just permute), a stale ref pointing at
  something that's about to be popped would break `HS1` for `cfg'`. The proof rules this out by
  `by_contra`-assuming a surviving ref resolves into the *popped* frame's exclusive objectIds, then
  deriving a contradiction from `vcfg.s2` (if the stale ref lived in an earlier, still-present frame) or
  `vcfg.h3` (if it lived in the heap) against the OLD config — i.e. `S2`/`H3` on `cfg` already prevented
  anyone from holding a forward-reference to the frame that's about to be popped, so no genuinely
  dangling ref can newly appear in `cfg'`. `exit_corollary_3` (the original last gap) required two more
  reusable helper lemmas
  alongside the three from `exit_corollary_1` (`heap_oid_unique_key`, `heap_objectIds_of_mem`,
  `List.find?_eq_some_of_unique`): `heap_status_update_find_none_iff` (a heap `find?` for a given `oid`
  is unaffected — as a `none`-preserving fact — by a status-only update at a key that already existed)
  and `stack_frame_oid_disjoint_of_dropLast` (L1's global object-id uniqueness rules out the
  about-to-be-popped last frame containing an `oid` that's already present earlier in the stack). Axiom
  check (`lean_verify`/`lean4-skills-check-axioms-inline`) confirms every declaration in the file only
  depends on `propext`/`Classical.choice`/`Quot.sound`, i.e. no accidental `sorry` leakage through a
  dependency. Recurring gotcha worth remembering for future proofs in this style: `rw
  [find?_cons_of_pos/neg h]` frequently fails via higher-order-unification ambiguity when `h`'s type is
  an unreduced lambda application; work around it by stating the target `find?` equality as its own
  fully-concrete-typed `have` first (with `h` as the proof term), then `rw` with that `have` instead of
  `h` directly. Same applies to defeq-only mismatches when supplying a record literal that only differs
  by one field (e.g. `status`) to a hypothesis expecting the original value — prefer a fully explicit
  term over `_` so elaboration doesn't propagate the wrong expected type into the hole.
- **`Enter.lean`** — **fully proved, builds cleanly, zero `sorry`, zero warnings** (as of 2026-07-25, now
  including `enter_HS1`). All 9 invariants (`enter_L1` … `enter_S3`, plus `enter_HS1`) plus `enter_valid`
  are real proofs. `enter_HS1` was easy relative to `exit_HS1` (`enter` is additive: pushes an empty
  frame and flips a heap region's status, never changing any objMap/varMap *content*) — it's a pure
  `List.Perm` argument (`cfg'.refs.Perm cfg.refs` and `cfg'.objectIds.Perm cfg.objectIds`, built the same
  way as the local permutation `have`s already inside `enter_L1`/`enter_H2`, just re-derived locally
  since nothing was factored out into a reusable corollary) composed with `vcfg.hs1`. Three reusable
  corollaries carry the weight: `enter_corollary_1` (heap region/oid uniqueness, stated over bare `L1
  cfg` rather than full `ValidConfig cfg` so it's usable on `cfg` inside proofs about `cfg'` before
  `cfg'`'s validity is established), `enter_corollary_2` (`(OId oid).loc? cfg = (OId oid).loc? cfg'`;
  the heap side needed a case split directly on the *main goal* rather than a standalone `find?`-equality
  lemma, since the entered region's `status` genuinely differs between `cfg`/`cfg'` when the entered
  `rid` is the one being looked up — a small match-congruence `have` shows the discarded `Region` isn't
  read by the outer `Location` match, so the differing `status` doesn't matter), and `enter_corollary_3`
  (the general `ref.loc? cfg = loc ↔ ref.loc? cfg' = loc`, reducing to `enter_corollary_2` for `OId` and
  to a heap-key-permutation argument for `RId`). `enter_H3`, `enter_S2`, `enter_S3` all lean on
  `enter_corollary_2`/`_3` to transport the `loc?` fact across the mutation; `enter_S1` instead uses `L2`
  directly (the freshly-pushed frame's region must have been Closed just before `enter` flips it Open, so
  no existing Open-region frame could already share that `regionId`). Three originally-stubbed
  corollaries (`enter_corollary_4`/`_5`/`_6`, refs-permutation facts) turned out unneeded by any of the
  8 invariants — `enter_H2`'s proof already computes the same permutation facts inline via its own
  unnamed `have`s — and were deleted rather than left as dead `sorry` stubs. Axiom check confirms only
  `propext`/`Classical.choice`/`Quot.sound` throughout.
- **`Merge.lean`** — **fully proved, builds cleanly, zero `sorry`** (finished 2026-07-26, across several
  checkpoints: scaffold, `S1`, `H1`, `L2`, `L1`, `HS2`, `H2`, `HS1`, then `H3`, `S2`, `S3`). All 10
  invariants and `merge_valid` are real proofs; axiom check on `merge_valid` confirms only
  `propext`/`Classical.choice`/`Quot.sound`. This was the hardest file in the project — the sole
  `Mutation.lean` operation that actually **relocates** existing objects between heap keys, rather than
  just inserting/overwriting a value at one key.
  - The operation: `merge x cfg` takes the current (last) frame's own region (`region`, must be `Open`)
    and a region referenced by `x` (`region'`, must be `Closed`, looked up via `frame.varMap.lookup x =
    some (RId rid')`), unions `region'.objMap` into `region.objMap` at `frame.regionId`, **erases `rid'`
    from the heap entirely**, and reassigns `x`'s varMap value from `RId rid'` to `OId
    region'.bridgeObjectId` (now itself living inside the merged region). No fresh id is allocated, but
    a whole heap *key* disappears — the first and only `Preservation` operation to do so alongside a
    genuine value relocation (every prior operation's `Reference.loc?` changes, if any, were either
    additive or key-preserving).
  - **Scaffold**: `merge_cases` unpacks the single-branch `do`-block (confirmed via CLAUDE.md's own
    prediction — merge really is the one operation with no location-dependent branching). Core
    corollaries: `merge_corollary_rid_ne_regionId` (`rid' ≠ frame.regionId`, from the mutually exclusive
    Open/Closed precondition), `merge_corollary_region_unique` (`L1`-based, mirrors `MakeObjRegion`'s),
    `merge_corollary_disjoint_keys`/`_union_append` (`region`/`region'`'s objMap keys are disjoint, so
    `region.objMap ∪ region'.objMap`'s `entries` is an *exact* append, not just a `Perm` — no
    `kunion`-induced reordering at all, via a new generic `List.kunion_eq_append_of_disjoint_keys` /
    `AList.union_eq_append_of_disjoint_keys` pair added to `Theorems.lean`).
  - **`merge_corollary_heap_entries_perm`**: extracts `rid'` then `frame.regionId` from `cfg.heap.entries`
    via two applications of `List.exists_of_kerase`, reassembling into
    `⟨frame.regionId,region⟩ :: ⟨rid',region'⟩ :: rest` — the same `rest` (`kerase frame.regionId
    (kerase rid' cfg.heap.entries)`) that `cfg'.heap.entries` is built from via `AList.entries_insert`
    after the erase+insert. This one `Perm` fact underlies `merge_corollary_heap_objectIds_perm`/
    `_heap_refs_perm` (nothing is created or destroyed by the merge, just regrouped into fewer heap
    keys — the merged region's own `objectIds`/`refs` are the *exact* append of `region`'s and
    `region'`'s, via `merge_corollary_mergedRegion_refs`) and, combined with `merge_corollary_rest_notMem`
    (the `rest` tail excludes both erased/reused keys, via `List.notMem_keys_kerase`) and
    `merge_corollary_entries_perm_mem` (`rest`, as membership, embeds back into `cfg.heap.entries`), the
    heap-side uniqueness corollary `merge_corollary_heap'_unique` (at most one `cfg'.heap` entry contains
    a given `oid` — every entry is either the merged head or from `rest`, reducing clashes to `L1`'s
    `region_unique` on `cfg`).
  - **`merge_H1`/`merge_L2`**: straightforward once the scaffold is in place — `H1`'s merged-region case
    is direct (`region.bridgeObjectId ∈ region.objMap.keys ⊆ mergedRegion.objMap.keys` via `mem_union`);
    `L2`'s three-way `by_cases` (frame''.regionId = frame.regionId / = rid' / neither) rules out the
    `rid'` case by contradiction (a stack frame can't have a Closed region) with no `S1`/uniqueness
    machinery needed at all.
  - **`merge_L1`/`merge_HS1`**: `cfg'.objectIds.Perm cfg.objectIds` follows from `heap_objectIds_perm`
    plus the fact that `Stack.objectIds` is *exactly* (not just `Perm`) unchanged — merge only ever
    touches `varMap`, never `objMap`, on the stack side. `HS1`'s one genuinely new stack occurrence
    (`region'.bridgeObjectId`, replacing `x`'s old `RId rid'` value) is already heap-allocated via `H1`
    on `region'`, so it transports into `cfg'.objectIds` trivially via the same `Perm`.
  - **`merge_H2`/`merge_HS2`**: both lean on copying two generic corollaries from `Swap.lean`'s convention
    (`merge_corollary_mem_keys_of_lookup`, `merge_corollary_alist_insert_count_eq` — the additive
    replace-at-existing-key count identity, dodging `Nat` subtraction) applied to the *single* varMap
    slot `x` changes. `H2`: the heap regroup preserves every `RId`'s count exactly (via the `Perm`), and
    the varMap change can only ever *decrease* any particular `RId`'s count, so the sum stays `≤ 1`.
    `HS2`'s harder direction (ruling out `RId rid'` surviving anywhere in `cfg'.refs`) uses `H2` itself as
    a lever: `x`'s own entry was already the *unique* occurrence of `RId rid'` in all of `cfg.refs` (the
    `H2` bound, with `x`'s entry as the witness contributing exactly 1), so once that entry is overwritten,
    the exact (not just `≤`) count drops to 0 — computed via the same additive alist-insert-count identity.
  - **`merge_H3`/`merge_S2`/`merge_S3`** (the hard trio, and the reason this file took the whole session):
    unlike every prior file, `oid`'s `Reference.loc?` genuinely *changes* for objects that were in
    `region'` (`Rgn rid'` in `cfg` → `Rgn frame.regionId` in `cfg'`), so there is no unconditional
    `loc?`-equality corollary here at all (contrast `Swap.lean`'s fully unconditional one). The payoff
    corollary, `merge_corollary_loc_of_mem` (built from `merge_corollary_stack_h1_none` — the stack side
    of `loc?` only ever reads `objMap`, never `varMap`, so a "not found on the stack" fact transports
    unconditionally across merge's only stack change, regardless of *where* the searched-for `oid`
    actually lives — plus `heap'_unique` via `List.find?_eq_some_of_unique`): if `oid` lives in `rid0`'s
    objMap in `cfg'.heap` (whichever heap key that is — the merge target *or* an untouched "rest"
    region), it resolves there in `cfg'` too. `H3` case-splits on `rid = frame.regionId` (referenced
    `oid` comes from `region.refs` or `region'.refs`, pinned via the *existing* `oid_loc_rgn_iff_in_heap`
    theorem applied to `cfg` — full `ValidConfig cfg` is available as `H3`'s own hypothesis, so no
    `L1`-only variant was needed here unlike `heap'_unique`) vs. an unaffected `rest` region (lookup
    transports unconditionally, `rid ≠ rid'` derived by contradiction since `rid'` is no longer a valid
    `cfg'.heap` key). `S2` additionally needed `merge_corollary_heap_find_none_iff_notin` (the heap side
    of `loc?` fails exactly when the oid isn't allocated anywhere — a pure unfolding fact needing no
    `L1`/uniqueness at all) plus a *sharper*, index-tracking version of the stack-none corollary
    (`merge_corollary_stack_h1_index_eq`, via `List.find?_append`'s `Option.or` short-circuit semantics)
    to reconstruct `loc? cfg = Stk fid'` in full from `loc? cfg' = Stk fid'`; from there every case reduces
    to invoking `S2` on `cfg` directly, except the one genuinely new stack occurrence (`x`'s slot holding
    `OId region'.bridgeObjectId`), which turns out **vacuous**: that id is already heap-allocated, directly
    contradicting the just-derived "`oid` not in `cfg'.heap.objectIds`".
  - **`merge_S3`'s surprising resolution**: it initially looks like `merge` breaks `S3` outright — an
    *earlier* (`dropLast`) stack frame could in principle hold a ref that used to resolve into `region'`
    and now resolves into `frame.regionId` (the *current*, highest-index frame's own region), for which
    no valid ancestor could possibly exist (ancestors need index `≤` the holder's, and nothing has a
    smaller index than an already-earlier frame yet *equal or larger* regionId-ownership than the last
    frame). The resolution: this scenario is **already impossible in `cfg`**, by `cfg`'s own `S3` (`+S1`/
    `L2`) — either the referenced `oid` was already in `region.objMap.keys` (then `S3` on `cfg` would
    already have required an ancestor owning `frame.regionId`, which by `S1`'s regionId-uniqueness
    lifted to `FrameWithIndex` — new corollary `merge_corollary_regionId_unique_index`, via
    `List.Nodup.getElem_inj_iff` — could only be `frame` itself, whose index exceeds any `dropLast`
    frame's, contradiction), or `oid` came from `region'` (then `S3` on `cfg` would need an ancestor
    owning `rid'`, but `rid'` is `Closed` so by `L2` no stack frame can have that regionId, contradiction).
    So the `dropLast`-frame case of `rid0 = frame.regionId` closes by contradiction, never needing a real
    witness; the trivial witness (`frame`/`newFrame` itself, `index ≤ index` reflexively) only has to
    cover the case where the *referencing* frame is itself the last one. The `rid0 ≠ frame.regionId`
    branch transports the ancestor found via `s3` on `cfg` back into `cfg'.stackWithIndex` through the
    shared `dropIdx` prefix (`merge_corollary_stackWithIndex_split`), ruling out the ancestor being the
    differently-regionId'd last frame directly from `heqr`.
  - **New gotchas this session**: (1) an `∃`-bundled goal (`merge_corollary_stack_h1_none`'s `∃ dropIdx,
    eq1 ∧ eq2`) that hides `dropIdx`'s *definition* behind the existential is fine for equality-only
    proofs but useless the moment a later proof needs to case-split `dropIdx`'s own structure (e.g. via
    `List.mem_mapIdx`) — switched to `set dropIdx := ... with dropIdx_def` (keeping the definition visible)
    once `merge_S3` needed to drill into it, at the cost of duplicating the two split equations per call
    site rather than sharing them via the packaged corollary. (2) `omega` intermittently refused simple
    `Nat` contradictions among `.index`/`.length`-projection hypotheses that were visibly sufficient
    (`"No usable constraints found"` despite `a ≤ b`, `b = c`, `c < a` all being literally in context) —
    same flakiness class already documented under `VarAsgn.lean`; worked around with an explicit
    `Nat.not_le.mpr`/`rw` chain instead of trusting `omega`. (3) `unfold RuntimeConfig.stackWithIndex` on
    a hypothesis/goal mentioning the substituted `cfg'` record literal leaves a dangling `.stack`/`.heap`
    projection on that literal that `unfold` alone doesn't reduce — needs a following `dsimp only` before
    any `rw` against a `cfg.stack.mapIdx (...) = ...`-shaped corollary can match syntactically.
  - Otherwise the recurring gotchas already documented under prior files resurfaced unchanged: the
    multi-line record-literal parser error inside a `have`'s type (`set newFrame`/`set dropIdx` fix), `rw
    [h]`/`▸` picking the wrong occurrence or direction when a pattern appears more than once (fixed with
    `subst`, or with fully spelled-out `rw [X] at h` chains instead of one-shot term rewrites), and `cases
    h : e with` silently generalizing a goal's own `∃`-conjunct (fixed with `rfl` in place of the naively
    expected hypothesis in `merge_cases`).
- **`MakeObjStack.lean`** — **fully proved, builds cleanly, zero `sorry`** (finished 2026-07-26, across
  several checkpoints: `H3` first, then `S2`, then `S3`, then the corollaries). All 9 invariants
  (`makeObjStack_L1` … `_S3`, plus `_HS1`) and `makeObjStack_valid` are real proofs. Axiom check confirms
  `makeObjStack_valid` depends only on `propext`/`Classical.choice`/`Quot.sound`.
  - The operation: `makeObjStack x cfg` takes the stack's **last** frame, allocates
    `newObjId := cfg.freshObjectId`, and returns `cfg` with that frame's `varMap` gaining `x ↦ OId
    newObjId` and its `objMap` gaining `newObjId ↦ ∅` (an empty object) — the heap is completely
    untouched, and every other frame is untouched. This makes it structurally simpler than
    `enter`/`exit` (no frame push/pop, no heap mutation) but the first `Preservation` file to introduce
    a genuinely *new* object id, which is what motivated adding `HS1` in the first place (see the
    `Validity.lean` note above).
  - **Only one corollary survived**: the file originally stubbed four skeleton corollaries
    (`makeObjStack_corollary_1` through `_4`, covering general forward `loc?` preservation, a heap-side
    `Rgn` iff, a stack-side `Stk` forward fact, and `RId` equality). All four were proved for real, but
    three of them — the general forward fact and the two it was built from — turned out to have **zero
    callers anywhere in the project**: nothing outside that small cluster needed them, since `H3` only
    ever used the `Rgn`-iff corollary. Rather than keep unused lemmas around, the other three were deleted
    and the survivor renamed down to `makeObjStack_corollary_1` (`∀ oid rid, (OId oid).loc? cfg = some
    (Rgn rid) ↔ (OId oid).loc? cfg' = some (Rgn rid)`, an unconditional iff since the heap is never
    touched by this operation — used by `makeObjStack_H3`).
  - **Why the corollaries as originally planned couldn't fully discharge `S2`/`S3`**: `S2`/`S3`'s
    hypotheses are stated over `cfg'` (e.g. `ref.loc? cfg' = some (Stk fid')`), but invoking
    `vcfg.s2`/`vcfg.s3` needs that same fact restated over `cfg` — i.e. a *backward* (`cfg' → cfg`)
    direction. The originally-planned corollaries are deliberately forward-only for the `Stk` case,
    because the freshly-created object is a genuine counterexample to any unconditional backward fact: it
    resolves to `Stk` in `cfg'` but doesn't exist at all in `cfg`. So `S2`/`S3` each build a *local*,
    self-contained `loc_eq_of_ne_fresh` lemma instead — a full `loc?` equality conditioned on
    `oid ≠ cfg.freshObjectId` — proved by showing the only structural difference between `cfg`/`cfg'`
    (one extra key in the last frame's `objMap`) doesn't change the position-by-position `findRev?` search
    for any *other* `oid`, via a `List.find?_cons_of_pos/neg` case split on whether that `oid` was already
    in the old last frame's `objMap`. `oid ≠ freshObjectId` itself comes from `vcfg.hs1` applied to the
    pre-existing reference (anything already stored resolves to an already-allocated id, which by
    construction can't be the fresh one). A second local lemma, `loc_fresh`, directly computes that the
    fresh object itself resolves to `Stk` at the (unchanged) index of the last frame — used to close the
    "ref is the newly-created one" case of `S2` directly, and to derive an immediate contradiction in `S3`
    (a `Stk` resolution can never match the `Rgn` shape `S3` needs). `S3` additionally needed a
    `transport` lemma: since `vcfg.s3`'s witness frame lives in `cfg.stackWithIndex`, `transport` carries
    it over to the corresponding frame in `cfg'.stackWithIndex` with the same `regionId`/`index` (both
    preserved everywhere by the mutation, dropLast frames literally unchanged and the last frame's
    `regionId` untouched by construction).
  - `makeObjStack_L1`/`_H2`/`_S1`/`_HS1`'s proofs all lean on the same freshness fact, re-derived inline
    each time (not factored into a shared corollary): `cfg.freshObjectId ∉ frame.objMap.keys`,
    proved from `RuntimeConfig.freshObjectId_not_mem cfg` plus membership in `Stack.objectIds`.
  - **Recurring gotcha this session**: writing a raw multi-field record literal (e.g. the new frame's
    `{ regionId := ..., bridgeVar := ..., objMap := ..., varMap := ... }`) directly inside a `have`'s
    *type* — especially split across multiple lines — repeatedly hit a hard parser error ("unexpected
    identifier; expected '}'") that has nothing to do with the math. Fix used throughout: `set newFrame
    : Frame := { ... } with newFrame_def` once, right after the fields it depends on
    (`fresh_not_in_frame` etc.) are established, then refer to `newFrame` everywhere afterward (`set`
    also retroactively abstracts the goal's own occurrences of the literal, which is what makes this
    work instead of just deferring the problem).
  - **New gotcha found while proving `S2`/`S3`**: `rw [List.find?_cons_of_pos/neg h]` fails via
    higher-order-unification ambiguity, essentially the same failure mode as the `find?_cons_of_pos/neg`
    gotcha already documented under `Exit.lean` above — Lean infers the wrong split of predicate/argument
    from `h`'s type alone (e.g. reads `¬ (AList.keys record.objMap).contains oid = true` as `¬ p a` with
    `p := (AList.keys record.objMap).contains` and `a := oid`, rather than the intended
    `FrameWithIndex`-typed predicate applied to `record`). Same fix as before: state the target `find?`
    equality as its own fully-concrete-typed `have`, proved via `exact`/plain term application (not `rw`)
    from `h`, then `rw` with that `have` instead of `h` directly.
  - **Another new gotcha**: after rewriting both branches of a `match h1, h2 with ...` into
    `some recordA`/`some recordB` (two *different* record literals that happen to share the same `.index`
    field), `rw`'s automatic trailing `rfl` (reducible transparency only) isn't enough to see the two
    branches are defeq — an explicit `rfl` tactic (default transparency) is needed as the next step, or
    `cases` on the remaining symbolic scrutinee to force full reduction first.
  - Also recurring: mixing `=` and `~` (`List.Perm`) steps in one `calc` block doesn't parse here (`~`
    isn't in scope as calc-compatible notation for `List.Perm` in this project) — every `List.Perm`
    argument this session was built as a flat sequence of separately-named `have`s (`eq1`/`perm2`/`eq2`
    style, chained with explicit `▸`/`.trans`) rather than a single mixed `calc`.
  - `Stack.objectIds`/`Stack.refs` don't resolve via dot-notation on a plain `List Frame` value (e.g.
    `cfg.stack.dropLast.objectIds` fails with "environment does not contain `List.objectIds`") because
    `List.dropLast`'s return type is bare `List Frame`, not the `Stack` alias — always write these as
    prefix applications, `Stack.objectIds cfg.stack.dropLast`, whenever the receiver came from a `List`
    op like `dropLast`/`++`.
- **`MakeObjRegion.lean`** — **fully proved, builds cleanly, zero `sorry`** (finished 2026-07-25, across
  several checkpoints: `L1`+`L2`, then `S1`+`H1`, then `HS1`, then `H2`, then the shared `loc_eq`
  corollary, then `H3`, then `loc_fresh`, then `S2`, then `S3`). All 9 invariants and `makeObjRegion_valid`
  are real proofs; axiom check on `makeObjRegion_valid` confirms only
  `propext`/`Classical.choice`/`Quot.sound`.
  - The operation: `makeObjRegion x cfg` takes the stack's **last** frame's region (via `cfg.heap.lookup
    frame.regionId`, requiring it to be `Open`), allocates `newObjId := cfg.freshObjectId`, and returns
    `cfg` with that frame's `varMap` gaining `x ↦ OId newObjId` and the **region's** `objMap` (not the
    frame's) gaining `newObjId ↦ ∅`. This is the mirror image of `makeObjStack`: the new object lives in
    the *heap* this time, not the frame. That flip actually makes several invariants *simpler* than
    `makeObjStack`'s: the frame's `objMap` is completely untouched (only `varMap` changes), so the stack
    side of `Reference.loc?` is unconditionally unaffected — no freshness case-split needed there at all.
    The genuine complexity moves to the heap side: `AList.insert` at the *already-present* region key
    (`frame.regionId`) reorders `cfg.heap.entries` (moves that entry to the front via the underlying
    `kinsert`/`kerase`), unlike the object-level insert into the region's `objMap` (a *fresh* key, so
    `AList.entries_insert_of_notMem` applies and nothing reorders).
  - **Three reusable corollaries, each pulled out because ≥2 invariants needed the exact same fact**:
    `makeObjRegion_corollary_objectIds_perm` (`cfg'.objectIds ~ cfg.objectIds ++ [freshObjectId]`; used by
    `L1` and `HS1`), `makeObjRegion_corollary_heap_refs_perm` (`cfg'.heap.refs ~ cfg.heap.refs`, since the
    newly-inserted object is `∅` and contributes no refs; used by `H2` and — via its own local copy, not
    reuse, see below — `HS1`), and `makeObjRegion_corollary_loc_eq` (`∀ oid ≠ freshObjectId, (OId
    oid).loc? cfg = (OId oid).loc? cfg'`; used by `H3`, `S2`, `S3` — the single biggest corollary in the
    file). Also a small non-`ValidConfig`-gated `makeObjRegion_corollary_fresh_not_in_region` (`cfg.heap.
    lookup rid = some region → freshObjectId ∉ region.objMap.keys`, used everywhere a fresh-key insert
    needs to be shown non-reordering) and `makeObjRegion_corollary_region_unique` (an oid appears in at
    most one region's `objMap`, stated over bare `L1` so it's usable before `cfg'`'s own validity is
    established — mirrors `Enter.lean`'s `enter_corollary_1`) and `makeObjRegion_corollary_loc_match_eq`
    (a generic combinator, see gotcha below) and `makeObjRegion_corollary_loc_fresh` (`∃ frame, cfg.stack.
    getLast? = some frame ∧ (OId freshObjectId).loc? cfg' = some (Rgn frame.regionId)` — the fresh object
    always resolves into the heap, at the current top frame's region; used by `S2`, to derive a
    contradiction since a `Stk` hypothesis can never match, and by `S3`, where it *is* the real content).
    `HS1` and `H2` each still carry their own local copy of the heap-refs-permutation derivation rather
    than calling the corollary in `HS1`'s case (written before the corollary existed; not worth the churn
    to retrofit once it was already green).
  - **Why `loc_eq` needs a case split at all on the stack side despite the frame's `objMap` being
    literally unchanged**: `findRev?`'s *result* (an `Option FrameWithIndex`) still differs syntactically
    between `cfg`/`cfg'` when the predicate matches the last frame — the returned record carries the
    differing `varMap` even though only its (unread) `.index` matters downstream. So the proof still
    needs `by_cases hb : frame.objMap.keys.contains oid`, but unlike `makeObjStack`'s version, `hb`'s
    positive-case pairing (`{frame with index:=n}` vs `{newFrame with index:=n}`) needs no freshness
    argument to justify `newFrame`'s predicate value equaling `frame`'s — it's `rfl`, since `newFrame.
    objMap = frame.objMap` by construction, not by an `insert`-then-erase computation.
  - **The heap side of `loc_eq`** reduces the whole `Reference.loc?` match to two `Option.map` facts
    (`(stack findRev?).map index` and `(heap find?).map fst` agreeing between `cfg`/`cfg'`) via a small
    generic combinator, `makeObjRegion_corollary_loc_match_eq : (match o1, o2 with | some f, none => ... |
    none, some ⟨rid,_⟩ => ... | _,_ => none) = (match o1.map index, o2.map fst with ...)`, proved once by
    `cases o1 <;> cases o2 <;> rfl`. The heap `find?` equality itself needs `makeObjRegion_corollary_
    region_unique` (an oid can't be in two regions at once) fed into `List.find?_eq_some_of_unique` to show
    `find?` still lands on the same region despite the `AList.insert`-induced reordering.
  - **New gotcha this session, worse than the already-documented `find?_cons_of_pos/neg` HOU failure**:
    using `makeObjRegion_corollary_loc_match_eq` via `rw` or `simp only` **fails outright** ("did not find
    pattern" / "made no progress") even though the goal's `match` expression is alpha-equivalent to the
    lemma's LHS — because each *occurrence* of `match ... with` syntax compiles to its own distinct
    auxiliary `match_1`/`match_2` definition, and `rw`/`simp` match on that syntactic head, not up to
    defeq. Fix: apply the combinator as a **term**, not a rewrite rule — build `step1 :=
    loc_match_eq (h1 for cfg) (h2 for cfg)`, `step2 := loc_match_eq (h1 for cfg') (h2 for cfg')`, `rw` the
    two `Option.map` equalities *inside* `step1` (safe — those are plain function applications, no `match`
    involved), then close with `step1.trans step2.symm`. `exact`/term application checks by full defeq and
    doesn't care that the two sides' match-auxiliaries have different names.
  - **`makeObjRegion_corollary_loc_fresh`'s own gotcha**: its conclusion mentions `cfg.stack.getLast?`
    literally (needed to name the region the fresh object lands in). Since `cases stackGetLast : cfg.
    stack.getLast? with` generalizes *every* occurrence of that expression in the current goal — not just
    hypotheses — the ∃'s own `cfg.stack.getLast? = some frame` conjunct gets rewritten too, so after
    supplying `frame` as the witness the first component's goal becomes `some frame = some frame` (closed
    by `rfl`), not `cfg.stack.getLast? = some frame` (which the `stackGetLast` hypothesis would have
    proved, and which — confusingly — *type-mismatches* if you try to hand it over instead).
  - Otherwise the recurring gotchas already documented under `MakeObjStack.lean` all resurfaced here
    too, unchanged: the multi-line record-literal parser error inside a `have`'s type (same `set
    newFrame`/`set cfgLit` fix, now needed in four separate proofs since the heap-changing shape means
    more of them embed the post-mutation record), and the `find?_cons_of_pos/neg` HOU failure (same fix —
    state the target `find?` equality as its own concrete `have` via term application first).
- **`MakeRegion.lean`** — **fully proved, builds cleanly, zero `sorry`** (done in a prior session, not
  fully documented here at the time). All 9 invariants (`makeRegion_L1` … `_S3`, `_HS1`, `_HS2`) plus
  `makeRegion_valid` are real proofs; axiom check on `makeRegion_valid` confirms only
  `propext`/`Classical.choice`/`Quot.sound`. The operation allocates *two* fresh ids at once —
  `newRegionId := cfg.freshRegionId` and `newObjectId := cfg.freshObjectId` (the new region's bridge
  object) — inserts `x ↦ RId newRegionId` into the last frame's `varMap`, and inserts a whole new
  `Closed` region (`{bridgeObjectId := newObjectId, objMap := {newObjectId ↦ ∅}, status := Closed}`) at
  the fresh heap key. Unlike `MakeObjStack`/`MakeObjRegion`, the new heap key is genuinely fresh (not an
  existing region being mutated), so the heap-side insert is a straight cons via
  `AList.entries_insert_of_notMem`/`List.kerase_of_notMem_keys` — no `List.exists_of_kerase`/
  region-reordering machinery needed. Has its own local `makeRegion_corollary_loc_match_eq` and
  `makeRegion_corollary_loc_eq` (same shape as `MakeObjRegion.lean`'s, conditioned on
  `oid ≠ cfg.freshObjectId`, since this op — like `MakeObjStack`/`MakeObjRegion` and unlike `VarAsgn`
  below — does allocate a fresh object id).
- **`VarAsgn.lean`** — **fully proved, builds cleanly, zero `sorry`** (finished 2026-07-26, all 10
  invariants in one session going easy-to-hard: `L1`, `HS2`, `S1`, `H1`, `L2`, `H2`, `HS1`, then `H3`,
  `S2`, `S3`). Axiom check on `varAsgn_valid` confirms only `propext`/`Classical.choice`/`Quot.sound`.
  - The operation: `varAsgn x yf cfg` resolves `yf` (a `FieldAccess`) to `yfRef := Reference.OId oid`
    (fails on `RId`) and has two branches on `x == frame.bridgeVar` (`frame` = the stack's **last**
    frame): (1) **bridge-var branch** — requires `yfRef.loc? cfg = some (Rgn rid)` with `rid ==
    frame.regionId`, and reassigns that region's `bridgeObjectId := oid` (`heap := cfg.heap.insert rid
    {region with bridgeObjectId := oid}`; stack untouched); (2) **fresh-var branch** — requires
    `resolveV x cfg == none` (`x` not already bound in *any* frame), and inserts `x ↦ yfRef` into the
    last frame's `varMap` (heap untouched, and — critically — the frame's `objMap` untouched too, only
    `varMap` gains a key). **`varAsgn` never allocates a fresh id** (unlike every other op proved so
    far except `Enter`/`Exit`) — the value it stores/reassigns is always a *pre-existing* reference
    resolved via `resolveFA`/`resolveV`. This is what made the whole file structurally easier than
    `MakeObjStack`/`MakeObjRegion`/`MakeRegion`: no `oid ≠ freshObjectId` case-split anywhere, and the
    reusable `Reference.loc?` transport corollary (`varAsgn_corollary_loc_eq`) is **unconditional** in
    `oid'` for both branches.
  - **Proof scaffold**: `varAsgn_cases` (a case-split lemma proved once via direct `unfold`/`cases`/
    `if_pos`/`if_neg` on the `do`-notation, elaborated form confirmed via `lean_goal` before writing the
    proof) turns `varAsgn x yf cfg = some cfg'` into the two branches above as an explicit disjunction of
    ∃-bundles (frame, oid, and — branch-dependent — rid/region/hridEq/hregion, or the
    `resolveV x cfg = none` fact), used via `obtain`/`rcases` at the top of all 10 invariant proofs and
    `varAsgn_corollary_loc_eq`. Building it hit the same "`cases h : e with` generalizes *every*
    occurrence of `e`, including inside the goal's own ∃-conjuncts" gotcha documented under
    `MakeObjStack.lean`/`MakeObjRegion.lean` (the `resolveFA y cfg = some (Reference.OId oid)` conjunct
    got silently rewritten to `some (Reference.OId oid) = some (Reference.OId oid)` after `cases`-ing on
    that exact term, so the tuple needed `rfl` there, not the `hyf` hypothesis).
  - **`AList.insert` at an existing key reorders `entries`** (bridge-var branch, `cfg.heap.insert rid
    {...}`, mirrors the `MakeObjRegion.lean` heap-reorder situation) — `varAsgn_corollary_bridge_heap_
    objectIds_perm`/`_heap_refs_perm` build the permutation via `List.exists_of_kerase` +
    `NodupKeys.eq_of_mk_mem` exactly as in `MakeObjRegion.lean`, but *simpler*: since only
    `bridgeObjectId` changes (never `objMap`), the mutated entry's own `.objectIds`/`.refs` contribution
    is *literally* unchanged (no freshness-conditioned equality needed), so these are proved once,
    unconditionally, and reused by `L1`, `H2`, `HS1`, `HS2`. `varAsgn_corollary_bridge_heap_keys_mem`
    (heap key *set* unchanged by an existing-key insert, via `AList.mem_insert` +
    `or_iff_right_of_imp`) is the `HS2`/`H2` counterpart for `rid ∈ heap.keys`.
  - **`varAsgn_corollary_fresh_not_in_frame`**: the fresh-var branch's `resolveV x cfg = none`
    precondition implies specifically `x ∉ frame.varMap.keys` for the *last* frame — proved directly
    (not by fully case-splitting `resolveV`'s generic `findRev?`-over-all-frames semantics) by observing
    that if `x` *were* in the last frame's `varMap`, `findRev?` would hit that frame immediately (it's
    the final/innermost element), forcing `resolveV x cfg ≠ none` by contradiction. Used everywhere the
    `varMap` insert needs to be treated as a fresh cons via `List.kerase_of_notMem_keys`.
  - **The hard part was `H3`/`S2`/`S3`, not id-freshness but *provenance*-tracing**: since neither
    branch allocates a new id, `Reference.loc?` transport (`varAsgn_corollary_loc_eq`, built from
    `varAsgn_corollary_bridge_loc_eq` + `varAsgn_corollary_fresh_loc_eq`, the latter needing *no*
    exception at all since the fresh-var branch never touches any `objMap`) was actually **more direct**
    than in `MakeObjStack.lean`/`MakeObjRegion.lean` — no `oid ≠ freshObjectId` case split anywhere.
    `varAsgn_corollary_bridge_loc_eq`'s heap side reuses the same `region_unique` +
    `loc_match_eq`-combinator + `List.find?_eq_some_of_unique` technique as `MakeObjRegion.lean`'s
    `loc_eq` (own local copies of both helper lemmas, per this repo's per-file-self-contained
    convention). The genuinely new difficulty was **`S3`'s fresh-var branch, "newly-inserted-value"
    case**: the value being freshly stored in `newFrame.varMap` (`OId oid`, from `resolveFA`) is a
    *pre-existing* reference, so if it resolves to a heap region `rid'`, `S3` requires some *already
    on-stack* ancestor frame owning `rid'` — but nothing hands you that witness directly, since `oid`
    wasn't previously *in the stack* at all (it could be purely heap-resident, e.g. a sibling field's
    value read off a region object). Resolved by tracing `resolveFA`'s own resolution chain as a new
    corollary, `varAsgn_corollary_yfRef_ancestor` (built on `varAsgn_corollary_resolveV_loc_ancestor` for
    the root-reference sub-case): case-split on whether `yf`'s *root* variable resolved to a `Stk`- or
    `Rgn`-located object — (a) root is `Stk`-located ⟹ the field's container object is `∈` that stack
    frame's `refs`, so `vcfg.s3` applies directly to *that* frame; (b) root is `Rgn`-located ⟹ by `H3`,
    the field *value* (`oid`) resolves into the *same* region as its container (regions don't hold
    external-pointing refs), so it reduces to finding an ancestor for the *root* reference itself, via
    `varAsgn_corollary_resolveV_loc_ancestor`, which further splits on *how* `resolveV` found the root:
    (b-i) as an ordinary `frame.varMap` entry ⟹ `vcfg.s3` applies to that frame directly; (b-ii) as a
    frame's *bridge var* (`frame.bridgeVar == var`, resolving via `Reference.OId <$> region.bridgeObjectId`
    — confirmed via `lean_run_code` to reduce to `some (Reference.OId region.bridgeObjectId)`, i.e. the
    do-block's `Id`-functor `<$>` gets `pure`-lifted, not an `Option`-functor `<$>` as the source syntax
    might suggest) ⟹ `H1` (`region.bridgeObjectId ∈ region.objMap`) plus `oid_loc_rgn_iff_in_heap`
    directly gives that *that* `frame` itself is the region's owner, no `s3` needed. All three leaves
    give a witness with `.index < cfg.stack.length` (via `List.mem_mapIdx` on stack-membership, not via
    `s3`'s own index bound, since `s3`'s witness for the *root* is a *different* frame than the outer
    one `S3` quantifies over) — composed with a local `transport` lemma (same shape as
    `MakeObjStack.lean`/`MakeObjRegion.lean`'s: maps a `cfg.stackWithIndex` member to its
    regionId/index-preserving counterpart in `cfg'.stackWithIndex`) to land the final bound.
  - **Recurring gotcha, worse than usual this session**: chaining `X ▸ h` to rewrite inside a hypothesis
    whose type contains `n + 1` repeatedly failed with *"expected result type of cast is `n.succ`, but
    the equality does not contain the expected result type on either side"* — `▸`'s unifier wants the
    rewrite target to *literally* match up to reducible defeq, and `+ 1` vs `.succ` display forms aren't
    always interchangeable for it. Fix used throughout: replace `X ▸ h` with an explicit `rw [X] at h`
    (or `rw [X] at h ⊢` on the goal) followed by a separate closing tactic (`Nat.le_of_lt_succ h`), never
    a one-shot `▸` term. Plain `omega` also intermittently failed to close goals that were trivially true
    given the visible hypotheses (e.g. `fid' < n + 1 ⊢ fid' ≤ n` with both facts in context, verified via
    `lean_goal`) despite the *same* goal succeeding instantly via `lean_multi_attempt` moments later —
    treated as an omega/LSP-state flakiness rather than a real proof gap; switching to an explicit term
    (`Nat.le_of_lt_succ`) sidestepped it reliably.
  - Also recurring, same fix as documented under `MakeObjStack.lean`/`MakeObjRegion.lean`: `cases h :
    e with` generalizing occurrences of `e` inside a *later* hypothesis (not just the goal) when that
    hypothesis was introduced by an *earlier* `cases`/`obtain` — e.g. `subst`-ing an equation derived
    from `Reference.OId.injEq` after `rcases newFrame_refs_mem _ href with hfreq | horig` silently
    renamed a variable (`oid`) needed later out of scope; fixed by using `rw [hfreq] at ...` on the
    specific hypothesis that needed the substitution instead of a blanket `subst`.
- **`FieldAsgn.lean`** — **fully proved, builds cleanly, zero `sorry`, zero warnings** (finished
  2026-07-26, all 10 invariants in one session going easy-to-hard: `S1`, `H1`, `L2`, `L1`, `HS2`, `H2`,
  `HS1`, then `H3`, `S2`, `S3`). Axiom check on `fieldAsgn_valid` confirms only
  `propext`/`Classical.choice`/`Quot.sound`.
  - The operation: `fieldAsgn xf y cfg` resolves both `xf.root` and `y` via `resolveV` — **both must
    resolve to `Reference.OId _`**, so the value newly written is always an `OId`, never an `RId`. Two
    branches on where `xf.root`'s object lives: (1) **FIELD-ASGN-STACK** — object in the **last** frame;
    replaces `frame.objMap` with `frame.objMap.insert oid (obj.insert xf.field yRef)`, heap/other frames
    untouched; (2) **FIELD-ASGN-REGION** — object in heap region `rid`; requires `yRef` to live in the
    *same* region and `region.status == Open`, replaces `cfg.heap` with an analogous `objMap`-level
    insert, stack entirely untouched. **Never allocates a fresh id** (like `VarAsgn`) — `oid` is always a
    pre-existing key, so every insert in this file replaces a value at an already-present key.
  - **New wrinkle vs. `VarAsgn.lean`**: `VarAsgn` changed only a *scalar* field or a *fresh* key, so its
    transport corollaries got away with literal equality or an unconditional `Perm`. Here the mutation
    replaces the *value* at an *already-present* key one level deeper (`frame`/`region`'s `objMap`, whose
    own `Object` value may itself be inserted at a fresh-or-existing field), so every "key set unchanged"
    argument needs a genuine `AList.insert`-at-existing-key permutation, not just equality. Two small
    generic corollaries carry most of the file: `fieldAsgn_corollary_insert_keys_perm` (any such insert
    permutes `.keys` but never changes the key *set*, via `List.exists_of_kerase` + `List.perm_middle.symm`
    — shorter than the ad-hoc constructions used for the analogous VarAsgn/MakeObjRegion fact) and
    `fieldAsgn_corollary_mem_keys_of_lookup` (a successful `lookup` means the key is already present).
  - `L1` needs the genuine `Perm` above (`fieldAsgn_corollary_region_heap_objectIds_perm`, composing the
    outer heap-entries reorder with the inner region-level permutation). `H2`/`HS2` lean on the fact that
    the newly-written value is always `OId`, so any `RId` count can only decrease-or-preserve — proved at
    the `Object`-field level then propagated up through `ObjMap`-bind, `Frame`/`Region`, `Stack`/`Heap`.
    `H3`/`S2`/`S3` each needed a full `Reference.loc?` transport corollary per branch
    (`fieldAsgn_corollary_stack_loc_eq`/`_region_loc_eq`, mirroring `VarAsgn`'s but needing a new
    `fieldAsgn_corollary_perm_contains_eq` — a `Perm` doesn't change what `.contains` reports — since the
    key *list* now genuinely reorders even though the key *set* doesn't). `S3`'s stack branch reused
    `varAsgn_corollary_resolveV_loc_ancestor` verbatim (renamed `fieldAsgn_corollary_resolveV_loc_ancestor`,
    copied per this repo's per-file convention) and came out simpler than `VarAsgn`'s equivalent since
    `fieldAsgn`'s `y : VarName` resolves directly via `resolveV`, with no `resolveFA` wrapper needed.
  - **New gotchas this session** (beyond the already-documented `find?_cons_of_pos/neg`/record-literal
    ones, which resurfaced here too): `AList.mem_insert.mpr` doesn't resolve as dot notation — needs
    `(AList.mem_insert _).mpr (...)`. `Status` derives `BEq`/`DecidableEq` but not `LawfulBEq`, so
    `beq_iff_eq` fails to synthesize — case-split on `region.status` directly instead. After `rw [hne]`
    turns an `ite` condition into `false = true`, `split_ifs <;> omega` doesn't discharge it — `omega`
    doesn't inspect `Bool`-equality hypotheses for contradictions, so eliminate the always-false branch
    explicitly first via `rw [if_neg (by decide)]`. A `rw [...]` list with the same-shaped lemma appearing
    twice (e.g. two `List.count_append`s) can silently rewrite the wrong occurrence — split into
    separately-named `have`s per side instead. A record literal `{ x with ... }` inside a *standalone*
    `have`'s type elaborates at `x`'s own declared type rather than the context's expected type (e.g.
    `FrameWithIndex` instead of `Frame`) — fix with an explicit ascription, `({ x with ... } : Frame)`.
- **`Swap.lean`** — **fully proved, builds cleanly, zero `sorry`, zero warnings** (finished 2026-07-26,
  in one session across the four sub-cases: `swap_cases` scaffold, then `S1`, `H1`, `L2`, `L1`, `HS2`,
  `HS1`, `H2`, then `H3`, `S2`, `S3`). Axiom check on `swap_valid` confirms only
  `propext`/`Classical.choice`/`Quot.sound`.
  - The operation: `swap x yf cfg` genuinely **exchanges** two live reference values — the value at
    variable `x` in the last frame and the value at field access `yf` — rather than overwriting one
    with a copy, which is what every other `Preservation` file so far actually did. Four sub-cases on
    where `yf` (and, when `x` isn't the bridge var, where `x`'s own value) live: **SWAP-STACK** (both in
    the last frame's own `objMap`/`varMap`), **SWAP-REGION-OBJECT** (`yf` in the frame's own region,
    `x`'s value an `OId` also in that region), **SWAP-REGION-REGION** (same as `-OBJECT` but `x`'s value
    is an `RId`, no location check needed), **SWAP-REGION-BRIDGE** (`x` *is* the bridge var, swapping the
    region's `bridgeObjectId` with a field value). `swap` never allocates a fresh id.
  - **The exchange-ness matters for `H2`**: since a value moves rather than being copied-then-discarded,
    proving `RId`-count preservation needed a genuine equality (not the `≤`-bound every prior file's `H2`
    got away with, since those only ever discarded an old value for a *new* one that was OId-shaped —
    never a two-way trade). `swap_corollary_alist_insert_count_eq` states this additively (`new_count t +
    (if v_old==t then 1 else 0) = old_count t + (if v_new==t then 1 else 0)`) to dodge `Nat` subtraction;
    applying it once per swapped slot and feeding both instances to `omega` makes the two `if`-terms
    cancel algebraically regardless of what the two exchanged values actually are. Composing container
    levels (`ObjMap`→`Region`/`Frame`, `Heap`) needed the same-shaped `swap_corollary_objMap_insert_bind_
    count_eq`/`_heap_insert_bind_count_eq`, each a genuine *identity* for **any** replacement value (no
    relationship between old/new required at that level — the identity is just "other entries' count +
    old's own count = other entries' count + new's own count" restated two ways). Recurring gotcha:
    `omega` treats `X.entries.map (·.2)` (raw) and `Object.refs X` (named) as unrelated opaque atoms
    despite being definitionally equal — needed an explicit `Object.refs`-wrapped restatement of the raw
    lemma's conclusion (via a term-mode type ascription, checked by defeq) wherever it had to combine with
    a lemma stated in the wrapped form.
  - **`H3`/`S2`/`S3`'s `loc?`-transport turned out unconditional for every object id** — sharper than
    every prior file (`MakeObjStack`/`MakeObjRegion`/`MakeRegion` all needed an `oid ≠ freshObjectId`
    exception): `Reference.loc?` never reads `varMap` or `bridgeObjectId`, only `objMap` keys, and `swap`
    never adds or removes an `objMap`/heap key anywhere (every insert replaces a value at an
    already-present key). So one pair of corollaries — `swap_corollary_stack_loc_eq` (frame-side, folds
    the simultaneous `varMap` change into an unused parameter) and `swap_corollary_region_loc_eq`
    (heap-side, folds `bridgeObjectId` changes into a generic `newRegion` parameter) — covers all four
    branches, composed via `.trans` for the two branches that touch both stack and heap (a third small
    corollary, `swap_corollary_stack_varmap_loc_eq`, handles a *pure* `varMap`-only change with no `Perm`
    argument at all, since the key set there is literally unchanged, not just `Perm`-equal).
  - **`S3` turned out simpler than `VarAsgn`/`FieldAsgn`'s**, which both needed genuine `resolveV`/
    `resolveFA` provenance-tracing corollaries to find an ancestor frame for a newly-written value.
    `swap`'s region-touching branches require the touched region to be the *current* frame's own region
    (`hrid : rid = frame.regionId` is part of the operation's own precondition), so any region-internal
    ref newly placed into scope already has `frame` itself as a valid ancestor witness — fixed via `H3`
    (the swapped-in value was already in `region.refs`) plus a trivial `le_refl` bound, no provenance
    chain needed. `SWAP-STACK`'s same-frame exchange means *every* ref in the mutated frame (old or
    newly-swapped-in) was already in `frame.refs` before the mutation, so plain self-reference against
    `vcfg.s3` always suffices there too; a small `transport` lemma then carries the resulting ancestor
    witness from `cfg.stackWithIndex` over to `cfg'.stackWithIndex` (regionId/index preserved, dropLast
    frames literally unchanged).
  - Recurring gotchas from prior files resurfaced: the multi-line record-literal parser error inside a
    `have`'s type (`set newFrame`/`set newRegion` fix), and `cases h : e with` silently generalizing a
    goal's own `∃`-conjunct when its LHS syntactically matches `e` independent of the existential witness
    (fixed with `rfl` in place of the naively-expected hypothesis at three sites in `swap_cases`).

### `Gc/Reachability/Referencable/Validity/` — CR3 preservation (mirrors the `Gc/Model/Preservation/` pattern above)

`Validity/Reachable.lean` defines the third reachability invariant:

```
def CR3 (cfg : RuntimeConfig) : Prop :=
  ∀ frame ∈ cfg.stackWithIndex, ∀ frame' ∈ cfg.stackWithIndex,
    frame.index < frame'.index →
    ∀ oid, (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) →
    FrameReachable cfg frame'.index (Reference.OId oid) →
    FrameReachable cfg frame.index (Reference.OId oid)
```

("if an object lives in a suspended region owned by an earlier frame F, and is frame-reachable from
some later frame F', it's already frame-reachable from F itself" — report.pdf CR3). Unlike L1–HS2, CR3
isn't provable from a `ValidConfig` snapshot alone (nothing in the 9 invariants says anything about
*how* a reference came to exist) — it's a fact about the operational semantics, so it's proved to hold
at `RuntimeConfig.start` (`Validity/Start.lean`) and preserved by every `Mutation.lean` operation
(`Validity/Preservation/*.lean`), exactly mirroring `Gc/Model/Preservation/*.lean`'s per-operation
pattern. `ValidReachableConfig cfg extends ValidConfig cfg` with a `cr3` field.

Per-operation status (8 of 9 operations done; `Swap.lean` is the one remaining `sorry` — see "Next
planned step" below):

- **`Enter.lean`/`Exit.lean`/`MakeObjStack.lean`/`MakeObjRegion.lean`/`MakeRegion.lean`/`Merge.lean`**
  — **all fully proved, zero `sorry`** (done across earlier sessions, before this file had a "Current
  known state" entry for the `Reachability/` layer at all — retroactively documented here from reading
  the finished proofs). All six follow the same skeleton: an `objAt_eq`/`refStep_iff` corollary showing
  `RefStep` is either fully unconditional or conditional only on "not the freshly-allocated id" (these
  five operations are additive — `Enter` pushes an empty frame, `MakeObjStack`/`MakeObjRegion`/
  `MakeRegion` allocate a fresh, isolated (empty) object — so newly-added content can never itself be a
  `RefStep` *source*); a `frameRoot_down`/`_iff` corollary transporting `FrameRoot` witnesses cfg'→cfg
  (unconditional for non-fresh values, since a fresh-var/fresh-region slot can never supply an
  already-existing `OId`/`RId` shape); and a main `<op>_cr3` proof that case-splits on whether the
  CR3-quantified `frame'` sits at the newly-added/mutated stack position or an old one, applying
  `vrcfg.cr3` in the "old position" branch and a direct argument in the "new position" branch (the
  fresh/entered content trivially can't already be region-resident in a way CR3 cares about). `Merge.lean`
  is the exception worth its own note: since merge *relocates* existing objects rather than adding a
  fresh one, its `objAt_eq`/`refStep_iff` corollaries (`merge_corollary_objAt_eq`/`_refStep_iff`) are
  **fully unconditional for every reference** (nothing is created, destroyed, or content-edited, only
  regrouped between heap keys) — the *simplest* of the six in this respect, despite `Merge.lean` being
  the hardest file in `Gc/Model/Preservation/` for the L1–HS2 invariants.
- **`FieldAsgn.lean`** — **fully proved, zero `sorry`** (finished 2026-07-28). The first CR3 proof where
  the mutated object's *own content* genuinely changes (a field write can add a brand-new edge, or
  silently overwrite an existing one) rather than the mutation being purely additive — so the "mutated
  object never lies on the relevant chain" argument the other six files lean on (fresh/isolated content,
  never a valid `RefStep` source) doesn't apply here at all, and this file took a full session.
  - **Key insight** (from the project's own author, sketched informally before any Lean was written): if
    a post-mutation reachability chain uses the newly-written field's edge, the value written there
    (`yRef`, from `resolveV`/`resolveFA`) was *already* resolvable pre-mutation, so it already has its
    own natural root `frameY`. By the same S2/S3 "no reference from an earlier frame into a later
    frame/region" argument CR2 already uses, `frame.index ≤ frameY.index` (`frame` being the suspended
    region's owner) — the pre-existing path *can't* have come from strictly later than `frame`, since
    `frame` itself already S1-uniquely owns the target region. The case split is then `frameY = frame`
    (trivial) or `frame.index < frameY.index` (recurse into `vrcfg.cr3` itself, using `frameY` as the
    "later frame" this time).
  - **New reusable facts added to `Corollaries/Common.lean`** (at the time still the single
    `Corollaries.lean`, later split — see its bullet above) to make this precise:
    `ReflTransGen_rgn_confined`, `ReflTransGen_upper_bound`, `FrameReachable_owner_index_le`,
    `FrameReachable_stk_index_le`. In the end only the latter two (the packaged wrappers, not the raw
    `ReflTransGen`-level ones) were needed by the final proof — `ReflTransGen_rgn_confined` was built
    first while exploring a more complicated "confinement" approach that turned out unnecessary once the
    owner's own S1+S3 argument (above) was worked out directly, but is left in as a genuinely reusable,
    independently-true fact (not yet needed elsewhere).
  - **Proof shape**: `fieldAsgn_corollary_stack_objAt_eq_of_ne`/`_region_objAt_eq_of_ne` (`objAt?`
    equality for any oid *other than* the mutated container, built on top of the already-unconditional
    `fieldAsgn_corollary_stack_loc_eq`/`_region_loc_eq` from `Gc.Model.Preservation.FieldAsgn`) plus
    `_stack_objAt_mutated`/`_region_objAt_mutated` (the mutated container's own exact new content). The
    main `fieldAsgn_cr3` proof structures the "down" transport as `main_claim`, an induction via
    `Relation.ReflTransGen.head_induction_on` (walking forward from the chain's start, target fixed at
    CR3's own `oid`) whose invariant is "the remaining suffix is *already* a valid cfg-chain, OR the
    overall goal is already established" — at each hop, `by_cases` on whether the hop's source is
    exactly the mutated container *and* its target is exactly the newly-written value; if so, invoke the
    escape (`FrameReachable_owner_index_le` + case split, described above); otherwise the hop transports
    down unconditionally (via the objAt-ne corollaries, plus `fieldAsgn_corollary_object_insert_refs_mem`
    from the Model layer to show a *retained* old field edge, when the target isn't the newly-written
    value specifically). The "up" transport (after invoking `vrcfg.cr3`) is comparatively easy: the
    suspended `frame` is *never* the mutated frame (`frame.index < frame'.index ≤` the mutated frame's
    own index, since the mutated frame is always the stack's *last* one), so its own root set and every
    `RefStep` hop reachable from it are provably untouched by the mutation, via the same bound applied to
    rule out the mutated object ever appearing on *this* chain specifically.
  - Axiom check on `fieldAsgn_cr3`/`fieldAsgn_reachable_valid` confirms only
    `propext`/`Classical.choice`/`Quot.sound`.
- **`VarAsgn.lean`** — **fully proved, zero `sorry`** (finished 2026-07-28, immediately after
  `FieldAsgn.lean` and considerably faster once the escape technique above already existed).
  Substantially simpler than `FieldAsgn.lean`: `varAsgn` never touches any `objMap` at all (only
  `varMap`, or a region's `bridgeObjectId` scalar field), so `varAsgn_corollary_objAt_eq` is fully
  **unconditional for every reference** (built directly on top of the already-unconditional
  `varAsgn_corollary_loc_eq` from the Model layer, plus new `varAsgn_corollary_stack_shape_eq`/
  `_heap_objMap_eq` showing the relevant `objMap` component is untouched at every position/key) —
  meaning `RefStep cfg = RefStep cfg'` pointwise, and no per-hop induction is needed *at all* (unlike
  `FieldAsgn.lean`'s `main_claim`). The only thing that can differ between cfg/cfg' is the *root set*
  itself: the bridge branch replaces one region's `bridgeObjectId`, the fresh-var branch adds one new
  `varMap` key — and in both branches, that one new/changed root value is always exactly `resolveFA
  y cfg`'s result (a pre-existing reference). New helper `varAsgn_corollary_resolveFA_frameReach`
  (`resolveFA y cfg = some (OId oid) → ∃ frameY, FrameReachable cfg frameY.index (OId oid)`, composing a
  `varAsgn_corollary_resolveV_frameRoot`-style root fact for `y.root` with one more `RefStep` hop for the
  field access itself) plays the analogous role to `FieldAsgn.lean`'s escape setup. The proof structure:
  build `hconcDown : FrameReachable cfg frameD.index oid` directly via an outer `rcases` on
  `varAsgn_cases`'s two branches, each further `rcases`-ing `FrameRoot`'s two disjuncts and `by_cases`-ing
  whether the specific witness frame/value is the mutated one; the `escape` closure (identical in shape
  to `FieldAsgn.lean`'s) handles that case, ordinary `FrameRoot` transport handles the rest. The final
  "up" transport is the same "the suspended `frame` is never the mutated frame" argument as
  `FieldAsgn.lean`.
  - Axiom check on `varAsgn_cr3`/`varAsgn_reachable_valid` confirms only
    `propext`/`Classical.choice`/`Quot.sound`.
- **`Swap.lean`** — **fully proved, zero `sorry`** (finished 2026-07-28, same session as
  `FieldAsgn`/`VarAsgn` above). This was the last remaining `sorry` anywhere in `Gc/` — its completion
  means every operation in both `Gc/Model/Preservation/` and `Gc/Reachability/Referencable/Validity/Preservation/`
  is now fully proved. `swap_cr3` had to combine **both** prior techniques at once: `fieldAsgn_cr3`'s
  per-hop `main_claim` induction (swap genuinely mutates a container's own field content, unlike
  `varAsgn`) *and* `varAsgn_cr3`'s root-escape technique (swap also writes a pre-existing value into a
  var/bridge root, unlike `fieldAsgn`) — necessary because `swap` is a true two-way exchange, not a
  one-directional overwrite.
  - **Mid-chain escape turned out simpler than expected**: for SWAP-STACK/SWAP-REGION-OBJECT/
    SWAP-REGION-REGION, the value newly written into the mutated container's field is always `x`'s own
    *old* var value — already a trivial `FrameRoot` witness via `Or.inl ⟨frame0, hframe0_mem, rfl, x,
    hxr⟩`, no `resolveV`/`resolveFA`-chain tracing needed at all (unlike `fieldAsgn`'s escape, which had
    to trace an arbitrary `y : VarName`'s resolution). SWAP-REGION-BRIDGE's mid-chain escape is the same
    shape, using the bridge disjunct (`region.bridgeObjectId`, since `yrid = frame0.regionId` is part of
    the operation's own precondition) instead of a var. For SWAP-REGION-REGION specifically, the
    mid-chain escape *never fires at all*: the written value there is `Reference.RId xrid`, which can
    never match a chain element (`RefStep`'s target must already be shown `OId`-shaped whenever the
    chain continues or ends at CR3's `OId oid`), so that case closes by a direct constructor-mismatch
    contradiction.
  - **Root escape is exactly `varAsgn`'s `resolveFA`-composed technique, reused verbatim** (copied as
    `swap_corollary_resolveFA_frameReach`, since `yf : FieldAccess` here is exactly like `varAsgn`'s
    `y`), needed uniformly across all four branches for "the var/bridge slot that gets `yfRef` written
    into it might itself be the whole chain's root."
  - **The genuinely new complication**: SWAP-REGION-OBJECT/SWAP-REGION-REGION change the stack (`x`'s
    var) *and* the heap (the region's field) **simultaneously**, and no single `Gc.Model.Preservation.
    Swap` corollary covers a combined mutation — each of `swap_corollary_region_loc_eq` and
    `swap_corollary_stack_varmap_loc_eq` only ever changes one side. Composing them naively via `rw
    [← hcfg']` fails outright (the two single-mutation corollaries' own stated configs don't
    syntactically match `cfg'`, which has *both* fields changed at once) — resolved by introducing
    `swap_corollary_region_stack_loc_eq`/`_objAt_eq_of_ne`/`_objAt_mutated`, each explicitly composing
    the heap-side and stack-side single-mutation facts via `.trans` against an intermediate
    `{ cfg with heap := ... }` config, then closing the real goal (`... = cfg'`) via `rw [hcfg']; exact
    ⟨composed proof⟩` (term-mode `exact`, which checks by defeq, rather than a syntactic `rw`).
    SWAP-REGION-BRIDGE has an analogous problem one level down — the mutated region's own
    `bridgeObjectId` *and* `objMap` both change together, and `swap_corollary_region_objAt_mutated`/
    `_objAt_eq_of_ne` (as reused unchanged from SWAP-REGION-OBJECT) hardcode `bridgeObjectId` unchanged
    — fixed by writing bridge-aware siblings (`swap_corollary_region_bridge_objAt_mutated`/
    `_objAt_eq_of_ne`) that fold `newBridge` directly into the composed `newRegion` literal from the
    start (no separate "bridge-only" transport step needed, since the underlying `Gc.Model.Preservation.
    Swap.swap_corollary_region_loc_eq` never reads `bridgeObjectId` regardless of what the caller passes
    for it).
  - **SWAP-REGION-BRIDGE's root/bridge-disjunct case split** (down *and* up directions) mirrors
    `varAsgn_cr3`'s own BRIDGE-branch handling almost exactly: `by_cases` on whether a candidate frame's
    `regionId` equals the touched region's id, using `merge_corollary_regionId_unique_index` (S1
    uniqueness) to collapse that case to "the frame IS `frame0`" in the DOWN direction (where it's a real
    possibility) or to a direct contradiction in the UP direction (where the suspended frame's index is
    already known `< frame0.index`, so it can never coincide with `frame0`).
  - **Recurring gotcha, worse than usual this session**: composing two implicit-argument-heavy corollary
    calls via `hframe0' : (...) .stackWithIndex.getLast? = some frame0 := hframe0` (a bare `have` binding
    with no tactic block, relying on defeq to accept `hframe0` unchanged for a differently-*written* but
    defeq-equal intermediate config) works fine, but supplying an explicit `newFrame`/`newRegion` as an
    **implicit** argument (letting Lean infer it from a `rfl`/`hcfg'`-shaped proof term) repeatedly
    mis-unified to a trivial/wrong value instead of the intended literal — same failure class as
    `MakeObjStack.lean`'s original gotcha, but here it silently produced a *type-mismatch* several lines
    later rather than an immediate error, making it harder to localize. Fix used throughout: make the
    replacement record (`newFrame`/`newRegion`/`newVal`/`field`/`newBridge`) an **explicit** argument (or
    pass it via named `(newVal := ...)`/`(field := ...)` at every call site) rather than relying on
    unification to recover it from a hypothesis. Also recurring: the multi-line record-literal parser
    error inside a `have`'s/theorem's type (same fix as every prior file — collapse the literal onto one
    line with an explicit `: Region`/`: RuntimeConfig` ascription).
  - Axiom check on `swap_cr3`/`swap_reachable_valid` confirms only `propext`/`Classical.choice`/
    `Quot.sound`. Full `lake build` (1058 jobs) and a project-wide sorry scan (0 sorries across 42
    files) both confirm `Gc/` is now completely `sorry`-free.

### `Gc/Reachability/Referencable/Validity/CR5.lean` — CR5 single-step (added 2026-07-29, restructured same day)

report.pdf CR5: "Activity in an active region and frame cannot affect the stack-reachability of
objects within suspended regions." Unlike CR1/CR2/CR4 (`Corollaries/{CR1,CR2,CR4}.lean`) and CR3 (a
`ValidConfig`-style invariant about one config), CR5 is fundamentally a claim about *change across a
transition* — so, mirroring how CR3 itself is proved, it's formalized as a per-operation single-step
fact first:

```
def Suspended (cfg : RuntimeConfig) (i : Index) : Prop :=
  ∃ frame ∈ cfg.stackWithIndex, frame.index = i ∧ i < cfg.stackWithIndex.length - 1

def CR5_helper_step (cmd : Stmt) : Prop :=
  ∀ cfg cfg' : RuntimeConfig, ValidReachableConfig cfg → step cmd cfg = some cfg' →
    ∀ i, Suspended cfg i → ∀ ref, FrameReachable cfg i ref ↔ FrameReachable cfg' i ref

def CR5_step (cmd : Stmt) : Prop :=
  ∀ cfg cfg' : RuntimeConfig, ValidReachableConfig cfg → step cmd cfg = some cfg' →
    ∀ i, Suspended cfg i → ∀ ref, FrameReachable cfg i ref →
    (StackReachable cfg ref ↔ StackReachable cfg' ref)
```

(`Stmt`/`step` come from `Gc/Model/Mutation/Stmt.lean` — see the Architecture section above.)
`enter`/`exit` need no special-casing despite changing *which* frame counts as active: `Suspended` is
evaluated pre-step, so `CR5_helper_step` only ever claims something about frames *already* suspended
before the operation runs, and no operation ever touches an already-suspended frame's own stack slot or
region (only the active/last frame's own).

**Restructured 2026-07-29 (commit `971c61c`), the same session `CR5_step` was first completed for all 9
operations.** Originally the easier-to-prove `FrameReachable` form above (per-operation, mirroring
`Validity/Preservation/*.lean`'s CR3 pattern) was itself named `CR5_step`, and a separate
`StackReachable`-flavored `CR5'_step` (the actual report.pdf-faithful statement) was explored, dropped
mid-session to keep scope contained, then picked back up and finished. Once `CR5'_step` worked for all 9
operations it took over the name `CR5_step` (matching report.pdf's own numbering — the same motivation
as the `Corollaries/` bare-CR-name rename above); the old `FrameReachable`-form `CR5_step` was demoted
to `CR5_helper_step`. `CR5_step` above is deliberately *restricted* to references already
`FrameReachable` from the suspended frame — an *unrestricted* `∀ ref, StackReachable cfg ref ↔
StackReachable cfg' ref` is false (e.g. `makeObjStack` can make a brand-new object `StackReachable` in
`cfg'` via the active frame's own fresh var, without it ever having been reachable, from anywhere, in
`cfg`; that has nothing to do with any suspended region). `cr5_step_of_helper : CR5_helper_step cmd →
CR5_step cmd` does the upgrade: once `ref` is already `FrameReachable` from the suspended frame,
`StackReachable cfg ref` is trivially witnessed by that same frame, and `StackReachable cfg' ref` falls
out of the helper's `FrameReachable cfg' i ref` fact by unfolding `FrameRoot` for a witness frame — no
`CR4`/`RegionReachable` machinery needed at all. Rather than keep the 9 per-operation `CR5_helper_step`
proofs separately named, each of `cr5_step_enter` .. `cr5_step_varAsgn` now proves the helper fact
internally (unnamed, via `apply cr5_step_of_helper` as its first line) and its own public signature is
`CR5_step` directly — the per-op techniques described below are otherwise unchanged from when they were
named `cr5_step_*` under the old `CR5_step` meaning. The deferred multi-step sketch (see "Not yet done"
below) was removed at the same time since it targeted the now-renamed helper form and needs
re-deriving, not patching, against the new shape.

**`CR5_step` is fully proved for all 9 operations, zero `sorry`** (`cr5_step_enter` … `cr5_step_swap`,
dispatched by `cr5_step_all`). Difficulty roughly tracked what was anticipated going in (easiest to
hardest: `enter`/`exit` ≈ trivial reuse; `varAsgn`/`makeObjStack`/`makeObjRegion`/`makeRegion`/`merge`
≈ easy-to-medium; `fieldAsgn` ≈ medium; `swap` ≈ hardest), and turned out **simpler than the
corresponding `<op>_cr3` proof in every case**: since the helper fact is only ever asked about an
*already-suspended* frame, the "does a chain reach the mutated container" question that `<op>_cr3`
needs an escape/induction argument for is instead **provably impossible** here (any object reachable
from a suspended frame has owner-index strictly below the active/mutated frame's, via
`FrameReachable_owner_index_le`/`_stk_index_le` from `Corollaries/Common.lean`) — so every proof reduces
to a plain position-based frame/heap-transport argument plus a straightforward (escape-free)
tail-induction on the `RefStep` chain in each direction.

- **`enter`/`exit`** — direct reuse of `enter_corollary_frameReachable_iff`/
  `exit_corollary_frameReachable_iff` (already proved, unconditionally for `enter`/for any surviving
  frame for `exit`, as part of `<op>_cr3`'s own scaffolding) — both were `private`, made public. No new
  proof content.
- **`makeObjStack`/`makeObjRegion`/`makeRegion`** — each got a new public
  `<op>_corollary_frameReachable_iff_of_lt` theorem in its own `Validity/Preservation/<Op>.lean`,
  generalizing the frame-transport/`FrameRoot`-iff argument `<op>_cr3` already built *inline* for
  itself (`frame_transport_down`/`_up`, an unnamed `frameRoot_iff_nonlast`-shaped block) into a
  standalone, reusable "`FrameReachable` unaffected at any position strictly before the mutated
  (active) one" fact.
- **`merge`** — same shape (`merge_corollary_frameReachable_iff_of_lt`), and needs only
  `ValidConfig cfg` (no `cfg'`-side validity), matching `merge_corollary_refStep_iff`'s own
  unconditional-in-`cfg'` shape. Turned out to be the *easiest* of the "real activity" operations
  despite `Merge.lean` being the hardest file in the project for `L1`–`HS2`: its `objAt_eq`/`refStep_
  iff` are already fully unconditional for every reference (nothing content-edited, only regrouped
  between heap keys).
- **`fieldAsgn`** — new `fieldAsgn_corollary_frameReachable_iff_of_lt`. Reuses
  `fieldAsgn_corollary_frameRoot_iff` directly (already fully unconditional for *every* `fid`, not
  just non-last ones, since `fieldAsgn` never touches `varMap`/`bridgeObjectId` at all — a stronger
  fact than CR3 needed). The only new work: an owner-index-bound argument (`hoidm_ne`/`hoidm_ne'`,
  established separately for `cfg` and `cfg'` via the model layer's unconditional `loc?`-preservation
  facts) ruling out the mutated container ever appearing in a suspended-rooted chain, then a plain
  `induction ... with | refl | tail` transport in each direction — no
  `Relation.ReflTransGen.head_induction_on`/escape-branch machinery like `fieldAsgn_cr3`'s own
  `main_claim` needed.
- **`swap`** — new `swap_corollary_frameReachable_iff_of_lt`, one case per branch (SWAP-STACK/
  -REGION-OBJECT/-REGION-REGION/-REGION-BRIDGE), each following the same fieldAsgn-style shape (owner-
  bound + escape-free tail-induction), reusing `swap_corollary_frame_transport_down`/`_up`,
  `swap_corollary_region_stack_loc_eq`/`_objAt_eq_of_ne` (the two branches touching stack and heap
  simultaneously), `swap_corollary_region_loc_eq`/`_objAt_eq_of_ne` (the bridge branch, heap-only), and
  `merge_corollary_regionId_unique_index` (S1-based `regionId ≠` argument, reused for all three
  heap-touching branches). Neither `swap_corollary_escape` nor `swap_corollary_root_escape`
  (`swap_cr3`'s own mid-chain/root escape machinery) was needed, confirming the "escape is impossible
  from a suspended root" expectation held even for swap's four-branch case.
- **Recurring gotcha this session**: `subst heq` (from `intro oidx hreachx heq; subst heq` where
  `heq : oidx = <outer-scope id>`) intermittently eliminated the *outer* identifier instead of the
  freshly-`intro`'d `oidx`, silently renaming it out of scope for later code that still referenced it
  by its old name (`Unknown identifier` several lines later, not at the `subst` site itself) — same
  failure class as documented under `Exit.lean`/`Swap.lean` above, worked around the same way
  (`rw [heq] at hreachx` instead of `subst heq`).
- Axiom check on `cr5_step_swap`/`cr5_step_all` confirms only `propext`/`Classical.choice`/
  `Quot.sound`. Full project `lake build` (1060 jobs) clean throughout.

**`Suspended` was refactored (2026-07-29, earlier the same session as the CR5'→CR5 rename above)** to
drop an "active frame" existential witness it originally carried (`∃ active, cfg.stackWithIndex.getLast?
= some active ∧ i < active.index`) in favor of stating the bound directly (`i <
cfg.stackWithIndex.length - 1`) — the two are equivalent, but the direct form is exactly what every
per-operation corollary above is stated in terms of, so the indirect form forced `exit`/`varAsgn` in
particular to do a `getLast?`/`injection`/`subst` dance just to extract a fact the hypothesis could hand
over for free. Net −35 lines across the 9 proofs; no proof obligations changed (verified via full
rebuild + axiom check on `cr5_step_all`).

**Not yet done**: multi-step CR5 (chaining `cr5_step_all` over an arbitrary-length `List Stmt` trace,
the actual report.pdf claim rather than just one operation) — not currently being pursued; deprioritized
per user direction 2026-07-29. A sketch existed against the old (pre-rename) `CR5_step` shape but was
deleted as part of the CR5'→CR5 rename above; would need re-deriving against the current shape if picked
back up.

Elsewhere:

- **`Gc/Model/Validity.lean`** — **fully proved, builds cleanly, zero `sorry`** (as of 2026-07-24). Its
  last two gaps, `oid_loc_rgn_iff_in_heap` (the `find?`-minimality sub-goal: an earlier heap entry can't
  also contain `oid`) and the full `oid_loc_stk_iff_in_stack` theorem, are both closed. Both use the same
  core technique: `L1` (`cfg.objectIds.Nodup`) split via `List.nodup_append` into the stack/heap parts,
  then `List.nodup_flatten` + `List.pairwise_map` turns the relevant part's nodup into a
  `List.Pairwise Disjoint` fact over per-region/per-frame `objectIds` lists, and
  `List.Pairwise.rel_get_of_lt` extracts pairwise disjointness at two explicit indices to contradict
  `oid` appearing in both. `oid_loc_stk_iff_in_stack`'s backward direction additionally needed
  `List.find?_eq_some_of_unique` (see below) to build the `findRev?` witness from global oid-uniqueness,
  and reuses the already-proved `oid_in_stack_implies_not_in_heap` to rule out the heap side rather than
  re-deriving stack/heap disjointness by hand. Axiom check confirms only
  `propext`/`Classical.choice`/`Quot.sound`. As part of this, `List.find?_eq_some_of_unique` — fully
  generic, no domain dependency — was moved from `Preservation/Exit.lean` into `Theorems.lean` (which
  `Validity.lean` now also imports) so both files can use it without an import cycle; `Exit.lean`'s own
  proofs were unaffected (same qualified name, still builds clean).
- `Gc/Reachability/Referencable/Guarantees.lean` is empty; `Gc/Reachability/Referencable/Invariants.lean` has no proofs yet — this
  layer is much earlier-stage than `Gc/Model/`.

### `Gc/Reachability/Reachable/` per-operation status (`stackReachable_invariant_<op>` in `Scratch.lean`)

Per-operation status of `StackReachable_invariant_for_suspended_region_objects`, proved one `Stmt` at a
time, easiest-to-hardest, each checkpointed as its own commit (`draft(lean4): ...` for `Lemmas.lean`
groundwork, `prove(lean4): stackReachable_invariant_<op>, zero sorry` once the main theorem closes):

- **`enter`/`exit`** — **fully proved, zero `sorry`** (both axiom-checked to only depend on
  `propext`/`Classical.choice`/`Quot.sound`). Both follow the same shape: forward direction transports
  any pre-existing witness frame up unchanged; backward direction splits on whether the `cfg'`-side
  witness frame is a survivor (transports down unchanged) or the newly-pushed/about-to-be-popped frame,
  closed via a `SafeRef`-based backward chase (`safe_reflTransGen_transport`/`_root_safe` in
  `Lemmas.lean`) showing any chain reaching such a frame's root must already have passed back through
  `frame`'s own region — i.e. the "unsafe" root case is vacuous once `hloc` pins `oid`'s location.
- **`makeObjStack`** — **fully proved, zero `sorry`** (finished 2026-07-31; axiom-checked). Structurally
  simpler than `enter`/`exit` in one key respect: `makeObjStack_step_eq` shows `ReachableStep cfg =
  ReachableStep cfg'` as a **literal function equality**, not just an iff — the heap is never touched at
  all, so only the *root set* (not the step relation) can differ between `cfg`/`cfg'`. The one new root
  the mutation can introduce is `x ↦ OId cfg.freshObjectId`; ruling this out as a viable path to `oid`
  needed two new general lemmas — `freshObjectId_loc_none`/`_ne_rgn` (a fresh id resolves to no
  location at all, so in particular never to `Rgn frame.regionId`, contradicting `hloc` if `oid` were
  ever forced to equal it) and `stackWithIndex_getLast_mem` (reifies `cfg.stack.getLast?` as a genuine
  `FrameWithIndex` member of `cfg.stackWithIndex`, needed to hand `lastFrame` itself to `hcr3` as the
  "later frame" witness in the backward direction's mutated-last-frame case). The var-root case
  (`var = x`) closes by deriving `oid = cfg.freshObjectId` from a zero-or-one-step `ReflTransGen` case
  split (`Relation.ReflTransGen.cases_head`) and contradicting it against `hloc`/`freshObjectId_loc_ne_rgn`;
  every other case reduces to `hcr3` applied to `lastFrame` (reindexed via `stackWithIndex_getLast_mem`)
  exactly as in `enter`/`exit`.
- **`makeObjRegion`/`makeRegion`** — **fully proved, zero `sorry`** (finished 2026-07-31, same session as
  `varAsgn`/`fieldAsgn` below). Close cousins of `makeObjStack` as expected: same fresh-id-root argument,
  just relocated to the heap side (`makeObjRegion`, mutating the active frame's own region's `objMap`) or
  to a brand-new region (`makeRegion`, which also allocates a fresh `RegionId`). Each got its own
  `<op>_objAt_eq_of_ne`/`_fresh_objAt_cfg'`/`_oid_step_iff`/`_rid_step_iff`/`_step_eq` cluster (the
  `_step_eq` showing `ReachableStep cfg = ReachableStep cfg'` pointwise, exactly as `makeObjStack`'s did)
  plus a `<op>_frame_cases`/`_frame_mem_up`/`_regionId_ne`/`_frame_reachable_iff` cluster re-deriving the
  frame-membership/index-transport facts fresh (no import from `Referencable/`). `makeRegion` additionally
  needed `freshRegionId_no_step` (a fresh `RegionId` can never be the source of a real `ReachableStep`,
  since nothing points at an unallocated region yet) and its own `makeRegion_corollary_loc_fresh`.
- **`varAsgn`** — **fully proved, zero `sorry`** (finished 2026-07-31, same session). Two new reusable
  lemmas that turned out to be the crux of everything downstream: `resolveV_frameRoot` (`resolveV var cfg
  = some (OId oid) → ∃ frameY ∈ cfg.stackWithIndex, FrameRoot cfg frameY.index (OId oid)` — i.e. any
  variable's resolved value already has an independent root) and `resolveFA_frameReach` (the one-more-hop
  version for a field access). `varAsgn_objAt_eq`/`_rid_step_iff`/`_step_eq` show the step relation is
  again pointwise-equal between `cfg`/`cfg'` (varAsgn never touches any `objMap`, only `varMap`/a region's
  `bridgeObjectId` scalar), so — like `makeObjStack` — the only thing that can differ is the *root set*,
  handled via `varAsgn_frame_mem_iff`/`_regionId_ne`/`_frame_reachable_iff`/`_freshvar_last_mem`. Also
  needed `RegionReachable_oid_confined`/`region_reachable_open_ne_absurd` (a fresh H3-driven confinement
  argument, re-derived independently rather than reusing `Referencable/`'s `RegionReachable_stays_in_region`).
- **`fieldAsgn`** — **fully proved, zero `sorry`** (finished 2026-07-31, same session, the hardest of the
  four and the last one attempted before checkpointing). Unlike `varAsgn`, `fieldAsgn` genuinely mutates a
  container object's own field content, so `ReachableStep cfg ≠ ReachableStep cfg'` pointwise — the step
  relation only agrees for sources *other than* the mutated container
  (`fieldAsgn_step_iff_of_ne`, returning the container's own id `oidC` existentially since callers need it
  anyway). The proof combines two techniques: an **owner-index-bound confinement** argument
  (`fieldAsgn_stack_container_confined`/`_region_container_confined`, built on new general lemmas
  `stack_step_index_le`/`stack_step_region_index_le` mirroring S2/S3 at the `ReachableStep` level) showing
  anything reachable from a suspended frame can never coincide with the mutated (active-frame-owned)
  container, so a suspended-rooted chain transports unconditionally
  (`fieldAsgn_confined_transport`); and, for the one case that genuinely needs it — a chain rooted at the
  *active* frame that uses the newly-written edge — a **per-branch escape/vacuity argument**: the
  FIELD-ASGN-STACK branch's newly-written value is a fresh `resolveV_frameRoot`-rooted reference (mirrors
  `varAsgn`'s escape), while the FIELD-ASGN-REGION branch's newly-written value is confined to the *same*
  region as the container (`hyloc`), so any chain using that edge can never reach an object in the
  suspended frame's *different* Open region — proved vacuous via a freshly-derived
  `reflTransGen_region_confined`/`reflTransGen_region_open_ne_absurd` pair (H3-driven, the same shape as
  `RegionReachable_oid_confined` above but generalized to an arbitrary confirmed-in-region starting point,
  not just a region's own bridge object). Both escape arguments are built as an induction via
  `Relation.ReflTransGen.head_induction_on`, generalized over an explicit `∀ a b, ...` (not just the fixed
  chain endpoints) — necessary because the chain's own root variables (`hrootG`/`hrootGcfg`) are already in
  scope when the induction starts, and `induction ... using head_induction_on` auto-reverts any hypothesis
  mentioning the chain's start point, bloating the motive if that point isn't first generalized away.
  Axiom-checked clean (`propext`/`Classical.choice`/`Quot.sound` only).
- **`merge`** — **fully proved, zero `sorry`** (finished 2026-07-31, commit `6a6ab82`, same session as
  `fieldAsgn` above). Confirmed the `merge_cr3` analogy from the note this bullet used to carry: `objAt?`
  is indeed fully unconditional (`merge_objAt_eq`, ported near-verbatim from `Referencable/`'s private
  `merge_corollary_objAt_eq` — the proof only depends on Model-layer facts, so it transplants directly),
  and `ReachableStep` for `OId` sources is unconditional too (`merge_oid_step_iff`). The one thing the
  `Referencable/` analogy did *not* anticipate: `ReachableStep` (unlike `RefStep`) has a real `RId` branch,
  and merge's mutation reassigns `x`'s var slot from `RId rid'` (the merged-away region) to `OId
  region'.bridgeObjectId` directly — a **genuine value change**, not just a relocation, for that one slot.
  This is where all the new work went:
  - **The key insight, `merge_ridPrime_step_iff_bridge`**: `RId rid'` and `OId region'.bridgeObjectId` are
    *interchangeable as `ReachableStep` sources* — stepping from `RId rid'` is by definition exactly
    stepping from the region's own (Closed) bridge object's fields. So `Relation.ReflTransGen
    (ReachableStep cfg) (RId rid') target ↔ ReflTransGen (ReachableStep cfg) (OId region'.bridgeObjectId)
    target` (`merge_ridPrime_reflTransGen_iff`, whenever `target` is neither of the two source shapes
    itself) — the reassigned var slot literally reads off the *same* reachable set, one hop shorter. This
    meant no escape/induction machinery was needed at all, unlike what `fieldAsgn`/`varAsgn` required —
    the "old" and "new" root values are provably equivalent, not just independently-rooted.
  - **H2-driven uniqueness** (`merge_ridPrime_not_step_target`, `merge_ridPrime_no_other_frame_var`,
    `merge_ridPrime_var_unique`): needed to confirm `RId rid'` can *only* ever be `x`'s own var value —
    never a step target anywhere (so it can't reappear mid-chain), never held by another frame's var, and
    never held by another var in the *same* frame (H2's global "at most one occurrence of a given `RId`"
    bound, pinned to exactly 1 by `x`'s own occurrence, forces every other slot to 0). This is what let the
    proof route around ever needing a `fieldAsgn`-style per-hop escape induction: since `RId rid'` can only
    be the *root*, not an intermediate node, `hstepIffOfNe`/`hchainTransportUp`/`_Down` transport whole
    chains unconditionally once the root itself is confirmed `≠ RId rid'`.
  - Two small generic list lemmas added to `Lemmas.lean` (`stack_refs_eq_flatMap`/`heap_refs_eq_flatMap`,
    reshaping `Stack.refs`/`Heap.refs` into plain `List.flatMap` form) made the H2 count arguments above go
    through `Gc.Model.Theorems`'s existing `List.two_le_count_flatMap_of_ne`/`List.count_le_count_flatMap_of_mem`
    directly, rather than re-deriving count identities from scratch.
  - Also ported (not otherwise available in this layer): `loc_ne_none_of_mem_objectIds`,
    `merge_objectIds_perm`, `merge_corollary_union_lookup_left`/`_right`, `merge_corollary_objMap_get_eq`
    (this last one a thin wrapper around `Gc.Model.Preservation.Common`'s already-public
    `stackWithIndex_objMap_get_eq_of_last_varMap_update`, so genuinely one line once the wrapper shape was
    right).
  - Axiom-checked clean (`propext`/`Classical.choice`/`Quot.sound` only, via `lean_verify` on
    `stackReachable_invariant_merge`).
- **`swap`** — **fully proved, zero `sorry`** (finished 2026-08-01, commit `ef84205`). All four branches
  (SWAP-STACK/SWAP-REGION-OBJECT/SWAP-REGION-REGION/SWAP-REGION-BRIDGE) done; this was, as anticipated,
  the largest operation in this layer. See "How `swap` actually went" immediately below for what
  happened relative to the pre-work scoping notes (kept for the one genuinely load-bearing architectural
  choice it records — the rest of the original scoping is superseded and was removed).

### How `swap` actually went (2026-08-01)

Scoped the session before as the hardest op left, expected to need `Referencable/`'s
`Validity/Preservation/Swap.lean` (`swap_cr3`, 1832 lines) as a structural map, re-derived fresh (never
imported, per this layer's independence rule) into `Reachable/Lemmas.lean` and
`Reachable/Scratch.lean`'s `stackReachable_invariant_swap`. Four branches, needing both `fieldAsgn`-style
per-hop escape induction (`main_claim`, since swap's mutated container's own content genuinely changes)
and `varAsgn`-style root escape (`resolveFA_frameReach`, since the swapped var/bridge slot gets a new
value) combined — confirmed correct going in.

**The one real surprise, and the reason the `RId`-mid-chain worry mostly evaporated**: `swap_cr3` proves
CR3 for *arbitrary* frame pairs, so its own escape helpers (`swap_corollary_escape`/`_root_escape`) have
to *collapse to the target frame internally* (via their own `by_cases heqidx` + `vrcfg.cr3` recursion).
`stackReachable_invariant_swap`'s target is different — a single *fixed* suspended `frame`/`oid` pair —
and the proof already builds a reusable `finish : ∀ E, FrameReachable cfg E.index oid → FrameReachable
cfg frame.index oid` for completely unrelated reasons (collapsing an arbitrary cfg-side witness down to
`frame` via `hcr3`). Once `main_claim`'s escape branch is written to return the *generic*
`∃ frameE ∈ cfg.stackWithIndex, FrameReachable cfg frameE.index b` (fieldAsgn's own shape — a witness
frame plus a fact about whatever the induction's target `b` happens to be, not yet collapsed to `frame`)
rather than swap_cr3's `FrameReachable cfg frameD.index oid` (already collapsed), `finish` handles the
collapse *once*, uniformly, after the escape — and at that point `FrameRoot`'s var/bridge disjuncts
literally don't care whether the escaped value is `OId`- or `RId`-shaped (`⟨xRef, Or.inl ⟨frame0, ...⟩,
hchain⟩` typechecks either way, `hchain` being an opaque already-established chain fact regardless of how
many further hops it represents). So `reflTransGen_rid_source_open_absurd` and `swap_root_escape_rid`
(built anticipating a `merge_ridPrime_step_iff_bridge`-style mid-chain continuation argument would be
needed, mirroring `swap_cr3`'s vacuity-dismissal gap over `RefStep`) ended up **not called** by the final
proof — genuinely dead code, kept rather than deleted since it's an independently true, cheap-to-state
fact and a plausible half-hour re-derivation cost if ever needed. This is the concrete lesson: *whether* a
`RefStep`→`ReachableStep` gap needs handling depends on which proof shape the theorem sits in, not just
on the operation's own diff, and it's worth checking whether a `finish`/collapse-once helper is already
available before assuming the CR3-style collapse-inside-the-escape technique is the only option.

Also generalized `resolveFA_frameReach` (in `Lemmas.lean`, shared with `varAsgn`/`fieldAsgn`) from an
`OId`-specific target to an arbitrary `Reference` — a field access can resolve to an `RId` value too
(objects can hold region references in their fields, same as `varMap`/`objMap` slots elsewhere in the
model), and swap's non-bridge branches write `resolveFA`'s result into a var slot without constraining
its shape. The generalization is a strict widening (implicit `ref` inferred as `Reference.OId oid` at
existing call sites), so `varAsgn`/`fieldAsgn`'s own uses were unaffected.

Recurring gotchas from every other file in this session resurfaced here too, unchanged: the multi-line
record-literal parser error inside a `have`'s/theorem parameter's type (fix: collapse to one line, or
`set` the record first); `subst` on an equation with the freshly-`induction`-introduced variable on one
side and an *outer* variable on the other silently eliminating the *outer* one instead (fix: `rw [h] at
hyp` targeted at the specific hypothesis, never blanket `subst`, exactly as documented under
`Swap.lean`/`CR5.lean` above); and `AList.lookup_insert`'s underlying-`AList` argument needing to be
supplied explicitly (`AList.lookup_insert cfg.heap`) whenever it can't be inferred purely from the
expected-type unification context.

Verified via a full `lake build` (1066 jobs, clean), a project-wide `grep -rc sorry Gc/` (0 across all
files), and `lean_verify` on `stackReachable_invariant_swap` (only `propext`/`Classical.choice`/
`Quot.sound`).

## Next planned step

`Gc/Model/` (the runtime model and its operational-semantics preservation proofs) has been **complete**
since 2026-07-26. As of 2026-07-28, `Gc/Reachability/Referencable/`'s CR3 layer (`Validity/Preservation/*.lean`) is
now **also complete: all 9 operations proved, zero `sorry`** — `Enter`/`Exit`/`MakeObjStack`/
`MakeObjRegion`/`MakeRegion`/`Merge` (earlier sessions), `FieldAsgn`/`VarAsgn` (earlier this session), and
finally `Swap.lean`'s `swap_cr3` (see its own "Current known state" bullet above for how it combines the
`fieldAsgn_cr3`/`varAsgn_cr3` techniques). A full `lake build` (1058 jobs) and a project-wide sorry scan
(0 sorries across all 42 `.lean` files under `Gc/`) both confirm the entire proof development is now
`sorry`-free — this is the first time that's been true since the `Reachability/` layer was started.

**The consolidation described above is now done (2026-07-28, same day as `swap_cr3`).** A new
`Gc/Model/Preservation/Common.lean` (imports only `Types`/`Helpers`/`Validity`/`Theorems` plus
`Mathlib.Data.List.Infix` — the latter turned out load-bearing: dropping it broke a `Nat`-order
dot-notation lemma, `hlt.trans`, in `Enter.lean`'s `enter_cr3`, since that Mathlib import was previously
reaching `Enter.lean` transitively through `Gc.Model.Preservation.Swap`) now holds every generic,
non-operation-specific fact that had accumulated in an arbitrary operation's own file:
`heap_objectIds_of_mem` (originally in `Exit.lean`; also used by `Merge`/`MakeObjStack`/`MakeObjRegion`/
`MakeRegion`'s CR3 files, purely via importing `Gc.Model.Preservation.Exit`),
`swap_corollary_stackWithIndex_index_inj`/`_find_eq` (originally in `Swap.lean`; used by all 9
`Reachability/Validity/Preservation/*.lean` files), and `merge_corollary_regionId_unique_index`
(originally in `Merge.lean`; used by `Corollaries.lean` itself plus `Swap`/`Exit`/`VarAsgn`/
`MakeObjRegion`'s CR3 files). Names were kept identical to their pre-extraction names to avoid a mass
rename across ~40 call sites — only the *location* and *import path* changed. Every
`Gc/Reachability/Referencable/Validity/Preservation/*.lean` file's imports were updated to `import
Gc.Model.Preservation.Common` directly (dropping `Gc.Model.Preservation.Swap`/`Exit` where that was the
only reason for the import; `Swap.lean`/`Exit.lean`/`Merge.lean`'s own Reachability-layer files keep their
legitimate operation-specific import *and* gained the explicit `Common` import, rather than relying on
getting these facts transitively). `Gc/Reachability/Referencable/Corollaries.lean` now imports
`Gc.Model.Preservation.Common` instead of `Gc.Model.Preservation.Merge`.

The triplicated `resolveV_frameRoot`/`resolveFA_frameReach` pair (`fieldAsgn_corollary_resolveV_frameRoot`/
`varAsgn_corollary_resolveV_frameRoot`/`swap_corollary_resolveV_frameRoot`, and
`varAsgn_corollary_resolveFA_frameReach`/`swap_corollary_resolveFA_frameReach`) were byte-for-byte
identical private copies in `FieldAsgn.lean`/`VarAsgn.lean`/`Swap.lean` — these are now a single public
`resolveV_frameRoot`/`resolveFA_frameReach` pair in `Gc.Reachability.Referencable.Corollaries` (already imported
everywhere they're needed), and all call sites across the three files were renamed to the shared,
un-prefixed names.

Verified via a full `lake build` (1060 jobs, clean) and a project-wide `grep -c sorry` (still 0 across all
of `Gc/`) after every edit.

**A second consolidation pass (2026-07-28, same day, later session) went beyond import-location smells and
found genuinely reconstructed proofs** — same theorem, copy-pasted body, in multiple
`Gc/Reachability/Referencable/Validity/Preservation/*.lean` files, not just a borrowed lemma:
- `stackWithIndex_getElem_index_eq` (`Common.lean`): `cfg.stackWithIndex[fid]? = some frame → frame.index
  = fid`, fully generic (no `cfg'`/mutation involved at all) — was three byte-for-byte-identical private
  copies (`enter`/`exit`/`makeObjStack_corollary_getElem_index_eq`).
- `stackWithIndex_frame_transport_down_of_shape_eq`/`_up_of_shape_eq` (`Common.lean`): generalizes over an
  arbitrary `proj : Frame → α` plus a hypothesis `∀ n, (cfg.stack[n]?).map proj = (cfg'.stack[n]?).map
  proj`. `varAsgn`/`swap`'s versions were byte-for-byte identical (`proj := fun f => (f.regionId,
  f.bridgeVar)`); `fieldAsgn`'s used a 3-wide `proj` (adds `f.varMap`) since it's `objMap` fieldAsgn leaves
  untouched, not `varMap`. All three per-operation files now have a ~5-line wrapper (call the generic
  lemma with their own `proj` and their own pre-existing `_stack_shape_eq` fact, then `injection` the
  returned `Prod` equality back into named fields) instead of a ~20-line rebuild.
- `stackWithIndex_objMap_get_eq_of_last_varMap_update` (`Common.lean`): `merge`/`makeObjRegion`/
  `makeRegion_corollary_objMap_get_eq` were three copies of the *same* ~25-line argument, differing only in
  *which* reference got inserted into the last frame's `varMap` — a fact the theorem's own conclusion
  (about `objMap`, never `varMap`) doesn't even mention. Needed one signature change from the naive
  version: constrain `cfg'.stack` directly (`hstack' : cfg'.stack = ...`) rather than a full `cfg' = {cfg
  with stack := ...}` record equality, since `merge`/`makeObjRegion`/`makeRegion` all also change
  `cfg'.heap` — a full-record hypothesis would reject their actual `cfg'`.
- **Judgment call that went the other way**: `objAt_fresh` (`makeObjStack`/`makeObjRegion`/
  `makeRegion_corollary_objAt_fresh`) has the *same statement* across all three but a genuinely *different*
  proof each time (the fresh object lands in the frame's own `objMap`, a heap region's `objMap`, or a
  brand-new region, respectively) — correctly left alone, not merged.

All wrapper theorems kept their exact original names/signatures, so zero call sites outside the
`private theorem` bodies themselves needed to change. Verified via full `lake build` (1060 jobs) after
every file. Comments directly above each rewritten wrapper were updated to name the `Common.lean` lemma
they now call (a couple of pre-existing comments were also stale/copy-paste artifacts from before this
session — e.g. `varAsgn_corollary_frame_transport_up`'s comment said "Mirrors
fieldAsgn_corollary_frame_transport_down", clearly copied from `FieldAsgn.lean` without updating the name
— fixed to reference `varAsgn`'s own `_down` instead).

**Branch-local duplication inside `Swap.lean` — done (2026-07-28, same day, via `/lean4:refactor`)**:
the `swap_corollary_region_*`/`_region_bridge_*` corollary families (`_objAt_mutated`/`_objAt_eq_of_ne`,
four theorems) were merged pairwise by folding an explicit `newBridge : ObjectId` parameter into
`swap_corollary_region_objAt_mutated`/`_objAt_eq_of_ne` (non-bridge callers now pass
`newBridge := region.bridgeObjectId`); the `_bridge_` variants were deleted and their 3 call sites
repointed. Inside `swap_cr3` itself, the `escape` `have`-block turned out **byte-for-byte identical**
across all four sub-branches (SWAP-STACK/SWAP-REGION-OBJECT/SWAP-REGION-REGION/SWAP-REGION-BRIDGE) —
confirmed via a literal `diff`, not just a visual skim — so it was pulled out verbatim as a standalone
`swap_corollary_escape` (parametrized over `oid`/`yf`/`yfRef`/`hyf`/`frameD`/`hframeDMem`/`hlocDown`; no
`Location`-parametrization was actually needed since `escape`'s own argument never inspects *where* the
mutated container lives). Separately, three of the four branches' `main_claim` (SWAP-STACK/
SWAP-REGION-OBJECT/SWAP-REGION-BRIDGE — SWAP-REGION-REGION's analogous case is vacuous, since its
`newVal = Reference.RId xrid` can never satisfy `heqv : Reference.OId oidc = newVal`) shared an
identical ~14-line "root escape" argument (`FrameReachable_owner_index_le` + `by_cases heqidx` +
`vrcfg.cr3` recursion) differing only in the swapped-in `newVal`/`hxRoot`; extracted as
`swap_corollary_root_escape`, parametrized over `newVal`, `hxRoot`, `heqv`, `ihchain`. All three batches
verified individually via `lean_diagnostic_messages` before moving to the next; final full `lake build`
(1060 jobs) clean, project-wide sorry scan still 0, and `lean_verify` on `swap_cr3`/`swap_reachable_valid`
still shows only `propext`/`Classical.choice`/`Quot.sound`. Net effect: 1489 → 1356 lines (~9% shorter).
`hoidm_ne` was deliberately **left alone**: it's already only 5 lines per branch, and unlike `escape`/
`main_claim`'s root-escape it isn't byte-identical across branches (SWAP-STACK's uses
`FrameReachable_stk_index_le`, the other three use `FrameReachable_owner_index_le` with a different
`rid`/`hrid`-direction argument each time) — factoring it would trade a few lines for an extra
indirection layer with no real duplication removed, so it wasn't worth the risk.

**Update (2026-07-29): `CR5_step` completed for all 9 operations, then restructured to match
report.pdf's own statement (CR5'→CR5 rename), and `CR4` was generalized to cover `RId` references
too** — see `Gc/Reachability/Referencable/Validity/CR5.lean`'s and `Gc/Reachability/Referencable/Corollaries/CR4.lean`'s own
entries above for the full breakdown. Two more structural changes landed the same day:

- **`Corollaries.lean` split** into `Corollaries/{Common,CR1,CR2,CR4}.lean`, and CR1/CR2/CR4's headline
  theorems renamed to bare `CR1`/`CR2`/`CR4` (matching report.pdf's numbering — same motivation as the
  CR5'→CR5 rename).
- **`Gc/Scratch.lean` retired.** It wasn't actually scratch — its `Stmt`/`step` dispatcher and
  `AllPreserve`/`allPreserve_ValidConfig`/`allPreserve_ValidReachableConfig` were genuine, load-bearing
  dependencies of `CR5.lean`. `Stmt`/`step` moved to `Gc/Model/Mutation/Stmt.lean`; the two
  `AllPreserve` instances folded into their respective layer's existing `Preservation.lean` aggregator
  (`Gc/Model/Preservation.lean` / `Gc/Reachability/Referencable/Validity/Preservation.lean`), which already imports
  exactly the per-operation facts each dispatcher needs. `Scratch.lean` itself was deleted; no proof or
  statement content changed.

Both verified via full `lake build` (1066 jobs) plus an explicit build of
`Gc.Reachability.Referencable.Validity.CR5` (still outside the default `Gc.lean` target — nothing downstream needs
it yet), zero live `sorry`.

**Current overall state** (this "Next planned step" section itself had drifted before this pass — the
`Mutation.lean`→`Mutation/` split and the deletion of the old `Reachability.lean` both predate the CR5
work above and were previously undocumented here; see the Architecture section for both):
- `Gc/Model/` — complete, zero `sorry`.
- `Gc/Reachability/Referencable/Validity/Reachable.lean` (CR3, all 9 operations) — complete, zero `sorry`.
- `Gc/Reachability/Referencable/Corollaries/{CR1,CR2,CR4}.lean` — complete.
- `Gc/Reachability/Referencable/Validity/CR5.lean` (`CR5_step`, single-step, all 9 operations) — complete, zero
  `sorry`.
- `Gc/Equivalence/Equivalence.lean` — still a genuine one-line stub (`import Gc.Model.Types` only), now
  tracked/committed (previously untracked WIP).
- `Gc/Reachability/Referencable/Guarantees.lean`/`Invariants.lean` — still empty / no proofs.

**Concretely still open** (multi-step CR5 deprioritized per user direction 2026-07-29 — not currently
being pursued, see `CR5.lean`'s own notes above):
- **report.pdf `CR6`** ("Liveness in a closed region is solely determined by region-reachability" —
  section 4.3.1, the corollary right after CR5, feeding guarantees G4/G5): not yet started anywhere in
  `Gc/`. Unlike CR3/CR5, its core fact ("no on-stack reference resolves into a Closed region") looks like
  it reduces directly to `S3` + `L2` on a single `ValidConfig` — no per-mutation preservation file
  needed — so it likely belongs in `Corollaries/` (a new `CR6.lean`) alongside CR1/CR2/CR4, not
  `Validity/`.
- After CR6, the natural next target is report.pdf's `Guarantees.lean` (currently empty) — CR5
  (report.pdf: "G3 comes directly as a result of CR5") is specifically the ingredient the
  concurrent-garbage-detection guarantee (G3) needs; CR6 similarly feeds G4/G5.

**`Gc/Reachability/Reachable/` is now complete (2026-08-01, commit `ef84205`)**: the new sibling
reachability layer described in its own Architecture bullet above. All 9 `Stmt` operations'
`stackReachable_invariant_<op>` proofs are done, zero `sorry` — `enter`/`exit`/`makeObjStack`/
`makeObjRegion`/`makeRegion`/`varAsgn`/`fieldAsgn`/`merge` (see that section's "per-operation status" for
details) and finally `swap` (see "How `swap` actually went" immediately after that section). This layer
still isn't wired into `Gc.lean`'s default target — build it explicitly via `lake build
Gc.Reachability.Reachable.Scratch` (or `.Lemmas`/`.Corollaries`/`.Semantics`), not the bare `lake build`.
A full project-wide `lake build` (1066 jobs) and `grep -rc sorry Gc/` (0 across every file) both confirm
the *entire* proof development — `Gc/Model/`, `Gc/Reachability/Referencable/`, and
`Gc/Reachability/Reachable/` — is `sorry`-free as of this commit.

**Not yet started, and no active thread currently claims it**: `stackReachable_invariant_all`'s own
consumers, i.e. nothing downstream of `Reachable/Scratch.lean` exists yet (no `Guarantees.lean`-analogue,
no multi-step generalization, and this layer was never wired to depend on or feed
`Gc/Reachability/Referencable/`'s CR3/CR5/CR6 work, by the independence rule stated in the Architecture
section). Natural next steps, in no particular committed order: wire this layer into `Gc.lean`'s default
build target now that it's complete; pursue report.pdf `CR6` (still open, see the bullet above); or
extend `Reachable/`'s own per-operation invariant to a multi-step version, mirroring the
`Referencable/`-side deprioritization of multi-step `CR5`. None of these has been started or asked for —
confirm direction with the user before picking one.

## Comment style

Lean comments (`--`) in this repo must be single-line only. Do not write multi-line/wrapped comment
blocks above declarations, even for non-obvious rationale — keep each comment to one line, or omit it.
