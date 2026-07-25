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
- **`lake build` (bare, no target) now succeeds end to end**, including `Gc`, `Main`, and the `gc`
  executable — fixed 2026-07-24. `Gc.lean` no longer imports `Gc/Reachability/Reachability.lean` (it
  pattern-matched on wrong `Location` constructor names — `Location.Stack`/`Location.Region` instead of
  the real `Location.Stk`/`Location.Rgn` — and never built; that file itself is untouched/still broken,
  it's just no longer pulled in). `Main.lean`'s undefined `hello` (leftover from the `lake new` template)
  was replaced with a plain greeting. The only remaining build output is expected `sorry` warnings from
  the not-yet-started `Preservation` files. Still prefer building the specific module(s) you're touching
  by qualified name for faster iteration, e.g. `lake build Gc.Model.Theorems`.
- Toolchain is pinned via `lean-toolchain` (`leanprover/lean4:v4.29.0-rc6`) and dependencies via
  `lake-manifest.json`; the main dependency is `mathlib`. First builds after a fresh clone can be slow
  because of mathlib — subsequent builds reuse `.lake/build`.

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
- `Mutation.lean` — the operational semantics: each of `varAsgn`, `fieldAsgn`, `swap`, `enter`, `exit`,
  `makeObjStack`, `makeObjRegion`, `makeRegion`, `merge` takes a `RuntimeConfig` and returns
  `Option RuntimeConfig` (`none` = the transition is stuck/illegal, e.g. an out-of-region write).
- `Start.lean` — `RuntimeConfig.start` (the initial configuration: one root region, one root frame) and
  a proof that it satisfies `ValidConfig`.
- `Preservation/*.lean` — one file per `Mutation` operation (`Enter`, `Exit`, `FieldAsgn`,
  `MakeObjRegion`, `MakeObjStack`, `MakeRegion`, `Merge`, `Swap`, `VarAsgn`). Each proves that the
  operation preserves `ValidConfig` by discharging the 9 sub-invariants (`<op>_L1` … `<op>_S3`, plus
  `<op>_HS1`) individually and then combining them into a single `<op>_valid : ValidConfig cfg → op ...
  cfg = some cfg' → ValidConfig cfg'`. **This is the recurring proof-engineering pattern in the repo** —
  a new mutation operation is expected to get its own `Preservation/<Op>.lean` following this same shape.
- `Theorems.lean` — generic `List`/`AList` lemmas (not domain-specific) used as a small helper library
  by the `Preservation` proofs.

### `Gc/Reachability/` — reachability/liveness definitions (newer, less complete layer)

- `Semantics.lean` — `RegionReachable` (reachable from a region's bridge object, staying inside the
  region), `StackReachable`/`FrameReachable` (reachable from stack variables, optionally scoped to one
  frame's stack-index).
- `Reachability.lean` — a fuel-based *computational* reachability walk (`Region.reachableRefs`,
  `RuntimeConfig.stackReachableRefs`) rather than the inductive props above; **currently fails to
  build** — it pattern-matches on `Location.Stack`/`Location.Region`, but `Types.lean`'s `Location`
  constructors are actually named `Location.Stk`/`Location.Rgn`.
- `Invariants.lean` — cross-config properties about reachability being preserved for suspended regions
  and earlier frames across a transition (currently just definitions/comments, no proofs yet).
- `Guarantees.lean` — currently an empty file (placeholder for the eventual GC-safety theorems).

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
- **`Merge.lean`, `Swap.lean`, `VarAsgn.lean`, `FieldAsgn.lean`, `MakeObjRegion.lean`,
  `MakeRegion.lean`** — not started: all 8 original invariant lemmas are bare `sorry`, and each now also
  has a bare-`sorry` `<op>_HS1` (added 2026-07-25 purely to keep these files compiling after `ValidConfig`
  gained the `hs1` field — no real `HS1` proof content for these ops yet). Only the combining `<op>_valid`
  theorem (which just assembles the 9 sorry'd lemmas, including `hs1 := <op>_HS1 vcfg h`) is written.
  These build successfully (a `sorry` doesn't fail compilation) but contain no real proof content yet.
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
- `Gc/Reachability/Guarantees.lean` is empty; `Gc/Reachability/Invariants.lean` has no proofs yet — this
  layer is much earlier-stage than `Gc/Model/`.

## Next planned step

`MakeObjStack.lean` is now finished (see its bullet above for full context — freshness helper, `set
newFrame` gotcha, `calc`-with-`Perm` gotcha, the `find?_cons_of_pos/neg` HOU gotcha, and the
corollary-pruning story). Together with `Exit.lean`, `Validity.lean`, `Enter.lean`, and `Start.lean`,
that's every proof-bearing file in `Gc/Model/` done except the six not-started `Preservation` files below
(zero `sorry` anywhere in `Gc/Model/`, including the `HS1` invariant added mid-session — see
`Validity.lean`'s note above for why it was added).

The remaining **not-started** `Preservation/*.lean` files — `Merge.lean`, `Swap.lean`, `VarAsgn.lean`,
`FieldAsgn.lean`, `MakeObjRegion.lean`, `MakeRegion.lean` — each have 9 bare-`sorry` invariant lemmas
(the original 8 plus `<op>_HS1`, added so they'd keep compiling after `ValidConfig` gained the `hs1`
field), with only the combining `<op>_valid` assembled. No specific one has been agreed on next — confirm
with the user before diving into any of these.
