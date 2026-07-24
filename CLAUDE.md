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
  and resolving variable/field-access expressions against a config (`resolveV`, `resolveFA`).
- `Validity.lean` — defines `ValidConfig` as a bundle of 8 named invariants: `L1`/`L2` (global,
  e.g. object-id uniqueness, stack regions are Open), `H1`/`H2`/`H3` (heap-shape invariants, e.g. a
  region's bridge object is in its own objMap, at most one external ref to a region, region-internal
  refs resolve back into that region), `S1`/`S2`/`S3` (stack-shape invariants, e.g. no two frames share
  a region, no reference from an earlier frame into a strictly later frame/region). Also has lemmas
  relating an id's `loc?` to where it actually sits in the stack/heap.
- `Mutation.lean` — the operational semantics: each of `varAsgn`, `fieldAsgn`, `swap`, `enter`, `exit`,
  `makeObjStack`, `makeObjRegion`, `makeRegion`, `merge` takes a `RuntimeConfig` and returns
  `Option RuntimeConfig` (`none` = the transition is stuck/illegal, e.g. an out-of-region write).
- `Start.lean` — `RuntimeConfig.start` (the initial configuration: one root region, one root frame) and
  a proof that it satisfies `ValidConfig`.
- `Preservation/*.lean` — one file per `Mutation` operation (`Enter`, `Exit`, `FieldAsgn`,
  `MakeObjRegion`, `MakeObjStack`, `MakeRegion`, `Merge`, `Swap`, `VarAsgn`). Each proves that the
  operation preserves `ValidConfig` by discharging the 8 sub-invariants (`<op>_L1` … `<op>_S3`)
  individually and then combining them into a single `<op>_valid : ValidConfig cfg → op ... cfg = some
  cfg' → ValidConfig cfg'`. **This is the recurring proof-engineering pattern in the repo** — a new
  mutation operation is expected to get its own `Preservation/<Op>.lean` following this same shape.
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

- **`Exit.lean`** — **fully proved, builds cleanly, zero `sorry`** (as of 2026-07-24). All 8 invariants
  (`exit_L1` … the `S1`/`S2`/`S3` analogues, misleadingly named `exit_S2`/`exit_S3`/`exit_S4` in the
  file) plus all 3 corollaries (`exit_corollary_1`, `exit_corollary_2`, `exit_corollary_3`) have real,
  fully written proofs. `exit_corollary_3` (the last gap) required two more reusable helper lemmas
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
- **`Enter.lean`** — **fully proved, builds cleanly, zero `sorry`, zero warnings** (as of 2026-07-24).
  All 8 invariants (`enter_L1` … `enter_S3`) plus `enter_valid` are real proofs. Three reusable
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
  `MakeObjStack.lean`, `MakeRegion.lean`** — not started: all 8 invariant lemmas are bare `sorry`: only
  the combining `<op>_valid` theorem (which just assembles the 8 sorry'd lemmas) is written. These
  build successfully (a `sorry` doesn't fail compilation) but contain no real proof content yet.

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

`Exit.lean`, `Validity.lean`, and `Enter.lean` are now all fully done (zero `sorry`). The remaining
`Preservation/*.lean` files — `Merge.lean`, `Swap.lean`, `VarAsgn.lean`, `FieldAsgn.lean`,
`MakeObjRegion.lean`, `MakeObjStack.lean`, `MakeRegion.lean` — are all not started (8 bare-`sorry`
invariant lemmas each, only the combining `<op>_valid` assembled). No specific one has been agreed on
next.

Not yet started — confirm with the user before diving in.
