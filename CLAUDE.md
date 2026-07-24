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
- **`lake build` / `lake build Gc` (the library target) is currently broken** — do not rely on it.
  `Gc.lean` still has the `lake new` template's `import Gc.Basic`, and `Gc/Basic.lean` no longer
  exists (the model code moved under `Gc/Model` and `Gc/Reachability` without updating the root
  import). Building the bare `Gc` target fails immediately with a missing-file error. Always build
  the specific module(s) you're touching by qualified name instead. The same applies to `Main.lean`.
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
- **`Enter.lean`** — partial: `enter_L1`, `enter_L2`, `enter_H1` are fully proved. `enter_H2` is
  attempted but currently ends in a genuine **"unsolved goals"** error partway through (an intermediate
  `have` isn't fully closed by its `rw`) — this is what makes the file fail to build. `enter_H3`,
  `enter_S1`, `enter_S2`, `enter_S3`, and all 4 `enter_corollary_*` lemmas are untouched `sorry` stubs.
- **`Merge.lean`, `Swap.lean`, `VarAsgn.lean`, `FieldAsgn.lean`, `MakeObjRegion.lean`,
  `MakeObjStack.lean`, `MakeRegion.lean`** — not started: all 8 invariant lemmas are bare `sorry`: only
  the combining `<op>_valid` theorem (which just assembles the 8 sorry'd lemmas) is written. These
  build successfully (a `sorry` doesn't fail compilation) but contain no real proof content yet.

Elsewhere:

- `Gc/Model/Validity.lean` has two remaining `sorry`s (in `oid_loc_rgn_iff_in_heap` and
  `oid_loc_stk_iff_in_stack`).
- `Gc/Reachability/Guarantees.lean` is empty; `Gc/Reachability/Invariants.lean` has no proofs yet — this
  layer is much earlier-stage than `Gc/Model/`.

## Next planned step

`Exit.lean` is now fully done (see above, zero `sorry`). The next natural target is `Enter.lean`:
`enter_L1`, `enter_L2`, `enter_H1` are proved; `enter_H2` has a genuine "unsolved goals" error partway
through (an intermediate `have` isn't fully closed by its `rw`) which is what currently fails the build;
`enter_H3`, `enter_S1`–`S3`, and all 4 `enter_corollary_*` lemmas are untouched `sorry` stubs. Not yet
started — confirm with the user before diving in.
