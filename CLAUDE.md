# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project

Final year project (Imperial College, 2025-26): a Lean 4 formalization of a Verona/Reggio-style
region-based memory management model (stack + heap of regions, bridge objects, region open/closed
status) and, on top of it, reachability definitions and per-operation invariants supporting garbage
collection safety guarantees.

Repo layout:
- `lean/gc/`: the Lean 4 project. All paths below are relative to this directory.
- `lean/gc/README.md`: raw meeting notes and design-decision log, not user docs. Read it for *why* the
  model is shaped the way it is (e.g. why `RegionId` is separate from `BridgeObjectId`, why a stack frame
  owns its own `objMap` for temporaries, why there's a single combined heap).
- `report.pdf`, `slides.pdf`: the written FYP report and presentation slides (binary).

## Commands

All commands below assume `cd lean/gc`.

- **Whole project**: `lake build`. `Gc.lean` imports every top-level module, so a bare build checks the
  entire development (Model and Reachable layers), plus `Main` and the `gc` executable. It builds with
  zero errors, zero warnings and zero `sorry`.
- **Single module**: `lake build Gc.Model.Preservation.Swap` (the dotted path mirrors the file path).
- Toolchain is pinned via `lean-toolchain` (`leanprover/lean4:v4.36.0`). The main dependency is
  `mathlib`, pinned to its `v4.36.0` tag in `lakefile.toml`. First builds after a fresh clone are slow
  because of mathlib; later builds reuse `.lake/build`.

## Workflow

Iterate through the `/lean4` skills (`/lean4:prove`, `/lean4:draft`, `/lean4:refactor`, `/lean4:golf`,
`/lean4:review`, `/lean4:checkpoint`, ...) and the Lean LSP MCP tools (`lean_goal`,
`lean_diagnostic_messages`, `lean_multi_attempt`, `lean_file_outline`, `lean_verify`, ...) rather than
shelling out to `lake build`/`grep` and hand-simulating goal states. Fall back to `lake build` only for a
concrete reason (checking the whole-project build after a cross-file change, or a stale/unresponsive LSP),
and say so when you do.

## Module system

Every file uses the Lean module system with the same header shape:

```lean
module

public import Gc.Some.Dependency

@[expose] public section
```

- Imports are minimal: a file does not re-import anything already brought in transitively by another of
  its imports. Aggregator files (`Gc.lean`, `Mutation/Mutation.lean`, `Preservation.lean`,
  `Reachable/Lemmas.lean`, the `All.lean` files) list their members explicitly.
- File-local helpers are `private`, so they are invisible downstream and can't clash with same-named
  helpers in sibling files. A helper needed by more than one file is made public and lives in the
  appropriate shared file (see the `Common.lean` files below).

## Architecture

### `Gc/Model/`: the runtime model and its operational semantics

- `Types.lean`: the core data model: `RegionId`/`ObjectId`/`BridgeObjectId`, `Reference` (`RId`/`OId`),
  `VarMap`/`ObjMap` (as `AList`s), `Region` (bridge object + objects + `Status` Open/Closed), `Frame`
  (region, bridge var, local var map, local obj map), `Stack`, `Heap`, `RuntimeConfig` (`stack` + `heap`),
  `Location` (`Rgn`/`Stk`).
- `Helpers.lean`: projections and derived queries: `refs`/`objectIds` of objects, regions, frames, heap,
  stack and config; `regionIds`; `freshRegionId`/`freshObjectId` (with `_not_mem` lemmas);
  `Reference.loc?` (where a reference lives); `Reference.objAt?`; `resolveV`/`resolveFA` (variable and
  field-access expressions).
- `Validity.lean`: `ValidConfig`, a bundle of **10** named invariants: `L1`/`L2` (global, e.g. object-id
  uniqueness, stack regions are Open), `H1`/`H2`/`H3` (heap shape, e.g. a region's bridge object is in its
  own objMap, at most one external ref to a region, region-internal refs resolve back into that region),
  `S1`/`S2`/`S3` (stack shape, e.g. no two frames share a region, no reference from an earlier frame into a
  strictly later frame/region), `HS1` (every stored `OId` is in `cfg.objectIds`) and `HS2` (every stored
  `RId` is a heap key). Also `oid_loc_rgn_iff_in_heap`/`oid_loc_stk_iff_in_stack` and the
  `oid_in_stack_implies_not_in_heap` pair relating `loc?` to actual placement.
- `Theorems.lean`: generic `List`/`AList` lemmas (not domain-specific), e.g. `List.find?_eq_some_of_unique`,
  `List.kunion_eq_append_of_disjoint_keys`, `List.two_le_count_flatMap_of_ne`,
  `List.eq_of_mem_flatten_map_nodup`/`List.index_eq_of_mem_flatten_map_nodup`,
  `AList.keys_insert_perm_of_mem`.
- `Mutation/<Op>.lean`, one per operation (`Enter`, `Exit`, `FieldAsgn`, `MakeObjRegion`, `MakeObjStack`,
  `MakeRegion`, `Merge`, `Swap`, `VarAsgn`): the operation itself (`RuntimeConfig → Option RuntimeConfig`,
  `none` meaning stuck/illegal) **and** a public `<op>_cases` lemma unpacking its `do`-block into explicit
  ∃-bundles. Every downstream proof about an op opens with `obtain ⟨..., rfl⟩ := <op>_cases h` instead of
  unfolding the operation. `Mutation/Mutation.lean` aggregates the nine.
- `Mutation/Stmt.lean`: `inductive Stmt` (one constructor per operation) and `step : Stmt → RuntimeConfig →
  Option RuntimeConfig`, so later layers can quantify over all operations.
- `Start.lean`: `RuntimeConfig.start` (one root region, one root frame) and `RuntimeConfig.start_valid`.
- `Preservation/<Op>.lean`: proves the op preserves each invariant (`<op>_L1` … `<op>_HS2`) and combines
  them into `<op>_valid : ValidConfig cfg → <op> ... cfg = some cfg' → ValidConfig cfg'`. The usual shape:
  one `<op>_cases` opener, one `<op>_loc`-style lemma describing every `loc?` after the op in terms of
  before, and frame-counterpart lemmas ("each new frame has an old counterpart with the same index and
  region", and conversely) from which the stack invariants follow. A new operation gets its own
  `Preservation/<Op>.lean` of this shape.
- `Preservation/Common.lean`: shared stack/heap transport facts. Check here (`lean_file_outline`) before
  re-deriving one. Highlights: `heap_region_unique`, `loc_match_eq`, `loc_eq_of_find_map_eq`,
  `stack_eq_of_stackWithIndex_getLast?`, `stackWithIndex_eq_of_getLast?`,
  `stackWithIndex_mk_append_singleton`, `stackWithIndex_frame_transport_down/up_of_shape_eq`,
  `refs_mem_of_stackWithIndex`, `stack_refs_mem`, `frame_varMap_insert_refs_mem`,
  `object_insert_refs_mem`, `objMap_insert_field_refs_mem`, `heap_insert_refs_mem`,
  `heap_insert_objectIds_perm`, `freshObjectId_not_mem_frame`, `ne_freshObjectId_of_mem_refs`,
  `merge_corollary_regionId_unique_index`, `swap_corollary_stackWithIndex_index_inj`.
- `Preservation.lean`: aggregator; defines `StepPreserves`/`AllPreserve` and proves
  `allPreserve_ValidConfig : AllPreserve ValidConfig` by `cases` on `Stmt`.

Each `<op>_valid` is a single-config invariant: nothing in this layer reasons about reachability chains.

### `Gc/Reachability/Reachable/`: reachability over `ReachableStep`

Organized property-first: one folder per headline claim, one file per operation inside it, with the shared
per-operation toolkit in `Lemmas/`.

- `Semantics.lean`: `ReachableStep` (an `OId` steps to any reference stored in the object it resolves to; an
  `RId` steps into a **Closed** region's bridge object, and doesn't step at all if the region is Open, so a
  chain can cross a Closed region's boundary), its unfolding lemmas `ReachableStep_rid_iff`/
  `ReachableStep_oid_iff`, and `RegionReachable`/`FrameReachable`/`StackReachable`/`FrameRoot` with the
  `RegionReachable_iff_reflTransGen`/`FrameReachable_iff_reflTransGen` conversions. Proofs work almost
  entirely with the `Relation.ReflTransGen (ReachableStep cfg)` form. `RegionReachable`/`FrameReachable`
  never cross an `RId` boundary within one relation; bridging that seam is what makes the Closed-region
  results below non-trivial.
- `Lemmas/Common.lean`: operation-independent machinery shared across the layer. Groups:
  - step unpacking: `bridge_loc`, `oid_step_container` (the target is a ref of the source's region or stack
    frame), `rid_step_inv`, `predecessor_cases`, `predecessor_of_region_object`,
    `predecessor_of_closed_region_object`, `predecessor_of_stack_object`, `open_rid_no_step`;
  - backward chase: `SafeRef`, `predecessor_safe`, `safe_reflTransGen_transport`;
  - owner-index bounds: `stack_container_confined`, `region_container_confined`, `stack_step_index_le`;
  - Closed regions: `closed_region_not_owned`, `closed_chain`, `RegionReachable_of_FrameReachable_closed`,
    `FrameReachable_rid_of_closed_container`;
  - chain building: `FrameReachable_extend`, `StackReachable_of_root`, `reflTransGen_split` (a chain under a
    relation that changed only at one source is an old chain or ends in an old chain from the new target),
    `StackReachable_of_edge_added`, `FrameReachable_of_StackReachable` (the forward direction every
    `<op>_suspended_reach` uses);
  - stack-index facts: `stackWithIndex_getLast_mem`, `regionId_ne_last_of_suspended`, `index_le_last`,
    `index_lt_length_sub_one`, `stackWithIndex_length_of_replace_last`, `last_frame_root`;
  - `objAt?`/step agreement after an edit: `objAt_of_loc_last`, `objAt_insert_step`, `objAt_last_frame_eq`,
    `objAt_heap_insert_eq`, `step_iff_of_ne_of_objAt`, `rid_step_iff_of_insert_open`,
    `ne_freshRegionId_of_lookup`, `frame_regionId_ne_fresh`.
- `Lemmas/<Op>.lean`: per-op `loc?`/`objAt?`/`ReachableStep` agreement facts, frame-membership transports
  (`<op>_frame_mem_up/down`, `<op>_frame_cases`), frame-reachability transports
  (`<op>_frame_reachable_iff`), and one `<op>_suspended_reach` lemma: the argument shared by both leaf
  files of that op. These files import `FrameReachableAtLaterFrame/Def.lean` where they need its
  hypothesis. `Lemmas.lean` aggregates all of `Lemmas/*.lean`.
- `StackReachableIffRegionReachableOfClosed.lean` (report.pdf CR6):
  - `StackReachable_iff_RegionReachable_of_closed`: for a Closed region `rid` whose `RId` is
    stack-reachable, an object inside `rid` is `StackReachable` iff it's `RegionReachable cfg rid`. The
    forward direction needs only closedness (every path enters through the bridge hop); the `RId`
    hypothesis is used to glue that hop onto the stack in reverse.
  - `not_StackReachable_rid_implies_not_StackReachable_objects_of_closed`: an unreachable Closed region's
    contents are all unreachable.
- `FrameReachableAtLaterFrame/`:
  - `Def.lean`: `FrameReachable_at_later_frame_implies_FrameReachable_at_frame cfg` (an object in an
    earlier frame's region that's frame-reachable from a later frame is already frame-reachable from the
    earlier one) and its single-step preservation wrapper `FrameReachableAtLaterFrame_step cmd`.
  - `Start.lean`: `RuntimeConfig.start_frameReachableAtLaterFrame`, the property at the initial config.
  - `<Op>.lean`: `frameReachableAtLaterFrame_step_<op>`, each a short derivation from
    `Lemmas/<Op>.lean`; `All.lean`: `frameReachableAtLaterFrame_step_all` (`cases cmd`).
- `StackReachableInvariant/`:
  - `Def.lean`: `StackReachable_invariant_for_suspended_region_objects cmd`, the layer's headline claim:
    for `ValidConfig cfg`, a step `cmd` to `cfg'`, the `FrameReachableAtLaterFrame` property on `cfg`,
    and an object `oid` in the region of a *suspended* frame (index below the last frame's),
    `StackReachable cfg (OId oid) ↔ StackReachable cfg' (OId oid)`.
  - `<Op>.lean`: `stackReachable_invariant_<op>`, each derived from `<op>_suspended_reach`; `All.lean`:
    `stackReachable_invariant_all`.

Leaf files import only the `Lemmas` aggregator (plus `StackReachableInvariant/Def.lean`); they never import each other.

### Proving technique for "suspended region unaffected by active-frame mutation"

If an operation is purely additive or only touches the active (last) frame's `varMap`/scalar fields, the
step relation is pointwise equal (or equal up to a fresh id) between `cfg` and `cfg'`, so only the root
set needs transporting (`<op>_frame_reachable_iff`). When an operation edits an existing object's field
(`FieldAsgn`/`Swap`), the step relation changes at the mutated container, so the proof splits each chain
with `reflTransGen_split` and closes the branch using the new edge either by an owner-index bound
(`region_container_confined`/`stack_container_confined`: the active container can't be reached from a
suspended root) or by tracing the written value's own root (`resolveV_frameRoot`/`resolveFA_frameReach`).

## Proof-engineering gotchas

- **`rw [find?_cons_of_pos/neg h]` fails via higher-order-unification ambiguity** when `h`'s type is an
  unreduced lambda application. Fix: state the concrete `find?` equality as its own `have` (proved by
  term application), then `rw` with that.
- **Multi-line record literals inside a `have`'s/theorem's type** can hit a parser error ("unexpected
  identifier; expected '}'"). Fix: `set newFrame : Frame := { ... } with newFrame_def` once and refer to
  `newFrame`, or put the literal on one line with a type ascription.
- **`cases h : e with` generalizes every occurrence of `e`**, including inside existential conjuncts and
  earlier hypotheses. Use `rfl` where a conjunct became reflexive, or `rw [h] at <hyp>` targeted.
- **A lemma stated with `match ... with` can't be used by `rw`/`simp`** on an alpha-equivalent goal (each
  `match` compiles to its own auxiliary definition). Apply it as a term (`.trans`/`exact`, which check by
  defeq).
- **`X ▸ h` can fail on `n + 1` vs `.succ` display mismatches.** Use `rw [X] at h` and a separate closing
  tactic.
- **`omega` fails on goals over `Index`** (and is occasionally flaky on visibly sufficient `Nat` goals).
  Use explicit lemmas instead: `Nat.le_of_lt_succ`, `lt_of_le_of_ne`, `Nat.not_le.mpr`.
- **`AList.insert` at an already-present key reorders `.entries`** (via `kerase`), unlike a fresh key
  (`AList.entries_insert_of_notMem`). Use the `List.Perm` facts `AList.keys_insert_perm_of_mem`,
  `heap_insert_refs_perm`, `heap_insert_objectIds_perm`.
- **`Stack.objectIds`/`Stack.refs` don't resolve via dot notation on a bare `List Frame`** (e.g. after
  `dropLast`/`++`). Write `Stack.objectIds cfg.stack.dropLast`.
- **Mixing `=` and `~` (`List.Perm`) steps in one `calc` doesn't parse.** Chain separately named `have`s
  with `.trans`.
- **`AList.mem_insert.mpr` doesn't resolve as dot notation.** Write `(AList.mem_insert _).mpr ...`.
- **`Status` derives `BEq`/`DecidableEq` but not `LawfulBEq`**, so `beq_iff_eq` won't synthesize and
  `Status.Closed == Status.Open` won't simp away. Case on the status or use `decide`.
- **After `rw [hne]` turns an `ite` condition into `false = true`, `split_ifs <;> omega` doesn't close it.**
  Eliminate the branch first, e.g. `rw [if_neg (by decide)]`.
- **A `rw` list with the same-shaped lemma twice can rewrite the wrong occurrence** (e.g. two
  `List.count_append`s). Split into separate `have`s.
- **`{ x with ... }` inside a standalone `have`'s type elaborates at `x`'s declared type** (e.g.
  `FrameWithIndex` instead of `Frame`). Ascribe: `({ x with ... } : Frame)`.
- **Passing a replacement record (`newFrame`/`newRegion`) implicitly can silently mis-unify.** Pass it
  explicitly or via `(newVal := ...)`.
- **`subst heq` can eliminate the outer variable instead of the fresh one.** Use `rw [heq] at <hyp>`.
- **`AList.lookup_insert` sometimes needs its `AList` explicitly**, e.g. `AList.lookup_insert cfg.heap`.
- **`Relation.ReflTransGen.head_induction_on` bloats its motive** if a hypothesis mentioning the chain's
  start is in scope. Generalize the start point first (induct over an explicit `∀ a b, ...`).

## Comment style

Lean comments (`--`) must be single-line: one short line per non-obvious declaration, or none. Comments
describe the code as it is now.
