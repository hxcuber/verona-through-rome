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

**`Merge.lean` is now finished** (2026-07-26; see its bullet above for full context — the heap-key-erasure
+ object-relocation machinery, the `merge_S3` "already impossible in `cfg`" resolution, and the new
generic `List.kunion_eq_append_of_disjoint_keys`/`AList.union_eq_append_of_disjoint_keys` pair added to
`Theorems.lean`). This was the last not-started `Preservation` file, so **every proof-bearing file in
`Gc/Model/` is now done, zero `sorry` anywhere**: `Start.lean`, `Validity.lean`, `Enter.lean`, `Exit.lean`,
`VarAsgn.lean`, `FieldAsgn.lean`, `Swap.lean`, `MakeObjStack.lean`, `MakeObjRegion.lean`, `MakeRegion.lean`,
and `Merge.lean` all build cleanly with fully-real proofs, and `lake build` (bare) succeeds end to end
(confirmed 2026-07-26 including the `merge_valid` axiom check: only `propext`/`Classical.choice`/
`Quot.sound`, no leaked `sorry`).

`Gc/Model/` — the runtime model and its operational-semantics preservation proofs — is thus **complete**.
The natural next step is the `Gc/Reachability/` layer (see its section above): `Reachability.lean`
currently fails to build (wrong `Location` constructor names, `Stack`/`Region` instead of `Stk`/`Rgn` —
not pulled into the default build target so this doesn't block `lake build`, but will need fixing before
that file is usable), `Invariants.lean` has definitions but no proofs yet, and `Guarantees.lean` is an
empty placeholder for the eventual GC-safety theorems this whole project is building toward. Scoping out
what those theorems should even *say*, in terms of `RegionReachable`/`StackReachable`/`FrameReachable`
from `Semantics.lean`, hasn't been done yet and would be the natural next planning session.
