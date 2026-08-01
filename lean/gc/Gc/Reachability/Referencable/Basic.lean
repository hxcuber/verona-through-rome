import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Mutation.Stmt
import Gc.Reachability.Referencable.Semantics

-- report.pdf CR3: if an object o lives in a (suspended) region R with associated frame F,
-- and o is frame-reachable from some later frame F', then o is frame-reachable from F itself.
-- "suspended" doesn't need to be stated separately: frame.index < frame'.index with both
-- frame/frame' on the stack already forces F to not be the active/last frame.
--
-- Unlike L1/H1-H3/S1-S3/HS1-HS2 (Gc/Model/Validity.lean), CR3 is not provable from a single
-- ValidConfig snapshot alone -- it's fundamentally a fact about how references come to exist
-- via the operational semantics (varAsgn/fieldAsgn's resolveV/resolveFA always resolving a
-- pre-existing path). So it's formalized here as its own invariant, proven to hold at
-- RuntimeConfig.start (CR3/Start.lean) and preserved by every Mutation.lean operation
-- (CR3/*.lean), mirroring the Gc/Model/Preservation/*.lean pattern.
def CR3 (cfg : RuntimeConfig) : Prop :=
  ∀ frame ∈ cfg.stackWithIndex, ∀ frame' ∈ cfg.stackWithIndex,
    frame.index < frame'.index →
    ∀ oid, (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) →
    FrameReferencable cfg frame'.index (Reference.OId oid) →
    FrameReferencable cfg frame.index (Reference.OId oid)

structure ValidReachableConfig (cfg : RuntimeConfig) extends ValidConfig cfg where
  cr3 : CR3 cfg

/-!
report.pdf CR5: "Activity in an active region and frame cannot affect the stack-reachability
of objects within suspended regions."

Unlike CR1-CR4 (`Gc/Reachability/Referencable/{CR1,CR2,CR4}.lean`) and CR3's `ValidConfig`-style
invariant (above), CR5 isn't a property of a single config -- it's a claim about *change over a
run of the operational semantics*: as long as some frame stays suspended (never becomes the
active/last frame) across a sequence of `Mutation.lean` operations, its frame-reachable set never
changes across that whole sequence, no matter how long it is or what happens inside the active
frame/region.

`CR5_step` is the actual report.pdf statement (in `StackReferencable` form, restricted to
references already `FrameReferencable` from the suspended frame -- an unrestricted version is
false, see `cr5_step_of_helper`'s own comment). It's proved via a helper, `CR5_helper_step`, which
is the easier-to-prove-per-operation `FrameReferencable` form (mirrors the `CR3/*.lean`
per-operation pattern already used for CR3) -- see `Gc/Reachability/Referencable/CR5/*.lean` for
the 9 per-operation proofs and their dispatcher.
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
