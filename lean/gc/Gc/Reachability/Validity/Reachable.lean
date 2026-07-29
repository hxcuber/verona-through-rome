import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Reachability.Semantics

-- report.pdf CR3: if an object o lives in a (suspended) region R with associated frame F,
-- and o is frame-reachable from some later frame F', then o is frame-reachable from F itself.
-- "suspended" doesn't need to be stated separately: frame.index < frame'.index with both
-- frame/frame' on the stack already forces F to not be the active/last frame.
--
-- Unlike L1/H1-H3/S1-S3/HS1-HS2 (Gc/Model/Validity.lean), CR3 is not provable from a single
-- ValidConfig snapshot alone -- it's fundamentally a fact about how references come to exist
-- via the operational semantics (varAsgn/fieldAsgn's resolveV/resolveFA always resolving a
-- pre-existing path). So it's formalized here as its own invariant, proven to hold at
-- RuntimeConfig.start (Start.lean) and preserved by every Mutation.lean operation
-- (Preservation/*.lean), mirroring the Gc/Model/Preservation/*.lean pattern.
def CR3 (cfg : RuntimeConfig) : Prop :=
  ∀ frame ∈ cfg.stackWithIndex, ∀ frame' ∈ cfg.stackWithIndex,
    frame.index < frame'.index →
    ∀ oid, (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) →
    FrameReferencable cfg frame'.index (Reference.OId oid) →
    FrameReferencable cfg frame.index (Reference.OId oid)

structure ValidReachableConfig (cfg : RuntimeConfig) extends ValidConfig cfg where
  cr3 : CR3 cfg
