import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Mutation.Mutation
import Gc.Model.Preservation
import Gc.Reachability.Reachable.Semantics

-- Re-derived helper lemmas for `Gc/Reachability/Reachable/Scratch.lean`'s
-- `stackReachable_invariant_*` proofs. Deliberately independent of
-- `Gc.Reachability.Referencable` -- anything needed from that layer (including a
-- CR3-style "later frame reaching into an earlier frame's region is already reachable
-- from that frame" fact) is re-derived fresh here against `ReachableStep`/`deref?`
-- instead of `RefStep`/`objAt?`.
