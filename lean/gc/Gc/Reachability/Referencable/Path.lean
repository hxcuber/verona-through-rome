import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Reachability.Referencable.Semantics

structure Path where
  refs : List Reference

-- a path is valid when consecutive references are linked by RefStep, mirroring the
-- `step` constructor of RegionReferencable/FrameReferencable in Semantics.lean
def ValidPath (cfg : RuntimeConfig) (path : Path) : Prop :=
  path.refs.IsChain (RefStep cfg)
