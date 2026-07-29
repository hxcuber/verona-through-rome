import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Reachability.Semantics

structure Path where
  refs : List Reference

-- a path is valid when consecutive references are linked by RefStep, mirroring the
-- `step` constructor of RegionReachable/FrameReachable in Semantics.lean
def ValidPath (cfg : RuntimeConfig) (path : Path) : Prop :=
  path.refs.IsChain (RefStep cfg)
