import Gc.Model.Types
import Gc.Model.Helpers

structure Path where
  refs : List Reference

-- `a` steps to `b` when `b` is a field value of the object `a` currently resolves to
def RefStep (cfg : RuntimeConfig) (a b : Reference) : Prop :=
  ∃ obj, a.objAt? cfg = some obj ∧ obj.refs.contains b

-- a path is valid when consecutive references are linked by RefStep, mirroring the
-- `step` constructor of RegionReachable/FrameReachable in Semantics.lean
def ValidPath (cfg : RuntimeConfig) (path : Path) : Prop :=
  path.refs.IsChain (RefStep cfg)
