import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity

-- what does it mean for an object to be reachable in a region?
inductive RegionReachable : RuntimeConfig → RegionId → Reference → Prop where
-- the object is the bridge object
| bridge : cfg.heap.lookup rid = some region →
    region.bridgeObjectId = oid →
    RegionReachable cfg rid (Reference.OId oid)
-- wherever the reachable object actually lives (region or frame, doesn't matter here)
| step : (Reference.OId oid).objAt? cfg = some obj →
    obj.refs.contains ref →
    RegionReachable cfg rid (Reference.OId oid) →
    RegionReachable cfg rid ref

-- what does it mean for an object to be reachable from a frame?
inductive FrameReachable : RuntimeConfig → Index → Reference → Prop where
-- the object is reachable from a variable in the stack
| var : frame ∈ cfg.stackWithIndex →
    frame.varMap.lookup var = some ref →
    FrameReachable cfg frame.index ref
| bridge : frame ∈ cfg.stackWithIndex →
    cfg.heap.lookup frame.regionId = some region →
    region.bridgeObjectId = oid →
    FrameReachable cfg frame.index (Reference.OId oid)
-- the object is referenced by a reachable object, wherever that object actually lives
| step : (Reference.OId oid).objAt? cfg = some obj →
    obj.refs.contains ref →
    FrameReachable cfg fid (Reference.OId oid) →
    FrameReachable cfg fid ref

def StackReachable (cfg : RuntimeConfig) (ref : Reference) : Prop :=
    ∃ frame ∈ cfg.stackWithIndex, FrameReachable cfg frame.index ref
