import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity

-- what does it mean for an object to be reachable in a region?
inductive RegionReachable : RuntimeConfig → RegionId → Reference → Prop where
-- the object is the bridge object
| bridge : cfg.heap.lookup rid = some region →
    region.bridgeObjectId = oid →
    RegionReachable cfg rid (Reference.OId oid)
-- the object is reachable from a reachable object inside the region
| step : cfg.heap.lookup rid = some region →
    -- we should have a lemma that just says if an object is reachable then
    -- it is in the region
    region.objMap.lookup oid = some obj →
    obj.refs.contains ref →
    RegionReachable cfg rid (Reference.OId oid) →
    RegionReachable cfg rid ref

-- what does it mean for an object to be reachable from the stack?
inductive StackReachable : RuntimeConfig → Reference → Prop where
-- the object is reachable from a variable in the stack
| var : frame ∈ cfg.stackWithIndex →
    frame.varMap.lookup var = some ref →
    StackReachable cfg ref
-- the object is referenced by a reachable object from the stack
| stack_step : frame ∈ cfg.stackWithIndex →
    frame.objMap.lookup oid = some obj →
    obj.refs.contains ref →
    StackReachable cfg (Reference.OId oid) →
    StackReachable cfg ref
-- the object is referenced by a reachable object from a region in the stack
| region_step : frame ∈ cfg.stackWithIndex →
    cfg.heap.lookup frame.regionId = some region →
    region.objMap.lookup oid = some obj →
    obj.refs.contains ref →
    StackReachable cfg (Reference.OId oid) →
    StackReachable cfg ref

-- what does it mean for an object to be reachable from the stack?
inductive FrameReachable : RuntimeConfig → Index → Reference → Prop where
-- the object is reachable from a variable in the stack
| var : frame ∈ cfg.stackWithIndex →
    frame.varMap.lookup var = some ref →
    FrameReachable cfg frame.index ref
-- the object is referenced by a reachable object from the stack
| stack_step : frame ∈ cfg.stackWithIndex →
    frame.objMap.lookup oid = some obj →
    obj.refs.contains ref →
    FrameReachable cfg fid (Reference.OId oid) →
    FrameReachable cfg fid ref
-- the object is referenced by a reachable object from a region in the stack
| region_step : frame ∈ cfg.stackWithIndex →
    cfg.heap.lookup frame.regionId = some region →
    region.objMap.lookup oid = some obj →
    obj.refs.contains ref →
    FrameReachable cfg fid (Reference.OId oid') →
    FrameReachable cfg fid ref

-- distinguish between frame reachability and stack reachability