import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Reachability.Semantics

-- Activity in an active region does not affect liveness in suspended regions
-- What if a suspended region contains an object that is reachable from the stack,
-- but not region reachable?
-- the stack reachable objects that aren't region reachable are dead once we exit
-- the region, so...

-- We can calculate the region reachability of objects within a suspended region,
-- but i don't think we can garbage collect based on region reachability alone,
-- since some stack variables of the earlier frames may point to objects in the
-- suspended region that are not connected to the bridge obejct

-- Perhaps we need a weaker (?) notion of stack reachability, where we only consider
-- the frames of suspended regions, or the stack up to a certain fid

-- from a newer frame, we can make a reference to an object in a suspended region,
-- but we may not mutate that object in any way
-- so we only care about the reachability of objects in the suspended region from
-- the frame associated with it
def suspended_regions_maintain_region_reachability (cfg cfg' : RuntimeConfig) : Prop :=
  ∀ rid ∈ cfg.stackWithIndex.dropLast.map (·.regionId),
  ∀ ref, RegionReachable cfg rid ref ↔ RegionReachable cfg' rid ref

def suspended_regions_maintain_frame_reachability (cfg cfg' : RuntimeConfig) : Prop :=
  ∀ fid < cfg.stackWithIndex.length - 1,
  ∀ ref, FrameReachable cfg fid ref ↔ FrameReachable cfg' fid ref
