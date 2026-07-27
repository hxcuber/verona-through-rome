Verona through Rome
---
My final year project from Imperial, 25-26.

Major changes from the report
---
- `HS1` - a new invariant stating that any object reference stored in any variable mapping in the configuration refers to an existing object (no dangling object references).

- `makeRegion` - regions have a completely separate counter to objects. this decoupling means that we dont run into the following case: object 99 and region 99 exists, object 99 gets dealloc'd, we create a new region, and then its new regionId is again 99, which already exists. this change also then introduces a couple of new helper functions for getting regionIds.

- `HS2` - same as `HS1`, but for region references.

- updated reachability semantic definitions to more accurately reflect what was said in the report - in particular generalising both region and frame reachability (`RegionReachable`, `FrameReachable`), and then truly matching stack reachability (`StackReachable`) to its definition found in the report.

- `CR3` is actually a valid configuration invariant that should be preserved with every operation, not just a corollary from the reachability statements. Deciding on what to do with it...
