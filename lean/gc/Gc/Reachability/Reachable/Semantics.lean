import Gc.Model.Types
import Gc.Model.Helpers

def Reference.deref? (cfg : RuntimeConfig) : Reference → Option Object
  | Reference.RId rid => do
    let region ← cfg.heap.lookup rid
    guard (region.status == Status.Closed)
    region.objMap.lookup region.bridgeObjectId
  | Reference.OId oid => do
    let loc ← (Reference.OId oid).loc? cfg
    match loc with
    | Location.Rgn rid =>
      let region ← cfg.heap.lookup rid
      region.objMap.lookup oid
    | Location.Stk fid =>
      let frame ← cfg.stackWithIndex.find? (fun frame => frame.index == fid)
      frame.objMap.lookup oid

def ReachableStep (cfg : RuntimeConfig) (a b : Reference) : Prop :=
  ∃ obj, a.deref? cfg = some obj ∧ obj.refs.contains b

inductive RegionReachable : RuntimeConfig → RegionId → Reference → Prop where
| bridge : cfg.heap.lookup rid = some region →
    region.bridgeObjectId = oid →
    RegionReachable cfg rid (Reference.OId oid)
| step : ReachableStep cfg ref' ref →
    RegionReachable cfg rid ref' →
    RegionReachable cfg rid ref

inductive FrameReachable : RuntimeConfig → Index → Reference → Prop where
| var : frame ∈ cfg.stackWithIndex →
    frame.varMap.lookup var = some ref →
    FrameReachable cfg frame.index ref
| bridge : frame ∈ cfg.stackWithIndex →
    cfg.heap.lookup frame.regionId = some region →
    region.bridgeObjectId = oid →
    FrameReachable cfg frame.index (Reference.OId oid)
| step : ReachableStep cfg ref' ref →
    FrameReachable cfg fid ref' →
    FrameReachable cfg fid ref

def StackReachable (cfg : RuntimeConfig) (ref : Reference) : Prop :=
    ∃ frame ∈ cfg.stackWithIndex, FrameReachable cfg frame.index ref

-- the two ways FrameReachable can start a path: from a stack variable's value, or from
-- the frame's own region's bridge object
def FrameRoot (cfg : RuntimeConfig) (fid : Index) (start : Reference) : Prop :=
  (∃ frame ∈ cfg.stackWithIndex, frame.index = fid ∧ ∃ var, frame.varMap.lookup var = some start) ∨
  (∃ frame ∈ cfg.stackWithIndex, frame.index = fid ∧
    ∃ region, cfg.heap.lookup frame.regionId = some region ∧ start = Reference.OId region.bridgeObjectId)

-- RegionReachable is exactly "reachable from the bridge object by zero or more RefSteps" --
-- `bridge` is the `refl` case and `step` is the `tail` case, so this is a straight
-- induction, not a change to the definition itself.
theorem RegionReachable_iff_reflTransGen (cfg : RuntimeConfig) (rid : RegionId) (ref : Reference) :
    RegionReachable cfg rid ref ↔
      ∃ region, cfg.heap.lookup rid = some region ∧
        Relation.ReflTransGen (ReachableStep cfg) (Reference.OId region.bridgeObjectId) ref := by
  constructor
  · intro h
    induction h with
    | bridge hlookup hbridge =>
      subst hbridge
      exact ⟨_, hlookup, Relation.ReflTransGen.refl⟩
    | step hstep _ ih =>
      obtain ⟨region, hlookup, hrtg⟩ := ih
      exact ⟨region, hlookup, hrtg.tail hstep⟩
  · rintro ⟨region, hlookup, hrtg⟩
    induction hrtg with
    | refl => exact RegionReachable.bridge hlookup rfl
    | tail _ hstep ih =>
      exact RegionReachable.step hstep ih

-- Same idea for FrameReachable, except there are two possible roots (a var's value, or
-- the frame's bridge object) instead of one, captured by FrameRoot.
theorem FrameReachable_iff_reflTransGen (cfg : RuntimeConfig) (fid : Index) (ref : Reference) :
    FrameReachable cfg fid ref ↔
      ∃ start, FrameRoot cfg fid start ∧ Relation.ReflTransGen (ReachableStep cfg) start ref := by
  constructor
  · intro h
    induction h with
    | var hmem hlookup =>
      exact ⟨_, Or.inl ⟨_, hmem, rfl, _, hlookup⟩, Relation.ReflTransGen.refl⟩
    | bridge hmem hlookup hbridge =>
      subst hbridge
      exact ⟨_, Or.inr ⟨_, hmem, rfl, _, hlookup, rfl⟩, Relation.ReflTransGen.refl⟩
    | step hstep _ ih =>
      obtain ⟨region, hlookup, hrtg⟩ := ih
      exact ⟨region, hlookup, hrtg.tail hstep⟩
  · rintro ⟨start, hroot, hrtg⟩
    induction hrtg with
    | refl =>
      rcases hroot with ⟨frame, hmem, hfid, var, hlookup⟩ | ⟨frame, hmem, hfid, region, hlookup, hstart⟩
      · subst hfid; exact FrameReachable.var hmem hlookup
      · subst hfid; subst hstart; exact FrameReachable.bridge hmem hlookup rfl
    | tail _ hstep ih =>
      exact FrameReachable.step hstep ih
