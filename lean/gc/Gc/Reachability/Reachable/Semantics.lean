import Gc.Model.Types
import Gc.Model.Helpers

def ReachableStep (cfg : RuntimeConfig) : Reference → Reference → Prop
  | Reference.RId rid, b =>
    ∃ region, cfg.heap.lookup rid = some region ∧
      region.status = Status.Closed ∧ b = Reference.OId region.bridgeObjectId
  | Reference.OId oid, b =>
    ∃ obj, (do
        let loc ← (Reference.OId oid).loc? cfg
        match loc with
        | Location.Rgn rid => (cfg.heap.lookup rid).bind (fun region => region.objMap.lookup oid)
        | Location.Stk fid =>
          (cfg.stackWithIndex.find? (fun frame => frame.index == fid)).bind
            (fun frame => frame.objMap.lookup oid)) = some obj ∧
      obj.refs.contains b

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

-- The two ways `FrameReachable` can start: a stack variable's value, or the frame's own bridge object.
def FrameRoot (cfg : RuntimeConfig) (fid : Index) (start : Reference) : Prop :=
  (∃ frame ∈ cfg.stackWithIndex, frame.index = fid ∧ ∃ var, frame.varMap.lookup var = some start) ∨
  (∃ frame ∈ cfg.stackWithIndex, frame.index = fid ∧
    ∃ region, cfg.heap.lookup frame.regionId = some region ∧ start = Reference.OId region.bridgeObjectId)

-- `RegionReachable` is exactly reachable from the bridge object by zero or more steps (`bridge`=`refl`, `step`=`tail`).
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

-- Same idea for `FrameReachable`, but with two possible roots (captured by `FrameRoot`) instead of one.
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
