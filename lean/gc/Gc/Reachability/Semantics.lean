import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Mathlib.Logic.Relation

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
        Relation.ReflTransGen (RefStep cfg) (Reference.OId region.bridgeObjectId) ref := by
  constructor
  · intro h
    induction h with
    | bridge hlookup hbridge =>
      subst hbridge
      exact ⟨_, hlookup, Relation.ReflTransGen.refl⟩
    | step hobj hcontains _ ih =>
      obtain ⟨region, hlookup, hrtg⟩ := ih
      exact ⟨region, hlookup, hrtg.tail ⟨_, hobj, hcontains⟩⟩
  · rintro ⟨region, hlookup, hrtg⟩
    induction hrtg with
    | refl => exact RegionReachable.bridge hlookup rfl
    | tail _ hstep ih =>
      obtain ⟨oid, rfl⟩ := hstep.exists_oid_left
      obtain ⟨obj, hobj, hcontains⟩ := hstep
      exact RegionReachable.step hobj hcontains ih

-- Same idea for FrameReachable, except there are two possible roots (a var's value, or
-- the frame's bridge object) instead of one, captured by FrameRoot.
theorem FrameReachable_iff_reflTransGen (cfg : RuntimeConfig) (fid : Index) (ref : Reference) :
    FrameReachable cfg fid ref ↔
      ∃ start, FrameRoot cfg fid start ∧ Relation.ReflTransGen (RefStep cfg) start ref := by
  constructor
  · intro h
    induction h with
    | var hmem hlookup =>
      exact ⟨_, Or.inl ⟨_, hmem, rfl, _, hlookup⟩, Relation.ReflTransGen.refl⟩
    | bridge hmem hlookup hbridge =>
      subst hbridge
      exact ⟨_, Or.inr ⟨_, hmem, rfl, _, hlookup, rfl⟩, Relation.ReflTransGen.refl⟩
    | step hobj hcontains _ ih =>
      obtain ⟨start, hroot, hrtg⟩ := ih
      exact ⟨start, hroot, hrtg.tail ⟨_, hobj, hcontains⟩⟩
  · rintro ⟨start, hroot, hrtg⟩
    induction hrtg with
    | refl =>
      rcases hroot with ⟨frame, hmem, hfid, var, hlookup⟩ | ⟨frame, hmem, hfid, region, hlookup, hstart⟩
      · subst hfid; exact FrameReachable.var hmem hlookup
      · subst hfid; subst hstart; exact FrameReachable.bridge hmem hlookup rfl
    | tail _ hstep ih =>
      obtain ⟨oid, rfl⟩ := hstep.exists_oid_left
      obtain ⟨obj, hobj, hcontains⟩ := hstep
      exact FrameReachable.step hobj hcontains ih
