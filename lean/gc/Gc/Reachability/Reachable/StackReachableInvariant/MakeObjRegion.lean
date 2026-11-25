module

public import Gc.Model.Types
public import Gc.Model.Helpers
public import Gc.Model.Validity
public import Gc.Model.Mutation.Mutation
public import Gc.Model.Mutation.Stmt
public import Gc.Model.Preservation
public import Gc.Reachability.Reachable.Semantics
public import Gc.Reachability.Reachable.StackReachableInvariant.Def
public import Gc.Reachability.Reachable.Lemmas
public import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.MakeObjRegion

@[expose] public section

theorem stackReachable_invariant_makeObjRegion (x : VarName) :
    StackReachable_invariant_for_suspended_region_objects (Stmt.makeObjRegion x) := by
  intro cfg cfg' vcfg h hFR3 frame hframeMem hframeSusp oid hloc
  obtain ⟨hmem', hfwd, hbwd⟩ := makeObjRegion_suspended_reach vcfg h hFR3 hframeMem hframeSusp hloc
  exact ⟨fun hs => ⟨frame, hmem', hfwd hs⟩, fun ⟨_, _, hr⟩ => hbwd _ hr⟩
