module

public import Gc.Reachability.Reachable.StackReachableInvariant.Def
public import Gc.Reachability.Reachable.Lemmas

@[expose] public section

theorem stackReachable_invariant_makeRegion (x : VarName) :
    StackReachable_invariant_for_suspended_region_objects (Stmt.makeRegion x) := by
  intro cfg cfg' vcfg h hFR3 frame hframeMem hframeSusp oid hloc
  obtain ⟨hmem', hfwd, hbwd⟩ := makeRegion_suspended_reach vcfg h hFR3 hframeMem hframeSusp hloc
  exact ⟨fun hs => ⟨frame, hmem', hfwd hs⟩, fun ⟨_, _, hr⟩ => hbwd _ hr⟩
