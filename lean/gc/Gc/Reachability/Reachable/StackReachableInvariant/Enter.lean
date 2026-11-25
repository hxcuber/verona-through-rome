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

@[expose] public section

theorem stackReachable_invariant_enter (xf : FieldAccess) (bridgeVar : VarName) :
    StackReachable_invariant_for_suspended_region_objects (Stmt.enter xf bridgeVar) := by
  intro cfg cfg' vcfg h _ frame hframeMem _ oid hloc
  have h' : enter xf bridgeVar cfg = some cfg' := h
  obtain ⟨_, _, -, -, -, hcfg'⟩ := enter_cases h'
  obtain ⟨hiff, hnew⟩ := enter_suspended_reach vcfg h' hframeMem hloc
  refine ⟨fun ⟨G, hG, hr⟩ => ⟨G, enter_frame_mem_up h' hG, (hiff G hG).mp hr⟩, fun ⟨G, hG, hr⟩ => ?_⟩
  rcases enter_frame_cases hcfg' hG with ⟨hGm, -⟩ | ⟨-, -, -, -, hi⟩
  · exact ⟨G, hGm, (hiff G hGm).mpr hr⟩
  · exact absurd (hi ▸ hr) hnew
