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

theorem stackReachable_invariant_swap (x : VarName) (yf : FieldAccess) :
    StackReachable_invariant_for_suspended_region_objects (Stmt.swap x yf) := by
  intro cfg cfg' vcfg h hcr3 frame hframeMem hframeSusp oid hloc
  have h' : swap x yf cfg = some cfg' := h
  have hframeLt : frame.index < cfg.stack.dropLast.length := by simpa [RuntimeConfig.stackWithIndex] using hframeSusp
  refine ⟨fun hs => ?_, fun ⟨G, hG, hr⟩ => swap_reach_down vcfg h' hG hr⟩
  obtain ⟨frw, hfrwmem, hidxfrw, -, -⟩ := swap_frame_transport_up h' frame hframeMem
  exact ⟨frw, hfrwmem, hidxfrw ▸ (swap_frame_reachable_iff_of_lt vcfg (swap_valid vcfg h') h' frame hframeLt _).mp
    (FrameReachable_of_StackReachable vcfg hcr3 hframeMem hloc hs)⟩
