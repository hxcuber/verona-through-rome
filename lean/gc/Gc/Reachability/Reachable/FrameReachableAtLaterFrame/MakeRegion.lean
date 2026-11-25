module

public import Gc.Model.Types
public import Gc.Model.Helpers
public import Gc.Model.Validity
public import Gc.Model.Mutation.Mutation
public import Gc.Model.Mutation.Stmt
public import Gc.Model.Preservation
public import Gc.Reachability.Reachable.Semantics
public import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.Def
public import Gc.Reachability.Reachable.Lemmas

@[expose] public section

theorem frameReachableAtLaterFrame_step_makeRegion (x : VarName) :
    FrameReachableAtLaterFrame_step (Stmt.makeRegion x) := by
  intro cfg cfg' vcfg h hFR3 frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  have h' : makeRegion x cfg = some cfg' := h
  have hle : frame'.index ≤ cfg.stack.length - 1 := by
    rcases makeRegion_frame_cases h' hframe'Mem with ⟨-, h1⟩ | ⟨-, -, -, -, -, -, h1⟩
    · exact h1.le
    · simp [h1]
  obtain ⟨hF, hFlt⟩ := (makeRegion_frame_cases h' hframeMem).resolve_right
    fun ⟨_, _, _, _, _, _, h1⟩ => by simp at h1; exact absurd hle (Nat.not_le.mpr (h1 ▸ hlt))
  have hne : oid ≠ cfg.freshObjectId := by
    rintro rfl
    simp only [makeRegion_corollary_loc_fresh h', Option.some_inj, Location.Rgn.injEq] at hloc
    exact frame_regionId_ne_fresh vcfg hF hloc.symm
  rw [← makeRegion_corollary_loc_eq vcfg h' oid hne] at hloc
  have hsr := makeRegion_suspended_reach vcfg h' hFR3 hF (by simpa [RuntimeConfig.stackWithIndex] using hFlt) hloc
  exact hsr.2.1 (hsr.2.2 _ hreach)
