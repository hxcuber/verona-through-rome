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

theorem frameReachableAtLaterFrame_step_makeObjStack (x : VarName) :
    FrameReachableAtLaterFrame_step (Stmt.makeObjStack x) := by
  intro cfg cfg' vcfg h hFR3 frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  have h' : makeObjStack x cfg = some cfg' := h
  obtain ⟨L, hL, hcfg'⟩ := makeObjStack_cases h'
  have hle : frame'.index ≤ cfg.stack.length - 1 := by
    rcases makeObjStack_frame_cases hL hcfg' hframe'Mem with ⟨-, h1⟩ | ⟨-, -, -, -, h1⟩
    · exact h1.le
    · simp [h1]
  obtain ⟨hF, hFlt⟩ := (makeObjStack_frame_cases hL hcfg' hframeMem).resolve_right
    fun ⟨_, _, _, _, h1⟩ => by simp at h1; exact absurd hle (Nat.not_le.mpr (h1 ▸ hlt))
  have hne : oid ≠ cfg.freshObjectId := by
    rintro rfl
    obtain ⟨r, hl, hm⟩ := (oid_loc_rgn_iff_in_heap (makeObjStack_valid vcfg h')).mp hloc
    subst hcfg'
    exact cfg.freshObjectId_not_mem (List.mem_append_right _ (heap_objectIds_of_mem (AList.lookup_mem_entries hl) hm))
  rw [← makeObjStack_loc_eq_of_ne h' hne] at hloc
  have hsr := makeObjStack_suspended_reach vcfg h' hFR3 hF (by simpa [RuntimeConfig.stackWithIndex] using hFlt) hloc
  exact hsr.2.1 (hsr.2.2 _ hreach)
