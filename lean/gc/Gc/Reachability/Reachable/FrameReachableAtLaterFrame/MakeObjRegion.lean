module

public import Gc.Reachability.Reachable.Lemmas

@[expose] public section

theorem frameReachableAtLaterFrame_step_makeObjRegion (x : VarName) :
    FrameReachableAtLaterFrame_step (Stmt.makeObjRegion x) := by
  intro cfg cfg' vcfg h hFR3 frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  have h' : makeObjRegion x cfg = some cfg' := h
  have hle : frame'.index ≤ cfg.stack.length - 1 := by
    rcases makeObjRegion_frame_cases h' hframe'Mem with ⟨-, h1⟩ | ⟨-, -, -, -, -, -, h1⟩
    · exact h1.le
    · simp [h1]
  obtain ⟨hF, hFlt⟩ := (makeObjRegion_frame_cases h' hframeMem).resolve_right
    fun ⟨_, _, _, _, _, _, h1⟩ => by simp at h1; exact absurd hle (Nat.not_le.mpr (h1 ▸ hlt))
  have hne : oid ≠ cfg.freshObjectId := by
    rintro rfl
    obtain ⟨L, hL, hlocF⟩ := makeObjRegion_corollary_loc_fresh vcfg h'
    simp only [hlocF, Option.some_inj, Location.Rgn.injEq] at hloc
    exact regionId_ne_last_of_suspended vcfg hF hFlt hL hloc.symm
  rw [← makeObjRegion_corollary_loc_eq vcfg h' oid hne] at hloc
  have hsr := makeObjRegion_suspended_reach vcfg h' hFR3 hF (by simpa [RuntimeConfig.stackWithIndex] using hFlt) hloc
  exact hsr.2.1 (hsr.2.2 _ hreach)
