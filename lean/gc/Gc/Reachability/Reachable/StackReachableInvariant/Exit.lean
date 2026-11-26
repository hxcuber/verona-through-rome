module

public import Gc.Reachability.Reachable.StackReachableInvariant.Def
public import Gc.Reachability.Reachable.Lemmas

@[expose] public section

theorem stackReachable_invariant_exit :
    StackReachable_invariant_for_suspended_region_objects Stmt.exit := by
  intro cfg cfg' vcfg h hcr3 frame hframeMem hframeSusp oid hloc
  have h' : exit cfg = some cfg' := h
  have hs : frame.index < cfg.stack.length - 1 := by simpa [RuntimeConfig.stackWithIndex] using hframeSusp
  obtain ⟨-, hiff⟩ := exit_suspended_reach vcfg h' hframeMem hs
    (by rwa [← exit_loc_eq_of_ne_popped vcfg h' oid (by simp [hloc])])
  refine ⟨fun ⟨G, hG, hr⟩ => ?_, fun ⟨G, hG, hr⟩ => ?_⟩
  · by_cases hGlt : G.index < cfg.stack.length - 1
    · exact ⟨G, exit_frame_mem_up h' hG hGlt, (hiff G hG hGlt).mp hr⟩
    · have hGeq : G.index = cfg.stack.length - 1 := by
        obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp hG
        grind
      exact ⟨frame, exit_frame_mem_up h' hframeMem hs,
        (hiff frame hframeMem hs).mp (hcr3 frame hframeMem G hG (hGeq ▸ hs) oid hloc hr)⟩
  · obtain ⟨hGm, hGlt⟩ := exit_frame_mem_down h' hG
    exact ⟨G, hGm, (hiff G hGm hGlt).mpr hr⟩
