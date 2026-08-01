import Gc.Reachability.Referencable.Basic
import Gc.Reachability.Referencable.Lemmas

theorem cr5_step_exit : CR5_step Stmt.exit := by
  apply cr5_step_of_helper
  intro cfg cfg' vrcfg h i hsusp ref
  obtain ⟨frame, hframe, hidx, hlt⟩ := hsusp
  have vcfg := vrcfg.toValidConfig
  have vcfg' := exit_valid vcfg h
  obtain ⟨poppedFrame, region, hlen2, hlast, hlookupPopped, hopenPopped, hcfg'⟩ := exit_cases h
  have hstackeq := exit_corollary_stackWithIndex_eq hlast
  have hlenWI : cfg.stackWithIndex.length = cfg.stack.length := by
    unfold RuntimeConfig.stackWithIndex; rw [List.length_mapIdx]
  have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by
    have stack_eq : cfg.stack = cfg.stack.dropLast ++ [poppedFrame] :=
      (List.dropLast_append_getLast? poppedFrame hlast).symm
    rw [stack_eq]; simp
  have hidlt : i < cfg.stack.dropLast.length := by
    rw [hlenWI, hlen] at hlt
    simpa using hlt
  rw [hstackeq] at hframe
  rw [List.mem_append] at hframe
  rcases hframe with hold | hpop
  · have hframe0' : frame ∈ cfg'.stackWithIndex := by
      rw [hcfg']
      unfold RuntimeConfig.stackWithIndex
      dsimp only
      exact hold
    subst hidx
    exact exit_corollary_frameReferencable_iff vcfg vcfg' h frame hframe0' ref
  · exfalso
    rw [List.mem_singleton] at hpop
    rw [hpop] at hidx
    dsimp only at hidx
    rw [hidx] at hidlt
    exact lt_irrefl _ hidlt

