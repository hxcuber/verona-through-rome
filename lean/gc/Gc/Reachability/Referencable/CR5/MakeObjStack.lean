import Gc.Reachability.Referencable.Basic
import Gc.Reachability.Referencable.Lemmas

theorem cr5_step_makeObjStack (x : VarName) : CR5_step (Stmt.makeObjStack x) := by
  apply cr5_step_of_helper
  intro cfg cfg' vrcfg h i hsusp ref
  have vcfg := vrcfg.toValidConfig
  have vcfg' := makeObjStack_valid vcfg h
  obtain ⟨_, _, _, hlt⟩ := hsusp
  obtain ⟨frame1, hframe1, hcfg'⟩ := makeObjStack_cases h
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame1] :=
    (List.dropLast_append_getLast? frame1 hframe1).symm
  have hlenWI : cfg.stackWithIndex.length = cfg.stack.length := by
    unfold RuntimeConfig.stackWithIndex; rw [List.length_mapIdx]
  have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq]; simp
  have hidlt : i < cfg.stack.dropLast.length := by
    rw [hlenWI, hlen] at hlt
    simpa using hlt
  exact makeObjStack_corollary_frameReferencable_iff_of_lt vcfg vcfg' h hidlt ref

