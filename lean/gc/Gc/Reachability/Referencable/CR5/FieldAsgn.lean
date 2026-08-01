import Gc.Reachability.Referencable.Basic
import Gc.Reachability.Referencable.Lemmas

theorem cr5_step_fieldAsgn (xf : FieldAccess) (y : VarName) : CR5_step (Stmt.fieldAsgn xf y) := by
  apply cr5_step_of_helper
  intro cfg cfg' vrcfg h i hsusp ref
  obtain ⟨frame, hframe, hidx, hlt⟩ := hsusp
  have vcfg := vrcfg.toValidConfig
  have vcfg' := fieldAsgn_valid vcfg h
  obtain ⟨frame0, hframe0, _⟩ := fieldAsgn_cases h
  obtain ⟨stack_eq0, hidx00⟩ := fieldAsgn_corollary_stack_eq hframe0
  have hlenWI : cfg.stackWithIndex.length = cfg.stack.length := by
    unfold RuntimeConfig.stackWithIndex; rw [List.length_mapIdx]
  have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq0]; simp
  have hidlt : i < cfg.stack.dropLast.length := by
    rw [hlenWI, hlen] at hlt
    simpa using hlt
  have hframelt : frame.index < cfg.stack.dropLast.length := by rw [hidx]; exact hidlt
  have hres := fieldAsgn_corollary_frameReferencable_iff_of_lt vcfg vcfg' h frame hframelt ref
  rwa [hidx] at hres

