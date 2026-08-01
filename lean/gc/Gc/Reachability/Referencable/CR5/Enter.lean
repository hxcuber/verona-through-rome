import Gc.Reachability.Referencable.Basic
import Gc.Reachability.Referencable.Lemmas

theorem cr5_step_enter (xf : FieldAccess) (a : VarName) : CR5_step (Stmt.enter xf a) := by
  apply cr5_step_of_helper
  intro cfg cfg' vrcfg h i hsusp ref
  obtain ⟨frame0, hframe0, hidx, _⟩ := hsusp
  subst hidx
  have vcfg := vrcfg.toValidConfig
  have vcfg' := enter_valid vcfg h
  exact enter_corollary_frameReferencable_iff vcfg vcfg' h frame0 hframe0 ref

