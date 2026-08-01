import Gc.Reachability.Referencable.Basic
import Gc.Reachability.Referencable.Lemmas

theorem cr5_step_varAsgn (x : VarName) (yf : FieldAccess) : CR5_step (Stmt.varAsgn x yf) := by
  apply cr5_step_of_helper
  intro cfg cfg' vrcfg h i hsusp ref
  obtain ⟨frame, hframe, hidx, hlt⟩ := hsusp
  have vcfg := vrcfg.toValidConfig
  have vcfg' := varAsgn_valid vcfg h
  have hRefStepIff : ∀ a b, RefStep cfg a b ↔ RefStep cfg' a b := by
    intro a b
    unfold RefStep
    rw [varAsgn_corollary_objAt_eq vcfg vcfg' h a]
  obtain ⟨frame0, hframe0, hcase⟩ := varAsgn_cases h
  have stack_eq0 : cfg.stack = cfg.stack.dropLast ++ [frame0] :=
    (List.dropLast_append_getLast? frame0 hframe0).symm
  set frame0W : FrameWithIndex := { frame0 with index := cfg.stack.dropLast.length } with frame0W_def
  have hlenWI : cfg.stackWithIndex.length = cfg.stack.length := by
    unfold RuntimeConfig.stackWithIndex; rw [List.length_mapIdx]
  have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq0]; simp
  have hidlt : i < cfg.stack.dropLast.length := by
    rw [hlenWI, hlen] at hlt
    simpa using hlt
  -- `frame` sits strictly before `frame0W` (the mutated/active frame), so it comes from the
  -- untouched `dropLast` part of the stack -- the same literal record on both sides.
  obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hframe
  have hidxn : frame.index = n := by rw [← hfeq]
  have hnlt : n < cfg.stack.dropLast.length := by
    rw [← hidxn, hidx]
    exact hidlt
  have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
    conv_lhs => rw [stack_eq0]
    rw [List.getElem?_append_left hnlt]
  have hcfgn : cfg.stack[n]? = some frame.toFrame := by
    rw [show frame.toFrame = cfg.stack[n] from by rw [← hfeq]]
    exact List.getElem?_eq_getElem hn
  have hdropn : cfg.stack.dropLast[n]? = some frame.toFrame := by rw [← e1]; exact hcfgn
  have hcfg'n : cfg'.stack[n]? = some frame.toFrame := by
    rcases hcase with
      ⟨oid, rid, region, hyf, hxb, hloc, hridEq, hregion, hcfg'⟩ | ⟨oid, hyf, hxb, hresolve, hcfg'⟩
    · rw [hcfg']; dsimp only; exact hcfgn
    · rw [hcfg']
      dsimp only
      rw [List.getElem?_append_left hnlt]
      exact hdropn
  obtain ⟨h1, heq⟩ := List.getElem?_eq_some_iff.mp hcfg'n
  have hframe' : frame ∈ cfg'.stackWithIndex := by
    unfold RuntimeConfig.stackWithIndex
    exact List.mem_mapIdx.mpr ⟨n, h1, by rw [heq, ← hidxn]⟩
  have hframe0W_mem : frame0W ∈ cfg.stackWithIndex := by
    unfold RuntimeConfig.stackWithIndex
    rw [stack_eq0, List.mapIdx_concat]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hridNe : frame.regionId ≠ frame0.regionId := by
    intro heqrid
    have heqrid' : frame.regionId = frame0W.regionId := heqrid
    have hidxeq := merge_corollary_regionId_unique_index vcfg.s1 hframe hframe0W_mem heqrid'
    rw [hidx] at hidxeq
    exact absurd hidxeq (Nat.ne_of_lt hidlt)
  have hheapEq : cfg'.heap.lookup frame.regionId = cfg.heap.lookup frame.regionId := by
    rcases hcase with
      ⟨oid, rid, region, hyf, hxb, hloc, hridEq, hregion, hcfg'⟩ | ⟨oid, hyf, hxb, hresolve, hcfg'⟩
    · rw [hcfg']
      dsimp only
      rw [hridEq] at hridNe
      exact AList.lookup_insert_ne hridNe
    · rw [hcfg']
  have hfrRootIff : ∀ start, FrameRoot cfg i start ↔ FrameRoot cfg' i start := by
    intro start
    unfold FrameRoot
    constructor
    · rintro (⟨fr1, hfr1, hidx1, var, hlookup1⟩ | ⟨fr1, hfr1, hidx1, region1, hlookup1, hstart⟩)
      · have heq1 : fr1 = frame := swap_corollary_stackWithIndex_index_inj hfr1 hframe (hidx1.trans hidx.symm)
        rw [heq1] at hlookup1
        exact Or.inl ⟨frame, hframe', hidx, var, hlookup1⟩
      · have heq1 : fr1 = frame := swap_corollary_stackWithIndex_index_inj hfr1 hframe (hidx1.trans hidx.symm)
        rw [heq1] at hlookup1
        exact Or.inr ⟨frame, hframe', hidx, region1, by rw [hheapEq]; exact hlookup1, hstart⟩
    · rintro (⟨fr1, hfr1, hidx1, var, hlookup1⟩ | ⟨fr1, hfr1, hidx1, region1, hlookup1, hstart⟩)
      · have heq1 : fr1 = frame := swap_corollary_stackWithIndex_index_inj hfr1 hframe' (hidx1.trans hidx.symm)
        rw [heq1] at hlookup1
        exact Or.inl ⟨frame, hframe, hidx, var, hlookup1⟩
      · have heq1 : fr1 = frame := swap_corollary_stackWithIndex_index_inj hfr1 hframe' (hidx1.trans hidx.symm)
        rw [heq1] at hlookup1
        exact Or.inr ⟨frame, hframe, hidx, region1, by rw [← hheapEq]; exact hlookup1, hstart⟩
  rw [FrameReferencable_iff_reflTransGen, FrameReferencable_iff_reflTransGen]
  constructor
  · rintro ⟨start, hroot, hrtg⟩
    exact ⟨start, (hfrRootIff start).mp hroot, hrtg.mono (fun a b hab => (hRefStepIff a b).mp hab)⟩
  · rintro ⟨start, hroot, hrtg⟩
    exact ⟨start, (hfrRootIff start).mpr hroot, hrtg.mono (fun a b hab => (hRefStepIff a b).mpr hab)⟩
