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

-- A root of the last frame of a stack `L ++ [g]` is one of `g`'s vars or the bridge of `g`'s region.
private theorem last_frame_root {c : RuntimeConfig} {L : List Frame} {g : Frame} {s : Reference}
    (h : FrameRoot c L.length s) (hst : c.stack = L ++ [g]) :
    (∃ var, g.varMap.lookup var = some s) ∨
      ∃ region, c.heap.lookup g.regionId = some region ∧ s = Reference.OId region.bridgeObjectId := by
  have key : ∀ fr ∈ c.stackWithIndex, fr.index = L.length → fr = { g with index := L.length } := by
    intro fr hfr hidx
    rw [RuntimeConfig.stackWithIndex, hst, List.mapIdx_concat, List.mem_append, List.mem_singleton] at hfr
    rcases hfr with hfr | rfl
    · obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp hfr
      exact absurd hidx (Nat.ne_of_lt hn)
    · rfl
  rcases h with ⟨fr, hfr, hidx, hv⟩ | ⟨fr, hfr, hidx, hb⟩
  · obtain rfl := key fr hfr hidx
    exact .inl hv
  · obtain rfl := key fr hfr hidx
    exact .inr hb

-- If steps only change at `OId yoid`, which gains at most the already-reachable `newVal`, and every root is already reachable, so is everything.
private theorem escape_of {cfg cfg' : RuntimeConfig} {yoid : ObjectId} {newVal : Reference} {fid : Index}
    (hS : ∀ a, a ≠ Reference.OId yoid → ∀ b, ReachableStep cfg a b ↔ ReachableStep cfg' a b)
    (hY : ∀ c, ReachableStep cfg' (Reference.OId yoid) c → c = newVal ∨ ReachableStep cfg (Reference.OId yoid) c)
    (hN : ∃ E ∈ cfg.stackWithIndex, FrameReachable cfg E.index newVal)
    (hR : ∀ s, FrameRoot cfg' fid s → ∃ E ∈ cfg.stackWithIndex, FrameReachable cfg E.index s)
    {r : Reference} (hr : FrameReachable cfg' fid r) : ∃ E ∈ cfg.stackWithIndex, FrameReachable cfg E.index r := by
  obtain ⟨s, hs, hrtg⟩ := (FrameReachable_iff_reflTransGen _ _ _).mp hr
  clear hr
  induction hrtg with
  | refl => exact hR s hs
  | @tail a b _ hstep ih =>
    obtain ⟨E, hE, ih⟩ := ih
    by_cases ha : a = Reference.OId yoid
    · subst ha
      rcases hY _ hstep with rfl | hstep
      · exact hN
      · exact ⟨E, hE, .step hstep ih⟩
    · exact ⟨E, hE, .step ((hS a ha b).mpr hstep) ih⟩

-- Anything reachable from the mutated (last) frame after a swap was already reachable from some frame before it.
private theorem swap_escape {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg) (h : swap x yf cfg = some cfg')
    {r : Reference} (hr : FrameReachable cfg' cfg.stack.dropLast.length r) :
    ∃ E ∈ cfg.stackWithIndex, FrameReachable cfg E.index r := by
  obtain ⟨f0, hf0, yRef, -, yRefLoc, hyrl, yfRef, hyf, _, -, hcase⟩ := swap_cases h
  have hmem0 := List.mem_of_getLast? hf0
  have hst := (stack_eq_of_stackWithIndex_getLast? hf0).1
  have hvar : ∀ var s, (f0.varMap.insert x yfRef).lookup var = some s →
      ∃ E ∈ cfg.stackWithIndex, FrameReachable cfg E.index s := by
    intro var s hv
    by_cases hvx : var = x
    · subst hvx
      rw [AList.lookup_insert, Option.some_inj] at hv
      exact hv ▸ resolveFA_frameReach hyf
    · rw [AList.lookup_insert_ne hvx] at hv
      exact ⟨f0, hmem0, .var hmem0 hv⟩
  rcases hcase with ⟨yoid, xRef, obj, -, rfl, rfl, hxr, hobj, rfl⟩ |
    ⟨yoid, rid, region, obj, xoid, xrid, -, rfl, rfl, rfl, hregion, hobj, hxr, -, -, hstatus, rfl⟩ |
    ⟨yoid, rid, region, obj, xrid, -, rfl, rfl, rfl, hregion, hobj, hxr, hstatus, rfl⟩ |
    ⟨yoid, yrid, yfoid, yfrid, region, obj, -, rfl, rfl, rfl, -, rfl, -, hregion, hobj, rfl⟩
  · refine escape_of (swap_stack_step_iff_of_ne hf0 hobj rfl)
      (fun _ hc => swap_stack_yoid_step_of_ne hf0 hyrl hobj rfl hc) ⟨f0, hmem0, .var hmem0 hxr⟩ (fun s hs => ?_) hr
    rcases last_frame_root hs rfl with ⟨var, hv⟩ | ⟨rg, hlk, rfl⟩
    · exact hvar var s hv
    · exact ⟨f0, hmem0, .bridge hmem0 hlk rfl⟩
  all_goals first
    | obtain ⟨_, hlk0, hstatus⟩ := l2_of_stackWithIndex vcfg hmem0
      obtain rfl := Option.some_inj.mp (hregion.symm.trans hlk0)
      refine escape_of (swap_bridge_step_iff_of_ne vcfg hregion hobj hstatus rfl)
        (fun _ hc => swap_bridge_yoid_step_of_ne vcfg hregion hobj hyrl hc) ⟨f0, hmem0, .bridge hmem0 hregion rfl⟩
        (fun s hs => ?_) hr
      rcases last_frame_root hs hst with ⟨var, hv⟩ | ⟨rg, hlk, rfl⟩
      · exact ⟨f0, hmem0, .var hmem0 hv⟩
      · simp only [AList.lookup_insert, Option.some_inj] at hlk
        subst hlk
        exact resolveFA_frameReach hyf
    | refine escape_of (swap_region_stack_step_iff_of_ne vcfg hf0 hregion hobj hstatus rfl)
        (fun _ hc => swap_region_stack_yoid_step_of_ne vcfg hf0 hregion hobj hyrl hc) ⟨f0, hmem0, .var hmem0 hxr⟩
        (fun s hs => ?_) hr
      rcases last_frame_root hs rfl with ⟨var, hv⟩ | ⟨rg, hlk, rfl⟩
      · exact hvar var s hv
      · simp only [AList.lookup_insert, Option.some_inj] at hlk
        subst hlk
        exact ⟨f0, hmem0, .bridge hmem0 hregion rfl⟩

-- Every frame of `cfg` sits at or below the last frame's index.
private theorem index_le_last {cfg : RuntimeConfig} {frame0 fr : FrameWithIndex}
    (hframe0 : cfg.stackWithIndex.getLast? = some frame0) (hfr : fr ∈ cfg.stackWithIndex) : fr.index ≤ frame0.index := by
  have hidx := (stack_eq_of_stackWithIndex_getLast? hframe0).2
  obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp hfr
  rw [List.length_dropLast] at hidx
  exact hidx ▸ Nat.le_sub_one_of_lt hn

theorem stackReachable_invariant_swap (x : VarName) (yf : FieldAccess) :
    StackReachable_invariant_for_suspended_region_objects (Stmt.swap x yf) := by
  intro cfg cfg' vcfg h hcr3 frame hframeMem hframeSusp oid hloc
  have h' : swap x yf cfg = some cfg' := h
  have vcfg' := swap_valid vcfg h'
  obtain ⟨frame0, hframe0, -⟩ := swap_cases h'
  have hidx0 := (stack_eq_of_stackWithIndex_getLast? hframe0).2
  have hframeLt : frame.index < cfg.stack.dropLast.length := by
    simpa [RuntimeConfig.stackWithIndex] using hframeSusp
  obtain ⟨regionF, hlkF, hopenF⟩ := l2_of_stackWithIndex vcfg hframeMem
  -- Collapses a `cfg`-side witness at or beyond `frame`'s index back to `frame`.
  have finish : (∃ E ∈ cfg.stackWithIndex, FrameReachable cfg E.index (Reference.OId oid)) →
      FrameReachable cfg frame.index (Reference.OId oid) := by
    rintro ⟨E, hEmem, hEreach⟩
    rcases (region_container_confined vcfg hlkF hopenF hframeMem rfl hloc hEreach).eq_or_lt with heqE | hltE
    · exact heqE ▸ hEreach
    · exact hcr3 frame hframeMem E hEmem hltE oid hloc hEreach
  constructor
  · rintro hG
    obtain ⟨frw, hfrwmem, hidxfrw, -, -⟩ := swap_frame_transport_up h' frame hframeMem
    exact ⟨frw, hfrwmem, hidxfrw ▸ (swap_frame_reachable_iff_of_lt vcfg vcfg' h' frame hframeLt _).mp (finish hG)⟩
  · rintro ⟨G, hGmem, hGreach⟩
    refine ⟨frame, hframeMem, finish ?_⟩
    by_cases hGeq : G.index = frame0.index
    · exact swap_escape vcfg h' (hidx0 ▸ hGeq ▸ hGreach)
    · obtain ⟨Gd, hGdmem, hidxGd, -, -⟩ := swap_frame_transport_down h' G hGmem
      have hGLt : G.index < cfg.stack.dropLast.length :=
        hidx0 ▸ lt_of_le_of_ne (hidxGd ▸ index_le_last hframe0 hGdmem) hGeq
      exact ⟨Gd, hGdmem, hidxGd ▸ (swap_frame_reachable_iff_of_lt vcfg vcfg' h' G hGLt _).mpr hGreach⟩
