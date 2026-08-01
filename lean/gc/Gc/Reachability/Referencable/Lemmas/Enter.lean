import Gc.Model.Mutation.Enter
import Gc.Model.Preservation.Enter
import Gc.Model.Preservation.Common
import Gc.Reachability.Referencable.Basic
import Gc.Reachability.Referencable.Lemmas.Common


-- Old (already-on-stack) frames' own region can never be the entered region: L2 says every
-- on-stack frame's own region is already Open, but `enter` requires the entered region Closed.
theorem enter_corollary_regionId_ne (vcfg : ValidConfig cfg)
    (rid : RegionId) (region : Region) (hclosed : region.status = Status.Closed)
    (hlookup : cfg.heap.lookup rid = some region) :
    ∀ frame ∈ cfg.stackWithIndex, frame.regionId ≠ rid := by
  intro frame hframe heq
  obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hframe
  have hmemstack : cfg.stack[n] ∈ cfg.stack := List.getElem_mem hn
  obtain ⟨region', hlookup', hopen'⟩ := vcfg.l2 cfg.stack[n] hmemstack
  have hregionId_eq : cfg.stack[n].regionId = rid := by
    rw [← hfeq] at heq
    dsimp only at heq
    exact heq
  rw [hregionId_eq, hlookup] at hlookup'
  injection hlookup' with hregion_eq
  rw [← hregion_eq, hclosed] at hopen'
  exact absurd hopen' (by decide)

theorem enter_corollary_frame_mem (h : enter xf a cfg = some cfg') :
    ∀ frame ∈ cfg.stackWithIndex, frame ∈ cfg'.stackWithIndex := by
  intro frame hframe
  obtain ⟨rid, region, _, _, _, hcfg'⟩ := enter_cases h
  subst hcfg'
  unfold RuntimeConfig.stackWithIndex at hframe ⊢
  dsimp only
  rw [List.mapIdx_concat]
  exact List.mem_append_left _ hframe

theorem enter_corollary_objAt_eq (vcfg : ValidConfig cfg) (vcfg' : ValidConfig cfg')
    (h : enter xf a cfg = some cfg') :
    ∀ oid, (Reference.OId oid).objAt? cfg = (Reference.OId oid).objAt? cfg' := by
  intro oid
  obtain ⟨rid, region, _, hlookupRid, hclosed, hcfg'⟩ := enter_cases h
  have hlocEq : (Reference.OId oid).loc? cfg = (Reference.OId oid).loc? cfg' :=
    enter_corollary_2 vcfg h oid
  cases hloc : (Reference.OId oid).loc? cfg with
  | none =>
    unfold Reference.objAt?
    dsimp only
    rw [hloc, ← hlocEq, hloc]
  | some loc =>
    have hloc' : (Reference.OId oid).loc? cfg' = some loc := by rw [← hlocEq]; exact hloc
    cases loc with
    | Rgn rid0 =>
      obtain ⟨region0, hlookup0, hmem0⟩ := (oid_loc_rgn_iff_in_heap vcfg).mp hloc
      obtain ⟨region0', hlookup0', hmem0'⟩ := (oid_loc_rgn_iff_in_heap vcfg').mp hloc'
      unfold Reference.objAt?
      dsimp only
      rw [hloc, hloc']
      dsimp only
      rw [hlookup0, hlookup0']
      by_cases hrideq : rid0 = rid
      · subst hrideq
        rw [hlookupRid] at hlookup0
        injection hlookup0 with hregion0_eq
        subst hregion0_eq
        rw [hcfg'] at hlookup0'
        dsimp only at hlookup0'
        rw [AList.lookup_insert] at hlookup0'
        injection hlookup0' with hregion0'_eq
        rw [← hregion0'_eq]
        rfl
      · have hlookup0'' : cfg'.heap.lookup rid0 = cfg.heap.lookup rid0 := by
          rw [hcfg']
          dsimp only
          exact AList.lookup_insert_ne hrideq
        rw [hlookup0'', hlookup0] at hlookup0'
        injection hlookup0' with hregion0'_eq
        rw [← hregion0'_eq]
    | Stk fid0 =>
      obtain ⟨frame0, hframe0, hmem0⟩ := (oid_loc_stk_iff_in_stack vcfg).mp hloc
      obtain ⟨frame0', hframe0', hmem0'⟩ := (oid_loc_stk_iff_in_stack vcfg').mp hloc'
      have hidx0 : frame0.index = fid0 := stackWithIndex_getElem_index_eq hframe0
      have hidx0' : frame0'.index = fid0 := stackWithIndex_getElem_index_eq hframe0'
      have hmem0mem : frame0 ∈ cfg.stackWithIndex := List.mem_of_getElem? hframe0
      have hmem0mem' : frame0' ∈ cfg'.stackWithIndex := List.mem_of_getElem? hframe0'
      have hmem0mem'' : frame0 ∈ cfg'.stackWithIndex := enter_corollary_frame_mem h frame0 hmem0mem
      have hframe0_eq : frame0 = frame0' :=
        swap_corollary_stackWithIndex_index_inj hmem0mem'' hmem0mem' (by rw [hidx0, hidx0'])
      unfold Reference.objAt?
      dsimp only
      rw [hloc, hloc']
      dsimp only
      have hfind0 : cfg.stackWithIndex.find? (fun f => f.index == fid0) = some frame0 := by
        rw [← hidx0]; exact swap_corollary_stackWithIndex_find_eq hmem0mem
      have hfind0' : cfg'.stackWithIndex.find? (fun f => f.index == fid0) = some frame0' := by
        rw [← hidx0']; exact swap_corollary_stackWithIndex_find_eq hmem0mem'
      rw [hfind0, hfind0', hframe0_eq]

theorem enter_corollary_objAt_eq_ref (vcfg : ValidConfig cfg) (vcfg' : ValidConfig cfg')
    (h : enter xf a cfg = some cfg') :
    ∀ ref : Reference, ref.objAt? cfg = ref.objAt? cfg' := by
  intro ref
  cases ref with
  | RId _ => rfl
  | OId oid => exact enter_corollary_objAt_eq vcfg vcfg' h oid

theorem enter_corollary_refStep_iff (vcfg : ValidConfig cfg) (vcfg' : ValidConfig cfg')
    (h : enter xf a cfg = some cfg') :
    ∀ x y, RefStep cfg x y ↔ RefStep cfg' x y := by
  intro x y
  unfold RefStep
  rw [enter_corollary_objAt_eq_ref vcfg vcfg' h x]

-- For a frame `frame0` already on the OLD stack, its two possible roots (a var's value, or its
-- own region's bridge object) are entirely unaffected by `enter`: any other frame claiming the
-- same index must (by index-injectivity) actually *be* `frame0`, whose own varMap is untouched
-- and whose own region is never the entered one (`enter_corollary_regionId_ne`), so its heap
-- lookup is untouched too.
theorem enter_corollary_frameRoot_iff (vcfg : ValidConfig cfg)
    (h : enter xf a cfg = some cfg')
    (frame0 : FrameWithIndex) (hframe0 : frame0 ∈ cfg.stackWithIndex) (start : Reference) :
    FrameRoot cfg frame0.index start ↔ FrameRoot cfg' frame0.index start := by
  obtain ⟨rid, region, _, hlookupRid, hclosed, hcfg'⟩ := enter_cases h
  have hne := enter_corollary_regionId_ne vcfg rid region hclosed hlookupRid frame0 hframe0
  have hframe0mem' : frame0 ∈ cfg'.stackWithIndex := enter_corollary_frame_mem h frame0 hframe0
  have hheap_eq : cfg'.heap.lookup frame0.regionId = cfg.heap.lookup frame0.regionId := by
    rw [hcfg']; dsimp only; exact AList.lookup_insert_ne hne
  unfold FrameRoot
  constructor
  · rintro (⟨frame1, hframe1, hidx1, var, hlookup1⟩ | ⟨frame1, hframe1, hidx1, region1, hlookup1, hstart⟩)
    · have heq1 : frame1 = frame0 := swap_corollary_stackWithIndex_index_inj hframe1 hframe0 hidx1
      subst heq1
      exact Or.inl ⟨frame1, hframe0mem', rfl, var, hlookup1⟩
    · have heq1 : frame1 = frame0 := swap_corollary_stackWithIndex_index_inj hframe1 hframe0 hidx1
      subst heq1
      exact Or.inr ⟨frame1, hframe0mem', rfl, region1, hheap_eq.trans hlookup1, hstart⟩
  · rintro (⟨frame1, hframe1, hidx1, var, hlookup1⟩ | ⟨frame1, hframe1, hidx1, region1, hlookup1, hstart⟩)
    · have heq1 : frame1 = frame0 := swap_corollary_stackWithIndex_index_inj hframe1 hframe0mem' hidx1
      subst heq1
      exact Or.inl ⟨frame1, hframe0, rfl, var, hlookup1⟩
    · have heq1 : frame1 = frame0 := swap_corollary_stackWithIndex_index_inj hframe1 hframe0mem' hidx1
      subst heq1
      exact Or.inr ⟨frame1, hframe0, rfl, region1, hheap_eq.symm.trans hlookup1, hstart⟩

theorem enter_corollary_frameReferencable_iff (vcfg : ValidConfig cfg) (vcfg' : ValidConfig cfg')
    (h : enter xf a cfg = some cfg')
    (frame0 : FrameWithIndex) (hframe0 : frame0 ∈ cfg.stackWithIndex) (ref : Reference) :
    FrameReferencable cfg frame0.index ref ↔ FrameReferencable cfg' frame0.index ref := by
  rw [FrameReferencable_iff_reflTransGen, FrameReferencable_iff_reflTransGen]
  constructor
  · rintro ⟨start, hroot, hrtg⟩
    exact ⟨start, (enter_corollary_frameRoot_iff vcfg h frame0 hframe0 start).mp hroot,
      hrtg.mono (fun x y hxy => (enter_corollary_refStep_iff vcfg vcfg' h x y).mp hxy)⟩
  · rintro ⟨start, hroot, hrtg⟩
    exact ⟨start, (enter_corollary_frameRoot_iff vcfg h frame0 hframe0 start).mpr hroot,
      hrtg.mono (fun x y hxy => (enter_corollary_refStep_iff vcfg vcfg' h x y).mpr hxy)⟩

theorem enter_corollary_mem_index_lt {cfg : RuntimeConfig} {frame : FrameWithIndex}
    (hframe : frame ∈ cfg.stackWithIndex) : frame.index < cfg.stack.length := by
  obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hframe
  have : frame.index = n := by rw [← hfeq]
  rw [this]; exact hn

-- Every frame in the post-mutation stack is either an old frame or exactly the freshly pushed one
-- (whose own index is `cfg.stack.length`, strictly above every old frame's index).
theorem enter_corollary_stackWithIndex_cases
    {cfg cfg' : RuntimeConfig} {a : VarName}
    (rid : RegionId) (region : Region) (hcfg' : cfg' = { cfg with
      stack := cfg.stack ++ [{ regionId := rid, bridgeVar := a, objMap := ∅, varMap := ∅ }],
      heap := cfg.heap.insert rid { region with status := Status.Open } }) :
    ∀ frame ∈ cfg'.stackWithIndex, frame ∈ cfg.stackWithIndex ∨ frame.index = cfg.stack.length := by
  intro frame hframe
  rw [hcfg'] at hframe
  unfold RuntimeConfig.stackWithIndex at hframe
  dsimp only at hframe
  rw [List.mapIdx_concat, List.mem_append, List.mem_singleton] at hframe
  rcases hframe with hold | hnew
  · exact Or.inl hold
  · right; rw [hnew]

