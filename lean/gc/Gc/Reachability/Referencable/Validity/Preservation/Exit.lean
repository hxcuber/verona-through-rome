import Gc.Model.Mutation.Exit
import Gc.Model.Preservation.Exit
import Gc.Model.Preservation.Common
import Gc.Reachability.Referencable.Validity.Reachable
import Gc.Reachability.Referencable.Corollaries.Common

theorem exit_corollary_stackWithIndex_eq {cfg : RuntimeConfig} {poppedFrame : Frame}
    (hlast : cfg.stack.getLast? = some poppedFrame) :
    cfg.stackWithIndex = cfg.stack.dropLast.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)) ++
      [({ poppedFrame with index := cfg.stack.dropLast.length } : FrameWithIndex)] := by
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [poppedFrame] :=
    (List.dropLast_append_getLast? poppedFrame hlast).symm
  unfold RuntimeConfig.stackWithIndex
  conv_lhs => rw [stack_eq]
  rw [List.mapIdx_concat]

-- Every frame surviving into `cfg'.stackWithIndex` is the *exact same* record as some frame in
-- `cfg.stackWithIndex` (the mutation only ever drops the last element, never touches earlier ones).
private theorem exit_corollary_frame_old {cfg cfg' : RuntimeConfig} {poppedFrame : Frame}
    (hlast : cfg.stack.getLast? = some poppedFrame) (hcfg'stack : cfg'.stack = cfg.stack.dropLast) :
    ∀ frame ∈ cfg'.stackWithIndex, frame ∈ cfg.stackWithIndex := by
  intro frame hframe
  rw [exit_corollary_stackWithIndex_eq hlast]
  apply List.mem_append_left
  unfold RuntimeConfig.stackWithIndex at hframe
  rw [hcfg'stack] at hframe
  exact hframe

-- The popped frame's own region can never be an earlier (surviving) frame's own region: by
-- S1-index-uniqueness, equal regionIds force equal indices, but the popped frame's own index
-- (`cfg.stack.dropLast.length`) is strictly above every surviving frame's.
private theorem exit_corollary_regionId_ne {cfg : RuntimeConfig} (s1 : S1 cfg) {poppedFrame : Frame}
    (hlast : cfg.stack.getLast? = some poppedFrame) :
    ∀ frame ∈ cfg.stack.dropLast.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex)),
      frame.regionId ≠ poppedFrame.regionId := by
  intro frame hframe heq
  have hpoppedmem : ({ poppedFrame with index := cfg.stack.dropLast.length } : FrameWithIndex) ∈
      cfg.stackWithIndex := by
    rw [exit_corollary_stackWithIndex_eq hlast]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hframemem : frame ∈ cfg.stackWithIndex := by
    rw [exit_corollary_stackWithIndex_eq hlast]
    exact List.mem_append_left _ hframe
  have hidxeq := merge_corollary_regionId_unique_index s1 hframemem hpoppedmem heq
  have hframe_lt : frame.index < cfg.stack.dropLast.length := by
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hframe
    have : frame.index = n := by rw [← hfeq]
    rw [this]; exact hn
  dsimp only at hidxeq
  rw [hidxeq] at hframe_lt
  exact absurd hframe_lt (lt_irrefl _)

private theorem exit_corollary_objAt_loc_some {cfg : RuntimeConfig} {oid : ObjectId} {obj : Object}
    (hobjAt : (Reference.OId oid).objAt? cfg = some obj) : (Reference.OId oid).loc? cfg ≠ none := by
  intro hnone
  unfold Reference.objAt? at hobjAt
  dsimp only at hobjAt
  rw [hnone] at hobjAt
  contradiction

-- For any oid known to survive (its cfg'-location is not none), `objAt?` agrees between cfg and
-- cfg' -- the popped frame's status flip never changes any objMap/bridgeObjectId content, and
-- every other region/frame is either untouched (AList.lookup_insert_ne) or, for the popped
-- region itself, its objMap component (all objAt? actually reads) is unaffected by the status
-- flip.
private theorem exit_corollary_objAt_eq_of_ne_none (vcfg : ValidConfig cfg) (vcfg' : ValidConfig cfg')
    (h : exit cfg = some cfg') (oid : ObjectId) (hne' : (Reference.OId oid).loc? cfg' ≠ none) :
    (Reference.OId oid).objAt? cfg = (Reference.OId oid).objAt? cfg' := by
  obtain ⟨poppedFrame, region, hlen, hlast, hlookupPopped, hopenPopped, hcfg'⟩ := exit_cases h
  cases hloc' : (Reference.OId oid).loc? cfg' with
  | none => exact absurd hloc' hne'
  | some loc' =>
    have hloc : (Reference.OId oid).loc? cfg = some loc' := by
      cases loc' with
      | Rgn rid0 => exact (exit_corollary_1 vcfg h (Reference.OId oid)).mpr hloc'
      | Stk fid0 => exact exit_corollary_3 vcfg h (Reference.OId oid) hloc'
    unfold Reference.objAt?
    dsimp only
    rw [hloc, hloc']
    cases loc' with
    | Rgn rid0 =>
      dsimp only
      obtain ⟨region0, hlookup0, hmem0⟩ := (oid_loc_rgn_iff_in_heap vcfg).mp hloc
      obtain ⟨region0', hlookup0', hmem0'⟩ := (oid_loc_rgn_iff_in_heap vcfg').mp hloc'
      rw [hlookup0, hlookup0']
      by_cases hrideq : rid0 = poppedFrame.regionId
      · subst hrideq
        rw [hlookupPopped] at hlookup0
        injection hlookup0 with hregion0_eq
        subst hregion0_eq
        rw [hcfg'] at hlookup0'
        dsimp only at hlookup0'
        rw [AList.lookup_insert] at hlookup0'
        injection hlookup0' with hregion0'_eq
        rw [← hregion0'_eq]
        rfl
      · have hlookup0'' : cfg'.heap.lookup rid0 = cfg.heap.lookup rid0 := by
          rw [hcfg']; dsimp only; exact AList.lookup_insert_ne hrideq
        rw [hlookup0'', hlookup0] at hlookup0'
        injection hlookup0' with hregion0'_eq
        rw [← hregion0'_eq]
    | Stk fid0 =>
      dsimp only
      obtain ⟨frame0, hframe0, hmem0⟩ := (oid_loc_stk_iff_in_stack vcfg).mp hloc
      obtain ⟨frame0', hframe0', hmem0'⟩ := (oid_loc_stk_iff_in_stack vcfg').mp hloc'
      have hidx0 : frame0.index = fid0 := stackWithIndex_getElem_index_eq hframe0
      have hidx0' : frame0'.index = fid0 := stackWithIndex_getElem_index_eq hframe0'
      have hmem0mem : frame0 ∈ cfg.stackWithIndex := List.mem_of_getElem? hframe0
      have hmem0mem' : frame0' ∈ cfg'.stackWithIndex := List.mem_of_getElem? hframe0'
      have hmem0mem'' : frame0' ∈ cfg.stackWithIndex :=
        exit_corollary_frame_old hlast (by rw [hcfg']) frame0' hmem0mem'
      have hframe0_eq : frame0 = frame0' :=
        swap_corollary_stackWithIndex_index_inj hmem0mem hmem0mem'' (by rw [hidx0, hidx0'])
      have hfind0 : cfg.stackWithIndex.find? (fun f => f.index == fid0) = some frame0 := by
        rw [← hidx0]; exact swap_corollary_stackWithIndex_find_eq hmem0mem
      have hfind0' : cfg'.stackWithIndex.find? (fun f => f.index == fid0) = some frame0' := by
        rw [← hidx0']; exact swap_corollary_stackWithIndex_find_eq hmem0mem'
      rw [hfind0, hfind0', hframe0_eq]

-- For a surviving frame (already on `cfg'.stackWithIndex`), FrameReferencable agrees between cfg
-- and cfg' at that frame's index: roots transport directly (same record, and the popped frame's
-- region can never be a surviving frame's own region, by exit_corollary_regionId_ne), and the
-- inductive `step` case transports via exit_corollary_objAt_eq_of_ne_none once we know (via HS1
-- + the direction we're proving) that the relevant oid actually survives.
private theorem exit_corollary_frameRoot_iff (vcfg : ValidConfig cfg)
    (h : exit cfg = some cfg')
    (frame0 : FrameWithIndex) (hframe0' : frame0 ∈ cfg'.stackWithIndex) (start : Reference) :
    FrameRoot cfg frame0.index start ↔ FrameRoot cfg' frame0.index start := by
  obtain ⟨poppedFrame, region, hlen, hlast, hlookupPopped, hopenPopped, hcfg'⟩ := exit_cases h
  have hframe0 : frame0 ∈ cfg.stackWithIndex := exit_corollary_frame_old hlast (by rw [hcfg']) frame0 hframe0'
  have hne : frame0.regionId ≠ poppedFrame.regionId := by
    have := exit_corollary_regionId_ne vcfg.s1 hlast
    unfold RuntimeConfig.stackWithIndex at hframe0'
    rw [(by rw [hcfg'] : cfg'.stack = cfg.stack.dropLast)] at hframe0'
    exact this frame0 hframe0'
  have hheap_eq : cfg'.heap.lookup frame0.regionId = cfg.heap.lookup frame0.regionId := by
    rw [hcfg']; dsimp only; exact AList.lookup_insert_ne hne
  unfold FrameRoot
  constructor
  · rintro (⟨frame1, hframe1, hidx1, var, hlookup1⟩ | ⟨frame1, hframe1, hidx1, region1, hlookup1, hstart⟩)
    · have heq1 : frame1 = frame0 := swap_corollary_stackWithIndex_index_inj hframe1 hframe0 hidx1
      subst heq1
      exact Or.inl ⟨frame1, hframe0', rfl, var, hlookup1⟩
    · have heq1 : frame1 = frame0 := swap_corollary_stackWithIndex_index_inj hframe1 hframe0 hidx1
      subst heq1
      exact Or.inr ⟨frame1, hframe0', rfl, region1, hheap_eq.trans hlookup1, hstart⟩
  · rintro (⟨frame1, hframe1, hidx1, var, hlookup1⟩ | ⟨frame1, hframe1, hidx1, region1, hlookup1, hstart⟩)
    · have heq1 : frame1 = frame0 := swap_corollary_stackWithIndex_index_inj hframe1 hframe0' hidx1
      subst heq1
      exact Or.inl ⟨frame1, hframe0, rfl, var, hlookup1⟩
    · have heq1 : frame1 = frame0 := swap_corollary_stackWithIndex_index_inj hframe1 hframe0' hidx1
      subst heq1
      exact Or.inr ⟨frame1, hframe0, rfl, region1, hheap_eq.symm.trans hlookup1, hstart⟩

-- A `RefStep`-target held by any resolved object is itself already in `cfg.refs` -- mirrors the
-- membership-chasing already done inline in `Corollaries.lean`'s `RefStep_lower_bound_step`, just
-- packaged as its own standalone fact (needed here to feed HS1 for the survival side-condition).
private theorem exit_corollary_objAt_target_mem_refs {cfg : RuntimeConfig} {oid oidb : ObjectId} {obj : Object}
    (hobjAt : (Reference.OId oid).objAt? cfg = some obj) (hcontains : obj.refs.contains (Reference.OId oidb)) :
    Reference.OId oidb ∈ cfg.refs := by
  unfold Reference.objAt? at hobjAt
  dsimp only at hobjAt
  cases hloc : (Reference.OId oid).loc? cfg with
  | none => rw [hloc] at hobjAt; simp at hobjAt
  | some loc =>
    rw [hloc] at hobjAt
    cases loc with
    | Rgn rid =>
      dsimp only at hobjAt
      cases hlookup : cfg.heap.lookup rid with
      | none => rw [hlookup] at hobjAt; simp at hobjAt
      | some region =>
        rw [hlookup] at hobjAt
        dsimp at hobjAt
        have hobj_mem_entries := AList.mem_lookup_iff.mp (Option.mem_def.mpr hobjAt)
        have hobj_mem_values := List.mem_map_of_mem (f := (·.2)) hobj_mem_entries
        dsimp only at hobj_mem_values
        have hb_in_obj_refs := List.contains_iff_mem.mp hcontains
        have hb_in_region_refs : _ ∈ region.refs := List.mem_flatMap_of_mem hobj_mem_values hb_in_obj_refs
        unfold RuntimeConfig.refs Heap.refs
        apply List.mem_append_right
        rw [List.bind_eq_flatMap, List.mem_flatMap]
        exact ⟨region, List.mem_map_of_mem (f := (·.2)) (AList.mem_lookup_iff.mp (Option.mem_def.mpr hlookup)),
          hb_in_region_refs⟩
    | Stk fid0 =>
      dsimp only at hobjAt
      cases hfind : cfg.stackWithIndex.find? (fun frame => frame.index == fid0) with
      | none => rw [hfind] at hobjAt; simp at hobjAt
      | some frameA =>
        rw [hfind] at hobjAt
        dsimp at hobjAt
        have hframeA_mem := List.mem_of_find?_eq_some hfind
        have hobj_mem_entries := AList.mem_lookup_iff.mp (Option.mem_def.mpr hobjAt)
        have hobj_mem_values := List.mem_map_of_mem (f := (·.2)) hobj_mem_entries
        dsimp only at hobj_mem_values
        have hb_in_obj_refs := List.contains_iff_mem.mp hcontains
        have hb_in_frame_refs : _ ∈ frameA.refs :=
          List.mem_append_left _ (List.mem_flatMap_of_mem hobj_mem_values hb_in_obj_refs)
        unfold RuntimeConfig.refs Stack.refs
        apply List.mem_append_left
        unfold RuntimeConfig.stackWithIndex at hframeA_mem
        obtain ⟨n, hn_len, hn_eq⟩ := List.mem_mapIdx.mp hframeA_mem
        have hg_in_stack : frameA.toFrame ∈ cfg.stack := by
          rw [← hn_eq]; dsimp; exact List.mem_iff_getElem.mpr ⟨n, _, rfl⟩
        rw [List.bind_eq_flatMap, List.mem_flatMap]
        exact ⟨Frame.refs frameA.toFrame, List.mem_map_of_mem hg_in_stack, hb_in_frame_refs⟩

-- A `RefStep`-hop valid in cfg' is also valid in cfg: surviving content is untouched, and the
-- hop's own `objAt?` success on its source already gives the survival side-condition
-- `exit_corollary_objAt_eq_of_ne_none` needs -- no extra bookkeeping required for this direction.
private theorem exit_corollary_refStep_down (vcfg : ValidConfig cfg) (vcfg' : ValidConfig cfg')
    (h : exit cfg = some cfg') {a b : Reference} (hstep : RefStep cfg' a b) : RefStep cfg a b := by
  obtain ⟨oid, rfl⟩ := hstep.exists_oid_left
  obtain ⟨obj, hobjAt, hcontains⟩ := hstep
  have hne' := exit_corollary_objAt_loc_some hobjAt
  exact ⟨obj, (exit_corollary_objAt_eq_of_ne_none vcfg vcfg' h oid hne').trans hobjAt, hcontains⟩

-- Downward chain transport: immediate from exit_corollary_refStep_down, hop by hop. Safe to
-- induct directly on `ReflTransGen` (unlike `FrameReferencable`): its relation/start arguments are
-- genuine *parameters*, not indices, so nothing outside the chain itself needs to be reverted.
private theorem exit_corollary_reflTransGen_down (vcfg : ValidConfig cfg) (vcfg' : ValidConfig cfg')
    (h : exit cfg = some cfg') {start ref : Reference}
    (hrtg : Relation.ReflTransGen (RefStep cfg') start ref) :
    Relation.ReflTransGen (RefStep cfg) start ref := by
  induction hrtg with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (exit_corollary_refStep_down vcfg vcfg' h hstep)

-- Every element reached by a cfg'-chain rooted at an already-alive `start` is itself alive.
private theorem exit_corollary_reflTransGen_alive {cfg' : RuntimeConfig} {start ref : Reference}
    (hrtg : Relation.ReflTransGen (RefStep cfg') start ref)
    (hstart_alive : ∀ oid, start = Reference.OId oid → (Reference.OId oid).loc? cfg' ≠ none)
    (vcfg' : ValidConfig cfg') :
    ∀ oid, ref = Reference.OId oid → (Reference.OId oid).loc? cfg' ≠ none := by
  induction hrtg with
  | refl => exact hstart_alive
  | tail _ hstep _ =>
    intro oid hoid
    subst hoid
    obtain ⟨oidb, rfl⟩ := hstep.exists_oid_left
    obtain ⟨obj, hobjAt, hcontains⟩ := hstep
    exact loc_ne_none_of_mem_objectIds cfg' vcfg' oid
      (vcfg'.hs1 oid (exit_corollary_objAt_target_mem_refs hobjAt hcontains))

-- Upward chain transport: each hop needs its source already known cfg'-alive, tracked via
-- exit_corollary_reflTransGen_alive applied to the (already-transported) prefix.
private theorem exit_corollary_reflTransGen_up (vcfg : ValidConfig cfg) (vcfg' : ValidConfig cfg')
    (h : exit cfg = some cfg') {start ref : Reference}
    (hrtg : Relation.ReflTransGen (RefStep cfg) start ref)
    (hstart_alive : ∀ oid, start = Reference.OId oid → (Reference.OId oid).loc? cfg' ≠ none) :
    Relation.ReflTransGen (RefStep cfg') start ref := by
  induction hrtg with
  | refl => exact Relation.ReflTransGen.refl
  | tail hprev hstep ih =>
    have ihres := ih
    obtain ⟨oidb, rfl⟩ := hstep.exists_oid_left
    have hb_alive := exit_corollary_reflTransGen_alive ihres hstart_alive vcfg' oidb rfl
    obtain ⟨obj, hobjAt, hcontains⟩ := hstep
    exact ihres.tail
      ⟨obj, (exit_corollary_objAt_eq_of_ne_none vcfg vcfg' h oidb hb_alive).symm.trans hobjAt, hcontains⟩

-- A `FrameRoot`'s own start reference is always alive: the var-disjunct's value transports
-- through HS1 (it's directly in the owning frame's own refs), the bridge-disjunct's through H1
-- (the region's bridge object is always in its own objMap).
private theorem exit_corollary_frameRoot_alive {cfg' : RuntimeConfig} (vcfg' : ValidConfig cfg')
    {fid : Index} {start : Reference} (hroot : FrameRoot cfg' fid start) :
    ∀ oid, start = Reference.OId oid → (Reference.OId oid).loc? cfg' ≠ none := by
  rcases hroot with ⟨frame1, hframe1, _, var, hlookup1⟩ | ⟨frame1, hframe1, _, region1, hlookup1, hstart⟩
  · intro oid hoid
    subst hoid
    apply loc_ne_none_of_mem_objectIds cfg' vcfg'
    apply vcfg'.hs1
    unfold RuntimeConfig.refs Stack.refs
    apply List.mem_append_left
    unfold RuntimeConfig.stackWithIndex at hframe1
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hframe1
    have hg_in_stack : cfg'.stack[n] ∈ cfg'.stack := List.getElem_mem hn
    rw [← hfeq] at hlookup1
    dsimp only at hlookup1
    rw [List.bind_eq_flatMap, List.mem_flatMap]
    refine ⟨Frame.refs cfg'.stack[n], List.mem_map_of_mem hg_in_stack, ?_⟩
    unfold Frame.refs
    apply List.mem_append_right
    exact List.mem_map_of_mem (f := (·.2)) (AList.mem_lookup_iff.mp (Option.mem_def.mpr hlookup1))
  · intro oid hoid
    have heq := hstart.symm.trans hoid
    injection heq with heq_eq
    subst heq_eq
    apply loc_ne_none_of_mem_objectIds cfg' vcfg'
    have hregionMem := AList.mem_lookup_iff.mp (Option.mem_def.mpr hlookup1)
    have hregionsMem := List.mem_map_of_mem (f := (·.2)) hregionMem
    have hbridgeMem := vcfg'.h1 _ hregionsMem
    unfold RuntimeConfig.objectIds
    apply List.mem_append_right
    exact heap_objectIds_of_mem hregionMem (AList.mem_keys.mpr hbridgeMem)

theorem exit_corollary_frameReferencable_iff (vcfg : ValidConfig cfg) (vcfg' : ValidConfig cfg')
    (h : exit cfg = some cfg')
    (frame0 : FrameWithIndex) (hframe0' : frame0 ∈ cfg'.stackWithIndex) (ref : Reference) :
    FrameReferencable cfg frame0.index ref ↔ FrameReferencable cfg' frame0.index ref := by
  rw [FrameReferencable_iff_reflTransGen, FrameReferencable_iff_reflTransGen]
  constructor
  · rintro ⟨start, hroot, hrtg⟩
    have hroot' := (exit_corollary_frameRoot_iff vcfg h frame0 hframe0' start).mp hroot
    have hstart_alive := exit_corollary_frameRoot_alive vcfg' hroot'
    exact ⟨start, hroot', exit_corollary_reflTransGen_up vcfg vcfg' h hrtg hstart_alive⟩
  · rintro ⟨start, hroot, hrtg⟩
    have hroot_down := (exit_corollary_frameRoot_iff vcfg h frame0 hframe0' start).mpr hroot
    exact ⟨start, hroot_down, exit_corollary_reflTransGen_down vcfg vcfg' h hrtg⟩

theorem exit_cr3 : ValidReachableConfig cfg →
  exit cfg = some cfg' →
  CR3 cfg' := by
  intro vrcfg h
  have vcfg := vrcfg.toValidConfig
  have vcfg' := exit_valid vcfg h
  obtain ⟨poppedFrame, region, hlen, hlast, hlookupPopped, hopenPopped, hcfg'⟩ := exit_cases h
  unfold CR3
  intro frame hframeMem frame' hframe'Mem hlt oid hloc hreach
  have hframeOld : frame ∈ cfg.stackWithIndex := exit_corollary_frame_old hlast (by rw [hcfg']) frame hframeMem
  have hframe'Old : frame' ∈ cfg.stackWithIndex := exit_corollary_frame_old hlast (by rw [hcfg']) frame' hframe'Mem
  have hlocDown : (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) :=
    (exit_corollary_1 vcfg h (Reference.OId oid)).mpr hloc
  have hreachDown : FrameReferencable cfg frame'.index (Reference.OId oid) :=
    (exit_corollary_frameReferencable_iff vcfg vcfg' h frame' hframe'Mem (Reference.OId oid)).mpr hreach
  have hconcDown : FrameReferencable cfg frame.index (Reference.OId oid) :=
    vrcfg.cr3 frame hframeOld frame' hframe'Old hlt oid hlocDown hreachDown
  exact (exit_corollary_frameReferencable_iff vcfg vcfg' h frame hframeMem (Reference.OId oid)).mp hconcDown

theorem exit_reachable_valid : ValidReachableConfig cfg →
  exit cfg = some cfg' →
  ValidReachableConfig cfg' := by
  intro vrcfg h
  exact { exit_valid vrcfg.toValidConfig h with cr3 := exit_cr3 vrcfg h }
