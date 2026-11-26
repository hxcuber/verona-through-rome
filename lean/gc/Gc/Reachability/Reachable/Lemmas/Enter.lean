module

public import Gc.Reachability.Reachable.Lemmas.Common

@[expose] public section

-- An on-stack frame's region is never what `enter` opens (L2: on-stack is Open, `enter` requires Closed).
theorem enter_regionId_ne {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {frame : FrameWithIndex} (hframe : frame ∈ cfg.stackWithIndex)
    {rid : RegionId} {region : Region} (hlookupRid : cfg.heap.lookup rid = some region)
    (hclosed : region.status = Status.Closed) : frame.regionId ≠ rid := by
  intro heq
  obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hframe
  obtain ⟨region', hlookup', hopen'⟩ := vcfg.l2 cfg.stack[n] (List.getElem_mem hn)
  rw [(congrArg (·.regionId) hfeq).trans heq, hlookupRid] at hlookup'
  cases hlookup'
  simp_all

-- `find? (index == fid)` over `stackWithIndex` is unaffected by appending a frame at a strictly larger index.
private theorem enter_stack_find_index_eq {cfg cfg' : RuntimeConfig} (h : enter xf a cfg = some cfg')
    (fid : Index) (hfid : fid < cfg.stack.length) :
    cfg.stackWithIndex.find? (fun frame => frame.index == fid) =
    cfg'.stackWithIndex.find? (fun frame => frame.index == fid) := by
  obtain ⟨rid, region, -, -, -, rfl⟩ := enter_cases h
  unfold RuntimeConfig.stackWithIndex
  dsimp only
  rw [List.mapIdx_concat, List.find?_append]
  simp [(Nat.ne_of_lt hfid).symm]

-- A `Stk fid` location is always a valid stack index.
theorem loc_stk_lt {cfg : RuntimeConfig} {oid : ObjectId} {fid : Index}
    (hloc : (Reference.OId oid).loc? cfg = some (Location.Stk fid)) : fid < cfg.stack.length := by
  unfold Reference.loc? at hloc
  dsimp only at hloc
  cases h1 : cfg.stackWithIndex.findRev? (fun frame => frame.objMap.keys.contains oid) <;>
  cases h2 : cfg.heap.entries.find? (fun (p : Sigma (fun _ : RegionId => Region)) => p.2.objMap.keys.contains oid) <;>
    simp only [h1, h2, Option.some.injEq, Location.Stk.injEq, reduceCtorEq] at hloc
  rename_i frame
  rw [List.findRev?_eq_find?_reverse] at h1
  obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp (List.mem_reverse.mp (List.mem_of_find?_eq_some h1))
  rw [← hloc, ← hfeq]
  exact hn

-- `objAt?` is unconditionally unchanged by `enter`, for every object id.
private theorem enter_objAt_eq {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : enter xf a cfg = some cfg') (oid : ObjectId) :
    (Reference.OId oid).objAt? cfg = (Reference.OId oid).objAt? cfg' := by
  obtain ⟨rid, region, -, hlookupRid, hclosed, hcfg'⟩ := enter_cases h
  have hlocEq := enter_corollary_2 vcfg h oid
  unfold Reference.objAt?
  dsimp only
  rw [hlocEq]
  cases hloc' : (Reference.OId oid).loc? cfg' with
  | none => rfl
  | some loc =>
    cases loc with
    | Rgn rid0 =>
      dsimp only
      subst hcfg'
      by_cases heq : rid0 = rid
      · subst heq
        rw [AList.lookup_insert, hlookupRid]
        rfl
      · rw [AList.lookup_insert_ne heq]
    | Stk fid =>
      dsimp only
      rw [enter_stack_find_index_eq h fid (loc_stk_lt (by rw [hlocEq]; exact hloc'))]

-- OId-sourced steps agree unconditionally between cfg/cfg' across `enter`.
theorem enter_oid_step_iff {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : enter xf a cfg = some cfg') (oid : ObjectId) (b : Reference) :
    ReachableStep cfg (Reference.OId oid) b ↔ ReachableStep cfg' (Reference.OId oid) b := by
  rw [ReachableStep_oid_iff, ReachableStep_oid_iff, enter_objAt_eq vcfg h oid]

-- The root of any chain reaching a safe reference is itself safe.
theorem safe_reflTransGen_root_safe {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid : RegionId} {region : Region} (hlookup : cfg.heap.lookup rid = some region)
    (hopen : region.status = Status.Open)
    {start ref : Reference} (hrtg : Relation.ReflTransGen (ReachableStep cfg) start ref) :
    SafeRef cfg rid ref → SafeRef cfg rid start := by
  induction hrtg with
  | refl => exact id
  | tail _ hstep ih => exact fun hsafe => ih (predecessor_safe vcfg hlookup hopen hsafe hstep)

-- Every pre-existing frame survives `enter` unchanged, at the same index.
theorem enter_frame_mem_up {cfg cfg' : RuntimeConfig} (h : enter xf a cfg = some cfg')
    {frame : FrameWithIndex} (hframe : frame ∈ cfg.stackWithIndex) : frame ∈ cfg'.stackWithIndex := by
  obtain ⟨rid, region, -, -, -, rfl⟩ := enter_cases h
  unfold RuntimeConfig.stackWithIndex at hframe ⊢
  dsimp only
  rw [List.mapIdx_concat]
  exact List.mem_append_left _ hframe

-- Every `cfg'.stackWithIndex` member is either a pre-existing frame or the freshly-appended one, pinned against the caller's own `rid`/`region`.
theorem enter_frame_cases {cfg cfg' : RuntimeConfig} {rid : RegionId} {region : Region} {a : VarName}
    (hcfg' : cfg' = { cfg with
      stack := cfg.stack ++ [{ regionId := rid, bridgeVar := a, objMap := ∅, varMap := ∅ }],
      heap := cfg.heap.insert rid { region with status := Status.Open } })
    {frame : FrameWithIndex} (hframe : frame ∈ cfg'.stackWithIndex) :
    (frame ∈ cfg.stackWithIndex ∧ frame.index < cfg.stack.length) ∨
    (frame.regionId = rid ∧ frame.bridgeVar = a ∧ frame.varMap = ∅ ∧ frame.objMap = ∅ ∧
      frame.index = cfg.stack.length) := by
  subst hcfg'
  unfold RuntimeConfig.stackWithIndex at hframe
  dsimp only at hframe
  rw [List.mapIdx_concat] at hframe
  rcases List.mem_append.mp hframe with hmem | hmem
  · obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hmem
    exact .inl ⟨hmem, by rw [← hfeq]; exact hn⟩
  · rw [List.mem_singleton] at hmem
    subst hmem
    exact .inr ⟨rfl, rfl, rfl, rfl, rfl⟩

-- Any `cfg'.stackWithIndex` member whose index still fits inside `cfg.stack` was already there.
theorem enter_frame_mem_down {cfg cfg' : RuntimeConfig} (h : enter xf a cfg = some cfg')
    {frame : FrameWithIndex} (hframe : frame ∈ cfg'.stackWithIndex) (hlt : frame.index < cfg.stack.length) :
    frame ∈ cfg.stackWithIndex := by
  obtain ⟨rid, region, -, -, -, hcfg'⟩ := enter_cases h
  rcases enter_frame_cases hcfg' hframe with ⟨hmem, -⟩ | ⟨-, -, -, -, hidx⟩
  · exact hmem
  · exact absurd (hidx ▸ hlt) (lt_irrefl _)

-- For `oid` in an on-stack frame's region, `enter` preserves frame-reachability from every old frame and the fresh frame reaches nothing of it.
theorem enter_suspended_reach {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : enter xf a cfg = some cfg') {F : FrameWithIndex} (hF : F ∈ cfg.stackWithIndex) {oid : ObjectId}
    (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn F.regionId)) :
    (∀ G ∈ cfg.stackWithIndex, FrameReachable cfg G.index (.OId oid) ↔ FrameReachable cfg' G.index (.OId oid)) ∧
    ¬ FrameReachable cfg' cfg.stack.length (.OId oid) := by
  have vcfg' := enter_valid vcfg h
  obtain ⟨rid, regionEntered, -, hlookupRid, hclosedRid, hcfg'⟩ := enter_cases h
  obtain ⟨region, hlookup, hopen⟩ := l2_of_stackWithIndex vcfg hF
  have hne := enter_regionId_ne vcfg hF hlookupRid hclosedRid
  have hlk : ∀ X ∈ cfg.stackWithIndex, cfg'.heap.lookup X.regionId = cfg.heap.lookup X.regionId := fun X hX => by
    rw [hcfg']; dsimp only
    rw [AList.lookup_insert_ne (enter_regionId_ne vcfg hX hlookupRid hclosedRid)]
  have hlookup' : cfg'.heap.lookup F.regionId = some region := (hlk F hF).trans hlookup
  have hloc' : (Reference.OId oid).loc? cfg' = some (Location.Rgn F.regionId) := by
    rwa [← enter_corollary_2 vcfg h oid]
  have hroot : ∀ G ∈ cfg.stackWithIndex, ∀ s, FrameRoot cfg G.index s ↔ FrameRoot cfg' G.index s := by
    intro G hG s
    have hGlt : G.index < cfg.stack.length := by
      obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp hG
      exact hn
    constructor
    · rintro (⟨X, hX, hi, v, hv⟩ | ⟨X, hX, hi, r, hl, hb⟩)
      · exact .inl ⟨X, enter_frame_mem_up h hX, hi, v, hv⟩
      · exact .inr ⟨X, enter_frame_mem_up h hX, hi, r, (hlk X hX).trans hl, hb⟩
    · rintro (⟨X, hX, hi, v, hv⟩ | ⟨X, hX, hi, r, hl, hb⟩)
      · exact .inl ⟨X, enter_frame_mem_down h hX (hi ▸ hGlt), hi, v, hv⟩
      · have hX' := enter_frame_mem_down h hX (hi ▸ hGlt)
        exact .inr ⟨X, hX', hi, r, (hlk X hX').symm.trans hl, hb⟩
  refine ⟨fun G hG => ?_, fun hr => ?_⟩
  · simp only [FrameReachable_iff_reflTransGen]
    constructor
    · rintro ⟨s, hs, hc⟩
      exact ⟨s, (hroot G hG s).mp hs,
        safe_reflTransGen_transport vcfg hlookup hopen (enter_oid_step_iff vcfg h) hc (.inl hloc)⟩
    · rintro ⟨s, hs, hc⟩
      exact ⟨s, (hroot G hG s).mpr hs, safe_reflTransGen_transport vcfg' hlookup' hopen
        (fun o b => (enter_oid_step_iff vcfg h o b).symm) hc (.inl hloc')⟩
  · obtain ⟨s, hs, hc⟩ := (FrameReachable_iff_reflTransGen ..).mp hr
    have hbr : s = Reference.OId regionEntered.bridgeObjectId := by
      rcases hs with ⟨X, hX, hi, v, hv⟩ | ⟨X, hX, hi, r, hl, hb⟩ <;>
        rcases enter_frame_cases hcfg' hX with ⟨-, hlt⟩ | ⟨hrid, -, hvm, -, -⟩
      · exact absurd hi hlt.ne
      · simp [hvm] at hv
      · exact absurd hi hlt.ne
      · rw [hrid, hcfg'] at hl
        dsimp only at hl
        rw [AList.lookup_insert] at hl
        cases hl
        exact hb
    subst hbr
    have hbridgeLoc : (Reference.OId regionEntered.bridgeObjectId).loc? cfg' = some (Location.Rgn rid) := by
      rw [oid_loc_rgn_iff_in_heap vcfg']
      refine ⟨{ regionEntered with status := Status.Open }, ?_, vcfg.h1 regionEntered ?_⟩
      · rw [hcfg']; dsimp only; rw [AList.lookup_insert]
      · exact List.mem_map_of_mem (AList.lookup_mem_entries hlookupRid)
    have hsafe := safe_reflTransGen_root_safe vcfg' hlookup' hopen hc (.inl hloc')
    simp only [SafeRef] at hsafe
    rcases hsafe with hb | ⟨f, hb⟩
    · simp [hbridgeLoc] at hb
      exact hne hb.symm
    · simp [hbridgeLoc] at hb
