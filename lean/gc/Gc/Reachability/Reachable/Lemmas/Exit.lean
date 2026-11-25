module

public import Gc.Model.Types
public import Gc.Model.Helpers
public import Gc.Model.Validity
public import Gc.Model.Mutation.Mutation
public import Gc.Model.Preservation
public import Gc.Reachability.Reachable.Semantics
public import Gc.Reachability.Reachable.Lemmas.Common
public import Gc.Reachability.Reachable.Lemmas.Enter

@[expose] public section

-- `cfg.stackWithIndex` is `cfg'.stackWithIndex` plus the popped frame at index `length - 1`.
private theorem exit_swi {cfg cfg' : RuntimeConfig} (h : exit cfg = some cfg') :
    ∃ p : Frame, cfg.stackWithIndex = cfg'.stackWithIndex ++ [{ p with index := cfg.stack.length - 1 }] ∧
      cfg'.stackWithIndex.length = cfg.stack.length - 1 := by
  obtain ⟨p, region, -, hlast, -, -, rfl⟩ := exit_cases h
  refine ⟨p, ?_, by simp [RuntimeConfig.stackWithIndex]⟩
  rw [stackWithIndex_eq_of_getLast? hlast, List.length_dropLast]
  rfl

-- A pre-existing, non-popped frame survives `exit` unchanged, at the same index.
theorem exit_frame_mem_up {cfg cfg' : RuntimeConfig} (h : exit cfg = some cfg')
    {frame : FrameWithIndex} (hframe : frame ∈ cfg.stackWithIndex) (hlt : frame.index < cfg.stack.length - 1) :
    frame ∈ cfg'.stackWithIndex := by
  obtain ⟨p, hswi, -⟩ := exit_swi h
  rcases List.mem_append.mp (hswi ▸ hframe) with hmem | hmem
  · exact hmem
  · obtain rfl := List.mem_singleton.mp hmem
    exact absurd hlt (lt_irrefl _)

-- Every `cfg'.stackWithIndex` member was already in `cfg`, with index below the popped frame's.
theorem exit_frame_mem_down {cfg cfg' : RuntimeConfig} (h : exit cfg = some cfg')
    {frame : FrameWithIndex} (hframe : frame ∈ cfg'.stackWithIndex) :
    frame ∈ cfg.stackWithIndex ∧ frame.index < cfg.stack.length - 1 := by
  obtain ⟨p, hswi, hlen⟩ := exit_swi h
  exact ⟨hswi ▸ List.mem_append_left _ hframe,
    hlen ▸ (List.getElem?_eq_some_iff.mp (stackWithIndex_mem_getElem_eq hframe)).1⟩

-- Every surviving stack index resolves to the same frame before and after `exit`.
private theorem exit_getElem_eq {cfg cfg' : RuntimeConfig} (h : exit cfg = some cfg')
    {fid : Index} (hfid : fid < cfg.stack.length - 1) : cfg'.stackWithIndex[fid]? = cfg.stackWithIndex[fid]? := by
  obtain ⟨p, hswi, hlen⟩ := exit_swi h
  rw [hswi, List.getElem?_append_left (hlen ▸ hfid)]

-- `loc?` agrees between `cfg`/`cfg'` for any oid not resolving to the popped frame's slot.
theorem exit_loc_eq_of_ne_popped {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : exit cfg = some cfg') (oid : ObjectId)
    (hne : (Reference.OId oid).loc? cfg ≠ some (Location.Stk (cfg.stack.length - 1))) :
    (Reference.OId oid).loc? cfg = (Reference.OId oid).loc? cfg' := by
  rcases exit_loc vcfg h (.OId oid) with heq | ⟨hnone, fid, hstk⟩
  · exact heq.symm
  · obtain ⟨frame, hget, hmem⟩ := (oid_loc_stk_iff_in_stack vcfg).mp hstk
    have hfidNe : fid ≠ cfg.stack.length - 1 := fun e => hne (e ▸ hstk)
    have hfid : fid < cfg.stack.length - 1 := lt_of_le_of_ne (Nat.le_sub_one_of_lt (loc_stk_lt hstk)) hfidNe
    have := (oid_loc_stk_iff_in_stack (exit_valid vcfg h)).mpr ⟨frame, (exit_getElem_eq h hfid).trans hget, hmem⟩
    simp [hnone] at this

-- Anything located in `cfg'` was located away from the popped slot in `cfg`.
private theorem exit_ne_popped_of_loc' {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : exit cfg = some cfg') {oid : ObjectId} {l : Location} (hl : (Reference.OId oid).loc? cfg' = some l) :
    (Reference.OId oid).loc? cfg ≠ some (Location.Stk (cfg.stack.length - 1)) := fun hbad => by
  rcases exit_loc vcfg h (.OId oid) with heq | ⟨hnone, -⟩
  · have hlt := loc_stk_lt (heq.trans hbad)
    obtain ⟨_, _, _, _, _, _, rfl⟩ := exit_cases h
    simp at hlt
  · simp [hnone] at hl

-- OId-sourced steps agree between cfg/cfg' across `exit`, for any oid not resolving to the popped frame's slot.
private theorem exit_oid_step_iff {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : exit cfg = some cfg') (oid : ObjectId)
    (hne : (Reference.OId oid).loc? cfg ≠ some (Location.Stk (cfg.stack.length - 1))) (b : Reference) :
    ReachableStep cfg (Reference.OId oid) b ↔ ReachableStep cfg' (Reference.OId oid) b := by
  rw [ReachableStep_oid_iff, ReachableStep_oid_iff]
  suffices (Reference.OId oid).objAt? cfg = (Reference.OId oid).objAt? cfg' by rw [this]
  have hlocEq := exit_loc_eq_of_ne_popped vcfg h oid hne
  obtain ⟨p, region, -, -, hlookupRid, -, hcfg'⟩ := exit_cases h
  unfold Reference.objAt?
  dsimp only
  rw [← hlocEq]
  rcases hloc : (Reference.OId oid).loc? cfg with _ | (rid0 | fid0)
  · rfl
  · subst hcfg'
    by_cases heq : rid0 = p.regionId
    · subst heq
      simp [hlookupRid]
    · simp [AList.lookup_insert_ne heq]
  · have hfid : fid0 < cfg.stack.length - 1 :=
      lt_of_le_of_ne (Nat.le_sub_one_of_lt (loc_stk_lt hloc)) fun e => hne (e ▸ hloc)
    simp only [stackWithIndex_find_index_eq_getElem, exit_getElem_eq h hfid]

-- A not-popped-rooted chain to an object of open region `rid` transports to `cfg'` (each hop stays not-popped by H3/S2).
private theorem exit_reflTransGen_transport {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : exit cfg = some cfg') {rid : RegionId} {region : Region}
    (hlookup : cfg.heap.lookup rid = some region) (hopen : region.status = Status.Open)
    {oid : ObjectId} (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn rid))
    {start : Reference} (hrtg : Relation.ReflTransGen (ReachableStep cfg) start (Reference.OId oid)) :
    (∀ o, start = Reference.OId o → (Reference.OId o).loc? cfg ≠ some (Location.Stk (cfg.stack.length - 1))) →
    Relation.ReflTransGen (ReachableStep cfg') start (Reference.OId oid) := by
  induction hrtg using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun _ => .refl
  | @head a c hstep hrest ih =>
    intro ha
    have haSafe := safe_reflTransGen_root_safe vcfg hlookup hopen (.head hstep hrest) (Or.inl hloc)
    have hcSafe := safe_reflTransGen_root_safe vcfg hlookup hopen hrest (Or.inl hloc)
    cases a with
    | RId _ => exact haSafe.elim
    | OId oA =>
      cases c with
      | RId _ => exact hcSafe.elim
      | OId oC =>
        refine .head ((exit_oid_step_iff vcfg h oA (ha oA rfl) _).mp hstep) (ih ?_)
        rintro _ ⟨⟩ hlocC
        rcases haSafe with hlocA | ⟨fidA, hlocA⟩
        · simp [successor_of_region_object vcfg hlookup hlocA hstep] at hlocC
        · exact ha oA rfl (le_antisymm (Nat.le_sub_one_of_lt (loc_stk_lt hlocA))
            (stack_step_index_le vcfg hlocA hstep hlocC) ▸ hlocA)

-- A `FrameRoot` rooted before the popped frame never resolves to the popped slot (S2, H1).
private theorem exit_root_avoid_popped {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {fid : Index} (hlt : fid < cfg.stack.length - 1) {start : Reference} (hroot : FrameRoot cfg fid start) :
    ∀ o, start = Reference.OId o → (Reference.OId o).loc? cfg ≠ some (Location.Stk (cfg.stack.length - 1)) := by
  rintro o rfl hlocStart
  rcases hroot with ⟨Xf, hXfmem, rfl, var, hvar⟩ | ⟨Xf, -, -, region', hlookupXf, hbridge⟩
  · exact absurd (vcfg.s2 Xf hXfmem _ (mem_frame_refs_of_mem_varMap hvar) _ o rfl hlocStart) (Nat.not_le.mpr hlt)
  · cases hbridge
    rw [(oid_loc_rgn_iff_in_heap vcfg).mpr ⟨region', hlookupXf,
      vcfg.h1 region' (List.mem_map_of_mem (AList.lookup_mem_entries hlookupXf))⟩] at hlocStart
    cases hlocStart

-- Every pre-existing frame below the popped one survives `exit` unchanged, same heap entry.
theorem exit_frame_reachable_transport {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : exit cfg = some cfg') {poppedFrame : Frame} {region0 : Region}
    (hlast : cfg.stack.getLast? = some poppedFrame)
    (hcfg' : cfg' = { cfg with
      stack := cfg.stack.dropLast,
      heap := cfg.heap.insert poppedFrame.regionId { region0 with status := Status.Closed } })
    {oid : ObjectId} {rid : RegionId} {region : Region} (hlookup : cfg.heap.lookup rid = some region)
    (hopen : region.status = Status.Open) (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn rid))
    {X : FrameWithIndex} (_hXmem : X ∈ cfg.stackWithIndex) (hXlt : X.index < cfg.stack.length - 1)
    (hXreach : FrameReachable cfg X.index (Reference.OId oid)) :
    FrameReachable cfg' X.index (Reference.OId oid) := by
  obtain ⟨start, hroot, hrtg⟩ := (FrameReachable_iff_reflTransGen _ _ _).mp hXreach
  refine (FrameReachable_iff_reflTransGen _ _ _).mpr ⟨start, ?_,
    exit_reflTransGen_transport vcfg h hlookup hopen hloc hrtg (exit_root_avoid_popped vcfg hXlt hroot)⟩
  rcases hroot with ⟨Xf, hXfmem, hXfidx, var, hvar⟩ | ⟨Xf, hXfmem, hXfidx, region', hlookupXf, hbridge⟩
  · exact .inl ⟨Xf, exit_frame_mem_up h hXfmem (hXfidx ▸ hXlt), hXfidx, var, hvar⟩
  · have hne := regionId_ne_last_of_suspended vcfg hXfmem (hXfidx ▸ hXlt) hlast
    exact .inr ⟨Xf, exit_frame_mem_up h hXfmem (hXfidx ▸ hXlt), hXfidx, region',
      by rw [hcfg']; simpa [AList.lookup_insert_ne hne] using hlookupXf, hbridge⟩

-- A `cfg'`-chain to a safe ref transports to `cfg`: every safe predecessor is located in `cfg'`, hence not popped.
private theorem exit_reflTransGen_transport_backward {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : exit cfg = some cfg') {rid : RegionId} {region : Region}
    (hlookup' : cfg'.heap.lookup rid = some region) (hopen : region.status = Status.Open)
    {start ref : Reference} (hrtg : Relation.ReflTransGen (ReachableStep cfg') start ref) :
    SafeRef cfg' rid ref → Relation.ReflTransGen (ReachableStep cfg) start ref := by
  induction hrtg with
  | refl => exact fun _ => .refl
  | @tail prev cur _ hstep ih =>
    intro hsafe
    have hprev := predecessor_safe (exit_valid vcfg h) hlookup' hopen hsafe hstep
    cases prev with
    | RId _ => exact hprev.elim
    | OId o =>
      have hne : (Reference.OId o).loc? cfg ≠ some (Location.Stk (cfg.stack.length - 1)) := by
        rcases hprev with hl | ⟨_, hl⟩ <;> exact exit_ne_popped_of_loc' vcfg h hl
      exact (ih hprev).tail ((exit_oid_step_iff vcfg h o hne cur).mpr hstep)

-- Backward analogue of `exit_frame_reachable_transport`: reachability in `cfg'` transports down to `cfg`.
theorem exit_frame_reachable_transport_backward {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : exit cfg = some cfg') {poppedFrame : Frame} {region0 : Region}
    (hlast : cfg.stack.getLast? = some poppedFrame)
    (hcfg' : cfg' = { cfg with
      stack := cfg.stack.dropLast,
      heap := cfg.heap.insert poppedFrame.regionId { region0 with status := Status.Closed } })
    {oid : ObjectId} {rid : RegionId} {region : Region} (_hlookup : cfg.heap.lookup rid = some region)
    (hlookup' : cfg'.heap.lookup rid = some region) (hopen : region.status = Status.Open)
    (hloc' : (Reference.OId oid).loc? cfg' = some (Location.Rgn rid))
    {X : FrameWithIndex} (_hXmem : X ∈ cfg'.stackWithIndex)
    (hXreach : FrameReachable cfg' X.index (Reference.OId oid)) :
    FrameReachable cfg X.index (Reference.OId oid) := by
  obtain ⟨start, hroot, hrtg⟩ := (FrameReachable_iff_reflTransGen _ _ _).mp hXreach
  refine (FrameReachable_iff_reflTransGen _ _ _).mpr ⟨start, ?_,
    exit_reflTransGen_transport_backward vcfg h hlookup' hopen hrtg (Or.inl hloc')⟩
  rcases hroot with ⟨Xf, hXfmem, hXfidx, var, hvar⟩ | ⟨Xf, hXfmem, hXfidx, region', hlookupXf, hbridge⟩
  · exact .inl ⟨Xf, (exit_frame_mem_down h hXfmem).1, hXfidx, var, hvar⟩
  · obtain ⟨hm, hl⟩ := exit_frame_mem_down h hXfmem
    rw [hcfg'] at hlookupXf
    exact .inr ⟨Xf, hm, hXfidx, region',
      by simpa [AList.lookup_insert_ne (regionId_ne_last_of_suspended vcfg hm hl hlast)] using hlookupXf, hbridge⟩

-- For `oid` in a suspended frame's region, `exit` preserves frame-reachability from every surviving frame.
theorem exit_suspended_reach {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg) (h : exit cfg = some cfg')
    {F : FrameWithIndex} (hF : F ∈ cfg.stackWithIndex) (hFlt : F.index < cfg.stack.length - 1) {oid : ObjectId}
    (hloc' : (Reference.OId oid).loc? cfg' = some (Location.Rgn F.regionId)) :
    (Reference.OId oid).loc? cfg = some (Location.Rgn F.regionId) ∧
    ∀ X ∈ cfg.stackWithIndex, X.index < cfg.stack.length - 1 →
      (FrameReachable cfg X.index (.OId oid) ↔ FrameReachable cfg' X.index (.OId oid)) := by
  obtain ⟨p, r0, -, hlast, -, -, hcfg'⟩ := exit_cases h
  obtain ⟨region, hlookup, hopen⟩ := l2_of_stackWithIndex vcfg hF
  have hlookup' : cfg'.heap.lookup F.regionId = some region := by
    rw [hcfg']; dsimp only
    rw [AList.lookup_insert_ne (regionId_ne_last_of_suspended vcfg hF hFlt hlast)]; exact hlookup
  have hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn F.regionId) := by
    rw [oid_loc_rgn_iff_in_heap vcfg]
    rw [oid_loc_rgn_iff_in_heap (exit_valid vcfg h)] at hloc'
    obtain ⟨r1, hl1, hm1⟩ := hloc'
    rw [hlookup'] at hl1
    cases hl1
    exact ⟨region, hlookup, hm1⟩
  exact ⟨hloc, fun X hX hXlt => ⟨fun hr => exit_frame_reachable_transport vcfg h hlast hcfg' hlookup hopen hloc hX hXlt hr,
    fun hr => exit_frame_reachable_transport_backward vcfg h hlast hcfg' hlookup hlookup' hopen hloc'
      (exit_frame_mem_up h hX hXlt) hr⟩⟩
