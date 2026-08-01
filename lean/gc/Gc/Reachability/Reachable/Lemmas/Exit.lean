import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Mutation.Mutation
import Gc.Model.Preservation
import Gc.Reachability.Reachable.Semantics
import Gc.Reachability.Reachable.Lemmas.Common
import Gc.Reachability.Reachable.Lemmas.Enter

-- A pre-existing, non-popped frame survives `exit` unchanged, at the same index.
theorem exit_frame_mem_up {cfg cfg' : RuntimeConfig} (h : exit cfg = some cfg')
    {frame : FrameWithIndex} (hframe : frame ∈ cfg.stackWithIndex) (hlt : frame.index < cfg.stack.length - 1) :
    frame ∈ cfg'.stackWithIndex := by
  obtain ⟨poppedFrame, region, hlen, hlast, hlookupRid, hopenRid, hcfg'⟩ := exit_cases h
  subst hcfg'
  unfold RuntimeConfig.stackWithIndex at hframe ⊢
  dsimp only
  obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hframe
  have hidx : frame.index = n := by rw [← hfeq]
  have hnlt : n < cfg.stack.dropLast.length := by rw [List.length_dropLast]; rw [hidx] at hlt; exact hlt
  apply List.mem_mapIdx.mpr
  refine ⟨n, hnlt, ?_⟩
  have hget : cfg.stack.dropLast[n] = cfg.stack[n] := List.getElem_dropLast hnlt
  rw [hget]
  exact hfeq

-- Every `cfg'.stackWithIndex` member was already in `cfg`, with index below the popped frame's.
theorem exit_frame_mem_down {cfg cfg' : RuntimeConfig} (h : exit cfg = some cfg')
    {frame : FrameWithIndex} (hframe : frame ∈ cfg'.stackWithIndex) :
    frame ∈ cfg.stackWithIndex ∧ frame.index < cfg.stack.length - 1 := by
  obtain ⟨poppedFrame, region, hlen, hlast, hlookupRid, hopenRid, hcfg'⟩ := exit_cases h
  subst hcfg'
  unfold RuntimeConfig.stackWithIndex at hframe ⊢
  dsimp only at hframe
  refine ⟨List.mem_of_mem_dropLast_mapIdx hframe, ?_⟩
  obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hframe
  have hidx : frame.index = n := by rw [← hfeq]
  rw [hidx, ← List.length_dropLast]
  exact hn

-- The popped frame itself, viewed as a `FrameWithIndex` at the last index.
theorem exit_poppedFrame_mem {cfg : RuntimeConfig} {poppedFrame : Frame}
    (hlast : cfg.stack.getLast? = some poppedFrame) (hlen : cfg.stack.length ≥ 2) :
    ∃ f : FrameWithIndex, f ∈ cfg.stackWithIndex ∧ f.toFrame = poppedFrame ∧
      f.index = cfg.stack.length - 1 := by
  have hne : cfg.stack ≠ [] := by intro hnil; rw [hnil] at hlen; simp at hlen
  rw [List.getLast?_eq_getLast_of_ne_nil hne, Option.some_inj] at hlast
  have hgetElem : cfg.stack[cfg.stack.length - 1] = poppedFrame := by
    rw [← hlast]
    exact (List.getLast_eq_getElem hne).symm
  refine ⟨{ toFrame := poppedFrame, index := cfg.stack.length - 1 }, ?_, rfl, rfl⟩
  unfold RuntimeConfig.stackWithIndex
  apply List.mem_mapIdx.mpr
  refine ⟨cfg.stack.length - 1, by omega, ?_⟩
  dsimp only
  rw [hgetElem]

-- A frame before the popped one has a different regionId (S1: injective across the stack).
theorem exit_regionId_ne {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {f : FrameWithIndex} (hf : f ∈ cfg.stackWithIndex) (hflt : f.index < cfg.stack.length - 1)
    {poppedFrame : Frame} (hlast : cfg.stack.getLast? = some poppedFrame) (hlen : cfg.stack.length ≥ 2) :
    f.regionId ≠ poppedFrame.regionId := by
  intro heq
  obtain ⟨fp, hfpMem, hfpEq, hfpIdx⟩ := exit_poppedFrame_mem hlast hlen
  have hregEq : f.regionId = fp.regionId := by rw [hfpEq]; exact heq
  have hidxEq : f.index = fp.index := merge_corollary_regionId_unique_index vcfg.s1 hf hfpMem hregEq
  rw [hfpIdx] at hidxEq
  rw [hidxEq] at hflt
  exact absurd hflt (lt_irrefl _)

-- If `a` avoids the popped slot and steps to `c` (both `SafeRef`), so does `c`: region hops stay in-region, stack hops only decrease index (S2).
theorem exit_avoid_popped_step {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid : RegionId} {region : Region} (hlookup : cfg.heap.lookup rid = some region)
    {poppedIdx : Index} (hpoppedIdx : poppedIdx = cfg.stack.length - 1)
    {a c : Reference} (haSafe : SafeRef cfg rid a) (hcSafe : SafeRef cfg rid c)
    (hstep : ReachableStep cfg a c)
    {oidA : ObjectId} (haEq : a = Reference.OId oidA)
    (haNe : (Reference.OId oidA).loc? cfg ≠ some (Location.Stk poppedIdx))
    {oidC : ObjectId} (hcEq : c = Reference.OId oidC) :
    (Reference.OId oidC).loc? cfg ≠ some (Location.Stk poppedIdx) := by
  intro hlocC
  subst haEq; subst hcEq
  unfold SafeRef at haSafe
  rcases haSafe with hlocA | ⟨fidA, hlocA⟩
  · have := successor_of_region_object vcfg hlookup hlocA hstep
    rw [hlocC] at this
    simp at this
  · have hfidNe : fidA ≠ poppedIdx := by intro heq; rw [heq] at hlocA; exact haNe hlocA
    have hle1 : poppedIdx ≤ fidA := stack_step_index_le vcfg hlocA hstep hlocC
    have hle2 : fidA < cfg.stack.length := loc_stk_lt hlocA
    subst hpoppedIdx
    exact hfidNe (le_antisymm (Nat.le_sub_one_of_lt hle2) hle1)

-- `find? (index == fid)` over `stackWithIndex` agrees between `cfg`/`cfg'` for any surviving index.
theorem exit_stack_find_index_eq {cfg cfg' : RuntimeConfig} (h : exit cfg = some cfg')
    (fid : Index) (hfid : fid < cfg.stack.length - 1) :
    cfg.stackWithIndex.find? (fun frame => frame.index == fid) =
    cfg'.stackWithIndex.find? (fun frame => frame.index == fid) := by
  have hfid' : fid < cfg.stack.length := lt_of_lt_of_le hfid (Nat.sub_le _ _)
  have hmem : ({ toFrame := cfg.stack[fid], index := fid } : FrameWithIndex) ∈ cfg.stackWithIndex :=
    List.mem_mapIdx.mpr ⟨fid, hfid', rfl⟩
  have hmem' : ({ toFrame := cfg.stack[fid], index := fid } : FrameWithIndex) ∈ cfg'.stackWithIndex :=
    exit_frame_mem_up h hmem hfid
  rw [swap_corollary_stackWithIndex_find_eq hmem, swap_corollary_stackWithIndex_find_eq hmem']

-- `loc?` agrees between `cfg`/`cfg'` for any oid not resolving to the popped frame's slot.
theorem exit_loc_eq_of_ne_popped {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : exit cfg = some cfg') (oid : ObjectId)
    (hne : (Reference.OId oid).loc? cfg ≠ some (Location.Stk (cfg.stack.length - 1))) :
    (Reference.OId oid).loc? cfg = (Reference.OId oid).loc? cfg' := by
  obtain ⟨poppedFrame, region, hlen, hlast, hlookupRid, hopenRid, hcfg'⟩ := exit_cases h
  cases hloc : (Reference.OId oid).loc? cfg with
  | none =>
    symm
    by_contra hcontra
    obtain ⟨loc, hloc'⟩ := Option.ne_none_iff_exists'.mp hcontra
    cases loc with
    | Rgn rid0 =>
      have := (exit_corollary_1 vcfg h (Reference.OId oid)).mpr hloc'
      rw [hloc] at this; exact absurd this (by simp)
    | Stk fid0 =>
      have := exit_corollary_3 vcfg h (Reference.OId oid) hloc'
      rw [hloc] at this; exact absurd this (by simp)
  | some loc =>
    cases loc with
    | Rgn rid0 => exact ((exit_corollary_1 vcfg h (Reference.OId oid)).mp hloc).symm
    | Stk fid0 =>
      have hfidNe : fid0 ≠ cfg.stack.length - 1 := by intro heq; rw [heq] at hloc; exact hne hloc
      obtain ⟨frame, hget, hobjmem⟩ := (oid_loc_stk_iff_in_stack vcfg).mp hloc
      have hmem : frame ∈ cfg.stackWithIndex := List.mem_of_getElem? hget
      have hidx : frame.index = fid0 := stackWithIndex_getElem_index_eq hget
      have hlt : frame.index < cfg.stack.length := by
        rw [hidx]
        have hlt0 : fid0 < cfg.stackWithIndex.length := (List.getElem?_eq_some_iff.mp hget).1
        unfold RuntimeConfig.stackWithIndex at hlt0
        rwa [List.length_mapIdx] at hlt0
      have hidxNe : frame.index ≠ cfg.stack.length - 1 := by rw [hidx]; exact hfidNe
      have hflt : frame.index < cfg.stack.length - 1 :=
        lt_of_le_of_ne (Nat.le_sub_one_of_lt hlt) hidxNe
      have hmem' : frame ∈ cfg'.stackWithIndex := exit_frame_mem_up h hmem hflt
      have hget' : cfg'.stackWithIndex[frame.index]? = some frame := stackWithIndex_mem_getElem_eq hmem'
      rw [hidx] at hget'
      have vcfg' : ValidConfig cfg' := exit_valid vcfg h
      exact ((oid_loc_stk_iff_in_stack vcfg').mpr ⟨frame, hget', hobjmem⟩).symm

-- `objAt?` agrees between `cfg`/`cfg'` for any oid not resolving to the popped frame's slot.
theorem exit_objAt_eq_of_ne_popped {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : exit cfg = some cfg') (oid : ObjectId)
    (hne : (Reference.OId oid).loc? cfg ≠ some (Location.Stk (cfg.stack.length - 1))) :
    (Reference.OId oid).objAt? cfg = (Reference.OId oid).objAt? cfg' := by
  obtain ⟨poppedFrame, region, hlen, hlast, hlookupRid, hopenRid, hcfg'⟩ := exit_cases h
  have hlocEq := exit_loc_eq_of_ne_popped vcfg h oid hne
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
      by_cases heq : rid0 = poppedFrame.regionId
      · subst heq
        rw [AList.lookup_insert, hlookupRid]
        rfl
      · rw [AList.lookup_insert_ne heq]
    | Stk fid0 =>
      dsimp only
      have hloc : (Reference.OId oid).loc? cfg = some (Location.Stk fid0) := by rw [hlocEq]; exact hloc'
      have hfidNe : fid0 ≠ cfg.stack.length - 1 := by
        intro heqfid; rw [heqfid] at hloc; exact hne hloc
      have hfid : fid0 < cfg.stack.length - 1 := by
        have hfidLt : fid0 < cfg.stack.length := loc_stk_lt hloc
        exact lt_of_le_of_ne (Nat.le_sub_one_of_lt hfidLt) hfidNe
      rw [exit_stack_find_index_eq h fid0 hfid]

-- OId-sourced steps agree between cfg/cfg' across `exit`, for any oid not resolving to the popped frame's slot.
theorem exit_oid_step_iff_of_ne_popped {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : exit cfg = some cfg') (oid : ObjectId)
    (hne : (Reference.OId oid).loc? cfg ≠ some (Location.Stk (cfg.stack.length - 1))) (b : Reference) :
    ReachableStep cfg (Reference.OId oid) b ↔ ReachableStep cfg' (Reference.OId oid) b := by
  rw [ReachableStep_oid_iff, ReachableStep_oid_iff, exit_objAt_eq_of_ne_popped vcfg h oid hne]

-- Combines `safe_reflTransGen_root_safe`, `exit_avoid_popped_step`, and `exit_oid_step_iff_of_ne_popped`: a not-popped-rooted chain to safe `oid` transports to `cfg'`.
theorem exit_reflTransGen_transport {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : exit cfg = some cfg') {rid : RegionId} {region : Region}
    (hlookup : cfg.heap.lookup rid = some region) (hopen : region.status = Status.Open)
    {oid : ObjectId} (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn rid))
    {start : Reference} (hrtg : Relation.ReflTransGen (ReachableStep cfg) start (Reference.OId oid)) :
    (∀ oidStart, start = Reference.OId oidStart →
      (Reference.OId oidStart).loc? cfg ≠ some (Location.Stk (cfg.stack.length - 1))) →
    Relation.ReflTransGen (ReachableStep cfg') start (Reference.OId oid) := by
  induction hrtg using Relation.ReflTransGen.head_induction_on with
  | refl => intro _; exact Relation.ReflTransGen.refl
  | @head a c hstep hrest ih =>
    intro haNotPopped
    have haSafe : SafeRef cfg rid a :=
      safe_reflTransGen_root_safe vcfg hlookup hopen (Relation.ReflTransGen.head hstep hrest) (Or.inl hloc)
    have hcSafe : SafeRef cfg rid c := safe_reflTransGen_root_safe vcfg hlookup hopen hrest (Or.inl hloc)
    cases a with
    | RId _ => exact absurd haSafe (by unfold SafeRef; exact id)
    | OId oidA =>
      have haNe := haNotPopped oidA rfl
      cases c with
      | RId _ => exact absurd hcSafe (by unfold SafeRef; exact id)
      | OId oidC =>
        have hcNe := exit_avoid_popped_step vcfg hlookup rfl haSafe hcSafe hstep rfl haNe rfl
        have hchain' := ih (fun oidC' hcEq => by
          rw [Reference.OId.injEq] at hcEq; rw [← hcEq]; exact hcNe)
        exact Relation.ReflTransGen.head ((exit_oid_step_iff_of_ne_popped vcfg h oidA haNe (Reference.OId oidC)).mp hstep) hchain'

-- A `FrameRoot` rooted before the popped frame never resolves to the popped slot (S2).
theorem exit_root_avoid_popped {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {X : FrameWithIndex} (hXmem : X ∈ cfg.stackWithIndex) (hXlt : X.index < cfg.stack.length - 1)
    {start : Reference} (hroot : FrameRoot cfg X.index start) :
    ∀ oidStart, start = Reference.OId oidStart →
      (Reference.OId oidStart).loc? cfg ≠ some (Location.Stk (cfg.stack.length - 1)) := by
  intro oidStart hstartEq hlocStart
  rcases hroot with ⟨Xf, hXfmem, hXfidx, var, hvar⟩ | ⟨Xf, hXfmem, hXfidx, region', hlookupXf, hbridge⟩
  · have hXfeq : Xf = X := swap_corollary_stackWithIndex_index_inj hXfmem hXmem hXfidx
    rw [hXfeq, hstartEq] at hvar
    have hmemrefs : (Reference.OId oidStart) ∈ X.refs := mem_frame_refs_of_mem_varMap hvar
    have hle := vcfg.s2 X hXmem (Reference.OId oidStart) hmemrefs (cfg.stack.length - 1) oidStart rfl hlocStart
    exact absurd hle (Nat.not_le.mpr hXlt)
  · rw [hstartEq] at hbridge
    injection hbridge with hbeq
    rw [hbeq] at hlocStart
    have hbridgeMem : region' ∈ cfg.heap.regions := by
      unfold Heap.regions
      exact List.mem_map_of_mem (AList.lookup_mem_entries hlookupXf)
    have hbridgeIn : region'.bridgeObjectId ∈ region'.objMap := vcfg.h1 region' hbridgeMem
    have hbridgeLoc : (Reference.OId region'.bridgeObjectId).loc? cfg = some (Location.Rgn Xf.regionId) :=
      (oid_loc_rgn_iff_in_heap vcfg).mpr ⟨region', hlookupXf, hbridgeIn⟩
    rw [hlocStart] at hbridgeLoc
    simp at hbridgeLoc

-- Every pre-existing frame below the popped one survives `exit` unchanged, same heap entry.
theorem exit_frame_reachable_transport {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : exit cfg = some cfg') {poppedFrame : Frame} {region0 : Region}
    (hlast : cfg.stack.getLast? = some poppedFrame) (hlen : cfg.stack.length ≥ 2)
    (_hlookupRid : cfg.heap.lookup poppedFrame.regionId = some region0) (_hopenRid : region0.status = Status.Open)
    (hcfg' : cfg' = { cfg with
      stack := cfg.stack.dropLast,
      heap := cfg.heap.insert poppedFrame.regionId { region0 with status := Status.Closed } })
    {oid : ObjectId} {rid : RegionId} {region : Region} (hlookup : cfg.heap.lookup rid = some region)
    (hopen : region.status = Status.Open) (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn rid))
    {X : FrameWithIndex} (hXmem : X ∈ cfg.stackWithIndex) (hXlt : X.index < cfg.stack.length - 1)
    (hXreach : FrameReachable cfg X.index (Reference.OId oid)) :
    FrameReachable cfg' X.index (Reference.OId oid) := by
  rw [FrameReachable_iff_reflTransGen] at hXreach
  obtain ⟨start, hroot, hrtg⟩ := hXreach
  have hstartAvoid := exit_root_avoid_popped vcfg hXmem hXlt hroot
  have hrtg' := exit_reflTransGen_transport vcfg h hlookup hopen hloc hrtg hstartAvoid
  have hXridNe : X.regionId ≠ poppedFrame.regionId := exit_regionId_ne vcfg hXmem hXlt hlast hlen
  have hroot' : FrameRoot cfg' X.index start := by
    rcases hroot with ⟨Xf, hXfmem, hXfidx, var, hvar⟩ | ⟨Xf, hXfmem, hXfidx, region', hlookupXf, hbridge⟩
    · exact Or.inl ⟨Xf, (exit_frame_mem_up h hXfmem (hXfidx ▸ hXlt)), hXfidx, var, hvar⟩
    · have hXfeq : Xf = X := swap_corollary_stackWithIndex_index_inj hXfmem hXmem hXfidx
      have hXfridNe : Xf.regionId ≠ poppedFrame.regionId := hXfeq ▸ hXridNe
      have hlookupXf' : cfg'.heap.lookup Xf.regionId = some region' := by
        rw [hcfg']
        dsimp only
        rwa [AList.lookup_insert_ne hXfridNe]
      exact Or.inr ⟨Xf, exit_frame_mem_up h hXfmem (hXfidx ▸ hXlt), hXfidx, region', hlookupXf', hbridge⟩
  exact (FrameReachable_iff_reflTransGen cfg' X.index (Reference.OId oid)).mpr ⟨start, hroot', hrtg'⟩

-- Anything stack-resident in `cfg'` also avoids the popped slot in `cfg` (`loc?` is a function, frame survives unchanged).
theorem exit_stk_not_popped_of_cfg' {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : exit cfg = some cfg') (oid : ObjectId) {fid : Index}
    (hloc' : (Reference.OId oid).loc? cfg' = some (Location.Stk fid)) :
    (Reference.OId oid).loc? cfg ≠ some (Location.Stk (cfg.stack.length - 1)) := by
  intro hbad
  have vcfg' : ValidConfig cfg' := exit_valid vcfg h
  obtain ⟨frameC, hgetC, hobjmemC⟩ := (oid_loc_stk_iff_in_stack vcfg').mp hloc'
  have hmemC : frameC ∈ cfg'.stackWithIndex := List.mem_of_getElem? hgetC
  have hidxC : frameC.index = fid := stackWithIndex_getElem_index_eq hgetC
  have hmemCcfg : frameC ∈ cfg.stackWithIndex := (exit_frame_mem_down h hmemC).1
  have hgetCcfg : cfg.stackWithIndex[frameC.index]? = some frameC := stackWithIndex_mem_getElem_eq hmemCcfg
  have hlocC : (Reference.OId oid).loc? cfg = some (Location.Stk frameC.index) :=
    (oid_loc_stk_iff_in_stack vcfg).mpr ⟨frameC, hgetCcfg, hobjmemC⟩
  rw [hbad] at hlocC
  injection hlocC with hlocC
  injection hlocC with hlocC
  rw [hidxC] at hlocC
  have hfidlt : frameC.index < cfg.stack.length - 1 := (exit_frame_mem_down h hmemC).2
  rw [hidxC, hlocC] at hfidlt
  exact absurd hfidlt (lt_irrefl _)

-- Anything resolving into an untouched region in `cfg'` also avoids the popped slot in `cfg` (`Rgn`/`Stk` are different shapes).
theorem exit_rgn_not_popped {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg) (vcfg' : ValidConfig cfg')
    {rid : RegionId} {region : Region} (hlookup : cfg.heap.lookup rid = some region)
    (hlookup' : cfg'.heap.lookup rid = some region)
    (oidX : ObjectId) (hlocX : (Reference.OId oidX).loc? cfg' = some (Location.Rgn rid)) :
    (Reference.OId oidX).loc? cfg ≠ some (Location.Stk (cfg.stack.length - 1)) := by
  intro hbad
  obtain ⟨region', hlookup'', hmemX⟩ := (oid_loc_rgn_iff_in_heap vcfg').mp hlocX
  rw [hlookup'] at hlookup''
  injection hlookup'' with hregionEq
  rw [← hregionEq] at hmemX
  have hlocXcfg : (Reference.OId oidX).loc? cfg = some (Location.Rgn rid) :=
    (oid_loc_rgn_iff_in_heap vcfg).mpr ⟨region, hlookup, hmemX⟩
  rw [hbad] at hlocXcfg
  simp at hlocXcfg

-- Backward direction: a `cfg'`-chain to a safe ref transports to `cfg`; "not popped" is derivable locally at every step, no monotonicity needed.
theorem exit_reflTransGen_transport_backward {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : exit cfg = some cfg') {rid : RegionId} {region : Region}
    (hlookup : cfg.heap.lookup rid = some region) (hlookup' : cfg'.heap.lookup rid = some region)
    (hopen : region.status = Status.Open)
    {start ref : Reference} (hrtg : Relation.ReflTransGen (ReachableStep cfg') start ref) :
    SafeRef cfg' rid ref → Relation.ReflTransGen (ReachableStep cfg) start ref := by
  have vcfg' : ValidConfig cfg' := exit_valid vcfg h
  induction hrtg with
  | refl => intro _; exact Relation.ReflTransGen.refl
  | tail hprev hstep ih =>
    rename_i prev cur
    intro hsafe
    have hsafePrev := predecessor_safe vcfg' hlookup' hopen hsafe hstep
    have hchainPrev := ih hsafePrev
    cases prev with
    | RId _ => exact absurd hsafePrev (by unfold SafeRef; exact id)
    | OId oidPrev =>
      have hne : (Reference.OId oidPrev).loc? cfg ≠ some (Location.Stk (cfg.stack.length - 1)) := by
        unfold SafeRef at hsafePrev
        rcases hsafePrev with hloc | ⟨fid, hloc⟩
        · exact exit_rgn_not_popped vcfg vcfg' hlookup hlookup' oidPrev hloc
        · exact exit_stk_not_popped_of_cfg' vcfg h oidPrev hloc
      exact hchainPrev.tail ((exit_oid_step_iff_of_ne_popped vcfg h oidPrev hne cur).mpr hstep)

-- Mirrors `exit_frame_reachable_transport`, backward: reachability transports down to `cfg`.
theorem exit_frame_reachable_transport_backward {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : exit cfg = some cfg') {poppedFrame : Frame} {region0 : Region}
    (hlast : cfg.stack.getLast? = some poppedFrame) (hlen : cfg.stack.length ≥ 2)
    (hcfg' : cfg' = { cfg with
      stack := cfg.stack.dropLast,
      heap := cfg.heap.insert poppedFrame.regionId { region0 with status := Status.Closed } })
    {oid : ObjectId} {rid : RegionId} {region : Region} (hlookup : cfg.heap.lookup rid = some region)
    (hlookup' : cfg'.heap.lookup rid = some region) (hopen : region.status = Status.Open)
    (hloc' : (Reference.OId oid).loc? cfg' = some (Location.Rgn rid))
    {X : FrameWithIndex} (hXmem : X ∈ cfg'.stackWithIndex)
    (hXreach : FrameReachable cfg' X.index (Reference.OId oid)) :
    FrameReachable cfg X.index (Reference.OId oid) := by
  rw [FrameReachable_iff_reflTransGen] at hXreach
  obtain ⟨start, hroot, hrtg⟩ := hXreach
  have hsafe : SafeRef cfg' rid (Reference.OId oid) := Or.inl hloc'
  have hrtg' := exit_reflTransGen_transport_backward vcfg h hlookup hlookup' hopen hrtg hsafe
  obtain ⟨hXmemcfg, hXlt⟩ := exit_frame_mem_down h hXmem
  have hXridNe : X.regionId ≠ poppedFrame.regionId := exit_regionId_ne vcfg hXmemcfg hXlt hlast hlen
  have hroot' : FrameRoot cfg X.index start := by
    rcases hroot with ⟨Xf, hXfmem, hXfidx, var, hvar⟩ | ⟨Xf, hXfmem, hXfidx, region', hlookupXf, hbridge⟩
    · have hXfeq : Xf = X := swap_corollary_stackWithIndex_index_inj hXfmem hXmem hXfidx
      exact Or.inl ⟨Xf, (hXfeq ▸ hXmemcfg), hXfidx, var, hvar⟩
    · have hXfeq : Xf = X := swap_corollary_stackWithIndex_index_inj hXfmem hXmem hXfidx
      have hXfridNe : Xf.regionId ≠ poppedFrame.regionId := hXfeq ▸ hXridNe
      have hlookupXf' : cfg.heap.lookup Xf.regionId = some region' := by
        rw [hcfg'] at hlookupXf
        dsimp only at hlookupXf
        rwa [AList.lookup_insert_ne hXfridNe] at hlookupXf
      exact Or.inr ⟨Xf, hXfeq ▸ hXmemcfg, hXfidx, region', hlookupXf', hbridge⟩
  exact (FrameReachable_iff_reflTransGen cfg X.index (Reference.OId oid)).mpr ⟨start, hroot', hrtg'⟩
