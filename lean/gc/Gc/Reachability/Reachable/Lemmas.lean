import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Mutation.Mutation
import Gc.Model.Preservation
import Gc.Reachability.Reachable.Semantics
import Gc.Reachability.Reachable.Corollaries

-- Helper lemmas for Scratch.lean, re-derived independently of Gc.Reachability.Referencable.

-- An object's own refs contribute to its region's overall refs.
theorem mem_region_refs_of_mem_objMap {region : Region} {oid : ObjectId} {obj : Object}
    (hlookup : region.objMap.lookup oid = some obj) {b : Reference} (hb : b ∈ obj.refs) :
    b ∈ region.refs := by
  unfold Region.refs
  rw [List.bind_eq_flatMap, List.mem_flatMap]
  exact ⟨obj, List.mem_map_of_mem (AList.lookup_mem_entries hlookup), hb⟩

-- An object's own refs contribute to its holding frame's overall refs.
theorem mem_frame_refs_of_mem_objMap {frame : Frame} {oid : ObjectId} {obj : Object}
    (hlookup : frame.objMap.lookup oid = some obj) {b : Reference} (hb : b ∈ obj.refs) :
    b ∈ frame.refs := by
  unfold Frame.refs
  rw [List.bind_eq_flatMap, List.mem_append, List.mem_flatMap]
  exact Or.inl ⟨obj, List.mem_map_of_mem (AList.lookup_mem_entries hlookup), hb⟩

-- S2, restated at the `ReachableStep` level: a stack-to-stack hop never increases the
-- owning frame's index (a frame can only reference itself or an earlier stack slot).
theorem stack_step_index_le {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {oid oid' : ObjectId} {fidCur fidNext : Index}
    (hloc : (Reference.OId oid).loc? cfg = some (Location.Stk fidCur))
    (hstep : ReachableStep cfg (Reference.OId oid) (Reference.OId oid'))
    (hloc' : (Reference.OId oid').loc? cfg = some (Location.Stk fidNext)) :
    fidNext ≤ fidCur := by
  rw [ReachableStep_oid_iff] at hstep
  obtain ⟨obj, hobjAt, hcontains⟩ := hstep
  unfold Reference.objAt? at hobjAt
  dsimp only at hobjAt
  rw [hloc] at hobjAt
  dsimp only at hobjAt
  cases hfind : cfg.stackWithIndex.find? (fun frame => frame.index == fidCur) with
  | none => rw [hfind] at hobjAt; simp at hobjAt
  | some someFrame =>
    rw [hfind] at hobjAt
    have hidxEq : someFrame.index = fidCur := by
      have := List.find?_some hfind
      exact beq_iff_eq.mp this
    have hmem : someFrame ∈ cfg.stackWithIndex := List.mem_of_find?_eq_some hfind
    have hmemrefs : (Reference.OId oid') ∈ someFrame.refs :=
      mem_frame_refs_of_mem_objMap hobjAt (List.contains_iff_mem.mp hcontains)
    have := vcfg.s2 someFrame hmem (Reference.OId oid') hmemrefs fidNext oid' rfl hloc'
    rw [hidxEq] at this
    exact this

-- L2's per-frame fact, restated directly in terms of `FrameWithIndex.regionId`.
theorem l2_of_stackWithIndex {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {frame : FrameWithIndex} (hframe : frame ∈ cfg.stackWithIndex) :
    ∃ region, cfg.heap.lookup frame.regionId = some region ∧ region.status = Status.Open := by
  obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hframe
  have hmemstack : cfg.stack[n] ∈ cfg.stack := List.getElem_mem hn
  have hfeq2 : cfg.stack[n].regionId = frame.regionId := congrArg (·.regionId) hfeq
  obtain ⟨region, hlookup, hopen⟩ := vcfg.l2 cfg.stack[n] hmemstack
  rw [hfeq2] at hlookup
  exact ⟨region, hlookup, hopen⟩

-- No successful ReachableStep can be sourced from the RId of an Open region (guard in
-- `deref?`'s RId branch requires Closed).
theorem open_rid_no_step {cfg : RuntimeConfig} {rid : RegionId} {region : Region}
    (hlookup : cfg.heap.lookup rid = some region) (hopen : region.status = Status.Open)
    {b : Reference} : ¬ ReachableStep cfg (Reference.RId rid) b := by
  rw [ReachableStep_rid_iff]
  rintro ⟨region', hlookup', hclosed', -⟩
  rw [hlookup] at hlookup'
  injection hlookup' with heq
  rw [← heq, hopen] at hclosed'
  exact absurd hclosed' (by decide)

-- Every predecessor of an object located inside an Open region is either another object
-- also inside that same region, or a stack-resident object (never an RId-crossing hop,
-- since that always requires a Closed target; never an OId from a *different* region,
-- since H3 confines a region's own internal refs back into itself).
theorem predecessor_of_region_object {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid : RegionId} {region : Region} (hlookup : cfg.heap.lookup rid = some region)
    (hopen : region.status = Status.Open) {oid : ObjectId}
    (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn rid))
    {a : Reference} (hstep : ReachableStep cfg a (Reference.OId oid)) :
    ∃ oid', a = Reference.OId oid' ∧
      ((Reference.OId oid').loc? cfg = some (Location.Rgn rid) ∨
       ∃ fid, (Reference.OId oid').loc? cfg = some (Location.Stk fid)) := by
  cases a with
  | RId rid' =>
    exact absurd hstep (by
      by_cases heq : rid' = rid
      · subst heq; exact open_rid_no_step hlookup hopen
      · intro hstep'
        rw [ReachableStep_rid_iff] at hstep'
        obtain ⟨region', hlookup', -, obj, hobjlookup, hcontains⟩ := hstep'
        have hmemrefs : (Reference.OId oid) ∈ region'.refs :=
          mem_region_refs_of_mem_objMap hobjlookup (List.contains_iff_mem.mp hcontains)
        have hloc' := vcfg.h3 rid' oid region' hlookup' hmemrefs
        rw [hloc] at hloc'
        injection hloc' with hridEq
        injection hridEq with hridEq
        exact heq hridEq.symm)
  | OId oid' =>
    refine ⟨oid', rfl, ?_⟩
    rw [ReachableStep_oid_iff] at hstep
    obtain ⟨obj, hobjAt, hcontains⟩ := hstep
    unfold Reference.objAt? at hobjAt
    dsimp only at hobjAt
    cases hloc' : (Reference.OId oid').loc? cfg with
    | none => rw [hloc'] at hobjAt; simp at hobjAt
    | some loc =>
      rw [hloc'] at hobjAt
      cases loc with
      | Rgn rid' =>
        dsimp only at hobjAt
        cases hlookup' : cfg.heap.lookup rid' with
        | none => rw [hlookup'] at hobjAt; simp at hobjAt
        | some region' =>
          rw [hlookup'] at hobjAt
          have hmemrefs : (Reference.OId oid) ∈ region'.refs :=
            mem_region_refs_of_mem_objMap hobjAt (List.contains_iff_mem.mp hcontains)
          have hridEq := vcfg.h3 rid' oid region' hlookup' hmemrefs
          rw [hloc] at hridEq
          injection hridEq with hridEq
          injection hridEq with hridEq
          left; rw [hridEq]
      | Stk fid => right; exact ⟨fid, rfl⟩

-- Every predecessor of a stack-resident object is also stack-resident (H3 rules out any
-- heap-region object -- bridge or not -- ever pointing at a stack-resident target).
theorem predecessor_of_stack_object {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {oid : ObjectId} {fid : Index} (hloc : (Reference.OId oid).loc? cfg = some (Location.Stk fid))
    {a : Reference} (hstep : ReachableStep cfg a (Reference.OId oid)) :
    ∃ oid' fid', a = Reference.OId oid' ∧ (Reference.OId oid').loc? cfg = some (Location.Stk fid') := by
  cases a with
  | RId rid' =>
    exfalso
    rw [ReachableStep_rid_iff] at hstep
    obtain ⟨region', hlookup', -, obj, hobjlookup, hcontains⟩ := hstep
    have hmemrefs : (Reference.OId oid) ∈ region'.refs :=
      mem_region_refs_of_mem_objMap hobjlookup (List.contains_iff_mem.mp hcontains)
    have hloc' := vcfg.h3 rid' oid region' hlookup' hmemrefs
    rw [hloc] at hloc'
    simp at hloc'
  | OId oid' =>
    rw [ReachableStep_oid_iff] at hstep
    obtain ⟨obj, hobjAt, hcontains⟩ := hstep
    unfold Reference.objAt? at hobjAt
    dsimp only at hobjAt
    cases hloc' : (Reference.OId oid').loc? cfg with
    | none => rw [hloc'] at hobjAt; simp at hobjAt
    | some loc =>
      rw [hloc'] at hobjAt
      cases loc with
      | Rgn rid' =>
        exfalso
        dsimp only at hobjAt
        cases hlookup' : cfg.heap.lookup rid' with
        | none => rw [hlookup'] at hobjAt; simp at hobjAt
        | some region' =>
          rw [hlookup'] at hobjAt
          have hmemrefs : (Reference.OId oid) ∈ region'.refs :=
            mem_region_refs_of_mem_objMap hobjAt (List.contains_iff_mem.mp hcontains)
          have hridEq := vcfg.h3 rid' oid region' hlookup' hmemrefs
          rw [hloc] at hridEq
          simp at hridEq
      | Stk fid' => exact ⟨oid', fid', rfl, hloc'⟩

-- A reference is "safe" (w.r.t. a fixed Open region rid) if it's either an object inside
-- rid or a stack-resident object -- never a bare RId, never an object in another region.
def SafeRef (cfg : RuntimeConfig) (rid : RegionId) : Reference → Prop
  | Reference.OId oid => (Reference.OId oid).loc? cfg = some (Location.Rgn rid) ∨
      ∃ fid, (Reference.OId oid).loc? cfg = some (Location.Stk fid)
  | Reference.RId _ => False

-- Combines `predecessor_of_region_object`/`predecessor_of_stack_object`: safety propagates
-- backward across a single ReachableStep hop.
theorem predecessor_safe {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid : RegionId} {region : Region} (hlookup : cfg.heap.lookup rid = some region)
    (hopen : region.status = Status.Open) {ref : Reference} (hsafe : SafeRef cfg rid ref)
    {a : Reference} (hstep : ReachableStep cfg a ref) : SafeRef cfg rid a := by
  cases ref with
  | RId _ => exact absurd hsafe (by unfold SafeRef; exact id)
  | OId oid =>
    unfold SafeRef at hsafe
    rcases hsafe with hloc | ⟨fid, hloc⟩
    · obtain ⟨oid', haeq, hoidloc⟩ := predecessor_of_region_object vcfg hlookup hopen hloc hstep
      subst haeq
      unfold SafeRef
      exact hoidloc
    · obtain ⟨oid', fid', haeq, hoidloc⟩ := predecessor_of_stack_object vcfg hloc hstep
      subst haeq
      unfold SafeRef
      right
      exact ⟨fid', hoidloc⟩

-- If OId-sourced steps agree between cfg/cfg', any cfg-chain reaching a safe reference
-- transports to a cfg'-chain.
theorem safe_reflTransGen_transport {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid : RegionId} {region : Region} (hlookup : cfg.heap.lookup rid = some region)
    (hopen : region.status = Status.Open)
    (hoidstep : ∀ oid b, ReachableStep cfg (Reference.OId oid) b ↔ ReachableStep cfg' (Reference.OId oid) b)
    {start ref : Reference} (hrtg : Relation.ReflTransGen (ReachableStep cfg) start ref) :
    SafeRef cfg rid ref → Relation.ReflTransGen (ReachableStep cfg') start ref := by
  induction hrtg with
  | refl => intro _; exact Relation.ReflTransGen.refl
  | tail hprev hstep ih =>
    rename_i prev cur
    intro hsafe
    have hsafe_prev := predecessor_safe vcfg hlookup hopen hsafe hstep
    have hchain_prev := ih hsafe_prev
    cases prev with
    | RId _ => exact absurd hsafe_prev (by unfold SafeRef; exact id)
    | OId oid_prev => exact hchain_prev.tail ((hoidstep oid_prev cur).mp hstep)

-- An on-stack frame's own region is never the region `enter` opens (L2: on-stack regions
-- are always Open, but `enter` requires the entered region Closed).
theorem enter_regionId_ne {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {frame : FrameWithIndex} (hframe : frame ∈ cfg.stackWithIndex)
    {rid : RegionId} {region : Region} (hlookupRid : cfg.heap.lookup rid = some region)
    (hclosed : region.status = Status.Closed) : frame.regionId ≠ rid := by
  intro heq
  obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hframe
  have hmemstack : cfg.stack[n] ∈ cfg.stack := List.getElem_mem hn
  obtain ⟨region', hlookup', hopen'⟩ := vcfg.l2 cfg.stack[n] hmemstack
  have hridEq : cfg.stack[n].regionId = rid := (congrArg (·.regionId) hfeq).trans heq
  rw [hridEq, hlookupRid] at hlookup'
  injection hlookup' with hregionEq
  rw [← hregionEq, hclosed] at hopen'
  exact absurd hopen' (by decide)

-- `find? (index == fid)` over `stackWithIndex` is unaffected by appending a frame at a
-- strictly larger index.
theorem enter_stack_find_index_eq {cfg cfg' : RuntimeConfig} (h : enter xf a cfg = some cfg')
    (fid : Index) (hfid : fid < cfg.stack.length) :
    cfg.stackWithIndex.find? (fun frame => frame.index == fid) =
    cfg'.stackWithIndex.find? (fun frame => frame.index == fid) := by
  obtain ⟨rid, region, -, -, -, hcfg'⟩ := enter_cases h
  subst hcfg'
  unfold RuntimeConfig.stackWithIndex
  dsimp only
  rw [List.mapIdx_concat, List.find?_append]
  have hne : cfg.stack.length ≠ fid := (Nat.ne_of_lt hfid).symm
  simp [hne]

-- A `Stk fid` location is always a valid stack index.
theorem loc_stk_lt {cfg : RuntimeConfig} {oid : ObjectId} {fid : Index}
    (hloc : (Reference.OId oid).loc? cfg = some (Location.Stk fid)) : fid < cfg.stack.length := by
  unfold Reference.loc? at hloc
  dsimp only at hloc
  cases h1 : cfg.stackWithIndex.findRev? (fun frame => frame.objMap.keys.contains oid) with
  | none =>
    rw [h1] at hloc
    cases h2 : cfg.heap.entries.find? (fun (p : Sigma (fun _ : RegionId => Region)) => p.2.objMap.keys.contains oid) with
    | none => rw [h2] at hloc; simp at hloc
    | some _ => rw [h2] at hloc; simp at hloc
  | some frame =>
    rw [h1] at hloc
    cases h2 : cfg.heap.entries.find? (fun (p : Sigma (fun _ : RegionId => Region)) => p.2.objMap.keys.contains oid) with
    | some _ => rw [h2] at hloc; simp at hloc
    | none =>
      rw [h2] at hloc
      simp only [Option.some.injEq, Location.Stk.injEq] at hloc
      rw [List.findRev?_eq_find?_reverse] at h1
      have hmem : frame ∈ cfg.stackWithIndex.reverse := List.mem_of_find?_eq_some h1
      have hmem' : frame ∈ cfg.stackWithIndex := List.mem_reverse.mp hmem
      obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hmem'
      have hfidx : frame.index = n := by rw [← hfeq]
      rw [← hloc, hfidx]
      exact hn

-- `objAt?` is unconditionally unchanged by `enter`, for every object id.
theorem enter_objAt_eq {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
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
      have hloc : (Reference.OId oid).loc? cfg = some (Location.Stk fid) := by rw [hlocEq]; exact hloc'
      have hfid : fid < cfg.stack.length := loc_stk_lt hloc
      rw [enter_stack_find_index_eq h fid hfid]

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
  | tail hprev hstep ih =>
    intro hsafe
    exact ih (predecessor_safe vcfg hlookup hopen hsafe hstep)

-- Every pre-existing frame survives `enter` unchanged, at the same index.
theorem enter_frame_mem_up {cfg cfg' : RuntimeConfig} (h : enter xf a cfg = some cfg')
    {frame : FrameWithIndex} (hframe : frame ∈ cfg.stackWithIndex) : frame ∈ cfg'.stackWithIndex := by
  obtain ⟨rid, region, -, -, -, hcfg'⟩ := enter_cases h
  subst hcfg'
  unfold RuntimeConfig.stackWithIndex at hframe ⊢
  dsimp only
  rw [List.mapIdx_concat]
  exact List.mem_append_left _ hframe

-- Every `cfg'.stackWithIndex` member is either a pre-existing frame (index still inside
-- `cfg.stack`) or exactly the freshly-appended one, whose shape/regionId we pin down
-- against the caller's own `rid`/`region` (taken as an explicit `hcfg'` equation, rather
-- than re-derived via a fresh `enter_cases` call, so its `rid` is provably the caller's).
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
  · left
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hmem
    have hidx : frame.index = n := by rw [← hfeq]
    exact ⟨hmem, hidx ▸ hn⟩
  · right
    rw [List.mem_singleton] at hmem
    subst hmem
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

-- Any `cfg'.stackWithIndex` member whose index still fits inside `cfg.stack` was already
-- a `cfg.stackWithIndex` member (i.e. it isn't the freshly-appended frame).
theorem enter_frame_mem_down {cfg cfg' : RuntimeConfig} (h : enter xf a cfg = some cfg')
    {frame : FrameWithIndex} (hframe : frame ∈ cfg'.stackWithIndex) (hlt : frame.index < cfg.stack.length) :
    frame ∈ cfg.stackWithIndex := by
  obtain ⟨rid, region, -, -, -, hcfg'⟩ := enter_cases h
  rcases enter_frame_cases hcfg' hframe with ⟨hmem, -⟩ | ⟨-, -, -, -, hidx⟩
  · exact hmem
  · rw [hidx] at hlt; exact absurd hlt (lt_irrefl _)

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

-- Every `cfg'.stackWithIndex` member was already a `cfg.stackWithIndex` member with index
-- strictly below the popped frame's (i.e. it survived `exit`).
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

-- A frame strictly before the popped one has a different regionId (S1: regionId is
-- injective across the stack).
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
