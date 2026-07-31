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

-- A var's own value contributes directly to its frame's overall refs.
theorem mem_frame_refs_of_mem_varMap {frame : Frame} {var : VarName} {b : Reference}
    (hlookup : frame.varMap.lookup var = some b) : b ∈ frame.refs := by
  unfold Frame.refs
  rw [List.mem_append]
  exact Or.inr (List.mem_map_of_mem (AList.lookup_mem_entries hlookup))

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

-- H3 restated forward: an OId-typed step out of an object inside region `rid` always lands
-- back inside `rid` too (no openness needed, unlike `predecessor_of_region_object`).
theorem successor_of_region_object {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid : RegionId} {region : Region} (hlookup : cfg.heap.lookup rid = some region)
    {oidA oidC : ObjectId} (hloc : (Reference.OId oidA).loc? cfg = some (Location.Rgn rid))
    (hstep : ReachableStep cfg (Reference.OId oidA) (Reference.OId oidC)) :
    (Reference.OId oidC).loc? cfg = some (Location.Rgn rid) := by
  rw [ReachableStep_oid_iff] at hstep
  obtain ⟨obj, hobjAt, hcontains⟩ := hstep
  unfold Reference.objAt? at hobjAt
  dsimp only at hobjAt
  rw [hloc] at hobjAt
  dsimp only at hobjAt
  rw [hlookup] at hobjAt
  have hmemrefs : (Reference.OId oidC) ∈ region.refs :=
    mem_region_refs_of_mem_objMap hobjAt (List.contains_iff_mem.mp hcontains)
  exact vcfg.h3 rid oidC region hlookup hmemrefs

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

-- If `a` doesn't resolve to the popped frame's own slot, and `a` steps to `c` (both
-- SafeRef, so both OId-typed), neither does `c`: an OId in `Rgn rid` can only step to
-- another `Rgn rid` object (never the stack); an OId stack-resident elsewhere can only step
-- to an equal-or-earlier stack slot (S2), which stays below the (maximal) popped index.
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

-- `find? (index == fid)` over `stackWithIndex` agrees between `cfg`/`cfg'` for any surviving
-- index (below the popped one).
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

-- Converse of `stackWithIndex_getElem_index_eq`: a member's own index recovers it via `[·]?`.
theorem stackWithIndex_mem_getElem_eq {cfg : RuntimeConfig} {frame : FrameWithIndex}
    (hmem : frame ∈ cfg.stackWithIndex) : cfg.stackWithIndex[frame.index]? = some frame := by
  obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hmem
  have hidx : frame.index = n := by rw [← hfeq]
  rw [hidx]
  unfold RuntimeConfig.stackWithIndex
  rw [List.getElem?_mapIdx, List.getElem?_eq_getElem hn, Option.map_some]
  exact congrArg some hfeq

-- Searching `stackWithIndex` by index is the same as direct indexing (indices are unique
-- and sequential, so at most one entry can ever match `index == fid`).
theorem stackWithIndex_find_index_eq_getElem {cfg : RuntimeConfig} (fid : Index) :
    cfg.stackWithIndex.find? (fun f => f.index == fid) = cfg.stackWithIndex[fid]? := by
  cases hget : cfg.stackWithIndex[fid]? with
  | none =>
    rw [List.find?_eq_none]
    intro fr hfr
    by_contra hcontra
    rw [beq_iff_eq] at hcontra
    have hget2 := stackWithIndex_mem_getElem_eq hfr
    rw [hcontra] at hget2
    rw [hget2] at hget
    exact absurd hget (by simp)
  | some frame =>
    have hidx : frame.index = fid := stackWithIndex_getElem_index_eq hget
    rw [← hidx]
    exact swap_corollary_stackWithIndex_find_eq (List.mem_of_getElem? hget)

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

-- OId-sourced steps agree between cfg/cfg' across `exit`, for any oid not resolving to the
-- popped frame's slot.
theorem exit_oid_step_iff_of_ne_popped {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : exit cfg = some cfg') (oid : ObjectId)
    (hne : (Reference.OId oid).loc? cfg ≠ some (Location.Stk (cfg.stack.length - 1))) (b : Reference) :
    ReachableStep cfg (Reference.OId oid) b ↔ ReachableStep cfg' (Reference.OId oid) b := by
  rw [ReachableStep_oid_iff, ReachableStep_oid_iff, exit_objAt_eq_of_ne_popped vcfg h oid hne]

-- Combines `safe_reflTransGen_root_safe` (freshly, at every point, via the remaining
-- suffix to `oid`), `exit_avoid_popped_step` and `exit_oid_step_iff_of_ne_popped`: any
-- cfg-chain from a not-popped root to a safe `oid` transports to cfg'.
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

-- A `FrameRoot` rooted at a frame strictly before the popped one never resolves to the
-- popped frame's own slot (S2, applied directly to the rooting frame).
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

-- Every pre-existing frame with index strictly below the popped one survives `exit`
-- unchanged, with the exact same heap entry for its own region.
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

-- Anything stack-resident in cfg' is (a fortiori) not resolving to the popped frame's own
-- slot in cfg either: `loc?` is a function, and the object's frame survives unchanged.
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

-- Anything resolving into an untouched region (its cfg/cfg' heap entries agree) in cfg' also
-- avoids the popped frame's cfg-side slot (Rgn and Stk are different shapes).
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

-- The backward direction: any cfg'-chain reaching a safe reference transports to cfg. No
-- monotonicity argument is needed here (unlike the forward direction): a `SafeRef cfg' rid`
-- node's "not popped" fact is derivable purely locally, from its own cfg'-side shape
-- (`exit_rgn_not_popped`/`exit_stk_not_popped_of_cfg'`), at every step.
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

-- Mirrors `exit_frame_reachable_transport`, backward: any `cfg'.stackWithIndex` member's
-- reachability of a frame.regionId-object transports down to `cfg`.
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

-- The freshly-allocated object id is never already present in the last frame's own objMap.
theorem makeObjStack_fresh_not_in_last {cfg : RuntimeConfig} {lastFrame : Frame}
    (hlast : cfg.stack.getLast? = some lastFrame) : cfg.freshObjectId ∉ lastFrame.objMap.keys := by
  intro hmem
  apply cfg.freshObjectId_not_mem
  unfold RuntimeConfig.objectIds
  rw [List.mem_append]
  left
  unfold Stack.objectIds
  rw [List.bind_eq_flatMap, List.mem_flatMap]
  have hmemStack : lastFrame ∈ cfg.stack := by
    have hne : cfg.stack ≠ [] := by intro hnil; rw [hnil] at hlast; simp at hlast
    rw [List.getLast?_eq_getLast_of_ne_nil hne, Option.some_inj] at hlast
    rw [← hlast]
    exact List.getLast_mem hne
  exact ⟨lastFrame.objectIds, List.mem_map_of_mem hmemStack, hmem⟩

-- `loc?` agrees between `cfg`/`cfg'` for any oid other than the freshly-allocated one.
theorem makeObjStack_loc_eq_of_ne {cfg cfg' : RuntimeConfig} (h : makeObjStack x cfg = some cfg')
    {oid : ObjectId} (hne : oid ≠ cfg.freshObjectId) :
    (Reference.OId oid).loc? cfg = (Reference.OId oid).loc? cfg' := by
  obtain ⟨lastFrame, hlast, hcfg'⟩ := makeObjStack_cases h
  have hfreshNotIn : cfg.freshObjectId ∉ lastFrame.objMap.keys := makeObjStack_fresh_not_in_last hlast
  have hkeq : (lastFrame.objMap.insert cfg.freshObjectId ∅).keys.contains oid = lastFrame.objMap.keys.contains oid := by
    rw [AList.keys_insert, List.erase_of_not_mem hfreshNotIn]
    simp only [List.contains_cons]
    have : (oid == cfg.freshObjectId) = false := by simpa using hne
    rw [this]
    simp
  have hne' : cfg.stack ≠ [] := by intro hnil; rw [hnil] at hlast; simp at hlast
  have hstackEq : cfg.stack = cfg.stack.dropLast ++ [lastFrame] := by
    rw [List.getLast?_eq_getLast_of_ne_nil hne', Option.some_inj] at hlast
    rw [← hlast]
    exact (List.dropLast_append_getLast hne').symm
  set newLastWI : FrameWithIndex := { lastFrame with
      varMap := lastFrame.varMap.insert x (Reference.OId cfg.freshObjectId),
      objMap := lastFrame.objMap.insert cfg.freshObjectId ∅,
      index := cfg.stack.dropLast.length } with hnewLastWI_def
  set oldLastWI : FrameWithIndex := { lastFrame with index := cfg.stack.dropLast.length } with holdLastWI_def
  set revTail : List FrameWithIndex :=
      (List.mapIdx (fun idx frame => ({ toFrame := frame, index := idx } : FrameWithIndex))
        cfg.stack.dropLast).reverse with hrevTail_def
  set pred : FrameWithIndex → Bool := fun frame => frame.objMap.keys.contains oid with hpred_def
  have hstackFindEq :
      (List.find? pred (newLastWI :: revTail)).map FrameWithIndex.index =
      (List.find? pred (oldLastWI :: revTail)).map FrameWithIndex.index := by
    have hnewval : pred newLastWI = pred oldLastWI := by
      rw [hnewLastWI_def, holdLastWI_def, hpred_def]
      exact hkeq
    cases hval : pred oldLastWI with
    | true =>
      have h1 : List.find? pred (newLastWI :: revTail) = some newLastWI :=
        List.find?_cons_of_pos (hnewval.trans hval)
      have h2 : List.find? pred (oldLastWI :: revTail) = some oldLastWI :=
        List.find?_cons_of_pos hval
      rw [h1, h2]
      rfl
    | false =>
      have h1 : List.find? pred (newLastWI :: revTail) = List.find? pred revTail :=
        List.find?_cons_of_neg (by rw [hnewval, hval]; decide)
      have h2 : List.find? pred (oldLastWI :: revTail) = List.find? pred revTail :=
        List.find?_cons_of_neg (by rw [hval]; decide)
      rw [h1, h2]
  unfold Reference.loc?
  dsimp only
  subst hcfg'
  unfold RuntimeConfig.stackWithIndex
  dsimp only
  conv_lhs => rw [hstackEq]
  rw [List.mapIdx_concat, List.mapIdx_concat]
  rw [List.findRev?_eq_find?_reverse, List.findRev?_eq_find?_reverse]
  rw [List.reverse_append, List.reverse_append, List.reverse_singleton, List.reverse_singleton]
  rw [List.singleton_append, List.singleton_append]
  cases hval1 : List.find? pred (oldLastWI :: revTail) with
  | none =>
    have hval2 : List.find? pred (newLastWI :: revTail) = none := by
      have := hstackFindEq
      rw [hval1] at this
      cases hval3 : List.find? pred (newLastWI :: revTail) with
      | none => rfl
      | some fr => rw [hval3] at this; simp at this
    rw [hval2]
  | some fr1 =>
    have hval2 : ∃ fr2, List.find? pred (newLastWI :: revTail) = some fr2 ∧ fr2.index = fr1.index := by
      have := hstackFindEq
      rw [hval1] at this
      cases hval3 : List.find? pred (newLastWI :: revTail) with
      | none => rw [hval3] at this; simp at this
      | some fr2 => rw [hval3] at this; simp at this; exact ⟨fr2, rfl, this⟩
    obtain ⟨fr2, hfr2, hidxeq⟩ := hval2
    rw [hfr2]
    cases cfg.heap.entries.find? (fun (e : Sigma (fun _ : RegionId => Region)) => e.snd.objMap.keys.contains oid) with
    | none => dsimp only; rw [hidxeq]
    | some _ => dsimp only

-- `objAt?` agrees between `cfg`/`cfg'` for any oid other than the freshly-allocated one.
theorem makeObjStack_objAt_eq_of_ne {cfg cfg' : RuntimeConfig} (h : makeObjStack x cfg = some cfg')
    {oid : ObjectId} (hne : oid ≠ cfg.freshObjectId) :
    (Reference.OId oid).objAt? cfg = (Reference.OId oid).objAt? cfg' := by
  obtain ⟨lastFrame, hlast, hcfg'⟩ := makeObjStack_cases h
  have hlocEq := makeObjStack_loc_eq_of_ne h hne
  unfold Reference.objAt?
  dsimp only
  rw [hlocEq]
  cases hloc' : (Reference.OId oid).loc? cfg' with
  | none => rfl
  | some loc =>
    cases loc with
    | Rgn rid0 => dsimp only; subst hcfg'; rfl
    | Stk fid0 =>
      dsimp only
      rw [stackWithIndex_find_index_eq_getElem, stackWithIndex_find_index_eq_getElem]
      have hne' : cfg.stack ≠ [] := by intro hnil; rw [hnil] at hlast; simp at hlast
      have hstackEq : cfg.stack = cfg.stack.dropLast ++ [lastFrame] := by
        rw [List.getLast?_eq_getLast_of_ne_nil hne', Option.some_inj] at hlast
        rw [← hlast]; exact (List.dropLast_append_getLast hne').symm
      have hgetCfg : cfg.stackWithIndex[fid0]? =
          (cfg.stack[fid0]?).map (fun f => ({ toFrame := f, index := fid0 } : FrameWithIndex)) := by
        unfold RuntimeConfig.stackWithIndex; rw [List.getElem?_mapIdx]
      have hgetCfg' : cfg'.stackWithIndex[fid0]? =
          (cfg'.stack[fid0]?).map (fun f => ({ toFrame := f, index := fid0 } : FrameWithIndex)) := by
        unfold RuntimeConfig.stackWithIndex; rw [List.getElem?_mapIdx]
      rw [hgetCfg, hgetCfg']
      by_cases hfid : fid0 < cfg.stack.dropLast.length
      · have h1 : cfg.stack[fid0]? = cfg.stack.dropLast[fid0]? := by
          conv_lhs => rw [hstackEq]
          rw [List.getElem?_append_left hfid]
        have h2 : cfg'.stack[fid0]? = cfg.stack.dropLast[fid0]? := by
          rw [hcfg']; dsimp only
          rw [List.getElem?_append_left hfid]
        rw [h1, h2]
      · push_neg at hfid
        set newLastFrame : Frame := { regionId := lastFrame.regionId, bridgeVar := lastFrame.bridgeVar, objMap := lastFrame.objMap.insert cfg.freshObjectId ∅, varMap := lastFrame.varMap.insert x (Reference.OId cfg.freshObjectId) } with hnewLastFrame_def
        have h1 : cfg.stack[fid0]? = [lastFrame][fid0 - cfg.stack.dropLast.length]? := by
          conv_lhs => rw [hstackEq]
          rw [List.getElem?_append_right hfid]
        have h2 : cfg'.stack[fid0]? = [newLastFrame][fid0 - cfg.stack.dropLast.length]? := by
          rw [hcfg']; dsimp only
          rw [List.getElem?_append_right hfid]
        rw [h1, h2]
        cases hidx : fid0 - cfg.stack.dropLast.length with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.map_some]
          rw [hnewLastFrame_def]
          dsimp only [Option.bind]
          rw [AList.lookup_insert_ne hne]
        | succ n => rfl

-- A fresh object id never resolves to any location (it isn't allocated yet).
theorem freshObjectId_loc_none {cfg : RuntimeConfig} :
    (Reference.OId cfg.freshObjectId).loc? cfg = none := by
  have hnotmem := cfg.freshObjectId_not_mem
  unfold RuntimeConfig.objectIds at hnotmem
  rw [List.mem_append] at hnotmem
  push_neg at hnotmem
  obtain ⟨hnotStack, hnotHeap⟩ := hnotmem
  unfold Reference.loc?
  dsimp only
  cases hh : cfg.stackWithIndex.findRev? (fun frame => frame.objMap.keys.contains cfg.freshObjectId) with
  | some frame =>
    exfalso
    apply hnotStack
    unfold Stack.objectIds
    rw [List.bind_eq_flatMap, List.mem_flatMap]
    rw [List.findRev?_eq_find?_reverse] at hh
    have hcontains := List.find?_some hh
    have hmem : frame ∈ cfg.stackWithIndex := List.mem_reverse.mp (List.mem_of_find?_eq_some hh)
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hmem
    have hmemStack : cfg.stack[n] ∈ cfg.stack := List.getElem_mem hn
    have hfeq2 : frame.objMap = cfg.stack[n].objMap := congrArg (·.objMap) hfeq.symm
    refine ⟨cfg.stack[n].objectIds, List.mem_map_of_mem hmemStack, ?_⟩
    unfold Frame.objectIds
    rw [← hfeq2]
    exact List.contains_iff_mem.mp hcontains
  | none =>
    cases hh2 : cfg.heap.entries.find? (fun (e : Sigma (fun _ : RegionId => Region)) => e.snd.objMap.keys.contains cfg.freshObjectId) with
    | none => rfl
    | some regionEntry =>
      exfalso
      apply hnotHeap
      unfold Heap.objectIds
      rw [List.mem_flatten]
      have hcontains := List.find?_some hh2
      refine ⟨regionEntry.snd.objectIds, List.mem_map_of_mem (List.mem_of_find?_eq_some hh2), ?_⟩
      unfold Region.objectIds
      exact List.contains_iff_mem.mp hcontains

-- A fresh object id never resolves anywhere (it isn't allocated yet).
theorem freshObjectId_objAt_none {cfg : RuntimeConfig} :
    (Reference.OId cfg.freshObjectId).objAt? cfg = none := by
  unfold Reference.objAt?
  dsimp only
  rw [freshObjectId_loc_none]

-- The freshly-allocated object resolves to its own (empty) content in cfg'.
theorem makeObjStack_fresh_objAt_cfg' {cfg cfg' : RuntimeConfig} (h : makeObjStack x cfg = some cfg') :
    (Reference.OId cfg.freshObjectId).objAt? cfg' = some (∅ : Object) := by
  obtain ⟨lastFrame, hlast, hcfg'⟩ := makeObjStack_cases h
  have hnotmem := cfg.freshObjectId_not_mem
  unfold RuntimeConfig.objectIds at hnotmem
  rw [List.mem_append] at hnotmem
  push_neg at hnotmem
  obtain ⟨-, hnotHeap⟩ := hnotmem
  have hne' : cfg.stack ≠ [] := by intro hnil; rw [hnil] at hlast; simp at hlast
  have hstackEq : cfg.stack = cfg.stack.dropLast ++ [lastFrame] := by
    rw [List.getLast?_eq_getLast_of_ne_nil hne', Option.some_inj] at hlast
    rw [← hlast]; exact (List.dropLast_append_getLast hne').symm
  have hheapNone : cfg.heap.entries.find?
      (fun (e : Sigma (fun _ : RegionId => Region)) => e.snd.objMap.keys.contains cfg.freshObjectId) = none := by
    rw [List.find?_eq_none]
    intro entry hentry hcontra
    apply hnotHeap
    unfold Heap.objectIds
    rw [List.mem_flatten]
    refine ⟨entry.snd.objectIds, List.mem_map_of_mem hentry, ?_⟩
    unfold Region.objectIds
    exact List.contains_iff_mem.mp hcontra
  have hcontainsNew : (lastFrame.objMap.insert cfg.freshObjectId ∅).keys.contains cfg.freshObjectId = true := by
    rw [AList.keys_insert]
    simp
  set dropLastLen : Nat := cfg.stack.dropLast.length with hdropLastLen_def
  set newLastFrame : Frame := { regionId := lastFrame.regionId, bridgeVar := lastFrame.bridgeVar, objMap := lastFrame.objMap.insert cfg.freshObjectId ∅, varMap := lastFrame.varMap.insert x (Reference.OId cfg.freshObjectId) } with hnewLastFrame_def
  have hloc' : (Reference.OId cfg.freshObjectId).loc? cfg' = some (Location.Stk dropLastLen) := by
    unfold Reference.loc?
    dsimp only
    rw [hcfg']
    dsimp only
    rw [hheapNone]
    unfold RuntimeConfig.stackWithIndex
    dsimp only
    rw [List.mapIdx_concat, List.findRev?_eq_find?_reverse, List.reverse_append,
      List.reverse_singleton, List.singleton_append]
    have hcontainsNew' : newLastFrame.objMap.keys.contains cfg.freshObjectId = true := hcontainsNew
    have hfindEq : List.find? (fun (frame : FrameWithIndex) => frame.objMap.keys.contains cfg.freshObjectId)
        (({ toFrame := newLastFrame, index := dropLastLen } : FrameWithIndex) ::
          (List.mapIdx (fun idx frame => ({ toFrame := frame, index := idx } : FrameWithIndex)) cfg.stack.dropLast).reverse) =
        some { toFrame := newLastFrame, index := dropLastLen } :=
      List.find?_cons_of_pos hcontainsNew'
    rw [hfindEq]
  unfold Reference.objAt?
  dsimp only
  rw [hloc']
  dsimp only
  have hmemNew : ({ toFrame := newLastFrame, index := dropLastLen } : FrameWithIndex) ∈ cfg'.stackWithIndex := by
    rw [hcfg']
    unfold RuntimeConfig.stackWithIndex
    dsimp only
    apply List.mem_mapIdx.mpr
    refine ⟨dropLastLen, by rw [hdropLastLen_def]; simp, ?_⟩
    dsimp only
    rw [List.getElem_append_right (by rw [hdropLastLen_def])]
    simp [hdropLastLen_def]
  have hfind : cfg'.stackWithIndex.find? (fun frame => frame.index == dropLastLen) =
      some { toFrame := newLastFrame, index := dropLastLen } :=
    swap_corollary_stackWithIndex_find_eq hmemNew
  rw [hfind]
  have hlookupNew : newLastFrame.objMap.lookup cfg.freshObjectId = some (∅ : Object) := by
    rw [hnewLastFrame_def]
    dsimp only
    rw [AList.lookup_insert]
  exact hlookupNew

-- `ReachableStep` agrees between `cfg`/`cfg'` for every oid, unconditionally: any hop
-- sourced at the freshly-allocated id is vacuously impossible on both sides (it doesn't
-- resolve at all in cfg, and resolves to an empty object in cfg').
theorem makeObjStack_oid_step_iff {cfg cfg' : RuntimeConfig} (h : makeObjStack x cfg = some cfg')
    (oid : ObjectId) (b : Reference) :
    ReachableStep cfg (Reference.OId oid) b ↔ ReachableStep cfg' (Reference.OId oid) b := by
  by_cases hne : oid = cfg.freshObjectId
  · subst hne
    constructor
    · intro hstep
      rw [ReachableStep_oid_iff] at hstep
      obtain ⟨obj, hobjAt, -⟩ := hstep
      rw [freshObjectId_objAt_none] at hobjAt
      exact absurd hobjAt (by simp)
    · intro hstep
      rw [ReachableStep_oid_iff] at hstep
      obtain ⟨obj, hobjAt, hcontains⟩ := hstep
      rw [makeObjStack_fresh_objAt_cfg' h] at hobjAt
      injection hobjAt with hobjAt
      rw [← hobjAt] at hcontains
      simp [Object.refs] at hcontains
  · rw [ReachableStep_oid_iff, ReachableStep_oid_iff, makeObjStack_objAt_eq_of_ne h hne]

-- Every `cfg'.stackWithIndex` member is either a pre-existing, content-unchanged frame
-- (index strictly below the last one) or exactly the modified last frame.
theorem makeObjStack_frame_cases {cfg cfg' : RuntimeConfig} {lastFrame : Frame} {x : VarName}
    (hlast : cfg.stack.getLast? = some lastFrame)
    (hcfg' : cfg' = { cfg with
      stack := cfg.stack.dropLast ++ [{ lastFrame with
        varMap := lastFrame.varMap.insert x (Reference.OId cfg.freshObjectId),
        objMap := lastFrame.objMap.insert cfg.freshObjectId ∅ }] })
    {frame : FrameWithIndex} (hframe : frame ∈ cfg'.stackWithIndex) :
    (frame ∈ cfg.stackWithIndex ∧ frame.index < cfg.stack.length - 1) ∨
    (frame.regionId = lastFrame.regionId ∧ frame.bridgeVar = lastFrame.bridgeVar ∧
      frame.varMap = lastFrame.varMap.insert x (Reference.OId cfg.freshObjectId) ∧
      frame.objMap = lastFrame.objMap.insert cfg.freshObjectId ∅ ∧
      frame.index = cfg.stack.dropLast.length) := by
  have hne' : cfg.stack ≠ [] := by intro hnil; rw [hnil] at hlast; simp at hlast
  have hstackEq : cfg.stack = cfg.stack.dropLast ++ [lastFrame] := by
    rw [List.getLast?_eq_getLast_of_ne_nil hne', Option.some_inj] at hlast
    rw [← hlast]; exact (List.dropLast_append_getLast hne').symm
  unfold RuntimeConfig.stackWithIndex at hframe
  rw [hcfg'] at hframe
  dsimp only at hframe
  rw [List.mapIdx_concat] at hframe
  rcases List.mem_append.mp hframe with hmem | hmem
  · left
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hmem
    have hidx : frame.index = n := by rw [← hfeq]
    have hmem' : frame ∈ cfg.stackWithIndex := by
      unfold RuntimeConfig.stackWithIndex
      conv_lhs => rw [hstackEq]
      rw [List.mapIdx_concat]
      exact List.mem_append_left _ hmem
    refine ⟨hmem', ?_⟩
    rw [hidx, ← List.length_dropLast]
    exact hn
  · right
    rw [List.mem_singleton] at hmem
    subst hmem
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

-- A pre-existing frame with index strictly below the last one survives `makeObjStack`
-- unchanged, at the same index.
theorem makeObjStack_frame_mem_up {cfg cfg' : RuntimeConfig} (h : makeObjStack x cfg = some cfg')
    {frame : FrameWithIndex} (hframe : frame ∈ cfg.stackWithIndex) (hlt : frame.index < cfg.stack.length - 1) :
    frame ∈ cfg'.stackWithIndex := by
  obtain ⟨lastFrame, hlast, hcfg'⟩ := makeObjStack_cases h
  unfold RuntimeConfig.stackWithIndex at hframe ⊢
  rw [hcfg']
  dsimp only
  obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hframe
  have hidx : frame.index = n := by rw [← hfeq]
  have hnlt : n < cfg.stack.dropLast.length := by rw [List.length_dropLast]; rw [hidx] at hlt; exact hlt
  apply List.mem_mapIdx.mpr
  refine ⟨n, ?_, ?_⟩
  · rw [List.length_append]; omega
  · rw [List.getElem_append_left hnlt, List.getElem_dropLast hnlt]
    exact hfeq

-- `ReachableStep` agrees between `cfg`/`cfg'` completely unconditionally -- heap is never
-- touched by `makeObjStack` at all, so RId-sourced steps agree trivially too.
theorem makeObjStack_step_eq {cfg cfg' : RuntimeConfig} (h : makeObjStack x cfg = some cfg') :
    ReachableStep cfg = ReachableStep cfg' := by
  obtain ⟨lastFrame, hlast, hcfg'⟩ := makeObjStack_cases h
  funext a b
  apply propext
  cases a with
  | OId oid => exact makeObjStack_oid_step_iff h oid b
  | RId rid =>
    rw [ReachableStep_rid_iff, ReachableStep_rid_iff]
    rw [hcfg']

-- `FrameReachable` agrees between `cfg`/`cfg'`, both directions, for any frame with index
-- strictly below the last one (content is literally untouched there).
theorem makeObjStack_frame_reachable_iff {cfg cfg' : RuntimeConfig} (h : makeObjStack x cfg = some cfg')
    {X : FrameWithIndex} (hXmem : X ∈ cfg.stackWithIndex) (hXlt : X.index < cfg.stack.length - 1)
    (ref : Reference) : FrameReachable cfg X.index ref ↔ FrameReachable cfg' X.index ref := by
  obtain ⟨lastFrame, hlast, hcfg'⟩ := makeObjStack_cases h
  rw [FrameReachable_iff_reflTransGen, FrameReachable_iff_reflTransGen, makeObjStack_step_eq h]
  constructor
  · rintro ⟨start, hroot, hrtg⟩
    refine ⟨start, ?_, hrtg⟩
    rcases hroot with ⟨Xf, hXfmem, hXfidx, var, hvar⟩ | ⟨Xf, hXfmem, hXfidx, region, hlookup, hbridge⟩
    · exact Or.inl ⟨Xf, makeObjStack_frame_mem_up h hXfmem (hXfidx ▸ hXlt), hXfidx, var, hvar⟩
    · have hlookup' : cfg'.heap.lookup Xf.regionId = some region := by rw [hcfg']; exact hlookup
      exact Or.inr ⟨Xf, makeObjStack_frame_mem_up h hXfmem (hXfidx ▸ hXlt), hXfidx, region, hlookup', hbridge⟩
  · rintro ⟨start, hroot, hrtg⟩
    refine ⟨start, ?_, hrtg⟩
    rcases hroot with ⟨Xf, hXfmem, hXfidx, var, hvar⟩ | ⟨Xf, hXfmem, hXfidx, region, hlookup, hbridge⟩
    · rcases makeObjStack_frame_cases hlast hcfg' hXfmem with ⟨hXfmemcfg, -⟩ | ⟨-, -, -, -, hXfidx2⟩
      · exact Or.inl ⟨Xf, hXfmemcfg, hXfidx, var, hvar⟩
      · exfalso
        have hXeq : X.index = cfg.stack.dropLast.length := by rw [← hXfidx, hXfidx2]
        rw [hXeq, List.length_dropLast] at hXlt
        exact absurd hXlt (lt_irrefl _)
    · rcases makeObjStack_frame_cases hlast hcfg' hXfmem with ⟨hXfmemcfg, -⟩ | ⟨-, -, -, -, hXfidx2⟩
      · have hlookup' : cfg.heap.lookup Xf.regionId = some region := by rw [hcfg'] at hlookup; exact hlookup
        exact Or.inr ⟨Xf, hXfmemcfg, hXfidx, region, hlookup', hbridge⟩
      · exfalso
        have hXeq : X.index = cfg.stack.dropLast.length := by rw [← hXfidx, hXfidx2]
        rw [hXeq, List.length_dropLast] at hXlt
        exact absurd hXlt (lt_irrefl _)


-- A fresh object id never resolves into any region (it isn't allocated yet).
theorem freshObjectId_loc_ne_rgn {cfg : RuntimeConfig} {rid : RegionId} :
    (Reference.OId cfg.freshObjectId).loc? cfg ≠ some (Location.Rgn rid) := by
  rw [freshObjectId_loc_none]
  simp

-- The stack's own last frame, reindexed as a `FrameWithIndex`, is a member of `stackWithIndex`.
theorem stackWithIndex_getLast_mem {cfg : RuntimeConfig} {lastFrame : Frame}
    (hlast : cfg.stack.getLast? = some lastFrame) :
    ({ lastFrame with index := cfg.stack.length - 1 } : FrameWithIndex) ∈ cfg.stackWithIndex := by
  have hne : cfg.stack ≠ [] := by intro hnil; rw [hnil] at hlast; simp at hlast
  have hlen1 : 1 ≤ cfg.stack.length := List.length_pos_of_ne_nil hne
  have hget : cfg.stack[cfg.stack.length - 1] = lastFrame := by
    rw [List.getLast?_eq_getLast_of_ne_nil hne, Option.some_inj] at hlast
    rw [← hlast, List.getLast_eq_getElem hne]
  unfold RuntimeConfig.stackWithIndex
  apply List.mem_mapIdx.mpr
  refine ⟨cfg.stack.length - 1, by omega, ?_⟩
  rw [hget]

-- ===== makeObjRegion =====

-- `objAt?` agrees between `cfg`/`cfg'` for any oid other than the freshly-allocated one. The
-- heap side genuinely reorders (the mutated region's entry moves via the kerase-based insert),
-- handled here directly via `makeObjRegion_corollary_loc_eq` (Model layer) pinning the same
-- `Location`; the stack side is unconditional (only `varMap` changes, never `objMap`), via the
-- generic `stackWithIndex_objMap_get_eq_of_last_varMap_update` (also Model layer).
theorem makeObjRegion_objAt_eq_of_ne {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeObjRegion x cfg = some cfg') {oid : ObjectId} (hne : oid ≠ cfg.freshObjectId) :
    (Reference.OId oid).objAt? cfg = (Reference.OId oid).objAt? cfg' := by
  obtain ⟨frame, region, hlast, hlookupRid, hopen, hcfg'⟩ := makeObjRegion_cases h
  have hlocEq := makeObjRegion_corollary_loc_eq vcfg h oid hne
  unfold Reference.objAt?
  dsimp only
  rw [hlocEq]
  cases hloc' : (Reference.OId oid).loc? cfg' with
  | none => rfl
  | some loc =>
    cases loc with
    | Rgn rid0 =>
      dsimp only
      by_cases heq : rid0 = frame.regionId
      · subst heq
        have hlookup' : cfg'.heap.lookup frame.regionId =
            some { region with objMap := region.objMap.insert cfg.freshObjectId ∅ } := by
          rw [hcfg']; dsimp only; rw [AList.lookup_insert]
        rw [hlookup', hlookupRid]
        simp [AList.lookup_insert_ne, hne]
      · have hlookup' : cfg'.heap.lookup rid0 = cfg.heap.lookup rid0 := by
          rw [hcfg']; dsimp only; rw [AList.lookup_insert_ne heq]
        rw [hlookup']
    | Stk fid0 =>
      dsimp only
      rw [stackWithIndex_find_index_eq_getElem, stackWithIndex_find_index_eq_getElem]
      have hshape := stackWithIndex_objMap_get_eq_of_last_varMap_update (cfg' := cfg') hlast (by rw [hcfg'])
      have hgetCfg : cfg.stackWithIndex[fid0]? =
          (cfg.stack[fid0]?).map (fun f => ({ toFrame := f, index := fid0 } : FrameWithIndex)) := by
        unfold RuntimeConfig.stackWithIndex; rw [List.getElem?_mapIdx]
      have hgetCfg' : cfg'.stackWithIndex[fid0]? =
          (cfg'.stack[fid0]?).map (fun f => ({ toFrame := f, index := fid0 } : FrameWithIndex)) := by
        unfold RuntimeConfig.stackWithIndex; rw [List.getElem?_mapIdx]
      rw [hgetCfg, hgetCfg']
      cases hc : cfg.stack[fid0]? with
      | none =>
        have hc' : cfg'.stack[fid0]? = none := by
          have hs := hshape fid0; rw [hc] at hs; simpa using hs.symm
        rw [hc']
      | some fA =>
        cases hc' : cfg'.stack[fid0]? with
        | none => have hs := hshape fid0; rw [hc, hc'] at hs; simp at hs
        | some fB =>
          have hobjmapEq : fA.objMap = fB.objMap := by
            have hs := hshape fid0; rw [hc, hc'] at hs; simpa using hs
          simp only [Option.map_some]
          dsimp only [Option.bind]
          rw [hobjmapEq]

-- The freshly-allocated object resolves to its own (empty) content in cfg'.
theorem makeObjRegion_fresh_objAt_cfg' {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeObjRegion x cfg = some cfg') :
    (Reference.OId cfg.freshObjectId).objAt? cfg' = some (∅ : Object) := by
  obtain ⟨frame, region, hlast, hlookupRid, hopen, hcfg'⟩ := makeObjRegion_cases h
  obtain ⟨frame0, hlast0, hlocFresh⟩ := makeObjRegion_corollary_loc_fresh vcfg h
  rw [hlast] at hlast0
  injection hlast0 with hlast0
  subst hlast0
  unfold Reference.objAt?
  dsimp only
  rw [hlocFresh]
  dsimp only
  have hlookup' : cfg'.heap.lookup frame.regionId =
      some { region with objMap := region.objMap.insert cfg.freshObjectId ∅ } := by
    rw [hcfg']; dsimp only; rw [AList.lookup_insert]
  rw [hlookup']
  simp [AList.lookup_insert]

-- `ReachableStep` agrees between `cfg`/`cfg'` for every OId-sourced step: unconditionally for
-- `oid ≠ freshObjectId` (via `makeObjRegion_objAt_eq_of_ne`), and vacuously (both sides
-- impossible) for the freshly-allocated id itself (it resolves nowhere in `cfg`, and to the
-- empty object -- no refs -- in `cfg'`).
theorem makeObjRegion_oid_step_iff {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeObjRegion x cfg = some cfg') (oid : ObjectId) (b : Reference) :
    ReachableStep cfg (Reference.OId oid) b ↔ ReachableStep cfg' (Reference.OId oid) b := by
  by_cases hne : oid = cfg.freshObjectId
  · subst hne
    constructor
    · intro hstep
      rw [ReachableStep_oid_iff] at hstep
      obtain ⟨obj, hobjAt, -⟩ := hstep
      rw [freshObjectId_objAt_none] at hobjAt
      exact absurd hobjAt (by simp)
    · intro hstep
      rw [ReachableStep_oid_iff] at hstep
      obtain ⟨obj, hobjAt, hcontains⟩ := hstep
      rw [makeObjRegion_fresh_objAt_cfg' vcfg h] at hobjAt
      injection hobjAt with hobjAt
      rw [← hobjAt] at hcontains
      simp [Object.refs] at hcontains
  · rw [ReachableStep_oid_iff, ReachableStep_oid_iff, makeObjRegion_objAt_eq_of_ne vcfg h hne]

-- `ReachableStep` agrees between `cfg`/`cfg'` for every RId-sourced step: the mutated region's
-- own status never changes (`Open` throughout), so `open_rid_no_step` rules out any step from it
-- on both sides; every other heap key is untouched by the mutation.
theorem makeObjRegion_rid_step_iff {cfg cfg' : RuntimeConfig}
    (h : makeObjRegion x cfg = some cfg') (rid : RegionId) (b : Reference) :
    ReachableStep cfg (Reference.RId rid) b ↔ ReachableStep cfg' (Reference.RId rid) b := by
  obtain ⟨frame, region, hlast, hlookupRid, hopen, hcfg'⟩ := makeObjRegion_cases h
  by_cases heq : rid = frame.regionId
  · subst heq
    have hlookup' : cfg'.heap.lookup frame.regionId =
        some { region with objMap := region.objMap.insert cfg.freshObjectId ∅ } := by
      rw [hcfg']; dsimp only; rw [AList.lookup_insert]
    constructor
    · intro hstep; exact absurd hstep (open_rid_no_step hlookupRid hopen)
    · intro hstep; exact absurd hstep (open_rid_no_step hlookup' hopen)
  · have hlookup' : cfg'.heap.lookup rid = cfg.heap.lookup rid := by
      rw [hcfg']; dsimp only; rw [AList.lookup_insert_ne heq]
    rw [ReachableStep_rid_iff, ReachableStep_rid_iff, hlookup']

-- `ReachableStep` agrees between `cfg`/`cfg'` completely, as a literal function equality --
-- combining the OId and RId cases above.
theorem makeObjRegion_step_eq {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeObjRegion x cfg = some cfg') :
    ReachableStep cfg = ReachableStep cfg' := by
  funext a b
  apply propext
  cases a with
  | OId oid => exact makeObjRegion_oid_step_iff vcfg h oid b
  | RId rid => exact makeObjRegion_rid_step_iff h rid b

-- Every `cfg'.stackWithIndex` member is either a pre-existing, content-unchanged frame (index
-- strictly below the last one) or exactly the last frame with `varMap` updated.
theorem makeObjRegion_frame_cases {cfg cfg' : RuntimeConfig} {x : VarName}
    (h : makeObjRegion x cfg = some cfg')
    {frame : FrameWithIndex} (hframe : frame ∈ cfg'.stackWithIndex) :
    (frame ∈ cfg.stackWithIndex ∧ frame.index < cfg.stack.length - 1) ∨
    (∃ lastFrame, cfg.stack.getLast? = some lastFrame ∧
      frame.regionId = lastFrame.regionId ∧ frame.bridgeVar = lastFrame.bridgeVar ∧
      frame.objMap = lastFrame.objMap ∧
      frame.varMap = lastFrame.varMap.insert x (Reference.OId cfg.freshObjectId) ∧
      frame.index = cfg.stack.dropLast.length) := by
  obtain ⟨lastFrame, region, hlast, hlookupRid, hopen, hcfg'⟩ := makeObjRegion_cases h
  have hstack' : cfg'.stack = cfg.stack.dropLast ++ [{ lastFrame with
      varMap := lastFrame.varMap.insert x (Reference.OId cfg.freshObjectId) }] := by rw [hcfg']
  have hstackEq : cfg.stack = cfg.stack.dropLast ++ [lastFrame] :=
    (List.dropLast_append_getLast? lastFrame hlast).symm
  unfold RuntimeConfig.stackWithIndex at hframe
  rw [hstack'] at hframe
  rw [List.mapIdx_concat] at hframe
  rcases List.mem_append.mp hframe with hmem | hmem
  · left
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hmem
    have hidx : frame.index = n := by rw [← hfeq]
    have hmem' : frame ∈ cfg.stackWithIndex := by
      unfold RuntimeConfig.stackWithIndex
      conv_lhs => rw [hstackEq]
      rw [List.mapIdx_concat]
      exact List.mem_append_left _ hmem
    refine ⟨hmem', ?_⟩
    rw [hidx, ← List.length_dropLast]
    exact hn
  · right
    rw [List.mem_singleton] at hmem
    subst hmem
    exact ⟨lastFrame, hlast, rfl, rfl, rfl, rfl, rfl⟩

-- A pre-existing frame with index strictly below the last one survives `makeObjRegion`
-- unchanged, at the same index.
theorem makeObjRegion_frame_mem_up {cfg cfg' : RuntimeConfig} {x : VarName}
    (h : makeObjRegion x cfg = some cfg')
    {frame : FrameWithIndex} (hframe : frame ∈ cfg.stackWithIndex) (hlt : frame.index < cfg.stack.length - 1) :
    frame ∈ cfg'.stackWithIndex := by
  obtain ⟨lastFrame, region, hlast, hlookupRid, hopen, hcfg'⟩ := makeObjRegion_cases h
  have hstack' : cfg'.stack = cfg.stack.dropLast ++ [{ lastFrame with
      varMap := lastFrame.varMap.insert x (Reference.OId cfg.freshObjectId) }] := by rw [hcfg']
  unfold RuntimeConfig.stackWithIndex at hframe ⊢
  rw [hstack']
  obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hframe
  have hidx : frame.index = n := by rw [← hfeq]
  have hnlt : n < cfg.stack.dropLast.length := by rw [List.length_dropLast]; rw [hidx] at hlt; exact hlt
  apply List.mem_mapIdx.mpr
  refine ⟨n, ?_, ?_⟩
  · rw [List.length_append]; omega
  · rw [List.getElem_append_left hnlt, List.getElem_dropLast hnlt]
    exact hfeq

-- A frame strictly before the last one has a different regionId from the last frame's own
-- (S1: regionId is injective across the stack).
theorem makeObjRegion_regionId_ne {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {f : FrameWithIndex} (hf : f ∈ cfg.stackWithIndex) (hflt : f.index < cfg.stack.length - 1)
    {lastFrame : Frame} (hlast : cfg.stack.getLast? = some lastFrame) :
    f.regionId ≠ lastFrame.regionId := by
  intro heq
  have hlastMem := stackWithIndex_getLast_mem hlast
  have hidxEq : f.index = ({ lastFrame with index := cfg.stack.length - 1 } : FrameWithIndex).index :=
    merge_corollary_regionId_unique_index vcfg.s1 hf hlastMem heq
  dsimp only at hidxEq
  rw [hidxEq] at hflt
  exact absurd hflt (lt_irrefl _)

-- `FrameReachable` agrees between `cfg`/`cfg'`, both directions, for any frame with index
-- strictly below the last one (content is literally untouched there, up to `ReachableStep`
-- agreeing everywhere via `makeObjRegion_step_eq`; the one new wrinkle relative to
-- `makeObjStack` is transporting a `FrameRoot`'s bridge-object heap lookup, needing the
-- regionId-disjointness fact above since the heap really is touched here).
theorem makeObjRegion_frame_reachable_iff {cfg cfg' : RuntimeConfig} {x : VarName} (vcfg : ValidConfig cfg)
    (h : makeObjRegion x cfg = some cfg')
    {X : FrameWithIndex} (_hXmem : X ∈ cfg.stackWithIndex) (hXlt : X.index < cfg.stack.length - 1)
    (ref : Reference) : FrameReachable cfg X.index ref ↔ FrameReachable cfg' X.index ref := by
  obtain ⟨lastFrame, region, hlast, hlookupRid, hopen, hcfg'⟩ := makeObjRegion_cases h
  rw [FrameReachable_iff_reflTransGen, FrameReachable_iff_reflTransGen, makeObjRegion_step_eq vcfg h]
  constructor
  · rintro ⟨start, hroot, hrtg⟩
    refine ⟨start, ?_, hrtg⟩
    rcases hroot with ⟨Xf, hXfmem, hXfidx, var, hvar⟩ | ⟨Xf, hXfmem, hXfidx, regionX, hlookup, hbridge⟩
    · exact Or.inl ⟨Xf, makeObjRegion_frame_mem_up h hXfmem (hXfidx ▸ hXlt), hXfidx, var, hvar⟩
    · have hXfne : Xf.regionId ≠ lastFrame.regionId :=
        makeObjRegion_regionId_ne vcfg hXfmem (hXfidx ▸ hXlt) hlast
      have hlookup' : cfg'.heap.lookup Xf.regionId = some regionX := by
        rw [hcfg']; dsimp only; rw [AList.lookup_insert_ne hXfne]; exact hlookup
      exact Or.inr ⟨Xf, makeObjRegion_frame_mem_up h hXfmem (hXfidx ▸ hXlt), hXfidx, regionX, hlookup', hbridge⟩
  · rintro ⟨start, hroot, hrtg⟩
    refine ⟨start, ?_, hrtg⟩
    rcases hroot with ⟨Xf, hXfmem, hXfidx, var, hvar⟩ | ⟨Xf, hXfmem, hXfidx, regionX, hlookup, hbridge⟩
    · rcases makeObjRegion_frame_cases h hXfmem with ⟨hXfmemcfg, -⟩ | ⟨lf, hlf, -, -, -, -, hXfidx2⟩
      · exact Or.inl ⟨Xf, hXfmemcfg, hXfidx, var, hvar⟩
      · exfalso
        rw [hlast] at hlf
        injection hlf with hlf
        subst hlf
        have hXeq : X.index = cfg.stack.dropLast.length := by rw [← hXfidx, hXfidx2]
        rw [hXeq, List.length_dropLast] at hXlt
        exact absurd hXlt (lt_irrefl _)
    · rcases makeObjRegion_frame_cases h hXfmem with ⟨hXfmemcfg, hXflt⟩ | ⟨lf, hlf, -, -, -, -, hXfidx2⟩
      · have hXfne : Xf.regionId ≠ lastFrame.regionId :=
          makeObjRegion_regionId_ne vcfg hXfmemcfg hXflt hlast
        have hlookupcfg : cfg.heap.lookup Xf.regionId = some regionX := by
          rw [hcfg'] at hlookup; dsimp only at hlookup
          rw [AList.lookup_insert_ne hXfne] at hlookup; exact hlookup
        exact Or.inr ⟨Xf, hXfmemcfg, hXfidx, regionX, hlookupcfg, hbridge⟩
      · exfalso
        rw [hlast] at hlf
        injection hlf with hlf
        subst hlf
        have hXeq : X.index = cfg.stack.dropLast.length := by rw [← hXfidx, hXfidx2]
        rw [hXeq, List.length_dropLast] at hXlt
        exact absurd hXlt (lt_irrefl _)

-- ===== makeRegion =====

-- A step sourced at the freshly-allocated region id is always impossible (the region doesn't
-- exist yet, so `deref?`'s heap lookup guard fails).
theorem freshRegionId_no_step {cfg : RuntimeConfig} {b : Reference} :
    ¬ ReachableStep cfg (Reference.RId cfg.freshRegionId) b := by
  rw [ReachableStep_rid_iff]
  rintro ⟨region, hlookup, -, -⟩
  apply RuntimeConfig.freshRegionId_not_mem cfg
  rw [← AList.mem_keys, ← AList.lookup_isSome, hlookup]
  simp

-- The freshly-created region's own bridge object always resolves into the heap, at the fresh
-- region id itself (never onto the stack, since no frame's `objMap` is ever touched by
-- `makeRegion`).
theorem makeRegion_corollary_loc_fresh {cfg cfg' : RuntimeConfig} {x : VarName}
    (h : makeRegion x cfg = some cfg') :
    (Reference.OId cfg.freshObjectId).loc? cfg' = some (Location.Rgn cfg.freshRegionId) := by
  obtain ⟨frame, hlast, hcfg'⟩ := makeRegion_cases h
  have fresh_not_in_any_frame : ∀ f ∈ cfg.stack, cfg.freshObjectId ∉ f.objMap.keys := by
    intro f hf hmem
    apply RuntimeConfig.freshObjectId_not_mem cfg
    unfold RuntimeConfig.objectIds Stack.objectIds Frame.objectIds
    rw [List.bind_eq_flatMap, List.flatMap_id, List.mem_append, List.mem_flatten]
    exact Or.inl ⟨f.objMap.keys, List.mem_map_of_mem hf, hmem⟩
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
    (List.dropLast_append_getLast? frame hlast).symm
  have frame_mem : frame ∈ cfg.stack := stack_eq ▸ List.mem_append_right _ (List.mem_singleton_self frame)
  set newFrame : Frame :=
    { regionId := frame.regionId, bridgeVar := frame.bridgeVar, objMap := frame.objMap,
      varMap := frame.varMap.insert x (Reference.RId cfg.freshRegionId) } with newFrame_def
  set newRegionVal : Region :=
    { bridgeObjectId := cfg.freshObjectId, objMap := (∅ : ObjMap).insert cfg.freshObjectId ∅,
      status := Status.Closed } with newRegionVal_def
  have dropLast_h1_none :
      List.find? (fun f => (AList.keys f.objMap).contains cfg.freshObjectId)
        (List.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex))
          cfg.stack.dropLast).reverse = none := by
    rw [List.find?_eq_none]
    intro f hf
    rw [List.mem_reverse] at hf
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hf
    intro hc
    apply fresh_not_in_any_frame cfg.stack.dropLast[n]
      (List.mem_of_mem_dropLast (List.mem_iff_getElem.mpr ⟨n, hn, rfl⟩))
    rw [← hfeq] at hc
    dsimp at hc
    exact List.contains_iff_mem.mp hc
  have h1_none :
      cfg'.stackWithIndex.findRev?
        (fun f => (AList.keys f.objMap).contains cfg.freshObjectId) = none := by
    rw [hcfg']
    unfold RuntimeConfig.stackWithIndex
    dsimp
    rw [List.mapIdx_concat, List.findRev?_eq_find?_reverse, List.reverse_append,
      List.reverse_singleton, List.singleton_append]
    have hnewFrame_false : ¬ (AList.keys ({ newFrame with
          index := cfg.stack.dropLast.length } : FrameWithIndex).objMap).contains
        cfg.freshObjectId = true := by
      dsimp
      intro hc
      exact fresh_not_in_any_frame frame frame_mem (List.contains_iff_mem.mp hc)
    have find_eq :
        List.find? (fun f => (AList.keys f.objMap).contains cfg.freshObjectId)
          (({ newFrame with index := cfg.stack.dropLast.length } : FrameWithIndex) ::
            (List.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex))
              cfg.stack.dropLast).reverse) =
        List.find? (fun f => (AList.keys f.objMap).contains cfg.freshObjectId)
          (List.mapIdx (fun idx f => ({ f with index := idx } : FrameWithIndex))
            cfg.stack.dropLast).reverse :=
      List.find?_cons_of_neg hnewFrame_false
    rw [find_eq, dropLast_h1_none]
  have h2_some :
      cfg'.heap.entries.find?
        (fun p => (AList.keys p.snd.objMap).contains cfg.freshObjectId) =
      some (⟨cfg.freshRegionId, newRegionVal⟩ : Sigma (fun _ : RegionId => Region)) := by
    rw [hcfg']
    dsimp
    rw [List.kerase_of_notMem_keys (RuntimeConfig.freshRegionId_not_mem cfg)]
    have hpos : (AList.keys newRegionVal.objMap).contains cfg.freshObjectId = true := by
      rw [newRegionVal_def]
      dsimp
      simp
    exact List.find?_cons_of_pos hpos
  unfold Reference.loc?
  dsimp
  rw [h1_none, h2_some]

-- `objAt?` agrees between `cfg`/`cfg'` for any oid other than the freshly-allocated one. The
-- heap side is a genuinely fresh key insert (no reordering of any existing entry); the stack
-- side is unconditional (only `varMap` changes, never `objMap`).
theorem makeRegion_objAt_eq_of_ne {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeRegion x cfg = some cfg') {oid : ObjectId} (hne : oid ≠ cfg.freshObjectId) :
    (Reference.OId oid).objAt? cfg = (Reference.OId oid).objAt? cfg' := by
  obtain ⟨frame, hlast, hcfg'⟩ := makeRegion_cases h
  have hlocEq := makeRegion_corollary_loc_eq vcfg h oid hne
  unfold Reference.objAt?
  dsimp only
  rw [hlocEq]
  cases hloc' : (Reference.OId oid).loc? cfg' with
  | none => rfl
  | some loc =>
    cases loc with
    | Rgn rid0 =>
      dsimp only
      have hlocCfg : (Reference.OId oid).loc? cfg = some (Location.Rgn rid0) := by rw [hlocEq]; exact hloc'
      obtain ⟨regionR, hlookupR, -⟩ := (oid_loc_rgn_iff_in_heap vcfg).mp hlocCfg
      have hne' : rid0 ≠ cfg.freshRegionId := by
        intro heq
        apply RuntimeConfig.freshRegionId_not_mem cfg
        rw [← AList.mem_keys, ← AList.lookup_isSome, ← heq, hlookupR]
        simp
      have hlookup' : cfg'.heap.lookup rid0 = cfg.heap.lookup rid0 := by
        rw [hcfg']; dsimp only; rw [AList.lookup_insert_ne hne']
      rw [hlookup']
    | Stk fid0 =>
      dsimp only
      rw [stackWithIndex_find_index_eq_getElem, stackWithIndex_find_index_eq_getElem]
      have hshape := stackWithIndex_objMap_get_eq_of_last_varMap_update (cfg' := cfg') hlast (by rw [hcfg'])
      have hgetCfg : cfg.stackWithIndex[fid0]? =
          (cfg.stack[fid0]?).map (fun f => ({ toFrame := f, index := fid0 } : FrameWithIndex)) := by
        unfold RuntimeConfig.stackWithIndex; rw [List.getElem?_mapIdx]
      have hgetCfg' : cfg'.stackWithIndex[fid0]? =
          (cfg'.stack[fid0]?).map (fun f => ({ toFrame := f, index := fid0 } : FrameWithIndex)) := by
        unfold RuntimeConfig.stackWithIndex; rw [List.getElem?_mapIdx]
      rw [hgetCfg, hgetCfg']
      cases hc : cfg.stack[fid0]? with
      | none =>
        have hc' : cfg'.stack[fid0]? = none := by
          have hs := hshape fid0; rw [hc] at hs; simpa using hs.symm
        rw [hc']
      | some fA =>
        cases hc' : cfg'.stack[fid0]? with
        | none => have hs := hshape fid0; rw [hc, hc'] at hs; simp at hs
        | some fB =>
          have hobjmapEq : fA.objMap = fB.objMap := by
            have hs := hshape fid0; rw [hc, hc'] at hs; simpa using hs
          simp only [Option.map_some]
          dsimp only [Option.bind]
          rw [hobjmapEq]

-- The freshly-allocated object resolves to its own (empty) content in cfg'.
theorem makeRegion_fresh_objAt_cfg' {cfg cfg' : RuntimeConfig} {x : VarName}
    (h : makeRegion x cfg = some cfg') :
    (Reference.OId cfg.freshObjectId).objAt? cfg' = some (∅ : Object) := by
  have hlocFresh := makeRegion_corollary_loc_fresh h
  unfold Reference.objAt?
  dsimp only
  rw [hlocFresh]
  dsimp only
  obtain ⟨frame, hlast, hcfg'⟩ := makeRegion_cases h
  have hlookup' : cfg'.heap.lookup cfg.freshRegionId = some ({ bridgeObjectId := cfg.freshObjectId, objMap := (∅ : ObjMap).insert cfg.freshObjectId ∅, status := Status.Closed } : Region) := by
    rw [hcfg']; dsimp only; rw [AList.lookup_insert]
  rw [hlookup']
  dsimp only [Option.bind]
  rw [AList.lookup_insert]

-- `ReachableStep` agrees between `cfg`/`cfg'` for every OId-sourced step: unconditionally for
-- `oid ≠ freshObjectId`, and vacuously for the freshly-allocated id itself (resolves nowhere in
-- `cfg`, resolves to the empty object -- no refs -- in `cfg'`).
theorem makeRegion_oid_step_iff {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeRegion x cfg = some cfg') (oid : ObjectId) (b : Reference) :
    ReachableStep cfg (Reference.OId oid) b ↔ ReachableStep cfg' (Reference.OId oid) b := by
  by_cases hne : oid = cfg.freshObjectId
  · subst hne
    constructor
    · intro hstep
      rw [ReachableStep_oid_iff] at hstep
      obtain ⟨obj, hobjAt, -⟩ := hstep
      rw [freshObjectId_objAt_none] at hobjAt
      exact absurd hobjAt (by simp)
    · intro hstep
      rw [ReachableStep_oid_iff] at hstep
      obtain ⟨obj, hobjAt, hcontains⟩ := hstep
      rw [makeRegion_fresh_objAt_cfg' h] at hobjAt
      injection hobjAt with hobjAt
      rw [← hobjAt] at hcontains
      simp [Object.refs] at hcontains
  · rw [ReachableStep_oid_iff, ReachableStep_oid_iff, makeRegion_objAt_eq_of_ne vcfg h hne]

-- `ReachableStep` agrees between `cfg`/`cfg'` for every RId-sourced step: the freshly-created
-- region is vacuous on both sides (doesn't exist in `cfg`; its bridge object is empty -- no refs
-- -- in `cfg'`); every other heap key is untouched (a genuinely fresh key insert).
theorem makeRegion_rid_step_iff {cfg cfg' : RuntimeConfig}
    (h : makeRegion x cfg = some cfg') (rid : RegionId) (b : Reference) :
    ReachableStep cfg (Reference.RId rid) b ↔ ReachableStep cfg' (Reference.RId rid) b := by
  obtain ⟨frame, hlast, hcfg'⟩ := makeRegion_cases h
  by_cases heq : rid = cfg.freshRegionId
  · subst heq
    constructor
    · intro hstep; exact absurd hstep freshRegionId_no_step
    · intro hstep
      exfalso
      rw [ReachableStep_rid_iff] at hstep
      obtain ⟨region, hlookup, -, obj, hobjlookup, hcontains⟩ := hstep
      have hlookup' : cfg'.heap.lookup cfg.freshRegionId = some ({ bridgeObjectId := cfg.freshObjectId, objMap := (∅ : ObjMap).insert cfg.freshObjectId ∅, status := Status.Closed } : Region) := by
        rw [hcfg']; dsimp only; rw [AList.lookup_insert]
      rw [hlookup'] at hlookup
      injection hlookup with hlookupEq
      rw [← hlookupEq] at hobjlookup
      dsimp only at hobjlookup
      rw [AList.lookup_insert] at hobjlookup
      injection hobjlookup with hobjlookup
      rw [← hobjlookup] at hcontains
      simp [Object.refs] at hcontains
  · have hlookup' : cfg'.heap.lookup rid = cfg.heap.lookup rid := by
      rw [hcfg']; dsimp only; rw [AList.lookup_insert_ne heq]
    rw [ReachableStep_rid_iff, ReachableStep_rid_iff, hlookup']

-- `ReachableStep` agrees between `cfg`/`cfg'` completely, as a literal function equality.
theorem makeRegion_step_eq {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : makeRegion x cfg = some cfg') :
    ReachableStep cfg = ReachableStep cfg' := by
  funext a b
  apply propext
  cases a with
  | OId oid => exact makeRegion_oid_step_iff vcfg h oid b
  | RId rid => exact makeRegion_rid_step_iff h rid b

-- Every `cfg'.stackWithIndex` member is either a pre-existing, content-unchanged frame (index
-- strictly below the last one) or exactly the last frame with `varMap` updated.
theorem makeRegion_frame_cases {cfg cfg' : RuntimeConfig} {x : VarName}
    (h : makeRegion x cfg = some cfg')
    {frame : FrameWithIndex} (hframe : frame ∈ cfg'.stackWithIndex) :
    (frame ∈ cfg.stackWithIndex ∧ frame.index < cfg.stack.length - 1) ∨
    (∃ lastFrame, cfg.stack.getLast? = some lastFrame ∧
      frame.regionId = lastFrame.regionId ∧ frame.bridgeVar = lastFrame.bridgeVar ∧
      frame.objMap = lastFrame.objMap ∧
      frame.varMap = lastFrame.varMap.insert x (Reference.RId cfg.freshRegionId) ∧
      frame.index = cfg.stack.dropLast.length) := by
  obtain ⟨lastFrame, hlast, hcfg'⟩ := makeRegion_cases h
  have hstack' : cfg'.stack = cfg.stack.dropLast ++ [{ lastFrame with
      varMap := lastFrame.varMap.insert x (Reference.RId cfg.freshRegionId) }] := by rw [hcfg']
  have hstackEq : cfg.stack = cfg.stack.dropLast ++ [lastFrame] :=
    (List.dropLast_append_getLast? lastFrame hlast).symm
  unfold RuntimeConfig.stackWithIndex at hframe
  rw [hstack'] at hframe
  rw [List.mapIdx_concat] at hframe
  rcases List.mem_append.mp hframe with hmem | hmem
  · left
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hmem
    have hidx : frame.index = n := by rw [← hfeq]
    have hmem' : frame ∈ cfg.stackWithIndex := by
      unfold RuntimeConfig.stackWithIndex
      conv_lhs => rw [hstackEq]
      rw [List.mapIdx_concat]
      exact List.mem_append_left _ hmem
    refine ⟨hmem', ?_⟩
    rw [hidx, ← List.length_dropLast]
    exact hn
  · right
    rw [List.mem_singleton] at hmem
    subst hmem
    exact ⟨lastFrame, hlast, rfl, rfl, rfl, rfl, rfl⟩

-- A pre-existing frame with index strictly below the last one survives `makeRegion` unchanged,
-- at the same index.
theorem makeRegion_frame_mem_up {cfg cfg' : RuntimeConfig} {x : VarName}
    (h : makeRegion x cfg = some cfg')
    {frame : FrameWithIndex} (hframe : frame ∈ cfg.stackWithIndex) (hlt : frame.index < cfg.stack.length - 1) :
    frame ∈ cfg'.stackWithIndex := by
  obtain ⟨lastFrame, hlast, hcfg'⟩ := makeRegion_cases h
  have hstack' : cfg'.stack = cfg.stack.dropLast ++ [{ lastFrame with
      varMap := lastFrame.varMap.insert x (Reference.RId cfg.freshRegionId) }] := by rw [hcfg']
  unfold RuntimeConfig.stackWithIndex at hframe ⊢
  rw [hstack']
  obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hframe
  have hidx : frame.index = n := by rw [← hfeq]
  have hnlt : n < cfg.stack.dropLast.length := by rw [List.length_dropLast]; rw [hidx] at hlt; exact hlt
  apply List.mem_mapIdx.mpr
  refine ⟨n, ?_, ?_⟩
  · rw [List.length_append]; omega
  · rw [List.getElem_append_left hnlt, List.getElem_dropLast hnlt]
    exact hfeq

-- `FrameReachable` agrees between `cfg`/`cfg'`, both directions, for any frame with index
-- strictly below the last one. Unlike `makeObjRegion`, no `S1`-based regionId-uniqueness
-- argument is needed to transport a `FrameRoot`'s bridge-object heap lookup: `makeRegion`'s heap
-- change is a genuinely *fresh* key insert, so any *existing* regionId (from a successful heap
-- lookup, on either side) automatically differs from it.
theorem makeRegion_frame_reachable_iff {cfg cfg' : RuntimeConfig} {x : VarName} (vcfg : ValidConfig cfg)
    (h : makeRegion x cfg = some cfg')
    {X : FrameWithIndex} (_hXmem : X ∈ cfg.stackWithIndex) (hXlt : X.index < cfg.stack.length - 1)
    (ref : Reference) : FrameReachable cfg X.index ref ↔ FrameReachable cfg' X.index ref := by
  obtain ⟨lastFrame, hlast, hcfg'⟩ := makeRegion_cases h
  rw [FrameReachable_iff_reflTransGen, FrameReachable_iff_reflTransGen, makeRegion_step_eq vcfg h]
  constructor
  · rintro ⟨start, hroot, hrtg⟩
    refine ⟨start, ?_, hrtg⟩
    rcases hroot with ⟨Xf, hXfmem, hXfidx, var, hvar⟩ | ⟨Xf, hXfmem, hXfidx, regionX, hlookup, hbridge⟩
    · exact Or.inl ⟨Xf, makeRegion_frame_mem_up h hXfmem (hXfidx ▸ hXlt), hXfidx, var, hvar⟩
    · have hXfne : Xf.regionId ≠ cfg.freshRegionId := by
        intro heq
        apply RuntimeConfig.freshRegionId_not_mem cfg
        rw [← AList.mem_keys, ← AList.lookup_isSome, ← heq, hlookup]
        simp
      have hlookup' : cfg'.heap.lookup Xf.regionId = some regionX := by
        rw [hcfg']; dsimp only; rw [AList.lookup_insert_ne hXfne]; exact hlookup
      exact Or.inr ⟨Xf, makeRegion_frame_mem_up h hXfmem (hXfidx ▸ hXlt), hXfidx, regionX, hlookup', hbridge⟩
  · rintro ⟨start, hroot, hrtg⟩
    refine ⟨start, ?_, hrtg⟩
    rcases hroot with ⟨Xf, hXfmem, hXfidx, var, hvar⟩ | ⟨Xf, hXfmem, hXfidx, regionX, hlookup, hbridge⟩
    · rcases makeRegion_frame_cases h hXfmem with ⟨hXfmemcfg, -⟩ | ⟨lf, hlf, -, -, -, -, hXfidx2⟩
      · exact Or.inl ⟨Xf, hXfmemcfg, hXfidx, var, hvar⟩
      · exfalso
        have hXeq : X.index = cfg.stack.dropLast.length := by rw [← hXfidx, hXfidx2]
        rw [hXeq, List.length_dropLast] at hXlt
        exact absurd hXlt (lt_irrefl _)
    · rcases makeRegion_frame_cases h hXfmem with ⟨hXfmemcfg, hXflt⟩ | ⟨lf, hlf, -, -, -, -, hXfidx2⟩
      · obtain ⟨regionCfg, hlookupCfg, -⟩ := l2_of_stackWithIndex vcfg hXfmemcfg
        have hXfne : Xf.regionId ≠ cfg.freshRegionId := by
          intro heq
          apply RuntimeConfig.freshRegionId_not_mem cfg
          rw [← AList.mem_keys, ← AList.lookup_isSome, ← heq, hlookupCfg]
          simp
        have hlookupcfg : cfg.heap.lookup Xf.regionId = some regionX := by
          rw [hcfg'] at hlookup; dsimp only at hlookup
          rw [AList.lookup_insert_ne hXfne] at hlookup; exact hlookup
        exact Or.inr ⟨Xf, hXfmemcfg, hXfidx, regionX, hlookupcfg, hbridge⟩
      · exfalso
        have hXeq : X.index = cfg.stack.dropLast.length := by rw [← hXfidx, hXfidx2]
        rw [hXeq, List.length_dropLast] at hXlt
        exact absurd hXlt (lt_irrefl _)

-- ===== varAsgn =====

-- A successful `resolveV` traces back to a genuine `FrameRoot`: either an ordinary `varMap`
-- entry, or the resolving frame's own bridge var. Re-derived independently of
-- `Gc.Reachability.Referencable`'s copy of the same fact.
theorem resolveV_frameRoot {cfg : RuntimeConfig} {var : VarName} {oid : ObjectId}
    (hrv : resolveV var cfg = some (Reference.OId oid)) :
    ∃ frameY : FrameWithIndex, frameY ∈ cfg.stackWithIndex ∧ FrameRoot cfg frameY.index (Reference.OId oid) := by
  unfold resolveV at hrv
  cases hfV : cfg.stackWithIndex.findRev? (fun frame => frame.varMap.keys.contains var ∨ frame.bridgeVar == var) with
  | none => rw [hfV] at hrv; contradiction
  | some frameV =>
    rw [hfV] at hrv
    dsimp at hrv
    have hframeV_mem : frameV ∈ cfg.stackWithIndex := by
      rw [List.findRev?_eq_find?_reverse] at hfV
      exact List.mem_reverse.mp (List.mem_of_find?_eq_some hfV)
    cases hlookupV : frameV.varMap.lookup var with
    | some refV =>
      rw [hlookupV] at hrv
      dsimp at hrv
      rw [Option.some_inj] at hrv
      subst hrv
      exact ⟨frameV, hframeV_mem, Or.inl ⟨frameV, hframeV_mem, rfl, var, hlookupV⟩⟩
    | none =>
      rw [hlookupV] at hrv
      dsimp at hrv
      by_cases hbv : frameV.bridgeVar == var
      · rw [if_pos hbv] at hrv
        cases hregionV : cfg.heap.lookup frameV.regionId with
        | none => rw [hregionV] at hrv; dsimp at hrv; contradiction
        | some regionV =>
          rw [hregionV] at hrv
          dsimp at hrv
          rw [Option.some_inj, Reference.OId.injEq] at hrv
          exact ⟨frameV, hframeV_mem, Or.inr ⟨frameV, hframeV_mem, rfl, regionV, hregionV, by rw [hrv]⟩⟩
      · rw [if_neg hbv] at hrv; contradiction

-- A successful `resolveFA` traces back to a genuine `FrameReachable`: the root var/bridge value
-- resolves via `resolveV_frameRoot`, and the field access itself is exactly one more
-- `ReachableStep` hop. Re-derived independently of `Gc.Reachability.Referencable`'s copy.
theorem resolveFA_frameReach {cfg : RuntimeConfig} {y : FieldAccess} {oid : ObjectId}
    (hyf : resolveFA y cfg = some (Reference.OId oid)) :
    ∃ frameY : FrameWithIndex, frameY ∈ cfg.stackWithIndex ∧ FrameReachable cfg frameY.index (Reference.OId oid) := by
  unfold resolveFA at hyf
  cases hrv : resolveV y.root cfg with
  | none => rw [hrv] at hyf; contradiction
  | some ref0 =>
    rw [hrv] at hyf
    dsimp at hyf
    cases ref0 with
    | RId rid0 => dsimp at hyf; contradiction
    | OId oid0 =>
      dsimp at hyf
      cases hloc0 : (Reference.OId oid0).loc? cfg with
      | none => rw [hloc0] at hyf; dsimp at hyf; contradiction
      | some loc0 =>
        rw [hloc0] at hyf
        dsimp at hyf
        obtain ⟨frameY, hframeYMem, hrootY⟩ := resolveV_frameRoot hrv
        have hreachY0 : FrameReachable cfg frameY.index (Reference.OId oid0) := by
          rw [FrameReachable_iff_reflTransGen]
          exact ⟨Reference.OId oid0, hrootY, Relation.ReflTransGen.refl⟩
        cases loc0 with
        | Stk fid0 =>
          dsimp at hyf
          cases hframe0 : cfg.stackWithIndex.find? (fun frame => frame.index == fid0) with
          | none => rw [hframe0] at hyf; dsimp at hyf; contradiction
          | some frame0 =>
            rw [hframe0] at hyf
            dsimp at hyf
            cases hobj0 : frame0.objMap.lookup oid0 with
            | none => rw [hobj0] at hyf; dsimp at hyf; contradiction
            | some obj0 =>
              rw [hobj0] at hyf
              dsimp at hyf
              have hobjAt0 : (Reference.OId oid0).objAt? cfg = some obj0 := by
                unfold Reference.objAt?
                dsimp only
                rw [hloc0]
                dsimp only
                rw [hframe0]
                exact hobj0
              have hstep0 : ReachableStep cfg (Reference.OId oid0) (Reference.OId oid) := by
                rw [ReachableStep_oid_iff]
                exact ⟨obj0, hobjAt0,
                  List.contains_iff_mem.mpr (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hyf))⟩
              exact ⟨frameY, hframeYMem, FrameReachable.step hstep0 hreachY0⟩
        | Rgn rid0 =>
          dsimp at hyf
          cases hregion0 : cfg.heap.lookup rid0 with
          | none => rw [hregion0] at hyf; dsimp at hyf; contradiction
          | some region0 =>
            rw [hregion0] at hyf
            dsimp at hyf
            cases hobj0 : region0.objMap.lookup oid0 with
            | none => rw [hobj0] at hyf; dsimp at hyf; contradiction
            | some obj0 =>
              rw [hobj0] at hyf
              dsimp at hyf
              have hobjAt0 : (Reference.OId oid0).objAt? cfg = some obj0 := by
                unfold Reference.objAt?
                dsimp only
                rw [hloc0]
                dsimp only
                rw [hregion0]
                exact hobj0
              have hstep0 : ReachableStep cfg (Reference.OId oid0) (Reference.OId oid) := by
                rw [ReachableStep_oid_iff]
                exact ⟨obj0, hobjAt0,
                  List.contains_iff_mem.mpr (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hyf))⟩
              exact ⟨frameY, hframeYMem, FrameReachable.step hstep0 hreachY0⟩

-- `RegionReachable`'s H3-confinement, lifted along the whole inductive chain: any `OId`-typed
-- element reached from region `rid`'s own bridge object resolves either back inside `rid` itself,
-- or inside some *other* region that was entered via a Closed-region RId hop somewhere along the
-- way (never onto the stack, and never into an arbitrary Open region).
theorem RegionReachable_oid_confined {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid : RegionId} {region : Region} (hlookup : cfg.heap.lookup rid = some region)
    {ref : Reference} (hrr : RegionReachable cfg rid ref) :
    (∃ oid ridCur region', ref = Reference.OId oid ∧ (Reference.OId oid).loc? cfg = some (Location.Rgn ridCur) ∧
       cfg.heap.lookup ridCur = some region' ∧ (ridCur = rid ∨ region'.status = Status.Closed)) ∨
    (∃ ridR, ref = Reference.RId ridR) := by
  induction hrr with
  | bridge hlk hbridge =>
    rename_i region0 oid0 cfg0 rid0
    subst hbridge
    left
    have hbridgeIn : region0.bridgeObjectId ∈ region0.objMap := by
      apply vcfg.h1
      unfold Heap.regions
      exact List.mem_map_of_mem (AList.lookup_mem_entries hlk)
    have hlocb : (Reference.OId region0.bridgeObjectId).loc? cfg0 = some (Location.Rgn rid0) :=
      (oid_loc_rgn_iff_in_heap vcfg).mpr ⟨region0, hlk, hbridgeIn⟩
    exact ⟨region0.bridgeObjectId, rid0, region0, rfl, hlocb, hlk, Or.inl rfl⟩
  | step hstep hrr' ih =>
    rename_i cfg0 refPrime refCur rid0
    have ih' := ih vcfg hlookup
    have hmemrefs : ∃ ridCur region', refCur ∈ region'.refs ∧ cfg0.heap.lookup ridCur = some region' ∧
        (ridCur = rid0 ∨ region'.status = Status.Closed) := by
      rcases ih' with ⟨oidA, ridCur, region', heqA, hlocA, hlkA, hcaseA⟩ | ⟨ridA, heqA⟩
      · subst heqA
        rw [ReachableStep_oid_iff] at hstep
        obtain ⟨obj, hobjAt, hcontains⟩ := hstep
        unfold Reference.objAt? at hobjAt
        dsimp only at hobjAt
        rw [hlocA] at hobjAt
        dsimp only at hobjAt
        rw [hlkA] at hobjAt
        exact ⟨ridCur, region', mem_region_refs_of_mem_objMap hobjAt (List.contains_iff_mem.mp hcontains), hlkA, hcaseA⟩
      · subst heqA
        rw [ReachableStep_rid_iff] at hstep
        obtain ⟨regionR, hlkR, hclosedR, obj, hobjlookup, hcontains⟩ := hstep
        exact ⟨ridA, regionR, mem_region_refs_of_mem_objMap hobjlookup (List.contains_iff_mem.mp hcontains),
          hlkR, Or.inr hclosedR⟩
    obtain ⟨ridCur, region', hmemB, hlkCur, hcaseCur⟩ := hmemrefs
    cases refCur with
    | OId oidB =>
      left
      have hridEq := vcfg.h3 ridCur oidB region' hlkCur hmemB
      exact ⟨oidB, ridCur, region', rfl, hridEq, hlkCur, hcaseCur⟩
    | RId ridB => right; exact ⟨ridB, rfl⟩

-- The specific contradiction `varAsgn`'s bridge-var branch needs: a chain rooted at region
-- `rid`'s own (Open) bridge object can never reach an object confirmed to live in some *other*,
-- also-Open region -- confinement (above) forces it to resolve either back inside `rid` or inside
-- a Closed region, neither of which a distinct Open region can be.
theorem region_reachable_open_ne_absurd {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid : RegionId} {region : Region} (hlookup : cfg.heap.lookup rid = some region)
    {oidTarget : ObjectId} {ridT : RegionId} {regionT : Region}
    (hlocT : (Reference.OId oidTarget).loc? cfg = some (Location.Rgn ridT))
    (hlkT : cfg.heap.lookup ridT = some regionT) (hopenT : regionT.status = Status.Open) (hne : ridT ≠ rid)
    (hrr : RegionReachable cfg rid (Reference.OId oidTarget)) : False := by
  rcases RegionReachable_oid_confined vcfg hlookup hrr with
    ⟨oid', ridCur, region', heq, hloc', hlk', hcase'⟩ | ⟨ridR, heq⟩
  · rw [Reference.OId.injEq] at heq
    subst heq
    rw [hlocT, Option.some_inj, Location.Rgn.injEq] at hloc'
    subst hloc'
    rw [hlkT, Option.some_inj] at hlk'
    subst hlk'
    rcases hcase' with hcaseEq | hcaseClosed
    · exact hne hcaseEq
    · rw [hopenT] at hcaseClosed
      exact absurd hcaseClosed (by decide)
  · exact absurd heq (by simp)

-- `objAt?` agrees between `cfg`/`cfg'` unconditionally, for every oid -- unlike
-- `makeObjStack`/`makeObjRegion`/`makeRegion`, `varAsgn` never allocates a fresh id, so there is
-- no exception to carve out.
theorem varAsgn_objAt_eq {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : varAsgn xf y cfg = some cfg') (oid : ObjectId) :
    (Reference.OId oid).objAt? cfg = (Reference.OId oid).objAt? cfg' := by
  obtain ⟨frame, hlast, hcase⟩ := varAsgn_cases h
  have hlocEq := varAsgn_corollary_loc_eq vcfg h oid
  unfold Reference.objAt?
  dsimp only
  rw [hlocEq]
  cases hloc' : (Reference.OId oid).loc? cfg' with
  | none => rfl
  | some loc =>
    cases loc with
    | Rgn rid0 =>
      dsimp only
      rcases hcase with ⟨oidY, rid, region, hyf, hxb, hloc, hridEq, hregion, hcfg'⟩ | ⟨oidY, hyf, hxb, hresolve, hcfg'⟩
      · by_cases heq : rid0 = rid
        · subst heq
          have hlookup' : cfg'.heap.lookup rid0 = some ({ region with bridgeObjectId := oidY } : Region) := by
            rw [hcfg']; dsimp only; rw [AList.lookup_insert]
          rw [hlookup', hregion]
          rfl
        · have hlookup' : cfg'.heap.lookup rid0 = cfg.heap.lookup rid0 := by
            rw [hcfg']; dsimp only; rw [AList.lookup_insert_ne heq]
          rw [hlookup']
      · have hlookup' : cfg'.heap.lookup rid0 = cfg.heap.lookup rid0 := by rw [hcfg']
        rw [hlookup']
    | Stk fid0 =>
      dsimp only
      rw [stackWithIndex_find_index_eq_getElem, stackWithIndex_find_index_eq_getElem]
      rcases hcase with ⟨oidY, rid, region, hyf, hxb, hloc, hridEq, hregion, hcfg'⟩ | ⟨oidY, hyf, hxb, hresolve, hcfg'⟩
      · have hstackEq : cfg'.stack = cfg.stack := by rw [hcfg']
        unfold RuntimeConfig.stackWithIndex
        rw [hstackEq]
      · have hshape := stackWithIndex_objMap_get_eq_of_last_varMap_update (cfg' := cfg') hlast (by rw [hcfg'])
        have hgetCfg : cfg.stackWithIndex[fid0]? =
            (cfg.stack[fid0]?).map (fun f => ({ toFrame := f, index := fid0 } : FrameWithIndex)) := by
          unfold RuntimeConfig.stackWithIndex; rw [List.getElem?_mapIdx]
        have hgetCfg' : cfg'.stackWithIndex[fid0]? =
            (cfg'.stack[fid0]?).map (fun f => ({ toFrame := f, index := fid0 } : FrameWithIndex)) := by
          unfold RuntimeConfig.stackWithIndex; rw [List.getElem?_mapIdx]
        rw [hgetCfg, hgetCfg']
        cases hc : cfg.stack[fid0]? with
        | none =>
          have hc' : cfg'.stack[fid0]? = none := by
            have hs := hshape fid0; rw [hc] at hs; simpa using hs.symm
          rw [hc']
        | some fA =>
          cases hc' : cfg'.stack[fid0]? with
          | none => have hs := hshape fid0; rw [hc, hc'] at hs; simp at hs
          | some fB =>
            have hobjmapEq : fA.objMap = fB.objMap := by
              have hs := hshape fid0; rw [hc, hc'] at hs; simpa using hs
            simp only [Option.map_some]
            dsimp only [Option.bind]
            rw [hobjmapEq]

-- `ReachableStep` agrees between `cfg`/`cfg'` for every RId-sourced step: the bridge-var branch
-- only ever mutates an *Open* region's `bridgeObjectId` scalar (never `objMap`), so no RId-sourced
-- step is ever possible from *that* region on either side (`open_rid_no_step`); every other heap
-- key -- and the fresh-var branch's heap entirely -- is untouched.
theorem varAsgn_rid_step_iff {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : varAsgn xf y cfg = some cfg') (rid : RegionId) (b : Reference) :
    ReachableStep cfg (Reference.RId rid) b ↔ ReachableStep cfg' (Reference.RId rid) b := by
  obtain ⟨frame, hlast, hcase⟩ := varAsgn_cases h
  rcases hcase with ⟨oid, rid0, region, hyf, hxb, hloc, hridEq, hregion, hcfg'⟩ | ⟨oid, hyf, hxb, hresolve, hcfg'⟩
  · by_cases heq : rid = rid0
    · subst heq
      have hlookup' : cfg'.heap.lookup rid = some ({ region with bridgeObjectId := oid } : Region) := by
        rw [hcfg']; dsimp only; rw [AList.lookup_insert]
      obtain ⟨region1, hlookup1, hopen1⟩ := l2_of_stackWithIndex vcfg (stackWithIndex_getLast_mem hlast)
      rw [hridEq, hregion] at hlookup1
      injection hlookup1 with hlookup1
      subst hlookup1
      constructor
      · intro hstep; exact absurd hstep (open_rid_no_step hregion hopen1)
      · intro hstep; exact absurd hstep (open_rid_no_step hlookup' hopen1)
    · have hlookup' : cfg'.heap.lookup rid = cfg.heap.lookup rid := by
        rw [hcfg']; dsimp only; rw [AList.lookup_insert_ne heq]
      rw [ReachableStep_rid_iff, ReachableStep_rid_iff, hlookup']
  · have hlookup' : cfg'.heap.lookup rid = cfg.heap.lookup rid := by rw [hcfg']
    rw [ReachableStep_rid_iff, ReachableStep_rid_iff, hlookup']

-- `ReachableStep` agrees between `cfg`/`cfg'` completely, as a literal function equality.
theorem varAsgn_step_eq {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : varAsgn xf y cfg = some cfg') :
    ReachableStep cfg = ReachableStep cfg' := by
  funext a b
  apply propext
  cases a with
  | OId oid => rw [ReachableStep_oid_iff, ReachableStep_oid_iff, varAsgn_objAt_eq vcfg h oid]
  | RId rid => exact varAsgn_rid_step_iff vcfg h rid b

-- `X.index < len - 1` membership in `cfg.stackWithIndex` agrees with membership in
-- `cfg'.stackWithIndex`, in both directions. The bridge-var branch never touches the stack at
-- all, so this holds unconditionally there; the fresh-var branch only inserts a fresh `varMap`
-- key into the *last* frame, leaving every other frame's record untouched.
theorem varAsgn_frame_mem_iff {cfg cfg' : RuntimeConfig}
    (h : varAsgn xf y cfg = some cfg')
    {X : FrameWithIndex} (hXlt : X.index < cfg.stack.length - 1) :
    X ∈ cfg.stackWithIndex ↔ X ∈ cfg'.stackWithIndex := by
  obtain ⟨frame, hlast, hcase⟩ := varAsgn_cases h
  rcases hcase with ⟨oid, rid, region, hyf, hxb, hloc, hridEq, hregion, hcfg'⟩ | ⟨oid, hyf, hxb, hresolve, hcfg'⟩
  · have hstackEq : cfg'.stack = cfg.stack := by rw [hcfg']
    unfold RuntimeConfig.stackWithIndex
    rw [hstackEq]
  · have hstack' : cfg'.stack = cfg.stack.dropLast ++ [{ frame with varMap := frame.varMap.insert xf (Reference.OId oid) }] := by
      rw [hcfg']
    have hstackEq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
      (List.dropLast_append_getLast? frame hlast).symm
    constructor
    · intro hXmem
      unfold RuntimeConfig.stackWithIndex
      rw [hstack']
      obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hXmem
      have hidx : X.index = n := by rw [← hfeq]
      have hnlt : n < cfg.stack.dropLast.length := by rw [List.length_dropLast]; rw [hidx] at hXlt; exact hXlt
      apply List.mem_mapIdx.mpr
      refine ⟨n, ?_, ?_⟩
      · rw [List.length_append]; omega
      · rw [List.getElem_append_left hnlt, List.getElem_dropLast hnlt]; exact hfeq
    · intro hXmem
      unfold RuntimeConfig.stackWithIndex at hXmem
      rw [hstack'] at hXmem
      rw [List.mapIdx_concat] at hXmem
      rcases List.mem_append.mp hXmem with hmem | hmem
      · obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hmem
        have hidx : X.index = n := by rw [← hfeq]
        unfold RuntimeConfig.stackWithIndex
        conv_lhs => rw [hstackEq]
        rw [List.mapIdx_concat]
        exact List.mem_append_left _ hmem
      · exfalso
        rw [List.mem_singleton] at hmem
        have hXeq : X.index = cfg.stack.dropLast.length := by rw [hmem]
        rw [hXeq, List.length_dropLast] at hXlt
        exact absurd hXlt (lt_irrefl _)

-- A frame strictly before the last one has a different regionId from the last frame's own
-- (S1: regionId is injective across the stack).
theorem varAsgn_regionId_ne {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {f : FrameWithIndex} (hf : f ∈ cfg.stackWithIndex) (hflt : f.index < cfg.stack.length - 1)
    {lastFrame : Frame} (hlast : cfg.stack.getLast? = some lastFrame) :
    f.regionId ≠ lastFrame.regionId := by
  intro heq
  have hlastMem := stackWithIndex_getLast_mem hlast
  have hidxEq : f.index = ({ lastFrame with index := cfg.stack.length - 1 } : FrameWithIndex).index :=
    merge_corollary_regionId_unique_index vcfg.s1 hf hlastMem heq
  dsimp only at hidxEq
  rw [hidxEq] at hflt
  exact absurd hflt (lt_irrefl _)

-- `FrameReachable` agrees between `cfg`/`cfg'`, both directions, for any frame with index
-- strictly below the last one. Combines `varAsgn_step_eq` (unconditional) with
-- `varAsgn_frame_mem_iff` (stack-membership) and `varAsgn_regionId_ne` (heap-lookup transport for
-- the bridge-var branch's mutated region, `S1`-based since -- unlike `makeObjRegion`/`makeRegion`
-- -- the bridge-var branch's heap key is neither fresh nor otherwise distinguishable a priori).
theorem varAsgn_frame_reachable_iff {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : varAsgn xf y cfg = some cfg')
    {X : FrameWithIndex} (hXmem : X ∈ cfg.stackWithIndex) (hXlt : X.index < cfg.stack.length - 1)
    (ref : Reference) : FrameReachable cfg X.index ref ↔ FrameReachable cfg' X.index ref := by
  obtain ⟨lastFrame, hlast, hcase⟩ := varAsgn_cases h
  rw [FrameReachable_iff_reflTransGen, FrameReachable_iff_reflTransGen, varAsgn_step_eq vcfg h]
  have hXmem' : X ∈ cfg'.stackWithIndex := (varAsgn_frame_mem_iff h hXlt).mp hXmem
  constructor
  · rintro ⟨start, hroot, hrtg⟩
    refine ⟨start, ?_, hrtg⟩
    rcases hroot with ⟨Xf, hXfmem, hXfidx, var, hvar⟩ | ⟨Xf, hXfmem, hXfidx, regionX, hlookup, hbridge⟩
    · have hXfmem' : Xf ∈ cfg'.stackWithIndex := (varAsgn_frame_mem_iff h (hXfidx ▸ hXlt)).mp hXfmem
      exact Or.inl ⟨Xf, hXfmem', hXfidx, var, hvar⟩
    · rcases hcase with ⟨oid, rid, region, hyf, hxb, hloc, hridEq, hregion, hcfg'⟩ | ⟨oid, hyf, hxb, hresolve, hcfg'⟩
      · have hXfne : Xf.regionId ≠ rid := hridEq ▸ varAsgn_regionId_ne vcfg hXfmem (hXfidx ▸ hXlt) hlast
        have hlookup' : cfg'.heap.lookup Xf.regionId = some regionX := by
          rw [hcfg']; dsimp only; rw [AList.lookup_insert_ne hXfne]; exact hlookup
        have hXfmem' : Xf ∈ cfg'.stackWithIndex := (varAsgn_frame_mem_iff h (hXfidx ▸ hXlt)).mp hXfmem
        exact Or.inr ⟨Xf, hXfmem', hXfidx, regionX, hlookup', hbridge⟩
      · have hlookup' : cfg'.heap.lookup Xf.regionId = some regionX := by rw [hcfg']; exact hlookup
        have hXfmem' : Xf ∈ cfg'.stackWithIndex := (varAsgn_frame_mem_iff h (hXfidx ▸ hXlt)).mp hXfmem
        exact Or.inr ⟨Xf, hXfmem', hXfidx, regionX, hlookup', hbridge⟩
  · rintro ⟨start, hroot, hrtg⟩
    refine ⟨start, ?_, hrtg⟩
    rcases hroot with ⟨Xf, hXfmem, hXfidx, var, hvar⟩ | ⟨Xf, hXfmem, hXfidx, regionX, hlookup, hbridge⟩
    · have hXfmem2 : Xf ∈ cfg.stackWithIndex := (varAsgn_frame_mem_iff h (hXfidx ▸ hXlt)).mpr hXfmem
      exact Or.inl ⟨Xf, hXfmem2, hXfidx, var, hvar⟩
    · have hXfmem2 : Xf ∈ cfg.stackWithIndex := (varAsgn_frame_mem_iff h (hXfidx ▸ hXlt)).mpr hXfmem
      rcases hcase with ⟨oid, rid, region, hyf, hxb, hloc, hridEq, hregion, hcfg'⟩ | ⟨oid, hyf, hxb, hresolve, hcfg'⟩
      · have hXfne : Xf.regionId ≠ rid := hridEq ▸ varAsgn_regionId_ne vcfg hXfmem2 (hXfidx ▸ hXlt) hlast
        have hlookup' : cfg.heap.lookup Xf.regionId = some regionX := by
          rw [hcfg'] at hlookup; dsimp only at hlookup
          rw [AList.lookup_insert_ne hXfne] at hlookup; exact hlookup
        exact Or.inr ⟨Xf, hXfmem2, hXfidx, regionX, hlookup', hbridge⟩
      · have hlookup' : cfg.heap.lookup Xf.regionId = some regionX := by rw [hcfg'] at hlookup; exact hlookup
        exact Or.inr ⟨Xf, hXfmem2, hXfidx, regionX, hlookup', hbridge⟩

-- The freshly-updated last frame (fresh-var branch), reindexed as a `FrameWithIndex`, is a member
-- of `cfg'.stackWithIndex` at the same index the original last frame had in `cfg`.
theorem varAsgn_freshvar_last_mem {cfg cfg' : RuntimeConfig} {xf : VarName} {oidY : ObjectId} {lastFrame : Frame}
    (hlast : cfg.stack.getLast? = some lastFrame)
    (hcfg' : cfg' = { cfg with stack := cfg.stack.dropLast ++
      [{ lastFrame with varMap := lastFrame.varMap.insert xf (Reference.OId oidY) }] }) :
    ({ lastFrame with varMap := lastFrame.varMap.insert xf (Reference.OId oidY), index := cfg.stack.length - 1 } : FrameWithIndex) ∈ cfg'.stackWithIndex := by
  have hstack' : cfg'.stack = cfg.stack.dropLast ++
      [{ lastFrame with varMap := lastFrame.varMap.insert xf (Reference.OId oidY) }] := by rw [hcfg']
  have hlen : cfg'.stack.length = cfg.stack.length := by
    rw [hstack']
    conv_rhs => rw [(List.dropLast_append_getLast? lastFrame hlast).symm]
    simp
  have hlast' : cfg'.stack.getLast? =
      some ({ lastFrame with varMap := lastFrame.varMap.insert xf (Reference.OId oidY) } : Frame) := by
    rw [hstack']; simp
  have hmem := stackWithIndex_getLast_mem hlast'
  rwa [hlen] at hmem

-- ===== fieldAsgn =====

-- FIELD-ASGN-STACK's mutated container always lives on the stack, at index `fidC`. Anything
-- `FrameReachable` from it (traced backward) stays confined to the stack, with index only ever
-- increasing (`stack_step_index_le`, chained), all the way back to its own `FrameRoot` -- which
-- (via `S2`, or a direct contradiction in the bridge case, since a bridge value never resolves
-- `Stk`) forces the rooting frame's own index to be `≥ fidC`.
theorem fieldAsgn_stack_container_confined {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {fidC : Index} {oidC : ObjectId} (hlocC : (Reference.OId oidC).loc? cfg = some (Location.Stk fidC))
    {fid : Index} (hreach : FrameReachable cfg fid (Reference.OId oidC)) :
    fidC ≤ fid := by
  rw [FrameReachable_iff_reflTransGen] at hreach
  obtain ⟨start, hroot, hrtg⟩ := hreach
  have hback : ∀ ref, Relation.ReflTransGen (ReachableStep cfg) start ref →
      ∀ oidR fidR, ref = Reference.OId oidR → (Reference.OId oidR).loc? cfg = some (Location.Stk fidR) →
        ∃ oidS fidS, start = Reference.OId oidS ∧ (Reference.OId oidS).loc? cfg = some (Location.Stk fidS) ∧
          fidR ≤ fidS := by
    intro ref hrtg2
    induction hrtg2 with
    | refl => intro oidR fidR heq hloc; exact ⟨oidR, fidR, heq, heq ▸ hloc, le_refl _⟩
    | tail hprev hstep ih =>
      intro oidR fidR heq hloc
      subst heq
      obtain ⟨oidB, fidB, hbeq, hlocB⟩ := predecessor_of_stack_object vcfg hloc hstep
      obtain ⟨oidS, fidS, hseq, hlocS, hle⟩ := ih oidB fidB hbeq hlocB
      have hstepBound := stack_step_index_le vcfg hlocB (hbeq ▸ hstep) hloc
      exact ⟨oidS, fidS, hseq, hlocS, le_trans hstepBound hle⟩
  obtain ⟨oidS, fidS, hseq, hlocS, hle⟩ := hback (Reference.OId oidC) hrtg oidC fidC rfl hlocC
  rcases hroot with
      ⟨frameR, hframeRmem, hframeRidx, var, hvar⟩ |
      ⟨frameR, hframeRmem, hframeRidx, regionR, hlookupR, hbridge⟩
  · rw [hseq] at hvar
    have hmemrefs : (Reference.OId oidS) ∈ frameR.refs := mem_frame_refs_of_mem_varMap hvar
    have hs2 := vcfg.s2 frameR hframeRmem (Reference.OId oidS) hmemrefs fidS oidS rfl hlocS
    rw [hframeRidx] at hs2
    exact le_trans hle hs2
  · exfalso
    rw [hseq] at hbridge
    injection hbridge with hbeq2
    have hbridgeIn : regionR.bridgeObjectId ∈ regionR.objMap := by
      apply vcfg.h1
      unfold Heap.regions
      exact List.mem_map_of_mem (AList.lookup_mem_entries hlookupR)
    have hlocBridge := (oid_loc_rgn_iff_in_heap vcfg).mpr ⟨regionR, hlookupR, hbridgeIn⟩
    rw [← hbeq2] at hlocBridge
    rw [hlocS] at hlocBridge
    simp at hlocBridge

-- S3 restated at the `ReachableStep` level (mirrors `stack_step_index_le`'s S2-flavored version):
-- a stack-to-region hop's *target* region is owned by a frame with index no greater than the
-- stack source's own.
theorem stack_step_region_index_le {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {oid : ObjectId} {fidCur : Index} {oid' : ObjectId} {rid' : RegionId}
    (hloc : (Reference.OId oid).loc? cfg = some (Location.Stk fidCur))
    (hstep : ReachableStep cfg (Reference.OId oid) (Reference.OId oid'))
    (hloc' : (Reference.OId oid').loc? cfg = some (Location.Rgn rid')) :
    ∃ frame' ∈ cfg.stackWithIndex, frame'.regionId = rid' ∧ frame'.index ≤ fidCur := by
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
    obtain ⟨frame', hmem', hridEq', hidx'⟩ := vcfg.s3 someFrame hmem (Reference.OId oid') hmemrefs rid' oid' rfl hloc'
    rw [hidxEq] at hidx'
    exact ⟨frame', hmem', hridEq', hidx'⟩

-- FIELD-ASGN-REGION's mutated container always lives inside the active frame's own region `rid`
-- (always Open, since it's on-stack, L2). Anything `FrameReachable` from it (traced backward)
-- either stays confined to the region the *whole* way back to its own `FrameRoot` (H3,
-- `predecessor_of_region_object`'s region case; `S1`/`S3` then bound the rooting frame's index),
-- or "escapes" onto the stack at some intermediate point (`predecessor_of_region_object`'s stack
-- case; `S1`/`S3` bound *that* point directly, then `fieldAsgn_stack_container_confined` finishes
-- the job by bounding the rooting frame's index against that intermediate stack point instead).
theorem fieldAsgn_region_container_confined {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid : RegionId} {region : Region} (hlookup : cfg.heap.lookup rid = some region) (hopen : region.status = Status.Open)
    {ownerFrame : FrameWithIndex} (hownerMem : ownerFrame ∈ cfg.stackWithIndex) (hownerRid : ownerFrame.regionId = rid)
    {oidC : ObjectId} (hlocC : (Reference.OId oidC).loc? cfg = some (Location.Rgn rid))
    {fid : Index} (hreach : FrameReachable cfg fid (Reference.OId oidC)) :
    ownerFrame.index ≤ fid := by
  rw [FrameReachable_iff_reflTransGen] at hreach
  obtain ⟨start, hroot, hrtg⟩ := hreach
  have hback : ∀ ref, Relation.ReflTransGen (ReachableStep cfg) start ref →
      ∀ oidR, ref = Reference.OId oidR → (Reference.OId oidR).loc? cfg = some (Location.Rgn rid) →
        (∃ oidS, start = Reference.OId oidS ∧ (Reference.OId oidS).loc? cfg = some (Location.Rgn rid)) ∨
        (∃ oidB fidB, Relation.ReflTransGen (ReachableStep cfg) start (Reference.OId oidB) ∧
          (Reference.OId oidB).loc? cfg = some (Location.Stk fidB) ∧ ownerFrame.index ≤ fidB) := by
    intro ref hrtg2
    induction hrtg2 with
    | refl => intro oidR heq hloc; left; exact ⟨oidR, heq, heq ▸ hloc⟩
    | tail hprev hstep ih =>
      intro oidR heq hloc
      subst heq
      obtain ⟨oidB, hbeq, hcaseB⟩ := predecessor_of_region_object vcfg hlookup hopen hloc hstep
      rcases hcaseB with hlocB | ⟨fidB, hlocB⟩
      · exact ih oidB hbeq hlocB
      · right
        refine ⟨oidB, fidB, hbeq ▸ hprev, hlocB, ?_⟩
        obtain ⟨frame', hmem', hridEq', hidx'⟩ :=
          stack_step_region_index_le vcfg hlocB (hbeq ▸ hstep) hloc
        have hidxEq : frame'.index = ownerFrame.index :=
          merge_corollary_regionId_unique_index vcfg.s1 hmem' hownerMem (hridEq'.trans hownerRid.symm)
        rw [← hidxEq]
        exact hidx'
  obtain ⟨oidS, hseq, hlocS⟩ | ⟨oidB, fidB, hprefixB, hlocB, hleB⟩ := hback (Reference.OId oidC) hrtg oidC rfl hlocC
  · rcases hroot with
        ⟨frameR, hframeRmem, hframeRidx, var, hvar⟩ |
        ⟨frameR, hframeRmem, hframeRidx, regionR, hlookupR, hbridge⟩
    · rw [hseq] at hvar
      have hmemrefs : (Reference.OId oidS) ∈ frameR.refs := mem_frame_refs_of_mem_varMap hvar
      obtain ⟨frame', hmem', hridEq', hidx'⟩ := vcfg.s3 frameR hframeRmem (Reference.OId oidS) hmemrefs rid oidS rfl hlocS
      have hidxEq : frame'.index = ownerFrame.index :=
        merge_corollary_regionId_unique_index vcfg.s1 hmem' hownerMem (hridEq'.trans hownerRid.symm)
      rw [hframeRidx] at hidx'
      rw [← hidxEq]
      exact hidx'
    · rw [hseq] at hbridge
      injection hbridge with hbeq2
      have hlocBridge : (Reference.OId regionR.bridgeObjectId).loc? cfg = some (Location.Rgn frameR.regionId) := by
        obtain ⟨regionR2, hlookupR2, hopenR2⟩ := l2_of_stackWithIndex vcfg hframeRmem
        rw [hlookupR2] at hlookupR
        injection hlookupR with hlookupR
        subst hlookupR
        have hbridgeIn : regionR2.bridgeObjectId ∈ regionR2.objMap := vcfg.h1 regionR2
          (by unfold Heap.regions; exact List.mem_map_of_mem (AList.lookup_mem_entries hlookupR2))
        exact (oid_loc_rgn_iff_in_heap vcfg).mpr ⟨regionR2, hlookupR2, hbridgeIn⟩
      rw [← hbeq2] at hlocBridge
      rw [hlocS] at hlocBridge
      injection hlocBridge with hlocBridge
      injection hlocBridge with hlocBridge
      have hidxEq : frameR.index = ownerFrame.index :=
        merge_corollary_regionId_unique_index vcfg.s1 hframeRmem hownerMem (hlocBridge.symm.trans hownerRid.symm)
      rw [hframeRidx] at hidxEq
      exact le_of_eq hidxEq.symm
  · have hreachB : FrameReachable cfg fid (Reference.OId oidB) :=
      (FrameReachable_iff_reflTransGen cfg fid (Reference.OId oidB)).mpr ⟨start, hroot, hprefixB⟩
    have hbound := fieldAsgn_stack_container_confined vcfg hlocB hreachB
    exact le_trans hleB hbound

-- `objAt?` agrees between `cfg`/`cfg'` for any oid' other than the mutated container's own
-- (FIELD-ASGN-STACK branch): the stack side reduces to the mutated frame's own `objMap.lookup`
-- for the position it lives at, unconditionally equal for `oid' ≠ oid` (`AList.lookup_insert_ne`);
-- the heap side is untouched entirely.
theorem fieldAsgn_stack_objAt_eq_of_ne {cfg cfg' : RuntimeConfig} {frame : FrameWithIndex} {oid : ObjectId}
    {obj : Object} {field : FieldName} {yRef : Reference}
    (hframe : cfg.stackWithIndex.getLast? = some frame) (hobj : frame.objMap.lookup oid = some obj)
    (hcfg' : cfg' = { cfg with stack := cfg.stack.dropLast ++
      [({ frame with objMap := frame.objMap.insert oid (obj.insert field yRef) } : Frame)] })
    {oid' : ObjectId} (hne : oid' ≠ oid) :
    (Reference.OId oid').objAt? cfg = (Reference.OId oid').objAt? cfg' := by
  have hlocEq : (Reference.OId oid').loc? cfg = (Reference.OId oid').loc? cfg' := by
    rw [hcfg']; exact fieldAsgn_corollary_stack_loc_eq hframe hobj oid'
  obtain ⟨stack_eq, hframeidx⟩ := fieldAsgn_corollary_stack_eq hframe
  unfold Reference.objAt?
  dsimp only
  rw [hlocEq]
  cases hloc' : (Reference.OId oid').loc? cfg' with
  | none => rfl
  | some loc =>
    cases loc with
    | Rgn ridX =>
      dsimp only
      have hheapEq : cfg'.heap = cfg.heap := by rw [hcfg']
      rw [hheapEq]
    | Stk fidX =>
      dsimp only
      rw [stackWithIndex_find_index_eq_getElem, stackWithIndex_find_index_eq_getElem]
      have hgetCfg : cfg.stackWithIndex[fidX]? =
          (cfg.stack[fidX]?).map (fun f => ({ toFrame := f, index := fidX } : FrameWithIndex)) := by
        unfold RuntimeConfig.stackWithIndex; rw [List.getElem?_mapIdx]
      have hgetCfg' : cfg'.stackWithIndex[fidX]? =
          (cfg'.stack[fidX]?).map (fun f => ({ toFrame := f, index := fidX } : FrameWithIndex)) := by
        unfold RuntimeConfig.stackWithIndex; rw [List.getElem?_mapIdx]
      rw [hgetCfg, hgetCfg']
      have hstack' : cfg'.stack = cfg.stack.dropLast ++
          [({ frame with objMap := frame.objMap.insert oid (obj.insert field yRef) } : Frame)] := by rw [hcfg']
      have hfidxlt : fidX < cfg'.stack.length := loc_stk_lt hloc'
      have hlen' : cfg'.stack.length = cfg.stack.dropLast.length + 1 := by rw [hstack']; simp
      rw [hlen'] at hfidxlt
      by_cases hfx : fidX = cfg.stack.dropLast.length
      · have h1 : cfg.stack[fidX]? = some frame.toFrame := by
          conv_lhs => rw [stack_eq, hfx]
          simp
        have h2 : cfg'.stack[fidX]? =
            some ({ frame with objMap := frame.objMap.insert oid (obj.insert field yRef) } : Frame) := by
          rw [hstack', hfx]
          simp
        rw [h1, h2]
        simp only [Option.map_some]
        dsimp only [Option.bind]
        rw [AList.lookup_insert_ne hne]
      · have hlt : fidX < cfg.stack.dropLast.length := lt_of_le_of_ne (Nat.lt_succ_iff.mp hfidxlt) hfx
        have h1 : cfg.stack[fidX]? = cfg.stack.dropLast[fidX]? := by
          conv_lhs => rw [stack_eq]
          rw [List.getElem?_append_left hlt]
        have h2 : cfg'.stack[fidX]? = cfg.stack.dropLast[fidX]? := by
          rw [hstack', List.getElem?_append_left hlt]
        rw [h1, h2]

-- `objAt?` agrees between `cfg`/`cfg'` for any oid' other than the mutated container's own
-- (FIELD-ASGN-REGION branch): mirrors the stack version, but at the heap level.
theorem fieldAsgn_region_objAt_eq_of_ne {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid oid : ObjectId} {region : Region} {obj : Object} {field : FieldName} {yRef : Reference}
    (hregion : cfg.heap.lookup rid = some region) (hobj : region.objMap.lookup oid = some obj)
    (hcfg' : cfg' = { cfg with heap := cfg.heap.insert rid ({ region with objMap := region.objMap.insert oid (obj.insert field yRef) } : Region) }) :
    ∀ {oid' : ObjectId}, oid' ≠ oid →
    (Reference.OId oid').objAt? cfg = (Reference.OId oid').objAt? cfg' := by
  intro oid' hne
  have hlocEq : (Reference.OId oid').loc? cfg = (Reference.OId oid').loc? cfg' := by
    rw [hcfg']; exact fieldAsgn_corollary_region_loc_eq vcfg hregion hobj oid'
  unfold Reference.objAt?
  dsimp only
  rw [hlocEq]
  cases hloc' : (Reference.OId oid').loc? cfg' with
  | none => rfl
  | some loc =>
    cases loc with
    | Rgn ridX =>
      dsimp only
      by_cases hridx : ridX = rid
      · subst hridx
        have hlookup' : cfg'.heap.lookup ridX = some
            ({ region with objMap := region.objMap.insert oid (obj.insert field yRef) } : Region) := by
          rw [hcfg']; dsimp only; rw [AList.lookup_insert]
        rw [hlookup', hregion]
        dsimp only [Option.bind]
        rw [AList.lookup_insert_ne hne]
      · have hlookup' : cfg'.heap.lookup ridX = cfg.heap.lookup ridX := by
          rw [hcfg']; dsimp only; rw [AList.lookup_insert_ne hridx]
        rw [hlookup']
    | Stk fidX =>
      dsimp only
      rw [stackWithIndex_find_index_eq_getElem, stackWithIndex_find_index_eq_getElem]
      have hstackEq : cfg'.stack = cfg.stack := by rw [hcfg']
      unfold RuntimeConfig.stackWithIndex
      rw [hstackEq]

-- `ReachableStep` agrees between `cfg`/`cfg'` for any source *other than* the mutated container's
-- own `OId`: unconditional in the target, for either branch (`fieldAsgn_stack_objAt_eq_of_ne`/
-- `_region_objAt_eq_of_ne` for `OId`-sourced steps; `open_rid_no_step`/untouched-heap for
-- `RId`-sourced ones). Returns the container's own id existentially, since the caller needs it
-- anyway to state "not the container".
theorem fieldAsgn_step_iff_of_ne {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : fieldAsgn xf y cfg = some cfg') :
    ∃ oidC : ObjectId, resolveV xf.root cfg = some (Reference.OId oidC) ∧
      ∀ a : Reference, a ≠ Reference.OId oidC → ∀ b : Reference,
      ReachableStep cfg a b ↔ ReachableStep cfg' a b := by
  obtain ⟨frame, hframe, hcase⟩ := fieldAsgn_cases h
  rcases hcase with
      ⟨oid, oid_y, obj, hxr, hyr, hloc, hobj, hcfg'⟩ |
      ⟨oid, oid_y, rid, region, obj, hxr, hyr, hloc, hregion, hobj, hyloc, hstatus, hfrid, hcfg'⟩
  · refine ⟨oid, hxr, fun a hane b => ?_⟩
    cases a with
    | OId oid' =>
      have hne : oid' ≠ oid := fun heq => hane (heq ▸ rfl)
      rw [ReachableStep_oid_iff, ReachableStep_oid_iff, fieldAsgn_stack_objAt_eq_of_ne hframe hobj hcfg' hne]
    | RId rid' =>
      have hheapEq : cfg'.heap = cfg.heap := by rw [hcfg']
      rw [ReachableStep_rid_iff, ReachableStep_rid_iff, hheapEq]
  · refine ⟨oid, hxr, fun a hane b => ?_⟩
    cases a with
    | OId oid' =>
      have hne : oid' ≠ oid := fun heq => hane (heq ▸ rfl)
      rw [ReachableStep_oid_iff, ReachableStep_oid_iff, fieldAsgn_region_objAt_eq_of_ne vcfg hregion hobj hcfg' hne]
    | RId rid' =>
      by_cases hridEq : rid' = rid
      · subst hridEq
        have hlookup' : cfg'.heap.lookup rid' = some
            ({ region with objMap := region.objMap.insert oid (obj.insert xf.field (Reference.OId oid_y)) } : Region) := by
          rw [hcfg']; dsimp only; rw [AList.lookup_insert]
        constructor
        · intro hstep; exact absurd hstep (open_rid_no_step hregion hstatus)
        · intro hstep; exact absurd hstep (open_rid_no_step hlookup' hstatus)
      · have hlookup' : cfg'.heap.lookup rid' = cfg.heap.lookup rid' := by
          rw [hcfg']; dsimp only; rw [AList.lookup_insert_ne hridEq]
        rw [ReachableStep_rid_iff, ReachableStep_rid_iff, hlookup']

-- `stackWithIndex_objMap_get_eq_of_last_varMap_update`'s mirror image: if `cfg'` is `cfg` with its
-- **last** frame's `objMap` replaced (everything else -- `regionId`/`bridgeVar`/`varMap` --
-- untouched, and every other frame untouched), then `(varMap, bridgeVar, regionId)` is unaffected
-- at every stack position.
theorem fieldAsgn_stack_shape_eq {cfg cfg' : RuntimeConfig} {frame : Frame}
    {newObjMap : ObjMap} (hframeLast : cfg.stack.getLast? = some frame)
    (hstack' : cfg'.stack = cfg.stack.dropLast ++
      [({ regionId := frame.regionId, bridgeVar := frame.bridgeVar, objMap := newObjMap,
          varMap := frame.varMap } : Frame)]) (n : ℕ) :
    (cfg.stack[n]?).map (fun f : Frame => (f.varMap, f.bridgeVar, f.regionId)) =
    (cfg'.stack[n]?).map (fun f : Frame => (f.varMap, f.bridgeVar, f.regionId)) := by
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
    (List.dropLast_append_getLast? frame hframeLast).symm
  set newFrame : Frame :=
    { regionId := frame.regionId, bridgeVar := frame.bridgeVar, objMap := newObjMap,
      varMap := frame.varMap } with newFrame_def
  by_cases hlp : n = cfg.stack.dropLast.length
  · have e1 : cfg.stack[n]? = some frame := by
      conv_lhs => rw [stack_eq, hlp]
      simp
    have e2 : cfg'.stack[n]? = some newFrame := by
      rw [hstack']; rw [hlp]
      simp
    rw [e1, e2]
    rfl
  · by_cases hlt : n < cfg.stack.dropLast.length
    · have e1 : cfg.stack[n]? = cfg.stack.dropLast[n]? := by
        conv_lhs => rw [stack_eq]
        rw [List.getElem?_append_left hlt]
      have e2 : cfg'.stack[n]? = cfg.stack.dropLast[n]? := by
        rw [hstack']; rw [List.getElem?_append_left hlt]
      rw [e1, e2]
    · have hlen : cfg.stack.length = cfg.stack.dropLast.length + 1 := by rw [stack_eq]; simp
      have hlen' : cfg'.stack.length = cfg.stack.dropLast.length + 1 := by rw [hstack']; simp
      have e1 : cfg.stack[n]? = none := List.getElem?_eq_none (by omega)
      have e2 : cfg'.stack[n]? = none := List.getElem?_eq_none (by omega)
      rw [e1, e2]

-- `FrameRoot` agrees between `cfg`/`cfg'` unconditionally, for every `fid`/`start`: neither branch
-- ever touches `varMap`/`bridgeVar`/`bridgeObjectId` (FIELD-ASGN-STACK only changes the active
-- frame's own `objMap`; FIELD-ASGN-REGION only changes the active region's own `objMap`) -- the
-- one wrinkle is the active frame's own stack *membership* (as an exact record, `objMap` included)
-- for the stack branch, handled via the generic shape-transport machinery
-- (`stackWithIndex_frame_transport_up/down_of_shape_eq`, Model layer) with `fieldAsgn_stack_shape_eq`.
theorem fieldAsgn_frame_root_iff {cfg cfg' : RuntimeConfig} (h : fieldAsgn xf y cfg = some cfg')
    (fid : Index) (start : Reference) : FrameRoot cfg fid start ↔ FrameRoot cfg' fid start := by
  obtain ⟨frame, hframe, hcase⟩ := fieldAsgn_cases h
  rcases hcase with
      ⟨oid, oid_y, obj, hxr, hyr, hloc, hobj, hcfg'⟩ |
      ⟨oid, oid_y, rid, region, obj, hxr, hyr, hloc, hregion, hobj, hyloc, hstatus, hfrid, hcfg'⟩
  · obtain ⟨stack_eq, hframeidx⟩ := fieldAsgn_corollary_stack_eq hframe
    have hframeLast : cfg.stack.getLast? = some frame.toFrame := by
      rw [stack_eq]; simp
    have hstack' : cfg'.stack = cfg.stack.dropLast ++
        [({ regionId := frame.regionId, bridgeVar := frame.bridgeVar,
            objMap := frame.objMap.insert oid (obj.insert xf.field (Reference.OId oid_y)),
            varMap := frame.varMap } : Frame)] := by rw [hcfg']
    have hshape := fieldAsgn_stack_shape_eq hframeLast hstack'
    have hheapEq : cfg'.heap = cfg.heap := by rw [hcfg']
    constructor
    · rintro (⟨frameV, hVmem, hVidx, var, hvar⟩ | ⟨frameV, hVmem, hVidx, regionV, hVlookup, hVbridge⟩)
      · obtain ⟨frameV0, hVmem0, hVidx0, hproj0⟩ := stackWithIndex_frame_transport_up_of_shape_eq hshape frameV hVmem
        refine Or.inl ⟨frameV0, hVmem0, hVidx0.trans hVidx, var, ?_⟩
        rw [show frameV0.varMap = frameV.varMap from congrArg (·.1) hproj0]
        exact hvar
      · obtain ⟨frameV0, hVmem0, hVidx0, hproj0⟩ := stackWithIndex_frame_transport_up_of_shape_eq hshape frameV hVmem
        refine Or.inr ⟨frameV0, hVmem0, hVidx0.trans hVidx, regionV, ?_, hVbridge⟩
        rw [show frameV0.regionId = frameV.regionId from congrArg (·.2.2) hproj0, hheapEq]
        exact hVlookup
    · rintro (⟨frameV, hVmem, hVidx, var, hvar⟩ | ⟨frameV, hVmem, hVidx, regionV, hVlookup, hVbridge⟩)
      · obtain ⟨frameV0, hVmem0, hVidx0, hproj0⟩ := stackWithIndex_frame_transport_down_of_shape_eq hshape frameV hVmem
        refine Or.inl ⟨frameV0, hVmem0, hVidx0.trans hVidx, var, ?_⟩
        rw [show frameV0.varMap = frameV.varMap from congrArg (·.1) hproj0]
        exact hvar
      · obtain ⟨frameV0, hVmem0, hVidx0, hproj0⟩ := stackWithIndex_frame_transport_down_of_shape_eq hshape frameV hVmem
        refine Or.inr ⟨frameV0, hVmem0, hVidx0.trans hVidx, regionV, ?_, hVbridge⟩
        rw [show frameV0.regionId = frameV.regionId from congrArg (·.2.2) hproj0, ← hheapEq]
        exact hVlookup
  · have hstackEq : cfg'.stack = cfg.stack := by rw [hcfg']
    have hstackWithIndexEq : cfg'.stackWithIndex = cfg.stackWithIndex := by
      unfold RuntimeConfig.stackWithIndex; rw [hstackEq]
    constructor
    · rintro (⟨frameV, hVmem, hVidx, var, hvar⟩ | ⟨frameV, hVmem, hVidx, regionV, hVlookup, hVbridge⟩)
      · exact Or.inl ⟨frameV, hstackWithIndexEq ▸ hVmem, hVidx, var, hvar⟩
      · by_cases hrideq : frameV.regionId = rid
        · have hlookup' : cfg'.heap.lookup frameV.regionId =
              some ({ region with objMap := region.objMap.insert oid (obj.insert xf.field (Reference.OId oid_y)) } : Region) := by
            rw [hrideq, hcfg']; dsimp only; rw [AList.lookup_insert]
          rw [hrideq] at hVlookup
          have hbeq : regionV = region := by
            have hcomb := hVlookup.symm.trans hregion
            injection hcomb
          rw [hbeq] at hVbridge
          exact Or.inr ⟨frameV, hstackWithIndexEq ▸ hVmem, hVidx, _, hlookup', hVbridge⟩
        · have hlookup' : cfg'.heap.lookup frameV.regionId = cfg.heap.lookup frameV.regionId := by
            rw [hcfg']; dsimp only; rw [AList.lookup_insert_ne hrideq]
          exact Or.inr ⟨frameV, hstackWithIndexEq ▸ hVmem, hVidx, regionV, hlookup'.trans hVlookup, hVbridge⟩
    · rintro (⟨frameV, hVmem, hVidx, var, hvar⟩ | ⟨frameV, hVmem, hVidx, regionV, hVlookup, hVbridge⟩)
      · exact Or.inl ⟨frameV, hstackWithIndexEq ▸ hVmem, hVidx, var, hvar⟩
      · by_cases hrideq : frameV.regionId = rid
        · have hlookupcfg' : cfg'.heap.lookup frameV.regionId =
              some ({ region with objMap := region.objMap.insert oid (obj.insert xf.field (Reference.OId oid_y)) } : Region) := by
            rw [hrideq, hcfg']; dsimp only; rw [AList.lookup_insert]
          rw [hlookupcfg'] at hVlookup
          injection hVlookup with hVlookupEq
          rw [← hVlookupEq] at hVbridge
          dsimp only at hVbridge
          exact Or.inr ⟨frameV, hstackWithIndexEq ▸ hVmem, hVidx, region, by rw [hrideq]; exact hregion, hVbridge⟩
        · have hlookup' : cfg'.heap.lookup frameV.regionId = cfg.heap.lookup frameV.regionId := by
            rw [hcfg']; dsimp only; rw [AList.lookup_insert_ne hrideq]
          exact Or.inr ⟨frameV, hstackWithIndexEq ▸ hVmem, hVidx, regionV, hlookup'.symm.trans hVlookup, hVbridge⟩

-- If a `FrameReachable cfg G ref` chain can never touch the mutated container `oidC` (at any
-- point along it -- guaranteed whenever `G` is confined below `oidC`'s own owner-index, via
-- `fieldAsgn_stack_container_confined`/`_region_container_confined`), it transports unconditionally
-- to `cfg'`: the root transports via `hframeRootIff` (unconditional), and every hop transports via
-- `hstepIffOfNe`, since the hop's own source is -- by the very fact it's `FrameReachable cfg G _`
-- -- itself confined away from `oidC`.
theorem fieldAsgn_confined_transport {cfg cfg' : RuntimeConfig}
    {oidC : ObjectId} (hstepIffOfNe : ∀ a : Reference, a ≠ Reference.OId oidC → ∀ b : Reference,
      ReachableStep cfg a b ↔ ReachableStep cfg' a b)
    (hframeRootIff : ∀ fid start, FrameRoot cfg fid start ↔ FrameRoot cfg' fid start)
    {G : Index} (hconfined : ∀ refX, FrameReachable cfg G refX → refX ≠ Reference.OId oidC)
    {ref : Reference} (hreach : FrameReachable cfg G ref) :
    FrameReachable cfg' G ref := by
  rw [FrameReachable_iff_reflTransGen] at hreach
  obtain ⟨start, hroot, hrtg⟩ := hreach
  rw [FrameReachable_iff_reflTransGen]
  refine ⟨start, (hframeRootIff G start).mp hroot, ?_⟩
  induction hrtg with
  | refl => exact Relation.ReflTransGen.refl
  | tail hprev hstep ih =>
    rename_i p c
    have hpReach : FrameReachable cfg G p :=
      (FrameReachable_iff_reflTransGen cfg G p).mpr ⟨start, hroot, hprev⟩
    have hpne : p ≠ Reference.OId oidC := hconfined p hpReach
    exact ih.tail ((hstepIffOfNe p hpne c).mp hstep)

-- `X.index < activeFrame.index` membership in `cfg.stackWithIndex` agrees with membership in
-- `cfg'.stackWithIndex`, in both directions. FIELD-ASGN-REGION never touches the stack at all, so
-- this holds unconditionally there; FIELD-ASGN-STACK only mutates the *active* frame's own
-- `objMap`, leaving every other frame's record untouched.
theorem fieldAsgn_frame_mem_iff {cfg cfg' : RuntimeConfig} (h : fieldAsgn xf y cfg = some cfg')
    {X : FrameWithIndex} {activeIdx : Index} (hXlt : X.index < activeIdx)
    (hactiveidx : activeIdx = cfg.stack.dropLast.length) :
    X ∈ cfg.stackWithIndex ↔ X ∈ cfg'.stackWithIndex := by
  obtain ⟨frame, hframe, hcase⟩ := fieldAsgn_cases h
  rcases hcase with
      ⟨oid, oid_y, obj, hxr, hyr, hloc, hobj, hcfg'⟩ |
      ⟨oid, oid_y, rid, region, obj, hxr, hyr, hloc, hregion, hobj, hyloc, hstatus, hfrid, hcfg'⟩
  · have hstack' : cfg'.stack = cfg.stack.dropLast ++
        [({ frame with objMap := frame.objMap.insert oid (obj.insert xf.field (Reference.OId oid_y)) } : Frame)] := by
      rw [hcfg']
    constructor
    · intro hXmem
      unfold RuntimeConfig.stackWithIndex
      rw [hstack']
      obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hXmem
      have hidx : X.index = n := by rw [← hfeq]
      have hnlt : n < cfg.stack.dropLast.length := by rw [← hidx, ← hactiveidx]; exact hXlt
      apply List.mem_mapIdx.mpr
      refine ⟨n, ?_, ?_⟩
      · rw [List.length_append]; omega
      · rw [List.getElem_append_left hnlt, List.getElem_dropLast hnlt]; exact hfeq
    · intro hXmem
      unfold RuntimeConfig.stackWithIndex at hXmem
      rw [hstack'] at hXmem
      rw [List.mapIdx_concat] at hXmem
      rcases List.mem_append.mp hXmem with hmem | hmem
      · obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hmem
        have hnlt : n < cfg.stack.length := lt_of_lt_of_le hn (List.length_dropLast .. ▸ Nat.sub_le _ _)
        unfold RuntimeConfig.stackWithIndex
        apply List.mem_mapIdx.mpr
        refine ⟨n, hnlt, ?_⟩
        rw [← List.getElem_dropLast hn]
        exact hfeq
      · exfalso
        rw [List.mem_singleton] at hmem
        have hXeq : X.index = cfg.stack.dropLast.length := by rw [hmem]
        rw [hXeq, ← hactiveidx] at hXlt
        exact absurd hXlt (lt_irrefl _)
  · have hstackEq : cfg'.stack = cfg.stack := by rw [hcfg']
    unfold RuntimeConfig.stackWithIndex
    rw [hstackEq]

-- The mutated container's own `ReachableStep`, restricted to `c ≠ OId oid_y` (i.e. not the
-- just-written field's own new value): transports backward unconditionally (FIELD-ASGN-STACK
-- branch), since the new refs are exactly the old refs with `oid_y` possibly added
-- (`fieldAsgn_corollary_object_insert_refs_mem`, Model layer).
theorem fieldAsgn_stack_oidC_step_of_ne_oidY {cfg cfg' : RuntimeConfig} {frame : FrameWithIndex}
    {oid oid_y : ObjectId} {obj : Object} {field : FieldName}
    (hframe : cfg.stackWithIndex.getLast? = some frame)
    (hlocC : (Reference.OId oid).loc? cfg = some (Location.Stk frame.index))
    (hobj : frame.objMap.lookup oid = some obj)
    (hcfg' : cfg' = { cfg with stack := cfg.stack.dropLast ++
      [({ frame with objMap := frame.objMap.insert oid (obj.insert field (Reference.OId oid_y)) } : Frame)] })
    {c : Reference} (hstep : ReachableStep cfg' (Reference.OId oid) c) :
    c = Reference.OId oid_y ∨ ReachableStep cfg (Reference.OId oid) c := by
  have hlocEq : (Reference.OId oid).loc? cfg = (Reference.OId oid).loc? cfg' := by
    rw [hcfg']; exact fieldAsgn_corollary_stack_loc_eq hframe hobj oid
  obtain ⟨stack_eq, hframeidx⟩ := fieldAsgn_corollary_stack_eq hframe
  have hstack' : cfg'.stack = cfg.stack.dropLast ++
      [({ frame with objMap := frame.objMap.insert oid (obj.insert field (Reference.OId oid_y)) } : Frame)] := by
    rw [hcfg']
  have hobjAtC : (Reference.OId oid).objAt? cfg' = some (obj.insert field (Reference.OId oid_y)) := by
    unfold Reference.objAt?
    dsimp only
    rw [← hlocEq, hlocC]
    dsimp only
    rw [stackWithIndex_find_index_eq_getElem]
    have hget : cfg'.stackWithIndex[frame.index]? =
        (cfg'.stack[frame.index]?).map (fun f => ({ toFrame := f, index := frame.index } : FrameWithIndex)) := by
      unfold RuntimeConfig.stackWithIndex; rw [List.getElem?_mapIdx]
    rw [hget]
    have hget2 : cfg'.stack[frame.index]? =
        some ({ frame with objMap := frame.objMap.insert oid (obj.insert field (Reference.OId oid_y)) } : Frame) := by
      rw [hstack', hframeidx]; simp
    rw [hget2]
    simp only [Option.map_some]
    dsimp only [Option.bind]
    rw [AList.lookup_insert]
  have hobjAt : (Reference.OId oid).objAt? cfg = some obj := by
    unfold Reference.objAt?
    dsimp only
    rw [hlocC]
    dsimp only
    rw [stackWithIndex_find_index_eq_getElem]
    have hget : cfg.stackWithIndex[frame.index]? =
        (cfg.stack[frame.index]?).map (fun f => ({ toFrame := f, index := frame.index } : FrameWithIndex)) := by
      unfold RuntimeConfig.stackWithIndex; rw [List.getElem?_mapIdx]
    rw [hget]
    have hget2 : cfg.stack[frame.index]? = some frame.toFrame := by
      conv_lhs => rw [stack_eq, hframeidx]
      simp
    rw [hget2]
    simp only [Option.map_some]
    dsimp only [Option.bind]
    exact hobj
  rw [ReachableStep_oid_iff] at hstep
  obtain ⟨objC, hobjAtC2, hcontainsC⟩ := hstep
  rw [hobjAtC] at hobjAtC2
  injection hobjAtC2 with hobjAtCeq
  rw [← hobjAtCeq] at hcontainsC
  rcases fieldAsgn_corollary_object_insert_refs_mem (List.contains_iff_mem.mp hcontainsC) with heq | hmem
  · left; exact heq
  · right
    rw [ReachableStep_oid_iff]
    exact ⟨obj, hobjAt, List.contains_iff_mem.mpr hmem⟩

-- Mirrors `fieldAsgn_stack_oidC_step_of_ne_oidY` for the FIELD-ASGN-REGION branch.
theorem fieldAsgn_region_oidC_step_of_ne_oidY {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid oid oid_y : ObjectId} {region : Region} {obj : Object} {field : FieldName}
    (hregion : cfg.heap.lookup rid = some region)
    (hlocC : (Reference.OId oid).loc? cfg = some (Location.Rgn rid))
    (hobj : region.objMap.lookup oid = some obj)
    (hcfg' : cfg' = { cfg with heap := cfg.heap.insert rid ({ region with objMap := region.objMap.insert oid (obj.insert field (Reference.OId oid_y)) } : Region) })
    {c : Reference} (hstep : ReachableStep cfg' (Reference.OId oid) c) :
    c = Reference.OId oid_y ∨ ReachableStep cfg (Reference.OId oid) c := by
  have hlocEq : (Reference.OId oid).loc? cfg = (Reference.OId oid).loc? cfg' := by
    rw [hcfg']; exact fieldAsgn_corollary_region_loc_eq vcfg hregion hobj oid
  have hobjAtC : (Reference.OId oid).objAt? cfg' = some (obj.insert field (Reference.OId oid_y)) := by
    unfold Reference.objAt?
    dsimp only
    rw [← hlocEq, hlocC]
    dsimp only
    have hlookup' : cfg'.heap.lookup rid =
        some ({ region with objMap := region.objMap.insert oid (obj.insert field (Reference.OId oid_y)) } : Region) := by
      rw [hcfg']; dsimp only; rw [AList.lookup_insert]
    rw [hlookup']
    dsimp only [Option.bind]
    rw [AList.lookup_insert]
  have hobjAt : (Reference.OId oid).objAt? cfg = some obj := by
    unfold Reference.objAt?
    dsimp only
    rw [hlocC]
    dsimp only
    rw [hregion]
    dsimp only [Option.bind]
    exact hobj
  rw [ReachableStep_oid_iff] at hstep
  obtain ⟨objC, hobjAtC2, hcontainsC⟩ := hstep
  rw [hobjAtC] at hobjAtC2
  injection hobjAtC2 with hobjAtCeq
  rw [← hobjAtCeq] at hcontainsC
  rcases fieldAsgn_corollary_object_insert_refs_mem (List.contains_iff_mem.mp hcontainsC) with heq | hmem
  · left; exact heq
  · right
    rw [ReachableStep_oid_iff]
    exact ⟨obj, hobjAt, List.contains_iff_mem.mpr hmem⟩

-- H3 lifted along a `ReachableStep` chain, rooted at an *arbitrary* object confirmed to be inside
-- region `rid` (not necessarily the region's own bridge object): mirrors
-- `RegionReachable_oid_confined`'s proof exactly (its `bridge` base case generalized to any
-- confirmed-in-`rid` starting point), so the conclusion is the same 3-way disjunction: the target
-- resolves back into `rid` itself, or into some *other* Closed region reached along the way, or
-- it's a bare region reference.
theorem reflTransGen_region_confined {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid : RegionId} {region : Region} (hlookup : cfg.heap.lookup rid = some region)
    {oidStart : ObjectId} (hlocStart : (Reference.OId oidStart).loc? cfg = some (Location.Rgn rid))
    {target : Reference} (hrtg : Relation.ReflTransGen (ReachableStep cfg) (Reference.OId oidStart) target) :
    (∃ oid ridCur region', target = Reference.OId oid ∧ (Reference.OId oid).loc? cfg = some (Location.Rgn ridCur) ∧
       cfg.heap.lookup ridCur = some region' ∧ (ridCur = rid ∨ region'.status = Status.Closed)) ∨
    (∃ ridR, target = Reference.RId ridR) := by
  induction hrtg with
  | refl => left; exact ⟨oidStart, rid, region, rfl, hlocStart, hlookup, Or.inl rfl⟩
  | tail hprev hstep ih =>
    rename_i b c
    have hmemrefs : ∃ ridCur region', c ∈ region'.refs ∧ cfg.heap.lookup ridCur = some region' ∧
        (ridCur = rid ∨ region'.status = Status.Closed) := by
      rcases ih with ⟨oidB, ridCur, region', heqB, hlocB, hlkB, hcaseB⟩ | ⟨ridB, heqB⟩
      · subst heqB
        rw [ReachableStep_oid_iff] at hstep
        obtain ⟨obj, hobjAt, hcontains⟩ := hstep
        unfold Reference.objAt? at hobjAt
        dsimp only at hobjAt
        rw [hlocB] at hobjAt
        dsimp only at hobjAt
        rw [hlkB] at hobjAt
        exact ⟨ridCur, region', mem_region_refs_of_mem_objMap hobjAt (List.contains_iff_mem.mp hcontains), hlkB, hcaseB⟩
      · subst heqB
        rw [ReachableStep_rid_iff] at hstep
        obtain ⟨regionR, hlkR, hclosedR, obj, hobjlookup, hcontains⟩ := hstep
        exact ⟨ridB, regionR, mem_region_refs_of_mem_objMap hobjlookup (List.contains_iff_mem.mp hcontains),
          hlkR, Or.inr hclosedR⟩
    obtain ⟨ridCur, region', hmemB, hlkCur, hcaseCur⟩ := hmemrefs
    cases c with
    | OId oidB =>
      left
      have hridEq := vcfg.h3 ridCur oidB region' hlkCur hmemB
      exact ⟨oidB, ridCur, region', rfl, hridEq, hlkCur, hcaseCur⟩
    | RId ridB => right; exact ⟨ridB, rfl⟩

-- The specific contradiction FIELD-ASGN-REGION's "G = active frame" backward case needs: a chain
-- rooted at some object confirmed inside `rid` (Open) can never reach an object confirmed to live
-- in some *other*, also-Open region -- mirrors `region_reachable_open_ne_absurd` exactly, just
-- built on `reflTransGen_region_confined`'s more general base case.
theorem reflTransGen_region_open_ne_absurd {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid : RegionId} {region : Region} (hlookup : cfg.heap.lookup rid = some region)
    {oidStart : ObjectId} (hlocStart : (Reference.OId oidStart).loc? cfg = some (Location.Rgn rid))
    {oidTarget : ObjectId} {ridT : RegionId} {regionT : Region}
    (hlocT : (Reference.OId oidTarget).loc? cfg = some (Location.Rgn ridT))
    (hlkT : cfg.heap.lookup ridT = some regionT) (hopenT : regionT.status = Status.Open) (hne : ridT ≠ rid)
    (hrtg : Relation.ReflTransGen (ReachableStep cfg) (Reference.OId oidStart) (Reference.OId oidTarget)) : False := by
  rcases reflTransGen_region_confined vcfg hlookup hlocStart hrtg with
    ⟨oid', ridCur, region', heq, hloc', hlk', hcase'⟩ | ⟨ridR, heq⟩
  · rw [Reference.OId.injEq] at heq
    subst heq
    rw [hlocT, Option.some_inj, Location.Rgn.injEq] at hloc'
    subst hloc'
    rw [hlkT, Option.some_inj] at hlk'
    subst hlk'
    rcases hcase' with hcaseEq | hcaseClosed
    · exact hne hcaseEq
    · rw [hopenT] at hcaseClosed
      exact absurd hcaseClosed (by decide)
  · exact absurd heq (by simp)

-- ===== merge =====

-- An allocated object id always resolves somewhere (never `none`); reproven here since this layer can't import `Gc.Reachability.Referencable`.
theorem loc_ne_none_of_mem_objectIds (cfg : RuntimeConfig) (hvalid : ValidConfig cfg) (oid : ObjectId)
    (hmem : oid ∈ cfg.objectIds) : (Reference.OId oid).loc? cfg ≠ none := by
  unfold RuntimeConfig.objectIds at hmem
  rw [List.mem_append] at hmem
  unfold Reference.loc?
  dsimp only
  cases hs : cfg.stackWithIndex.findRev? (fun frame => frame.objMap.keys.contains oid) with
  | some frame => rw [oid_in_stack_implies_not_in_heap hvalid hs]; simp
  | none =>
    cases hh : cfg.heap.entries.find? (fun x => x.snd.objMap.keys.contains oid) with
    | some pr => simp
    | none =>
      simp only [ne_eq, not_true_eq_false]
      rcases hmem with hmem_stack | hmem_heap
      · unfold Stack.objectIds at hmem_stack
        rw [List.bind_eq_flatMap, List.flatMap_id, List.mem_flatten] at hmem_stack
        obtain ⟨keys, hkeys_mem, hoid_mem⟩ := hmem_stack
        obtain ⟨frame0, hframe0_mem, hframe0_eq⟩ := List.mem_map.mp hkeys_mem
        unfold Frame.objectIds at hframe0_eq
        rw [← hframe0_eq] at hoid_mem
        obtain ⟨n, hn, hn_eq⟩ := List.mem_iff_getElem.mp hframe0_mem
        have hlen : n < cfg.stackWithIndex.length := by
          unfold RuntimeConfig.stackWithIndex; rwa [List.length_mapIdx]
        have hget : cfg.stackWithIndex[n].objMap = frame0.objMap := by
          unfold RuntimeConfig.stackWithIndex
          rw [List.getElem_mapIdx, hn_eq]
        have hmemW := List.getElem_mem hlen
        have hcontains : cfg.stackWithIndex[n].objMap.keys.contains oid = true := by
          rw [hget]; exact List.contains_iff_mem.mpr (AList.mem_keys.mpr hoid_mem)
        rw [List.findRev?_eq_find?_reverse] at hs
        exact List.find?_eq_none.mp hs cfg.stackWithIndex[n] (List.mem_reverse.mpr hmemW) hcontains
      · unfold Heap.objectIds at hmem_heap
        rw [List.mem_flatten] at hmem_heap
        obtain ⟨keys, hkeys_mem, hoid_mem⟩ := hmem_heap
        obtain ⟨pr, hpr_mem, hpr_eq⟩ := List.mem_map.mp hkeys_mem
        unfold Region.objectIds at hpr_eq
        rw [← hpr_eq] at hoid_mem
        have hcontains : pr.2.objMap.keys.contains oid = true :=
          List.contains_iff_mem.mpr (AList.mem_keys.mpr hoid_mem)
        exact List.find?_eq_none.mp hh pr hpr_mem hcontains

-- merge relocates objects between heap keys but never creates/destroys any object id (mirrors `merge_L1`).
theorem merge_objectIds_perm (vcfg : ValidConfig cfg) {x : VarName} {cfg' : RuntimeConfig}
    (h : merge x cfg = some cfg') : cfg'.objectIds.Perm cfg.objectIds := by
  have l1 := vcfg.l1
  obtain ⟨frame, rid', region, region', hframe, hxref, hregion, hregion', hclosed, hopen, hcfg'⟩ :=
    merge_cases h
  subst hcfg'
  have hne := merge_corollary_rid_ne_regionId hregion hregion' hclosed hopen
  have heap_perm := merge_corollary_heap_objectIds_perm l1 hregion hregion' hne
  have stack_eq : cfg.stack = cfg.stack.dropLast ++ [frame] :=
    (List.dropLast_append_getLast? frame hframe).symm
  unfold RuntimeConfig.objectIds
  dsimp only
  have stack_objectIds_eq : Stack.objectIds (cfg.stack.dropLast ++
      [{ frame with varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) }]) =
      Stack.objectIds cfg.stack := by
    conv_rhs => rw [stack_eq]
    unfold Stack.objectIds
    rw [List.map_append, List.map_append]
    rfl
  rw [stack_objectIds_eq]
  exact List.Perm.append_left (Stack.objectIds cfg.stack) heap_perm

-- Every frame's `objMap` is unaffected by merge (only the last frame's `varMap` changes); wraps `stackWithIndex_objMap_get_eq_of_last_varMap_update`.
theorem merge_corollary_objMap_get_eq {cfg cfg' : RuntimeConfig} {x : VarName}
    (h : merge x cfg = some cfg') (n : ℕ) :
    (cfg.stack[n]?).map Frame.objMap = (cfg'.stack[n]?).map Frame.objMap := by
  obtain ⟨frame, rid', region, region', hframe, hxref, hregion, hregion', hclosed, hopen, hcfg'⟩ :=
    merge_cases h
  have hstack' : cfg'.stack = cfg.stack.dropLast ++
      [({ regionId := frame.regionId, bridgeVar := frame.bridgeVar, objMap := frame.objMap,
          varMap := AList.insert x (Reference.OId region'.bridgeObjectId) frame.varMap } : Frame)] := by
    rw [hcfg']
  exact stackWithIndex_objMap_get_eq_of_last_varMap_update hframe hstack' n

-- On disjoint keys, `.lookup` on the union agrees with `.lookup` on whichever side has the key.
theorem merge_corollary_union_lookup_left {region region' : Region} {oid : ObjectId}
    (hoid : oid ∈ region.objMap.keys)
    (heq : (region.objMap ∪ region'.objMap).entries = region.objMap.entries ++ region'.objMap.entries) :
    (region.objMap ∪ region'.objMap).lookup oid = region.objMap.lookup oid := by
  unfold AList.lookup
  rw [heq, List.dlookup_append]
  cases hv : List.dlookup oid region.objMap.entries with
  | none =>
    exfalso
    have : region.objMap.lookup oid = none := by unfold AList.lookup; rw [hv]
    rw [AList.lookup_eq_none] at this
    exact this hoid
  | some v => rfl

theorem merge_corollary_union_lookup_right {region region' : Region} {oid : ObjectId}
    (hoid : oid ∈ region'.objMap.keys)
    (hdisj : ∀ o ∈ region.objMap.keys, o ∉ region'.objMap.keys)
    (heq : (region.objMap ∪ region'.objMap).entries = region.objMap.entries ++ region'.objMap.entries) :
    (region.objMap ∪ region'.objMap).lookup oid = region'.objMap.lookup oid := by
  unfold AList.lookup
  rw [heq, List.dlookup_append]
  have hnone : List.dlookup oid region.objMap.entries = none := by
    have : region.objMap.lookup oid = none := by
      rw [AList.lookup_eq_none]
      intro hc
      exact hdisj oid hc hoid
    unfold AList.lookup at this
    exact this
  rw [hnone]
  rfl

-- `objAt?` is unconditionally preserved by merge (only relocates heap entries, never edits content); ported from Referencable's private `merge_corollary_objAt_eq`.
theorem merge_objAt_eq (vcfg : ValidConfig cfg) {x : VarName} {cfg' : RuntimeConfig}
    (h : merge x cfg = some cfg') (oid : ObjectId) :
    (Reference.OId oid).objAt? cfg = (Reference.OId oid).objAt? cfg' := by
  have vcfg' := merge_valid vcfg h
  have l1 := vcfg.l1
  obtain ⟨frame, rid', region, region', hframe, hxref, hregion, hregion', hclosed, hopen, hcfg'⟩ :=
    merge_cases h
  have hne := merge_corollary_rid_ne_regionId hregion hregion' hclosed hopen
  have hdisj := merge_corollary_disjoint_keys l1 hregion hregion' hne
  have hunion_append := merge_corollary_union_append l1 hregion hregion' hne
  have hobjeq : ({ frame with varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) } :
      Frame).objMap = frame.objMap := rfl
  cases hloc : (Reference.OId oid).loc? cfg with
  | none =>
    have hloc' : (Reference.OId oid).loc? cfg' = none := by
      by_contra hc
      have hmem' : oid ∈ cfg'.objectIds := by
        rcases Option.ne_none_iff_exists'.mp hc with ⟨loc', hloc'eq⟩
        cases loc' with
        | Stk fid0 =>
          obtain ⟨frame0, hframe0, hmem0⟩ := (oid_loc_stk_iff_in_stack vcfg').mp hloc'eq
          obtain ⟨sf0, hsf0, hsf0_eq⟩ : ∃ sf, cfg'.stack[fid0]? = some sf ∧ frame0 = { sf with index := fid0 } := by
            have h' := hframe0
            unfold RuntimeConfig.stackWithIndex at h'
            rw [List.getElem?_mapIdx, Option.map_eq_some_iff] at h'
            obtain ⟨sf, hsf, hsf_eq⟩ := h'
            exact ⟨sf, hsf, hsf_eq.symm⟩
          unfold RuntimeConfig.objectIds Stack.objectIds Frame.objectIds
          rw [List.bind_eq_flatMap, List.flatMap_id, List.mem_append, List.mem_flatten]
          left
          refine ⟨frame0.objMap.keys, ?_, AList.mem_keys.mpr hmem0⟩
          rw [hsf0_eq]
          dsimp only
          exact List.mem_map_of_mem (List.mem_of_getElem? hsf0)
        | Rgn rid0 =>
          obtain ⟨region0, hlookup0, hmem0⟩ := (oid_loc_rgn_iff_in_heap vcfg').mp hloc'eq
          unfold RuntimeConfig.objectIds
          apply List.mem_append_right
          exact heap_objectIds_of_mem (AList.lookup_mem_entries hlookup0) (AList.mem_keys.mpr hmem0)
      have hmem : oid ∈ cfg.objectIds := (merge_objectIds_perm vcfg h).mem_iff.mp hmem'
      exact loc_ne_none_of_mem_objectIds cfg vcfg oid hmem hloc
    unfold Reference.objAt?
    dsimp only
    rw [hloc, hloc']
  | some loc =>
    cases loc with
    | Stk fid0 =>
      obtain ⟨frame0, hframe0, hmem0⟩ := (oid_loc_stk_iff_in_stack vcfg).mp hloc
      obtain ⟨sf0, hsf0, hsf0_eq⟩ : ∃ sf, cfg.stack[fid0]? = some sf ∧ frame0 = { sf with index := fid0 } := by
        have h' := hframe0
        unfold RuntimeConfig.stackWithIndex at h'
        rw [List.getElem?_mapIdx, Option.map_eq_some_iff] at h'
        obtain ⟨sf, hsf, hsf_eq⟩ := h'
        exact ⟨sf, hsf, hsf_eq.symm⟩
      have hmapeq1 := merge_corollary_objMap_get_eq h fid0
      rw [hsf0] at hmapeq1
      obtain ⟨sf0', hsf0', hsf0'_objMap⟩ := Option.map_eq_some_iff.mp hmapeq1.symm
      have hsf0_objMap_eq : sf0.objMap = frame0.objMap := by rw [hsf0_eq]
      have hmem0' : oid ∈ ({ sf0' with index := fid0 } : FrameWithIndex).objMap := by
        show oid ∈ sf0'.objMap
        rw [hsf0'_objMap, hsf0_objMap_eq]
        exact hmem0
      have hcfg'_swi : cfg'.stackWithIndex[fid0]? = some ({ sf0' with index := fid0 } : FrameWithIndex) := by
        unfold RuntimeConfig.stackWithIndex
        rw [List.getElem?_mapIdx, hsf0']
        rfl
      have hloc' : (Reference.OId oid).loc? cfg' = some (Location.Stk fid0) :=
        (oid_loc_stk_iff_in_stack vcfg').mpr ⟨{ sf0' with index := fid0 }, hcfg'_swi, hmem0'⟩
      have hmem0mem : frame0 ∈ cfg.stackWithIndex := List.mem_of_getElem? hframe0
      have hmem0mem' : ({ sf0' with index := fid0 } : FrameWithIndex) ∈ cfg'.stackWithIndex := by
        obtain ⟨hn, heq⟩ := List.getElem?_eq_some_iff.mp hsf0'
        unfold RuntimeConfig.stackWithIndex
        exact List.mem_mapIdx.mpr ⟨fid0, hn, by rw [heq]⟩
      have hidx0 : frame0.index = fid0 := by rw [hsf0_eq]
      have hfind0 : cfg.stackWithIndex.find? (fun f => f.index == fid0) = some frame0 := by
        rw [← hidx0]; exact swap_corollary_stackWithIndex_find_eq hmem0mem
      have hfind0' : cfg'.stackWithIndex.find? (fun f => f.index == fid0) = some { sf0' with index := fid0 } :=
        swap_corollary_stackWithIndex_find_eq hmem0mem'
      have hobjMap0 : frame0.objMap = ({ sf0' with index := fid0 } : FrameWithIndex).objMap := by
        show frame0.objMap = sf0'.objMap
        rw [← hsf0_objMap_eq, hsf0'_objMap]
      unfold Reference.objAt?
      dsimp only
      rw [hloc, hloc']
      dsimp only
      rw [hfind0, hfind0']
      exact congrArg (AList.lookup oid) hobjMap0
    | Rgn rid0 =>
      obtain ⟨region0, hlookup0, hmem0⟩ := (oid_loc_rgn_iff_in_heap vcfg).mp hloc
      have hstack_none : cfg.stackWithIndex.findRev? (fun f => f.objMap.keys.contains oid) = none :=
        merge_corollary_loc_rgn_stack_none hloc
      by_cases heqr : rid0 = frame.regionId
      · subst heqr
        rw [hregion, Option.some_inj] at hlookup0
        subst hlookup0
        have hoid0' : oid ∈ ({ region with objMap := region.objMap ∪ region'.objMap } : Region).objMap.keys :=
          AList.mem_union.mpr (Or.inl hmem0)
        have hloc' : (Reference.OId oid).loc? cfg' = some (Location.Rgn frame.regionId) := by
          rw [hcfg']
          exact merge_corollary_loc_of_mem l1 hregion hregion' hne hobjeq hframe hstack_none
            (AList.lookup_insert (a := frame.regionId)
              (b := { region with objMap := region.objMap ∪ region'.objMap }) (s := cfg.heap.erase rid')) hoid0'
        unfold Reference.objAt?
        dsimp only
        rw [hloc, hloc']
        dsimp only
        rw [hregion, hcfg']
        dsimp only
        rw [AList.lookup_insert]
        exact (merge_corollary_union_lookup_left (AList.mem_keys.mp hmem0) hunion_append).symm
      · by_cases hrid' : rid0 = rid'
        · subst hrid'
          rw [hregion', Option.some_inj] at hlookup0
          subst hlookup0
          have hoid0' : oid ∈ ({ region with objMap := region.objMap ∪ region'.objMap } : Region).objMap.keys :=
            AList.mem_union.mpr (Or.inr hmem0)
          have hloc' : (Reference.OId oid).loc? cfg' = some (Location.Rgn frame.regionId) := by
            rw [hcfg']
            exact merge_corollary_loc_of_mem l1 hregion hregion' hne hobjeq hframe hstack_none
              (AList.lookup_insert (a := frame.regionId)
                (b := { region with objMap := region.objMap ∪ region'.objMap }) (s := cfg.heap.erase rid0)) hoid0'
          unfold Reference.objAt?
          dsimp only
          rw [hloc, hloc']
          dsimp only
          rw [hregion', hcfg']
          dsimp only
          rw [AList.lookup_insert]
          exact (merge_corollary_union_lookup_right (AList.mem_keys.mp hmem0) hdisj hunion_append).symm
        · have hlookup_cfg' : cfg'.heap.lookup rid0 = cfg.heap.lookup rid0 := by
            rw [hcfg']
            dsimp only
            exact AList.lookup_insert_ne heqr |>.trans (AList.lookup_erase_ne hrid')
          have hloc' : (Reference.OId oid).loc? cfg' = some (Location.Rgn rid0) :=
            (oid_loc_rgn_iff_in_heap vcfg').mpr ⟨region0, by rw [hlookup_cfg']; exact hlookup0, hmem0⟩
          unfold Reference.objAt?
          dsimp only
          rw [hloc, hloc']
          dsimp only
          rw [hlookup_cfg']

-- ReachableStep from an `OId` is unconditionally preserved by merge (direct corollary of `merge_objAt_eq`).
theorem merge_oid_step_iff (vcfg : ValidConfig cfg) {x : VarName} {cfg' : RuntimeConfig}
    (h : merge x cfg = some cfg') (oid : ObjectId) (b : Reference) :
    ReachableStep cfg (Reference.OId oid) b ↔ ReachableStep cfg' (Reference.OId oid) b := by
  rw [ReachableStep_oid_iff, ReachableStep_oid_iff, merge_objAt_eq vcfg h oid]

-- ReachableStep from `RId rid` with `rid ≠ rid'` is unconditional: `cfg.heap.lookup rid` is untouched by merge's insert/erase (and the active region stays Open, so it never steps either way).
theorem merge_rid_step_iff_of_ne {cfg cfg' : RuntimeConfig} {x : VarName} {frame : Frame} {rid' : RegionId}
    {region region' : Region}
    (_hframe : cfg.stack.getLast? = some frame) (_hxref : frame.varMap.lookup x = some (Reference.RId rid'))
    (hregion : cfg.heap.lookup frame.regionId = some region) (_hregion' : cfg.heap.lookup rid' = some region')
    (_hclosed : region'.status = Status.Closed) (hopen : region.status = Status.Open)
    (hcfg' : cfg' = { cfg with
      heap := (cfg.heap.erase rid').insert frame.regionId { region with objMap := region.objMap ∪ region'.objMap },
      stack := cfg.stack.dropLast ++
        [{ frame with varMap := frame.varMap.insert x (Reference.OId region'.bridgeObjectId) }] }) :
    ∀ {rid : RegionId}, rid ≠ rid' → ∀ (b : Reference),
    ReachableStep cfg (Reference.RId rid) b ↔ ReachableStep cfg' (Reference.RId rid) b := by
  intro rid hne b
  by_cases heq : rid = frame.regionId
  · subst heq
    have hlookup' : cfg'.heap.lookup frame.regionId =
        some { region with objMap := region.objMap ∪ region'.objMap } := by
      rw [hcfg']; dsimp only; rw [AList.lookup_insert]
    exact iff_of_false (open_rid_no_step hregion hopen) (open_rid_no_step hlookup' hopen)
  · have hlookup_eq : cfg'.heap.lookup rid = cfg.heap.lookup rid := by
      rw [hcfg']; dsimp only
      rw [AList.lookup_insert_ne heq, AList.lookup_erase_ne hne]
    rw [ReachableStep_rid_iff, ReachableStep_rid_iff, hlookup_eq]

-- Reshapes `Stack.refs`/`Heap.refs` into plain `List.flatMap` form so `Gc.Model.Theorems`'s count lemmas apply directly.
theorem stack_refs_eq_flatMap (stack : Stack) : stack.refs = stack.flatMap Frame.refs := by
  unfold Stack.refs
  rw [List.bind_eq_flatMap, List.flatMap_id, List.flatMap_def]

theorem heap_refs_eq_flatMap (heap : Heap) :
    heap.refs = heap.entries.flatMap (fun e => e.2.refs) := by
  unfold Heap.refs
  rw [List.bind_eq_flatMap, List.flatMap_def, List.map_map, ← List.flatMap_def]
  rfl

-- `RId rid'` is never a `ReachableStep` target: `x`'s varMap entry is H2's one allowed occurrence, so it can only ever be a chain's root, never a later hop.
theorem merge_ridPrime_not_step_target (vcfg : ValidConfig cfg) {frame : Frame} {rid' : RegionId}
    (hframemem : frame ∈ cfg.stack) (hxref : frame.varMap.lookup x = some (Reference.RId rid')) :
    ∀ (a : Reference), ¬ ReachableStep cfg a (Reference.RId rid') := by
  intro a hstep
  have h2 := vcfg.h2 rid'
  cases a with
  | RId ridA =>
    rw [ReachableStep_rid_iff] at hstep
    obtain ⟨regionA, hlookupA, -, obj, hobjlookup, hcontains⟩ := hstep
    have hmemrefs : Reference.RId rid' ∈ regionA.refs :=
      mem_region_refs_of_mem_objMap hobjlookup (List.contains_iff_mem.mp hcontains)
    have hcount_heap : 1 ≤ cfg.heap.refs.count (Reference.RId rid') := by
      rw [heap_refs_eq_flatMap]
      apply List.count_pos_iff.mpr
      rw [List.mem_flatMap]
      exact ⟨⟨ridA, regionA⟩, AList.lookup_mem_entries hlookupA, hmemrefs⟩
    have hcount_stack : 1 ≤ cfg.stack.refs.count (Reference.RId rid') := by
      rw [stack_refs_eq_flatMap]
      apply List.count_pos_iff.mpr
      rw [List.mem_flatMap]
      exact ⟨frame, hframemem, mem_frame_refs_of_mem_varMap hxref⟩
    omega
  | OId oidA =>
    rw [ReachableStep_oid_iff] at hstep
    obtain ⟨obj, hobjAt, hcontains⟩ := hstep
    unfold Reference.objAt? at hobjAt
    dsimp only at hobjAt
    cases hloc' : (Reference.OId oidA).loc? cfg with
    | none => rw [hloc'] at hobjAt; simp at hobjAt
    | some loc =>
      rw [hloc'] at hobjAt
      cases loc with
      | Rgn ridR =>
        dsimp only at hobjAt
        cases hlookupR : cfg.heap.lookup ridR with
        | none => rw [hlookupR] at hobjAt; simp at hobjAt
        | some regionR =>
          rw [hlookupR] at hobjAt
          have hmemrefs : Reference.RId rid' ∈ regionR.refs :=
            mem_region_refs_of_mem_objMap hobjAt (List.contains_iff_mem.mp hcontains)
          have hcount_heap : 1 ≤ cfg.heap.refs.count (Reference.RId rid') := by
            rw [heap_refs_eq_flatMap]
            apply List.count_pos_iff.mpr
            rw [List.mem_flatMap]
            exact ⟨⟨ridR, regionR⟩, AList.lookup_mem_entries hlookupR, hmemrefs⟩
          have hcount_stack : 1 ≤ cfg.stack.refs.count (Reference.RId rid') := by
            rw [stack_refs_eq_flatMap]
            apply List.count_pos_iff.mpr
            rw [List.mem_flatMap]
            exact ⟨frame, hframemem, mem_frame_refs_of_mem_varMap hxref⟩
          omega
      | Stk fidR =>
        dsimp only at hobjAt
        cases hfind : cfg.stackWithIndex.find? (fun f => f.index == fidR) with
        | none => rw [hfind] at hobjAt; simp at hobjAt
        | some someFrame =>
          rw [hfind] at hobjAt
          have hmemSWI : someFrame ∈ cfg.stackWithIndex := List.mem_of_find?_eq_some hfind
          have hmemstack : someFrame.toFrame ∈ cfg.stack := by
            obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hmemSWI
            rw [← hfeq]; exact List.getElem_mem hn
          have hmemrefs : Reference.RId rid' ∈ someFrame.refs :=
            mem_frame_refs_of_mem_objMap hobjAt (List.contains_iff_mem.mp hcontains)
          by_cases heqframe : someFrame.toFrame = frame
          · have hmemrefs' : Reference.RId rid' ∈ frame.refs := heqframe ▸ hmemrefs
            have hcount_frame : 2 ≤ frame.refs.count (Reference.RId rid') := by
              unfold Frame.refs
              rw [List.count_append]
              have hobjmem : Reference.RId rid' ∈ (frame.objMap.entries.map (·.2) >>= Object.refs) := by
                have : someFrame.objMap.entries.map (·.2) >>= Object.refs =
                    frame.objMap.entries.map (·.2) >>= Object.refs := by rw [heqframe]
                rw [← this, List.bind_eq_flatMap, List.mem_flatMap]
                exact ⟨obj, List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hobjAt),
                  List.contains_iff_mem.mp hcontains⟩
              have hvarmem : Reference.RId rid' ∈ (frame.varMap.entries.map (·.2)) :=
                List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hxref)
              have h1 : 1 ≤ (frame.objMap.entries.map (·.2) >>= Object.refs).count (Reference.RId rid') :=
                List.count_pos_iff.mpr hobjmem
              have h1' : 1 ≤ (frame.varMap.entries.map (·.2)).count (Reference.RId rid') :=
                List.count_pos_iff.mpr hvarmem
              omega
            have hcount_stack : 2 ≤ cfg.stack.refs.count (Reference.RId rid') := by
              rw [stack_refs_eq_flatMap]
              exact le_trans hcount_frame (List.count_le_count_flatMap_of_mem hframemem)
            omega
          · have hcount_stack : 2 ≤ cfg.stack.refs.count (Reference.RId rid') := by
              rw [stack_refs_eq_flatMap]
              exact List.two_le_count_flatMap_of_ne (f := Frame.refs) heqframe hmemstack hframemem
                hmemrefs (mem_frame_refs_of_mem_varMap hxref)
            omega

-- `RId rid'` and `OId region'.bridgeObjectId` are interchangeable as `ReachableStep` sources: a step from the (Closed) region is exactly a step from its own bridge object's fields.
theorem merge_ridPrime_step_iff_bridge (vcfg : ValidConfig cfg) {rid' : RegionId} {region' : Region}
    (hregion' : cfg.heap.lookup rid' = some region') (hclosed : region'.status = Status.Closed)
    (b : Reference) :
    ReachableStep cfg (Reference.RId rid') b ↔ ReachableStep cfg (Reference.OId region'.bridgeObjectId) b := by
  have hbridgeMem : region' ∈ cfg.heap.regions := by
    unfold Heap.regions
    exact List.mem_map_of_mem (AList.lookup_mem_entries hregion')
  have hbridgeIn : region'.bridgeObjectId ∈ region'.objMap := vcfg.h1 region' hbridgeMem
  have hloc : (Reference.OId region'.bridgeObjectId).loc? cfg = some (Location.Rgn rid') :=
    (oid_loc_rgn_iff_in_heap vcfg).mpr ⟨region', hregion', hbridgeIn⟩
  rw [ReachableStep_rid_iff, ReachableStep_oid_iff]
  unfold Reference.objAt?
  dsimp only
  rw [hloc]
  dsimp only
  rw [hregion']
  constructor
  · rintro ⟨region2, hlookup2, -, obj, hobj, hcontains⟩
    injection hlookup2 with hlookup2eq
    subst hlookup2eq
    exact ⟨obj, hobj, hcontains⟩
  · rintro ⟨obj, hobj, hcontains⟩
    exact ⟨region', rfl, hclosed, obj, hobj, hcontains⟩

-- Chain-level version: for `target` other than `RId rid'`/the bridge object, a `RId rid'`-rooted chain to it exists iff a chain rooted at `region'.bridgeObjectId` (one hop shorter) does.
theorem merge_ridPrime_reflTransGen_iff (vcfg : ValidConfig cfg) {rid' : RegionId} {region' : Region}
    (hregion' : cfg.heap.lookup rid' = some region') (hclosed : region'.status = Status.Closed)
    {target : Reference} (hne1 : target ≠ Reference.RId rid')
    (hne2 : target ≠ Reference.OId region'.bridgeObjectId) :
    Relation.ReflTransGen (ReachableStep cfg) (Reference.RId rid') target ↔
    Relation.ReflTransGen (ReachableStep cfg) (Reference.OId region'.bridgeObjectId) target := by
  constructor
  · intro hrtg
    rcases hrtg.cases_head with heq | ⟨c, hstep, hrest⟩
    · exact absurd heq.symm hne1
    · exact Relation.ReflTransGen.head ((merge_ridPrime_step_iff_bridge vcfg hregion' hclosed c).mp hstep) hrest
  · intro hrtg
    rcases hrtg.cases_head with heq | ⟨c, hstep, hrest⟩
    · exact absurd heq.symm hne2
    · exact Relation.ReflTransGen.head ((merge_ridPrime_step_iff_bridge vcfg hregion' hclosed c).mpr hstep) hrest

-- `x`'s own varMap entry is the only occurrence of `RId rid'` on the stack: no other frame can hold it too, or H2's count bound would be exceeded.
theorem merge_ridPrime_no_other_frame_var (vcfg : ValidConfig cfg) {frame : Frame} {rid' : RegionId}
    (hframemem : frame ∈ cfg.stack) (hxref : frame.varMap.lookup x = some (Reference.RId rid')) :
    ∀ {frame0 : Frame}, frame0 ∈ cfg.stack → frame0.regionId ≠ frame.regionId →
    ∀ {var0 : VarName}, frame0.varMap.lookup var0 ≠ some (Reference.RId rid') := by
  intro frame0 hframe0mem hridne var0 hvar0
  have h2 := vcfg.h2 rid'
  have hne : frame0 ≠ frame := fun hc => hridne (by rw [hc])
  have hmemrefs0 : Reference.RId rid' ∈ frame0.refs := mem_frame_refs_of_mem_varMap hvar0
  have hmemrefsF : Reference.RId rid' ∈ frame.refs := mem_frame_refs_of_mem_varMap hxref
  have hcount2 : 2 ≤ cfg.stack.refs.count (Reference.RId rid') := by
    rw [stack_refs_eq_flatMap]
    exact List.two_le_count_flatMap_of_ne hne hframe0mem hframemem hmemrefs0 hmemrefsF
  omega

-- Same idea, within a single frame: two distinct var slots can't both hold `RId rid'` either.
theorem merge_ridPrime_var_unique (vcfg : ValidConfig cfg) {frame : Frame} {rid' : RegionId}
    (hframemem : frame ∈ cfg.stack) (hxref : frame.varMap.lookup x = some (Reference.RId rid')) :
    ∀ {var0 : VarName}, var0 ≠ x → frame.varMap.lookup var0 ≠ some (Reference.RId rid') := by
  intro var0 hne hvar0
  have h2 := vcfg.h2 rid'
  have hmemX : (⟨x, Reference.RId rid'⟩ : Sigma (fun _ : VarName => Reference)) ∈ frame.varMap.entries :=
    AList.lookup_mem_entries hxref
  have hmemV : (⟨var0, Reference.RId rid'⟩ : Sigma (fun _ : VarName => Reference)) ∈ frame.varMap.entries :=
    AList.lookup_mem_entries hvar0
  have hneSig : (⟨x, Reference.RId rid'⟩ : Sigma (fun _ : VarName => Reference)) ≠ ⟨var0, Reference.RId rid'⟩ :=
    fun hc => hne (congrArg Sigma.fst hc).symm
  have hflatMapEq : frame.varMap.entries.flatMap (fun e => [e.2]) = frame.varMap.entries.map (·.2) := by
    induction frame.varMap.entries with
    | nil => rfl
    | cons a as ih => simp [List.flatMap_cons, ih]
  have hcount2 : 2 ≤ (frame.varMap.entries.map (·.2)).count (Reference.RId rid') := by
    rw [← hflatMapEq]
    exact List.two_le_count_flatMap_of_ne hneSig hmemX hmemV (List.mem_singleton_self _) (List.mem_singleton_self _)
  have hle1 : (frame.varMap.entries.map (·.2)).count (Reference.RId rid') ≤ frame.refs.count (Reference.RId rid') := by
    unfold Frame.refs; rw [List.count_append]; omega
  have hle2 : frame.refs.count (Reference.RId rid') ≤ cfg.stack.refs.count (Reference.RId rid') := by
    rw [stack_refs_eq_flatMap]
    exact List.count_le_count_flatMap_of_mem hframemem
  omega
