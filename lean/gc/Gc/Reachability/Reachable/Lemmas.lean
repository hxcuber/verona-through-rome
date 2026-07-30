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

-- A fresh object id never resolves anywhere (it isn't allocated yet).
theorem freshObjectId_objAt_none {cfg : RuntimeConfig} :
    (Reference.OId cfg.freshObjectId).objAt? cfg = none := by
  have hnotmem := cfg.freshObjectId_not_mem
  unfold RuntimeConfig.objectIds at hnotmem
  rw [List.mem_append] at hnotmem
  push_neg at hnotmem
  obtain ⟨hnotStack, hnotHeap⟩ := hnotmem
  have hloc : (Reference.OId cfg.freshObjectId).loc? cfg = none := by
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
  unfold Reference.objAt?
  dsimp only
  rw [hloc]

