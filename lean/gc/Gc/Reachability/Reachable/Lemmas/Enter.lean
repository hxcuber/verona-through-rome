import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Mutation.Mutation
import Gc.Model.Preservation
import Gc.Reachability.Reachable.Semantics
import Gc.Reachability.Reachable.Basic
import Gc.Reachability.Reachable.Lemmas.Common

-- An on-stack frame's region is never what `enter` opens (L2: on-stack is Open, `enter` requires Closed).
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

-- `find? (index == fid)` over `stackWithIndex` is unaffected by appending a frame at a strictly larger index.
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
  · left
    obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hmem
    have hidx : frame.index = n := by rw [← hfeq]
    exact ⟨hmem, hidx ▸ hn⟩
  · right
    rw [List.mem_singleton] at hmem
    subst hmem
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

-- Any `cfg'.stackWithIndex` member whose index still fits inside `cfg.stack` was already there.
theorem enter_frame_mem_down {cfg cfg' : RuntimeConfig} (h : enter xf a cfg = some cfg')
    {frame : FrameWithIndex} (hframe : frame ∈ cfg'.stackWithIndex) (hlt : frame.index < cfg.stack.length) :
    frame ∈ cfg.stackWithIndex := by
  obtain ⟨rid, region, -, -, -, hcfg'⟩ := enter_cases h
  rcases enter_frame_cases hcfg' hframe with ⟨hmem, -⟩ | ⟨-, -, -, -, hidx⟩
  · exact hmem
  · rw [hidx] at hlt; exact absurd hlt (lt_irrefl _)
