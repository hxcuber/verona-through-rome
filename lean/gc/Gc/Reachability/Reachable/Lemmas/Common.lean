import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Mutation.Mutation
import Gc.Model.Preservation
import Gc.Reachability.Reachable.Semantics
import Gc.Reachability.Reachable.Basic

-- Generic, non-operation-specific helper lemmas shared across `Lemmas/<Op>.lean`, re-derived independently of `Gc.Reachability.Referencable`.

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

-- S2 at the `ReachableStep` level: a stack-to-stack hop's owning frame index never increases.
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

-- H3 forward: an `OId` step out of an object in region `rid` always lands back in `rid`.
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

-- L2's contrapositive: an on-stack frame can never own a Closed region.
theorem closed_region_not_owned {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid : RegionId} {region : Region} (hlookup : cfg.heap.lookup rid = some region)
    (hclosed : region.status = Status.Closed)
    {frame : FrameWithIndex} (hmem : frame ∈ cfg.stackWithIndex) (hrid : frame.regionId = rid) : False := by
  obtain ⟨region2, hlookup2, hopen2⟩ := l2_of_stackWithIndex vcfg hmem
  rw [hrid, hlookup] at hlookup2
  injection hlookup2 with heq
  rw [← heq, hclosed] at hopen2
  exact absurd hopen2 (by decide)

-- No `ReachableStep` sources from an Open region's `RId` (`deref?`'s guard requires Closed).
theorem open_rid_no_step {cfg : RuntimeConfig} {rid : RegionId} {region : Region}
    (hlookup : cfg.heap.lookup rid = some region) (hopen : region.status = Status.Open)
    {b : Reference} : ¬ ReachableStep cfg (Reference.RId rid) b := by
  rw [ReachableStep_rid_iff]
  rintro ⟨region', hlookup', hclosed', -⟩
  rw [hlookup] at hlookup'
  injection hlookup' with heq
  rw [← heq, hopen] at hclosed'
  exact absurd hclosed' (by decide)

-- A predecessor of an in-region object is itself in that region or on the stack (never `RId`, never another region — H3/Open-only rule those out).
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
        obtain ⟨region', hlookup', -, hbeq⟩ := hstep'
        injection hbeq with hbeqOid
        have hbridgeIn : region'.bridgeObjectId ∈ region'.objMap := vcfg.h1 region'
          (by unfold Heap.regions; exact List.mem_map_of_mem (AList.lookup_mem_entries hlookup'))
        have hlocBridge : (Reference.OId region'.bridgeObjectId).loc? cfg = some (Location.Rgn rid') :=
          (oid_loc_rgn_iff_in_heap vcfg).mpr ⟨region', hlookup', hbridgeIn⟩
        rw [← hbeqOid, hloc] at hlocBridge
        injection hlocBridge with hridEq
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

-- Closed-region analogue of `predecessor_of_region_object`: the "on stack" escape becomes impossible
-- (S3/L2), and the `RId` source becomes the portal hop instead of `open_rid_no_step`'s contradiction.
theorem predecessor_of_closed_region_object {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid : RegionId} {region : Region} (hlookup : cfg.heap.lookup rid = some region)
    (hclosed : region.status = Status.Closed) {oid : ObjectId}
    (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn rid))
    {a : Reference} (hstep : ReachableStep cfg a (Reference.OId oid)) :
    (∃ oid', a = Reference.OId oid' ∧ (Reference.OId oid').loc? cfg = some (Location.Rgn rid)) ∨
      (a = Reference.RId rid ∧ oid = region.bridgeObjectId) := by
  cases a with
  | RId rid' =>
    right
    rw [ReachableStep_rid_iff] at hstep
    obtain ⟨region', hlookup', -, hbeq⟩ := hstep
    injection hbeq with hbeqOid
    have hbridgeIn : region'.bridgeObjectId ∈ region'.objMap := vcfg.h1 region'
      (by unfold Heap.regions; exact List.mem_map_of_mem (AList.lookup_mem_entries hlookup'))
    have hlocBridge : (Reference.OId region'.bridgeObjectId).loc? cfg = some (Location.Rgn rid') :=
      (oid_loc_rgn_iff_in_heap vcfg).mpr ⟨region', hlookup', hbridgeIn⟩
    rw [← hbeqOid, hloc] at hlocBridge
    injection hlocBridge with hridEq
    injection hridEq with hridEq
    rw [← hridEq] at hlookup'
    rw [hlookup] at hlookup'
    injection hlookup' with hregionEq
    refine ⟨congrArg Reference.RId hridEq.symm, ?_⟩
    rw [hregionEq]
    exact hbeqOid
  | OId oid' =>
    left
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
          rw [hridEq]
      | Stk fid =>
        exfalso
        dsimp only at hobjAt
        cases hfind : cfg.stackWithIndex.find? (fun frame => frame.index == fid) with
        | none => rw [hfind] at hobjAt; simp at hobjAt
        | some someFrame =>
          rw [hfind] at hobjAt
          have hmem : someFrame ∈ cfg.stackWithIndex := List.mem_of_find?_eq_some hfind
          have hmemrefs : (Reference.OId oid) ∈ someFrame.refs :=
            mem_frame_refs_of_mem_objMap hobjAt (List.contains_iff_mem.mp hcontains)
          obtain ⟨frame', hmem', hridEq', -⟩ :=
            vcfg.s3 someFrame hmem (Reference.OId oid) hmemrefs rid oid rfl hloc
          exact closed_region_not_owned vcfg hlookup hclosed hmem' hridEq'

-- A predecessor of a stack-resident object is itself stack-resident (H3 rules out any region object pointing at the stack).
theorem predecessor_of_stack_object {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {oid : ObjectId} {fid : Index} (hloc : (Reference.OId oid).loc? cfg = some (Location.Stk fid))
    {a : Reference} (hstep : ReachableStep cfg a (Reference.OId oid)) :
    ∃ oid' fid', a = Reference.OId oid' ∧ (Reference.OId oid').loc? cfg = some (Location.Stk fid') := by
  cases a with
  | RId rid' =>
    exfalso
    rw [ReachableStep_rid_iff] at hstep
    obtain ⟨region', hlookup', -, hbeq⟩ := hstep
    injection hbeq with hbeqOid
    have hbridgeIn : region'.bridgeObjectId ∈ region'.objMap := vcfg.h1 region'
      (by unfold Heap.regions; exact List.mem_map_of_mem (AList.lookup_mem_entries hlookup'))
    have hlocBridge : (Reference.OId region'.bridgeObjectId).loc? cfg = some (Location.Rgn rid') :=
      (oid_loc_rgn_iff_in_heap vcfg).mpr ⟨region', hlookup', hbridgeIn⟩
    rw [← hbeqOid, hloc] at hlocBridge
    simp at hlocBridge
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

-- `SafeRef cfg rid`: an object inside `rid` or on the stack — never a bare `RId`, never another region's object.
def SafeRef (cfg : RuntimeConfig) (rid : RegionId) : Reference → Prop
  | Reference.OId oid => (Reference.OId oid).loc? cfg = some (Location.Rgn rid) ∨
      ∃ fid, (Reference.OId oid).loc? cfg = some (Location.Stk fid)
  | Reference.RId _ => False

-- Safety propagates backward across one `ReachableStep` hop (combines the two predecessor lemmas above).
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

-- If OId-sourced steps agree between cfg/cfg', any cfg-chain reaching a safe reference transports to a cfg'-chain.
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

-- Converse of `stackWithIndex_getElem_index_eq`: a member's own index recovers it via `[·]?`.
theorem stackWithIndex_mem_getElem_eq {cfg : RuntimeConfig} {frame : FrameWithIndex}
    (hmem : frame ∈ cfg.stackWithIndex) : cfg.stackWithIndex[frame.index]? = some frame := by
  obtain ⟨n, hn, hfeq⟩ := List.mem_mapIdx.mp hmem
  have hidx : frame.index = n := by rw [← hfeq]
  rw [hidx]
  unfold RuntimeConfig.stackWithIndex
  rw [List.getElem?_mapIdx, List.getElem?_eq_getElem hn, Option.map_some]
  exact congrArg some hfeq

-- Searching `stackWithIndex` by index is the same as direct indexing (indices are unique).
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

-- Anything reaching a stack-resident container at `fidC` roots from a frame with index `≥ fidC` (S2, chased backward via `stack_step_index_le`).
theorem stack_container_confined {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
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

-- S3 at the `ReachableStep` level: a stack-to-region hop's target region is owned by a frame with index ≤ the stack source's.
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

-- Anything reaching an in-region container roots from a frame with index `≥` the region owner's (H3-driven, whether the chase stays in-region or escapes to the stack).
theorem region_container_confined {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
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
    have hbound := stack_container_confined vcfg hlocB hreachB
    exact le_trans hleB hbound

-- Extends a `FrameReachable` witness forward along any further `ReachableStep` chain.
theorem FrameReachable_extend {cfg : RuntimeConfig} {fid : Index} {x y : Reference}
    (hx : FrameReachable cfg fid x) (hxy : Relation.ReflTransGen (ReachableStep cfg) x y) :
    FrameReachable cfg fid y := by
  induction hxy with
  | refl => exact hx
  | tail _ hstep ih => exact FrameReachable.step hstep ih

-- Closed-region confinement, the key CR6 ingredient: any way of reaching an object inside a Closed
-- region must factor through the region's own bridge object (the single portal hop `RId rid`).
theorem RegionReachable_of_FrameReachable_closed {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid : RegionId} {region : Region} (hlookup : cfg.heap.lookup rid = some region)
    (hclosed : region.status = Status.Closed)
    {fid : Index} {oid : ObjectId} (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn rid))
    (hreach : FrameReachable cfg fid (Reference.OId oid)) :
    RegionReachable cfg rid (Reference.OId oid) := by
  rw [FrameReachable_iff_reflTransGen] at hreach
  obtain ⟨start, hroot, hrtg⟩ := hreach
  have hback : ∀ ref, Relation.ReflTransGen (ReachableStep cfg) start ref →
      ∀ oidR, ref = Reference.OId oidR → (Reference.OId oidR).loc? cfg = some (Location.Rgn rid) →
        RegionReachable cfg rid ref := by
    intro ref hrtg2
    induction hrtg2 with
    | refl =>
      intro oidR heq hloc'
      exfalso
      rw [heq] at hroot
      rcases hroot with ⟨frame, hmem, -, var, hvar⟩ | ⟨frame, hmem, -, region2, hlookup2, hstart⟩
      · have hmemrefs : (Reference.OId oidR) ∈ frame.refs := mem_frame_refs_of_mem_varMap hvar
        obtain ⟨frame', hmem', hridEq', -⟩ := vcfg.s3 frame hmem (Reference.OId oidR) hmemrefs rid oidR rfl hloc'
        exact closed_region_not_owned vcfg hlookup hclosed hmem' hridEq'
      · injection hstart with hstartEq
        have hbridgeIn : region2.bridgeObjectId ∈ region2.objMap := vcfg.h1 region2
          (by unfold Heap.regions; exact List.mem_map_of_mem (AList.lookup_mem_entries hlookup2))
        have hlocBridge : (Reference.OId region2.bridgeObjectId).loc? cfg =
            some (Location.Rgn frame.regionId) :=
          (oid_loc_rgn_iff_in_heap vcfg).mpr ⟨region2, hlookup2, hbridgeIn⟩
        rw [← hstartEq, hloc'] at hlocBridge
        injection hlocBridge with hlocBridge'
        injection hlocBridge' with hlocBridge''
        exact closed_region_not_owned vcfg hlookup hclosed hmem hlocBridge''.symm
    | tail hprev hstep ih =>
      intro oidR heq hloc'
      subst heq
      rcases predecessor_of_closed_region_object vcfg hlookup hclosed hloc' hstep with
        ⟨oid', haeq, hloc''⟩ | ⟨-, hbridgeeq⟩
      · exact RegionReachable.step hstep (ih oid' haeq hloc'')
      · exact RegionReachable.bridge hlookup hbridgeeq.symm
  exact hback _ hrtg oid rfl hloc

-- The other half of closed-region confinement: reaching an object inside a Closed region forces the
-- region's own `RId` to already be frame-reachable (the portal hop is unavoidable, not just available).
theorem FrameReachable_rid_of_closed_container {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid : RegionId} {region : Region} (hlookup : cfg.heap.lookup rid = some region)
    (hclosed : region.status = Status.Closed)
    {fid : Index} {oid : ObjectId} (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn rid))
    (hreach : FrameReachable cfg fid (Reference.OId oid)) :
    FrameReachable cfg fid (Reference.RId rid) := by
  rw [FrameReachable_iff_reflTransGen] at hreach
  obtain ⟨start, hroot, hrtg⟩ := hreach
  have hback : ∀ ref, Relation.ReflTransGen (ReachableStep cfg) start ref →
      ∀ oidR, ref = Reference.OId oidR → (Reference.OId oidR).loc? cfg = some (Location.Rgn rid) →
        FrameReachable cfg fid (Reference.RId rid) := by
    intro ref hrtg2
    induction hrtg2 with
    | refl =>
      intro oidR heq hloc'
      exfalso
      rw [heq] at hroot
      rcases hroot with ⟨frame, hmem, -, var, hvar⟩ | ⟨frame, hmem, -, region2, hlookup2, hstart⟩
      · have hmemrefs : (Reference.OId oidR) ∈ frame.refs := mem_frame_refs_of_mem_varMap hvar
        obtain ⟨frame', hmem', hridEq', -⟩ := vcfg.s3 frame hmem (Reference.OId oidR) hmemrefs rid oidR rfl hloc'
        exact closed_region_not_owned vcfg hlookup hclosed hmem' hridEq'
      · injection hstart with hstartEq
        have hbridgeIn : region2.bridgeObjectId ∈ region2.objMap := vcfg.h1 region2
          (by unfold Heap.regions; exact List.mem_map_of_mem (AList.lookup_mem_entries hlookup2))
        have hlocBridge : (Reference.OId region2.bridgeObjectId).loc? cfg =
            some (Location.Rgn frame.regionId) :=
          (oid_loc_rgn_iff_in_heap vcfg).mpr ⟨region2, hlookup2, hbridgeIn⟩
        rw [← hstartEq, hloc'] at hlocBridge
        injection hlocBridge with hlocBridge'
        injection hlocBridge' with hlocBridge''
        exact closed_region_not_owned vcfg hlookup hclosed hmem hlocBridge''.symm
    | tail hprev hstep ih =>
      intro oidR heq hloc'
      subst heq
      rcases predecessor_of_closed_region_object vcfg hlookup hclosed hloc' hstep with
        ⟨oid', haeq, hloc''⟩ | ⟨haeq, -⟩
      · exact ih oid' haeq hloc''
      · rw [haeq] at hprev
        exact (FrameReachable_iff_reflTransGen cfg fid (Reference.RId rid)).mpr ⟨start, hroot, hprev⟩
  exact hback _ hrtg oid rfl hloc
