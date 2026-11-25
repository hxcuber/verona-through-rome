module

public import Gc.Model.Types
public import Gc.Model.Helpers
public import Gc.Model.Validity
public import Gc.Model.Mutation.Mutation
public import Gc.Model.Preservation
public import Gc.Reachability.Reachable.Semantics

@[expose] public section

-- Generic, non-operation-specific helper lemmas shared across `Lemmas/<Op>.lean`.

-- An object's own refs contribute to its region's overall refs.
theorem mem_region_refs_of_mem_objMap {region : Region} {oid : ObjectId} {obj : Object}
    (hlookup : region.objMap.lookup oid = some obj) {b : Reference} (hb : b ∈ obj.refs) :
    b ∈ region.refs :=
  objMap_bind_refs_mem_of_lookup hlookup hb

-- An object's own refs contribute to its holding frame's overall refs.
theorem mem_frame_refs_of_mem_objMap {frame : Frame} {oid : ObjectId} {obj : Object}
    (hlookup : frame.objMap.lookup oid = some obj) {b : Reference} (hb : b ∈ obj.refs) :
    b ∈ frame.refs :=
  List.mem_append_left _ (objMap_bind_refs_mem_of_lookup hlookup hb)

-- A var's own value contributes directly to its frame's overall refs.
theorem mem_frame_refs_of_mem_varMap {frame : Frame} {var : VarName} {b : Reference}
    (hlookup : frame.varMap.lookup var = some b) : b ∈ frame.refs :=
  List.mem_append_right _ (List.mem_map_of_mem (AList.lookup_mem_entries hlookup))

-- A region's bridge object lives in that region (H1).
theorem bridge_loc {cfg : RuntimeConfig} (vcfg : ValidConfig cfg) {rid : RegionId} {region : Region}
    (hlookup : cfg.heap.lookup rid = some region) :
    (Reference.OId region.bridgeObjectId).loc? cfg = some (Location.Rgn rid) :=
  (oid_loc_rgn_iff_in_heap vcfg).mpr
    ⟨region, hlookup, vcfg.h1 region (List.mem_map_of_mem (AList.lookup_mem_entries hlookup))⟩

-- An `OId` hop's target is a ref of the source's container, either a heap region or a stack frame.
theorem oid_step_container {cfg : RuntimeConfig} {oid : ObjectId} {b : Reference}
    (hstep : ReachableStep cfg (Reference.OId oid) b) :
    (∃ rid region, (Reference.OId oid).loc? cfg = some (Location.Rgn rid) ∧
      cfg.heap.lookup rid = some region ∧ b ∈ region.refs) ∨
    (∃ frame ∈ cfg.stackWithIndex, (Reference.OId oid).loc? cfg = some (Location.Stk frame.index) ∧
      b ∈ frame.refs) := by
  obtain ⟨obj, hobjAt, hc⟩ := hstep
  have hb := List.contains_iff_mem.mp hc
  simp only [Reference.objAt?] at hobjAt
  split at hobjAt
  · rename_i rid hloc
    obtain ⟨region, hlk, hobj⟩ := Option.bind_eq_some_iff.mp hobjAt
    exact .inl ⟨rid, region, hloc, hlk, mem_region_refs_of_mem_objMap hobj hb⟩
  · rename_i fid hloc
    obtain ⟨frame, hfind, hobj⟩ := Option.bind_eq_some_iff.mp hobjAt
    have hidx := List.find?_some hfind
    rw [← beq_iff_eq.mp hidx] at hloc
    exact .inr ⟨frame, List.mem_of_find?_eq_some hfind, hloc, mem_frame_refs_of_mem_objMap hobj hb⟩
  · simp at hobjAt

-- An `RId` hop lands on the region's own bridge object, which lives in that (Closed) region.
theorem rid_step_inv {cfg : RuntimeConfig} (vcfg : ValidConfig cfg) {rid : RegionId} {oid : ObjectId}
    (hstep : ReachableStep cfg (Reference.RId rid) (Reference.OId oid)) :
    (Reference.OId oid).loc? cfg = some (Location.Rgn rid) ∧ ∃ region, cfg.heap.lookup rid = some region ∧
      region.status = Status.Closed ∧ oid = region.bridgeObjectId := by
  obtain ⟨region, hl, hc, he⟩ := hstep
  cases he
  exact ⟨bridge_loc vcfg hl, region, hl, hc, rfl⟩

-- Every predecessor of an in-region object: an in-region object, a stack object holding it, or the region's portal `RId`.
theorem predecessor_cases {cfg : RuntimeConfig} (vcfg : ValidConfig cfg) {rid : RegionId} {oid : ObjectId}
    (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn rid))
    {a : Reference} (hstep : ReachableStep cfg a (Reference.OId oid)) :
    (∃ oid', a = Reference.OId oid' ∧ (Reference.OId oid').loc? cfg = some (Location.Rgn rid)) ∨
    (∃ oid', ∃ frame ∈ cfg.stackWithIndex, a = Reference.OId oid' ∧
      (Reference.OId oid').loc? cfg = some (Location.Stk frame.index) ∧ Reference.OId oid ∈ frame.refs) ∨
    (a = Reference.RId rid ∧ ∃ region, cfg.heap.lookup rid = some region ∧
      region.status = Status.Closed ∧ oid = region.bridgeObjectId) := by
  cases a with
  | RId rid' =>
    obtain ⟨hl', h⟩ := rid_step_inv vcfg hstep
    obtain rfl : rid = rid' := by simpa using hloc.symm.trans hl'
    exact .inr (.inr ⟨rfl, h⟩)
  | OId oid' =>
    rcases oid_step_container hstep with ⟨rid', region', hl', hlk', hb⟩ | ⟨frame, hmem, hl', hb⟩
    · obtain rfl : rid = rid' := by simpa using hloc.symm.trans (vcfg.h3 rid' oid region' hlk' hb)
      exact .inl ⟨oid', rfl, hl'⟩
    · exact .inr (.inl ⟨oid', frame, hmem, rfl, hl', hb⟩)

-- S2 at the `ReachableStep` level: a stack-to-stack hop's owning frame index never increases.
theorem stack_step_index_le {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {oid oid' : ObjectId} {fidCur fidNext : Index}
    (hloc : (Reference.OId oid).loc? cfg = some (Location.Stk fidCur))
    (hstep : ReachableStep cfg (Reference.OId oid) (Reference.OId oid'))
    (hloc' : (Reference.OId oid').loc? cfg = some (Location.Stk fidNext)) :
    fidNext ≤ fidCur := by
  rcases oid_step_container hstep with ⟨rid, -, hl, -⟩ | ⟨frame, hmem, hl, hb⟩
  · simp [hl] at hloc
  · obtain rfl : frame.index = fidCur := by simpa using hl.symm.trans hloc
    exact vcfg.s2 frame hmem _ hb fidNext oid' rfl hloc'

-- H3 forward: an `OId` step out of an object in region `rid` always lands back in `rid`.
theorem successor_of_region_object {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid : RegionId} {region : Region} (hlookup : cfg.heap.lookup rid = some region)
    {oidA oidC : ObjectId} (hloc : (Reference.OId oidA).loc? cfg = some (Location.Rgn rid))
    (hstep : ReachableStep cfg (Reference.OId oidA) (Reference.OId oidC)) :
    (Reference.OId oidC).loc? cfg = some (Location.Rgn rid) := by
  rcases oid_step_container hstep with ⟨rid', region', hl, hlk, hb⟩ | ⟨frame, -, hl, -⟩
  · obtain rfl : rid' = rid := by simpa using hl.symm.trans hloc
    exact vcfg.h3 rid' oidC region' hlk hb
  · simp [hl] at hloc

-- L2's per-frame fact, restated directly in terms of `FrameWithIndex.regionId`.
theorem l2_of_stackWithIndex {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {frame : FrameWithIndex} (hframe : frame ∈ cfg.stackWithIndex) :
    ∃ region, cfg.heap.lookup frame.regionId = some region ∧ region.status = Status.Open := by
  obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp hframe
  exact vcfg.l2 _ (List.getElem_mem hn)

-- L2's contrapositive: an on-stack frame can never own a Closed region.
theorem closed_region_not_owned {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid : RegionId} {region : Region} (hlookup : cfg.heap.lookup rid = some region)
    (hclosed : region.status = Status.Closed)
    {frame : FrameWithIndex} (hmem : frame ∈ cfg.stackWithIndex) (hrid : frame.regionId = rid) : False := by
  obtain ⟨region2, hlookup2, hopen2⟩ := l2_of_stackWithIndex vcfg hmem
  rw [hrid, hlookup, Option.some_inj] at hlookup2
  simp [← hlookup2, hclosed] at hopen2

-- No `ReachableStep` sources from an Open region's `RId` (the `RId` branch requires Closed).
theorem open_rid_no_step {cfg : RuntimeConfig} {rid : RegionId} {region : Region}
    (hlookup : cfg.heap.lookup rid = some region) (hopen : region.status = Status.Open)
    {b : Reference} : ¬ ReachableStep cfg (Reference.RId rid) b := by
  rintro ⟨region', hlookup', hclosed', -⟩
  rw [hlookup, Option.some_inj] at hlookup'
  simp [← hlookup', hopen] at hclosed'

-- A predecessor of an in-region object is itself in that region or on the stack (never `RId`, never another region — H3/Open-only rule those out).
theorem predecessor_of_region_object {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid : RegionId} {region : Region} (hlookup : cfg.heap.lookup rid = some region)
    (hopen : region.status = Status.Open) {oid : ObjectId}
    (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn rid))
    {a : Reference} (hstep : ReachableStep cfg a (Reference.OId oid)) :
    ∃ oid', a = Reference.OId oid' ∧
      ((Reference.OId oid').loc? cfg = some (Location.Rgn rid) ∨
       ∃ fid, (Reference.OId oid').loc? cfg = some (Location.Stk fid)) := by
  rcases predecessor_cases vcfg hloc hstep with ⟨oid', rfl, h⟩ | ⟨oid', frame, -, rfl, h, -⟩ | ⟨rfl, -⟩
  · exact ⟨oid', rfl, .inl h⟩
  · exact ⟨oid', rfl, .inr ⟨_, h⟩⟩
  · exact (open_rid_no_step hlookup hopen hstep).elim

-- Closed-region analogue of `predecessor_of_region_object`: no stack predecessor (S3/L2), and the `RId` source is the portal hop.
theorem predecessor_of_closed_region_object {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid : RegionId} {region : Region} (hlookup : cfg.heap.lookup rid = some region)
    (hclosed : region.status = Status.Closed) {oid : ObjectId}
    (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn rid))
    {a : Reference} (hstep : ReachableStep cfg a (Reference.OId oid)) :
    (∃ oid', a = Reference.OId oid' ∧ (Reference.OId oid').loc? cfg = some (Location.Rgn rid)) ∨
      (a = Reference.RId rid ∧ oid = region.bridgeObjectId) := by
  rcases predecessor_cases vcfg hloc hstep with h | ⟨-, frame, hmem, -, -, hb⟩ | ⟨rfl, region', hl, -, rfl⟩
  · exact .inl h
  · obtain ⟨frame', hmem', hrid', -⟩ := vcfg.s3 frame hmem _ hb rid oid rfl hloc
    exact (closed_region_not_owned vcfg hlookup hclosed hmem' hrid').elim
  · rw [hlookup, Option.some_inj] at hl
    exact .inr ⟨rfl, hl ▸ rfl⟩

-- A predecessor of a stack-resident object is itself stack-resident (H3 rules out any region object pointing at the stack).
theorem predecessor_of_stack_object {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {oid : ObjectId} {fid : Index} (hloc : (Reference.OId oid).loc? cfg = some (Location.Stk fid))
    {a : Reference} (hstep : ReachableStep cfg a (Reference.OId oid)) :
    ∃ oid' fid', a = Reference.OId oid' ∧ (Reference.OId oid').loc? cfg = some (Location.Stk fid') := by
  cases a with
  | RId rid' => simp [(rid_step_inv vcfg hstep).1] at hloc
  | OId oid' =>
    rcases oid_step_container hstep with ⟨rid', region', -, hlk, hb⟩ | ⟨frame, -, hl, -⟩
    · simp [vcfg.h3 rid' oid region' hlk hb] at hloc
    · exact ⟨oid', _, rfl, hl⟩

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
  | RId _ => exact hsafe.elim
  | OId oid =>
    rcases hsafe with hloc | ⟨fid, hloc⟩
    · obtain ⟨oid', rfl, h⟩ := predecessor_of_region_object vcfg hlookup hopen hloc hstep
      exact h
    · obtain ⟨oid', fid', rfl, h⟩ := predecessor_of_stack_object vcfg hloc hstep
      exact .inr ⟨fid', h⟩

-- If OId-sourced steps agree between cfg/cfg', any cfg-chain reaching a safe reference transports to a cfg'-chain.
theorem safe_reflTransGen_transport {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid : RegionId} {region : Region} (hlookup : cfg.heap.lookup rid = some region)
    (hopen : region.status = Status.Open)
    (hoidstep : ∀ oid b, ReachableStep cfg (Reference.OId oid) b ↔ ReachableStep cfg' (Reference.OId oid) b)
    {start ref : Reference} (hrtg : Relation.ReflTransGen (ReachableStep cfg) start ref) :
    SafeRef cfg rid ref → Relation.ReflTransGen (ReachableStep cfg') start ref := by
  induction hrtg with
  | refl => exact fun _ => .refl
  | @tail prev cur _ hstep ih =>
    intro hsafe
    have hprev := predecessor_safe vcfg hlookup hopen hsafe hstep
    cases prev with
    | RId _ => exact hprev.elim
    | OId o => exact (ih hprev).tail ((hoidstep o cur).mp hstep)

-- Converse of `stackWithIndex_getElem_index_eq`: a member's own index recovers it via `[·]?`.
theorem stackWithIndex_mem_getElem_eq {cfg : RuntimeConfig} {frame : FrameWithIndex}
    (hmem : frame ∈ cfg.stackWithIndex) : cfg.stackWithIndex[frame.index]? = some frame := by
  obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp hmem
  simp [RuntimeConfig.stackWithIndex, hn]

-- Searching `stackWithIndex` by index is the same as direct indexing (indices are unique).
theorem stackWithIndex_find_index_eq_getElem {cfg : RuntimeConfig} (fid : Index) :
    cfg.stackWithIndex.find? (fun f => f.index == fid) = cfg.stackWithIndex[fid]? := by
  cases hget : cfg.stackWithIndex[fid]? with
  | none =>
    refine List.find?_eq_none.mpr fun fr hfr h => ?_
    simp [← beq_iff_eq.mp h, stackWithIndex_mem_getElem_eq hfr] at hget
  | some frame =>
    rw [← stackWithIndex_getElem_index_eq hget]
    exact swap_corollary_stackWithIndex_find_eq (List.mem_of_getElem? hget)

-- Anything reaching a stack-resident container at `fidC` roots from a frame with index `≥ fidC` (S2, chased backward via `stack_step_index_le`).
theorem stack_container_confined {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {fidC : Index} {oidC : ObjectId} (hlocC : (Reference.OId oidC).loc? cfg = some (Location.Stk fidC))
    {fid : Index} (hreach : FrameReachable cfg fid (Reference.OId oidC)) :
    fidC ≤ fid := by
  obtain ⟨start, hroot, hrtg⟩ := (FrameReachable_iff_reflTransGen _ _ _).mp hreach
  have hback : ∀ ref, Relation.ReflTransGen (ReachableStep cfg) start ref →
      ∀ oidR fidR, ref = Reference.OId oidR → (Reference.OId oidR).loc? cfg = some (Location.Stk fidR) →
        ∃ oidS fidS, start = Reference.OId oidS ∧ (Reference.OId oidS).loc? cfg = some (Location.Stk fidS) ∧
          fidR ≤ fidS := by
    intro ref h
    induction h with
    | refl => rintro oidR fidR rfl hloc; exact ⟨oidR, fidR, rfl, hloc, le_rfl⟩
    | tail _ hstep ih =>
      rintro oidR fidR rfl hloc
      obtain ⟨oidB, fidB, rfl, hlocB⟩ := predecessor_of_stack_object vcfg hloc hstep
      obtain ⟨oidS, fidS, hseq, hlocS, hle⟩ := ih oidB fidB rfl hlocB
      exact ⟨oidS, fidS, hseq, hlocS, (stack_step_index_le vcfg hlocB hstep hloc).trans hle⟩
  obtain ⟨oidS, fidS, rfl, hlocS, hle⟩ := hback _ hrtg oidC fidC rfl hlocC
  rcases hroot with ⟨frameR, hmem, rfl, var, hvar⟩ | ⟨frameR, -, -, regionR, hlk, hbr⟩
  · exact hle.trans (vcfg.s2 frameR hmem _ (mem_frame_refs_of_mem_varMap hvar) fidS oidS rfl hlocS)
  · cases hbr
    simp [bridge_loc vcfg hlk] at hlocS

-- S3 at the `ReachableStep` level: a stack-to-region hop's target region is owned by a frame with index ≤ the stack source's.
theorem stack_step_region_index_le {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {oid : ObjectId} {fidCur : Index} {oid' : ObjectId} {rid' : RegionId}
    (hloc : (Reference.OId oid).loc? cfg = some (Location.Stk fidCur))
    (hstep : ReachableStep cfg (Reference.OId oid) (Reference.OId oid'))
    (hloc' : (Reference.OId oid').loc? cfg = some (Location.Rgn rid')) :
    ∃ frame' ∈ cfg.stackWithIndex, frame'.regionId = rid' ∧ frame'.index ≤ fidCur := by
  rcases oid_step_container hstep with ⟨rid, -, hl, -⟩ | ⟨frame, hmem, hl, hb⟩
  · simp [hl] at hloc
  · obtain rfl : frame.index = fidCur := by simpa using hl.symm.trans hloc
    exact vcfg.s3 frame hmem _ hb rid' oid' rfl hloc'

-- Anything reaching an in-region container roots from a frame with index `≥` the region owner's (H3-driven, whether the chase stays in-region or escapes to the stack).
theorem region_container_confined {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid : RegionId} {region : Region} (hlookup : cfg.heap.lookup rid = some region) (hopen : region.status = Status.Open)
    {ownerFrame : FrameWithIndex} (hownerMem : ownerFrame ∈ cfg.stackWithIndex) (hownerRid : ownerFrame.regionId = rid)
    {oidC : ObjectId} (hlocC : (Reference.OId oidC).loc? cfg = some (Location.Rgn rid))
    {fid : Index} (hreach : FrameReachable cfg fid (Reference.OId oidC)) :
    ownerFrame.index ≤ fid := by
  obtain ⟨start, hroot, hrtg⟩ := (FrameReachable_iff_reflTransGen _ _ _).mp hreach
  have hown : ∀ {f : FrameWithIndex}, f ∈ cfg.stackWithIndex → f.regionId = rid → f.index = ownerFrame.index :=
    fun hf hr => merge_corollary_regionId_unique_index vcfg.s1 hf hownerMem (hr.trans hownerRid.symm)
  have hback : ∀ ref, Relation.ReflTransGen (ReachableStep cfg) start ref →
      ∀ oidR, ref = Reference.OId oidR → (Reference.OId oidR).loc? cfg = some (Location.Rgn rid) →
        (∃ oidS, start = Reference.OId oidS ∧ (Reference.OId oidS).loc? cfg = some (Location.Rgn rid)) ∨
        (∃ oidB fidB, Relation.ReflTransGen (ReachableStep cfg) start (Reference.OId oidB) ∧
          (Reference.OId oidB).loc? cfg = some (Location.Stk fidB) ∧ ownerFrame.index ≤ fidB) := by
    intro ref h
    induction h with
    | refl => rintro oidR rfl hloc; exact .inl ⟨oidR, rfl, hloc⟩
    | tail hprev hstep ih =>
      rintro oidR rfl hloc
      obtain ⟨oidB, rfl, hlocB | ⟨fidB, hlocB⟩⟩ := predecessor_of_region_object vcfg hlookup hopen hloc hstep
      · exact ih oidB rfl hlocB
      · obtain ⟨frame', hmem', hrid', hidx'⟩ := stack_step_region_index_le vcfg hlocB hstep hloc
        exact .inr ⟨oidB, fidB, hprev, hlocB, hown hmem' hrid' ▸ hidx'⟩
  rcases hback _ hrtg oidC rfl hlocC with ⟨oidS, rfl, hlocS⟩ | ⟨oidB, fidB, hprefixB, hlocB, hleB⟩
  · rcases hroot with ⟨frameR, hmem, rfl, var, hvar⟩ | ⟨frameR, hmem, rfl, regionR, hlk, hbr⟩
    · obtain ⟨frame', hmem', hrid', hidx'⟩ :=
        vcfg.s3 frameR hmem _ (mem_frame_refs_of_mem_varMap hvar) rid oidS rfl hlocS
      exact hown hmem' hrid' ▸ hidx'
    · cases hbr
      exact (hown hmem (by simpa using (bridge_loc vcfg hlk).symm.trans hlocS)).ge
  · exact hleB.trans (stack_container_confined vcfg hlocB
      ((FrameReachable_iff_reflTransGen _ _ _).mpr ⟨start, hroot, hprefixB⟩))

-- Extends a `FrameReachable` witness forward along any further `ReachableStep` chain.
theorem FrameReachable_extend {cfg : RuntimeConfig} {fid : Index} {x y : Reference}
    (hx : FrameReachable cfg fid x) (hxy : Relation.ReflTransGen (ReachableStep cfg) x y) :
    FrameReachable cfg fid y := by
  induction hxy with
  | refl => exact hx
  | tail _ hstep ih => exact .step hstep ih

-- Any root-to-object chain into a Closed region passes through the portal `RId rid` and is region-reachable.
theorem closed_chain {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid : RegionId} {region : Region} (hlookup : cfg.heap.lookup rid = some region)
    (hclosed : region.status = Status.Closed) {fid : Index} {start : Reference} (hroot : FrameRoot cfg fid start) :
    ∀ ref, Relation.ReflTransGen (ReachableStep cfg) start ref →
      ∀ oid, ref = Reference.OId oid → (Reference.OId oid).loc? cfg = some (Location.Rgn rid) →
        Relation.ReflTransGen (ReachableStep cfg) start (Reference.RId rid) ∧ RegionReachable cfg rid ref := by
  intro ref h
  induction h with
  | refl =>
    rintro oid rfl hloc
    exfalso
    rcases hroot with ⟨frame, hmem, -, var, hvar⟩ | ⟨frame, hmem, -, region2, hlk2, hstart⟩
    · obtain ⟨frame', hmem', hrid', -⟩ := vcfg.s3 frame hmem _ (mem_frame_refs_of_mem_varMap hvar) rid oid rfl hloc
      exact closed_region_not_owned vcfg hlookup hclosed hmem' hrid'
    · cases hstart
      exact closed_region_not_owned vcfg hlookup hclosed hmem (by simpa using (bridge_loc vcfg hlk2).symm.trans hloc)
  | tail hprev hstep ih =>
    rintro oid rfl hloc
    rcases predecessor_of_closed_region_object vcfg hlookup hclosed hloc hstep with
      ⟨oid', rfl, hloc'⟩ | ⟨rfl, rfl⟩
    · exact (ih oid' rfl hloc').imp_right (.step hstep)
    · exact ⟨hprev, .bridge hlookup rfl⟩

-- Closed-region confinement, the key CR6 ingredient: any way of reaching an object inside a Closed region factors through its bridge object.
theorem RegionReachable_of_FrameReachable_closed {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid : RegionId} {region : Region} (hlookup : cfg.heap.lookup rid = some region)
    (hclosed : region.status = Status.Closed)
    {fid : Index} {oid : ObjectId} (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn rid))
    (hreach : FrameReachable cfg fid (Reference.OId oid)) :
    RegionReachable cfg rid (Reference.OId oid) := by
  obtain ⟨start, hroot, hrtg⟩ := (FrameReachable_iff_reflTransGen _ _ _).mp hreach
  exact (closed_chain vcfg hlookup hclosed hroot _ hrtg oid rfl hloc).2

-- Reaching an object inside a Closed region forces the region's own `RId` to already be frame-reachable.
theorem FrameReachable_rid_of_closed_container {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {rid : RegionId} {region : Region} (hlookup : cfg.heap.lookup rid = some region)
    (hclosed : region.status = Status.Closed)
    {fid : Index} {oid : ObjectId} (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn rid))
    (hreach : FrameReachable cfg fid (Reference.OId oid)) :
    FrameReachable cfg fid (Reference.RId rid) := by
  obtain ⟨start, hroot, hrtg⟩ := (FrameReachable_iff_reflTransGen _ _ _).mp hreach
  exact (FrameReachable_iff_reflTransGen _ _ _).mpr
    ⟨start, hroot, (closed_chain vcfg hlookup hclosed hroot _ hrtg oid rfl hloc).1⟩

-- The stack's own last frame, reindexed as a `FrameWithIndex`, is a member of `stackWithIndex`.
theorem stackWithIndex_getLast_mem {cfg : RuntimeConfig} {lastFrame : Frame}
    (hlast : cfg.stack.getLast? = some lastFrame) :
    ({ lastFrame with index := cfg.stack.length - 1 } : FrameWithIndex) ∈ cfg.stackWithIndex := by
  simp [stackWithIndex_eq_of_getLast? hlast]

-- A frame strictly before the last one has a different regionId from the last frame's own (S1).
theorem regionId_ne_last_of_suspended {cfg : RuntimeConfig} (vcfg : ValidConfig cfg)
    {f : FrameWithIndex} (hf : f ∈ cfg.stackWithIndex) (hflt : f.index < cfg.stack.length - 1)
    {lastFrame : Frame} (hlast : cfg.stack.getLast? = some lastFrame) :
    f.regionId ≠ lastFrame.regionId := fun heq => by
  have := merge_corollary_regionId_unique_index vcfg.s1 hf (stackWithIndex_getLast_mem hlast) heq
  simp only at this
  exact lt_irrefl _ (this ▸ hflt)
