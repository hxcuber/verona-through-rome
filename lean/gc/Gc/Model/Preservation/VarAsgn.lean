module

public import Gc.Model.Types
public import Gc.Model.Helpers
public import Gc.Model.Validity
public import Gc.Model.Theorems
public import Gc.Model.Mutation.VarAsgn
public import Gc.Model.Preservation.Common

public import Mathlib.Data.List.Infix

@[expose] public section

-- A stackWithIndex frame's index is below the stack length.
private theorem swi_index_lt {cfg : RuntimeConfig} {f : FrameWithIndex} (hf : f ∈ cfg.stackWithIndex) :
    f.index < cfg.stack.length := by
  obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp hf
  exact hn

-- Inserting a fresh variable adds exactly its value to the frame's refs.
private theorem newFrame_refs_perm {frame : Frame} {x : VarName} {v : Reference} (hx : x ∉ frame.varMap.keys) :
    (Frame.refs { frame with varMap := frame.varMap.insert x v }).Perm (v :: frame.refs) := by
  simp only [Frame.refs, AList.entries_insert, List.kerase_of_notMem_keys hx, List.map_cons]
  exact List.perm_middle

-- Inserting a region with the same objMap at an existing heap key preserves every loc?.
private theorem heap_insert_loc_eq {cfg : RuntimeConfig} {rid : RegionId} {region newRegion : Region}
    (l1 : L1 cfg) (hregion : cfg.heap.lookup rid = some region) (hobj : newRegion.objMap = region.objMap)
    (oid' : ObjectId) :
    (Reference.OId oid').loc? { cfg with heap := cfg.heap.insert rid newRegion } = (Reference.OId oid').loc? cfg := by
  obtain ⟨region2, l1e, l2e, -, heq, hkerase⟩ := List.exists_of_kerase (AList.mem_keys_of_lookup_eq_some hregion)
  have hmem : (⟨rid, region⟩ : Sigma (fun _ : RegionId => Region)) ∈ cfg.heap.entries :=
    AList.lookup_mem_entries hregion
  have := List.NodupKeys.eq_of_mk_mem cfg.heap.nodupKeys (heq ▸ List.mem_append_right _ List.mem_cons_self) hmem
  subst region2
  have hfind : ((cfg.heap.insert rid newRegion).entries.find? (fun p => p.2.objMap.keys.contains oid')).map
      Sigma.fst = (cfg.heap.entries.find? (fun p => p.2.objMap.keys.contains oid')).map Sigma.fst := by
    rw [AList.entries_insert, hkerase]
    by_cases hb : region.objMap.keys.contains oid'
    · rw [List.find?_eq_some_of_unique hmem hb fun ⟨r, g⟩ hy hp => by
        obtain rfl := heap_region_unique l1 hy (List.contains_iff_mem.mp hp) hmem (List.contains_iff_mem.mp hb)
        rw [List.NodupKeys.eq_of_mk_mem cfg.heap.nodupKeys hy hmem]]
      simp [hobj, show oid' ∈ region.objMap.keys by simpa using hb]
    · rw [heq]
      simp [List.find?_append, hobj, show oid' ∉ region.objMap.keys by simpa using hb]
  have h1 := loc_match_eq (cfg.stackWithIndex.findRev? (fun f => f.objMap.keys.contains oid'))
    ((cfg.heap.insert rid newRegion).entries.find? (fun p => p.2.objMap.keys.contains oid'))
  rw [hfind, ← loc_match_eq] at h1
  exact h1

-- `resolveV xf cfg = none` means the last frame's varMap doesn't contain xf.
theorem varAsgn_corollary_fresh_not_in_frame {cfg : RuntimeConfig} {frame : Frame} {xf : VarName}
    (hframe : cfg.stack.getLast? = some frame) (hresolve : resolveV xf cfg = none) :
    xf ∉ frame.varMap.keys := by
  intro hmem
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr (AList.mem_keys.mpr hmem))
  simp [resolveV, stackWithIndex_eq_of_getLast? hframe, List.findRev?_eq_find?_reverse, hmem, hv] at hresolve

-- A resolved field value is stored in a stack frame, or in a heap region holding the resolved root object.
private theorem resolveFA_mem {cfg : RuntimeConfig} {y : FieldAccess} {r : Reference}
    (h : resolveFA y cfg = some r) :
    ∃ oid0, resolveV y.root cfg = some (.OId oid0) ∧ ((∃ f ∈ cfg.stackWithIndex, r ∈ f.refs) ∨
      ∃ rid0 region0, (Reference.OId oid0).loc? cfg = some (.Rgn rid0) ∧ cfg.heap.lookup rid0 = some region0 ∧
        r ∈ region0.refs) := by
  unfold resolveFA at h
  rcases hrv : resolveV y.root cfg with _ | _ | oid0 <;> simp [hrv] at h
  refine ⟨oid0, rfl, ?_⟩
  rcases hloc : (Reference.OId oid0).loc? cfg with _ | _ | rid0 <;> simp [hloc] at h
  · obtain ⟨region0, hreg, obj, hobj, hf⟩ := by simpa only [Option.bind_eq_some_iff] using h
    exact Or.inr ⟨_, region0, rfl, hreg,
      objMap_bind_refs_mem_of_lookup hobj (List.mem_map_of_mem (AList.lookup_mem_entries hf))⟩
  · obtain ⟨f, hfind, obj, hobj, hf⟩ := by simpa only [Option.bind_eq_some_iff] using h
    exact Or.inl ⟨f, List.mem_of_find?_eq_some hfind,
      List.mem_append_left _ (objMap_bind_refs_mem_of_lookup hobj (List.mem_map_of_mem (AList.lookup_mem_entries hf)))⟩

-- A successfully resolved field value is already stored in cfg.
private theorem resolveFA_refs_mem {cfg : RuntimeConfig} {y : FieldAccess} {r : Reference}
    (h : resolveFA y cfg = some r) : r ∈ cfg.refs := by
  obtain ⟨_, -, ⟨f, hf, hr⟩ | ⟨_, _, -, hreg, hr⟩⟩ := resolveFA_mem h
  · exact refs_mem_of_stackWithIndex hf hr
  · exact List.mem_append_right _ (heap_refs_mem_of_lookup hreg hr)

-- An object in region rid0 named by a variable already has an owning frame on the stack.
theorem varAsgn_corollary_resolveV_loc_ancestor {cfg : RuntimeConfig} {var : VarName} {oid0 : ObjectId}
    (vcfg : ValidConfig cfg) (hrv : resolveV var cfg = some (Reference.OId oid0)) (rid0 : RegionId)
    (hloc0 : (Reference.OId oid0).loc? cfg = some (Location.Rgn rid0)) :
    ∃ frame'' ∈ cfg.stackWithIndex, frame''.regionId = rid0 ∧ frame''.index < cfg.stack.length := by
  simp [resolveV, Option.bind_eq_some_iff] at hrv
  obtain ⟨frameV, hfV, hrv⟩ := hrv
  have hmem : frameV ∈ cfg.stackWithIndex := List.mem_reverse.mp (List.mem_of_find?_eq_some hfV)
  rcases hrv with hlk | ⟨-, -, regionV, hregV, rfl⟩
  · obtain ⟨g, hg, hgr, hgi⟩ := vcfg.s3 frameV hmem _
      (List.mem_append_right _ (List.mem_map_of_mem (AList.lookup_mem_entries hlk))) rid0 oid0 rfl hloc0
    exact ⟨g, hg, hgr, hgi.trans_lt (swi_index_lt hmem)⟩
  · have := (oid_loc_rgn_iff_in_heap vcfg).mpr
      ⟨regionV, hregV, vcfg.h1 regionV (List.mem_map_of_mem (AList.lookup_mem_entries hregV))⟩
    rw [hloc0] at this
    cases this
    exact ⟨frameV, hmem, rfl, swi_index_lt hmem⟩

-- A resolved field value located in region rid' already has an owning frame on the stack.
private theorem resolveFA_loc_ancestor {cfg : RuntimeConfig} {y : FieldAccess} {oid : ObjectId}
    (vcfg : ValidConfig cfg) (hyf : resolveFA y cfg = some (Reference.OId oid)) {rid' : RegionId}
    (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn rid')) :
    ∃ frame'' ∈ cfg.stackWithIndex, frame''.regionId = rid' ∧ frame''.index < cfg.stack.length := by
  obtain ⟨oid0, hrv, ⟨f, hf, hr⟩ | ⟨rid0, reg0, hloc0, hreg, hr⟩⟩ := resolveFA_mem hyf
  · obtain ⟨g, hg, hgr, hgi⟩ := vcfg.s3 f hf _ hr rid' oid rfl hloc
    exact ⟨g, hg, hgr, hgi.trans_lt (swi_index_lt hf)⟩
  · have := vcfg.h3 rid0 oid reg0 hreg hr
    rw [hloc] at this
    cases this
    exact varAsgn_corollary_resolveV_loc_ancestor vcfg hrv rid' hloc0

-- varAsgn preserves every object's location.
theorem varAsgn_corollary_loc_eq : ValidConfig cfg →
  varAsgn xf y cfg = some cfg' →
  ∀ oid', (Reference.OId oid').loc? cfg = (Reference.OId oid').loc? cfg' := by
  intro vcfg h oid'
  obtain ⟨frame, hframe, ⟨oid, rid, region, -, -, -, -, hregion, rfl⟩ | ⟨oid, -, -, -, rfl⟩⟩ := varAsgn_cases h
  · exact (heap_insert_loc_eq (newRegion := { region with bridgeObjectId := oid }) vcfg.l1 hregion rfl oid').symm
  · simp only [Reference.loc?]
    rw [stackWithIndex_eq_of_getLast? hframe, stackWithIndex_mk_append_singleton]
    simp only [List.findRev?_eq_find?_reverse, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.find?_cons]
    cases frame.objMap.keys.contains oid' <;> cases cfg.heap.entries.find? (fun x => x.2.objMap.keys.contains oid') <;>
      rfl

-- cfg'.objectIds is a permutation of cfg.objectIds.
private theorem objectIds_perm (h : varAsgn xf y cfg = some cfg') : cfg'.objectIds.Perm cfg.objectIds := by
  obtain ⟨frame, hframe, ⟨oid, rid, region, -, -, -, -, hregion, rfl⟩ | ⟨oid, -, -, -, rfl⟩⟩ := varAsgn_cases h
  · exact (heap_insert_objectIds_perm hregion (List.Perm.refl _)).append_left _
  · unfold RuntimeConfig.objectIds
    conv_rhs => rw [← List.dropLast_append_getLast? frame hframe]
    simp [Stack.objectIds, Frame.objectIds]

-- Every ref stored after varAsgn was already stored.
private theorem refs_mem (h : varAsgn xf y cfg = some cfg') {r : Reference} (hr : r ∈ cfg'.refs) :
    r ∈ cfg.refs := by
  obtain ⟨frame, hframe, ⟨oid, rid, region, -, -, -, -, hregion, rfl⟩ | ⟨oid, hyf, -, hres, rfl⟩⟩ :=
    varAsgn_cases h
  · rcases List.mem_append.mp hr with hs | hh
    · exact List.mem_append_left _ hs
    · exact List.mem_append_right _ ((heap_insert_refs_mem (AList.mem_keys_of_lookup_eq_some hregion) hh).elim
        (fun hr => heap_refs_mem_of_lookup hregion hr) id)
  · simp only [RuntimeConfig.refs, stack_refs_append_singleton, List.mem_append] at hr
    rcases hr with (hd | hn) | hh
    · exact List.mem_append_left _ (by
        rw [← List.dropLast_append_getLast? frame hframe, stack_refs_append_singleton]
        exact List.mem_append_left _ hd)
    · rcases List.mem_cons.mp ((newFrame_refs_perm (varAsgn_corollary_fresh_not_in_frame hframe hres)).mem_iff.mp hn)
        with rfl | hn
      · exact resolveFA_refs_mem hyf
      · exact List.mem_append_left _ (stack_refs_mem (List.mem_of_getLast? hframe) hn)
    · exact List.mem_append_right _ hh

-- Each new frame has an old counterpart with the same index and region covering its refs, bar the resolved value on top.
private theorem swi_down (h : varAsgn xf y cfg = some cfg') {f' : FrameWithIndex}
    (hf' : f' ∈ cfg'.stackWithIndex) :
    ∃ f ∈ cfg.stackWithIndex, f.index = f'.index ∧ f.regionId = f'.regionId ∧
      ∀ r ∈ f'.refs, r ∈ f.refs ∨ (resolveFA y cfg = some r ∧ cfg.stack.length ≤ f'.index + 1) := by
  obtain ⟨frame, hframe, ⟨_, _, _, -, -, -, -, -, rfl⟩ | ⟨oid, hyf, -, hres, rfl⟩⟩ := varAsgn_cases h
  · exact ⟨f', hf', rfl, rfl, fun r hr => Or.inl hr⟩
  · rw [stackWithIndex_eq_of_getLast? hframe]
    rw [stackWithIndex_mk_append_singleton] at hf'
    rcases List.mem_append.mp hf' with hd | hl
    · exact ⟨f', List.mem_append_left _ hd, rfl, rfl, fun r hr => Or.inl hr⟩
    · obtain rfl := List.mem_singleton.mp hl
      refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl, fun r hr => ?_⟩
      rcases List.mem_cons.mp ((newFrame_refs_perm (varAsgn_corollary_fresh_not_in_frame hframe hres)).mem_iff.mp hr)
        with rfl | hr
      · exact Or.inr ⟨hyf, by
        simpa using (Nat.sub_add_cancel (List.length_pos_of_mem (List.mem_of_getLast? hframe))).ge⟩
      · exact Or.inl hr

-- Each old frame has a counterpart after varAsgn with the same index and region.
private theorem swi_up (h : varAsgn xf y cfg = some cfg') {f : FrameWithIndex} (hf : f ∈ cfg.stackWithIndex) :
    ∃ f' ∈ cfg'.stackWithIndex, f'.index = f.index ∧ f'.regionId = f.regionId := by
  obtain ⟨frame, hframe, ⟨_, _, _, -, -, -, -, -, rfl⟩ | ⟨_, -, -, -, rfl⟩⟩ := varAsgn_cases h
  · exact ⟨f, hf, rfl, rfl⟩
  · rw [stackWithIndex_eq_of_getLast? hframe] at hf
    rw [stackWithIndex_mk_append_singleton]
    rcases List.mem_append.mp hf with hd | hl
    · exact ⟨f, List.mem_append_left _ hd, rfl, rfl⟩
    · obtain rfl := List.mem_singleton.mp hl
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl⟩

theorem varAsgn_L1 : ValidConfig cfg →
  varAsgn xf y cfg = some cfg' →
  L1 cfg' := fun vcfg h => vcfg.l1.perm (objectIds_perm h).symm

theorem varAsgn_L2 : ValidConfig cfg →
  varAsgn xf y cfg = some cfg' →
  L2 cfg' := by
  intro vcfg h f hf
  obtain ⟨frame, hframe, ⟨oid, rid, region, -, -, -, -, hregion, rfl⟩ | ⟨_, -, -, -, rfl⟩⟩ := varAsgn_cases h
  · obtain ⟨r0, hl, ho⟩ := vcfg.l2 f hf
    by_cases heq : f.regionId = rid
    · subst heq
      exact ⟨{ region with bridgeObjectId := oid }, by simp,
        Option.some_inj.mp (hl.symm.trans hregion) ▸ ho⟩
    · exact ⟨r0, by rwa [AList.lookup_insert_ne heq], ho⟩
  · rcases List.mem_append.mp hf with hd | hl
    · exact vcfg.l2 f (List.mem_of_mem_dropLast hd)
    · obtain rfl := List.mem_singleton.mp hl
      exact vcfg.l2 frame (List.mem_of_getLast? hframe)

theorem varAsgn_H1 : ValidConfig cfg →
  varAsgn xf y cfg = some cfg' →
  H1 cfg' := by
  intro vcfg h
  obtain ⟨frame, -, ⟨oid, rid, region, -, -, hloc, -, hregion, rfl⟩ | ⟨_, -, -, -, rfl⟩⟩ := varAsgn_cases h
  · intro r hr
    unfold Heap.regions at hr
    rw [AList.entries_insert, List.map_cons, List.mem_cons] at hr
    rcases hr with rfl | hr
    · obtain ⟨_, hl, hm⟩ := (oid_loc_rgn_iff_in_heap vcfg).mp hloc
      obtain rfl := Option.some_inj.mp (hl.symm.trans hregion)
      exact hm
    · exact vcfg.h1 r (((List.kerase_sublist rid _).map _).mem hr)
  · exact vcfg.h1

theorem varAsgn_H2 : ValidConfig cfg →
  varAsgn xf y cfg = some cfg' →
  H2 cfg' := by
  intro vcfg h rid'
  obtain ⟨frame, hframe, ⟨oid, rid, region, -, -, -, -, hregion, rfl⟩ | ⟨oid, -, -, hres, rfl⟩⟩ :=
    varAsgn_cases h
  · exact (heap_insert_refs_perm hregion rfl).count_eq _ ▸ vcfg.h2 rid'
  · have := vcfg.h2 rid'
    rw [← List.dropLast_append_getLast? frame hframe, stack_refs_append_singleton, List.count_append] at this
    dsimp only
    rw [stack_refs_append_singleton, List.count_append,
      (newFrame_refs_perm (varAsgn_corollary_fresh_not_in_frame hframe hres)).count_eq, List.count_cons]
    simpa using this

theorem varAsgn_H3 : ValidConfig cfg →
  varAsgn xf y cfg = some cfg' →
  H3 cfg' := by
  intro vcfg h rid0 oid0 reg hreg hr
  rw [← varAsgn_corollary_loc_eq vcfg h]
  obtain ⟨frame, -, ⟨oid, rid, region, -, -, -, -, hregion, rfl⟩ | ⟨_, -, -, -, rfl⟩⟩ := varAsgn_cases h
  · by_cases he : rid0 = rid
    · subst he
      obtain rfl : _ = reg := Option.some_inj.mp ((AList.lookup_insert cfg.heap).symm.trans hreg)
      exact vcfg.h3 _ _ region hregion hr
    · exact vcfg.h3 _ _ reg (by rwa [AList.lookup_insert_ne he] at hreg) hr
  · exact vcfg.h3 _ _ reg hreg hr

theorem varAsgn_S1 : ValidConfig cfg →
  varAsgn xf y cfg = some cfg' →
  S1 cfg' := by
  intro vcfg h
  obtain ⟨frame, hframe, ⟨_, _, _, -, -, -, -, -, rfl⟩ | ⟨_, -, -, -, rfl⟩⟩ := varAsgn_cases h
  · exact vcfg.s1
  · have := vcfg.s1
    rw [S1, ← List.dropLast_append_getLast? frame hframe] at this
    simpa [S1] using this

theorem varAsgn_S2 : ValidConfig cfg →
  varAsgn xf y cfg = some cfg' →
  S2 cfg' := by
  intro vcfg h f' hf' r hr fid oid0 hreq hloc
  subst hreq
  rw [← varAsgn_corollary_loc_eq vcfg h] at hloc
  obtain ⟨f, hf, hidx, -, hrefs⟩ := swi_down h hf'
  rcases hrefs _ hr with hr | ⟨-, hlen⟩
  · exact hidx ▸ vcfg.s2 f hf _ hr fid oid0 rfl hloc
  · obtain ⟨g, hg, -⟩ := (oid_loc_stk_iff_in_stack vcfg).mp hloc
    have := (List.getElem?_eq_some_iff.mp hg).1
    simp only [RuntimeConfig.stackWithIndex, List.length_mapIdx] at this
    exact Nat.le_of_lt_succ (this.trans_le hlen)

theorem varAsgn_S3 : ValidConfig cfg →
  varAsgn xf y cfg = some cfg' →
  S3 cfg' := by
  intro vcfg h f' hf' r hr rid' oid0 hreq hloc
  subst hreq
  rw [← varAsgn_corollary_loc_eq vcfg h] at hloc
  obtain ⟨f, hf, hidx, -, hrefs⟩ := swi_down h hf'
  rcases hrefs _ hr with hr | ⟨hyf, hlen⟩
  · obtain ⟨g, hg, hgr, hgi⟩ := vcfg.s3 f hf _ hr rid' oid0 rfl hloc
    obtain ⟨g', hg', hgi', hgr'⟩ := swi_up h hg
    exact ⟨g', hg', hgr'.trans hgr, hgi'.trans_le (hidx ▸ hgi)⟩
  · obtain ⟨g, hg, hgr, hgi⟩ := resolveFA_loc_ancestor vcfg hyf hloc
    obtain ⟨g', hg', hgi', hgr'⟩ := swi_up h hg
    exact ⟨g', hg', hgr'.trans hgr, hgi' ▸ Nat.le_of_lt_succ (hgi.trans_le hlen)⟩

theorem varAsgn_HS1 : ValidConfig cfg →
  varAsgn xf y cfg = some cfg' →
  HS1 cfg' := fun vcfg h oid hmem => (objectIds_perm h).mem_iff.mpr (vcfg.hs1 oid (refs_mem h hmem))

theorem varAsgn_HS2 : ValidConfig cfg →
  varAsgn xf y cfg = some cfg' →
  HS2 cfg' := by
  intro vcfg h rid hmem
  have := vcfg.hs2 rid (refs_mem h hmem)
  obtain ⟨frame, -, ⟨oid, rid0, region, -, -, -, -, hregion, rfl⟩ | ⟨_, -, -, -, rfl⟩⟩ := varAsgn_cases h
  · exact (heap_insert_keys_mem (AList.mem_keys_of_lookup_eq_some hregion) rid).mpr this
  · exact this

theorem varAsgn_valid : ValidConfig cfg →
  varAsgn xf y cfg = some cfg' →
  ValidConfig cfg' := by
  intro vcfg h
  exact {
    l1 := varAsgn_L1 vcfg h,
    l2 := varAsgn_L2 vcfg h,
    h1 := varAsgn_H1 vcfg h,
    h2 := varAsgn_H2 vcfg h,
    h3 := varAsgn_H3 vcfg h,
    s1 := varAsgn_S1 vcfg h,
    s2 := varAsgn_S2 vcfg h,
    s3 := varAsgn_S3 vcfg h,
    hs1 := varAsgn_HS1 vcfg h,
    hs2 := varAsgn_HS2 vcfg h
  }
