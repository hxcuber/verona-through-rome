module

public import Gc.Model.Helpers
public import Mathlib.Data.List.Pairwise

@[expose] public section

def L1 (cfg : RuntimeConfig) : Prop :=
  cfg.objectIds.Nodup

def L2 (cfg : RuntimeConfig) : Prop :=
  ∀ frame ∈ cfg.stack, ∃ region,
    cfg.heap.lookup frame.regionId = some region ∧
    region.status = Status.Open

def H1 (cfg : RuntimeConfig) : Prop :=
  ∀ region ∈ cfg.heap.regions,
    region.bridgeObjectId ∈ region.objMap

def H2 (cfg : RuntimeConfig) : Prop :=
  ∀ rid,
    (cfg.stack.refs.count (Reference.RId rid))
    + (cfg.heap.refs.count (Reference.RId rid)) ≤ 1

def H3 (cfg : RuntimeConfig) : Prop :=
  ∀ rid oid region,
    cfg.heap.lookup rid = some region →
    (Reference.OId oid) ∈ region.refs →
    (Reference.OId oid).loc? cfg = some (Location.Rgn rid)

def S1 (cfg : RuntimeConfig) : Prop :=
  (cfg.stack.map (λ frame => frame.regionId)).Nodup

def S2 (cfg : RuntimeConfig) : Prop :=
  ∀ frame ∈ cfg.stackWithIndex, ∀ ref ∈ frame.refs, ∀ fid' oid,
    ref = Reference.OId oid →
    ref.loc? cfg = some (Location.Stk fid') →
    fid' <= frame.index

def S3 (cfg : RuntimeConfig) : Prop :=
  ∀ frame ∈ cfg.stackWithIndex, ∀ ref ∈ frame.refs, ∀ rid' oid,
    ref = Reference.OId oid →
    ref.loc? cfg = some (Location.Rgn rid') →
    ∃ frame' ∈ cfg.stackWithIndex,
      frame'.regionId = rid' ∧ frame'.index <= frame.index

def HS1 (cfg : RuntimeConfig) : Prop :=
  ∀ oid, Reference.OId oid ∈ cfg.refs → oid ∈ cfg.objectIds

def HS2 (cfg : RuntimeConfig) : Prop :=
  ∀ rid, Reference.RId rid ∈ cfg.refs → rid ∈ cfg.heap.keys

structure ValidConfig (cfg : RuntimeConfig) where
  l1 : L1 cfg
  l2 : L2 cfg
  h1 : H1 cfg
  h2 : H2 cfg
  h3 : H3 cfg
  s1 : S1 cfg
  s2 : S2 cfg
  s3 : S3 cfg
  hs1 : HS1 cfg
  hs2 : HS2 cfg

private theorem stack_objectIds_eq (stack : Stack) :
    stack.objectIds = (stack.map Frame.objectIds).flatten := by
  simp [Stack.objectIds, List.flatMap_id]

private theorem mem_stack_objectIds_of_findRev {cfg : RuntimeConfig} {oid : ObjectId} {frame : FrameWithIndex}
    (h : cfg.stackWithIndex.findRev? (λ f => f.objMap.keys.contains oid) = some frame) :
    oid ∈ cfg.stack.objectIds := by
  rw [List.findRev?_eq_find?_reverse] at h
  obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp (List.mem_reverse.mp (List.mem_of_find?_eq_some h))
  have := List.find?_some h
  simp only [List.contains_iff_mem] at this
  rw [stack_objectIds_eq]
  exact List.mem_flatten.mpr ⟨_, List.mem_map_of_mem (List.getElem_mem hn), this⟩

private theorem mem_heap_objectIds_of_find {cfg : RuntimeConfig} {oid : ObjectId} {rid : RegionId} {region : Region}
    (h : cfg.heap.entries.find? (λ ⟨_, region⟩ => region.objMap.keys.contains oid) = some ⟨rid, region⟩) :
    oid ∈ cfg.heap.objectIds := by
  have := List.find?_some h
  simp only [List.contains_iff_mem] at this
  exact List.mem_flatten.mpr ⟨_, List.mem_map_of_mem (List.mem_of_find?_eq_some h), this⟩

private theorem not_mem_stack_or_heap_objectIds {cfg : RuntimeConfig} {oid : ObjectId} (v : ValidConfig cfg) :
    oid ∈ cfg.stack.objectIds → oid ∈ cfg.heap.objectIds → False :=
  fun hs hh => (List.nodup_append.mp v.l1).2.2 oid hs oid hh rfl

theorem oid_in_stack_implies_not_in_heap : ValidConfig cfg →
  cfg.stackWithIndex.findRev? (λ frame => frame.objMap.keys.contains oid) = some frame →
  cfg.heap.entries.find? (λ ⟨_, region⟩ => region.objMap.keys.contains oid) = none := by
  intro vcfg h
  by_contra hne
  obtain ⟨⟨rid, region⟩, hp⟩ := Option.ne_none_iff_exists'.mp hne
  exact not_mem_stack_or_heap_objectIds vcfg (mem_stack_objectIds_of_findRev h) (mem_heap_objectIds_of_find hp)

theorem oid_in_heap_implies_not_in_stack : ValidConfig cfg →
  cfg.heap.entries.find? (λ ⟨_, region⟩ => region.objMap.keys.contains oid) = some ⟨rid, region⟩ →
  cfg.stackWithIndex.findRev? (λ frame => frame.objMap.keys.contains oid) = none := by
  intro vcfg h
  by_contra hne
  obtain ⟨frame, hp⟩ := Option.ne_none_iff_exists'.mp hne
  exact not_mem_stack_or_heap_objectIds vcfg (mem_stack_objectIds_of_findRev hp) (mem_heap_objectIds_of_find h)

theorem oid_loc_rgn_iff_in_heap : ValidConfig cfg →
  ((Reference.OId oid).loc? cfg = some (Location.Rgn rid) ↔
  ∃ region, cfg.heap.lookup rid = some region ∧ oid ∈ region.objMap) := by
  intro vcfg
  constructor
  · intro h
    simp only [Reference.loc?] at h
    split at h <;> simp at h
    rename_i rid' region' _ hfind
    subst h
    have := List.find?_some hfind
    simp only [List.contains_iff_mem] at this
    exact ⟨region', AList.mem_lookup_iff.mpr (List.mem_of_find?_eq_some hfind), AList.mem_keys.mp this⟩
  · rintro ⟨region, hlk, hoid⟩
    have hk : oid ∈ region.objMap.keys := AList.mem_keys.mpr hoid
    have hfind : cfg.heap.entries.find? (λ ⟨_, region⟩ => region.objMap.keys.contains oid) = some ⟨rid, region⟩ := by
      refine List.find?_eq_some_of_unique (AList.mem_lookup_iff.mp hlk) (by simpa using hk) ?_
      rintro ⟨rid2, r2⟩ hm hc
      have hnd := (List.nodup_append.mp vcfg.l1).2.1
      simp only [List.contains_iff_mem] at hc
      exact List.eq_of_mem_flatten_map_nodup hnd hm (AList.mem_lookup_iff.mp hlk) (a := oid) hc hk
    unfold Reference.loc?
    dsimp
    rw [hfind, oid_in_heap_implies_not_in_stack vcfg hfind]

private theorem findRev_eq_of_getElem {cfg : RuntimeConfig} (vcfg : ValidConfig cfg) {oid : ObjectId} {i : Nat}
    (hi : i < cfg.stack.length) (hoid : oid ∈ cfg.stack[i].objMap.keys) :
    cfg.stackWithIndex.findRev? (λ f => f.objMap.keys.contains oid) = some ⟨cfg.stack[i], i⟩ := by
  rw [List.findRev?_eq_find?_reverse]
  refine List.find?_eq_some_of_unique ?_ (by simpa using hoid) ?_
  · exact List.mem_reverse.mpr (List.mem_mapIdx.mpr ⟨i, hi, rfl⟩)
  · intro x hx hc
    obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp (List.mem_reverse.mp hx)
    simp only [List.contains_iff_mem] at hc
    have hnd := (List.nodup_append.mp vcfg.l1).1
    rw [stack_objectIds_eq] at hnd
    cases List.index_eq_of_mem_flatten_map_nodup hnd hn hi (a := oid) hc hoid
    rfl

theorem oid_loc_stk_iff_in_stack : ValidConfig cfg →
  ((Reference.OId oid).loc? cfg = some (Location.Stk fid) ↔
  ∃ frame, cfg.stackWithIndex[fid]? = some frame ∧ oid ∈ frame.objMap) := by
  intro vcfg
  constructor
  · intro h
    simp only [Reference.loc?] at h
    split at h
    · rename_i f hs _
      simp only [Option.some.injEq, Location.Stk.injEq] at h
      subst h
      have hc := List.find?_some (List.findRev?_eq_find?_reverse .. ▸ hs)
      simp only [List.contains_iff_mem] at hc
      obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp
        (List.mem_reverse.mp (List.mem_of_find?_eq_some (List.findRev?_eq_find?_reverse .. ▸ hs)))
      exact ⟨_, by simp [RuntimeConfig.stackWithIndex, hn], AList.mem_keys.mp hc⟩
    all_goals simp at h
  · rintro ⟨frame, hf, hoid⟩
    simp only [RuntimeConfig.stackWithIndex, List.getElem?_mapIdx, Option.map_eq_some_iff] at hf
    obtain ⟨f, hf, rfl⟩ := hf
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hf
    have hfind := findRev_eq_of_getElem vcfg hi (AList.mem_keys.mpr hoid)
    simp only [Reference.loc?]
    rw [hfind, oid_in_stack_implies_not_in_heap vcfg hfind]
