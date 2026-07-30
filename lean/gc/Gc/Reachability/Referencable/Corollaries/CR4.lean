import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Preservation.Common
import Gc.Reachability.Referencable.Semantics
import Gc.Reachability.Referencable.Validity.Reachable
import Gc.Reachability.Referencable.Corollaries.Common

-- Unpacks a `Rgn`-located `objAt?` success into the concrete region and objMap lookup witnessing
-- it -- used to line up two `Rgn`-located objects against the *same* region record before
-- invoking `two_oid_fields_mem_heap_refs`.
private theorem oid_region_lookup (cfg : RuntimeConfig) (oid : ObjectId) (rid : RegionId) (obj : Object)
    (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn rid))
    (hobjAt : (Reference.OId oid).objAt? cfg = some obj) :
    ∃ region, cfg.heap.lookup rid = some region ∧ region.objMap.lookup oid = some obj := by
  dsimp only [Reference.objAt?] at hobjAt
  rw [hloc] at hobjAt
  dsimp only at hobjAt
  cases hlookup : cfg.heap.lookup rid with
  | none => rw [hlookup] at hobjAt; simp at hobjAt
  | some region =>
    rw [hlookup] at hobjAt
    dsimp at hobjAt
    exact ⟨region, rfl, hobjAt⟩

-- An object already stored at some key of a region's objMap already contributes its own field
-- values to the whole region's refs.
private theorem objMap_lookup_mem_region_refs (region : Region) (oid : ObjectId) (obj : Object)
    (hobj : region.objMap.lookup oid = some obj) (r : Reference) (hcontains : obj.refs.contains r = true) :
    r ∈ Region.refs region := by
  have hobj_mem_entries := AList.mem_lookup_iff.mp (Option.mem_def.mpr hobj)
  have hobj_mem_values := List.mem_map_of_mem (f := (·.2)) hobj_mem_entries
  dsimp only at hobj_mem_values
  have hr_in_obj_refs := List.contains_iff_mem.mp hcontains
  exact List.mem_flatMap_of_mem hobj_mem_values hr_in_obj_refs

-- If `oid` resolves into region `rid` and some `r` is one of its object's own field values,
-- `r` already contributes to the whole heap's refs. Used by the CR4-for-regions case below to
-- turn an in-region object's field occurrence of a region reference into an `H2`-countable fact.
private theorem oid_field_mem_heap_refs (cfg : RuntimeConfig) (oid : ObjectId) (rid : RegionId)
    (obj : Object) (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn rid))
    (hobjAt : (Reference.OId oid).objAt? cfg = some obj) (r : Reference)
    (hcontains : obj.refs.contains r = true) :
    r ∈ cfg.heap.refs := by
  dsimp only [Reference.objAt?] at hobjAt
  rw [hloc] at hobjAt
  dsimp only at hobjAt
  cases hlookup : cfg.heap.lookup rid with
  | none => rw [hlookup] at hobjAt; simp at hobjAt
  | some region =>
    rw [hlookup] at hobjAt
    dsimp at hobjAt
    have hobj_mem_entries := AList.mem_lookup_iff.mp (Option.mem_def.mpr hobjAt)
    have hobj_mem_values := List.mem_map_of_mem (f := (·.2)) hobj_mem_entries
    dsimp only at hobj_mem_values
    have hr_in_obj_refs := List.contains_iff_mem.mp hcontains
    have hr_in_region_refs : r ∈ region.refs :=
      List.mem_flatMap_of_mem hobj_mem_values hr_in_obj_refs
    have hregion_mem_entries : (⟨rid, region⟩ : Sigma (fun _ : RegionId => Region)) ∈ cfg.heap.entries :=
      AList.mem_lookup_iff.mp (Option.mem_def.mpr hlookup)
    have hregion_mem_values := List.mem_map_of_mem (f := (·.2)) hregion_mem_entries
    dsimp only at hregion_mem_values
    unfold Heap.refs
    rw [List.bind_eq_flatMap, List.mem_flatMap]
    exact ⟨region, hregion_mem_values, hr_in_region_refs⟩

-- Any reference already present in some on-stack frame's own refs already contributes to the
-- whole stack's refs.
private theorem frame_refs_mem_stack_refs (cfg : RuntimeConfig) (frame1 : FrameWithIndex)
    (hframe1mem : frame1 ∈ cfg.stackWithIndex) (r : Reference) (hr : r ∈ frame1.refs) :
    r ∈ cfg.stack.refs := by
  have hframe1mem' : frame1 ∈ cfg.stackWithIndex := hframe1mem
  unfold RuntimeConfig.stackWithIndex at hframe1mem'
  obtain ⟨n, hn_len, hn_eq⟩ := List.mem_mapIdx.mp hframe1mem'
  have hg_in_stack : frame1.toFrame ∈ cfg.stack := by
    rw [← hn_eq]
    dsimp
    exact List.mem_iff_getElem.mpr ⟨n, _, rfl⟩
  unfold Stack.refs
  rw [List.bind_eq_flatMap, List.mem_flatMap]
  exact ⟨Frame.refs frame1.toFrame, List.mem_map_of_mem hg_in_stack, hr⟩

-- Any value in a stack frame's own varMap already contributes to the whole stack's refs.
private theorem var_mem_stack_refs (cfg : RuntimeConfig) (frame1 : FrameWithIndex)
    (hframe1mem : frame1 ∈ cfg.stackWithIndex) (var : VarName) (r : Reference)
    (hlookup : frame1.varMap.lookup var = some r) :
    r ∈ cfg.stack.refs := by
  have hr_mem_entries := AList.mem_lookup_iff.mp (Option.mem_def.mpr hlookup)
  have hr_mem_values := List.mem_map_of_mem (f := (·.2)) hr_mem_entries
  dsimp only at hr_mem_values
  exact frame_refs_mem_stack_refs cfg frame1 hframe1mem r (List.mem_append_right _ hr_mem_values)

-- If `oid` resolves onto the stack at index `fid` and some `r` is one of its object's own field
-- values, `r` already contributes to the whole stack's refs. Mirrors `oid_field_mem_heap_refs`.
private theorem oid_field_mem_stack_refs (cfg : RuntimeConfig) (oid : ObjectId) (fid : Index)
    (obj : Object) (hloc : (Reference.OId oid).loc? cfg = some (Location.Stk fid))
    (hobjAt : (Reference.OId oid).objAt? cfg = some obj) (r : Reference)
    (hcontains : obj.refs.contains r = true) :
    r ∈ cfg.stack.refs := by
  dsimp only [Reference.objAt?] at hobjAt
  rw [hloc] at hobjAt
  dsimp only at hobjAt
  cases hfind : cfg.stackWithIndex.find? (fun frame => frame.index == fid) with
  | none => rw [hfind] at hobjAt; simp at hobjAt
  | some frameA =>
    rw [hfind] at hobjAt
    dsimp at hobjAt
    have hobj_mem_entries := AList.mem_lookup_iff.mp (Option.mem_def.mpr hobjAt)
    have hobj_mem_values := List.mem_map_of_mem (f := (·.2)) hobj_mem_entries
    dsimp only at hobj_mem_values
    have hr_in_obj_refs := List.contains_iff_mem.mp hcontains
    have hr_in_frame_refs : r ∈ frameA.refs :=
      List.mem_append_left _ (List.mem_flatMap_of_mem hobj_mem_values hr_in_obj_refs)
    exact frame_refs_mem_stack_refs cfg frameA (List.mem_of_find?_eq_some hfind) r hr_in_frame_refs

-- Two distinct objects in the *same* region, both holding `r` as a field value, already forces
-- `cfg.heap.refs.count r ≥ 2` -- used (contrapositively) to rule out a region reference having
-- two distinct storage locations inside one region, per `H2`.
private theorem two_oid_fields_mem_heap_refs (cfg : RuntimeConfig) (rid : RegionId) (region : Region)
    (hlookup : cfg.heap.lookup rid = some region)
    (oid1 : ObjectId) (obj1 : Object) (hobj1 : region.objMap.lookup oid1 = some obj1)
    (oid2 : ObjectId) (obj2 : Object) (hobj2 : region.objMap.lookup oid2 = some obj2)
    (hne : oid1 ≠ oid2) (r : Reference)
    (hcontains1 : obj1.refs.contains r = true) (hcontains2 : obj2.refs.contains r = true) :
    2 ≤ cfg.heap.refs.count r := by
  have hmem1 : (⟨oid1, obj1⟩ : Sigma (fun _ : ObjectId => Object)) ∈ region.objMap.entries :=
    AList.mem_lookup_iff.mp (Option.mem_def.mpr hobj1)
  have hmem2 : (⟨oid2, obj2⟩ : Sigma (fun _ : ObjectId => Object)) ∈ region.objMap.entries :=
    AList.mem_lookup_iff.mp (Option.mem_def.mpr hobj2)
  have hneq : (⟨oid1, obj1⟩ : Sigma (fun _ : ObjectId => Object)) ≠ ⟨oid2, obj2⟩ := by
    intro h; exact hne (congrArg Sigma.fst h)
  have hb1 : r ∈ Object.refs obj1 := List.contains_iff_mem.mp hcontains1
  have hb2 : r ∈ Object.refs obj2 := List.contains_iff_mem.mp hcontains2
  have hcount := List.two_le_count_flatMap_of_ne (f := fun e => Object.refs e.2) hneq hmem1 hmem2 hb1 hb2
  have hregion_eq : region.objMap.entries.flatMap (fun e => Object.refs e.2) = Region.refs region := by
    unfold Region.refs
    rw [List.bind_eq_flatMap, List.flatMap_map]
  rw [hregion_eq] at hcount
  have hregion_mem : region ∈ cfg.heap.entries.map (·.2) :=
    List.mem_map_of_mem (AList.mem_lookup_iff.mp (Option.mem_def.mpr hlookup))
  have hle := List.count_le_count_flatMap_of_mem (f := Region.refs) hregion_mem (b := r)
  unfold Heap.refs
  rw [List.bind_eq_flatMap]
  omega

-- Two distinct regions, both holding `r` as a field value somewhere inside them, already forces
-- `cfg.heap.refs.count r ≥ 2` -- used (contrapositively) to rule out a region reference having
-- two distinct storage locations across different regions, per `H2`.
private theorem two_region_refs_mem_heap_refs (cfg : RuntimeConfig)
    (rid1 : RegionId) (region1 : Region) (hlookup1 : cfg.heap.lookup rid1 = some region1)
    (rid2 : RegionId) (region2 : Region) (hlookup2 : cfg.heap.lookup rid2 = some region2)
    (hne : rid1 ≠ rid2) (r : Reference)
    (hmem1 : r ∈ Region.refs region1) (hmem2 : r ∈ Region.refs region2) :
    2 ≤ cfg.heap.refs.count r := by
  have hmemE1 : (⟨rid1, region1⟩ : Sigma (fun _ : RegionId => Region)) ∈ cfg.heap.entries :=
    AList.mem_lookup_iff.mp (Option.mem_def.mpr hlookup1)
  have hmemE2 : (⟨rid2, region2⟩ : Sigma (fun _ : RegionId => Region)) ∈ cfg.heap.entries :=
    AList.mem_lookup_iff.mp (Option.mem_def.mpr hlookup2)
  have hneq : (⟨rid1, region1⟩ : Sigma (fun _ : RegionId => Region)) ≠ ⟨rid2, region2⟩ := by
    intro h; exact hne (congrArg Sigma.fst h)
  have hcount := List.two_le_count_flatMap_of_ne (f := fun e => Region.refs e.2) hneq hmemE1 hmemE2 hmem1 hmem2
  have hheap_eq : cfg.heap.entries.flatMap (fun e => Region.refs e.2) = Heap.refs cfg.heap := by
    unfold Heap.refs
    rw [List.bind_eq_flatMap, List.flatMap_map]
  rwa [hheap_eq] at hcount

-- Core CR4 argument for an object directly resident in the suspended region, reused both by
-- `CR4`'s own `OId` case and by its `RId` case (once an `RId`'s
-- unique storage location is traced back to an in-region object, see `oid_field_unique` below).
private theorem stackReferencable_iff_frameReferencable_oid (cfg : RuntimeConfig)
    (vrcfg : ValidReachableConfig cfg) (frame : FrameWithIndex) (hframemem : frame ∈ cfg.stackWithIndex)
    (oid : ObjectId) (hoid : (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId)) :
    StackReferencable cfg (Reference.OId oid) ↔ FrameReferencable cfg frame.index (Reference.OId oid) := by
  constructor
  · intro hstackreachable
    unfold StackReferencable at hstackreachable
    obtain ⟨frame', hframe'mem, hframe'framereachable⟩ := hstackreachable
    have cr3 := vrcfg.cr3
    unfold CR3 at cr3
    have hle := FrameReferencable_owner_index_le cfg vrcfg.toValidConfig frame' hframe'framereachable
      frame.regionId hoid frame hframemem rfl
    rcases hle.lt_or_eq with hlt | heq
    · exact cr3 frame hframemem frame' hframe'mem hlt oid hoid hframe'framereachable
    · have hframeq : frame = frame' := swap_corollary_stackWithIndex_index_inj hframemem hframe'mem heq
      rw [hframeq]; exact hframe'framereachable
  · intro hframereachable
    exists frame

-- report.pdf CR4, generalized to arbitrary references (not just objects): the hypothesis
-- `RegionReferencable cfg frame.regionId ref` covers both the original OId-restricted case (`ref`
-- itself resides in the suspended region -- H3 forces every OId reachable *within* a region to
-- stay `loc?`-located in that same region, so this case reduces to the original argument via
-- `RegionReferencable_stays_in_region`) and the new case where `ref` is a region reference
-- (`Reference.RId rid'`) sitting one field-hop beyond an in-region object -- `RegionReferencable`'s
-- own `step` constructor already allows this, since only its *source* needs to be `OId`-shaped.
-- `_hframesus` isn't needed by the proof (CR3 already forces it vacuously when `frame` is the
-- active/last frame) -- kept only to stay faithful to the report's statement.
-- turns out this is irrespective of the frame, so we do not need a hypothesis saying that the
-- frame is suspended.
theorem CR4 (cfg : RuntimeConfig) (vrcfg : ValidReachableConfig cfg)
    (frame : FrameWithIndex) (hframemem : frame ∈ cfg.stackWithIndex)
    (ref : Reference) (href : RegionReferencable cfg frame.regionId ref) :
    StackReferencable cfg ref ↔
    FrameReferencable cfg frame.index ref := by
  cases ref with
  | OId oid =>
    have hoid : (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) :=
      RegionReferencable_stays_in_region vrcfg.toValidConfig href
    exact stackReferencable_iff_frameReferencable_oid cfg vrcfg frame hframemem oid hoid
  | RId rid' =>
    cases href with
    | step hobj hcontains hrr =>
      rename_i oid obj
      have hoid : (Reference.OId oid).loc? cfg = some (Location.Rgn frame.regionId) :=
        RegionReferencable_stays_in_region vrcfg.toValidConfig hrr
      constructor
      · intro hstackreachable
        obtain ⟨frame', hframe'mem, hframe'framereachable⟩ := hstackreachable
        have hrtg := (FrameReferencable_iff_reflTransGen cfg frame'.index (Reference.RId rid')).mp
          hframe'framereachable
        obtain ⟨start, hroot, hchain⟩ := hrtg
        cases hchain with
        | refl =>
          exfalso
          rcases hroot with ⟨frame1, hframe1mem, _, var, hlookup⟩ |
            ⟨_, _, _, region1, _, hbridge⟩
          · have h1 : Reference.RId rid' ∈ cfg.stack.refs :=
              var_mem_stack_refs cfg frame1 hframe1mem var (Reference.RId rid') hlookup
            have h2 : Reference.RId rid' ∈ cfg.heap.refs :=
              oid_field_mem_heap_refs cfg oid frame.regionId obj hoid hobj (Reference.RId rid') hcontains
            have hc1 := List.count_pos_iff.mpr h1
            have hc2 := List.count_pos_iff.mpr h2
            have hbound := vrcfg.h2 rid'
            omega
          · exact absurd hbridge (by simp)
        | tail hprev hstep =>
          rename_i y
          obtain ⟨oid0, hy_eq⟩ := hstep.exists_oid_left
          subst hy_eq
          obtain ⟨obj0, hobjAt0, hcontains0⟩ := hstep
          cases hloc0 : (Reference.OId oid0).loc? cfg with
          | none =>
            exfalso
            dsimp only [Reference.objAt?] at hobjAt0
            rw [hloc0] at hobjAt0
            simp at hobjAt0
          | some loc0 =>
            cases loc0 with
            | Stk fid0 =>
              exfalso
              have h1 : Reference.RId rid' ∈ cfg.stack.refs :=
                oid_field_mem_stack_refs cfg oid0 fid0 obj0 hloc0 hobjAt0 (Reference.RId rid') hcontains0
              have h2 : Reference.RId rid' ∈ cfg.heap.refs :=
                oid_field_mem_heap_refs cfg oid frame.regionId obj hoid hobj (Reference.RId rid') hcontains
              have hc1 := List.count_pos_iff.mpr h1
              have hc2 := List.count_pos_iff.mpr h2
              have hbound := vrcfg.h2 rid'
              omega
            | Rgn rid0 =>
              obtain ⟨region0, hlookup0, hobjlookup0⟩ := oid_region_lookup cfg oid0 rid0 obj0 hloc0 hobjAt0
              obtain ⟨region, hlookup, hobjlookup⟩ := oid_region_lookup cfg oid frame.regionId obj hoid hobj
              by_cases heqrid : rid0 = frame.regionId
              · subst heqrid
                rw [hlookup] at hlookup0
                injection hlookup0 with hregion_eq
                subst hregion_eq
                by_cases heqoid : oid0 = oid
                · subst heqoid
                  rw [hobjlookup] at hobjlookup0
                  injection hobjlookup0 with hobj_eq
                  subst hobj_eq
                  have hoidreach : FrameReferencable cfg frame'.index (Reference.OId oid0) :=
                    (FrameReferencable_iff_reflTransGen cfg frame'.index (Reference.OId oid0)).mpr
                      ⟨start, hroot, hprev⟩
                  have hoidstack : StackReferencable cfg (Reference.OId oid0) := ⟨frame', hframe'mem, hoidreach⟩
                  have hoidframe :=
                    (stackReferencable_iff_frameReferencable_oid cfg vrcfg frame hframemem oid0 hoid).mp hoidstack
                  exact FrameReferencable.step hobj hcontains hoidframe
                · exfalso
                  have hcount := two_oid_fields_mem_heap_refs cfg frame.regionId region hlookup
                    oid obj hobjlookup oid0 obj0 hobjlookup0 (Ne.symm heqoid) (Reference.RId rid')
                    hcontains hcontains0
                  have hbound := vrcfg.h2 rid'
                  have hcstack : 0 ≤ cfg.stack.refs.count (Reference.RId rid') := Nat.zero_le _
                  omega
              · exfalso
                have hmem : Reference.RId rid' ∈ Region.refs region :=
                  objMap_lookup_mem_region_refs region oid obj hobjlookup (Reference.RId rid') hcontains
                have hmem0 : Reference.RId rid' ∈ Region.refs region0 :=
                  objMap_lookup_mem_region_refs region0 oid0 obj0 hobjlookup0 (Reference.RId rid') hcontains0
                have hcount := two_region_refs_mem_heap_refs cfg frame.regionId region hlookup rid0 region0
                  hlookup0 (Ne.symm heqrid) (Reference.RId rid') hmem hmem0
                have hbound := vrcfg.h2 rid'
                have hcstack : 0 ≤ cfg.stack.refs.count (Reference.RId rid') := Nat.zero_le _
                omega
      · intro hframereachable
        exists frame
