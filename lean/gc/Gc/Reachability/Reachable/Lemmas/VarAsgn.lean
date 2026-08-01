import Gc.Model.Types
import Gc.Model.Helpers
import Gc.Model.Validity
import Gc.Model.Mutation.Mutation
import Gc.Model.Preservation
import Gc.Reachability.Reachable.Semantics
import Gc.Reachability.Reachable.Basic
import Gc.Reachability.Reachable.Lemmas.Common
import Gc.Reachability.Reachable.Lemmas.MakeObjStack

-- ===== varAsgn =====

-- A successful `resolveV` traces back to a genuine `FrameRoot`: an ordinary `varMap` entry or the frame's own bridge var.
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

-- A successful `resolveFA` traces back to a genuine `FrameReachable`: the root resolves via `resolveV_frameRoot`, plus one more `ReachableStep` hop.
theorem resolveFA_frameReach {cfg : RuntimeConfig} {y : FieldAccess} {ref : Reference}
    (hyf : resolveFA y cfg = some ref) :
    ∃ frameY : FrameWithIndex, frameY ∈ cfg.stackWithIndex ∧ FrameReachable cfg frameY.index ref := by
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
              have hstep0 : ReachableStep cfg (Reference.OId oid0) ref := by
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
              have hstep0 : ReachableStep cfg (Reference.OId oid0) ref := by
                rw [ReachableStep_oid_iff]
                exact ⟨obj0, hobjAt0,
                  List.contains_iff_mem.mpr (List.mem_map_of_mem (f := (·.2)) (AList.lookup_mem_entries hyf))⟩
              exact ⟨frameY, hframeYMem, FrameReachable.step hstep0 hreachY0⟩

-- H3-confinement lifted along the whole chain: an `OId` reached from `rid`'s bridge resolves back into `rid`, or into a region entered via a Closed-region hop.
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

-- A chain rooted at `rid`'s (Open) bridge can never reach an object in a different Open region (confinement above forces back into `rid` or a Closed region).
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

-- `objAt?` agrees between `cfg`/`cfg'` unconditionally: unlike the `make*` ops, `varAsgn` never allocates a fresh id.
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

-- `ReachableStep` agrees for every `RId`-sourced step: the bridge-var branch only mutates an Open region's scalar, never `objMap`, so no `RId` step is possible there either side.
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

-- Stack membership below the last frame agrees between `cfg`/`cfg'`: varAsgn never touches any other frame's record.
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

-- A frame strictly before the last one has a different regionId from the last frame's own (S1: regionId is injective across the stack).
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

-- `FrameReachable` agrees below the last frame: combines `varAsgn_step_eq`, `varAsgn_frame_mem_iff`, and `varAsgn_regionId_ne` (S1-based, since the mutated region's key isn't fresh).
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

-- The freshly-updated last frame is a member of `cfg'.stackWithIndex`, at the same index it had in `cfg`.
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
