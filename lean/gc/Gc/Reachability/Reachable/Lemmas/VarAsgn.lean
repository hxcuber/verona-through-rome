module

public import Gc.Model.Types
public import Gc.Model.Helpers
public import Gc.Model.Validity
public import Gc.Model.Mutation.Mutation
public import Gc.Model.Preservation
public import Gc.Reachability.Reachable.Semantics
public import Gc.Reachability.Reachable.FrameReachableAtLaterFrame.Def
public import Gc.Reachability.Reachable.Lemmas.Common
public import Gc.Reachability.Reachable.Lemmas.MakeObjStack

@[expose] public section

-- A successful `resolveV` traces back to a genuine `FrameRoot`: an ordinary `varMap` entry or the frame's own bridge var.
theorem resolveV_frameRoot {cfg : RuntimeConfig} {var : VarName} {oid : ObjectId}
    (hrv : resolveV var cfg = some (Reference.OId oid)) :
    ∃ frameY : FrameWithIndex, frameY ∈ cfg.stackWithIndex ∧ FrameRoot cfg frameY.index (Reference.OId oid) := by
  simp [resolveV, Option.bind_eq_some_iff] at hrv
  obtain ⟨frameV, hfV, hrv⟩ := hrv
  have hmem : frameV ∈ cfg.stackWithIndex := List.mem_reverse.mp (List.mem_of_find?_eq_some hfV)
  rcases hrv with hlk | ⟨-, -, regionV, hregV, rfl⟩
  · exact ⟨frameV, hmem, .inl ⟨frameV, hmem, rfl, _, hlk⟩⟩
  · exact ⟨frameV, hmem, .inr ⟨frameV, hmem, rfl, regionV, hregV, rfl⟩⟩

-- A successful `resolveFA` traces back to a genuine `FrameReachable`: the root resolves via `resolveV_frameRoot`, plus one more `ReachableStep` hop.
theorem resolveFA_frameReach {cfg : RuntimeConfig} {y : FieldAccess} {ref : Reference}
    (hyf : resolveFA y cfg = some ref) :
    ∃ frameY : FrameWithIndex, frameY ∈ cfg.stackWithIndex ∧ FrameReachable cfg frameY.index ref := by
  unfold resolveFA at hyf
  rcases hrv : resolveV y.root cfg with _ | _ | oid0 <;> simp only [hrv] at hyf
  · simp at hyf
  · simp at hyf
  obtain ⟨frameY, hmem, hroot⟩ := resolveV_frameRoot hrv
  obtain ⟨obj, hobj, hf⟩ : ∃ obj, (Reference.OId oid0).objAt? cfg = some obj ∧ obj.lookup y.field = some ref := by
    unfold Reference.objAt?
    rcases hloc : (Reference.OId oid0).loc? cfg with _ | _ | _ <;> simp_all [Option.bind_eq_some_iff] <;> aesop
  exact ⟨frameY, hmem, .step ((ReachableStep_oid_iff ..).mpr ⟨obj, hobj, List.contains_iff_mem.mpr (List.mem_map_of_mem (AList.lookup_mem_entries hf))⟩)
    ((FrameReachable_iff_reflTransGen ..).mpr ⟨_, hroot, .refl⟩)⟩

-- `objAt?` agrees between `cfg`/`cfg'` unconditionally: `varAsgn` never allocates and never edits an `objMap`.
private theorem varAsgn_objAt_eq {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : varAsgn xf y cfg = some cfg') (oid : ObjectId) :
    (Reference.OId oid).objAt? cfg = (Reference.OId oid).objAt? cfg' := by
  have hlocEq := varAsgn_corollary_loc_eq vcfg h oid
  obtain ⟨frame, hlast, ⟨oidY, rid, region, -, -, -, -, hregion, rfl⟩ | ⟨oidY, -, -, -, rfl⟩⟩ := varAsgn_cases h
  · simp only [Reference.objAt?, ← hlocEq]
    rcases (Reference.OId oid).loc? cfg with _ | rid0 | _
    · rfl
    · by_cases heq : rid0 = rid
      · subst heq
        simp [hregion]
      · simp [AList.lookup_insert_ne heq]
    · rfl
  · simp only [Reference.objAt?, ← hlocEq]
    rcases (Reference.OId oid).loc? cfg with _ | _ | fid
    · rfl
    · rfl
    dsimp only
    rw [stackWithIndex_find_index_eq_getElem, stackWithIndex_find_index_eq_getElem,
      stackWithIndex_eq_of_getLast? hlast, stackWithIndex_mk_append_singleton]
    simp only [List.getElem?_append, List.getElem?_singleton]
    split_ifs <;> simp

-- `ReachableStep` agrees for every `RId`-sourced step: the bridge-var branch only edits the active frame's Open region.
private theorem varAsgn_rid_step_iff {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : varAsgn xf y cfg = some cfg') (rid : RegionId) (b : Reference) :
    ReachableStep cfg (Reference.RId rid) b ↔ ReachableStep cfg' (Reference.RId rid) b := by
  obtain ⟨frame, hlast, ⟨oid, rid0, region, -, -, -, rfl, hregion, rfl⟩ | ⟨oid, -, -, -, rfl⟩⟩ := varAsgn_cases h
  · by_cases heq : rid = frame.regionId
    · subst heq
      obtain ⟨region1, hlookup1, hopen1⟩ := l2_of_stackWithIndex vcfg (stackWithIndex_getLast_mem hlast)
      obtain rfl : region1 = region := by simpa [hregion] using hlookup1.symm
      simp [ReachableStep_rid_iff, hregion, hopen1]
    · simp only [ReachableStep_rid_iff, AList.lookup_insert_ne heq]
  · rfl

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
  obtain ⟨frame, hlast, ⟨-, -, -, -, -, -, -, -, rfl⟩ | ⟨-, -, -, -, rfl⟩⟩ := varAsgn_cases h
  · rfl
  · rw [stackWithIndex_eq_of_getLast? hlast, stackWithIndex_mk_append_singleton]
    have hne : ∀ f : Frame, X ≠ { f with index := cfg.stack.dropLast.length } := by
      rintro f rfl
      simp at hXlt
    simp only [List.mem_append, List.mem_singleton, or_iff_left (hne _)]

-- `FrameReachable` agrees below the last frame: the step relation is unchanged and so is every suspended root (S1 keeps the edited region apart).
theorem varAsgn_frame_reachable_iff {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : varAsgn xf y cfg = some cfg')
    {X : FrameWithIndex} (_hXmem : X ∈ cfg.stackWithIndex) (hXlt : X.index < cfg.stack.length - 1)
    (ref : Reference) : FrameReachable cfg X.index ref ↔ FrameReachable cfg' X.index ref := by
  have hmem : ∀ {f : FrameWithIndex}, f.index = X.index → (f ∈ cfg.stackWithIndex ↔ f ∈ cfg'.stackWithIndex) :=
    fun hfi => varAsgn_frame_mem_iff h (hfi ▸ hXlt)
  have hheap : ∀ {f : FrameWithIndex}, f ∈ cfg.stackWithIndex → f.index = X.index →
      cfg'.heap.lookup f.regionId = cfg.heap.lookup f.regionId := by
    intro f hf hfi
    obtain ⟨lastFrame, hlast, ⟨-, _, -, -, -, -, rfl, -, rfl⟩ | ⟨-, -, -, -, rfl⟩⟩ := varAsgn_cases h
    · exact AList.lookup_insert_ne (regionId_ne_last_of_suspended vcfg hf (hfi ▸ hXlt) hlast)
    · rfl
  have hroot : ∀ start, FrameRoot cfg X.index start ↔ FrameRoot cfg' X.index start := fun start => by
    constructor
    · rintro (⟨f, hf, hfi, hv⟩ | ⟨f, hf, hfi, r, hr, hb⟩)
      · exact .inl ⟨f, (hmem hfi).mp hf, hfi, hv⟩
      · exact .inr ⟨f, (hmem hfi).mp hf, hfi, r, (hheap hf hfi).trans hr, hb⟩
    · rintro (⟨f, hf, hfi, hv⟩ | ⟨f, hf, hfi, r, hr, hb⟩)
      · exact .inl ⟨f, (hmem hfi).mpr hf, hfi, hv⟩
      · exact .inr ⟨f, (hmem hfi).mpr hf, hfi, r, (hheap ((hmem hfi).mpr hf) hfi).symm.trans hr, hb⟩
  simp only [FrameReachable_iff_reflTransGen, varAsgn_step_eq vcfg h, hroot]

-- The freshly-updated last frame is a member of `cfg'.stackWithIndex`, at the same index it had in `cfg`.
theorem varAsgn_freshvar_last_mem {cfg cfg' : RuntimeConfig} {xf : VarName} {oidY : ObjectId} {lastFrame : Frame}
    (_hlast : cfg.stack.getLast? = some lastFrame)
    (hcfg' : cfg' = { cfg with stack := cfg.stack.dropLast ++
      [{ lastFrame with varMap := lastFrame.varMap.insert xf (Reference.OId oidY) }] }) :
    ({ lastFrame with varMap := lastFrame.varMap.insert xf (Reference.OId oidY), index := cfg.stack.length - 1 } : FrameWithIndex) ∈ cfg'.stackWithIndex := by
  subst hcfg'
  simp [stackWithIndex_mk_append_singleton]

-- varAsgn preserves the stack length.
theorem varAsgn_length {cfg cfg' : RuntimeConfig} (h : varAsgn xf y cfg = some cfg') :
    cfg'.stackWithIndex.length = cfg.stackWithIndex.length := by
  obtain ⟨A, hA, ⟨-, -, -, -, -, -, -, -, rfl⟩ | ⟨-, -, -, -, rfl⟩⟩ := varAsgn_cases h
  · rfl
  · exact stackWithIndex_length_of_replace_last hA rfl

-- Every root after varAsgn is stack-reachable before it: the only new root value is `y`'s resolved object.
private theorem varAsgn_root_reach {cfg cfg' : RuntimeConfig} (h : varAsgn xf y cfg = some cfg')
    {fid : Index} {start : Reference} (hs : FrameRoot cfg' fid start) : StackReachable cfg start := by
  have hR : ∀ fid, FrameRoot cfg fid start → StackReachable cfg start := fun _ hr => StackReachable_of_root hr .refl
  obtain ⟨A, hA, ⟨oidY, rid, region, hyf, -, -, rfl, hregion, rfl⟩ | ⟨oidY, hyf, -, -, rfl⟩⟩ := varAsgn_cases h
  · rcases hs with ⟨f, hf, rfl, v, hv⟩ | ⟨f, hf, rfl, r, hr, rfl⟩
    · exact hR _ (.inl ⟨f, hf, rfl, v, hv⟩)
    · by_cases he : f.regionId = A.regionId
      · rw [he, AList.lookup_insert] at hr
        obtain rfl := Option.some.inj hr
        exact resolveFA_frameReach hyf
      · exact hR _ (.inr ⟨f, hf, rfl, r, by simpa [AList.lookup_insert_ne he] using hr, rfl⟩)
  · have hsw := stackWithIndex_eq_of_getLast? hA
    have hlastA : ({ A with index := cfg.stack.dropLast.length } : FrameWithIndex) ∈ cfg.stackWithIndex := by
      simp [hsw]
    rw [FrameRoot, stackWithIndex_mk_append_singleton] at hs
    rcases hs with ⟨f, hf, rfl, v, hv⟩ | ⟨f, hf, rfl, r, hr, rfl⟩ <;>
      rcases List.mem_append.mp hf with hf | hf
    · exact hR _ (.inl ⟨f, hsw ▸ List.mem_append_left _ hf, rfl, v, hv⟩)
    · obtain rfl := List.mem_singleton.mp hf
      by_cases hv' : v = xf
      · subst hv'
        simp at hv
        exact hv ▸ resolveFA_frameReach hyf
      · exact hR _ (.inl ⟨_, hlastA, rfl, v, by simpa [AList.lookup_insert_ne hv'] using hv⟩)
    · exact hR _ (.inr ⟨f, hsw ▸ List.mem_append_left _ hf, rfl, r, hr, rfl⟩)
    · obtain rfl := List.mem_singleton.mp hf
      exact hR _ (.inr ⟨_, hlastA, rfl, r, hr, rfl⟩)

-- For `oid` in a suspended frame `F`'s region, varAsgn neither creates nor destroys its reachability from `F`.
theorem varAsgn_suspended_reach {cfg cfg' : RuntimeConfig} (vcfg : ValidConfig cfg)
    (h : varAsgn xf y cfg = some cfg') (hFR3 : FrameReachable_at_later_frame_implies_FrameReachable_at_frame cfg)
    {F : FrameWithIndex} (hF : F ∈ cfg.stackWithIndex) (hFlt : F.index < cfg.stackWithIndex.length - 1)
    {oid : ObjectId} (hloc : (Reference.OId oid).loc? cfg = some (Location.Rgn F.regionId)) :
    F ∈ cfg'.stackWithIndex ∧ (StackReachable cfg (.OId oid) → FrameReachable cfg' F.index (.OId oid)) ∧
    ∀ fid, FrameReachable cfg' fid (.OId oid) → StackReachable cfg (.OId oid) := by
  have hFlt' : F.index < cfg.stack.length - 1 := by simpa [RuntimeConfig.stackWithIndex] using hFlt
  refine ⟨(varAsgn_frame_mem_iff h hFlt').mp hF, fun hs => (varAsgn_frame_reachable_iff vcfg h hF hFlt' _).mp
    (FrameReachable_of_StackReachable vcfg hFR3 hF hloc hs), fun fid hr => ?_⟩
  obtain ⟨start, hs, hc⟩ := (FrameReachable_iff_reflTransGen ..).mp hr
  obtain ⟨S, hS, hSr⟩ := varAsgn_root_reach h hs
  exact ⟨S, hS, FrameReachable_extend hSr (varAsgn_step_eq vcfg h ▸ hc)⟩
