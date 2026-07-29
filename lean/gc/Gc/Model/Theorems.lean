import Mathlib.Data.List.AList

theorem AList.lookup_mem_entries {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a} {s : AList β} :
  AList.lookup a s = some b → ⟨a, b⟩ ∈ s.entries := by
  intro h
  rw [← Option.mem_def, AList.mem_lookup_iff] at h
  exact h

theorem List.mem_of_mem_dropLast_mapIdx {β : Type u_1} {α : Type u_2} {f : Nat → α → β} {b : β} {l : List α} :
  b ∈ (List.dropLast l).mapIdx f → b ∈ l.mapIdx f := by
  intro h
  induction l generalizing f b with
  | nil =>
    rw [List.dropLast_nil] at h
    contradiction
  | cons head tail ih =>
    cases tail with
    | nil =>
      dsimp at h
      contradiction
    | cons head' tail' =>
      dsimp at h
      rw [List.mapIdx_cons] at h
      cases h with
      | head =>
        rw [List.mapIdx_cons]
        left
      | tail _ h_tail =>
        rw [List.mapIdx_cons]
        right
        apply ih
        exact h_tail

theorem List.mem_append_mapIdx_of_mem {β : Type u_1} {α : Type u_2} {f : Nat → α → β} {b : β} {l : List α} {a : α} :
  b ∈ l.mapIdx f → b ∈ (l ++ [a]).mapIdx f := by
  intro h
  induction l generalizing f b with
  | nil =>
    contradiction
  | cons head tail ih =>
    rw [List.mapIdx_cons] at h
    cases h with
    | head =>
      rw [List.cons_append, List.mapIdx_cons]
      left
    | tail _ h_tail =>
      rw [List.cons_append, List.mapIdx_cons]
      right
      apply ih
      exact h_tail

theorem List.mem_append_singleton_iff_mem_cons : a ∈ (l ++ [b]) ↔ a ∈ b :: l := by
  constructor
  · intro h
    induction l with
    | nil =>
      rw [List.nil_append] at h
      exact h
    | cons head tail ih =>
      rw [List.cons_append] at h
      cases h with
      | head =>
        right
        left
      | tail _ h_tail =>
        apply (List.Perm.mem_iff (List.perm_append_singleton b (head :: tail))).mp
        right
        exact h_tail
  · intro h
    induction l with
    | nil =>
      rw [List.nil_append]
      exact h
    | cons head tail ih =>
      rw [List.cons_append]
      cases h with
      | head =>
        apply (List.Perm.mem_iff (List.perm_append_singleton b (head :: tail))).mpr
        left
      | tail _ h_tail =>
        apply (List.Perm.mem_iff (List.perm_append_singleton b (head :: tail))).mpr
        right
        exact h_tail

theorem List.Sublist.flatten_sublist {α : Type} {l m : List (List α)} (h : l.Sublist m) :
  l.flatten.Sublist m.flatten := by
  induction h with
  | slnil =>
    rw [List.flatten_nil]
  | cons head sublist ih =>
    rw [List.flatten_cons]
    exact List.sublist_append_of_sublist_right ih
  | cons₂ head sublist ih =>
    rw [List.flatten_cons, List.flatten_cons]
    exact (List.append_sublist_append_left head).mpr ih

theorem List.le_foldl_max_self {l : List Nat} : ∀ init : Nat, init ≤ l.foldl max init := by
  induction l with
  | nil => intro init; exact le_refl init
  | cons a l ih =>
    intro init
    rw [List.foldl_cons]
    exact le_trans (le_max_left init a) (ih (max init a))

theorem List.mem_le_foldl_max {l : List Nat} : ∀ (init x : Nat), x ∈ l → x ≤ l.foldl max init := by
  induction l with
  | nil => intro init x hx; exact absurd hx (List.not_mem_nil)
  | cons a l ih =>
    intro init x hx
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hx with heq | hmem
    · subst heq
      exact le_trans (le_max_right init x) (List.le_foldl_max_self (max init x))
    · exact ih (max init a) x hmem

theorem List.kunion_eq_append_of_disjoint_keys {α : Type u} {β : α → Type v} [DecidableEq α]
    {l1 l2 : List (Sigma β)} (h : ∀ a ∈ l1.keys, a ∉ l2.keys) :
    List.kunion l1 l2 = l1 ++ l2 := by
  induction l1 generalizing l2 with
  | nil => rw [List.nil_kunion]; rfl
  | cons s l1 ih =>
    rw [List.kunion_cons]
    have hs : s.1 ∉ l2.keys := h s.1 (by rw [List.keys_cons]; exact List.mem_cons_self)
    rw [List.kerase_of_notMem_keys hs]
    rw [ih (fun a ha => h a (by rw [List.keys_cons]; exact List.mem_cons_of_mem _ ha))]
    rfl

theorem AList.union_eq_append_of_disjoint_keys {α : Type u} {β : α → Type v} [DecidableEq α]
    {s1 s2 : AList β} (h : ∀ a ∈ s1.keys, a ∉ s2.keys) :
    (s1 ∪ s2).entries = s1.entries ++ s2.entries := by
  rw [AList.union_entries]
  exact List.kunion_eq_append_of_disjoint_keys h

-- If two distinct list elements `a1 ≠ a2` both witness `b ∈ f a`, `l.flatMap f` contains `b`
-- at least twice: `a1`/`a2`'s own contributions to the flatMap are disjoint list segments (one
-- per occurrence of `a1`/`a2` in `l`), so each contributes independently to the total count.
theorem List.two_le_count_flatMap_of_ne {α β : Type*} [DecidableEq β] {f : α → List β}
    {l : List α} {a1 a2 : α} (hne : a1 ≠ a2) (hmem1 : a1 ∈ l) (hmem2 : a2 ∈ l)
    {b : β} (hb1 : b ∈ f a1) (hb2 : b ∈ f a2) :
    2 ≤ (l.flatMap f).count b := by
  induction l with
  | nil => exact absurd hmem1 List.not_mem_nil
  | cons x xs ih =>
    rw [List.flatMap_cons, List.count_append]
    rcases List.mem_cons.mp hmem1 with rfl | hmem1'
    · rcases List.mem_cons.mp hmem2 with heq | hmem2'
      · exact absurd heq.symm hne
      · have h1 : 1 ≤ (f a1).count b := List.count_pos_iff.mpr hb1
        have h2 : 1 ≤ (xs.flatMap f).count b :=
          List.count_pos_iff.mpr (List.mem_flatMap.mpr ⟨a2, hmem2', hb2⟩)
        omega
    · rcases List.mem_cons.mp hmem2 with rfl | hmem2'
      · have h1 : 1 ≤ (f a2).count b := List.count_pos_iff.mpr hb2
        have h2 : 1 ≤ (xs.flatMap f).count b :=
          List.count_pos_iff.mpr (List.mem_flatMap.mpr ⟨a1, hmem1', hb1⟩)
        omega
      · have := ih hmem1' hmem2'
        omega

-- A single contributing element's own count is always a lower bound on the whole flatMap's count.
theorem List.count_le_count_flatMap_of_mem {α β : Type*} [DecidableEq β] {f : α → List β}
    {l : List α} {a : α} (hmem : a ∈ l) {b : β} :
    (f a).count b ≤ (l.flatMap f).count b := by
  induction l with
  | nil => exact absurd hmem List.not_mem_nil
  | cons x xs ih =>
    rw [List.flatMap_cons, List.count_append]
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · omega
    · have := ih hmem'
      omega

theorem List.find?_eq_some_of_unique {α} {p : α → Bool} {l : List α} {e : α}
    (mem : e ∈ l) (pe : p e) (uniq : ∀ x ∈ l, p x → x = e) : l.find? p = some e := by
  obtain ⟨as, bs, hl, e_notin_as⟩ := List.eq_append_cons_of_mem mem
  apply List.find?_eq_some_iff_append.mpr
  refine ⟨pe, as, bs, hl, ?_⟩
  intro x hx
  simp only [Bool.not_eq_true']
  by_contra hpx
  simp only [Bool.not_eq_false] at hpx
  apply e_notin_as
  have hx' : x ∈ l := by rw [hl]; exact List.mem_append_left _ hx
  rw [uniq x hx' hpx] at hx
  exact hx
