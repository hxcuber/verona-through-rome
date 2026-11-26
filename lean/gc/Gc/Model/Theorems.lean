module

public import Mathlib.Data.List.AList

@[expose] public section

theorem AList.lookup_mem_entries {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a} {s : AList β} :
  AList.lookup a s = some b → ⟨a, b⟩ ∈ s.entries :=
  AList.mem_lookup_iff.mp

theorem List.mem_of_mem_dropLast_mapIdx {β : Type u_1} {α : Type u_2} {f : Nat → α → β} {b : β} {l : List α} :
  b ∈ (List.dropLast l).mapIdx f → b ∈ l.mapIdx f := by
  intro h
  obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.mp h
  exact List.mem_mapIdx.mpr ⟨i, by simp at hi ⊢; omega, by simp [List.getElem_dropLast]⟩

theorem List.Sublist.flatten_sublist {α : Type} {l m : List (List α)} (h : l.Sublist m) :
  l.flatten.Sublist m.flatten := by
  induction h with
  | slnil => simp
  | cons head _ ih => simpa using List.sublist_append_of_sublist_right ih
  | cons_cons head _ ih => simpa using (List.append_sublist_append_left head).mpr ih

theorem List.le_foldl_max_self {l : List Nat} : ∀ init : Nat, init ≤ l.foldl max init := by
  induction l with
  | nil => exact fun _ => le_rfl
  | cons a l ih => exact fun init => le_trans (le_max_left init a) (ih _)

theorem List.mem_le_foldl_max {l : List Nat} : ∀ (init x : Nat), x ∈ l → x ≤ l.foldl max init := by
  induction l with
  | nil => simp
  | cons a l ih =>
    intro init x hx
    rcases List.mem_cons.mp hx with rfl | h
    · exact le_trans (le_max_right init x) (List.le_foldl_max_self _)
    · exact ih _ x h

theorem List.kunion_eq_append_of_disjoint_keys {α : Type u} {β : α → Type v} [DecidableEq α]
    {l1 l2 : List (Sigma β)} (h : ∀ a ∈ l1.keys, a ∉ l2.keys) :
    List.kunion l1 l2 = l1 ++ l2 := by
  induction l1 generalizing l2 with
  | nil => simp
  | cons s l1 ih =>
    rw [List.kunion_cons, List.kerase_of_notMem_keys (h s.1 (by simp)), ih (fun a ha => h a (by simp [ha]))]
    rfl

theorem AList.union_eq_append_of_disjoint_keys {α : Type u} {β : α → Type v} [DecidableEq α]
    {s1 s2 : AList β} (h : ∀ a ∈ s1.keys, a ∉ s2.keys) :
    (s1 ∪ s2).entries = s1.entries ++ s2.entries := by
  rw [AList.union_entries]
  exact List.kunion_eq_append_of_disjoint_keys h

-- If two distinct elements `a1 ≠ a2` of `l` both witness `b ∈ f a`, then `l.flatMap f` contains `b` at least twice.
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

-- A single element's count is a lower bound on the whole flatMap's count.
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
  refine List.find?_eq_some_iff_append.mpr ⟨pe, as, bs, hl, fun x hx => ?_⟩
  by_contra hpx
  exact e_notin_as (uniq x (hl ▸ List.mem_append_left _ hx) (by simpa using hpx) ▸ hx)

-- Inserting at an already-present key only permutes `.keys`.
theorem AList.keys_insert_perm_of_mem {α : Type*} {β : α → Type*} [DecidableEq α]
    {l : AList β} {k : α} {v : β k} (hk : k ∈ l.keys) :
    (l.insert k v).keys.Perm l.keys := by
  obtain ⟨v0, l1e, l2e, hnotmem, heq, hkerase⟩ := List.exists_of_kerase hk
  unfold AList.keys
  rw [AList.entries_insert, hkerase]
  conv_rhs => rw [heq]
  rw [List.keys_cons, List.keys_append, List.keys_append, List.keys_cons]
  exact List.perm_middle.symm

-- A successful `lookup` means the key is already present.
theorem AList.mem_keys_of_lookup_eq_some {α : Type*} {β : α → Type*} [DecidableEq α]
    {l : AList β} {k : α} {v : β k} (hv : l.lookup k = some v) : k ∈ l.keys :=
  AList.mem_keys.mp (AList.lookup_isSome.mp (by rw [hv]; rfl))

-- If `(l.map f).flatten` is nodup, a shared element pins down the index it came from.
theorem List.index_eq_of_mem_flatten_map_nodup {γ α : Type*} {l : List γ} {f : γ → List α}
    (h : (l.map f).flatten.Nodup) {i j : Nat} (hi : i < l.length) (hj : j < l.length) {a : α}
    (hai : a ∈ f l[i]) (haj : a ∈ f l[j]) : i = j := by
  rw [List.nodup_flatten, List.pairwise_map, List.pairwise_iff_getElem] at h
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · exact (h.2 i j hi hj hlt hai haj).elim
  · rfl
  · exact (h.2 j i hj hi hgt haj hai).elim

theorem List.eq_of_mem_flatten_map_nodup {γ α : Type*} {l : List γ} {f : γ → List α}
    (h : (l.map f).flatten.Nodup) {x y : γ} (hx : x ∈ l) (hy : y ∈ l) {a : α}
    (hax : a ∈ f x) (hay : a ∈ f y) : x = y := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hy
  cases List.index_eq_of_mem_flatten_map_nodup h hi hj hax hay
  rfl
