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
