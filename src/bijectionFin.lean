import data.set.basic
open list
open nat

def is_finite {A: Type} (S: set A): Prop := ∃ (n:ℕ) (f:S → {x // x < n}), function.bijective f

section operations
variables {A: Type} [decidable_eq A]

lemma subset_of_fin_is_fin (s1 s2: set A) (subs: s2 ⊆  s1) (s1_fin: is_finite s1): is_finite s2 :=
begin
  unfold is_finite at s1_fin,
  rcases s1_fin with ⟨n_s1, f_s1, f_s1_bij⟩,
  unfold is_finite,
  sorry,
end

lemma intersection_preserves_fin (s1 s2: set A) (s1_fin: is_finite s1) (s2_fin: is_finite s2): is_finite (s1 ∩ s2) :=
begin
  apply subset_of_fin_is_fin s1 (s1 ∩ s2),
  rw set.subset_def,
  intro a,
  rw set.mem_inter_iff,
  intro h,
  cases h,
  exact h_left,
  exact s1_fin,
end

lemma difference_preserves_fin (s1 s2: set A) (s1_fin: is_finite s1) (s2_fin: is_finite s2): is_finite (s1 \ s2) :=
begin
  apply subset_of_fin_is_fin s1 (s1 \ s2),
  rw set.subset_def,
  intro a,
  rw set.mem_diff,
  intro h,
  cases h,
  exact h_left,
  exact s1_fin,
end

def disjoint_union_bij (s1 s2: set A) (disj: disjoint s1 s2) {n1 n2: ℕ } (fs1: s1 → {x // x < n1}) (fs2: s2 → {x // x < n2}): (s1 ∪ s2) → {x // x < (n1 + n2)} := λ a, if a ∈ s1 then fs1 else n1 + fs2 

lemma disjoint_union_preserves_fin (s1 s2: set A) [∀ (a:A) (s:set A), decidable (a ∈ s)] (s1_fin: is_finite s1) (s2_fin: is_finite s2) (disj: disjoint s1 s2): is_finite (s1 ∪ s2) :=
begin
  unfold is_finite,
  unfold is_finite at s1_fin,
  unfold is_finite at s2_fin,
  rcases s1_fin with ⟨n_s1, f_s1, f_s1_bij⟩,
  rcases s2_fin with ⟨n_s2, f_s2, f_s2_bij⟩,
  existsi (n_s1 + n_s2),
  existsi ( λ (a ∈  (s1 ∪ s2)), if a ∈ s1 then f_s1 a else (n_s1 + f_s2 a)),
  sorry,
end

lemma disjoint_union_preserves_fin (s1 s2: set A) [has_mem ↥(s1 ∪ s2) (set A)] [∀ (a:A) (s:set A), decidable (a ∈ s)] [has_mem ↥(s1 \ s2 ∪ s2) (set A)] [has_mem A (set A)] [∀ (a:A) (s:set A), decidable (a ∈ s)] (s1_fin: is_finite s1) (s2_fin: is_finite s2): is_finite (s1 ∪ s2) :=
begin
  by_cases int: s1 ∩ s2 = ∅,
  apply disjoint_union_preserves_fin s1 s2 s1_fin s2_fin,
  rw set.disjoint_iff_inter_eq_empty,
  exact int,

  have h: s1 ∪ s2 = (s1 \ s2) ∪ s2,
  rw set.ext_iff,
  intro x,
  rw set.mem_union,
  rw set.mem_union,
  rw set.mem_diff,
  tauto,
  rw h,
  apply disjoint_union_preserves_fin (s1 \ s2) s2,
end

end operations

section size
variables {A: Type} [decidable_eq A]

def size (s: set A) (fin: is_finite s): ℕ :=
begin
  unfold is_finite at fin,
  rcases fin with ⟨n_s1, f_s1, f_s1_bij⟩,
end
end size