import data.set.basic data.set.function data.nat.basic
open list
open nat

def is_finite {A: Type} (S: set A): Prop := ∃ (n:ℕ) (f: ℕ → A), set.bij_on f (set_of (λ (a:ℕ), a < n)) S

def is_finite_n {A: Type} (S: set A) (n: ℕ ): Prop := ∃ (f: ℕ → A), set.bij_on f (set_of (λ (a:ℕ), a < n)) S


section operations
variables {A: Type} [decidable_eq A] [nonempty A]

lemma is_finite_ex_intro (s: set A) (n: ℕ) (fin_n: is_finite_n s n): is_finite s :=
begin
  unfold is_finite,
  use n,
  unfold is_finite_n at fin_n,
  exact fin_n,
end

lemma member_set_of_iff_pred {a:A} {p: A -> Prop}: a ∈ set_of p ↔ p a :=
begin
  rw set.mem_def,
  rw set.set_of_app_iff,
end

lemma a_lt_0_is_empty: (set_of (λ (a:ℕ), a < 0)) = (∅: set ℕ)  :=
begin
  rw set.ext_iff,
  intro x,
  simp,
end

lemma x_lt_1_iff_x_eq_0 (x: ℕ ): x < 1 ↔ x = 0 :=
begin
  rw nat.lt_succ_iff,
  split,
  intro h,
  cases h,
  refl,
  intro h,
  rw h,
end

lemma a_lt_1_is_zero_set: (set_of (λ (a:ℕ), a < 1)) = {0} :=
begin
  rw set.ext_iff,
  intro x,
  simp,
  apply x_lt_1_iff_x_eq_0,
end

lemma empty_set_is_finite: is_finite (∅:set A) :=
begin
  unfold is_finite,
  use 0,
  existsi (λ (a:ℕ), classical.choice _inst_2),
  rw a_lt_0_is_empty,
  apply set.bij_on_empty,
end

lemma singleton_is_finite (a:A): is_finite ({a}: set A) :=
begin
  unfold is_finite,
  use 1,
  use (λ (b:ℕ ), a),
  rw a_lt_1_is_zero_set,
  rw set.bij_on_singleton,
end

lemma lt_succ_n_eq_lt_n_or_eq_n (a n: ℕ): a < n.succ ↔ a < n ∨ a = n :=
begin
  sorry,
end

lemma subset_of_lt_n_is_bij_to_lt_n (n: ℕ) {s2: set ℕ} (subs: s2 ⊆ (set_of (λ (a:ℕ), a < n))): ∃ (n': ℕ) (f': ℕ → ℕ), set.bij_on f' s2 (set_of (λ (a:ℕ), a < n')) :=
begin
  induction n with n' ih generalizing s2,
  rw a_lt_0_is_empty at subs,
  have s2_empty: s2 = ∅,
  rw ← set.subset_empty_iff,
  exact subs,
  use 0,
  use (λ (a:ℕ), 0),
  rw s2_empty,
  rw a_lt_0_is_empty,
  apply set.bij_on_empty,

  by_cases n'_member: n' ∈ s2,
  let s2':= s2 \ {n'},
  have s2'_fin: ∃ (n' : ℕ) (f' : ℕ → ℕ), set.bij_on f' s2' {a : ℕ | a < n'},
  apply ih,
  rw set.subset_def,
  intro x,
  intro x_s2,
  rw set.mem_set_of,

  rw set.subset_def at subs,

  admit,
  rcases s2'_fin with ⟨n_s2', f_s2',bij_s2'⟩,
  use n_s2'+1,
  use (λ (a:ℕ ), if a < n_s2' then f_s2' a else n_s2'),
  apply set.bij_on.mk,
  unfold set.maps_to,
  intro x,
  intro x_s2,
  by_cases x_lt_n_s2': x < n_s2',
  rw if_pos x_lt_n_s2',
  admit,
  rw if_neg x_lt_n_s2',
  rw member_set_of_iff_pred,
  rw nat.lt_succ_iff,
  admit,
  unfold set.surj_on,
  rw set.subset_def,
  intro x,
  rw member_set_of_iff_pred,
  rw lt_succ_n_eq_lt_n_or_eq_n,
  intro h,
  cases h,

  admit,

  -- not member
  apply ih,
  rw set.subset_def,
  rw set.subset_def at subs,
  intro x,
  intro x_s2,
  rw member_set_of_iff_pred,
  have subs_x: x ∈ {a : ℕ | a < n'.succ},
  apply subs,
  apply x_s2,

  rw member_set_of_iff_pred at subs_x,
  
  rw lt_succ_n_eq_lt_n_or_eq_n at subs_x,
  cases subs_x,
  exact subs_x,

  exfalso,
  rw subs_x at x_s2,
  exact absurd x_s2 n'_member,
end

lemma subset_of_fin_is_fin (s1 s2: set A) (subs: s2 ⊆  s1) (s1_fin: is_finite s1): is_finite s2 :=
begin
  unfold is_finite at s1_fin,
  rcases s1_fin with ⟨n_s1, f_s1, f_s1_bij⟩,
  unfold is_finite,
  let s2_pred:= set_of (λ (a:ℕ), a < n_s1 ∧ f_s1 a ∈ s2),
  have s2_pred_bij: set.bij_on f_s1 s2_pred s2,
  apply set.bij_on.mk,
  unfold set.maps_to,
  intro x,
  rw member_set_of_iff_pred,
  intro h,
  cases h,
  exact h_right,

  unfold set.inj_on,
  intros x1 x1_mem x2 x2_mem,
  have f_s1_inj: set.inj_on f_s1 {a : ℕ | a < n_s1},
  apply set.bij_on.inj_on f_s1_bij,
  unfold set.inj_on at f_s1_inj,
  apply f_s1_inj,
  rw member_set_of_iff_pred at x1_mem,
  rw member_set_of_iff_pred,
  cases x1_mem,
  exact x1_mem_left,
  rw member_set_of_iff_pred,
  rw member_set_of_iff_pred at x2_mem,
  cases x2_mem,
  exact x2_mem_left,

  have f_s1_surj: set.surj_on f_s1 {a : ℕ | a < n_s1} s1,
  apply set.bij_on.surj_on f_s1_bij,
  unfold set.surj_on,
  rw set.subset_def,
  intro a,
  rw set.mem_image_iff_bex,
  intro a_s2,

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

lemma disjoint_union_preserves_fin (s1 s2: set A)  (s1_fin: is_finite s1) (s2_fin: is_finite s2) (disj: disjoint s1 s2): is_finite (s1 ∪ s2) :=
begin
  unfold is_finite,
  unfold is_finite at s1_fin,
  unfold is_finite at s2_fin,
  rcases s1_fin with ⟨n_s1, f_s1, f_s1_bij⟩,
  rcases s2_fin with ⟨n_s2, f_s2, f_s2_bij⟩,
  use (n_s1 + n_s2),
  use ( λ (a: ℕ), if a < n_s1 then f_s1 a else f_s2 (a - n_s1)),
  apply set.bij_on.mk,
  admit,

  unfold set.inj_on,
  intros x1 x1_mem x2 x2_mem,
  by_cases x1_lt_n_s1: x1 < n_s1,
  by_cases x2_lt_n_s1: x2 < n_s1,
  rw if_pos x1_lt_n_s1,
  rw if_pos x2_lt_n_s1,
  have f_s1_inj: set.inj_on f_s1 {a : ℕ | a < n_s1},
  apply set.bij_on.inj_on f_s1_bij,
  unfold set.inj_on at f_s1_inj,
  apply f_s1_inj,
  rw member_set_of_iff_pred,
  exact x1_lt_n_s1,
  rw member_set_of_iff_pred,
  exact x2_lt_n_s1,

  rw if_pos x1_lt_n_s1,
  rw if_neg x2_lt_n_s1,
end

lemma disjoint_difference_s1_s2_with_s2 (s1 s2: set A): disjoint (s1 \ s2) s2 :=
begin
  rw set.disjoint_iff_inter_eq_empty,
  rw set.ext_iff,
  intro x,
  rw set.mem_inter_iff,
  rw set.mem_diff,
  tauto,
end

lemma union_preserves_fin (s1 s2: set A) (s1_fin: is_finite s1) (s2_fin: is_finite s2): is_finite (s1 ∪ s2) :=
begin
  by_cases int: s1 ∩ s2 = ∅,
  apply disjoint_union_preserves_fin s1 s2 s1_fin s2_fin,
  rw set.disjoint_iff_inter_eq_empty,
  exact int,

  rw ← set.diff_union_self,
  apply disjoint_union_preserves_fin (s1 \ s2) s2,
  apply difference_preserves_fin s1 s2 s1_fin s2_fin,
  apply s2_fin,
  apply disjoint_difference_s1_s2_with_s2,
end

end operations

section size
variables {A: Type} [decidable_eq A][nonempty A]

lemma equivalent_set_size_is_unique (n1 n2: ℕ) (s: set A)(f1 f2: ℕ → A) (bij_1: set.bij_on f1 (set_of (λ a, a < n1)) s) (bij_2: set.bij_on f2 (set_of (λ a, a < n2)) s): n1 = n2 :=
begin
  sorry,
end

noncomputable def size (s: set A) (fin: is_finite s): ℕ :=
begin
  unfold is_finite at fin,
  exact classical.some fin,
end

end size