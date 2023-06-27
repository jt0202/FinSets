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
  rw nat.lt_succ_iff,
  exact le_iff_lt_or_eq,
end

lemma set_lt_n1_plus_n2_is_union (n1 n2: ℕ): {a | a < (n1 + n2)} = {a| a < n1} ∪ {a | a ≥ n1 ∧ a < n1 + n2} :=
begin
  sorry,
end

lemma subset_of_lt_n_is_bij_to_lt_n (n: ℕ) {s2: set ℕ} (subs: s2 ⊆ (set_of (λ (a:ℕ), a < n))): ∃ (n': ℕ) (f': ℕ → ℕ), set.bij_on f' (set_of (λ (a:ℕ), a < n')) s2:=
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
  have s2'_fin: ∃ (n' : ℕ) (f' : ℕ → ℕ), set.bij_on f' {a : ℕ | a < n'} s2',
  apply ih,
  rw set.subset_def,
  intro x,
  intro x_s2',
  rw set.mem_set_of,

  rw set.subset_def at subs,
  have h:  x ∈ {a : ℕ | a < n'.succ},
  apply subs,
  have s2'_subs_s2: s2' ⊆ s2,
  rw set.subset_def,
  intro x,
  rw set.mem_diff,
  intro h',
  cases h',
  exact h'_left,
  rw set.subset_def at s2'_subs_s2,
  apply s2'_subs_s2,
  exact x_s2',

  rw set.mem_diff at x_s2',
  simp at x_s2',
  cases x_s2',
  rw member_set_of_iff_pred at h,
  rw lt_succ_n_eq_lt_n_or_eq_n at h,
  cases h,
  exact h,
  exfalso,
  exact absurd h x_s2'_right,

  rcases s2'_fin with ⟨n_s2', f_s2',bij_s2'⟩,
  use n_s2'+1,
  use (λ (a:ℕ ), if a < n_s2' then f_s2' a else n'),

  have s2_union: s2 = s2' ∪ {n'},
  rw set.ext_iff,
  simp [s2'],
  intro x,
  split,
  intro h,
  right,
  exact h,
  intro h,
  cases h,
  rw h,
  exact n'_member,
  exact h,

  rw s2_union,
  rw set_lt_n1_plus_n2_is_union,

  apply set.bij_on.union,
  apply set.bij_on.congr,
  apply bij_s2',
  unfold set.eq_on,
  intros x x_lt_n_s1,
  rw member_set_of_iff_pred at x_lt_n_s1,
  rw if_pos x_lt_n_s1,

  have sing: {a : ℕ | a ≥ n_s2' ∧ a < n_s2' + 1} = {n_s2'},
  rw set.ext_iff,
  intro x,
  rw member_set_of_iff_pred,
  simp,
  rw lt_succ_n_eq_lt_n_or_eq_n,
  split,
  intro h,
  cases h,
  cases h_right,
  admit,
  exact h_right,
  intro h,
  split,
  apply nat.le_of_eq (eq.symm h),
  right,
  exact h,
  rw sing,
  rw set.bij_on_singleton,
  have ns2_lt_ns2: ¬ n_s2' < n_s2',
  apply nat.lt_irrefl,
  rw if_neg ns2_lt_ns2,
  
  -- set.inj on combined function
  unfold set.inj_on,
  intros x1 x1_mem x2 x2_mem,
  rw set.mem_union at x1_mem,
  rw member_set_of_iff_pred at x1_mem,
  rw member_set_of_iff_pred at x1_mem,
  
  rw set.mem_union at x2_mem,
  rw member_set_of_iff_pred at x2_mem,
  rw member_set_of_iff_pred at x2_mem,

  cases x1_mem,
  cases x2_mem,
  rw if_pos x1_mem,
  rw if_pos x2_mem,
  have inj_s2': set.inj_on f_s2' {a : ℕ | a < n_s2'},
  apply set.bij_on.inj_on bij_s2',
  unfold set.inj_on at inj_s2',
  apply inj_s2',
  rw member_set_of_iff_pred,
  exact x1_mem,
  rw member_set_of_iff_pred,
  exact x2_mem,

  rw if_pos x1_mem,
  
end

lemma bij_on_preserved_on_subset {s1 s2: set A} {n:ℕ } (f: ℕ → A) (bij: set.bij_on f ({a : ℕ | a < n}) s1 ) (subs: s2 ⊆ s1): set.bij_on f {a : ℕ | a < n ∧ f a ∈ s2} s2 :=
begin
  apply set.bij_on.mk,
  --maps to
  unfold set.maps_to,
  intro x,
  rw member_set_of_iff_pred,
  intro h,
  cases h,
  exact h_right,

  --inj_on
  unfold set.inj_on,
  intros x1 x1_mem x2 x2_mem,
  have f_s1_inj: set.inj_on f {a : ℕ | a < n},
  apply set.bij_on.inj_on bij,
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

  --surj_on
  have f_s1_surj: set.surj_on f {a : ℕ | a < n} s1,
  apply set.bij_on.surj_on bij,
  unfold set.surj_on,
  rw set.subset_def,
  intro b,
  rw set.mem_image_iff_bex,
  intro b_s2,
  unfold set.surj_on at f_s1_surj,
  rw set.subset_def at f_s1_surj,
  have b_image: b ∈ f '' {a : ℕ | a < n},
  apply f_s1_surj,
  rw set.subset_def at subs,
  apply subs,
  exact b_s2,
  rw set.mem_image_iff_bex at b_image,
  rcases b_image with ⟨b_pre_el, b_pre_el_in_s1, b_pre_el_proof⟩,
  use b_pre_el,
  split,
  rw member_set_of_iff_pred,
  split,
  rw member_set_of_iff_pred at b_pre_el_in_s1,
  exact b_pre_el_in_s1,
  rw b_pre_el_proof,
  exact b_s2,
  exact b_pre_el_proof,
end

lemma subset_of_fin_is_fin (s1 s2: set A) (subs: s2 ⊆  s1) (s1_fin: is_finite s1): is_finite s2 :=
begin
  unfold is_finite at s1_fin,
  rcases s1_fin with ⟨n_s1, f_s1, f_s1_bij⟩,
  unfold is_finite,
  let s2_pred:= set_of (λ (a:ℕ), a < n_s1 ∧ f_s1 a ∈ s2),
  have s2_pred_bij: set.bij_on f_s1 s2_pred s2,
  apply bij_on_preserved_on_subset f_s1 f_s1_bij subs,
  have subN_to_normal_form: ∃ (n : ℕ) (f : ℕ → ℕ), set.bij_on f {a : ℕ | a < n} s2_pred,
  apply subset_of_lt_n_is_bij_to_lt_n n_s1,
  rw set.subset_def,
  intro x,
  rw member_set_of_iff_pred,
  rw member_set_of_iff_pred,
  intro h,
  cases h,
  exact h_left,
  rcases subN_to_normal_form with ⟨n, f, bij_2⟩,
  use n,
  use f_s1 ∘ f,
  apply set.bij_on.comp s2_pred_bij,
  apply bij_2,
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
  rw set_lt_n1_plus_n2_is_union,
  apply set.bij_on.union,

  -- bij on s1
  rw set.eq_on.bij_on_iff,
  apply f_s1_bij,
  unfold set.eq_on,
  intro x,
  rw member_set_of_iff_pred,
  intro x_n_s1,
  rw if_pos x_n_s1,

  -- bij on lifted s2
  apply set.bij_on.mk,
  -- maps to lifted s2
  unfold set.maps_to,
  intro x,
  rw member_set_of_iff_pred,
  intro h,
  cases h,
  have n_x_lt_ns1: ¬ x < n_s1,
  push_neg,
  apply h_left,
  rw if_neg n_x_lt_ns1,
  have f_s2_maps_to: set.maps_to f_s2 {a : ℕ | a < n_s2} s2,
  apply set.bij_on.maps_to f_s2_bij,
  unfold set.maps_to at f_s2_maps_to,
  apply f_s2_maps_to,
  rw member_set_of_iff_pred,
  have h: n_s1 + (x - n_s1) < n_s1 + n_s2,
  rw nat.add_sub_of_le h_left,
  exact h_right,
  apply nat.lt_of_add_lt_add_left h,

  -- inj on lifted s2
  unfold set.inj_on,
  intro x1,
  rw member_set_of_iff_pred,
  intro x1_mem,
  intro x2,
  rw member_set_of_iff_pred,
  intro x2_mem,

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