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

lemma is_finite_to_is_finite_n (s: set A) (fin: is_finite s): ∃ (n:ℕ), is_finite_n s n :=
begin
  unfold is_finite_n,
  unfold is_finite at fin,
  exact fin,
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

lemma ge_n_and_le_n_succ_eq_n {x n: ℕ}: x ≥ n ∧ x < n +1 → x = n :=
begin
  intro h,
  cases h,
  rw lt_succ_n_eq_lt_n_or_eq_n at h_right,
  cases h_right,
  exfalso,
  rw ← not_le at h_right,
  exact absurd h_left h_right,
  exact h_right,
end

lemma set_lt_n1_plus_n2_is_union (n1 n2: ℕ): {a | a < (n1 + n2)} = {a| a < n1} ∪ {a | a ≥ n1 ∧ a < n1 + n2} :=
begin
  rw set.ext_iff,
  intro x,
  rw set.mem_union,
  repeat {rw member_set_of_iff_pred},
  split,
  intro h,
  by_cases x_n1: x < n1,
  left,
  exact x_n1,
  push_neg at x_n1,
  right,
  split,
  exact x_n1,
  exact h,

  intro h,
  cases h,
  cases n2,
  rw nat.add_zero,
  exact h,
  rw ← nat.add_zero x,
  apply nat.add_lt_add,
  exact h,
  apply nat.zero_lt_succ,
  cases h,
  exact h_right,
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

  -- largest element in subset
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
  rw ← not_le at h_right,
  exfalso,
  exact absurd h_left h_right,
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
  have x2_eq_n_s2': x2 = n_s2',
  apply ge_n_and_le_n_succ_eq_n x2_mem,

  simp [x2_eq_n_s2'],
  intro h,
  have f_s2'_maps_to: set.maps_to f_s2' {a : ℕ | a < n_s2'} s2',
  apply set.bij_on.maps_to bij_s2',
  unfold set.maps_to at f_s2'_maps_to,
  exfalso,
  have x1_maps_to: x1 ∈ {a : ℕ | a < n_s2'} → f_s2' x1 ∈ s2',
  apply f_s2'_maps_to,

  rw h at x1_maps_to,
  simp at x1_maps_to,
  apply x1_maps_to,
  exact x1_mem,

  have x1_eq_n_s2': x1 = n_s2',
  apply ge_n_and_le_n_succ_eq_n x1_mem,
  simp [x1_eq_n_s2'],
  cases x2_mem,
  rw if_pos x2_mem,
  have f_s2'_maps_to: set.maps_to f_s2' {a : ℕ | a < n_s2'} s2',
  apply set.bij_on.maps_to bij_s2',
  unfold set.maps_to at f_s2'_maps_to,
  intro h,
  exfalso,
  have x2_maps_to: x2 ∈ {a : ℕ | a < n_s2'} → f_s2' x2 ∈ s2',
  apply f_s2'_maps_to,
  rw ←  h at x2_maps_to,
  simp at x2_maps_to,
  apply x2_maps_to,
  exact x2_mem,
  have x2_eq_n_s2': x2 = n_s2',
  apply ge_n_and_le_n_succ_eq_n x2_mem,
  simp [x2_eq_n_s2'],

  --largest element not in subset
  apply ih,
  rw set.subset_def,
  rw set.subset_def at subs,
  intros x h,
  rw member_set_of_iff_pred,
  have x_subs: x ∈ {a : ℕ | a < n'.succ},
  apply subs,
  exact h,

  rw member_set_of_iff_pred at x_subs,
  rw lt_succ_n_eq_lt_n_or_eq_n at x_subs,
  cases x_subs,
  exact x_subs,
  rw x_subs at h,
  exfalso,
  exact absurd h n'_member,
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

lemma sub_at_both_sides (n m k: ℕ ) (n_ge_k: n ≥ k) (m_ge_k: m ≥ k):n = m ↔ n -k = m -k :=
begin
  split,
  intro h,
  rw h,

  induction k with k ih,
  rw nat.sub_zero,
  rw nat.sub_zero,
  intro h,
  exact h,

  intro h,
  apply ih,
  rw nat.sub_succ at h,
  rw nat.sub_succ at h,
end

lemma sub_lt_to_other_side (n m k: ℕ): n - m < k ↔ n < m + k :=
begin
  induction m with m' ih,
  rw nat.sub_zero,
  rw nat.zero_add,

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
  cases x1_mem,
  rw ge_iff_le at x1_mem_left,
  rw ← not_lt at x1_mem_left,
  rw if_neg x1_mem_left,
  cases x2_mem,
  rw ge_iff_le at x2_mem_left,
  rw ← not_lt at x2_mem_left,
  rw if_neg x2_mem_left,

  have f_s2_inj: set.inj_on f_s2 {a : ℕ | a < n_s2},
  apply set.bij_on.inj_on f_s2_bij,
  unfold set.inj_on at f_s2_inj,
  intro h,
  rw sub_at_both_sides x1 x2 n_s1,
  apply f_s2_inj,
  rw member_set_of_iff_pred,
  rw sub_lt_to_other_side,
  exact x1_mem_right,
  rw member_set_of_iff_pred,
  rw sub_lt_to_other_side,
  exact x2_mem_right,
  exact h,
  rw not_lt at x1_mem_left,
  exact x1_mem_left,
  rw not_lt at x2_mem_left,
  exact x2_mem_left,
  
  -- surj_on lifted s2
  unfold set.surj_on,
  rw set.subset_def,
  intro x,
  rw set.mem_image_iff_bex,
  intro x_s2,
  have f_s2_surj: set.surj_on f_s2 {a : ℕ | a < n_s2} s2,
  apply set.bij_on.surj_on f_s2_bij,
  unfold set.surj_on at f_s2_surj,
  rw set.subset_def at f_s2_surj,
  simp_rw set.mem_image_iff_bex at f_s2_surj,
  have x_f_s2_surj: (∃ (x_1 : ℕ) (_x : x_1 ∈ {a : ℕ | a < n_s2}), f_s2 x_1 = x),
  apply f_s2_surj,
  exact x_s2,
  rcases x_f_s2_surj with ⟨preimage, member_proof, x_surj⟩,
  use preimage + n_s1,
  split,
  rw member_set_of_iff_pred,
  rw member_set_of_iff_pred at member_proof,
  split,
  unfold ge,
  apply nat.le_add_left,
  rw nat.add_comm n_s1 _,
  apply nat.add_lt_add_right member_proof,
  have n_if_con: ¬ preimage + n_s1 < n_s1,
  push_neg,
  rw nat.add_comm,
  apply nat.le_add_right,
  rw if_neg n_if_con,
  rw nat.add_sub_cancel,
  exact x_surj,

  -- inj on both
  unfold set.inj_on,
  have f_s1_inj: set.inj_on f_s1 {a : ℕ | a < n_s1},
  apply set.bij_on.inj_on f_s1_bij,
  unfold set.inj_on at f_s1_inj,
  have f_s2_inj: set.inj_on f_s2 {a : ℕ | a < n_s2},
  apply set.bij_on.inj_on f_s2_bij,
  unfold set.inj_on at f_s2_inj,
  have f_s1_maps_to: set.maps_to f_s1 {a : ℕ | a < n_s1} s1,
  apply set.bij_on.maps_to f_s1_bij,
  unfold set.maps_to at f_s1_maps_to,
  have f_s2_maps_to: set.maps_to f_s2 {a : ℕ | a < n_s2} s2,
  apply set.bij_on.maps_to f_s2_bij,
  unfold set.maps_to at f_s2_maps_to,
  rw set.disjoint_iff at disj,
  rw set.subset_def at disj,
  simp at disj,
  intros x1 x1_mem x2 x2_mem,
  rw set.mem_union at x1_mem,
  rw member_set_of_iff_pred at x1_mem,
  rw member_set_of_iff_pred at x1_mem,
  rw set.mem_union at x2_mem,
  rw member_set_of_iff_pred at x2_mem,
  rw member_set_of_iff_pred at x2_mem,
  cases x1_mem,
  rw if_pos x1_mem,
  cases x2_mem,
  rw if_pos x2_mem,
  apply f_s1_inj,
  rw member_set_of_iff_pred,
  exact x1_mem,
  rw member_set_of_iff_pred,
  exact x2_mem,
  cases x2_mem,
  simp at x2_mem_left,
  rw ←  not_lt at x2_mem_left,
  rw if_neg x2_mem_left,
  intro h,
  exfalso,
  have f_s1_x1_in_s1: f_s1 x1 ∈ s1,
  apply f_s1_maps_to,
  rw member_set_of_iff_pred,
  exact x1_mem,
  have f_s2_x2_n_s1_in_s2: f_s2 (x2 - n_s1) ∈ s2,
  apply f_s2_maps_to,
  rw member_set_of_iff_pred,
  rw sub_lt_to_other_side,
  exact x2_mem_right,
  rw ← h at f_s2_x2_n_s1_in_s2,
  apply disj (f_s1 x1) f_s1_x1_in_s1 f_s2_x2_n_s1_in_s2,
  cases x1_mem,
  simp at x1_mem_left,
  rw ← not_lt at x1_mem_left,
  rw if_neg x1_mem_left,
  cases x2_mem,
  rw if_pos x2_mem,
  intro h,
  exfalso,
  have f_s1_x2_s1: f_s1 x2 ∈ s1,
  apply f_s1_maps_to,
  rw member_set_of_iff_pred,
  exact x2_mem,
  have f_s2_x1_ns1_s2: f_s2 (x1 - n_s1) ∈ s2,
  apply f_s2_maps_to,
  rw member_set_of_iff_pred,
  rw sub_lt_to_other_side,
  exact x1_mem_right,
  rw h at f_s2_x1_ns1_s2,
  apply disj (f_s1 x2) f_s1_x2_s1 f_s2_x1_ns1_s2,
  cases x2_mem,
  simp at x2_mem_left,
  rw ← not_lt at x2_mem_left,
  rw if_neg x2_mem_left,
  intro h,
  rw sub_at_both_sides x1 x2 n_s1,
  apply f_s2_inj,
  rw member_set_of_iff_pred,
  rw sub_lt_to_other_side,
  exact x1_mem_right,
  rw member_set_of_iff_pred,
  rw sub_lt_to_other_side,
  exact x2_mem_right,
  exact h,

  rw not_lt at x1_mem_left,
  exact x1_mem_left,
  rw not_lt at x2_mem_left,
  exact x2_mem_left,
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

noncomputable def size (s: set A) (fin: is_finite s): ℕ := classical.some fin

lemma size_is_is_fin_n_1 (s: set A) (fin: is_finite s) (n: ℕ) (h: size s fin = n): is_finite_n s n:=
begin
  rw ← h,
  apply classical.some_spec,
end

lemma no_bijection_between_different_lt_n (n1 n2: ℕ) (h: n1 ≠ n2) : ∀ (f: ℕ → ℕ ), ¬ set.bij_on f {x| x < n1} {x| x < n2} :=
begin
  sorry,
end


lemma size_is_is_fin_n_2 (s: set A) (n: ℕ )(fin_n: is_finite_n s n) (fin: is_finite s): size s fin = n :=
begin
  dunfold size,
  by_contradiction,
  have h': ∃ (n'), n ≠ n' ∧  classical.some fin = n',
  by_contradiction h',
  push_neg at h',
  have self_non_equal: classical.some fin ≠ classical.some fin,
  apply h',
  apply ne.symm,
  rw ne.def,
  exact h,
  apply self_non_equal,
  refl,

  rcases h' with ⟨n', fin_n'⟩,
  rcases fin_n' with ⟨n'_neq_n, class_n'⟩,
  have fin_n': is_finite_n s n',
  apply size_is_is_fin_n_1 s fin n' class_n',
  unfold is_finite_n at fin_n,
  rcases fin_n with ⟨f, bij_f⟩,
  unfold is_finite_n at fin_n',
  rcases fin_n' with ⟨f', bij_f'⟩,
  
  -- construct inverse of f' on s
  have bij_f'_inv: set.bij_on (function.inv_fun_on f' {a : ℕ | a < n'}) s {a : ℕ | a < n'},
  have f'_inv_inv_on: set.inv_on (function.inv_fun_on f' {a : ℕ | a < n'}) f' {a : ℕ | a < n'} s,
  apply set.bij_on.inv_on_inv_fun_on bij_f',
  apply set.inv_on.bij_on,
  apply set.inv_on.symm,
  exact f'_inv_inv_on,
  unfold set.inv_on at f'_inv_inv_on,
  cases f'_inv_inv_on,
  apply set.left_inv_on.maps_to,  
  apply f'_inv_inv_on_left,
  apply set.bij_on.surj_on bij_f',
  apply set.bij_on.maps_to bij_f',

  
  have bij_n: set.bij_on (function.inv_fun_on f' {a : ℕ | a < n'} ∘ f) {a : ℕ | a < n} {a : ℕ | a < n'},
  apply set.bij_on.comp bij_f'_inv bij_f,

  apply no_bijection_between_different_lt_n n n' n'_neq_n (function.inv_fun_on f' {a : ℕ | a < n'} ∘ f),
  exact bij_n,
end

lemma size_is_is_fin_n (s: set A) (fin: is_finite s) (n: ℕ): size s fin = n ↔ is_finite_n s n :=
begin
  split,
  apply size_is_is_fin_n_1,
  intro h,
  apply size_is_is_fin_n_2,
  exact h,
end


end size