import tactic.rcases data.quot tactic.nth_rewrite tactic.push_neg

namespace listSet
def same_members (A: Type) (l1 l2: list A): Prop := ∀ (a:A), a ∈ l1 ↔ a ∈ l2
variables {A: Type} [decidable_eq A]

lemma same_members_refl: reflexive(same_members A):=
begin
  unfold reflexive,
  unfold same_members,
  cc,
end

lemma same_members_symm: symmetric (same_members A):=
begin
  unfold symmetric,
  unfold same_members,
  intros x y h a,
  apply iff.symm,
  apply h,
end

lemma same_members_trans: transitive (same_members A) :=
begin
  unfold transitive,
  unfold same_members,
  intros x y z h1 h2 a,
  rw h1,
  rw h2,
end

lemma same_members_as_nil_is_nil (l: list A) (eqv: same_members A list.nil l): l = list.nil :=
begin
  cases l,
  refl,

  unfold same_members at eqv,
  simp at eqv,
  exfalso,
  apply eqv l_hd,
  left,
  refl,
end

lemma member_preserved (a:A) (l1 l2: list A) (eqv: same_members A l1 l2): (a ∈ l1) = (a ∈ l2) :=
begin
  unfold same_members at eqv,
  simp,
  apply eqv,
end

def member_bool:A -> list A → bool
| a list.nil := ff
| a (hd::tl) := a = hd ∨ (member_bool a tl) = tt

lemma member_iff_member_bool (a:A) (l:list A): a ∈ l ↔ member_bool a l = tt:=
begin
  induction l with hd tl ih,
  unfold member_bool,
  simp,

  rw list.mem_cons_iff,
  unfold member_bool,
  simp [ih],
end

lemma not_eq_tt_implies_eq_ff (f: A → bool) (a: A): ¬(f a = tt) → f a = ff :=
begin
  intro h,
  cases (f a),
  refl,
  exact false.elim (h rfl),
end

lemma member_bool_preserved (a:A) (l1 l2: list A) (eqv: same_members A l1 l2): (member_bool a l1) = (member_bool a l2) :=
begin
  unfold same_members at eqv,
  by_cases mem_a_l1: member_bool a l1 = tt,
  rw mem_a_l1 ,
  rw ←  member_iff_member_bool at mem_a_l1,
  rw eqv at mem_a_l1,
  rw member_iff_member_bool at mem_a_l1,
  rw mem_a_l1,

  have mem_ff: member_bool a l1 = ff,
  apply not_eq_tt_implies_eq_ff ,
  apply mem_a_l1,
  rw ←  member_iff_member_bool at mem_a_l1,
  rw eqv at mem_a_l1,
  rw member_iff_member_bool at mem_a_l1,
  rw mem_ff,
  have mem_ff_2: member_bool a l2 = ff,
  apply not_eq_tt_implies_eq_ff ,
  apply mem_a_l1,
  rw ← mem_ff_2,
end

def union (l1 l2: list A) : list A := l1 ++ l2

lemma in_union_iff_in_either (l1 l2: list A) (a:A): a ∈ union l1 l2 ↔ a ∈ l1 ∨ a ∈ l2 :=
begin
  unfold union,
  induction l1 with a' l ih,
  rw list.nil_append,
  rw list.mem_nil_iff,
  simp,

  rw list.mem_append,
end

lemma union_preserved (l1 l2 l3 l4: list A) (eqv12: same_members A l1 l2) (eqv34: same_members A l3 l4): quot.mk (same_members A) (union l1 l3) = quot.mk (same_members A) (union l2 l4):=
begin
  apply quot.sound,
  unfold same_members,
  intro a,
  rw in_union_iff_in_either,
  rw in_union_iff_in_either,
  unfold same_members at eqv12,
  unfold same_members at eqv34,
  rw eqv12,
  rw eqv34,
end

lemma union_preserved_1 (l1 l2 l: list A) (eqv: same_members A l1 l2): quot.mk (same_members A) (union l1 l) = quot.mk (same_members A) (union l2 l) :=
begin
  apply union_preserved,
  apply eqv,
  apply same_members_refl,
end

lemma union_preserved_2 (l l3 l4: list A) (eqv: same_members A l3 l4): quot.mk (same_members A) (union l l3) = quot.mk (same_members A) (union l l4):=
begin
  apply union_preserved,
  apply same_members_refl,
  apply eqv,
end

def comprehension: (A → bool) → list A → list A
| φ list.nil := list.nil
| φ (hd::tl) := if φ hd = tt then hd::(comprehension φ tl) else (comprehension φ tl)

lemma comprehension_semantics (φ: A → bool) (l: list A) (a: A): a ∈  (comprehension φ l) ↔ a ∈ l ∧  φ a = tt :=
begin
  induction l with hd tl ih,
  unfold comprehension,
  simp,

  unfold comprehension,
  by_cases hd_phi: φ hd = tt,
  rw if_pos hd_phi,
  rw list.mem_cons_eq,
  by_cases a_hd: a = hd,
  rw a_hd,
  simp,
  apply hd_phi,
  simp [a_hd],
  apply ih,

  rw if_neg hd_phi,
  rw ih,
  rw list.mem_cons_eq,
  simp,
  intro a_phi,
  have a_neq_hd: a ≠ hd,
  by_contradiction,
  rw h at a_phi,
  exact absurd a_phi hd_phi,
  simp [a_neq_hd],
end

lemma comprehension_preserved (φ: A → bool) (l1 l2:list A) (eqv: same_members A l1 l2): quot.mk (same_members A) (comprehension φ l1) = quot.mk (same_members A) (comprehension φ l2):=
begin
  apply quot.sound,
  unfold same_members,
  intro a,
  rw comprehension_semantics,
  rw comprehension_semantics,
  unfold same_members at eqv,
  rw eqv,
end

def disjoint (X Y: list A): Prop := ∀ (a: A), ¬( a ∈ X ∧ a ∈ Y)

def set_size: list A -> ℕ
| list.nil := 0
| (hd:: tl) := if hd ∈ tl then set_size tl else 1 + set_size tl

lemma ne_of_not_eq (a b: A): ¬ (a = b) ↔ a ≠ b :=
begin
  cc,
end

def delete: A -> list A -> list A
| a list.nil := list.nil
| a (hd::tl) := if a = hd then (delete a tl) else hd::(delete a tl)

lemma delete_semantics (a: A) (l: list A): ∀ (b: A), b ∈ delete a l ↔ b ∈ l ∧ b ≠ a:=
begin
  intro b,
  induction l with hd tl ih,
  unfold delete,
  simp,

  unfold delete,
  by_cases a_hd: a = hd,
  rw if_pos a_hd,
  rw ih,
  simp,
  intro h,
  rw a_hd at h,
  simp [h],

  rw if_neg a_hd,
  simp,
  rw ih,
  rw ne_of_not_eq,
  by_cases b_hd: b = hd,
  rw b_hd,
  simp,
  by_contradiction,
  rw h at a_hd,
  simp at a_hd,
  apply a_hd,
  simp[b_hd],
end



lemma deleting_non_member_doesnt_change (a: A) (X: list A) (mem: ¬ a ∈ X): X = delete a X :=
begin
  induction X with hd tl ih,
  unfold delete,

  unfold delete,
  simp at mem,
  push_neg at mem,
  cases mem,
  have n_a_hd: ¬ a = hd,
  rw ne_of_not_eq,
  apply mem_left,

  rw if_neg n_a_hd,
  rw ← ih,
  apply mem_right,
end



lemma delete_member_is_size_plus_one (a: A) (X: list A) (mem: a ∈ X): set_size X = set_size (delete a X) + 1 :=
begin
  induction X with hd tl ih,
  exfalso,
  simp at mem,
  apply mem,

  unfold set_size,
  by_cases a_hd: a = hd,
  by_cases hd_tl: hd ∈ tl,
  rw if_pos,
  rw ← a_hd,
  unfold delete,
  simp,
  apply ih,
  rw a_hd,
  apply hd_tl,
  apply hd_tl,

  rw if_neg hd_tl,
  rw ← a_hd,
  unfold delete,
  simp,
  rw ← deleting_non_member_doesnt_change a tl,
  rw nat.add_comm,
  rw a_hd,
  apply hd_tl,

  unfold delete,
  rw if_neg a_hd,
  unfold set_size,
  by_cases hd_tl: hd ∈ tl,
  rw if_pos hd_tl,
  have hd_delete: hd ∈ delete a tl,
  rw delete_semantics,
  split,
  apply hd_tl,
  rw ne_of_not_eq at a_hd,
  apply ne.symm,
  apply a_hd,
  rw if_pos hd_delete,
  apply ih,
  cases mem,
  exfalso,
  exact absurd mem a_hd,
  apply mem,

  rw if_neg hd_tl,
  have hd_delete: ¬ hd ∈ delete a tl,
  rw delete_semantics,
  simp,
  intro h,
  exact absurd h hd_tl,
  rw if_neg hd_delete,
  rw ih,
  rw nat.add_assoc,

  cases mem,
  exact absurd mem a_hd,
  apply mem,
end

lemma set_size_preserved (l1 l2: list A) (eqv: same_members A l1 l2): set_size l1 = set_size l2 :=
begin
  induction l1 with hd tl ih generalizing l2,
  rw same_members_as_nil_is_nil l2,
  apply eqv,
  
  unfold set_size,
  by_cases hd_tl: hd ∈ tl,
  rw if_pos hd_tl,
  apply ih,
  unfold same_members,
  unfold same_members at eqv,
  intro a,
  rw ← eqv,
  rw list.mem_cons_eq,
  split,
  intro h,
  right,
  exact h,
  intro h,
  cases h,
  rw ← h at hd_tl,
  apply hd_tl,
  apply h,

  rw if_neg hd_tl,

  rw delete_member_is_size_plus_one hd l2,
  rw nat.add_comm,
  rw ih,
  unfold same_members,
  intro a,
  rw delete_semantics,
  unfold same_members at eqv,
  rw ← eqv,
  simp,
  rw or_and_distrib_right,
  simp,
  intro a,
  by_contradiction,
  rw ←  h at hd_tl,
  exact absurd a hd_tl,

  unfold same_members at eqv,
  simp at eqv,
  rw ← eqv,
  left,
  refl,
end

end listSet

def finSet (A: Type):= quot (listSet.same_members A)

variables {A: Type} [decidable_eq A]

def member (a:A) (X: finSet A): Prop := quot.lift (λ (l: list A), a ∈ l) (listSet.member_preserved a) X

def member_bool (a:A) (X: finSet A): bool := quot.lift (λ (l: list A), listSet.member_bool a l) (listSet.member_bool_preserved a) X

def emptySet: finSet A := quot.mk (listSet.same_members A) list.nil

def singleton (a:A): finSet A := quot.mk (listSet.same_members A) (a::list.nil)

lemma emptySet_has_no_members (a:A): member a emptySet = false :=
begin
  unfold emptySet,
  unfold member,
  simp,
end



lemma member_lift (a: A) (l: list A): member a (quot.mk (listSet.same_members A) l) ↔ a ∈ l :=
begin
  unfold member,
end

lemma member_singleton (a b:A): member b (singleton a) ↔ a = b :=
begin
  dunfold singleton,
  rw member_lift,
  simp,
  cc,
end

lemma member_iff_member_bool_tt (a: A) (X: finSet A): member a X ↔ member_bool a X = tt :=
begin
  apply quot.induction_on X,
  intro l,
  rw member_lift,
  unfold member_bool,
  apply listSet.member_iff_member_bool,
end

lemma neg_member_iff_member_bool_ff (a: A) (X: finSet A): ¬ member a X ↔ member_bool a X = ff :=
begin
  rw member_iff_member_bool_tt,
  simp,
end

lemma extensionality (X Y: finSet A): X = Y ↔ ∀ (a:A), member a X ↔ member a Y :=
begin
  split,
  intros h a,
  rw h,

  apply quot.induction_on₂ X Y,
  intros a b h,
  apply quot.sound,
  unfold listSet.same_members,
  intro a,
  simp [member_lift] at h,
  apply h,
end

def union (X Y: finSet A): finSet A := quot.lift₂ (λ ( X Y: list A), quot.mk (listSet.same_members A) (listSet.union X Y)) listSet.union_preserved_2 listSet.union_preserved_1 X Y

lemma union_lift (X Y: list A): quot.mk (listSet.same_members A) (listSet.union X Y) = union (quot.mk (listSet.same_members A) X) (quot.mk (listSet.same_members A) Y) :=
begin
  unfold union,
end

lemma in_union_iff_in_either (X Y: finSet A) (a:A): member a (union X Y) ↔ member a X ∨ member a Y :=
begin
  apply quot.induction_on₂ X Y,
  unfold union,
  unfold member,
  unfold listSet.union,
  apply list.mem_append,
end

lemma union_assoc (X Y Z: finSet A): union X (union Y Z) = union (union X Y) Z :=
begin
  rw extensionality,
  intro a,
  repeat{rw in_union_iff_in_either},
  rw or.assoc,
end

lemma union_comm (X Y: finSet A): union X Y = union Y X :=
begin
  rw extensionality,
  intro a,
  repeat{rw in_union_iff_in_either},
  rw or.comm,
end

lemma union_idem (X: finSet A): union X X = X :=
begin
  rw extensionality,
  intro a,
  rw in_union_iff_in_either,
  cc,
end

lemma union_with_empty_is_self (X: finSet A): union X emptySet = X :=
begin
  rw extensionality,
  intro a,
  rw in_union_iff_in_either,
  simp[emptySet_has_no_members],
end

lemma union_with_singleton_of_member_is_self (a: A) (X: finSet A) (mem: member a X): union (singleton a:finSet A) X =X :=
begin
  rw extensionality,
  intro b,
  rw in_union_iff_in_either,
  rw member_singleton,
  split,
  intro h,
  cases h,
  rw ← h,
  apply mem,
  apply h,
  intro h,
  right,
  exact h,
end

lemma finSet_induction(f : finSet A → Prop) (emptyCase: f emptySet) (step: ∀ (a:A )(Y: finSet A), f Y → f (union (singleton a) Y)) (X: finSet A): f X :=
begin
  apply quot.induction_on X,
  intro l,
  induction l with hd tl ih,
  unfold emptySet at emptyCase,
  apply emptyCase,

  have h: quot.mk (listSet.same_members A) (hd :: tl) = union (singleton hd) (quot.mk (listSet.same_members A)  tl),
  apply quot.sound,
  unfold listSet.same_members,
  intro a,
  unfold listSet.union,
  simp,

  rw h,
  apply step,
  apply ih,
end

def comprehension (φ: A → bool) (X: finSet A): finSet A := quot.lift (λ (Y: list A), quot.mk (listSet.same_members A) (listSet.comprehension φ Y)) (listSet.comprehension_preserved φ) X

lemma comprehension_semantics (φ: A → bool) (X: finSet A) (a:A): member a (comprehension φ X) ↔ φ a = tt ∧ member a X :=
begin
  apply quot.induction_on X,
  intro l,
  unfold comprehension,
  rw member_lift,
  rw member_lift,
  rw and.comm,
  apply listSet.comprehension_semantics,
end

def intersection (X Y: finSet A): finSet A := comprehension (λ (a:A), member_bool a Y) X

lemma in_intersection_iff_in_both (a:A) (X Y: finSet A): member a (intersection X Y ) ↔ member a X ∧ member a Y :=
begin
  unfold intersection,
  rw comprehension_semantics,
  rw ← member_iff_member_bool_tt,
  rw and.comm,
end

def difference (X Y: finSet A): finSet A := comprehension (λ (a:A), ¬ member_bool a Y) X

def in_difference_iff_only_in_first (a: A) (X Y: finSet A): member a (difference X Y) ↔ member a X ∧ ¬ member a Y :=
begin
  unfold difference,
  rw comprehension_semantics,
  simp,
  rw neg_member_iff_member_bool_ff,
  rw and.comm,
end

lemma intersection_and_difference_are_set (X Y: finSet A): X = union (intersection X Y) (difference X Y) :=
begin
  rw extensionality,
  intro a,
  rw in_union_iff_in_either,
  rw in_intersection_iff_in_both,
  rw in_difference_iff_only_in_first,
  by_cases aY: member a Y,
  simp [aY],
  simp[aY],
end

def disjoint (X Y: finSet A): Prop := intersection X Y = emptySet

def subset (X Y: finSet A): Prop := ∀ (a:A), member a X → member a Y

lemma disjoint_under_subset_preserved (X Y Z: finSet A) (disj: disjoint X Y) (subs: subset Z X): disjoint Z Y :=
begin
  unfold disjoint,
  unfold disjoint at disj,
  unfold subset at subs,
  rw extensionality,
  intro a,
  rw in_intersection_iff_in_both,
  rw emptySet_has_no_members,
  rw extensionality at disj,

  have disj_a: member a (intersection X Y) ↔ member a emptySet,
  apply disj,
  rw emptySet_has_no_members at disj_a,
  rw in_intersection_iff_in_both at disj_a,

  by_cases aZ: member a Z,
  have aX: member a X,
  apply subs _  aZ,
  have aY: ¬ member a Y,
  by_contradiction,
  rw ←  disj_a,
  split,
  apply aX,
  apply h,
  simp [aY],
  simp [aZ],
end

lemma intersection_and_difference_are_disjoint (X Y: finSet A): disjoint (intersection X Y) (difference X Y) :=
begin
  unfold disjoint,
  rw extensionality,
  intro a,
  rw emptySet_has_no_members,
  rw in_intersection_iff_in_both,
  rw in_difference_iff_only_in_first,
  rw in_intersection_iff_in_both,
  simp,
  cc,
end

lemma difference_and_set_are_union (X Y: finSet A): union (difference X Y) Y = union X Y :=
begin
  rw extensionality,
  intro a,
  rw in_union_iff_in_either,
  rw in_union_iff_in_either,
  rw in_difference_iff_only_in_first,
  by_cases aY: member a Y,
  simp [aY],
  simp[aY],
end

lemma difference_and_set_are_disjoint (X Y: finSet A): disjoint (difference X Y) Y :=
begin
  unfold disjoint,
  rw extensionality,
  intro a,
  rw emptySet_has_no_members,
  rw in_intersection_iff_in_both,
  rw in_difference_iff_only_in_first,
  simp,
end

def size (X: finSet A): ℕ := quot.lift listSet.set_size listSet.set_size_preserved X

lemma emptySet_has_size_zero: (size (emptySet: finSet A)) = 0 :=
begin
  unfold size,
  unfold emptySet,
  unfold listSet.set_size,
end

lemma singleton_has_size_one (a:A): size (singleton a: finSet A) = 1 :=
begin
  dunfold singleton,
  unfold size,
  unfold listSet.set_size,
  simp,
end

lemma size_union_with_non_member_singleton_is_plus_one (a: A) (X: finSet A) (mem: ¬ member a X): size (union (singleton a: finSet A) X) = 1 + size X :=
begin
  revert mem,
  apply quot.induction_on X,
  intro l,
  dunfold singleton,
  unfold size,
  unfold union,
  unfold listSet.union,
  simp,
  unfold listSet.set_size,
  rw member_lift,
  intro h,
  rw if_neg h,
end


lemma size_disjoint_union_is_sum (X Y: finSet A) (disj: disjoint X Y): size (union X Y) = size X + size Y :=
begin
  unfold disjoint at disj,
  induction X using finSet_induction with a X ih,
  rw union_comm,
  rw union_with_empty_is_self,
  rw emptySet_has_size_zero,
  rw nat.zero_add,

  by_cases a_X: member a X,
  rw union_with_singleton_of_member_is_self _ _ a_X,
  rw union_with_singleton_of_member_is_self _ _ a_X at disj,
  apply ih,
  apply disj,

  rw ←  union_assoc,
  rw size_union_with_non_member_singleton_is_plus_one,
  rw size_union_with_non_member_singleton_is_plus_one,
  rw ih,
  rw nat.add_assoc,

  apply disjoint_under_subset_preserved (union (singleton a: finSet A) X) Y X,
  unfold disjoint,
  apply disj,

  unfold subset,
  intro b,
  rw in_union_iff_in_either,
  cc,

  apply a_X,
  by_contradiction,
  rw in_union_iff_in_either at h,
  cases h,
  exact absurd h a_X,

  rw extensionality at disj,
  have disj_a: member a (intersection (union (singleton a) X) Y) ↔ member a emptySet,
  apply disj,
  rw emptySet_has_no_members at disj_a,
  rw ← disj_a,
  rw in_intersection_iff_in_both,
  rw in_union_iff_in_either,
  rw member_singleton,
  split,
  left,
  refl,
  exact h,
end

theorem inclusion_exclusion (X Y: finSet A): size (union X Y) + size (intersection X Y) = size X + size Y :=
begin
  nth_rewrite 2 (intersection_and_difference_are_set X Y),
  rw size_disjoint_union_is_sum _ _ (intersection_and_difference_are_disjoint X Y),
  rw nat.add_assoc,
  rw ← size_disjoint_union_is_sum _ _ (difference_and_set_are_disjoint X Y),
  rw difference_and_set_are_union,
  rw nat.add_comm,
end
