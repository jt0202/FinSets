import tactic.push_neg
open list
open nat

universe u

namespace listSet


axiom cons_idem {A: Type u} (a: A) (X: (list A)):  a :: (a:: X) = a:: X
axiom cons_comm {A: Type u} (a b: A) (X: list A): a::(b::X) = b:: (a :: X)

def union {A:Type u} (X Y: list A): list A := X ++ Y

notation (name:= list_union) X ∪ Y := union X Y

def singleton {A: Type u} (a:A): list A:= a::nil

section union_properties
variables {A:Type u} (X Y Z: list A) (a b: A)

theorem empty_union: nil ∪ X = X :=
begin
  unfold union,
  simp,
end

theorem union_empty: X ∪ nil = X :=
begin
  unfold union,
  simp,
end

theorem pull_head_out (hd:A) (tl l: list A): hd::tl ∪ l = hd :: (tl ∪ l) :=
begin
  unfold union,
  simp,
end

lemma append_singleton (a:A) (X: list A): a::X = X ∪ (a::nil):=
begin
  induction X with hd tl ih,
  rw empty_union,
  rw cons_comm,
  rw ih,
  rw pull_head_out,
end

theorem union_assoc: X ∪ (Y ∪ Z) = (X ∪ Y) ∪ Z:=
begin
  induction X with hd tl ih,
  rw empty_union,
  rw empty_union,

  rw pull_head_out,
  rw ih,
  rw pull_head_out,
  rw pull_head_out,
end

theorem union_comm: X ∪ Y = Y ∪ X :=
begin
  induction Y with hdY tlY ihY,
  rw empty_union,
  rw union_empty,

  rw pull_head_out,
  rw append_singleton,
  rw union_assoc,
  rw ihY,
  rw append_singleton hdY (tlY ∪ X),
end

theorem union_idem: X ∪ X = X :=
begin
  induction X with hd tl ih,
  rw union_empty,

  rw pull_head_out,
  rw union_comm,
  rw pull_head_out,
  rw cons_idem,
  rw ih,
end

lemma in_union_iff_in_either (X Y: list A) (a:A): a ∈ union X Y ↔ (a ∈ X) ∨ (a ∈ Y):=
begin
  unfold union,
  by_cases aX: a ∈ X,
  simp [aX],
  simp [aX],
end

end union_properties

section extensionality
variables {A:Type u} [decidable_eq A]

lemma append_members_doesnt_change (a:A) (X: list A) (h: a ∈ X): a::X = X :=
begin
  induction X with hd tl ih,
  simp at h,
  exfalso,
  exact h,

  cases h,
  rw h,
  rw cons_idem,

  rw cons_comm,
  rw ih,
  exact h,
end

lemma equiv_subset1_r (X Y: list A): (∀ (a:A), a ∈ Y → a ∈ X) → union Y X = X :=
begin
  induction Y with hd tl ih,
  intro h,
  rw empty_union,

  intro h,
  rw pull_head_out,
  have ihv: ∀ (a:A), a ∈ tl → a ∈ X,
  intro a,
  intro atl,
  apply h,
  simp[atl],
  rw ih ihv,

  have hdX: hd ∈ X,
  apply h,
  simp,

  rw append_members_doesnt_change hd X hdX,

end

lemma prop_iff_is_eq (P Q: Prop): (P ↔ Q) ↔ (P=Q):=
begin
  split,
  cc,
  cc,
end

lemma eq_subset1 (X Y: list A): ((union Y X) = X ∧ (union X Y) = Y) ↔ ∀ (a:A), (a ∈ X) = (a ∈  Y) :=
begin
  split,
  intro hxy,
  cases hxy,
  intro a,
  rw ← hxy_left,
  rw union_comm,
  rw hxy_right,

  intro h,
  split,
  apply equiv_subset1_r X Y,
  intro a,
  have ha: a ∈ X = (a ∈ Y),
  apply h,
  rw ha,
  simp,

  apply equiv_subset1_r Y X,
  intro a,
  have ha: a ∈ X = (a ∈ Y),
  apply h,
  rw ha,
  simp,
end

lemma eq_subset2 (X Y: list A): X=Y ↔ ((union Y X) = X ∧ (union X Y) = Y) :=
begin
  split,
  intro h,
  rw h,
  rw union_idem,
  simp,

  intro h,
  cases h,
  rw ← h_left,
  rw union_comm,
  rw h_right,
end

theorem extensionality (X Y: list A): (X = Y) ↔ ∀ (a:A), a ∈ X ↔ a ∈ Y:=
begin
  rw eq_subset2,
  rw eq_subset1,

  split,
  intro h,
  intro a,
  rw prop_iff_is_eq,
  revert a,
  exact h,

  intro h,
  intro a,
  rw ← prop_iff_is_eq,
  revert a,
  exact h,
end


end extensionality

section operations
variables {A:Type u} [decidable_eq A]

def comprehension: (A-> bool) -> list A -> list A 
| φ nil := nil
| φ (a::X) := if φ a = tt then a :: (comprehension φ X) else (comprehension φ X)

theorem comprehension_semantics (a:A) (X: list A) (φ: A -> bool): a ∈ comprehension φ X ↔ (φ a = tt) ∧ a ∈ X :=
begin
  induction X with hd tl ih,
  simp [comprehension],
  unfold comprehension,
  
  by_cases phihd: φ hd = tt,
  simp [phihd],
  rw ih,
  by_cases a_hd: (a = hd),
  simp[a_hd, phihd],

  simp[a_hd],

  simp [phihd],
  rw ih,

  by_cases a_hd: (a = hd),
  simp [a_hd, phihd],

  simp[a_hd],
end

def intersection (X Y: list A) := comprehension (λ (a:A), a ∈ Y ) X

lemma in_intersection_iff_in_both (a: A) (X Y: list A) : a ∈ intersection X Y ↔ a ∈ X ∧ a ∈ Y :=
begin
  unfold intersection,
  rw comprehension_semantics,
  simp ,
  by_cases a ∈ X,
  simp [h],
  simp [h],
end

def difference (X Y: list A) := comprehension (λ (a:A), ¬ a ∈ Y ) X

lemma in_difference_iff_only_in_first (a: A) (X Y: list A) : a ∈ difference X Y ↔ a ∈ X ∧ a ∉ Y :=
begin
  unfold difference,
  rw comprehension_semantics,
  simp,
  by_cases a ∈ X,
  simp [h],
  simp [h],
end

def disjoint (X Y: list A): Prop := intersection X Y = nil
def subset (X Y: list A): Prop := ∀ (a:A), a ∈ X → a ∈ Y

lemma disjoint_preserved_under_subset (X Y Z: list A) (subs: subset X Y) (disj:disjoint Y Z ): disjoint X Z:=
begin
  unfold disjoint,
  rw extensionality,
  intro a,
  rw in_intersection_iff_in_both,
  simp,

  unfold disjoint at disj,
  rw extensionality at disj,

  have aYZ: a ∈ intersection Y Z ↔ a ∈ nil,
  apply disj,

  rw in_intersection_iff_in_both at aYZ,
  simp at aYZ,

  unfold subset at subs,
  have aXY: a ∈ X → a ∈ Y,
  apply subs,

  by_cases aX: a ∈ X,
  simp [aX],
  have aY: a ∈ Y,
  apply aXY,
  apply aX,

  simp [aY] at aYZ,
  exact aYZ,

  simp[aX],
  intro f,
  intro aZ,
  exact f,
end


lemma intersection_and_difference_are_disjoint (X Y: list A): disjoint (intersection X Y) (difference X Y) :=
begin
  unfold disjoint,
  rw extensionality,
  intro a,
  rw in_intersection_iff_in_both,
  rw in_intersection_iff_in_both,
  rw in_difference_iff_only_in_first,
  simp,
  by_cases aY: a ∈ Y,
  simp [aY],
  simp [aY],
  intro aX,
  intro f,
  intro aX',
  exact f,
end


lemma set_as_difference_and_intersection (X Y: list A): union (difference X Y)  (intersection X Y)= X :=
begin
  rw extensionality,
  intro a,
  rw in_union_iff_in_either,
  rw in_intersection_iff_in_both,
  rw in_difference_iff_only_in_first,
  by_cases aY: a ∈ Y,
  simp [aY],
  simp [aY],
end

lemma set_and_difference_are_union (X Y: list A): union (difference Y X) X = union X Y :=
begin
  rw extensionality,
  intro a,
  rw in_union_iff_in_either,
  rw in_union_iff_in_either,
  rw in_difference_iff_only_in_first,
  by_cases aX: a ∈ X,
  simp [aX],
  simp [aX],
end

lemma set_and_difference_are_disjoint (X Y: list A): disjoint (difference Y X) X :=
begin
  unfold disjoint,
  rw extensionality,
  intro a,
  rw in_intersection_iff_in_both,
  rw in_difference_iff_only_in_first,
  simp,
end
end operations

section length
variables {A:Type u} [decidable_eq A]

def set_size: list A -> ℕ
| nil := 0
| (hd::tl) := if hd ∈ tl then set_size(tl) else set_size(tl) + 1

lemma disjoint_size_is_sum (X Y: list A) (disj: disjoint X Y): set_size(union X Y) = set_size X + set_size Y :=
begin
  induction X with hd tl ih,
  rw empty_union,
  simp [set_size],
  rw nat.zero_add,

  rw pull_head_out,
  unfold set_size,
  by_cases hd_tl: hd ∈ tl,
  have hd_tlY: hd ∈ union tl Y,
  rw in_union_iff_in_either,
  left,
  exact hd_tl,
  simp [hd_tl, hd_tlY],
  rw ih,
  apply disjoint_preserved_under_subset tl (hd::tl) Y,

  unfold subset,
  intro a,
  simp,
  cc,
  exact disj,

  have n_hd_tlY: ¬ hd ∈ union tl Y,
  rw in_union_iff_in_either,
  push_neg,
  split,
  exact hd_tl,

  unfold disjoint at disj,
  rw extensionality at disj,

  have hd_int: hd ∈ intersection (hd::tl) Y ↔ hd ∈ nil,
  apply disj,
  rw in_intersection_iff_in_both at hd_int,
  simp at hd_int,
  exact hd_int,

  simp [n_hd_tlY, hd_tl],
  rw nat.add_assoc,
  rw nat.add_comm 1 _,
  rw ← nat.add_assoc,
  rw ih,
  apply disjoint_preserved_under_subset tl (hd::tl) Y,
  unfold subset,
  intro a,
  simp,
  cc,
  exact disj,
end

theorem inclusion_exclusion (X Y: list A): set_size( union X Y) + set_size (intersection X Y) = set_size X + set_size Y :=
begin
  have size_x: (set_size(X) = set_size( union (intersection X Y) (difference X Y))),
  conv
  begin
    to_lhs,
    rw ← set_as_difference_and_intersection X Y,
    rw union_comm,
    skip,
  end,
  rw size_x,
  rw disjoint_size_is_sum (intersection X Y) _,
  rw nat.add_assoc,
  rw ← disjoint_size_is_sum (difference X Y) _,
  rw set_and_difference_are_union Y X,
  rw union_comm Y X,
  rw nat.add_comm,
  apply set_and_difference_are_disjoint,
  apply intersection_and_difference_are_disjoint,
end
end length

section marriage_theorem

end marriage_theorem

end listSet