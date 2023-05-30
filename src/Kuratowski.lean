open bool
open decidable
open nat
open list
open classical


universe u

namespace Kuratowksi

inductive Kuratowski (A:Type u) 
| empty: Kuratowski 
| singleton : A -> Kuratowski 
| union : Kuratowski  -> Kuratowski  -> Kuratowski 

-- notation (name :=emptyset) Kuratowski.empty := Kuratowski.empty
notation {a} := Kuratowski.singleton a
notation (name := union) x ∪ y := Kuratowski.union x y

axiom union_comm {A:Type u} (x y : Kuratowski A): x ∪ y = y ∪ x
axiom union_singleton_idem {A:Type u} (x : A): {x} ∪ {x} = {x}
axiom union_assoc {A:Type u} (x y z : Kuratowski A): x ∪ (y ∪ z) = (x ∪ y) ∪ z
axiom empty_union {A:Type u} (x : Kuratowski A): Kuratowski.empty ∪ x = x
axiom union_empty {A: Type u} {x: Kuratowski A} : x ∪ Kuratowski.empty = x

/-
These two axioms are new and not in the original paper but seem to be necessary 
from the current pov. Perhaps they can later be removed.
-/


axiom singleton_not_empty {A: Type u} (a: A): {a} ≠ Kuratowski.empty
axiom non_emptiness_preserved {A:Type u} (x y: Kuratowski A): (x ≠ Kuratowski.empty) ∧ (y ≠ Kuratowski.empty) ↔   x ∪ y ≠ Kuratowski.empty


theorem union_idem {A:Type u} (x:Kuratowski A): x ∪ x = x :=
begin
  induction x with x1 x1  x2 h_x1 h_x2,
  apply union_empty,
  apply union_singleton_idem,
  rw union_assoc (x1 ∪ x2) x1 x2,
  rw union_comm x1 x2,
  rw ← union_assoc x2 x1 x1,
  rw h_x1,
  rw union_comm x2 x1,
  rw ← union_assoc x1 x2 x2,
  rw h_x2,
end

lemma union_at_both_sides {A: Type u} (X Y Z: Kuratowski A) (h: X= Y): X ∪ Z = Y ∪ Z :=
begin
  induction Z with a z1 z2 h_z1 h_z2,
  rw union_empty,
  rw union_empty,
  exact h,

  rw h,
  rw union_assoc,
  rw union_assoc,
  rw h_z1,
end

def fset_under_map (A: Type u) (B: Type u): Kuratowski A -> (A -> B) -> Kuratowski B
| Kuratowski.empty _ := Kuratowski.empty
| {a} f := {f(a)}
| (u ∪ v) f := fset_under_map u f ∪ fset_under_map v f

def kuratowski_member {A:Type u} [decidable_eq A] : A -> Kuratowski A -> bool
| x Kuratowski.empty := false
| x {y} := x=y
| x (y ∪ z) := (kuratowski_member x z)= tt ∨ (kuratowski_member x y) = tt

def kuratowski_member_prop {A:Type u} [decidable_eq A] : A -> Kuratowski A -> Prop
| x Kuratowski.empty := ff
| x {y} := x=y
| x (y ∪ z) := (kuratowski_member_prop x z) ∨ (kuratowski_member_prop x y)

lemma kuratowski_member_iff_kuratowski_member_prop {A:Type u} [decidable_eq A] (a:A) (X: Kuratowski A): (kuratowski_member a X = tt) ↔ kuratowski_member_prop a X :=
begin
  induction X with a' X1 X2 h_X1 h_X2,
  simp [kuratowski_member, kuratowski_member_prop],
  by_cases (a=a'),
  rw h,
  simp [kuratowski_member, kuratowski_member_prop],
  simp [kuratowski_member, kuratowski_member_prop, h],
  simp [kuratowski_member, kuratowski_member_prop],
  rw ← h_X1,
  rw ← h_X2,
end

def boolean_negation: bool -> bool
| tt := ff
| ff := tt

lemma kuratowski_member_false_iff_neg_kuratowski_member_prop {A:Type u} [decidable_eq A] (a:A) (X: Kuratowski A): ¬ (kuratowski_member a X) = tt ↔ ¬ kuratowski_member_prop a X :=
begin
  rw ← kuratowski_member_iff_kuratowski_member_prop,
end

section extensionality
variables {A: Type u} [decidable_eq A]

lemma equiv_subset1_l (X Y: Kuratowski A) (H: Y ∪ X = X) (a: A) (aY: (kuratowski_member_prop a Y)): kuratowski_member_prop a X :=
begin
  cases X,
  rw union_empty at H,
  rw H at aY,
  exact aY,

  rw ← H,
  unfold kuratowski_member_prop,
  right,
  exact aY,

  rw ← H,
  unfold kuratowski_member_prop,
  right,
  exact aY,
end

lemma equiv_subset1_r (X Y: Kuratowski A): (∀ (a:A), (kuratowski_member_prop a Y -> kuratowski_member_prop a X)) -> Y ∪ X = X :=
begin
  induction Y with a' y1 y2 h_y1 h_y2,
  intro h,
  rw empty_union,

  intro h,
  have h': ∀ (x: Kuratowski A), kuratowski_member_prop a' x → {a'} ∪ x = x,
  intro x,
  induction x with a'' x1 x2 h_x1 h_x2,
  simp [kuratowski_member_prop],
  intro f,
  exact f,
  intro p,
  simp [kuratowski_member_prop] at p,
  rw p,
  rw union_idem,
  intro h',
  simp [kuratowski_member_prop] at h',
  cases h',
  rw union_comm x1 x2,
  rw union_assoc,
  rw h_x2,
  exact h',
  rw union_assoc,
  rw h_x1,
  exact h',
  apply h',
  apply h,
  simp [kuratowski_member_prop],

  intro h,
  rw ← union_assoc,
  rw h_y2,
  rw h_y1,
  
  unfold kuratowski_member_prop at h,
  intro a,
  intro h',
  apply h,
  right,
  exact h',

  unfold kuratowski_member_prop at h,
  intro a,
  intro h',
  apply h,
  left,
  exact h',
end

lemma prop_iff_is_eq (P Q: Prop): (P ↔ Q) ↔ (P=Q):=
begin
  split,
  cc,
  cc,
end

lemma eq_subset1 (X Y: Kuratowski A): ((Y ∪ X) = X ∧ (X ∪ Y) = Y) ↔ ∀ (a:A), kuratowski_member_prop a X = kuratowski_member_prop a Y :=
begin
  split,
  intro h,
  have h1: (Y ∪ X) = X,
  simp [h],
  have h2: (X ∪ Y) = Y,
  simp [h],
  intro a,
  rw ← prop_iff_is_eq,
  split,
  intro h_x,
  apply equiv_subset1_l Y X h2 a h_x,
  intro h_y,
  apply equiv_subset1_l X Y h1 a h_y,

  intro h,
  split,
  apply equiv_subset1_r,
  intro a,  
  intro h',
  rw h,
  exact h',

  apply equiv_subset1_r,
  intro a,
  intro h',
  rw ← h,
  exact h',
end

lemma eq_subset2 (X Y: Kuratowski A): (X = Y) ↔ (( X ∪ Y = Y) ∧  (Y ∪ X = X)) :=
begin
  split,
  intro h,
  rw h,
  rw union_idem,
  have h_eq: Y=Y,
  refl,
  split,
  exact h_eq,
  exact h_eq,

  intro h,
  cases h,
  rw ← h_left,
  rw union_comm,
  rw h_right,
end

theorem extensionality (X Y: Kuratowski A): X = Y ↔ (∀ (a:A), kuratowski_member_prop a X = kuratowski_member_prop a Y):=
begin
  split,
  rw eq_subset2,
  rw eq_subset1,
  intro h,
  intro a,
  apply eq.symm,
  revert a,
  exact h,

  rw eq_subset2,
  rw eq_subset1,
  intro h,
  intro a,
  apply eq.symm,
  revert a,
  exact h,
end

end extensionality

section Length

def kuratowski_to_list {A:Type u}: Kuratowski A -> list A
| Kuratowski.empty := []
| {a} := a :: []
| (X ∪ Y) := append (kuratowski_to_list X) (kuratowski_to_list Y)

def set_size_of_list {A: Type u} [∀ (a: A) (L: list A), decidable (a ∈ L)]: list A -> ℕ
| [] := 0
| (cons a L) := if (a ∈ L) then set_size_of_list L else set_size_of_list L + 1

def size {A: Type u} [∀ (a: A) (L: list A), decidable (a ∈ L)] (x:Kuratowski A) : ℕ  := set_size_of_list(kuratowski_to_list (x))

lemma kuratowski_to_list_preserves_membership {A: Type u} [decidable_eq A] (x: Kuratowski A) (a: A): (( kuratowski_member_prop a x) ↔ (a ∈ kuratowski_to_list x)) :=
begin
  split,
  induction x with a' x1 x2 h_x1 h_x2,
  simp [kuratowski_member_prop],
  intro h,
  exfalso,
  exact h,

  simp [kuratowski_member_prop],
  intro h,
  simp [kuratowski_to_list],
  exact h,

  simp [kuratowski_member_prop],
  intro h,
  simp [kuratowski_to_list],
  cases h,
  right,
  apply h_x2,
  exact h,

  left,
  apply h_x1,
  exact h,

  induction x with a' x1 x2 h_x1 h_x2,
  simp [kuratowski_to_list, kuratowski_member_prop],
  intro h,
  exact h,

  simp [kuratowski_to_list, kuratowski_member_prop],
  intro h,
  exact h,

  simp [kuratowski_to_list, kuratowski_member_prop],
  intro h,
  cases h,
  right,
  apply h_x1,
  exact h,

  left,
  apply h_x2,
  exact h,
end


lemma empty_set_has_size_0 {A:Type u} [∀ (a: A) (L: list A), decidable (a ∈ L)] (x: Kuratowski A) (h: x = Kuratowski.empty): (size (x) = 0) :=
begin
  unfold size,
  rw h,
  unfold kuratowski_to_list,
  unfold set_size_of_list,
end

lemma singleton_has_size_1 {A:Type u} [∀ (a: A) (L: list A), decidable (a ∈ L)] (a:A): (size ({a}) = 1) :=
begin
  unfold size,
  unfold kuratowski_to_list,
  simp [set_size_of_list],
end


theorem union_with_member_does_not_increase_size {A:Type u} [decidable_eq A] [∀ (a: A) (L: list A), decidable (a ∈ L)] (x: Kuratowski A) (a: A) (h: (kuratowski_member_prop a x)): (size (x) = size ( {a} ∪ x)) :=
begin
  dunfold size,
  dunfold kuratowski_to_list,
  simp [set_size_of_list],
  rw kuratowski_to_list_preserves_membership at h,
  simp [h],
end

def comprehension{A:Type u}: (A -> bool) -> Kuratowski A -> Kuratowski A
| ϕ Kuratowski.empty := Kuratowski.empty
| ϕ {a} := if (ϕ a = tt) then {a} else Kuratowski.empty
| ϕ (x ∪ y) := comprehension ϕ x ∪ comprehension ϕ y

lemma and_or_distr (P Q R: Prop): P ∧ Q ∨ P ∧ R ↔ P ∧ (Q ∨ R) :=
begin
  by_cases P,
  simp [h],
  simp [h],
end

lemma comprehension_semantics {A:Type u} [decidable_eq A](p: A -> bool) (X : Kuratowski A) (a: A): kuratowski_member_prop a (comprehension p X) ↔ (p a = tt) ∧ kuratowski_member_prop a X :=
begin
  induction X with a' x1 x2 h_x1 h_x2,
  simp [comprehension, kuratowski_member_prop],
  unfold comprehension,
  by_cases (p a' = tt),
  simp[h, kuratowski_member_prop],
  by_cases h': (a = a'),
  simp [h'],
  exact h,
  simp [h'],
  simp [h],
  by_cases h' : (a = a'),
  simp [h', h, kuratowski_member_prop],
  simp [kuratowski_member_prop, h'],

  simp [comprehension, kuratowski_member_prop],
  rw h_x1,
  rw h_x2,
  rw and_or_distr,
end

def kuratowski_intersection {A:Type u} [decidable_eq A] (x y:Kuratowski A) : Kuratowski A:= comprehension (λ (a:A),kuratowski_member a y) x

notation (name := kuratowski_intersection) x ∩ y := kuratowski_intersection x y


lemma in_intersection_iff_in_both {A:Type u} [decidable_eq A] (X Y: Kuratowski A) (a:A): kuratowski_member_prop a (X ∩ Y) = (kuratowski_member_prop a X ∧ kuratowski_member_prop a Y):=
begin
  unfold kuratowski_intersection,
  rw comprehension_semantics,
  rw kuratowski_member_iff_kuratowski_member_prop,
  rw and.comm,
end

def disjoint {A: Type u} [decidable_eq A] (X Y: Kuratowski A):= (kuratowski_intersection X Y) = Kuratowski.empty


def kuratowski_difference {A:Type u} [decidable_eq A] (x y:Kuratowski A): Kuratowski A := comprehension (λ (a:A), ¬ ( kuratowski_member a y = tt))  x

notation (name := kuratowski_difference) x \ y := kuratowski_difference x y

lemma test (a: bool): to_bool(¬ a = tt) =tt ↔ ¬ a = tt :=
begin
  cases a,
  simp,
  simp,
end

lemma in_difference_if_only_in_first {A:Type u} [decidable_eq A] (X Y: Kuratowski A) (a:A): kuratowski_member_prop a (X \ Y) = (kuratowski_member_prop a X ∧ ¬  kuratowski_member_prop a Y) :=
begin
  dunfold kuratowski_difference,
  rw comprehension_semantics,
  rw test,
  rw kuratowski_member_false_iff_neg_kuratowski_member_prop,
  rw and.comm,
end

lemma intersection_and_difference_are_disjoint {A:Type u} [decidable_eq A] (X Y: Kuratowski A) : disjoint (X ∩ Y) (X \ Y) :=
begin
  unfold disjoint,
  rw extensionality,
  intro a,
  rw in_intersection_iff_in_both,
  rw in_intersection_iff_in_both,
  rw in_difference_if_only_in_first,
  by_cases h: (kuratowski_member_prop a Y),
  simp [h, kuratowski_member_prop],
  simp [h, kuratowski_member_prop],
end


lemma disjoint_of_union {A: Type u} [decidable_eq A] (X1 X2 X Y: Kuratowski A) (d: disjoint X Y) (h: X= X1 ∪ X2): disjoint X1 Y :=
begin
  rw h at d,
  rw disjoint at d,
  rw extensionality at d,
  rw disjoint,
  rw extensionality,
  intro a',
  have d_a': kuratowski_member_prop a' ((X1∪X2)∩Y) = kuratowski_member_prop a' Kuratowski.empty,
  apply d,
  rw ← d_a',
  rw in_intersection_iff_in_both,
  rw in_intersection_iff_in_both,
  simp [kuratowski_member_prop],
  by_cases aY: kuratowski_member_prop a' Y,
  simp [aY],
  by_cases aX2: kuratowski_member_prop a' X2,
  exfalso,
  rw in_intersection_iff_in_both at d_a',
  simp [kuratowski_member_prop, aY, aX2] at d_a',
  rw ← d_a',
  exact true.intro,
  simp [aX2],
  simp [aY],
end

lemma set_as_difference_and_intersection {A: Type u} [decidable_eq A] (X Y:Kuratowski A): X = (X ∩ Y) ∪ (X \ Y):=
begin
  rw extensionality,
  intro a,
  unfold kuratowski_member_prop,
  rw in_difference_if_only_in_first,
  rw in_intersection_iff_in_both,
  by_cases (kuratowski_member_prop a Y),
  simp [h],
  simp [h],
end

lemma set_and_difference_are_union {A: Type u} [decidable_eq A] (X Y: Kuratowski A): X ∪ (Y \ X) = (X ∪ Y) :=
begin
  rw extensionality,
  intro a,
  simp [kuratowski_member_prop],
  rw in_difference_if_only_in_first,
  by_cases aX: kuratowski_member_prop a X,
  simp [aX],
  simp [aX],
end

lemma set_and_difference_disjoint {A: Type u} [decidable_eq A] (X Y: Kuratowski A): disjoint X (Y \ X) :=
begin
  unfold disjoint,
  rw extensionality,
  intro a,
  rw in_intersection_iff_in_both,
  rw in_difference_if_only_in_first,
  by_cases aX: kuratowski_member_prop a X,
  simp [aX,kuratowski_member_prop],
  simp [aX,kuratowski_member_prop],

end

lemma length_disjoint {A:Type u} [decidable_eq A] [∀ (a: A) (L: list A), decidable (a ∈ L)] (X Y: Kuratowski A) (h: disjoint X Y): size(X ∪ Y) = size(X) + size(Y) :=
begin
  induction X with a X1 X2 h_X1 h_X2,
  simp [empty_union, empty_set_has_size_0],
  rw nat.zero_add,
  rw singleton_has_size_1,
  unfold size,
  unfold kuratowski_to_list,
  simp [set_size_of_list],
  have aY: ¬ a ∈ kuratowski_to_list Y,
  rw ←  kuratowski_to_list_preserves_membership,
  rw disjoint at h,
  rw extensionality at h,
  have h': kuratowski_member_prop a ({a} ∩ Y) = kuratowski_member_prop a Kuratowski.empty,
  apply h,
  rw in_intersection_iff_in_both at h',
  simp [kuratowski_member_prop] at h',
  rw h',
  simp,
  simp [aY],
  rw nat.add_comm,


end



theorem inclusion_exclusion  {A:Type u} [decidable_eq A] [∀ (a: A) (L: list A), decidable (a ∈ L)] (X Y: Kuratowski A): size(X) + size (Y) = size (X ∪ Y) + size (X ∩ Y) :=
begin
  have size_x: (size(X) = size( X ∩ Y ∪ X \ Y)),
  conv
  begin
    to_lhs,
    rw set_as_difference_and_intersection X Y,
    skip,
  end,
  rw size_x,
  rw length_disjoint (X ∩ Y) (X \ Y) (intersection_and_difference_are_disjoint X Y) ,
  rw nat.add_assoc,
  rw nat.add_comm (size(X \ Y)) _,
  rw ← length_disjoint Y (X \ Y) (set_and_difference_disjoint Y X),
  rw set_and_difference_are_union,
  rw nat.add_comm,
  rw union_comm Y X,
end

end Length

end Kuratowksi