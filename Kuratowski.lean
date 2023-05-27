open bool
open decidable
open nat
open list

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

def fset_under_map (A: Type u) (B: Type u): Kuratowski A -> (A -> B) -> Kuratowski B
| Kuratowski.empty _ := Kuratowski.empty
| {a} f := {f(a)}
| (u ∪ v) f := fset_under_map u f ∪ fset_under_map v f

section Length

def kuratowski_to_list {A:Type u}: Kuratowski A -> list A
| Kuratowski.empty := []
| {a} := a :: []
| (X ∪ Y) := append (kuratowski_to_list X) (kuratowski_to_list Y)

def set_size_of_list {A: Type u} [∀ (a: A) (L: list A), decidable (a ∈ L)]: list A -> ℕ
| [] := 0
| (cons a L) := if (a ∈ L) then set_size_of_list L else set_size_of_list L + 1

def size {A: Type u} [∀ (a: A) (L: list A), decidable (a ∈ L)] (x:Kuratowski A) : ℕ  := set_size_of_list(kuratowski_to_list (x))

def kuratowski_member {A:Type u} [decidable_eq A] : A -> Kuratowski A -> bool
| x Kuratowski.empty := false
| x {y} := x=y
| x (y ∪ z) := (kuratowski_member x z) ∨ (kuratowski_member x y)

def kuratowski_member_prop {A:Type u} [decidable_eq A] : A -> Kuratowski A -> Prop
| x Kuratowski.empty := ff
| x {y} := x=y
| x (y ∪ z) := (kuratowski_member_prop x z) ∨ (kuratowski_member_prop x y)

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


theorem empty_set_has_size_0 {A:Type u} [∀ (a: A) (L: list A), decidable (a ∈ L)] (x: Kuratowski A) (h: x = Kuratowski.empty): (size (x) = 0) :=
begin
  unfold size,
  rw h,
  unfold kuratowski_to_list,
  unfold set_size_of_list,
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
| ϕ {a} := if ϕ a then {a} else Kuratowski.empty
| ϕ (x ∪ y) := comprehension ϕ x ∪ comprehension ϕ y

def kuratowski_intersection {A:Type u} [decidable_eq A] (x y:Kuratowski A) : Kuratowski A:= comprehension (λ (a:A),kuratowski_member a y) x

notation (name := kuratowski_intersection) x ∩ y := kuratowski_intersection x y

def disjoint {A: Type u} [decidable_eq A] (X Y: Kuratowski A):= (kuratowski_intersection X Y) = Kuratowski.empty

def kuratowski_difference {A:Type u} [decidable_eq A] (x y:Kuratowski A): Kuratowski A := comprehension (λ (a:A), ¬ kuratowski_member a y) x

end Length

end Kuratowksi