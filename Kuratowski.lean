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

notation (name :=emptyset) ∅ := Kuratowski.empty
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
axiom non_emptiness_preserved {A:Type u} (x y: Kuratowski A): (x ≠ ∅) ∧ (y ≠ ∅) ↔   x ∪ y ≠ ∅


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
| ∅ _ := ∅
| {a} f := {f(a)}
| (u ∪ v) f := fset_under_map u f ∪ fset_under_map v f

section Length

def flatten {A:Type u}: Kuratowski A -> list A
| ∅ := []
| {a} := a :: []
| (X ∪ Y) := append (flatten X) (flatten Y)

def list_to_right_associative_tree {A:Type u}: list A -> Kuratowski A
| [] := ∅
| (a :: l) := {a} ∪ (list_to_right_associative_tree l)

theorem flatten_to_right_associative_tree_is_equiv {A:Type u} (x:Kuratowski A): x = list_to_right_associative_tree(flatten x) :=
begin
  induction x,
  sorry
end

theorem normal_form {A:Type u} (x:Kuratowski A) (x ≠ Kuratowski.empty) :(∃ (a:A) (y: Kuratowski A), x = {a} ∪ y) :=
begin
  induction x with a' x1 x2 h_x1 h_x2,
  exfalso,
  apply H,
  refl,
  existsi [a', Kuratowski.empty] ,
  apply symm,
  apply union_empty,
  rw h_x1,
  sorry
end

def kuratowski_member {A:Type u} [decidable_eq A] : A -> Kuratowski A -> bool
| x ∅ := false
| x {y} := x=y
| x (y ∪ z) := (kuratowski_member x z) ∨ (kuratowski_member x y)

def comprehension{A:Type u}: (A -> bool) -> Kuratowski A -> Kuratowski A
| ϕ ∅ := ∅
| ϕ {a} := if ϕ a then {a} else ∅
| ϕ (x ∪ y) := comprehension ϕ x ∪ comprehension ϕ y

def kuratowski_intersection {A:Type u} [decidable_eq A] (x y:Kuratowski A) : Kuratowski A:= comprehension (λ (a:A),kuratowski_member a y) x

notation (name := kuratowski_intersection) x ∩ y := kuratowski_intersection x y

def size {A: Type u} (x: Kuratowski A): ℕ :=
begin
  if (x = Kuratowski.empty)
  then size(x) => 0
  else
end

end Length

end Kuratowksi