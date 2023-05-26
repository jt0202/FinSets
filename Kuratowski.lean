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

def size {A: Type u} (x:Kuratowski A) [∀ (a: A) (L: list A), decidable (a ∈ L)]: ℕ  := set_size_of_list(kuratowski_to_list (x))

def kuratowski_member {A:Type u} [decidable_eq A] : A -> Kuratowski A -> bool
| x Kuratowski.empty := false
| x {y} := x=y
| x (y ∪ z) := (kuratowski_member x z) ∨ (kuratowski_member x y)

theorem empty_set_has_size_0 {A:Type u} [e: ∀ (a: A) (L: list A), decidable (a ∈ L)]: (size (Kuratowski.empty))  = 0 :=
begin
  unfold size,
end

def comprehension{A:Type u}: (A -> bool) -> Kuratowski A -> Kuratowski A
| ϕ Kuratowski.empty := Kuratowski.empty
| ϕ {a} := if ϕ a then {a} else Kuratowski.empty
| ϕ (x ∪ y) := comprehension ϕ x ∪ comprehension ϕ y

def kuratowski_intersection {A:Type u} [decidable_eq A] (x y:Kuratowski A) : Kuratowski A:= comprehension (λ (a:A),kuratowski_member a y) x

notation (name := kuratowski_intersection) x ∩ y := kuratowski_intersection x y


end Length

end Kuratowksi