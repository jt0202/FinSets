import tactic.rcases
open bool
open decidable
open nat
open list
open function

universe u

namespace Kuratowksi

inductive Kuratowski (A:Type u) 
| empty: Kuratowski 
| singleton : A -> Kuratowski 
| union : Kuratowski  -> Kuratowski  -> Kuratowski 

-- notation (name :=emptyset) Kuratowski.empty := Kuratowski.empty
notation {a} := Kuratowski.singleton a
notation (name := Kuratowski.union) x ∪ y := Kuratowski.union x y

axiom union_comm {A:Type u} (x y : Kuratowski A): x ∪ y = y ∪ x
axiom union_singleton_idem {A:Type u} (x : A): {x} ∪ {x} = {x}
axiom union_assoc {A:Type u} (x y z : Kuratowski A): x ∪ (y ∪ z) = (x ∪ y) ∪ z
axiom empty_union {A:Type u} (x : Kuratowski A): Kuratowski.empty ∪ x = x
axiom union_empty {A: Type u} {x: Kuratowski A} : x ∪ Kuratowski.empty = x



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

def fset_under_map {A: Type u} {B: Type u}: Kuratowski A -> (A -> B) -> Kuratowski B
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

section toList
def kuratowski_to_list {A:Type u}: Kuratowski A -> list A
| Kuratowski.empty := []
| {a} := a :: []
| (X ∪ Y) := append (kuratowski_to_list X) (kuratowski_to_list Y)


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

  simp [kuratowski_to_list, kuratowski_member_prop],

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
end toList

section operations
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
  intro f,
  exfalso,
  exact f,
  by_cases h' : (a = a'),
  simp [h', h, kuratowski_member_prop],
  simp [kuratowski_member_prop, h', h],

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

def list_disjoint {A: Type u} [decidable_eq A] (l1 l2: list A):= ∀ (a:A), ¬ (a ∈ l1 ∧ a ∈ l2) 

def kuratowski_to_list_preserves_disjoint {A: Type u} [decidable_eq A] (X Y: Kuratowski A): disjoint X Y ↔ list_disjoint (kuratowski_to_list X) (kuratowski_to_list Y) :=
begin
  dunfold list_disjoint,
  dunfold disjoint,
  rw extensionality,
  simp [in_intersection_iff_in_both, kuratowski_to_list_preserves_membership, kuratowski_member_prop],
end

def kuratowski_difference {A:Type u} [decidable_eq A] (x y:Kuratowski A): Kuratowski A := comprehension (λ (a:A), ¬ ( kuratowski_member a y = tt))  x

notation (name := kuratowski_difference) x \ y := kuratowski_difference x y

lemma pull_out_negation_to_bool (a: bool): to_bool(¬ a = tt) =tt ↔ ¬ a = tt :=
begin
  cases a,
  simp,
  simp,
end

lemma in_difference_if_only_in_first {A:Type u} [decidable_eq A] (X Y: Kuratowski A) (a:A): kuratowski_member_prop a (X \ Y) = (kuratowski_member_prop a X ∧ ¬  kuratowski_member_prop a Y) :=
begin
  dunfold kuratowski_difference,
  rw comprehension_semantics,
  rw pull_out_negation_to_bool,
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
  exact d_a',
  simp [aX2],
  simp [aY],
  intro f,
  exfalso,
  exact f,
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

lemma neg_or_is_and_neg (P Q: Prop): ¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q) :=
begin
  by_cases P,
  simp [h],
  simp[h],
end

lemma neg_and_is_or_neg (P Q: Prop): ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q):=
begin
  by_cases P,
  simp [h],
  simp[h],
end

lemma list_disjoint_head_removed {A: Type u} [decidable_eq A] (hd:A) (tl l: list A): list_disjoint (hd::tl) l → list_disjoint tl l :=
begin
  dunfold list_disjoint,
  simp[neg_and_is_or_neg],
  intro h,
  intro a,

  have p: ¬ (a = hd ∨  a ∈  tl) ∨ a ∉ l,
  simp [h],

  rw neg_or_is_and_neg at p,
  cases p,
  left,
  simp [p],

  right,
  exact p,
end

end operations

section Length

def set_size_of_list {A: Type u} [∀ (a: A) (L: list A), decidable (a ∈ L)]: list A -> ℕ
| [] := 0
| (cons a L) := if (a ∈ L) then set_size_of_list L else set_size_of_list L + 1

def size {A: Type u} [∀ (a: A) (L: list A), decidable (a ∈ L)] (x:Kuratowski A) : ℕ  := set_size_of_list(kuratowski_to_list (x))

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


lemma length_disjoint {A:Type u} [decidable_eq A] [∀ (a: A) (L: list A), decidable (a ∈ L)] (X Y: Kuratowski A): disjoint X Y → (size(X ∪ Y) = size(X) + size(Y)) :=
begin
  dunfold size,
  dunfold kuratowski_to_list,
  rw kuratowski_to_list_preserves_disjoint,

  -- if disjoint (X Y) appears inside the goal, the induction hypothesis is also applied to it. 
  -- If it is already a hypothesis this doesnt happen

  --case empty list
  induction kuratowski_to_list X,
  intro h,
  simp [set_size_of_list],
  rw nat.add_comm,
  rw nat.add_zero,

  -- case append
  intro h_disj,
  -- pull outside to unfold set_size
  have list_rw: hd::tl ++ kuratowski_to_list Y = hd :: (tl ++ kuratowski_to_list Y),
  simp,


  by_cases hd_tl: hd ∈ tl,
  simp [set_size_of_list, hd_tl],
  apply ih,
  apply list_disjoint_head_removed hd tl (kuratowski_to_list Y) h_disj,

  -- if hd is not in tl, then it is also not in Y as they are disjoint
  -- show by contradiction. Assume in Y and show that it is not disjoint
  have hdY: ¬ hd ∈ kuratowski_to_list Y,
  by_contradiction,
  simp [list_disjoint] at h_disj,
  simp [h] at h_disj,
  exact h_disj,

  rw list_rw,

  have p: ¬ hd ∈ (tl ++ kuratowski_to_list Y),
  simp,
  rw neg_or_is_and_neg,
  split,
  exact hd_tl,
  exact hdY,
  simp [set_size_of_list, p, hd_tl],
  rw nat.add_comm (set_size_of_list tl) 1,
  rw nat.add_comm _ 1,
  rw ih,
  rw nat.add_assoc,
  apply list_disjoint_head_removed hd _ _,
  exact h_disj,
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

section marriage_theorem

def subset {A: Type u}[decidable_eq A] (X Y: Kuratowski A): Prop := ∀ (a:A), kuratowski_member_prop a X → kuratowski_member_prop a Y

def family_union{A:Type u}: Kuratowski (Kuratowski A) →  Kuratowski A
| Kuratowski.empty := Kuratowski.empty
| {X} := X
| (X ∪ Y) := family_union(X) ∪ family_union (Y) 

lemma injective_preserves_size {A:Type u}[decidable_eq A] [∀(a:Kuratowski A)(l:list (Kuratowski A)), decidable(a ∈ l)] (X:Kuratowski( Kuratowski A)) (f: Kuratowski A -> A) (h_inj: injective f): size(X) ≤ size (fset_under_map X f) :=
begin
  unfold size,
  induction kuratowski_to_list X,
end

def distinctRepr {A: Type u} [decidable_eq A](f:(Kuratowski A) -> A) (F: Kuratowski (Kuratowski A)): Prop := injective f ∧ ∀ (X:Kuratowski A), kuratowski_member_prop (f X) X 

theorem marriage_theorem {A: Type u}[decidable_eq A] [decidable_eq (Kuratowski A)][∀(a:Kuratowski A)(l:list (Kuratowski A)), decidable(a ∈ l)] (F: Kuratowski (Kuratowski A)) (f_inh: F ≠ Kuratowski.empty) (f_mem_inh: ∀ X: (Kuratowski A), kuratowski_member_prop X F → X ≠ Kuratowski.empty  ): (∃ (f: Kuratowski A → A), distinctRepr f F) ↔ ∀ (G: Kuratowski (Kuratowski A) ), subset G F → size(G) ≤ size (family_union G) :=
begin
  split,
  intro hf,
  

  sorry,
end

end marriage_theorem

end Kuratowksi