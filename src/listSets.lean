import tactic.push_neg
open list
open nat
open function

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

lemma intersection_symm {X Y: list A}: intersection X Y = intersection Y X :=
begin
  rw extensionality,
  intro a,
  rw in_intersection_iff_in_both,
  rw in_intersection_iff_in_both,
  by_cases aX:a ∈ X,
  simp[aX],
  simp[aX],
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

def subset (X Y: list A): Prop := ∀ (a:A), a ∈ X → a ∈ Y

lemma head_removed_preserves_subset (hd: A) (tl Y: list A) (subs: subset (hd::tl) Y): subset tl Y :=
begin
  unfold subset,
  unfold subset at subs,
  intro a,
  intro a_tl,
  apply subs,
  simp,
  right,
  exact a_tl,
end

def pull_member_out (a: A) (X: list A) (aX: a ∈ X): list A := a :: (difference X (a::nil))

lemma pull_member_out_is_eq (a: A) (X: list A) (aX: a ∈ X): X = pull_member_out a X aX :=
begin
  unfold pull_member_out,
  rw extensionality,
  intro a1,
  simp,
  rw in_difference_iff_only_in_first,
  by_cases aa: a1 = a,
  simp[aa],
  exact aX,

  simp [aa],
end

lemma subset_transitive (X Y Z: list A) (subs1: subset X Y) (subs2: subset Y Z): subset X Z :=
begin
  unfold subset,
  unfold subset at subs2,
  unfold subset at subs1,
  intro a,
  intro aX,
  apply subs2,
  apply subs1,
  exact aX,
end

def disjoint (X Y: list A): Prop := intersection X Y = nil

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

lemma disjoint_symm {X Y: list A} (d: disjoint X Y): disjoint Y X :=
begin
  unfold disjoint,
  rw intersection_symm,
  apply d,
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

theorem size_0_iff_empty_set (X: list A): set_size(X) = 0 ↔ X = nil :=
begin
  split,
  induction X with hd tl ih,
  intro h,
  refl,

  intro h,
  exfalso,
  rw extensionality at ih,
  simp at ih,
  by_cases hhd: hd ∈ tl,
  simp [set_size, hhd] at h,
  simp [h] at ih,
  have nhhd: ¬ hd ∈ tl,
  apply ih,
  contradiction,

  simp [set_size, hhd] at h,
  rw ← nat.succ_eq_add_one at h,
  simp [nat.succ_ne_zero] at h,
  exact h,

  intro h,
  rw h,
  unfold set_size,
end

lemma subset_nil_eq_nil (X: list A) (subs: subset X nil): X = nil :=
begin
  rw extensionality,
  intro a,
  split,
  apply subs,
  simp,
  intro f,
  exfalso,
  exact f,
end

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

lemma subset_size_leq (X Y: list A) (subs: subset X Y): set_size X ≤ set_size Y :=
begin
  rw ← set_as_difference_and_intersection Y X,
  rw disjoint_size_is_sum (difference Y X) (intersection Y X),
  have h_int: intersection Y X = X,
  rw extensionality,
  intro a,
  rw in_intersection_iff_in_both,
  simp,
  apply subs,
  rw h_int,
  rw nat.add_comm,
  induction set_size (difference Y X),
  rw nat.add_zero,
  rw nat.succ_eq_add_one,
  rw ←  nat.add_assoc,
  have ineq: set_size X + n ≤ set_size X + n + 1,
  rw ← succ_eq_add_one,
  apply nat.le_succ,
  apply nat.le_trans ih ineq,

  apply disjoint_symm,
  apply intersection_and_difference_are_disjoint,
  

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
variables {A: Type u} [decidable_eq A] [nonempty A]

def family_union: list (list A) -> list A
| nil := nil
| (hd::tl) := union hd (family_union tl)

def injective_on (f: (list A) → A) (G: list (list A)) : Prop := ∀ (x1 x2 : list A), x1 ∈ G ∧ x2 ∈ G → f x1 = f x2 → x1 = x2 

lemma injective_on_under_subset (f: (list A) → A) (F: list (list A) ) (G: list (list A)) (inj: injective_on f F) (subs: subset G F): injective_on f G :=
begin
  unfold injective_on,
  unfold injective_on at inj,
  intro x1,
  intro x2,
  intro xG,
  apply inj,
  cases xG,
  unfold subset at subs,

  split,
  apply subs,
  exact xG_left,

  apply subs,
  exact xG_right,
end

lemma injective_on_under_head_removed (f: (list A) → A) (tl: list (list A)) (hd: list A) (inj: injective_on f (hd::tl)): injective_on f tl :=
begin
  unfold injective_on,
  unfold injective_on at inj,
  intro x1,
  intro x2,
  intro h,
  apply inj,
  simp [h],
end

def SDR (f: (list A) → A) (G: list (list A)): Prop := injective_on f G ∧ ∀ (l: list A), l ∈ G → f l ∈ l

lemma SDR_on_under_subset (f: (list A) → A) (F: list (list A) ) (G: list (list A)) (sdr: SDR f F) (subs: subset G F): SDR f G :=
begin
  unfold SDR,
  unfold SDR at sdr,
  cases sdr with inj ssp,
  split,
  apply injective_on_under_subset f F G inj subs,

  intro l,
  intro lG,
  apply ssp,
  unfold subset at subs,
  apply subs,
  exact lG,
end

lemma SDR_on_empty_set (f: (list A) → A): SDR f nil :=
begin
  unfold SDR,
  split,
  unfold injective_on,
  intro x1,
  intro x2,
  simp,
  intro f,
  exfalso,
  exact f,

  intro l,
  simp,
  intro f,
  exfalso,
  exact f,
end

def collectFunctionResults:((list A) -> A) -> list (list A) -> list A
| f nil := nil
| f (hd::tl) :=  (f hd) :: (collectFunctionResults f tl)

lemma collectFunctionResults_SDR_semantics_1 (f: list A → A)  (G: list (list A)) (inj: injective_on f G)(l: list A): l ∈ G →  f l ∈ collectFunctionResults f G :=
begin
  induction G with hd tl ih,
  simp [collectFunctionResults],

  by_cases lhd: l = hd,
  rw lhd,
  unfold collectFunctionResults,
  simp,

  unfold collectFunctionResults,
  simp [lhd],
  intro ltl,
  right,
  apply ih,
  apply injective_on_under_head_removed f tl hd inj,
  exact ltl,
end

lemma collectFunctionResults_SDR_semantics_2 (f: list A → A)  (G: list (list A)) (inj: injective_on f G)(l: list A):  f l ∈ collectFunctionResults f G → ∃ (l': list A), l' ∈ G ∧ f l' = f l :=
begin
  induction G with hd tl ih,
  unfold collectFunctionResults,
  simp,

  unfold collectFunctionResults,
  simp,
  intro h,
  cases h,
  existsi hd,
  rw h,
  simp,
  simp [injective_on_under_head_removed f tl hd inj, h] at ih,
  cases ih with il il_proof,
  existsi il,
  simp [il_proof],
end


lemma mt_easy (G: list (list A)) (f:(list A) → A ) (inj: injective_on f G): set_size G ≤ set_size (collectFunctionResults f G) :=
begin
  induction G with hd tl ih,
  simp [collectFunctionResults],
  refl,

  unfold collectFunctionResults,
  unfold set_size,

  by_cases hd ∈ tl,
  have fhd: (f hd ∈ collectFunctionResults f tl),
  apply collectFunctionResults_SDR_semantics_1,
  apply injective_on_under_head_removed f tl hd inj,
  exact h,
  simp [h, fhd],
  apply ih,
  apply injective_on_under_head_removed f tl hd inj,

  have fhd: (f hd ∉ collectFunctionResults f tl),
  by_contradiction fhd,
  have e: ∃ (l: list A), l ∈ tl ∧ f l = f hd,
  apply collectFunctionResults_SDR_semantics_2,
  apply injective_on_under_head_removed f tl hd inj,
  apply fhd,
  cases e,
  cases e_h,
  unfold injective_on at inj,
  have member:  e_w ∈ hd::tl ∧ hd ∈ hd::tl,
  simp [e_h_left],
  have ewhd:e_w = hd,
  apply inj,
  exact member,
  exact e_h_right,
  rw ewhd at e_h_left,
  exact absurd e_h_left h,

  simp [h, fhd],
  rw ← succ_eq_add_one,
  rw ← succ_eq_add_one,
  apply nat.succ_le_succ,
  apply ih,
  apply injective_on_under_head_removed f tl hd inj,
end

lemma collectFunctionResults_is_subset_of_family_union (G: list (list A)) (f:(list A) → A ) (sdr: SDR f G): subset (collectFunctionResults f G) (family_union G):=
begin
  induction G with hd tl ih,
  simp [collectFunctionResults, family_union, subset],

  unfold subset,
  intro a,
  unfold collectFunctionResults,
  unfold family_union,
  unfold SDR at sdr,
  cases sdr with inj sdr_prop,
  have sdr: SDR f (hd::tl),
  unfold SDR,
  split,
  exact inj,
  exact sdr_prop,

  by_cases ha: a = (f hd),
  rw ha,
  simp [in_union_iff_in_either],
  left,
  apply sdr_prop,
  simp,

  unfold subset at ih,
  simp [ha],
  intro cf,
  rw in_union_iff_in_either,
  right,
  apply ih,
  have subs: subset tl (hd::tl),
  unfold subset,
  intro a,
  intro atl,
  simp [atl],
  apply SDR_on_under_subset f (hd::tl) tl sdr subs,
  exact cf,
end

theorem marriage_theorem (F: list (list A)) (non_empty: ∀(G: list A), G ∈ F →  G ≠ nil)  : (∃ (f:(list A) → A ), SDR f F) ↔  (∀ (G: list (list A)), (subset G F → set_size(G) ≤ set_size (family_union G))) :=
begin
  split,
  intro hf,
  cases hf with f sdr_f,
  unfold SDR at sdr_f,
  cases sdr_f with inj ssp,
  intro G,
  intro subG,

  have leq1: set_size G ≤ set_size (collectFunctionResults f G),
  apply mt_easy G f (injective_on_under_subset f F G inj subG),
  have leq2: set_size (collectFunctionResults f G) ≤ set_size(family_union G),
  apply subset_size_leq,
  apply collectFunctionResults_is_subset_of_family_union,
  unfold SDR,
  simp [injective_on_under_subset f F G inj subG, ssp],
  intro l,
  intro lG,
  apply ssp,
  unfold subset at subG,
  apply subG,
  exact lG,
  
  apply nat.le_trans leq1 leq2,

  induction h: (set_size F) generalizing F,
  have F_empty: F = nil,
  rw ←  size_0_iff_empty_set,
  exact h,

  intro mc,
  rw F_empty,
  existsi (λ (l: list A), classical.choice _inst_2),
  apply SDR_on_empty_set,

  intro mc,

  by_cases critical: ∃ (C: list (list A)), subset C F ∧ set_size C = set_size (family_union C),
  cases critical,


  
  
  
end

end marriage_theorem

end listSet