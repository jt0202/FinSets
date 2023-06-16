import init.algebra.order tactic.rcases data.list.sort logic.basic
open list


inductive binaryTree (A : Type)
| empty: binaryTree 
| node : binaryTree  -> A -> binaryTree -> binaryTree

variables {A: Type} [linear_order A]
def member: A -> binaryTree A -> Prop
| x binaryTree.empty := false 
| x (binaryTree.node tl a tr) := (x =a ) ∨ member x tl ∨  member x tr


def member_bool: A -> binaryTree A -> bool
| x binaryTree.empty := ff 
| x (binaryTree.node tl a tr) := (x =a ) ∨ member_bool x tl ∨  member_bool x tr

lemma member_iff_member_bool (a:A) (T: binaryTree A): member a T ↔ member_bool a T = tt :=
begin
  induction T with tl x tr h_tl h_tr,
  unfold member,
  unfold member_bool,
  simp,

  unfold member,
  unfold member_bool,
  rw h_tl,
  rw h_tr,
  simp,
end

noncomputable lemma member_decidable (a:A) (T: binaryTree A): decidable (member a T) :=
begin
  rw member_iff_member_bool,
  apply bool.decidable_eq,
end

def flatten: binaryTree A -> list A 
| binaryTree.empty := []
| (binaryTree.node tl x tr) := (flatten tl) ++ (x:: flatten tr)

lemma member_in_tree_iff_in_flat (a:A)(t:binaryTree A): member a t ↔ a ∈ flatten t :=
begin
  induction t with tl x tr h_tl h_tr,
  simp[flatten, member],

  simp[flatten, member],
  rw h_tl,
  rw h_tr,
  by_cases (a=x),
  simp[h],
  simp[h],
end


def forall_keys  (p: A -> A -> Prop) (a : A) (t: binaryTree A): Prop :=
  ∀ a', (member a' t) -> p a a'

def ordered: binaryTree A -> Prop
| binaryTree.empty := true
| (binaryTree.node  tl x tr) := ordered tl ∧ ordered tr ∧ (forall_keys (>) x tl) ∧ (forall_keys (<) x tr)

-- use this to show tree_extensionality
lemma flatten_is_sorted (t: binaryTree A) (o: ordered t): sorted (<) (flatten t) :=
begin
  induction t with tl x tr h_tl h_tr,
  unfold flatten,
  apply list.sorted_nil,

  unfold ordered at o,
  cases o with o_tl o_right,
  cases o_right with o_tr,
  cases o_right_right,
  unfold flatten,
  induction ftl:(flatten tl),
  rw nil_append,
  rw list.sorted_cons,
  split,
  unfold forall_keys at o_right_right_right,
  simp [member_in_tree_iff_in_flat] at o_right_right_right,
  apply o_right_right_right,
  apply h_tr,
  exact o_tr,

  rw list.cons_append,
  rw list.sorted_cons,
  sorry,
end


def ordered_member : A -> binaryTree A -> Prop
| x binaryTree.empty := false 
| x (binaryTree.node tl a tr) := 
  if x < a then ordered_member x tl
  else if x > a then ordered_member x tr
  else x = a

lemma ordered_member_eq_member_in_searchtree (T: binaryTree A) (o: ordered T) (x: A): member x T ↔ ordered_member x T :=
begin
  induction T with tl a tr h_tl h_tr,
  simp [member, ordered_member],

  split,
  unfold member,
  unfold ordered_member,
  by_cases h: x=a,
  simp [h],
  have alta: ¬ a < a,
  simp,
  simp [h, alta],
  
  unfold ordered at o,
  cases o with o_tl o_right,
  cases o_right with o_tr,
  cases o_right_right,
  -- if mem left, then x < a
  
  intro mem,
  cases mem,
  have xa: x < a,
  unfold forall_keys at o_right_right_left,
  apply o_right_right_left,
  exact mem,
  rw if_pos,
  rw ← h_tl,
  exact mem,
  exact o_tl,
  exact xa,

  -- if mem right, then x > a
  have xa: x > a,
  unfold forall_keys at o_right_right_right,
  apply o_right_right_right,
  exact mem,
  rw if_neg,
  split,
  exact xa,
  rw ← h_tr,
  exact mem,
  exact o_tr,
  simp,
  apply le_of_lt_or_eq,
  left,
  apply xa,

  unfold ordered at o,
  cases o with o_tl o_right,
  cases o_right with o_tr,
  cases o_right_right,
  unfold member,
  unfold ordered_member, 
  by_cases x_eq_a: x=a,
  simp [x_eq_a],

  simp [x_eq_a],
  by_cases x_lt_a: x < a,
  simp [x_lt_a],
  intro om,
  left,
  rw h_tl,
  exact om,
  exact o_tl,

  simp [x_lt_a],
  intro x_gt_a,
  intro om,
  right,
  rw h_tr,
  exact om,
  exact o_tr,
end

def set_equality  (T1 T2: binaryTree A): Prop := flatten (T1) = flatten(T2)

lemma set_equality_symm {T1 T2: binaryTree A} (h: set_equality T1 T2): set_equality T2 T1 :=
begin
  unfold set_equality,
  unfold set_equality at h,
  rw h,
end

theorem tree_extensionality  (T1 T2: binaryTree A): set_equality T1 T2 ↔ (∀ (a:A), member a T1 ↔ member a T2) :=
begin
  split,
  -- easy direction
  intro seq,
  intro a,
  unfold set_equality at seq,
  rw member_in_tree_iff_in_flat,
  rw member_in_tree_iff_in_flat,
  rw seq,

  unfold set_equality,
  simp [member_in_tree_iff_in_flat],
  
  -- need order property here
  intro mem_prop,
  sorry,
end
section insert_and_union

def unbalanced_insert : A -> binaryTree A -> binaryTree A
| x binaryTree.empty := (binaryTree.node binaryTree.empty x binaryTree.empty)
| x (binaryTree.node  tl a tr) := 
  if (x = a)
    then (binaryTree.node tl a tr)
  else if x < a 
    then binaryTree.node (unbalanced_insert x tl) a tr
  else
    binaryTree.node tl a (unbalanced_insert x tr)

lemma member_after_insert (a: A) (t: binaryTree A): member a (unbalanced_insert a t) :=
begin
  induction t with tl x tr h_tl h_tr,
  unfold unbalanced_insert,
  unfold member,
  left,
  refl,

  unfold unbalanced_insert,
  by_cases ax: a=x,
  rw if_pos ax,
  unfold member,
  left,
  exact ax,

  rw if_neg,
  by_cases a_lt_x: a < x,
  rw if_pos a_lt_x,
  unfold member,
  right,
  left,
  exact h_tl,
  rw if_neg a_lt_x,
  unfold member,
  right,
  right,
  exact h_tr,
  exact ax,
end

lemma insert_keeps_previous_members (t:binaryTree A) (a b:A): member a t → member a (unbalanced_insert b t) :=
begin
  induction t with tl x tr h_tl h_tr,
  unfold unbalanced_insert,
  unfold member,
  intro f,
  right,
  left,
  exact f,

  unfold unbalanced_insert,
  unfold member,
  intro mem,

  by_cases bx: b=x,
  rw if_pos bx,
  unfold member,
  exact mem,

  rw if_neg bx,
  by_cases b_lt_x: b < x,
  rw if_pos b_lt_x,
  unfold member,
  cases mem,
  left,
  exact mem,
  cases mem,
  right,
  left,
  apply h_tl,
  exact mem,
  right,
  right,
  exact mem,

  rw if_neg b_lt_x,
  unfold member,
  cases mem,
  left,
  exact mem,
  cases mem,
  right,
  left,
  exact mem,
  right,
  right,
  apply h_tr,
  exact mem,
end

lemma insert_only_adds_argument (a b: A) (t: binaryTree A): member b (unbalanced_insert a t) → member b t ∨ (b=a) :=
begin
  induction t with tl x tr h_tl h_tr,
  unfold unbalanced_insert,
  unfold member,
  cc,

  unfold unbalanced_insert,
  by_cases ax: a=x,
  rw if_pos ax,
  intro mem,
  left,
  exact mem,

  rw if_neg ax,
  by_cases a_lt_x: a < x,
  rw if_pos a_lt_x,
  unfold member,
  intro mem,

  cases mem,
  left,
  left,
  exact mem,

  cases mem,
  -- organize the or elements in a complicated way to match later. how to do it easier ?
  rw or.assoc,
  right,
  rw or.comm,
  rw ← or.assoc,
  left,
  rw or.comm,
  apply h_tl,
  exact mem,
  
  left,
  right,
  right,
  exact mem,

  rw if_neg a_lt_x,
  unfold member,
  intro mem,
  cases mem,
  left,
  left,
  exact mem,
  cases mem,
  left,
  right,
  left,
  exact mem,
  rw or.assoc,
  rw or.assoc,
  right,
  right,
  apply h_tr,
  exact mem,
end

lemma insert_semantics (a:A) (t: binaryTree A): ∀ (b:A), member b (unbalanced_insert a t) ↔ member b t ∨ b = a :=
begin
  intro b,
  split,
  apply insert_only_adds_argument,

  intro mem,
  cases mem,
  apply insert_keeps_previous_members t b a mem,
  rw mem,
  apply member_after_insert,
end

lemma insert_preserves_order (a: A)(t: binaryTree A) (o: ordered t): ordered (unbalanced_insert a t) :=
begin
  induction t with tl x tr h_tl h_tr,
  unfold unbalanced_insert,
  unfold ordered,
  unfold forall_keys,
  unfold member,
  simp,

  unfold unbalanced_insert,
  by_cases ax: a=x,
  rw if_pos ax,
  exact o,
  rw if_neg ax,
  unfold ordered at o,
  cases o with o_tl o_rest,
  cases o_rest with o_tr o_rest,
  cases o_rest with fk_tl fk_tr,
  by_cases a_lt_x: a < x,
  rw if_pos a_lt_x,
  unfold ordered,
  split,
  apply h_tl,
  exact o_tl,
  split,
  exact o_tr,
  split,
  unfold forall_keys,
  intro a',
  rw insert_semantics,
  intro mem,
  cases mem,
  unfold forall_keys at fk_tl,
  apply fk_tl,
  exact mem,
  rw ← mem at a_lt_x,
  apply a_lt_x,
  exact fk_tr,

  rw if_neg a_lt_x,
  unfold ordered,
  split,
  exact o_tl,
  split,
  apply h_tr,
  exact o_tr,
  split,
  exact fk_tl,
  unfold forall_keys,
  intro a',
  rw insert_semantics,
  intro mem,
  cases mem,
  unfold forall_keys at fk_tr,
  apply fk_tr,
  exact mem,
  rw mem,
  push_neg at a_lt_x,
  rw lt_iff_le_and_ne,
  split,
  exact a_lt_x,
  simp,
  intro h,
  apply ax,
  apply eq.symm,
  exact h,
end

lemma lt_implies_neq {a x: A}: (a < x) -> ¬ (a = x) :=
begin
  intro h,
  by_contradiction h1,
  rw h1 at h,
  apply lt_irrefl x,
  exact h,
end

lemma inserting_member_has_no_effect {a: A} {t: binaryTree A} (mem: member a t) (o: ordered t): t = unbalanced_insert a t :=
begin
  induction t with tl x tr h_tl h_tr,
  exfalso,
  unfold member at mem,
  exact mem,

  unfold unbalanced_insert,
  by_cases ax: a=x,
  rw if_pos ax,

  rw if_neg ax,
  by_cases a_lt_x: a < x,
  rw if_pos a_lt_x,
  rw ordered_member_eq_member_in_searchtree at mem,
  unfold ordered_member at mem,
  rw if_pos a_lt_x at mem,
  rw ←  h_tl,
  rw ordered_member_eq_member_in_searchtree,
  exact mem,
  unfold ordered at o,
  cases o,
  exact o_left,
  cases o,
  exact o_left,
  exact o,

  rw if_neg a_lt_x,
  rw ordered_member_eq_member_in_searchtree at mem,
  unfold ordered_member at mem,
  rw if_neg a_lt_x at mem,
  have lt_gt: a > x ∨ a < x,
  apply lt_or_gt_of_ne,
  apply ne.symm,
  exact ax,
  have a_gt_x: a > x,
  simp [a_lt_x]  at lt_gt,
  exact lt_gt,
  rw if_pos a_gt_x at mem,
  unfold ordered at o,
  cases o,
  cases o_right,
  rw ← h_tr,
  rw ← ordered_member_eq_member_in_searchtree tr o_right_left at mem,
  exact mem,
  exact o_right_left,
  exact o,
end

def union: binaryTree A -> binaryTree A -> binaryTree A
| B binaryTree.empty := B
| B (binaryTree.node tl x tr) := union ( union (unbalanced_insert x B) tl) tr

lemma in_union_iff_in_either (X Y: binaryTree A) (a: A): member a (union X Y) ↔ member a X ∨ member a Y :=
begin
  induction Y with tl x tr h_tl h_tr generalizing X,
  unfold union,
  unfold member,
  simp,

  unfold union,
  rw h_tr,
  rw h_tl,
  unfold member,
  rw insert_semantics,
  cc,
end

lemma union_preserves_order (X Y: binaryTree A) (o: ordered X): ordered(union X Y) :=
begin
  induction Y with tl x tr h_tl h_tr generalizing X,
  unfold union,
  exact o,

  unfold union,
  apply h_tr,
  apply h_tl,
  apply insert_preserves_order,
  exact o,
end

def subset (X Y: binaryTree A): Prop := ∀ (a:A), member a X → member a Y

lemma subset_reflexive (X: binaryTree A): subset X X:=
begin
  unfold subset,
  intro a,
  intro h,
  exact h,
end

lemma union_with_subset_doesnt_change (X Y: binaryTree A) (subs: subset X Y) (ox: ordered X) (oy: ordered Y): union Y X = Y :=
begin
  induction X with tl x tr h_tl h_tr,
  unfold union,

  unfold union,
  have xY: member x Y,
  unfold subset at subs,
  apply subs,
  unfold member,
  left,
  refl,
  rw ←  inserting_member_has_no_effect xY oy,
  have subs_tl: subset tl Y,
  unfold subset,
  unfold subset at subs,
  intro a,
  intro mem_a_tl,
  apply subs,
  unfold member,
  right,
  left,
  exact mem_a_tl,
  unfold ordered at ox,
  cases ox with o_tl o_rest,
  rw h_tl subs_tl o_tl,

  have subs_tr: subset tr Y,
  unfold subset,
  unfold subset at subs,
  intro a,
  intro mem_a_tr,
  apply subs,
  unfold member,
  right,
  right,
  exact mem_a_tr,
  cases o_rest with o_tr,
  rw h_tr subs_tr o_tr,
end

lemma union_idempotent (X: binaryTree A) (o: ordered X): union X X = X :=
begin
  apply union_with_subset_doesnt_change,
  apply subset_reflexive,
  exact o,
  exact o,
end

lemma union_comm (X Y: binaryTree A): set_equality (union X Y) (union Y X) :=
begin
  rw tree_extensionality,
  intro a,
  rw in_union_iff_in_either,
  rw in_union_iff_in_either,
  tauto,
end


def comprehension: (A -> bool) ->  binaryTree A -> binaryTree A
| φ binaryTree.empty := binaryTree.empty
| φ (binaryTree.node tl x tr) :=  if φ x = tt then union (unbalanced_insert x (comprehension φ tl)) (comprehension φ tr) else union (comprehension φ tl) (comprehension φ tr)

lemma comprehension_semantics (φ: A -> bool) (t: binaryTree A) (a:A):  member a (comprehension φ t) ↔ φ a = tt ∧ member a t :=
begin
  induction t with tl x tr h_tl h_tr,
  unfold comprehension,
  unfold member,
  simp,

  unfold comprehension,
  unfold member,
  by_cases phix: φ x = tt,
  rw if_pos phix,
  rw in_union_iff_in_either,
  rw h_tr,
  rw insert_semantics,
  rw h_tl,

  -- cases phi a to simplify
  by_cases phia: φ a = tt,
  simp [phia],
  cc,
  simp [phia],
  by_contradiction,
  rw h at phia,
  exact absurd phix phia,

  rw if_neg phix,
  rw in_union_iff_in_either,
  rw h_tl,
  rw h_tr,
  by_cases phia: φ a = tt,
  simp [phia],
  have ax: ¬ a =x,
  by_contradiction,
  rw h at phia,
  exact absurd phia phix,
  simp [ax],
  simp [phia],
end

lemma comprehension_preserves_order (φ: A -> bool) (t: binaryTree A) (o: ordered t): ordered (comprehension φ t) :=
begin
  induction t with tl x tr h_tl h_tr,
  unfold comprehension,

  unfold ordered at o,
  cases o with o_tl o_rest,
  unfold comprehension,
  by_cases phix: φ x =tt,
  rw if_pos phix,
  apply union_preserves_order,
  apply insert_preserves_order,
  apply h_tl,
  exact o_tl,

  rw if_neg phix,
  apply union_preserves_order,
  apply h_tl,
  exact o_tl,
end

def intersection (X Y: binaryTree A) : binaryTree A := comprehension (λ (a:A), member_bool a X) Y

def disjoint_tree (X Y: binaryTree A): Prop := set_equality (intersection X Y) binaryTree.empty

lemma in_intersection_iff_in_both (a:A) (X Y: binaryTree A): member a (intersection X Y) ↔ member a X ∧ member a Y :=
begin
  unfold intersection,
  rw comprehension_semantics,
  rw ← member_iff_member_bool,
end

lemma intersection_preserves_order (X Y: binaryTree A) (oy: ordered Y): ordered (intersection X Y) :=
begin
  unfold intersection,
  apply comprehension_preserves_order,
  exact oy,
end

def difference (X Y: binaryTree A) : binaryTree A := comprehension (λ (a:A), ¬ (member_bool a Y = tt)) X

lemma pull_out_negation_to_bool (a: bool): to_bool(¬ a = tt) =tt ↔ ¬ a = tt :=
begin
  cases a,
  simp,
  simp,
end

lemma in_difference_if_only_in_first (a:A) (X Y: binaryTree A): member a (difference X Y) ↔ member a X ∧ ¬ member a Y :=
begin
  unfold difference,
  rw comprehension_semantics,
  rw pull_out_negation_to_bool,
  rw  ← member_iff_member_bool,
  rw and.comm,
end

lemma difference_preserves_ordered (X Y: binaryTree A) (ox: ordered X): ordered (difference X Y) :=
begin
  unfold difference,
  apply comprehension_preserves_order,
  exact ox,
end

lemma difference_and_tree_are_seteq_union (X Y :binaryTree A): set_equality (union X Y) (union X (difference Y X)) :=
begin
  rw  tree_extensionality,
  intro a,
  rw in_union_iff_in_either,
  rw in_union_iff_in_either,
  rw in_difference_if_only_in_first,
  rw or_and_distrib_left,
  tauto,
end

lemma intersection_and_difference_are_seteq_set (X Y: binaryTree A): set_equality (union (difference X Y) (intersection X Y)) (X) :=
begin
  rw tree_extensionality,
  intro a,
  rw in_union_iff_in_either,
  rw in_intersection_iff_in_both,
  rw in_difference_if_only_in_first,
  by_cases aY: member a Y,
  simp[aY],
  simp[aY],
end

lemma intersection_and_difference_are_disjoint (X Y: binaryTree A): disjoint_tree (difference X Y) (intersection X Y) :=
begin
  unfold disjoint_tree,
  rw tree_extensionality,
  intro a,
  rw in_intersection_iff_in_both,
  rw in_intersection_iff_in_both,
  rw in_difference_if_only_in_first,
  unfold member,
  tauto,
end

lemma difference_and_set_are_disjoint (X Y: binaryTree A): disjoint_tree (difference Y X) X :=
begin
  unfold disjoint_tree,
  rw tree_extensionality,
  intro a,
  rw in_intersection_iff_in_both,
  rw in_difference_if_only_in_first,
  tauto,
end

lemma difference_and_set_are_union (X Y: binaryTree A): set_equality (union (difference Y X) X )  (union X Y) :=
begin
  rw tree_extensionality,
  intro a,
  rw in_union_iff_in_either,
  rw in_union_iff_in_either,
  rw in_difference_if_only_in_first,
  rw and_or_distrib_right,
  by_cases aX: member a X,
  simp [aX],
  simp [aX],
end

end insert_and_union

section delete

end delete

section size

def size: binaryTree A -> ℕ 
| binaryTree.empty := 0
| (binaryTree.node tl x tr) := 1 +size tl + size tr

lemma size_eq_flatten_size (X: binaryTree A): size X = length (flatten X) :=
begin
  induction X with tl x tr h_tl h_tr,
  unfold flatten,
  unfold size,
  simp,

  unfold size,
  unfold flatten,
  simp,
  rw h_tl,
  rw h_tr,
  rw nat.add_comm (flatten tr).length 1,
  rw ← nat.add_assoc,
  rw nat.add_comm _ 1,
end

lemma set_equal_trees_have_same_size (X Y: binaryTree A) (hxy: set_equality X Y): size X = size Y :=
begin
  rw size_eq_flatten_size,
  rw size_eq_flatten_size,
  unfold set_equality at hxy,
  rw hxy,
end

lemma add_new_member_increases_size (a: A) (t: binaryTree A) (not_mem: ¬ member a t): size (unbalanced_insert a t) = size(t) + 1 :=
begin
  induction t with tl x tr h_tl h_tr,
  unfold unbalanced_insert,
  unfold size,

  unfold unbalanced_insert,
  by_cases ax: a=x,
  exfalso,
  rw ax at not_mem,
  unfold member at not_mem,
  simp at not_mem,
  exact not_mem,

  unfold member at not_mem,
  push_neg at not_mem,
  cases not_mem,
  cases not_mem_right,
  rw if_neg ax,
  by_cases a_lt_x: a < x,
  rw if_pos a_lt_x,
  unfold size,
  rw h_tl,
  rw  nat.add_assoc,
  rw nat.add_assoc,
  rw nat.add_comm 1 (size tr),
  rw ← nat.add_assoc,
  rw ← nat.add_assoc,
  exact not_mem_right_left,
  
  rw if_neg a_lt_x,
  unfold size,
  rw h_tr,
  rw ←  nat.add_assoc,
  exact not_mem_right_right,
end

lemma disjoint_union_process_1 (X tl tr: binaryTree A) (y:A) (disj: disjoint_tree X (binaryTree.node tl y tr)) (o: ordered (binaryTree.node tl y tr)): disjoint_tree (unbalanced_insert y X) tl :=
begin
  unfold disjoint_tree,
  rw tree_extensionality,
  simp_rw [in_intersection_iff_in_both, member],
  intro a,
  rw insert_semantics,
  by_cases h: member a tl,
  unfold ordered at o,
  rcases o with ⟨o_tl, o_tr,fk_tl, fk_tr⟩,

  have y_gt_a: y > a,
  apply fk_tl,
  apply h,
  have ay: ¬ a =y,
  unfold forall_keys at fk_tl,
  apply ne_of_lt,
  apply y_gt_a,


  have aX: ¬ member a X,
  unfold disjoint_tree at disj,
  rw tree_extensionality at disj,
  simp [member, in_intersection_iff_in_both] at disj,
  by_contradiction aX,
  have hax: member a X → ¬(a = y ∨ member a tl ∨ member a tr),
  apply disj,
  apply hax,
  apply aX,
  right,
  left,
  apply h,

  simp[aX, ay],

  simp [h],
end

lemma disjoint_union_process_2 (X tl tr: binaryTree A) (y:A) (disj: disjoint_tree X (binaryTree.node tl y tr)) (o: ordered (binaryTree.node tl y tr)): disjoint_tree (union (unbalanced_insert y X) tl) tr :=
begin
  unfold disjoint_tree,
  rw tree_extensionality,
  intro a,
  rw in_intersection_iff_in_both,
  rw in_union_iff_in_either,
  rw insert_semantics,
  unfold member,
  by_cases a_tr: member a tr,
  rcases o with ⟨o_tl, o_tr,fk_tl, fk_tr⟩,

  have y_lt_a: y < a,
  unfold forall_keys at fk_tr,
  apply fk_tr,
  exact a_tr,

  have ay: ¬ a= y,
  apply ne_of_gt,
  apply y_lt_a,

  have a_tl: ¬ member a tl,
  by_contradiction,
  unfold forall_keys at fk_tl,
  have y_gt_a: y > a,
  apply fk_tl,
  apply h,
  exact absurd y_lt_a (not_lt_of_gt y_gt_a),

  have aX: ¬ member a X,
  unfold disjoint_tree at disj,
  rw tree_extensionality at disj,
  simp [member, in_intersection_iff_in_both] at disj,
  by_contradiction,
  have aY: ¬(a = y ∨ member a tl ∨ member a tr),
  apply disj,
  apply h,
  push_neg at aY,
  rcases aY with ⟨a1, a2, a3⟩,
  exact absurd a_tr a3,

  simp [ay, aX, a_tl],
  simp [a_tr],
end

lemma disjoint_size (X Y: binaryTree A) (disj: disjoint_tree X Y) (ox: ordered X) (oy: ordered Y): size(union X Y) = size X + size Y :=
begin
  induction Y with tl y tr h_tl h_tr generalizing X,
  unfold union,
  unfold size,
  refl,

  unfold union,
  
  have yX: ¬ member y X,
  have y_disj: ¬ (member y X ∧ member y (binaryTree.node tl y tr)),
  unfold disjoint_tree at disj,
  rw tree_extensionality at disj,
  simp [member] at disj,
  simp_rw in_intersection_iff_in_both at disj,
  apply disj,
  unfold member at y_disj,
  simp at y_disj,
  exact y_disj,
  



  have yX_tl_disj: disjoint_tree (unbalanced_insert y X) tl,
  apply disjoint_union_process_1 X tl tr y disj oy,

  have yXtl_tr_disj: disjoint_tree (union (unbalanced_insert y X) tl) tr,
  apply disjoint_union_process_2 X tl tr y disj oy,

  cases oy with oy_tl oy_rest,
  cases oy_rest with oy_tr oy_rest, 
  rw h_tr oy_tr _ yXtl_tr_disj (union_preserves_order (unbalanced_insert y X) tl (insert_preserves_order y X ox)),
  rw h_tl oy_tl _ yX_tl_disj (insert_preserves_order y X ox),
  rw add_new_member_increases_size y X yX,
  unfold size,
  repeat {rw ← nat.add_assoc},
end

theorem inclusion_exclusion (X Y: binaryTree A) (ox: ordered X) (oy: ordered Y): size( union X Y) + size (intersection X Y) = size X + size Y :=
begin
  have h: size X= size (union (difference X Y) (intersection X Y)),
  apply set_equal_trees_have_same_size,
  apply set_equality_symm,
  apply intersection_and_difference_are_seteq_set,

  rw h,
  rw disjoint_size _ _ (intersection_and_difference_are_disjoint X Y) (difference_preserves_ordered X Y ox) (intersection_preserves_order X Y oy),
  rw nat.add_comm,
  rw nat.add_comm (size (difference X Y)) _,
  rw nat.add_assoc,

  have sxy: (size (difference X Y) + size Y) = size (union X Y),
  rw ← disjoint_size _ _ (difference_and_set_are_disjoint Y X) (difference_preserves_ordered X Y ox) oy,
  rw set_equal_trees_have_same_size (union X Y) (union Y X) (union_comm X Y),
  apply set_equal_trees_have_same_size _ _ (difference_and_set_are_union Y X),

  rw sxy,
end
end size