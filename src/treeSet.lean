import init.algebra.order tactic.rcases data.list.sort logic.basic
open list

namespace binaryTree
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

def singleton (a: A): binaryTree A := binaryTree.node (binaryTree.empty) a (binaryTree.empty)

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

lemma flatten_nil_iff_tree_empty (t: binaryTree A): flatten t = nil ↔ t = binaryTree.empty :=
begin
  split,
  cases t with tl a tr,
  intro h,
  refl,
  have a_t: a ∈ flatten (binaryTree.node tl a tr),
  rw ← member_in_tree_iff_in_flat,
  unfold member,
  left,
  refl,
  intro h,
  exfalso,
  rw h at a_t,
  rw ← list.mem_nil_iff a,
  exact a_t,

  intro h,
  rw h,
  unfold flatten,
end


def forall_keys  (p: A -> A -> Prop) (a : A) (t: binaryTree A): Prop :=
  ∀ a', (member a' t) -> p a a'

def ordered: binaryTree A -> Prop
| binaryTree.empty := true
| (binaryTree.node  tl x tr) := ordered tl ∧ ordered tr ∧ (forall_keys (>) x tl) ∧ (forall_keys (<) x tr)

lemma emptyTree_ordered: ordered (binaryTree.empty: binaryTree A) := by unfold ordered

lemma singleton_ordered (a:A): ordered (singleton a) :=
begin
  unfold singleton,
  unfold ordered,
  unfold forall_keys,
  simp[member],
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

lemma root_not_in_left_subtree {A: Type} [linear_order A](a: A) (tl tr: binaryTree A) (o: ordered (binaryTree.node tl a tr)): ¬ member a tl :=
begin
  rcases o with ⟨o_tl, o_tr, fk_tl, fk_tr⟩,
  by_contradiction,
  unfold forall_keys at fk_tl,
  have aa: a > a,
  apply fk_tl,
  exact h,
  have naa: ¬ a > a,
  push_neg,
  apply le_refl,
  exact absurd aa naa,
end

lemma root_not_in_right_subtree {A: Type} [linear_order A](a: A) (tl tr: binaryTree A) (o: ordered (binaryTree.node tl a tr)): ¬ member a tr :=
begin
  rcases o with ⟨o_tl, o_tr, fk_tl, fk_tr⟩,
  by_contradiction,
  unfold forall_keys at fk_tr,
  have aa: a < a,
  apply fk_tr,
  exact h,
  have naa: ¬ a < a,
  push_neg,
  apply le_refl,
  exact absurd aa naa,
end

lemma smaller_elements_not_in_right_subtree {A: Type} [linear_order A](a x: A) (tl tr: binaryTree A) (o: ordered (binaryTree.node tl a tr)) (xa: x < a): ¬ member x tr :=
begin
  by_contradiction,
  rcases o with ⟨o_tl, o_tr, fk_tl, fk_tr⟩,
  unfold forall_keys at fk_tr,
  have ax: a < x,
  apply fk_tr,
  exact h,
  have nax: ¬ a < x,
  push_neg,
  apply le_of_lt,
  exact xa,
  exact absurd ax nax,
end

lemma greater_elements_not_in_left_subtree {A: Type} [linear_order A](a x: A) (tl tr: binaryTree A) (o: ordered (binaryTree.node tl a tr)) (xa: x > a): ¬ member x tl :=
begin
  by_contradiction,
  rcases o with ⟨o_tl, o_tr, fk_tl, fk_tr⟩,
  unfold forall_keys at fk_tl,
  have ax: a > x,
  apply fk_tl,
  exact h,
  have nxa: ¬ x > a,
  push_neg,
  apply le_of_lt,
  exact ax,
  exact absurd xa nxa,
end


def set_equality (A: Type)[linear_order A] (T1 T2: binaryTree A): Prop := flatten (T1) = flatten(T2)

lemma set_equality_refl: reflexive (set_equality A) := 
begin
  unfold reflexive,
  intro x,
  unfold set_equality,
end

lemma set_equality_symm: symmetric (set_equality A) :=
begin
  unfold1 symmetric,
  intros x y,
  unfold set_equality,
  intro h,
  rw h,
end

lemma set_equality_trans: transitive (set_equality A) :=
begin
  unfold transitive,
  unfold set_equality,
  intros x y z h1 h2,
  rw h1,
  rw h2,
end

lemma set_equality_is_equiv: equivalence (set_equality A) 
 := mk_equivalence (set_equality A) set_equality_refl set_equality_symm set_equality_trans

lemma first_element_of_flatten_is_root_or_left_subtree (hd x: A) (ltl: list A) (t tl tr: binaryTree A)(h1: t = (binaryTree.node tl x tr)) (h2: flatten t = hd::ltl): hd = x ∨ member hd tl :=
begin
  rw h1 at h2,
  unfold flatten at h2,
  rw member_in_tree_iff_in_flat,
  cases h:(flatten tl) with hd2 tl2,
  rw h at h2,
  rw nil_append at h2,
  left,
  apply eq.symm,
  apply list.head_eq_of_cons_eq h2,
  rw h at h2,
  right,
  simp,
  left,
  apply eq.symm,
  apply list.head_eq_of_cons_eq h2,
end

lemma flatten_nodup (T: binaryTree A) (o:ordered T): nodup (flatten T) :=
begin
  induction h:T with tl x tr h_tl h_tr generalizing T,
  unfold flatten,
  apply list.nodup_nil,

  rw h at o,
  have o2: ordered (binaryTree.node tl x tr),
  exact o,
  rcases o with ⟨o_tl, o_tr, fk_tl, fk_tr⟩,
  unfold flatten,
  rw list.nodup_append,
  rw list.nodup_cons,
  split,
  apply h_tl tl o_tl,
  refl,
  split,
  split,
  rw ← member_in_tree_iff_in_flat,
  apply root_not_in_right_subtree x tl tr o2,
  apply h_tr tr o_tr,
  refl,

  unfold list.disjoint,
  intro a,
  rw ← member_in_tree_iff_in_flat,
  intro a_tl,
  rw list.mem_cons_eq,
  rw ← member_in_tree_iff_in_flat,
  intro a_x_tr,
  unfold forall_keys at fk_tl,
  unfold forall_keys at fk_tr,

  cases a_x_tr,

  have x_gt_a: x > a,
  apply fk_tl,
  exact a_tl,
  rw a_x_tr at x_gt_a,
  simp at x_gt_a,
  exact x_gt_a,

  have x_gt_a: x > a,
  apply fk_tl,
  exact a_tl,

  have n_x_gt_a: ¬  x > a,
  push_neg,
  apply le_of_lt_or_eq,
  left,
  apply fk_tr,
  exact a_x_tr,

  exact absurd x_gt_a n_x_gt_a,
end

lemma list_sorted_append (l1 l2: list A) (r: A -> A -> Prop) (s1: sorted r l1) (s2: sorted r l2) (h: forall (a: A), a ∈ l1 → ∀ (b:A), b ∈ l2 → r a b): sorted r (l1 ++ l2) :=
begin
  induction l1 with hd tl ih,
  rw nil_append,
  exact s2,

  rw list.cons_append,
  rw list.sorted_cons,
  split,
  swap,
  apply ih,
  apply list.sorted.of_cons s1,  
  intro a,
  intro a_tl,
  apply h,
  rw list.mem_cons_iff,
  right,
  exact a_tl,

  rw list.sorted_cons at s1,
  cases s1,
  intro b,
  rw list.mem_append,
  intro b_tl_l2,
  cases b_tl_l2,
  apply s1_left,
  exact b_tl_l2,

  apply h,
  simp,
  exact b_tl_l2,
end

lemma flatten_sorted (T: binaryTree A) (o: ordered T): sorted has_lt.lt (flatten T) :=
begin
  induction T with tl x tr h_tl h_tr,
  unfold flatten,
  apply list.sorted_nil,

  rcases o with ⟨o_tl, o_tr, fk_tl, fk_tr⟩,
  unfold flatten,
  apply list_sorted_append,
  apply h_tl,
  exact o_tl,

  rw list.sorted_cons,
  split,
  intro b,
  rw ← member_in_tree_iff_in_flat,
  apply fk_tr,
  apply h_tr o_tr,

  unfold forall_keys at fk_tr,
  unfold forall_keys at fk_tl,
  intro a,
  rw ← member_in_tree_iff_in_flat,
  intro a_tl,
  intro b,
  rw list.mem_cons_eq,
  intro b_x_tr,
  cases b_x_tr,
  rw b_x_tr,
  apply fk_tl,
  exact a_tl,
  have x_lt_b: x < b,
  apply fk_tr,
  rw member_in_tree_iff_in_flat,
  exact b_x_tr,
  have a_lt_x: a < x,
  apply fk_tl,
  exact a_tl,
  apply has_lt.lt.trans a_lt_x x_lt_b, 
end

theorem tree_extensionality  (T1 T2: binaryTree A) (o1: ordered T1) (o2: ordered T2): set_equality A T1 T2 ↔ (∀ (a:A), member a T1 ↔ member a T2) :=
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
  have perm: (flatten T1) ~ (flatten T2),
  rw list.perm_ext (flatten_nodup T1 o1) (flatten_nodup T2 o2),
  apply mem_prop,

  apply list.eq_of_perm_of_sorted perm (flatten_sorted T1 o1) (flatten_sorted T2 o2), 
end

lemma member_sound (a:A ) (X Y: binaryTree A) (ox: ordered X) (oy: ordered Y) (s: set_equality A X Y): member a X = member a Y :=
begin
  rw tree_extensionality _ _ ox oy at s,
  rw s,
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

lemma insert_sound (a:A) (X Y: binaryTree A) (ox: ordered X) (oy: ordered Y) (seq: set_equality A X Y): set_equality A (unbalanced_insert a X) (unbalanced_insert a Y) :=
begin
  rw tree_extensionality _ _ (insert_preserves_order _ _ ox) (insert_preserves_order _ _ oy),
  intro a',
  rw insert_semantics,
  rw insert_semantics,
  rw tree_extensionality _ _ ox oy at seq,
  simp [seq],
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

lemma union_comm (X Y: binaryTree A) (ox: ordered X) (oy: ordered Y): set_equality A (union X Y) (union Y X) :=
begin
  rw tree_extensionality (union X Y) (union Y X) (union_preserves_order X Y ox) (union_preserves_order Y X oy),
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

def disjoint_tree (X Y: binaryTree A): Prop := set_equality A (intersection X Y) binaryTree.empty

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

lemma difference_and_tree_are_seteq_union (X Y :binaryTree A) (ox: ordered X) (oy: ordered Y): set_equality A (union X Y) (union X (difference Y X)) :=
begin
  rw  tree_extensionality (union X Y) (union X (difference Y X)) (union_preserves_order X Y ox) (union_preserves_order X (difference Y X) ox),
  intro a,
  rw in_union_iff_in_either,
  rw in_union_iff_in_either,
  rw in_difference_if_only_in_first,
  rw or_and_distrib_left,
  tauto,
end

lemma intersection_and_difference_are_seteq_set (X Y: binaryTree A) (ox: ordered X) (oy: ordered Y): set_equality A (union (difference X Y) (intersection X Y)) (X) :=
begin
  rw tree_extensionality (union (difference X Y) (intersection X Y)) X (union_preserves_order (difference X Y) (intersection X Y) (difference_preserves_ordered X Y ox)) ox,
  intro a,
  rw in_union_iff_in_either,
  rw in_intersection_iff_in_both,
  rw in_difference_if_only_in_first,
  by_cases aY: member a Y,
  simp[aY],
  simp[aY],
end

lemma intersection_and_difference_are_disjoint (X Y: binaryTree A) (ox: ordered X) (oy: ordered Y): disjoint_tree (difference X Y) (intersection X Y) :=
begin
  unfold disjoint_tree,
  rw tree_extensionality (intersection (difference X Y) (intersection X Y)) (binaryTree.empty) (intersection_preserves_order (difference X Y) (intersection X Y) (intersection_preserves_order X Y oy)),
  intro a,
  rw in_intersection_iff_in_both,
  rw in_intersection_iff_in_both,
  rw in_difference_if_only_in_first,
  unfold member,
  tauto,

  unfold ordered,
end

lemma difference_and_set_are_disjoint (X Y: binaryTree A) (ox: ordered X) (oy: ordered Y): disjoint_tree (difference Y X) X :=
begin
  unfold disjoint_tree,
  rw tree_extensionality (intersection (difference Y X) X) binaryTree.empty (intersection_preserves_order (difference Y X) X ox),
  intro a,
  rw in_intersection_iff_in_both,
  rw in_difference_if_only_in_first,
  tauto,

  unfold ordered,
end

lemma difference_and_set_are_union (X Y: binaryTree A) (ox: ordered X) (oy: ordered Y): set_equality A (union (difference Y X) X )  (union X Y) :=
begin
  rw tree_extensionality (union (difference Y X) X )  (union X Y) (union_preserves_order (difference Y X) X (difference_preserves_ordered Y X oy)) (union_preserves_order X Y ox),
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

def delete:A -> binaryTree A -> binaryTree A
| a (binaryTree.empty) := binaryTree.empty
| a (binaryTree.node tl x tr) := if a = x then union tl tr else if a < x then (binaryTree.node (delete a tl) x tr) else (binaryTree.node tl x (delete a tr))

lemma elements_after_delete_were_there_before (a b:A) (t: binaryTree A) (o: ordered t): member b (delete a t) → member b t :=
begin
  induction t with tl x tr h_tl h_tr,
  unfold delete,
  unfold member,
  simp,

  rcases o with ⟨o_tl, o_tr, fk_tl, fk_tr⟩,
  unfold delete,
  by_cases ax: a=x,
  simp [ax],
  rw in_union_iff_in_either,
  unfold member,
  intro h,
  cases h,
  right,
  left,
  exact h,
  right,
  right,
  exact h,

  by_cases a_lt_x: a < x,
  simp [ax, a_lt_x],
  unfold member,
  intro h,
  cases h,
  left,
  exact h,
  cases h,
  right,
  left,
  apply h_tl o_tl,
  exact h,
  right,
  right,
  exact h,

  simp [ax, a_lt_x],
  unfold member,
  intro h,
  cases h,
  left,
  exact h,
  cases h,
  right,
  left,
  exact h,
  right,
  right,
  apply h_tr o_tr,
  exact h,
end

lemma delete_preserves_order (a:A) (t: binaryTree A) (o: ordered t): ordered (delete a t) :=
begin
  induction t with tl x tr h_tl h_tr,
  unfold delete,

  rcases o with ⟨o_tl, o_tr, fk_tl, fk_tr⟩,
  unfold delete,
  by_cases ax: a=x,
  simp [ax],
  apply union_preserves_order,
  exact o_tl,
  by_cases a_lt_x: a < x,
  simp [ax, a_lt_x],
  unfold ordered,
  split,
  apply h_tl o_tl,
  split,
  exact o_tr,
  split,
  unfold forall_keys,
  unfold forall_keys at fk_tl,
  intro a',
  intro h,
  apply fk_tl,
  apply elements_after_delete_were_there_before,
  exact o_tl,
  exact h,
  exact fk_tr,

  simp[ax, a_lt_x],
  unfold ordered,
  split,
  exact o_tl,
  split,
  apply h_tr o_tr,
  split,
  exact fk_tl,
  unfold forall_keys,
  intros a' h,
  unfold forall_keys at fk_tr,
  apply fk_tr,
  apply elements_after_delete_were_there_before,
  exact o_tr,
  apply h,
end

lemma deleting_non_member_doesnt_change (a b: A) (t:binaryTree A) (mem: ¬ member a t): delete a t = t:=
begin
  induction t with tl x tr h_tl h_tr,
  unfold delete,

  unfold delete,
  unfold member at mem,
  push_neg at mem,
  rcases mem with ⟨ax, a_tl, a_tr⟩,
  simp [ax],
  by_cases a_lt_x: a < x,
  rw if_pos a_lt_x,
  rw h_tl a_tl,
  rw if_neg a_lt_x,
  rw h_tr a_tr,
end

lemma deleted_element_gone (a b: A) (t:binaryTree A) (o: ordered t) (mem: member a t ): ¬ member a (delete a t) :=
begin
  induction t with tl x tr h_tl h_tr,
  unfold delete,
  unfold member,
  simp,

  -- rw ordered_member_eq_member_in_searchtree (delete a (binaryTree.node tl x tr)) (delete_preserves_order a (binaryTree.node tl x tr) o),
  unfold delete,
  rw ordered_member_eq_member_in_searchtree (binaryTree.node tl x tr) o at mem,
  by_cases ax: a=x,
  simp [ax],
  rw in_union_iff_in_either,
  push_neg,
  split,
  apply root_not_in_left_subtree x tl tr o,
  apply root_not_in_right_subtree x tl tr o,

  have o2: ordered (binaryTree.node tl x tr),
  exact o,
  rcases o with ⟨o_tl, o_tr,fk_tl, fk_tr⟩,

  by_cases a_lt_x: a < x,
  simp [ax, a_lt_x],
  unfold member,
  push_neg,
  split,
  exact ax,
  split,
  apply h_tl o_tl,
  unfold ordered_member at mem,
  simp [a_lt_x] at mem,
  rw ← ordered_member_eq_member_in_searchtree tl o_tl at mem,
  exact mem,
  apply smaller_elements_not_in_right_subtree x a tl tr o2 a_lt_x,

  simp [ax, a_lt_x],
  unfold member,
  push_neg,
  split,
  exact ax,
  have a_gt_x: a > x,
  by_contradiction,
  push_neg at h,
  push_neg at a_lt_x,
  have ax':a =x,
  apply le_antisymm,
  exact h,
  exact a_lt_x,
  exact absurd ax' ax,
  split,
  
  apply greater_elements_not_in_left_subtree x a tl tr o2 a_gt_x,
  apply h_tr o_tr,
  unfold ordered_member at mem,
  simp [a_lt_x, a_gt_x] at mem,
  rw ← ordered_member_eq_member_in_searchtree tr o_tr at mem,
  exact mem,
end

lemma deleting_different_element (a b: A) (t: binaryTree A) (hab: a ≠ b) (mem: member a t): member a (delete b t) :=
begin
  induction t with tl x tr h_tl h_tr,
  unfold delete,
  exact mem,

  unfold delete,
  by_cases bx: b=x,
  simp [bx],
  unfold member at mem,
  cases mem,
  exfalso,
  rw ← bx at mem,
  exact absurd mem hab,
  rw in_union_iff_in_either,
  exact mem,

  simp[bx],
  unfold member at mem,
  by_cases b_lt_x: b < x,
  simp [b_lt_x],
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

  simp [b_lt_x],
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

lemma deletion_semantics (a b: A) (t: binaryTree A) (o: ordered t): member a (delete b t) ↔ member a t ∧ a ≠ b :=
begin
  split,
  intro h,
  split,
  apply elements_after_delete_were_there_before b a t o,
  exact h,
  by_contradiction h2,
  apply deleted_element_gone b a t o,
  apply elements_after_delete_were_there_before a b t o,
  rw h2 at h,
  rw h2,
  exact h,
  rw h2 at h,
  exact h,

  intro h,
  cases h,
  apply deleting_different_element a b t h_right h_left,
end

def difference': binaryTree A -> binaryTree A -> binaryTree A
| t (binaryTree.empty) := t
| t (binaryTree.node tl x tr) := difference' (difference' (delete x t) tl) tr

lemma difference'_preserves_order (X Y: binaryTree A) (ox: ordered X): ordered (difference' X Y) :=
begin
  induction Y with tl y tr h_tl h_tr generalizing X,
  unfold difference',
  exact ox,

  unfold difference',
  apply h_tr,
  apply h_tl,
  apply delete_preserves_order,
  exact ox,
end

lemma difference'_semantics (a: A) (X Y: binaryTree A) (ox: ordered X): member a (difference' X Y) ↔ member a X ∧ ¬ member a Y :=
begin
  induction Y with tl y tr h_tl h_tr generalizing X,
  unfold difference',
  unfold member,
  cc,

  unfold difference',
  rw h_tr,
  rw h_tl,
  unfold member,
  push_neg,
  rw deletion_semantics a y X ox,
  tauto,

  apply delete_preserves_order,
  exact ox,

  apply difference'_preserves_order,
  apply delete_preserves_order,
  exact ox,
end

lemma difference_and_difference'_are_set_equal (X Y: binaryTree A) (ox: ordered X): set_equality A (difference X Y) (difference' X Y) :=
begin
  rw tree_extensionality (difference X Y) (difference' X Y) (difference_preserves_ordered X Y ox) (difference'_preserves_order X Y ox),
  intro a,
  rw in_difference_if_only_in_first,
  rw difference'_semantics,
  exact ox,
end

def intersection' (X Y: binaryTree A): binaryTree A := difference' (union X Y) (union (difference' X Y) (difference' Y X))

lemma intersection'_semantics (a:A) (X Y: binaryTree A) (ox: ordered X) (oy: ordered Y): member a (intersection' X Y) ↔ member a X ∧ member a Y :=
begin
  unfold intersection',
  rw difference'_semantics,
  rw in_union_iff_in_either,
  rw in_union_iff_in_either,
  rw difference'_semantics,
  rw difference'_semantics,

  push_neg,
  by_cases ax: member a X,
  simp [ax],
  simp [ax],
  exact oy,
  exact ox,
  apply union_preserves_order X Y ox ,
end

lemma intersection'_preserves_order (X Y: binaryTree A) (ox: ordered X) : ordered (intersection' X Y) :=
begin
  unfold intersection',
  apply difference'_preserves_order _ _ (union_preserves_order X Y ox), 
end

lemma intersection_and_intersection'_are_set_equal (X Y: binaryTree A) (ox: ordered X) (oy: ordered Y): set_equality A (intersection X Y) (intersection' X Y) :=
begin
  rw tree_extensionality (intersection X Y) (intersection' X Y) (intersection_preserves_order X Y oy) (intersection'_preserves_order X Y ox),
  intro a,
  rw in_intersection_iff_in_both,
  rw intersection'_semantics a X Y ox oy,
end

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

lemma set_equal_trees_have_same_size (X Y: binaryTree A) (hxy: set_equality A X Y): size X = size Y :=
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

lemma disjoint_union_process_1 (X tl tr: binaryTree A) (y:A) (disj: disjoint_tree X (binaryTree.node tl y tr)) (o: ordered (binaryTree.node tl y tr)) (ox: ordered X): disjoint_tree (unbalanced_insert y X) tl :=
begin
  have o2: ordered (binaryTree.node tl y tr),
  exact o,
  unfold ordered at o,
  rcases o with ⟨o_tl, o_tr,fk_tl, fk_tr⟩,
  unfold disjoint_tree,
  rw tree_extensionality (intersection (unbalanced_insert y X) tl) (binaryTree.empty) (intersection_preserves_order (unbalanced_insert y X) tl o_tl),
  simp_rw [in_intersection_iff_in_both, member],
  intro a,
  rw insert_semantics,
  by_cases h: member a tl,
  

  have y_gt_a: y > a,
  apply fk_tl,
  apply h,
  have ay: ¬ a =y,
  unfold forall_keys at fk_tl,
  apply ne_of_lt,
  apply y_gt_a,


  have aX: ¬ member a X,
  unfold disjoint_tree at disj,
  rw tree_extensionality _ binaryTree.empty (intersection_preserves_order X (binaryTree.node tl y tr) o2) at disj,
  simp [member, in_intersection_iff_in_both] at disj,
  by_contradiction aX,
  have hax: member a X → ¬(a = y ∨ member a tl ∨ member a tr),
  apply disj,
  apply hax,
  apply aX,
  right,
  left,
  apply h,

  unfold ordered,

  simp[aX, ay],

  simp [h],

  unfold ordered,
end

lemma disjoint_union_process_2 (X tl tr: binaryTree A) (y:A) (disj: disjoint_tree X (binaryTree.node tl y tr)) (o: ordered (binaryTree.node tl y tr)): disjoint_tree (union (unbalanced_insert y X) tl) tr :=
begin
  have o2: ordered (binaryTree.node tl y tr),
  exact o,
  rcases o with ⟨o_tl, o_tr,fk_tl, fk_tr⟩,
  unfold disjoint_tree,
  rw tree_extensionality _ _ (intersection_preserves_order _ _ o_tr),
  intro a,
  rw in_intersection_iff_in_both,
  rw in_union_iff_in_either,
  rw insert_semantics,
  unfold member,
  by_cases a_tr: member a tr,

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
  rw tree_extensionality _ _ (intersection_preserves_order _ _ o2) at disj,
  simp [member, in_intersection_iff_in_both] at disj,
  by_contradiction,
  have aY: ¬(a = y ∨ member a tl ∨ member a tr),
  apply disj,
  apply h,
  push_neg at aY,
  rcases aY with ⟨a1, a2, a3⟩,
  exact absurd a_tr a3,

  unfold ordered,

  simp [ay, aX, a_tl],
  simp [a_tr],

  unfold ordered,
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
  rw tree_extensionality _ _ (intersection_preserves_order _ _ oy) at disj,
  simp [member] at disj,
  simp_rw in_intersection_iff_in_both at disj,
  apply disj,
  unfold ordered,
  unfold member at y_disj,
  simp at y_disj,
  exact y_disj,




  have yX_tl_disj: disjoint_tree (unbalanced_insert y X) tl,
  apply disjoint_union_process_1 X tl tr y disj oy ox,

  have yXtl_tr_disj: disjoint_tree (union (unbalanced_insert y X) tl) tr,
  apply disjoint_union_process_2 X tl tr y disj oy ,
  
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
  apply intersection_and_difference_are_seteq_set _ _ ox oy,
  
  rw h,
  rw disjoint_size _ _ (intersection_and_difference_are_disjoint X Y ox oy) (difference_preserves_ordered X Y ox) (intersection_preserves_order X Y oy),
  rw nat.add_comm,
  rw nat.add_comm (size (difference X Y)) _,
  rw nat.add_assoc,

  have sxy: (size (difference X Y) + size Y) = size (union X Y),
  rw ← disjoint_size _ _ (difference_and_set_are_disjoint Y X oy ox) (difference_preserves_ordered X Y ox) oy,
  rw set_equal_trees_have_same_size (union X Y) (union Y X) (union_comm X Y ox oy),
  apply set_equal_trees_have_same_size _ _ (difference_and_set_are_union Y X oy ox),

  rw sxy,
end
end size
end binaryTree
section ordered_trees
namespace ordered_tree
  variables {A: Type} [linear_order A]
  structure ordered_tree (A: Type) [linear_order A] := (base: binaryTree.binaryTree A) (o: binaryTree.ordered base)

  def member (a:A) (t: ordered_tree A): Prop := binaryTree.member a t.base

  def emptyTree: ordered_tree A := {base:= binaryTree.binaryTree.empty, o:= binaryTree.emptyTree_ordered}

  def singleton (a:A): ordered_tree A := {base:= binaryTree.singleton a, o:= binaryTree.singleton_ordered a}

  def flatten (X: ordered_tree A) : list A := binaryTree.flatten X.base

  lemma member_in_tree_iff_in_flat (a:A) (X: ordered_tree A): member a X ↔ a ∈ flatten X :=
  begin
    unfold member,
    unfold flatten,
    rw binaryTree.member_in_tree_iff_in_flat,
  end

  def set_equality (A: Type) [linear_order A] (X Y: ordered_tree A): Prop := binaryTree.set_equality A X.base Y.base

  lemma set_equality_refl: reflexive (set_equality A) :=
  begin
    unfold reflexive,
    intro x,
    unfold set_equality,
    unfold binaryTree.set_equality,
  end

  lemma set_equality_symm: symmetric (set_equality A) :=
  begin
    unfold symmetric,
    unfold set_equality,
    unfold binaryTree.set_equality,
    intros x y hxy,
    rw hxy,
  end

  lemma set_equality_trans: transitive (set_equality A) :=
  begin
    unfold transitive,
    unfold set_equality,
    unfold binaryTree.set_equality,
    intros x y z hxy hyz,
    rw hxy,
    rw hyz,
  end

  theorem set_equality_equiv: equivalence (set_equality A) :=
  begin
    unfold equivalence,
    split,
    exact set_equality_refl,
    split,
    exact set_equality_symm,
    exact set_equality_trans,
  end

  theorem tree_extensionality (X Y: ordered_tree A): set_equality A X Y ↔ ∀ (a:A), member a X ↔ member a Y :=
  begin
    unfold member,
    unfold set_equality,
    exact binaryTree.tree_extensionality X.base Y.base X.o Y.o,
  end

  lemma set_equality_is_eq_set_equality_base (X Y: ordered_tree A): set_equality A X Y ↔ binaryTree.set_equality A X.base Y.base :=
  begin
    unfold set_equality,
  end

  lemma member_sound (a: A) (t1 t2: ordered_tree A) (s: set_equality A t1 t2): member a t1 = member a t2 :=
  begin
    unfold member,
    rw set_equality_is_eq_set_equality_base at s,
    apply binaryTree.member_sound a t1.base t2.base t1.o t2.o s,
  end

  lemma flatten_sound (t1 t2: ordered_tree A) (s: set_equality A t1 t2): flatten t1 = flatten t2 :=
  begin
    unfold set_equality at s,
    unfold binaryTree.set_equality at s,
    unfold flatten,
    exact s,
  end

  def insert (a:A) (t: ordered_tree A): ordered_tree A := {base:= binaryTree.unbalanced_insert a t.base,o:= binaryTree.insert_preserves_order a t.base t.o }

  lemma insert_sound (a: A) (t1 t2: ordered_tree A) (s:set_equality A t1 t2): set_equality A (insert a t1) (insert a t2) :=
  begin
    rw tree_extensionality,
    unfold member,
    unfold insert,
    simp,
    intro a',
    rw binaryTree.insert_semantics,
    rw binaryTree.insert_semantics,
    rw tree_extensionality at s,
    unfold member at s,
    rw s,
  end

  lemma insert_sound' (a: A) (t1 t2: ordered_tree A) (s:set_equality A t1 t2): quot.mk (set_equality A) (insert a t1) =  quot.mk (set_equality A) (insert a t2) :=
  begin
    apply quot.sound,
    apply insert_sound,
    apply s,
  end

  def delete (a:A) (t: ordered_tree A): ordered_tree A := {base:= binaryTree.delete a t.base, o:= binaryTree.delete_preserves_order a t.base t.o}

  lemma delete_sound (a: A) (t1 t2: ordered_tree A) (s:set_equality A t1 t2): set_equality A (delete a t1) (delete a t2) :=
  begin
    rw tree_extensionality,
    unfold member,
    unfold delete,
    simp,
    intro a',
    rw binaryTree.deletion_semantics _ _ _ t1.o,
    rw binaryTree.deletion_semantics _ _ _ t2.o,
    rw tree_extensionality at s,
    unfold member at s,
    rw s,
  end

  def union (X Y: ordered_tree A): ordered_tree A :={base:= binaryTree.union X.base Y.base, o:= binaryTree.union_preserves_order X.base Y.base X.o}

  lemma in_union_iff_in_either {X Y: ordered_tree A} {a:A}: member a (union X Y) ↔ member a X ∨ member a Y :=
  begin
    unfold member,
    apply binaryTree.in_union_iff_in_either,
  end

  lemma union_sound (X1 X2 Y1 Y2: ordered_tree A) (sx: set_equality A X1 X2) (sy: set_equality A Y1 Y2): set_equality A (union X1 Y1) (union X2 Y2) :=
  begin
    rw tree_extensionality,
    unfold member,
    unfold union,
    simp,
    rw tree_extensionality at sx,
    unfold member at sx,
    rw tree_extensionality at sy,
    unfold member at sy,
    intro a',
    rw binaryTree.in_union_iff_in_either X1.base Y1.base a',
    rw binaryTree.in_union_iff_in_either X2.base Y2.base a',
    rw sx,
    rw sy,
  end

  lemma union_sound_first (X1 X2 Y: ordered_tree A) (sx: set_equality A X1 X2): quot.mk (set_equality A) (union X1 Y) = quot.mk (set_equality A) (union X2 Y) :=
  begin
    apply quot.sound,
    apply union_sound,
    exact sx,
    apply set_equality_refl,
  end

  lemma union_sound_second (X Y1 Y2: ordered_tree A) (sy: set_equality A Y1 Y2): quot.mk (set_equality A) (union X Y1) = quot.mk (set_equality A) (union X Y2) :=
  begin
    apply quot.sound,
    apply union_sound,
    apply set_equality_refl,
    exact sy,
  end

  def intersection (X Y: ordered_tree A): ordered_tree A := {base:= binaryTree.intersection X.base Y.base, o:= binaryTree.intersection_preserves_order X.base Y.base Y.o}

  lemma in_intersection_iff_in_both {X Y: ordered_tree A} {a:A}: member a (intersection X Y) ↔ member a X ∧  member a Y :=
  begin
    unfold member,
    apply binaryTree.in_intersection_iff_in_both,
  end

  lemma intersection_sound (X1 X2 Y1 Y2: ordered_tree A) (sx: set_equality A X1 X2) (sy: set_equality A Y1 Y2): set_equality A (intersection X1 Y1) (intersection X2 Y2) :=
  begin
    rw tree_extensionality,
    unfold member,
    unfold intersection,
    simp,
    rw tree_extensionality at sx,
    unfold member at sx,
    rw tree_extensionality at sy,
    unfold member at sy,
    intro a',
    rw binaryTree.in_intersection_iff_in_both,
    rw binaryTree.in_intersection_iff_in_both,
    rw sx,
    rw sy,
  end

  lemma intersection_sound_first (X1 X2 Y: ordered_tree A) (sx: set_equality A X1 X2): quot.mk (set_equality A) (intersection X1 Y) = quot.mk (set_equality A) (intersection X2 Y) :=
  begin
    apply quot.sound,
    apply intersection_sound,
    apply sx,
    apply set_equality_refl,
  end

  lemma intersection_sound_second (X Y1 Y2: ordered_tree A) (sy: set_equality A Y1 Y2): quot.mk (set_equality A) (intersection X Y1) = quot.mk (set_equality A) (intersection X Y2) :=
  begin
    apply quot.sound,
    apply intersection_sound,
    apply set_equality_refl,
    apply sy,
  end

  def difference (X Y: ordered_tree A): ordered_tree A := {base:= binaryTree.difference X.base Y.base, o:= binaryTree.difference_preserves_ordered X.base Y.base X.o}

  lemma in_difference_if_only_in_first (X Y: ordered_tree A) (a:A): member a (difference X Y) ↔ member a X ∧ ¬ member a Y :=
  begin
    unfold member,
    unfold difference,
    simp,
    rw binaryTree.in_difference_if_only_in_first,
  end

  lemma difference_sound (X1 X2 Y1 Y2: ordered_tree A) (sx: set_equality A X1 X2) (sy: set_equality A Y1 Y2): set_equality A (difference X1 Y1) (difference X2 Y2) :=
  begin
    rw tree_extensionality,
    intro a,
    rw in_difference_if_only_in_first,
    rw in_difference_if_only_in_first,
    have mem_x: member a X1 = member a X2,
    apply member_sound,
    apply sx,
    rw mem_x,
    have mem_y: member a Y1 = member a Y2,
    apply member_sound,
    apply sy,
    rw mem_y,
  end

  lemma difference_sound_first (X1 X2 Y: ordered_tree A) (sx: set_equality A X1 X2): quot.mk (set_equality A) (difference X1 Y) = quot.mk (set_equality A) (difference X2 Y) :=
  begin
    apply quot.sound,
    apply difference_sound,
    apply sx,
    apply set_equality_refl,
  end

  lemma difference_sound_second (X Y1 Y2: ordered_tree A) (sy: set_equality A Y1 Y2): quot.mk (set_equality A) (difference X Y1) = quot.mk (set_equality A) (difference X Y2) :=
  begin
    apply quot.sound,
    apply difference_sound,
    apply set_equality_refl,
    apply sy,
  end


  def disjoint (X Y: ordered_tree A): Prop := binaryTree.disjoint_tree X.base Y.base

  lemma disjoint_semantics (X Y: ordered_tree A): disjoint X Y ↔ set_equality A (intersection X Y) emptyTree :=
  begin
    unfold disjoint,
    unfold binaryTree.disjoint_tree,
    unfold set_equality,
    unfold emptyTree,
    unfold intersection,
  end

  lemma disjoint_sound (X1 X2 Y1 Y2: ordered_tree A) (sx: set_equality A X1 X2) (sy: set_equality A Y1 Y2): disjoint X1 Y1 = disjoint X2 Y2 :=
  begin
    rw disjoint_semantics,
    rw disjoint_semantics,
    simp [tree_extensionality, in_intersection_iff_in_both],
    have mem_x: ∀ (a:A), member a X1 = member a X2,
    intro a,
    apply member_sound,
    exact sx,
    have mem_y:∀ (a:A), member a Y1 = member a Y2,
    intro a,
    apply member_sound,
    exact sy,
    simp [mem_x, mem_y],
  end 

  lemma disjoint_sound_first (X1 X2 Y: ordered_tree A) (sx: set_equality A X1 X2): disjoint X1 Y = disjoint X2 Y :=
  begin
    apply disjoint_sound,
    exact sx,
    apply set_equality_refl,
  end

  lemma disjoint_sound_second (X Y1 Y2: ordered_tree A) (sy: set_equality A Y1 Y2): disjoint X Y1 = disjoint X Y2 :=
  begin
    apply disjoint_sound,
    apply set_equality_refl,
    exact sy,
  end

  def size (X: ordered_tree A): ℕ := binaryTree.size (X.base)

  lemma size_sound (X Y: ordered_tree A) (s: set_equality A X Y): size X = size Y :=
  begin
    unfold size,
    unfold set_equality at s,
    unfold binaryTree.set_equality at s,
    rw binaryTree.size_eq_flatten_size,
    rw binaryTree.size_eq_flatten_size,
    rw s,
  end

  lemma size_empty_set_zero: size (emptyTree: ordered_tree A) = 0 :=
  begin
    unfold size,
    unfold emptyTree,
    unfold binaryTree.size,
  end
  
  lemma disjoint_size (X Y: ordered_tree A) (disj: disjoint X Y): size (union X Y) = size X + size Y :=
  begin
    unfold size,
    apply binaryTree.disjoint_size,
    unfold disjoint at disj,
    apply disj,
    apply X.o,
    apply Y.o,
  end

  lemma inclusion_exclusion (X Y: ordered_tree A): size (union X Y) + size (intersection X Y) = size X + size Y :=
  begin
    unfold size,
    apply binaryTree.inclusion_exclusion,
    exact X.o,
    exact Y.o,
  end
  
end ordered_tree
end ordered_trees


section treeSets
namespace treeSet
  def treeSet (A: Type) [linear_order A] := quot (ordered_tree.set_equality A)

  variables {A: Type} [linear_order A]

  def empty: treeSet A := quot.mk (ordered_tree.set_equality A) ordered_tree.emptyTree

  def singleton (a:A): treeSet A := quot.mk (ordered_tree.set_equality A) (ordered_tree.singleton a)

  def member (a:A) (X: treeSet A): Prop := quot.lift (ordered_tree.member a) (ordered_tree.member_sound a) X

  lemma member_lift (X: ordered_tree.ordered_tree A) (a: A): member a (quot.mk (ordered_tree.set_equality A) X) ↔ ordered_tree.member a X :=
  begin
    unfold member,
  end

  def disjoint (X Y: treeSet A): Prop := quot.lift₂ ordered_tree.disjoint ordered_tree.disjoint_sound_second ordered_tree.disjoint_sound_first X Y

  lemma disjoint_lift (X Y: ordered_tree.ordered_tree A): disjoint (quot.mk (ordered_tree.set_equality A) X) (quot.mk (ordered_tree.set_equality A) Y)  = ordered_tree.disjoint X Y :=
  begin
    unfold disjoint,
  end

  def insert (a:A) (X: treeSet A): treeSet A := quot.lift (λ (t: ordered_tree.ordered_tree A), quot.mk (ordered_tree.set_equality A) (ordered_tree.insert a t)) (ordered_tree.insert_sound' a) X

  lemma quot_sound_set_equality (X Y: ordered_tree.ordered_tree A): ordered_tree.set_equality A X Y ↔ quot.mk (ordered_tree.set_equality A) X = quot.mk (ordered_tree.set_equality A) Y :=
  begin
    split,
    intro h,
    apply quot.sound,
    apply h,
    intro h,
    rw quot.eq at h,
    induction h,
    apply h_ᾰ,
    apply ordered_tree.set_equality_refl,
    apply ordered_tree.set_equality_symm,
    apply h_ih,
    apply ordered_tree.set_equality_trans,
    apply h_ih_ᾰ,
    apply h_ih_ᾰ_1,
  end

  lemma extensionality (X Y: treeSet A): X = Y ↔ ∀ (a:A), member a X ↔ member a Y:=
  begin
    split,
    intro h,
    rw h,
    simp,

    apply quot.induction_on₂ X Y,
    intros a b h,
    apply quot.sound,
    simp [member_lift] at h,
    rw ordered_tree.tree_extensionality,
    apply h,
  end

  def flatten (X: treeSet A): list A := quot.lift (ordered_tree.flatten) ordered_tree.flatten_sound X

  def size (X: treeSet A): ℕ := quot.lift (ordered_tree.size) ordered_tree.size_sound X

  lemma size_lift (X: ordered_tree.ordered_tree A): size (quot.mk (ordered_tree.set_equality A) X) = ordered_tree.size X :=
  begin
    unfold size,
  end

  def union (X Y: treeSet A): treeSet A := quot.lift₂ (λ (X Y: ordered_tree.ordered_tree A), quot.mk (ordered_tree.set_equality A) (ordered_tree.union X Y)) ordered_tree.union_sound_second ordered_tree.union_sound_first X Y

  lemma union_lift (X Y: ordered_tree.ordered_tree A): union (quot.mk (ordered_tree.set_equality A) X) (quot.mk (ordered_tree.set_equality A) Y)  = quot.mk (ordered_tree.set_equality A) (ordered_tree.union X Y) :=
  begin
    unfold union,
  end

  lemma in_union_iff_in_either (X Y: treeSet A) (a: A): member a (union X Y) ↔ member a X ∨ member a Y :=
  begin
    apply quot.induction_on₂ X Y,
    intros a b1,
    rw union_lift,
    rw member_lift,
    rw member_lift,
    rw member_lift,
    apply ordered_tree.in_union_iff_in_either,
  end

  lemma union_comm (X Y: treeSet A): union X Y = union Y X :=
  begin
    rw extensionality,
    intro a,
    rw in_union_iff_in_either,
    rw in_union_iff_in_either,
    tauto,
  end 

  lemma union_idem (X: treeSet A): union X X = X :=
  begin
    rw extensionality,
    intro a,
    rw in_union_iff_in_either,
    tauto,
  end
  
  def intersection(X Y: treeSet A): treeSet A := quot.lift₂ (λ (X Y: ordered_tree.ordered_tree A), quot.mk (ordered_tree.set_equality A) (ordered_tree.intersection X Y)) ordered_tree.intersection_sound_second ordered_tree.intersection_sound_first X Y

  lemma intersection_lift (X Y: ordered_tree.ordered_tree A): intersection (quot.mk (ordered_tree.set_equality A) X) (quot.mk (ordered_tree.set_equality A) Y)  = quot.mk (ordered_tree.set_equality A) (ordered_tree.intersection X Y) :=
  begin
    unfold intersection,
  end

  lemma in_intersection_iff_in_both (X Y: treeSet A) (a: A): member a (intersection X Y) ↔ member a X ∧  member a Y :=
  begin
    apply quot.induction_on₂ X Y,
    intros a b,
    rw intersection_lift,
    repeat {rw member_lift},
    apply ordered_tree.in_intersection_iff_in_both,
  end

  lemma disjoint_semantics (X Y: treeSet A): disjoint X Y ↔ intersection X Y = empty :=
  begin
    apply quot.induction_on₂ X Y,
    intros a b,
    rw disjoint_lift,
    rw intersection_lift,
    unfold empty,
    split,
    intro h,
    apply quot.sound,
    rw ←  ordered_tree.disjoint_semantics,
    apply h,

    intro h,
    rw ordered_tree.disjoint_semantics,
    rw ← quot_sound_set_equality at h,
    apply h,
  end

  def treeSet_induction_union (f: treeSet A -> Prop) (empty: f empty) (sing: ∀ (a:A), f (singleton a)) (step: ∀(X Y: treeSet A), f X ∧ f Y → f (union X Y)) (X: treeSet A): f X :=
  begin
    apply quot.induction_on X,
    intro t,
    induction t,
    induction t_base with tl x tr ih_tl ih_tr,
    unfold treeSet.empty at empty,
    unfold ordered_tree.emptyTree at empty,
    apply empty,

    unfold binaryTree.ordered at t_o,
    rcases t_o with ⟨o_tl, o_tr, fk_tr, fk_tr⟩,
    have h: quot.mk (ordered_tree.set_equality A) {base := tl.node x tr, o := t_o} = union (singleton x) (union (quot.mk (ordered_tree.set_equality A) {base:= tl, o:=o_tl}) (quot.mk (ordered_tree.set_equality A) {base:= tr, o:=o_tr})),
    rw extensionality,
    intro a,
    rw member_lift,
    rw in_union_iff_in_either,
    rw in_union_iff_in_either,
    rw member_lift,
    rw member_lift,
    unfold singleton,
    rw member_lift,
    unfold ordered_tree.member,
    unfold ordered_tree.singleton,
    simp,
    unfold binaryTree.singleton,
    unfold binaryTree.member,
    cc,

    rw h,
    apply step,
    split,
    apply sing,
    apply step,
    split,
    apply ih_tl,
    apply ih_tr,
  end


  def difference (X Y: treeSet A): treeSet A := quot.lift₂ (λ (X Y: ordered_tree.ordered_tree A), quot.mk (ordered_tree.set_equality A) (ordered_tree.difference X Y)) ordered_tree.difference_sound_second ordered_tree.difference_sound_first X Y

  lemma difference_lift (X Y: ordered_tree.ordered_tree A): difference (quot.mk (ordered_tree.set_equality A) X) (quot.mk (ordered_tree.set_equality A) Y)  = quot.mk (ordered_tree.set_equality A) (ordered_tree.difference X Y) :=
  begin
    unfold difference,
  end

  lemma in_difference_if_only_in_first (X Y: treeSet A) (a: A): member a (difference X Y) ↔ member a X ∧ ¬   member a Y :=
  begin
    apply quot.induction_on₂ X Y,
    intros a b,
    rw difference_lift,
    repeat {rw member_lift},
    apply ordered_tree.in_difference_if_only_in_first,
  end

  lemma empty_set_has_size_zero: size (empty: treeSet A) = 0 :=
  begin
    unfold size,
    unfold empty,
    apply ordered_tree.size_empty_set_zero,
  end

  lemma disjoint_size (X Y: treeSet A) (disj: disjoint X Y): size (union X Y) = size X + size Y :=
  begin
    revert disj,
    apply quot.induction_on₂ X Y,
    intros a b,
    rw union_lift,
    repeat {rw size_lift},
    rw disjoint_lift,
    apply ordered_tree.disjoint_size,
  end

  lemma inclusion_exclusion {X Y: treeSet A}: size (union X Y) + size (intersection X Y) = size X + size Y :=
  begin
    apply quot.induction_on₂ X Y,
    intros a b,
    rw union_lift,
    rw intersection_lift,
    repeat {rw size_lift},
    apply ordered_tree.inclusion_exclusion,
  end

end treeSet
end treeSets