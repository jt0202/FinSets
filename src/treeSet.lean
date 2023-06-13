import init.algebra.order tactic.rcases data.list.sort
open list


inductive binaryTree (A : Type)
| empty: binaryTree 
| node : binaryTree  -> A -> binaryTree -> binaryTree

section operations
variables {A: Type} [linear_order A]
def member: A -> binaryTree A -> Prop
| x binaryTree.empty := false 
| x (binaryTree.node tl a tr) := (x =a ) ∨ member x tl ∨  member x tr


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
| binaryTree.empty := tt
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

end operations