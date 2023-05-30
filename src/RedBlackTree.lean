-- set_option trace.eqn_compiler.elim_match true

inductive Color
| red: Color 
| black: Color

inductive RedBlackTree (A : Type)
| empty: RedBlackTree 
| node : Color -> A -> RedBlackTree -> RedBlackTree -> RedBlackTree

def member {A: Type} [decidable_eq A] [preorder A] [∀ (a b: A), decidable( a < b)]: A -> RedBlackTree A -> Prop
| x RedBlackTree.empty := false 
| x (RedBlackTree.node _ a tl tr) := 
  if (x = a) 
    then true 
    else  member x tl ∨  member x tr

def unbalanced_insert {A: Type} [preorder A] [decidable_eq A] [∀ (a b: A), decidable( a < b)]: A -> RedBlackTree A -> RedBlackTree A
| x RedBlackTree.empty := (RedBlackTree.node Color.black x RedBlackTree.empty RedBlackTree.empty)
| x (RedBlackTree.node c a tl tr) := 
  if (x = a)
    then (RedBlackTree.node c a tl tr)
  else if x < a 
    then RedBlackTree.node c a (unbalanced_insert x tl) tr
  else
    RedBlackTree.node c a tl (unbalanced_insert x tr)

def size {A:Type} :RedBlackTree A ->  ℕ
| RedBlackTree.empty := 0
| (RedBlackTree.node _ a tl tr) := 1 + size tl + size tr

def forall_keys {A: Type} [decidable_eq A] [preorder A][∀ (a b: A), decidable( a < b)] (p: A -> A -> Prop) (a : A) (t: RedBlackTree A): Prop :=
  ∀ a', (member a' t) -> p a a'

def ordered {A: Type} [decidable_eq A] [preorder A] [∀ (a b: A), decidable( a < b)]: RedBlackTree A -> Prop
| RedBlackTree.empty := tt
| (RedBlackTree.node _ x tl tr) := ordered tl ∧ ordered tr ∧ (forall_keys (>) x tl) ∧ (forall_keys (<) x tr)

lemma lt_implies_neq {A:Type} [decidable_eq A] [preorder A] {a x: A}: (a < x) -> ¬ (a = x) :=
begin
  intro h,
  by_contradiction h1,
  rw h1 at h,
  apply lt_irrefl x,
  exact h,
end

lemma lt_all_eq_no_member {A:Type} [decidable_eq A] [preorder A] [∀ (a b: A), decidable( a < b)] (T: RedBlackTree A) (o: ordered(T)) (a: A) (p: ∀ (x:A), member x T -> x > a): ¬ (member a T) :=
begin
  induction T with c y tl tr h_tl h_tr,
  unfold member,
  simp,
  unfold member,
  simp,
  apply not_or_distrib,
end

lemma ordered_less_than_eq_in_left_tree {A:Type} [decidable_eq A] [preorder A] [∀ (a b: A), decidable( a < b)] {a: A} {tl tr: RedBlackTree A} {c:Color}(T: RedBlackTree A) (T_node: T = (RedBlackTree.node c a tl tr) )(o:ordered(T)) (x: A) (h: member x T) (lt: x < a) : member x tl  :=
begin
  cases T,
  exfalso,
  unfold member at h,
  apply h,

  have neq: ¬(x=a),
  apply lt_implies_neq,
  exact lt,
  rw T_node at h,
  rw T_node at o,
  dunfold member at h,
  simp [neq] at h,
end

theorem cant_unbalanced_insert_twice {A:Type} [preorder A] [decidable_eq A] [∀ (a b: A), decidable( a < b)] (a:A) (T: RedBlackTree A) (h: member a T) : T = unbalanced_insert a T :=
begin
  induction T with c x tl tr h_tl h_tr,
  exfalso,
  unfold member at h,
  apply h,
  by_cases h1: (a= x),
  rw h1,
  dunfold unbalanced_insert, -- unfold doesn't work here
  simp [h1],
  by_cases h2: (a < x),  
  dunfold unbalanced_insert,
  simp [h1, h2],
  apply h_tl,
  admit,
  dunfold unbalanced_insert,
  simp [h1, h2],
  apply h_tr,
  admit,
end


def union {A:Type} [preorder A] [decidable_eq A] [∀ (a b: A), decidable( a < b)]: RedBlackTree A -> RedBlackTree A -> RedBlackTree A
| B RedBlackTree.empty := B
| B (RedBlackTree.node c x tl tr) := union ( union (unbalanced_insert x B) tl) tr