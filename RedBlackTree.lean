-- set_option trace.eqn_compiler.elim_match true

inductive Color
| red: Color 
| black: Color

inductive RedBlackTree (A : Type)
| empty: RedBlackTree 
| node : Color -> A -> RedBlackTree -> RedBlackTree -> RedBlackTree

def member {A: Type} [decidable_eq A]: A -> RedBlackTree A -> bool
| x RedBlackTree.empty := false 
| x (RedBlackTree.node _ a tl tr) := 
  if (x = a) 
    then true 
    else member x tl ∨ member x tr

def insert {A: Type} [has_lt A] [decidable_eq A] [∀ (a b: A), decidable( a < b)]: A -> RedBlackTree A -> RedBlackTree A
| x RedBlackTree.empty := (RedBlackTree.node Color.black x RedBlackTree.empty RedBlackTree.empty)
| x (RedBlackTree.node c a tl tr) := 
  if (x = a)
    then (RedBlackTree.node c a tl tr)
  else if x < a 
    then RedBlackTree.node c a (insert x tl) tr
  else
    RedBlackTree.node c a tl (insert x tr)

def size {A:Type} :RedBlackTree A ->  ℕ
| RedBlackTree.empty := 0
| (RedBlackTree.node _ a tl tr) := 1 + size tl + size tr

theorem cant_insert_twice {A:Type} [has_lt A] [decidable_eq A] [∀ (a b: A), decidable( a < b)] (a:A) (T: RedBlackTree A) (h: member a T) : T = insert a T :=
begin
  induction T with c x tl tr h_tl h_tr,
  exfalso,
  unfold member at h,
  simp at h,
  apply h, 
end
