import .basic

namespace data.containers
namespace rbtree

open color

/-- An insert_result is a generalization of the tree to allow
a node with 2-keys and 3-children each of which should have the
same height.

This is used
Specifically, it is either a tree that respects the red-black rules,
or a the concatenation of three trees with the same height.
-/
inductive insert_result (E : Type _)
| tree : Π (t : rbtree E), insert_result
-- When inserting into a binary tree that respects the ordering
-- and red-black color rules, by construction we know that the trees
-- are in ascending order, either the first or third tree are colored
-- black, and the center node is colored black.
| triple : rbtree E → E → rbtree E →  E → rbtree E → insert_result

namespace insert_result
section
parameters {E:Type _}

/--
Convert an insert result to a tree.

N.B. This may increase the black-height, so should only be called in contexts
where that matters (i.e. at the roto.)
-/
def as_tree : insert_result E → rbtree E
| (tree u) := u
| (triple l x c y r) := bin black (bin red l x c) y r

def to_list : insert_result E → list E
| (tree t) := t.to_list
| (triple l x c y r) := l.to_list ++ [x] ++ c.to_list ++ [y] ++ r.to_list

parameters [has_preordering E]

/-- Check whether a insert_result respects the ordering relation. -/
def is_ordered : insert_result E → Prop
| (tree t) := t.is_ordered
| (triple l x c y r) :=
   l.is_ordered
   ∧ all_lt l x
   ∧ all_gt c x
   ∧ c.is_ordered ∧ has_preordering.cmp x y = ordering.lt
   ∧ all_lt c y
   ∧ all_gt r y
   ∧ r.is_ordered

instance (r : insert_result E) : decidable (is_ordered r) :=
begin
  cases r; simp [is_ordered]; apply_instance,
end

/- Return true if keys on right spine of rbtree are less then k. -/
def all_lt : insert_result E → E → Prop
| (tree t) a := t.all_lt a
| (triple l x c y r) a :=
  has_preordering.cmp y a = ordering.lt ∧ r.all_lt a

/- Return true if keys on right spine of rbtree are less then k. -/
def all_gt : insert_result E → E → Prop
| (tree t) a := t.all_gt a
| (triple l x c y r) a :=
  has_preordering.cmp a x = ordering.lt ∧ l.all_gt a

end
end insert_result

section insert_def
parameters {E:Type _}

open insert_result

def balanceL : color → insert_result E → E → rbtree E → insert_result E
-- In this case, the caller should be able to guarantee that co is black, so the
-- black depth of the tree should not change.
| co (triple ll lx lc ly lr) x r :=
  tree (bin red (bin black ll lx lc) ly (bin black lr x r))
| co (tree l) x r :=
  match (co, l) with
  | (red, bin red ll lx lr) := triple ll lx lr x r
  | _ := tree (bin co l x r)
  end

def balanceR : color → rbtree E → E → insert_result E → insert_result E
-- In this case co is guaranteed to be black, so the
-- black depth of the tree should not change.
| co l x (triple rl rx rc ry rr) :=
  tree (bin red (bin black l x rl) rx (bin black rc ry rr))
| co l x (tree r) :=
  match (co, r) with
  | (red, bin red rl rx rr) := triple l x rl rx rr
  | _ := tree (bin co l x r)
  end

parameters [has_preordering E]

def insert_core (y : E) : rbtree E → insert_result E
| empty := tree (bin red empty y empty)
| (bin c l x r) :=
  match has_preordering.cmp y x with
  | ordering.lt := balanceL c (insert_core l) x r
  | ordering.eq := tree (bin c l y r)
  | ordering.gt := balanceR c l x (insert_core r)
  end

def insert (y : E) (t : rbtree E) : rbtree E :=
  (insert_core y t).as_tree

end insert_def

-----------------------------------------------------------------------
-- to_list

section to_list_theorems
parameters {E:Type _}

theorem to_list_balanceL (c : color) (l : insert_result E) (x : E) (r : rbtree E)
: (balanceL c l x r).to_list  = l.to_list ++ [x] ++ r.to_list :=
begin
  cases l with t tl tx tc ty tr;
    try { cases t with lc ll lx lr; try { cases lc }; cases c, };
  simp [*, balanceL, insert_result.to_list, to_list],
end

theorem to_list_balanceR
(c : color) (l : rbtree E) (x : E) (r : insert_result E)
: (balanceR c l x r).to_list = l.to_list ++ [x] ++ r.to_list :=
begin
  cases r with t l x tc y r;
    try {
      cases t with rc rl rx rr; try { cases rc };
        cases c,
    };
  simp [*, balanceR, insert_result.to_list, to_list],
end

theorem to_list_as_tree (r : insert_result E)
: r.as_tree.to_list = r.to_list :=
begin
  cases r with t tl tx tc ty tr;
    try { cases tl with tlc tll tlx tlr;  try { cases tlc }, };
    simp [insert_result.as_tree, rbtree.tree_color, insert_result.to_list, to_list],
end

parameters [has_preordering E]

theorem to_list_insert_core (y : E) (t : rbtree E)
: is_ordered t
→ (insert_core y t).to_list
    = t.to_list.filter (key_is_lt y) ++ y :: t.to_list.filter (key_is_gt y) :=
begin
  induction t,
  case empty {
    intros,
    simp [insert_core, insert_result.to_list, to_list],
  },
  case bin : c l x r l_ind r_ind {
    simp [is_ordered, insert_core, to_list, list.filter, key_is_lt, key_is_gt],

    have g1 : (ordering.gt ≠ ordering.lt), exact dec_trivial,
    have g2 : ordering.lt ≤ ordering.eq, exact dec_trivial,
    have g3 : ordering.eq ≤ ordering.eq, exact dec_trivial,
    have g4 : ordering.eq ≠ ordering.lt, exact dec_trivial,

    have cmp_x_y_eq : has_preordering.cmp x y = (has_preordering.cmp y x).swap,
    { rw [has_preordering.swap_cmp], },

    intros iso_l iso_r all_gt_r_x all_lt_l_x,
    have all_lt_r_key := all_lt_congr l x y,
    have all_gt_r_key := all_gt_congr r y x,
    have l_lt := filter_lt_of_all_lt l y,
    have l_gt := filter_gt_of_all_lt l y,
    have r_lt := filter_lt_of_all_gt r y,
    have r_gt := filter_gt_of_all_gt r y,
    destruct (has_preordering.cmp y x); intro cmp_y_x;
      simp [cmp_y_x, ordering.swap] at cmp_x_y_eq,
    { simp [insert_core, *, to_list_balanceL, l_ind], },
    { simp [insert_core, *, insert_result.to_list, to_list ], },
    { simp [insert_core, *, to_list_balanceR, r_ind], },
  },
end

theorem to_list_insert (y : E) (t : rbtree E) : is_ordered t
 → to_list (insert y t)
    = t.to_list.filter (key_is_lt y) ++ y :: t.to_list.filter (key_is_gt y) :=
begin
  intros,
  simp [insert, to_list_as_tree, to_list_insert_core, *],
end

theorem insert_eq (y : E)
: ∀{t u : rbtree E},
   is_ordered t
   → is_ordered u
   → t.to_list = u.to_list
   → to_list (insert y t) = to_list (insert y t) :=
begin
  intros x y x_order y_order x_eq_y,
  simp [to_list_insert, *],
end

end to_list_theorems

-----------------------------------------------------------------------
-- is_ordered

section is_ordered_theorems
parameters {E:Type _}

parameters [has_preordering E]
local attribute [simp] balanceL balanceR insert_result.is_ordered is_ordered
  insert_result.all_lt all_lt insert_result.all_gt all_gt
  insert_core

section balanceL
parameters (c : color) (l : insert_result E) (y : E) (r : rbtree E)

theorem all_lt_balanceL (a : E)
  (all_lt_l : l.all_lt a)
  (y_lt_bnd : has_preordering.cmp y a = ordering.lt)
  (all_lt_r : all_lt r a)
: (balanceL c l y r).all_lt a :=
begin
  cases l with t tl tx tc ty tr;
    try { cases t with lc ll lx lr; try { cases lc }; cases c, };
  try { simp at all_lt_l, simp [*], },
end

theorem all_gt_balanceL (a : E)
  (iso : l.is_ordered)
  (a_lt_y : has_preordering.cmp a y = ordering.lt)
  (all_gt_l : l.all_gt a)
: (balanceL c l y r).all_gt a :=
begin
  cases l with t tl tx tc ty tr;
    try { cases t with lc ll lx lr; try { cases lc }; cases c, };
  try { simp at all_gt_l, simp [*], },
  simp at iso,
  apply has_preordering.lt_of_lt_of_lt a tx ty; simp [*],
end

theorem is_ordered_balanceL
  (l_iso : l.is_ordered)
  (all_lt_l_y : l.all_lt y)
  (all_gt_r_y : all_gt r y)
  (iso_r : is_ordered r)
: (balanceL c l y r).is_ordered :=
begin
  cases l with t tl tx tc ty tr;
    try { cases t with lc ll lx lr; try { cases lc }; cases c, };
  try {   simp at l_iso all_lt_l_y, simp [*],},
end
end balanceL

section balanceR
parameters (c : color) (l : rbtree E) (y : E) (r : insert_result E)

theorem all_lt_balanceR (a : E)
  (iso : r.is_ordered)
  (y_lt_a : has_preordering.cmp y a = ordering.lt)
  (all_lt_r_a : r.all_lt a)
: (balanceR c l y r).all_lt a :=
begin
  cases r with t tl tx tc ty tr;
    try { cases t with rc rl rx rr; try { cases rc }; cases c, };
  try { simp at all_lt_r_a, simp [*], },
  simp at iso,
  apply has_preordering.lt_of_lt_of_lt tx ty a; simp [*],
end

theorem all_gt_balanceR (a : E)
  (a_lt_y : has_preordering.cmp a y = ordering.lt)
  (all_gt_l : all_gt l a)
  (all_gt_r : r.all_gt a)
: (balanceR c l y r).all_gt a :=
begin
  cases r with t tl tx tc ty tr;
    try { cases t with rc rl rx rr; try { cases rc }; cases c, };
  try { simp at all_gt_r, simp[*], },
end

theorem is_ordered_balanceR
  (l_iso : is_ordered l)
  (all_lt_l_y : all_lt l y)
  (all_gt_r_y : r.all_gt y)
  (r_iso : r.is_ordered)
: (balanceR c l y r).is_ordered :=
begin
  cases r with t tl tx tc ty tr;
    try { cases t with rc rl rx rr; try { cases rc }; cases c, };
  try { simp at all_gt_r_y r_iso, simp[*], },
end
end balanceR

theorem is_ordered_as_tree {r : insert_result E}
  (iso : r.is_ordered)
: r.as_tree.is_ordered :=
begin
  cases r with t tl tx tc ty tr;
    try { cases tl with lc ll lx lr; try { cases lc}, };
  simp at iso; simp [insert_result.as_tree, *],
end

theorem insert_core_preserves (y : E) {t : rbtree E}
  (iso : is_ordered t)
: (insert_core y t).is_ordered
∧ (∀ (a : E), has_preordering.cmp y a = ordering.lt
            → t.all_lt a
            → (insert_core y t).all_lt a)
∧ (∀ (a:E), has_preordering.cmp a y = ordering.lt
               → t.all_gt a
               → (insert_core y t).all_gt a) :=
begin
  induction t,
  case empty {
    intros,
    simp,
  },
  case bin : c l x r l_ind r_ind {
    simp at iso,
    simp only [iso, true_implies_iff] at l_ind r_ind,
    have l_all_lt := l_ind.right.left,
    have r_all_gt := r_ind.right.right,
    destruct (has_preordering.cmp y x);
      intro cmp_y_s;
      simp only [cmp_y_s, insert_core, all_lt],
    { apply and.intro,
      { apply is_ordered_balanceL,
        all_goals { simp [*], },
      },
      apply and.intro,
      { intros a y_lt_a pr,
        apply all_lt_balanceL,
        apply l_all_lt,
        all_goals { try { simp [*],} },
        apply all_lt_congr l x a; simp[*],
      },
      { intros a a_lt_y pr,
        simp at pr,
        apply all_gt_balanceL,
        all_goals { simp [*], },
      }
    },
    { apply and.intro,
      { simp [*],
        apply and.intro,
        { have h0 := has_preordering.eq_symm y x,
          apply all_lt_congr l x y; simp [*],
        },
        { apply all_gt_congr r y x; simp [*], },
      },
      apply and.intro,
      { intros a y_lt_a x_lt_a, simp [*], },
      { intros a a_lt_y gt_a, simp at gt_a, simp [*], },
    },
    { rw [has_preordering.gt_lt_symm] at cmp_y_s,
      apply and.intro,
      { apply is_ordered_balanceR; simp[*], },
      apply and.intro,
      { intros a y_lt_a x_lt_a,
        apply all_lt_balanceR; simp[*],
      },
      { intros a a_lt_y pr,
        simp at pr,
        apply all_gt_balanceR; try { simp[*] },
        apply r_all_gt; try { simp[*] },
        apply all_gt_congr r a x; try { simp[*] },
      },
    },
  },
end

theorem is_ordered_insert (y : E) (t : rbtree E)
: is_ordered t → is_ordered (insert y t) :=
begin
  intro iso,
  simp [insert],
  apply is_ordered_as_tree,
  have h := insert_core_preserves y iso,
  simp[h],
end
end is_ordered_theorems

-----------------------------------------------------------------------
-- to_list


namespace insert_result
section
parameters {E:Type _}

def black_height : insert_result E → ℕ
| (triple l _ _ _ _) := l.black_height
| (tree t) := t.black_height

def well_formed : insert_result E → Prop
| (triple l x c y r) :=
  l.well_formed
  ∧ c.well_formed
  ∧ r.well_formed
  ∧ l.black_height = c.black_height
  ∧ c.black_height = r.black_height
  ∧ c.tree_color = black
  ∧ l.tree_color = black
  ∧ r.tree_color = black
| (tree t) := t.well_formed

end
end insert_result

section is_well_formed_theorems
parameters {E:Type _}
local attribute [simp] balanceL balanceR insert_result.well_formed well_formed
  rbtree.tree_color insert_result.black_height black_height
  insert_result.as_tree nat.add_succ
  insert_core

theorem succ_eq_succ (m n :ℕ) : (nat.succ m = nat.succ n) ↔ (m = n) :=
  iff.intro nat.succ.inj (congr_arg nat.succ)

local attribute [simp] succ_eq_succ

theorem well_formed_balanceL_black (l : insert_result E) (x : E) (r : rbtree E)
(l_wf : l.well_formed)
(r_wf : r.well_formed)
(l_ht_eq_r_ht : r.black_height = l.black_height)
: (balanceL black l x r).well_formed  :=
begin
  cases l with t tl tx tc ty tr;
    try { cases t with lc ll lx lr; try { cases lc } };
    simp at l_wf l_ht_eq_r_ht;
    simp [*],
end

theorem well_formed_balanceL_red (l : insert_result E) (x : E) (r : rbtree E)
(l_wf : l.well_formed)
(r_wf : r.well_formed)
(l_ht_eq_r_ht : r.black_height = l.black_height)
(r_black : r.tree_color = black)
: (balanceL red l x r).well_formed  :=
begin
  cases l with t tl tx tc ty tr;
    try { cases t with lc ll lx lr; try { cases lc } };
    simp at l_wf;
    simp [*],
end

theorem well_formed_balanceR_black (l : rbtree E) (x : E) (r : insert_result E)
(l_wf : l.well_formed)
(r_wf : r.well_formed)
(l_ht_eq_r_ht : l.black_height = r.black_height)
: (balanceR black l x r).well_formed  :=
begin
  cases r with t tl tx tc ty tr;
    try { cases t with rc rl rx rr; try { cases rc } };
    simp at r_wf;
    simp [*],
end

theorem well_formed_balanceR_red (l : rbtree E) (x : E) (r : insert_result E)
(l_wf : l.well_formed)
(r_wf : r.well_formed)
(l_ht_eq_r_ht : l.black_height = r.black_height)
(l_black : l.tree_color = black)
: (balanceR red l x r).well_formed  :=
begin
  cases r with t tl tx tc ty tr;
    try { cases t with rc rl rx rr; try { cases rc } };
    simp at r_wf;
    try { simp [*], },
end


theorem black_height_balanceL_black (l : insert_result E) (x : E) (r : rbtree E)
: (balanceL black l x r).black_height = l.black_height + 1 :=
begin
  cases l with t tl tx tc ty tr;
    try { cases t with lc ll lx lr; try { cases lc } };
    simp [*],
end

theorem black_height_balanceL_red (l : rbtree E) (x : E) (r : rbtree E)
: (balanceL red (insert_result.tree l) x r).black_height = l.black_height :=
begin
  cases l with t tl tx tc ty tr;
    try { cases t with lc ll lx lr; try { cases lc } };
    simp [*],
end

theorem black_height_balanceR_black (l : rbtree E) (x : E) (r : insert_result E)
: (balanceR black l x r).black_height = l.black_height + 1 :=
begin
  cases r with t tl tx tc ty tr;
    try { cases t with rc rl rx rr; try { cases rc } };
    simp [*],
end

theorem black_height_balanceR_red (l : rbtree E) (x : E) (r : rbtree E)
: (balanceR red l x (insert_result.tree r)).black_height = l.black_height :=
begin
  cases r with t tl tx tc ty tr;
    try { cases t with rc rl rx rr; try { cases rc } };
    simp [*],
end

theorem well_formed_as_tree (r : insert_result E)
: r.well_formed → r.as_tree.well_formed :=
begin
  intro r_wf,
  cases r with t tl tx tc ty tr;
    try { cases tl with tlc tll tlx tlr; try { cases tlc }, };
    try { simp at r_wf, simp[r_wf], };
    cc
end

-- To simplify insert_core, we need a restricted definitions that work
-- when the root node of the tree is colored black.  This allows us
-- to make balanceL, balanceR, and insert_core return rbtrees rather
-- that insert_result.
section

def balanceL_black : insert_result E → E → rbtree E → rbtree E
| (insert_result.triple ll lx lc ly lr) x r :=
  bin red (bin black ll lx lc) ly (bin black lr x r)
| (insert_result.tree l) x r := bin black l x r

def balanceR_black : rbtree E → E → insert_result E → rbtree E
| l x (insert_result.triple rl rx rc ry rr) :=
 bin red (bin black l x rl) rx (bin black rc ry rr)
| l x (insert_result.tree r) := bin black l x r

parameters [has_preordering E]

def insert_core_black (y : E) : rbtree E → rbtree E
| empty := bin red empty y empty
| (bin c l x r) :=
  match has_preordering.cmp y x with
  | ordering.lt := balanceL_black (insert_core y l) x r
  | ordering.eq := bin c l y r
  | ordering.gt := balanceR_black l x (insert_core y r)
  end

theorem insert_core_black_eq (y : E) (t : rbtree E)
: t.tree_color = black → insert_core y t = insert_result.tree (insert_core_black y t) :=
begin
  intro isb,
  cases t with c l x r,
  { simp [insert_core_black], },
  { simp at isb,
    destruct (has_preordering.cmp y x); intro cmp_y_x;
      simp [*, insert_core_black],
    { cases (insert_core y l); simp [balanceL_black], },
    { cases (insert_core y r); simp [balanceR_black], },
  },
end
end

parameters [has_preordering E]

local attribute [simp]
  black_height_balanceL_black
  black_height_balanceL_red
  black_height_balanceR_black
  black_height_balanceR_red

theorem black_height_insert_core (y : E) (t : rbtree E)
: t.well_formed → (insert_core y t).black_height = t.black_height :=
begin
  induction t,
  case empty {
    intros,
    simp,
  },
  case bin : c l x r l_ind r_ind {
    cases c,
    case red {
      destruct (has_preordering.cmp y x); intro cmp_y_x; simp [cmp_y_x],
      { intros l_isb r_isb l_wf r_wf l_ht_eq,
        simp only [insert_core_black_eq y l l_isb, insert_result.black_height ] at l_ind,
        simp only [*, insert_core_black_eq y l l_isb, black_height_balanceL_red],
      },
      { intros l_isb r_isb l_wf r_wf l_ht_eq,
        simp only [*, insert_core_black_eq y r r_isb, black_height_balanceR_red],
      },
    },
    case black {
      destruct (has_preordering.cmp y x); intro cmp_y_x; simp [cmp_y_x],
      { intros l_wf r_wf l_ht_eq,
        simp only [*],
      },
    }
  },
end

local attribute [simp] black_height_insert_core

theorem well_formed_insert_core (y : E) (t : rbtree E)
: t.well_formed → (insert_core y t).well_formed :=
begin
  induction t,
  case empty {
    intros,
    simp,
  },
  case bin : c l x r l_ind r_ind {
    cases c,
    case red {
      destruct (has_preordering.cmp y x);
        intro cmp_y_x;
        simp [cmp_y_x];
        intros,
      { apply well_formed_balanceL_red; simp [*], },
      { simp[*], },
      { apply well_formed_balanceR_red; simp[*], },
    },
    case black {
      destruct (has_preordering.cmp y x);
        intro cmp_y_x;
        simp [cmp_y_x];
        intros,
      { apply well_formed_balanceL_black; simp [*], },
      { simp[*], },
      { apply well_formed_balanceR_black; simp[*], },
    }
  },
end

theorem well_formed_insert (y : E) (t : rbtree E) :
 t.well_formed → (insert y t).well_formed :=
begin
  intros,
  apply well_formed_as_tree,
  apply well_formed_insert_core,
  assumption,
end

end is_well_formed_theorems

end rbtree
end data.containers
