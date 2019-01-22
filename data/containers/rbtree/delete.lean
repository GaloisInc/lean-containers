import .basic

namespace data.containers
namespace rbtree
namespace delete

lemma cancel_plus (k x y:ℕ) :
  x + k = y + k →
  x = y :=
begin
  induction k; simp
end.


open color
open rbtree

universe u

inductive delete_result (E:Type u)
-- The deleted node and a tree result with black-height equal to the original tree.
| tree_result : E -> rbtree E -> delete_result

-- The deleted node and a black-colored tree result with black-height one less than
-- the original tree.  The resulting tree is always colored black.
| extra_black_result : E -> rbtree E -> delete_result

-- The element to delete wasn't in the tree at all.  Tree is unchanged.
| unchanged : delete_result
.

namespace delete_result
open delete_result

variable {E:Type u}.
variable [has_preordering E].

@[simp] def has_black_height : delete_result E → ℕ → Prop
| (tree_result _ t) := λ n, t.black_height = n
| (extra_black_result _ t) := λ n, t.black_height + 1 = n
| (unchanged _) := λ_, true
.

@[simp] def is_black : delete_result E → Prop
| (tree_result _ t) := t.tree_color = black
| (extra_black_result _ _) := true
| (unchanged _) := true
.

@[simp] def well_formed : delete_result E → Prop
| (extra_black_result _ t) := t.well_formed ∧ t.tree_color = black
| (tree_result _ t) := t.well_formed
| (unchanged _) := true
.

@[simp] def is_ordered : delete_result E → Prop
| (extra_black_result _ t) := t.is_ordered
| (tree_result _ t)        := t.is_ordered
| (unchanged _)            := true
.

@[simp] def all_lt : delete_result E → E → Prop
| (tree_result _ t)        x := t.all_lt x
| (extra_black_result _ t) x := t.all_lt x
| (unchanged _ )           x := true
.

@[simp] def all_gt : delete_result E → E → Prop
| (tree_result _ t)        x := t.all_gt x
| (extra_black_result _ t) x := t.all_gt x
| (unchanged _ )           x := true
.


@[simp] def mergeL : color -> delete_result E -> E -> rbtree E -> delete_result E
| _ (unchanged _) _ _
        := unchanged E

 -- NB, we assume subtrees are properly colored...
| cl (tree_result q l) x r
        := tree_result q (bin cl l x r)

| _     (extra_black_result q l) x empty
        := unchanged E -- impossible!

| red   (extra_black_result q l) x (bin _ a y b) -- must be black
        := match a with
           | bin red c z d
               := tree_result q (bin red (bin black l x c) z (bin black d y b))
           | _ := tree_result q (bin black (bin red l x a) y b)
           end

| black (extra_black_result q l) x (bin black a y b)
        := match a with
           | bin red c z d
               := tree_result q (bin black (bin black l x c) z (bin black d y b))
           | _ := extra_black_result q (bin black (bin red l x a) y b)
           end

| black (extra_black_result q l) x (bin red a y b)
        := match a with
           | bin black c z d :=
              match c with
              | bin red f w g :=
                  tree_result q (bin black (bin red (bin black l x f) w (bin black g z d)) y b)
              | _ :=
                  tree_result q (bin black (bin black (bin red l x c) z d) y b)
              end
           | _ := unchanged E -- impossible!
           end
.

-- NB! the arguments are in a strange order.  This makes the equation compiler
--  produce code that is easier to reason about
@[simp] def mergeR : color -> delete_result E -> rbtree E -> E -> delete_result E
| _ (unchanged _) _ _
        := unchanged E

 -- NB, we assume subtrees are properly colored...
| cl (tree_result q r) l x
        := tree_result q (bin cl l x r)

| _ (extra_black_result q r) empty x
        := unchanged E -- impossible!

| red (extra_black_result q r) (bin _ a y b) x -- tree must be black
        := match b with
           | bin red c z d
               := tree_result q (bin red (bin black a y c) z (bin black d x r))
           | _ := tree_result q (bin black a y (bin red b x r))
           end

| black (extra_black_result q r) (bin black a y b) x
        := match b with
           | bin red c z d
               := tree_result q (bin black (bin black a y c) z (bin black d x r))
           | _ := extra_black_result q (bin black a y (bin red b x r))
           end

| black (extra_black_result q r) (bin red a y b) x
        := match b with
           | bin black c z d :=
              match d with
              | bin red f w g :=
                     tree_result q (bin black a y (bin red (bin black c z f) w (bin black g x r)))
              | _ := tree_result q (bin black a y (bin black c z (bin red d x r)))
              end
           | _ := unchanged E -- impossible!
           end
.


attribute [simp] rbtree.black_height rbtree.well_formed rbtree.tree_color rbtree.is_ordered
  rbtree.all_lt rbtree.all_gt.

lemma mergeL_is_ordered (co:color) (l:delete_result E) (x:E) (r:rbtree E) :
  l.all_lt x →
  r.all_gt x →
  l.is_ordered →
  r.is_ordered →
  (mergeL co l x r).is_ordered :=
begin
  cases l with q t q t,
  case unchanged { cases r; cases co; simp },
  case tree_result { cases r; cases co; simp; cc },
  case extra_black_result {
    cases r,
    case empty { cases co; simp },
    case bin : co' a y b {
      cases co,
      case black {
        cases co',
        case black { cases a with co_a; simp, cc, cases co_a; simp; cc },
        case red {
          cases a with co_a c z d; simp, cases co_a; simp, cases c; simp, cc, cases c_a; simp; try {cc},
          intros, repeat{ split }; try {cc},
          apply (has_preordering.lt_of_lt_of_lt _ z _); assumption
        }
      },
      case red { cases a with co_a; simp, cc, cases co_a; simp; cc }
    }
  }
end.

lemma mergeL_preserves_lt (co:color) (l:delete_result E) (x:E) (r:rbtree E) (q:E) :
  l.all_lt q →
  has_preordering.cmp x q = ordering.lt →
  r.all_lt q →
  r.is_ordered →
  (mergeL co l x r).all_lt q :=
begin
  cases l,
  case unchanged{ cases r; cases co; simp },
  case tree_result : w t { cases r; cases co; simp; cc },
  case extra_black_result : w t {
    cases r,
    case empty { cases co; simp },
    case bin : co' a y b {
      cases co,
      case black {
        cases co'; cases a with co_a c z d; simp; try{cc}; cases co_a; simp; try{cc},
        { cases c with co_c, {simp, cc}, cases co_c; simp; cc },
        { intros; repeat{split}; try{cc}, apply (has_preordering.lt_of_lt_of_lt _ y _); assumption }
      },
      case red {
        cases co'; cases a with co_a c z d; simp; try{cc},
        cases co_a; simp; try{cc},
        { intros; repeat{split}; try{cc}, apply (has_preordering.lt_of_lt_of_lt _ y _); assumption },
        { cases co_a; simp; intros; repeat{split}; try{cc},
           apply (has_preordering.lt_of_lt_of_lt _ y _); assumption },
      }
    }
  },
end.

lemma mergeL_preserves_gt (co:color) (l:delete_result E) (x:E) (r:rbtree E) (q:E) :
  l.all_gt q →
  has_preordering.cmp q x = ordering.lt →
  r.all_gt q →
  (mergeL co l x r).all_gt q :=
begin
  cases l,
  case unchanged{ cases r; cases co; simp },
  case tree_result : w t { cases r; cases co; simp; cc },
  case extra_black_result : w t {
    cases r,
    case empty { cases co; simp },
    case bin : co' a y b {
      cases co,
      case black {
        cases co'; cases a with co_a c z d; simp; try{cc}; cases co_a; simp; try{cc},
        { cases c with co_c, {simp, cc}, cases co_c; simp; cc }
      },
      case red { cases co'; cases a with co_a c z d; simp; try{cc}; cases co_a; simp; try{cc} }
    }
  }
end.


lemma mergeR_preserves_lt (co:color) (l:rbtree E) (x:E) (r:delete_result E) (q:E) :
  l.all_lt q →
  has_preordering.cmp x q = ordering.lt →
  r.all_lt q →
  (mergeR co r l x).all_lt q :=
begin
  cases r,
  case unchanged { cases l; cases co; simp },
  case tree_result : w t { cases l; cases co; simp; cc },
  case extra_black_result : w t {
    cases l,
    case empty { cases co; simp },
    case bin : co' a y b {
      cases co,
      case black {
        simp, cases co'; cases b with co'' c z d ; simp; try {cc},
        { cases co'', { simp }, cases d with co_d ; simp, cc, cases co_d; simp; cc },
        { cases co'', { simp, cc }, cases d with co_d; {simp, cc} }
      },
      case red { simp, cases co'; cases b with co'' c z d; simp; try{cc},
        { cases co'', { simp, cc }, cases d; simp; cc },
        { cases co'', { simp, cc }, cases d; simp; cc }
      }
    }
  }
end.

lemma mergeR_preserves_gt (co:color) (l:rbtree E) (x:E) (r:delete_result E) (q:E) :
  l.is_ordered →
  l.all_gt q →
  has_preordering.cmp q x = ordering.lt →
  r.all_gt q →
  (mergeR co r l x).all_gt q :=
begin
  cases r,
  case unchanged { cases l; cases co; simp },
  case tree_result : w t { cases l; cases co; simp; cc },
  case extra_black_result : w t {
    cases l,
    case empty { cases co; simp },
    case bin : co' a y b {
      cases co,
      case black {
        simp, cases co'; cases b with co'' c z d ; simp; try {cc},
        { cases co'', { simp }, cases d with co_d ; simp, cc, cases co_d; simp; cc },
        { cases co'', { simp, intros; repeat {split}; try{cc},
            apply (has_preordering.lt_of_lt_of_lt _ y _); assumption },
            cases d with co_d; {simp, cc}
        }
      },
      case red { simp, cases co'; cases b with co'' c z d; simp; try{cc},
        { cases co'', { simp, intros; repeat{split}; try{cc},
            apply (has_preordering.lt_of_lt_of_lt _ y _); assumption },
          cases d; simp; cc
        },
        { cases co'', { simp, intros; repeat{split}; try{cc},
            apply (has_preordering.lt_of_lt_of_lt _ y _); assumption },
          cases d; simp; cc
        }
      }
    }
  },
end.


lemma mergeR_is_ordered (co:color) (l:rbtree E) (x:E) (r:delete_result E) :
  l.all_lt x →
  r.all_gt x →
  l.is_ordered →
  r.is_ordered →
  (mergeR co r l x).is_ordered :=
begin
  cases r with q t q t,
  case unchanged { cases l; cases co; simp },
  case tree_result { cases l; cases co; simp; cc },
  case extra_black_result {
    cases l,
    case empty { cases co; simp },
    case bin : co' a y b {
      cases co,
      case black {
        cases co',
        case black { cases b with co_b; simp, cc, cases co_b; simp; cc },
        case red {
          cases b with co_b c z d; simp, cases co_b; simp, cases d; simp, cc,
            cases d_a; simp; try { cc },
            intros; repeat { split }; try { cc },
            apply (has_preordering.lt_of_lt_of_lt _ z _); assumption
        }
      },
      case red { cases b with co_b; simp, cc, cases co_b; simp; cc }
    }
  },
end.


lemma mergeL_black_bh (l:delete_result E) (x:E) (r:rbtree E) :
  l.has_black_height (r.black_height) →
  (mergeL black l x r).has_black_height (r.black_height + 1) :=
begin
  cases l,
  case unchanged { simp },
  case tree_result : q t {
    cases t,
    case empty { simp, intro H, rw <- H },
    case bin { simp, intro H, rw <- H, simp }
  },
  case extra_black_result : q t {
    cases r,
    case empty { simp },
    case bin : cl a y b {
      cases cl,
      case red {
        cases a; simp,
        case bin : cl c z d {
          cases cl; simp, cases c with cl'; simp,
          { intro H, rewrite H },
          { cases cl'; simp, intro H, rewrite H }
        },
      },
      case black {
        cases a with cl; simp,
        { intro H, change (black_height t + 1 + 1 = 2), rewrite H },
        { cases cl; simp, intro H, change (t.black_height + 1 + 1 = black_height a_a + 3), rewrite H }
      }
    }
  },
end.

lemma mergeL_red_bh (l:delete_result E) (x:E) (r:rbtree E) :
  l.has_black_height (r.black_height) →
  (mergeL red l x r).has_black_height (r.black_height) :=
begin
  cases l,
  case unchanged { simp },
  case tree_result : q t {
    cases t,
    case empty { simp },
    case bin : c a y b { cases c; simp }
  },
  case extra_black_result : q t {
    cases t,
    case empty {
      simp, cases r,
      case empty { simp },
      case bin : c' c z d {
        simp, cases c,
        case empty { simp },
        case bin : c'' _ _ _ { cases c''; simp }
      }
    },
    case bin : c a y b {
      cases r,
      case empty { simp },
      case bin : c' c z d { cases c with cl; simp, cases cl; simp }
    }
  },
end.

lemma mergeR_black_bh (l:rbtree E) (x:E) (r:delete_result E) :
  r.has_black_height (l.black_height) →
  (mergeR black r l x).has_black_height (l.black_height + 1) :=
begin
  cases r,
  case unchanged { simp },
  case tree_result : q t { cases t; simp },
  case extra_black_result : q t {
    simp, intro Ht,
    cases l,
    case empty { simp },
    case bin : co a y b {
      cases co,
      case red {
        simp, cases b,
        case empty { simp },
        case bin : co' c z d {
          cases co'; simp,
          cases d,
          case empty { simp },
          case bin : co'' f w g { cases co''; simp }
        }
      },
      case black {
        simp, cases b,
        case empty{ simp },
        case bin : co' c z d { cases co'; simp }
      }
    }
  },
end.

lemma mergeR_red_bh (l:rbtree E) (x:E) (r:delete_result E) :
  l.tree_color = black →
  r.has_black_height (l.black_height) →
  (mergeR red r l x).has_black_height (l.black_height) :=
begin
  cases r,
  case unchanged { simp },
  case tree_result { simp },
  case extra_black_result : q t {
    cases l,
    case empty { simp },
    case bin : co a y b {
      simp, cases co; simp; cases b,
        case empty { simp },
        case bin : co' c z d { cases co'; simp }
    }
  }
end.


lemma mergeR_red_wf (l:rbtree E) (x:E) (r:delete_result E) :
  l.well_formed →
  r.well_formed →
  l.tree_color = black →
  r.is_black →
  r.has_black_height (l.black_height) →
  (mergeR red r l x).well_formed :=
begin
  cases r,
  case unchanged{ simp },
  case tree_result : q t { simp, cc },
  case extra_black_result : q t {
    cases l,
    case empty { simp },
    case bin : cl a y b {
      cases cl,
      case black {
        cases b,
        case empty { simp, cc },
        case bin : cl' c z d { cases cl'; simp; cc }
      },
      case red { simp }
    }
  }
end.

lemma mergeR_black_wf (l:rbtree E) (x:E) (r:delete_result E) :
  l.well_formed →
  r.well_formed →
  r.has_black_height (l.black_height) →
  (mergeR black r l x).well_formed :=
begin
  cases r,
  case unchanged{ simp },
  case tree_result { simp, cc },
  case extra_black_result : q t {
    cases l,
    case empty { simp },
    case bin : cl a y b {
      cases cl,
      case black {
        simp, cases b,
        case empty { simp, cc },
        case bin : cl' c z d {
          cases cl',
          case black { simp, cc },
          case red { simp, cc }
        }
      },
      case red {
        simp, cases b,
        case empty { simp },
        case bin : cl' c z d {
          cases cl',
          case red { simp },
          case black {
            simp,
            cases d,
            case empty { simp, intros,
              have Ht : t.black_height = 0, { apply (cancel_plus 1), simp,
              rewrite a_8, rewrite a_5, rewrite a_4 }, cc
            },
            case bin : cl'' f w g {
              cases cl'',
              case black { simp, intros, repeat {split}; try {cc},
                 rewrite <- a_7, rewrite a_8 at a_11, apply (cancel_plus 1), cc },
              case red { simp, intros, repeat {split}; try {cc},
                 rewrite <- a_8, rewrite <- a_9, rewrite a_10 at a_13,
                 apply (cancel_plus 1), cc
              }
            }
          }
        }
      }
    }
  }
end.

lemma mergeL_black_wf (l:delete_result E) (x:E) (r:rbtree E) :
  l.well_formed →
  r.well_formed →
  l.has_black_height (r.black_height) →
  (mergeL black l x r).well_formed :=
begin
  cases l,
  case unchanged { intros, trivial },
  case tree_result : q t { simp, cc },
  case extra_black_result : q t {
    cases r,
    case empty { simp },
    case bin : cl a y b {
      cases cl,
      case black {
        simp,
        cases a,
        case empty { simp, intros, cc },
        case bin : cl' c z d {
          cases cl',
          case red { simp, intros, cc },
          case black { simp, intros, cc }
        }
      },
      case red {
        simp,
        cases a,
        case empty { simp },
        case bin : cl' c z d {
          simp, intros, subst cl', simp,
          cases c,
          case empty {
            simp at *,
            have Ht : t.black_height = 0, { apply (cancel_plus 1), assumption }, cc
          },
          case bin : cl'' f w g {
            cases cl'',
            case black {
              simp at *,
              have Ht : t.black_height = f.black_height + 1, { apply (cancel_plus 1), assumption }, cc
            },
            case red { simp at *, cc }
          }
        }
      },
    }
  },
end.


lemma mergeL_red_wf (l:delete_result E) (x:E) (r:rbtree E) :
  l.well_formed →
  r.well_formed →
  l.has_black_height (r.black_height) →
  l.is_black →
  r.tree_color = black →
  (mergeL red l x r).well_formed :=
begin
  cases l,
  case unchanged { intros; trivial },
  case tree_result : q t {
    cases t,
    case empty { simp, cc },
    case bin : c a y b { cases c; simp; cc }
  },
  case extra_black_result : q t {
    cases r; simp,
    case bin : c a y b {
      cases c,
      case red {
        unfold rbtree.tree_color rbtree.well_formed, intros,
        cases a,
        case bin : c' c z d { cases c'; simp; cc },
        case empty { simp; cc }
      },
      case black {
        cases a,
        case empty {
          simp, intros,
          have Ht : t.black_height = 0, { apply (cancel_plus 1), assumption }, cc
        },
        case bin : c' c z d {
          cases c'; simp; intros,
          { cc },
          { have Htc : t.black_height = c.black_height + 1, { apply (cancel_plus 1), assumption }, cc }
        }
      }
    }
  },
end.


lemma mergeL_is_black (l:delete_result E) (x:E) (r:rbtree E) :
  (mergeL black l x r).is_black :=
begin
  cases l,
  case tree_result : q t { simp },
  case extra_black_result : q t {
    cases r,
    case empty{ simp },
    case bin : cl a y b {
      cases cl,
      case black {
        cases a,
        case empty { simp },
        case bin : cl' _ _ _ { cases cl'; simp }
      },
      case red {
        cases a,
        case empty { simp },
        case bin : cl' f w g { cases cl'; simp, cases f, simp, cases f_a; simp }
      }
    }
  },
  case unchanged : { simp }
end.


lemma mergeR_is_black (l:rbtree E) (x:E) (r:delete_result E) :
  (mergeR black r l x).is_black :=
begin
  cases r,
  case unchanged { simp },
  case tree_result : q t { simp },
  case extra_black_result : q t {
    cases l,
    case empty{ simp },
    case bin : cl a y b {
      cases cl,
      case black {
        cases b,
        case empty { simp },
        case bin : co_b c z d { cases co_b; simp }
      },
      case red {
        cases b,
        case empty { simp },
        case bin : co_b c z d { cases co_b; simp,
          cases d,
          case empty{ simp },
          case bin : d_a { cases d_a; simp }
        }
      }
    }
  }
end.


@[simp] def delete_min : rbtree E -> delete_result E
| empty                                 := unchanged E
| (bin red   empty x r)                 := tree_result x r
| (bin black empty x (bin red a y b))   := tree_result x (bin black a y b)
| (bin black empty x r)                 := extra_black_result x r
| (bin c l x r)                         := mergeL c (delete_min l) x r
.

lemma delete_min_bh (x:rbtree E) :
  x.well_formed →
  (delete_min x).has_black_height (x.black_height) :=
begin
  induction x,
  case empty { intros, simp },
  case bin : cl l x r IHl IHr {
    cases l,
    case empty {
      cases cl; simp; try { cc },
      cases r,
      case empty { simp },
      case bin : cl a y b {
        cases cl; simp,
        { intros, rewrite <- a_6 },
        { intros, change (black_height a + 1 + 1 = 1), rewrite <- a_4 }
      },
    },
    case bin : cl' a y b {
      cases cl,
      case red {
        simp, intros, subst cl', simp at *,
        rw a_5,
        apply mergeL_red_bh,
        rw <- a_5,
        apply IHl; cc
      },
      case black {
        cases cl',
        case red {
          simp, intros, rw a_7,
          apply mergeL_black_bh,
          simp at *,
          rw <- a_7,
          apply IHl; assumption
        },
        case black {
          simp at *, intros, change (black_height a + 2) with (black_height a + 1 + 1),
          rewrite a_5,
          apply mergeL_black_bh,
          rewrite <- a_5, apply IHl; assumption
        }
      }
    }
  }
end.

lemma delete_min_is_black (l:rbtree E) (x:E) (r:rbtree E) :
  l.black_height = r.black_height →
  (delete_min (bin black l x r)).is_black :=
begin
  induction l,
  case empty { simp,
    cases r,
    case bin : cl a y b { cases cl; simp },
    case empty { simp }
  },
  case bin : {
    simp, intros,
    apply mergeL_is_black
  }
end.

lemma delete_min_well_formed (x:rbtree E) :
  x.well_formed → (delete_min x).well_formed :=
begin
  induction x,
  case empty { simp },
  case bin : cl l x r IHl IHr {
    cases l,
    case empty {
      cases cl,
      case red { simp, cc },
      case black {
        cases r,
        case empty { simp },
        case bin : cl' a y b {
          cases cl'; simp; cc
        }
      }
    },
    case bin : cl' a y b {
      cases cl; simp; intros,
      { apply mergeL_red_wf; try { cc },
        rw <- a_5, apply delete_min_bh, assumption,
        subst cl', apply delete_min_is_black,
        simp at *, cc
      },
      { apply mergeL_black_wf; try { cc },
        rw <- a_3, apply delete_min_bh, assumption
      }
    }
  }
end.

lemma delete_min_is_ordered (t:rbtree E) :
  t.is_ordered →
  ((delete_min t).is_ordered) ∧
  (∀ q, t.all_lt q → (delete_min t).all_lt q) ∧
  (∀ q, t.all_gt q → (delete_min t).all_gt q) :=
begin
  induction t,
  case empty { simp },
  case bin : co a x b IHl IHr {
    cases a,
    case empty {
      cases co; simp,
      { intros; repeat {split;intros}; try{cc}, apply (all_gt_congr b q x), assumption, rewrite a_2,
        (do t <- tactic.target, t' <- tactic.whnf t, tactic.change t'), trivial
      },
      { cases b,
        case empty{ simp, },
        case bin : co_b c z d { simp,
          cases co_b; simp; intros; repeat{split;intros}; try{cc},
          { apply (all_gt_congr c q x), assumption, rewrite a_6,
            (do t <- tactic.target, t' <- tactic.whnf t, tactic.change t'), trivial },
          { apply (has_preordering.lt_of_lt_of_lt _ x _); assumption },
          { apply (all_gt_congr c q x), assumption, rewrite a_6,
            (do t <- tactic.target, t' <- tactic.whnf t, tactic.change t'), trivial },
          { apply (has_preordering.lt_of_lt_of_lt _ x _); assumption },
        }
      }
    },
    case bin : co_a c z d IHa {
      cases co,
      case black { simp; intros, split,
        { apply mergeL_is_ordered; try {simp at *, cc},
          have Hczd : (bin co_a c z d).is_ordered, { simp, cc },
          destruct (IHa Hczd); simp; intros IH1 IH2 IH3, apply IH2; assumption },
        split,
        { intros; apply mergeL_preserves_lt; try{assumption},
          have Hczd : (bin co_a c z d).is_ordered, { simp, cc },
          destruct (IHa Hczd); simp; intros IH1 IH2 IH3, apply IH2,
          { apply (has_preordering.lt_of_lt_of_lt _ x _); assumption },
          { apply (all_lt_congr d x q), assumption,
            rewrite a_8,
            (do t <- tactic.target, t' <- tactic.whnf t, tactic.change t'), trivial }
        },
        { intros; apply mergeL_preserves_gt; try{assumption},
          have Hczd : (bin co_a c z d).is_ordered, { simp, cc },
          destruct (IHa Hczd); simp; intros IH1 IH2 IH3, apply IH3; try{assumption},
          apply (all_gt_congr b q x), assumption,
            rewrite a_10,
            (do t <- tactic.target, t' <- tactic.whnf t, tactic.change t'), trivial }
      },
      case red { sorry }
    }
  }
end.

@[simp] def merge (co:color) (x:E) (l:rbtree E) (r:rbtree E) : delete_result E :=
  match delete_min r with
  | unchanged _ :=
       match co with
       | red   := tree_result x l
       | black := extra_black_result x l
       end
  | tree_result q r'        := mergeR co (tree_result x r') l q
  | extra_black_result q r' := mergeR co (extra_black_result x r') l q
  end.

lemma merge_black_bh (x:E) (l:rbtree E) (r:rbtree E) :
  l.black_height = r.black_height →
  r.well_formed →
  (merge black x l r).has_black_height (l.black_height + 1) :=
begin
  unfold merge, intros Hlr Hr_wf,
  destruct (delete_min r),
  { intros q t Hr, rw Hr, simp },
  { intros q t Hr, rw Hr, simp, apply mergeR_black_bh, simp,
    have Hr_bh := (delete_min_bh r Hr_wf),
    rewrite Hr at Hr_bh, simp at *, cc
  },
  { intro Hr, rw Hr, simp }
end.

lemma merge_red_bh (x:E) (l:rbtree E) (r:rbtree E) :
  l.black_height = r.black_height →
  l.tree_color = black →
  r.well_formed →
  (merge red x l r).has_black_height (l.black_height) :=
begin
  unfold merge, intros Hl_blk Hlr Hr_wf,
  destruct (delete_min r),
  { intros q t Hr, rw Hr, simp,
  },
  { intros q t Hr, rw Hr, simp, apply mergeR_red_bh, try {assumption},
    have Hr_bh := (delete_min_bh r Hr_wf),
    rewrite Hr at Hr_bh, rewrite Hl_blk, simp at *, assumption
  },
  { intro Hr, rw Hr, simp }
end.


@[simp] def delete_core (p:E -> ordering) : rbtree E -> delete_result E
| empty := delete_result.unchanged E
| (bin c l x r) :=
    match p x with
    | ordering.lt := mergeL c (delete_core l) x r
    | ordering.eq := merge c x l r
    | ordering.gt := mergeR c (delete_core r) l x
    end
.

lemma delete_core_bh (p : E -> ordering) (t:rbtree E) :
  t.well_formed →
  (delete_core p t).has_black_height (t.black_height) :=
begin
  induction t,
  case empty { simp },
  case bin : co l x r IHl IHr {
    unfold delete_core, cases (p x),
    case ordering.lt {
      simp, cases co,
      case red {
        simp, intros Hl_b Hr_b Hl_wf Hr_wf Hrl,
        rewrite Hrl, apply mergeL_red_bh, rewrite <- Hrl, cc
      },
      case black {
        simp, intros Hl_wf Hr_wf Hrl,
        rewrite Hrl, apply mergeL_black_bh, rewrite <- Hrl, cc
      }
    },
    case ordering.gt {
      simp, cases co,
      case red { simp, intros, apply mergeR_red_bh, cc, rewrite a_4; cc },
      case black { simp, intros, apply mergeR_black_bh, rewrite a_2; cc }
    },
    case ordering.eq {
      cases co,
      case red { simp; intros, apply merge_red_bh; assumption },
      case black{ simp; intros, apply merge_black_bh; assumption }
    }
  }
end.

def delete (p:E -> ordering) (t:rbtree E) : option (E × rbtree E) :=
  match delete_core p t with
  | unchanged _             := none
  | tree_result q t'        := some (q,t')
  | extra_black_result q t' := some (q,t')
  end.

end delete_result.
end delete.
end rbtree.
end data.containers.
