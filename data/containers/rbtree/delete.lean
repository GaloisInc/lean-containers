import .basic

namespace data.containers
namespace rbtree
namespace delete

open color
open rbtree

universe u

inductive delete_result (E:Type u)
-- The deleted node and a tree result with black-height equal to the original tree.
| tree_result : E -> rbtree E -> delete_result

-- The deleted node and a black-colored tree result with black-height one less than
-- the original tree.  The resulting tree is always colored black.
| double_black_result : E -> rbtree E -> delete_result

-- The deleted node, together with a triple of subtrees all of the same black height
-- | triple : E -> rbtree E -> E -> rbtree E -> E -> rbtree E -> delete_result

-- The element to delete wasn't in the tree at all.  Tree is unchanged.
| unchanged : delete_result
.

namespace delete_result
open delete_result

variable {E:Type u}
variable [has_preordering E]

@[simp] def has_black_height : delete_result E → ℕ → Prop
| (tree_result _ t) n := t.black_height = n
| (double_black_result _ t) n := t.black_height + 1 = n
-- | (triple _ t _ _ _ _) n := t.black_height = n
| (unchanged _) _ := true
.

@[simp] def is_black : delete_result E → Prop
| (tree_result _ t) := t.tree_color = black
| (double_black_result _ _) := true
| (unchanged _) := true
.

@[simp] def well_formed : delete_result E → Prop
| (tree_result _ t) := t.well_formed
| (double_black_result _ t) :=
   t.well_formed ∧
   t.tree_color = black
-- | (triple _ a x b y c) :=
--    a.well_formed ∧
--    b.well_formed ∧
--    c.well_formed ∧
--    a.black_height = b.black_height ∧
--    b.black_height = c.black_height ∧
--    a.tree_color = black ∧
--    b.tree_color = black ∧
--   c.tree_color = black
| (unchanged _) := true
.

@[simp] def mergeR : color -> rbtree E -> E -> delete_result E -> delete_result E :=
  _ .


@[simp] def mergeL : color -> delete_result E -> E -> rbtree E -> delete_result E
| _ (unchanged _) _ _                       := unchanged E

 -- NB, we assume subtrees are properly colored...
| cl (tree_result q l) x r                  := tree_result q (bin cl l x r)

| _     (double_black_result q l) x empty   := unchanged E -- impossible!

| red   (double_black_result q l) x (bin _ a y b) -- must be black
        := match a with
           | bin red c z d
               := tree_result q (bin red (bin black l x c) z (bin black d y b))
           | _ := tree_result q (bin black (bin red l x a) y b)
           end
| black (double_black_result q l) x (bin black a y b)
        := match a with
           | bin red c z d
               := tree_result q (bin black (bin black l x c) z (bin black d y b))
           | _ := double_black_result q (bin black (bin red l x a) y b)
           end
| black (double_black_result q l) x (bin red a y b)
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

attribute [simp] rbtree.black_height rbtree.well_formed rbtree.tree_color.

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
  case double_black_result : q t {
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
  case double_black_result : q t {
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


lemma mergeL_black_wf (l:delete_result E) (x:E) (r:rbtree E) :
  l.well_formed →
  r.well_formed →
  l.has_black_height (r.black_height) →
  (mergeL black l x r).well_formed :=
begin
  cases l,
  case unchanged { intros, trivial },
  case tree_result : q t { simp, cc },
  case double_black_result : q t {
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
            have Ht : t.black_height = 0, { sorry }, cc
          },
          case bin : cl'' f w g {
            cases cl'',
            case black {
              simp at *,
              have Ht : t.black_height = f.black_height + 1, { sorry }, cc
            },
            case red { simp at *, cc }
          }
        }
      },
    }
  },
  -- case triple : q a x b y z { simp; cc }
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
  case double_black_result : q t {
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
          have Ht : t.black_height = 0, { sorry }, cc
        },
        case bin : c' c z d {
          cases c'; simp; intros,
          { cc },
          { have Htc : t.black_height = c.black_height + 1, { sorry }, cc }
        }
      }
    }
  },
end.

@[simp] def delete_min : rbtree E -> delete_result E
| empty                                 := unchanged E
| (bin red   empty x r)                 := tree_result x r
| (bin black empty x empty)             := double_black_result x empty
| (bin black empty x (bin red a y b))   := tree_result x (bin black a y b)
| (bin black empty x (bin black a y b)) := double_black_result x (bin black a y b)
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

lemma mergeL_is_black (l:delete_result E) (x:E) (r:rbtree E) :
  (mergeL black l x r).is_black :=
begin
  cases l,
  case tree_result : q t { simp },
  case double_black_result : q t {
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

def merge (co:color) (x:E) (l:rbtree E) (r:rbtree E) : delete_result E :=
  match delete_min r with
  | unchanged _ :=
       match co with
       | red   := tree_result x l
       | black := double_black_result x l
       end
  | tree_result q r'         := mergeR co l q (tree_result x r')
  | double_black_result q r' := mergeR co l q (double_black_result x r')
  end.

def delete_core (p:E -> ordering) : rbtree E -> delete_result E
| empty := delete_result.unchanged E
| (bin c l x r) :=
    match p x with
    | ordering.lt := mergeL c (delete_core l) x r
    | ordering.eq := merge c x l r
    | ordering.gt := mergeR c l x (delete_core r)
    end
.

def delete (p:E -> ordering) (t:rbtree E) : option (E × rbtree E) :=
  match delete_core p t with
  | unchanged _              := none
  | tree_result q t'         := some (q,t')
  | double_black_result q t' := some (q,t')
  end.


end delete
end rbtree
end data.containers
