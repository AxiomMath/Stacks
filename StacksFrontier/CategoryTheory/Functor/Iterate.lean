module

public import Mathlib.CategoryTheory.Equivalence
public import StacksFrontier.AlgebraicTopology.StandardResolution.Godement

/-!
# Iterates of a natural transformation out of the identity

For an endofunctor `F : C ⥤ C` and `n : ℕ`, the `n`-fold composite `F^{∘ n} = F ∘ ⋯ ∘ F` is
`CategoryTheory.Functor.iterate`. For a natural transformation `μ : 𝟭 ⟶ F` this file defines its
`n`-fold iterate `𝟭 ⟶ F^{∘ n}`, whose component at `X` is `X ⟶ F X ⟶ ⋯ ⟶ F^{∘ n} X`.

## Main definitions

* `CategoryTheory.Functor.iterateNatTrans`: the `n`-fold iterate of `μ : 𝟭 ⟶ F`.

## Main results

* `CategoryTheory.Functor.isEquivalence_iterate`: the iterates of an autoequivalence are
  autoequivalences.
* `CategoryTheory.Functor.iterateNatTrans_app_zero`,
  `CategoryTheory.Functor.iterateNatTrans_app_succ`: the components of the iterate.
-/

@[expose] public section

namespace CategoryTheory.Functor

universe v u

variable {C : Type u} [Category.{v} C] (F : C ⥤ C)

/-- **The iterates of an autoequivalence are autoequivalences.** -/
instance isEquivalence_iterate [F.IsEquivalence] : ∀ n : ℕ, (F.iterate n).IsEquivalence
  | 0 => inferInstanceAs (𝟭 C).IsEquivalence
  | n + 1 =>
    have := isEquivalence_iterate n
    inferInstanceAs (F.iterate n ⋙ F).IsEquivalence

variable {F}

/-- The `n`-fold iterate `𝟭 ⟶ F^{∘ n}` of a natural transformation `μ : 𝟭 ⟶ F`: its component at
`X` is the composite `X ⟶ F X ⟶ ⋯ ⟶ F^{∘ n} X` of the components of `μ`. -/
def iterateNatTrans (μ : 𝟭 C ⟶ F) : ∀ n : ℕ, 𝟭 C ⟶ F.iterate n
  | 0 => 𝟙 _
  | n + 1 => iterateNatTrans μ n ≫ (F.iterate n).rightUnitor.inv ≫ whiskerLeft (F.iterate n) μ

/-- The component of the `0`-fold iterate is the identity. -/
@[simp]
theorem iterateNatTrans_app_zero (μ : 𝟭 C ⟶ F) (X : C) :
    (iterateNatTrans μ 0).app X = 𝟙 X := rfl

/-- The component of the `(n + 1)`-fold iterate at `X` is that of the `n`-fold iterate followed by
the component of `μ` at `F^{∘ n} X`. -/
@[simp]
theorem iterateNatTrans_app_succ (μ : 𝟭 C ⟶ F) (n : ℕ) (X : C) :
    (iterateNatTrans μ (n + 1)).app X =
      (iterateNatTrans μ n).app X ≫ μ.app ((F.iterate n).obj X) :=
  congrArg ((iterateNatTrans μ n).app X ≫ ·) (Category.id_comp (μ.app ((F.iterate n).obj X)))

end CategoryTheory.Functor
