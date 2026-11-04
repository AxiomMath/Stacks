module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.CohomologyComparison
public import
 StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.CohomologicalDescentUnconditional

/-!
# Étale cohomology equals fppf cohomology of the inverse image

Let `B` be a big fppf site, `X` an object of it (a scheme), and
`a_X : Sh((Sch/X)_fppf) ⟶ Sh(X_étale)` the composite `π_X ∘ ε_X`. This file proves Stacks 0DDU:

1. `H^q(X_étale, F) = H^q_fppf(X, a_X^{-1}F)` for an abelian sheaf `F` on `X_étale`;
2. `H^q(X_étale, K) = H^q_fppf(X, a_X^{-1}K)` for `K` in `D⁺(X_étale)`;

and the example `H^q_étale(X, A) = H^q_fppf(X, A)` for an abelian group `A`.

The maps are the canonical ones of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.CohomologyComparison`:
`AlgebraicGeometry.fppfSmallEtaleHypercohomologyPullback`,
`AlgebraicGeometry.fppfSmallEtaleCohomologyPullback` (with `H^q = R^qΓ`, Stacks 015A) and
`AlgebraicGeometry.fppfSmallEtaleConstantCohomologyPullback`.

## Main results

* `AlgebraicGeometry.isIso_fppfSmallEtaleCohomologyPullbacks`: Stacks 0DDU, parts (1) and (2)
  and the example, as one statement.

## The proof

As in the source: Stacks 0DDT by Stacks 08J6. The map `RΓ(X_étale, K) ⟶ RΓ_fppf(X, a_X^{-1}K)`
is `RΓ(X_étale, -)` of the map `K ⟶ Ra_{X,*}a_X^{-1}K` of Stacks 0DDT followed by the inverse of
the factorization `RΓ_fppf(X, -) = RΓ(X_étale, -) ∘ Ra_{X,*}` (`a_{X,*}` preserves injective
objects, the input of Stacks 08J6). By Stacks 0DDT,
`AlgebraicGeometry.isIso_fppfSmallEtaleAdjunctionDerivedUnit_app`, the first map is invertible,
hence so is the composite (`Stacks.LerayPullbackComparison.isIso_lerayPullback_app`). Part (2)
is its degree `q` cohomology, part (1) is part (2) at `F[0]`, and the example is part (1) at a
constant sheaf, read through `a_X^{-1}A = A`.

The instance `AlgebraicGeometry.SmallEtale.isGrothendieckAbelian_abelianSheaf` is removed for
the declaration here: its universe is `max (u + 1) v` with `v` free, so instance search on the
small étale site stops on an unsolvable universe constraint. The removal is scoped to the single
declaration so that it cannot reach importers.

The derived categories are arbitrary models: the statements carry `HasDerivedCategory`
instances for the two sheaf categories and for abelian groups.

## References

* [Stacks Project, Tag 0DDU](https://stacks.math.columbia.edu/tag/0DDU)
* [Stacks Project, Tag 0DDT](https://stacks.math.columbia.edu/tag/0DDT)
* [Stacks Project, Tag 08J6](https://stacks.math.columbia.edu/tag/08J6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} (X : B.Schemes)
  [HasDerivedCategory
    (Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (B.topology.over X) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory AddCommGrpCat.{u + 1}]

attribute [-instance] AlgebraicGeometry.SmallEtale.isGrothendieckAbelian_abelianSheaf in
/-- **Stacks 0DDU.** Let `X` be a scheme and `a_X : Sh((Sch/X)_fppf) ⟶ Sh(X_étale)`. Then, for
every `q`:

1. `H^q(X_étale, F) = H^q_fppf(X, a_X^{-1}F)` for an abelian sheaf `F` on `X_étale`, with
   `H^q = R^qΓ` (`CategoryTheory.Functor.rightDerivedPlus`, Stacks 015A): the canonical map
   `AlgebraicGeometry.fppfSmallEtaleCohomologyPullback` is an isomorphism;
2. `H^q(X_étale, K) = H^q_fppf(X, a_X^{-1}K)` for `K` in `D⁺(X_étale)`: the canonical map
   `AlgebraicGeometry.fppfSmallEtaleHypercohomologyPullback` is an isomorphism;

and, the example, `H^q_étale(X, A) = H^q_fppf(X, A)` for an abelian group `A` and its constant
sheaves: the canonical map `AlgebraicGeometry.fppfSmallEtaleConstantCohomologyPullback` is an
isomorphism. -/
@[stacks 0DDU]
theorem isIso_fppfSmallEtaleCohomologyPullbacks :
    (∀ (q : ℤ)
      (F : Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1}),
        IsIso (fppfSmallEtaleCohomologyPullback B X q F)) ∧
    (∀ (q : ℤ) (K : DerivedCategory.Plus
      (Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1})),
        IsIso (fppfSmallEtaleHypercohomologyPullback B X q K)) ∧
    ∀ (q : ℤ) (A : AddCommGrpCat.{u + 1}),
      IsIso (fppfSmallEtaleConstantCohomologyPullback B X q A) := by
  -- Part (2): `RΓ` of the map of Stacks 0DDT, then the factorization of Stacks 08J6.
  have h₂ : ∀ (q : ℤ) (K : DerivedCategory.Plus
      (Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1})),
      IsIso (fppfSmallEtaleHypercohomologyPullback B X q K) := fun q K ↦ by
    have : IsIso ((Stacks.LerayPullbackComparison.derivedUnit
        (fppfSmallEtaleAbelianAdjunction B X)).app K) :=
      isIso_fppfSmallEtaleAdjunctionDerivedUnit_app B X K
    have : IsIso ((fppfSmallEtaleDerivedSectionsPullback B X).app K) :=
      Stacks.LerayPullbackComparison.isIso_lerayPullback_app _ _ _ _ K
    rw [fppfSmallEtaleHypercohomologyPullback]
    infer_instance
  -- Part (1): part (2) at `F[0]`, read through `a_X^{-1}(F[0]) = (a_X^{-1}F)[0]`.
  have h₁ : ∀ (q : ℤ)
      (F : Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1}),
      IsIso (fppfSmallEtaleCohomologyPullback B X q F) := fun q F ↦ by
    have := h₂ q ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
    rw [fppfSmallEtaleCohomologyPullback]
    exact IsIso.comp_isIso' this
      ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q).mapIso
        ((Sheaf.Γ (B.topology.over X) AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.mapIso
          ((fppfSmallEtaleAbelianPullback B X).mapDerivedCategoryPlusObjSingleIso F))).isIso_hom
  -- The example: part (1) at the constant sheaf `A`, read through `a_X^{-1}A = A`.
  refine ⟨h₁, h₂, fun q A ↦ ?_⟩
  have := h₁ q ((constantSheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2)
    AddCommGrpCat.{u + 1}).obj A)
  rw [fppfSmallEtaleConstantCohomologyPullback]
  infer_instance

end AlgebraicGeometry
