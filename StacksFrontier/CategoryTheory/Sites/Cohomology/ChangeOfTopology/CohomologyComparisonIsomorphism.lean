module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.HigherDirectImageVanishing
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.VanishingConditionInduction
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology is unchanged by the change of topology

Let `C` carry a finer coverage `τ` and a coarser coverage `τ'` as in the situation of Stacks
0EZ3, let `X` be an object of `C` and write `ε_X : C_τ/X ⟶ C_{τ'}/X` for the change-of-topology
morphism. For a sheaf `ℱ'` of the weak Serre class `𝒜'_X` on the coarser localized site, and
more generally for a bounded below object `K'` of `D⁺_{𝒜'_X}(C_{τ'}/X)`, cohomology over `X`
computed for `τ'` agrees with cohomology over `X` of the inverse image computed for `τ`:

`H^n_{τ'}(X, ℱ') = H^n_τ(X, ε_X^{-1}ℱ')` and `H^n_{τ'}(X, K') = H^n_τ(X, ε_X^{-1}K')`.

This file proves both, as the assertion that the canonical comparison maps are isomorphisms.

## Main definitions

* `Stacks.ComparingTopologies.cohomologyChangeOfTopology`: the canonical map
  `H^n_{τ'}(X, ℱ') ⟶ H^n_τ(X, ε_X^{-1}ℱ')`, the comparison map of Stacks 0EZC precomposed with
  the unit `ℱ' ⟶ ε_{X,*}ε_X^{-1}ℱ'`.

## Main results

* `Stacks.ComparingTopologies.isIso_cohomologyChangeOfTopology_app`: the first clause.
* `Stacks.ComparingTopologies.isIso_derivedCohomologyComparison_app_of_weakSerre` and
  `isIso_homology_derivedCohomologyComparison_app_of_weakSerre`: the second clause, first as an
  isomorphism in `D⁺(Ab)` and then in each degree.

## The argument

For a single sheaf: an object of `𝒜'_X` already satisfies the sheaf condition for `τ`, so the
unit `ℱ' ⟶ ε_{X,*}ε_X^{-1}ℱ'` is invertible, and `ε_X^{-1}ℱ'` lies in `𝒜_X` by definition of
that class, so the comparison map of Stacks 0EZC is invertible in every degree by the vanishing
condition. For a bounded below complex: the derived unit `K' ⟶ Rε_{X,*}(ε_X^{-1}K')` is
invertible by clause (1) of Stacks 0EZF, and cohomology over `X` for `τ` is cohomology over `X`
for `τ'` of the derived direct image.

## Hypotheses

Nothing is assumed beyond the tag's own hypotheses: the condition `(V_n)` in every degree is
`CohomologyComparison.vanishingCondition_all` (Stacks 0EZF).

## References

* [Stacks Project, Tag 0EZH](https://stacks.math.columbia.edu/tag/0EZH)
* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
* [Stacks Project, Tag 0EZ3](https://stacks.math.columbia.edu/tag/0EZ3)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.ComparingTopologies

open Stacks.Cohomology.Localization

variable {C : Type u} [Category.{v} C]

attribute [local instance] HasDerivedCategory.standard

/-- The canonical map `H^n_{τ'}(X, ℱ') ⟶ H^n_τ(X, ε_X^{-1}ℱ')`: the unit
`ℱ' ⟶ ε_{X,*}ε_X^{-1}ℱ'` of the change-of-topology adjunction followed by the comparison map
`H^n_{τ'}(X, ε_{X,*}ℱ) ⟶ H^n_τ(X, ℱ)` of Stacks 0EZC at `ℱ = ε_X^{-1}ℱ'`. -/
def cohomologyChangeOfTopology (S : CohomologyComparison C) (X : C) (n : ℕ) :
    (globalSectionsOver S.coarseCoverage.toGrothendieck X).rightDerived n ⟶
      abelianComparisonPullback S.fineCoverage S.coarseCoverage X ⋙
        (globalSectionsOver S.fineCoverage.toGrothendieck X).rightDerived n :=
  Functor.whiskerRight (abelianComparisonAdjunction S.fineCoverage S.coarseCoverage
      S.coarse_le_fine X).unit
    ((globalSectionsOver S.coarseCoverage.toGrothendieck X).rightDerived n) ≫
  Functor.whiskerLeft (abelianComparisonPullback S.fineCoverage S.coarseCoverage X)
    (cohomologyComparison S X n)

/-- **Clause (1) of Stacks 0EZH.** In the comparison situation of Stacks 0EZ3, let `X` be an
object of `C` and let `ℱ'` be a sheaf of the weak Serre class `𝒜'_X` on the coarser localized
site. Then for every `n` the canonical map

`H^n_{τ'}(X, ℱ') ⟶ H^n_τ(X, ε_X^{-1}ℱ')`

is an isomorphism. -/
@[stacks 0EZH "(1)"]
theorem isIso_cohomologyChangeOfTopology_app (S : CohomologyComparison C) (X : C)
    (F : Sheaf (S.coarseCoverage.toGrothendieck.over X) Ab.{max u v})
    (hF : S.weakSerre X F) (n : ℕ) :
    IsIso ((cohomologyChangeOfTopology S X n).app F) := by
  have hunit : IsIso ((abelianComparisonAdjunction S.fineCoverage S.coarseCoverage
      S.coarse_le_fine X).unit.app F) :=
    isIso_abelianComparisonAdjunction_unit_of_weakSerre S X F hF
  have h1 : IsIso (((globalSectionsOver S.coarseCoverage.toGrothendieck X).rightDerived n).map
      ((abelianComparisonAdjunction S.fineCoverage S.coarseCoverage
        S.coarse_le_fine X).unit.app F)) := inferInstance
  have h2 : IsIso ((cohomologyComparison S X n).app
      ((abelianComparisonPullback S.fineCoverage S.coarseCoverage X).obj F)) :=
    isIso_cohomologyComparison_app S n (S.vanishingCondition_all n) X n le_rfl _
      ((S.weakSerre X).prop_map_obj _ hF)
  dsimp only [cohomologyChangeOfTopology]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  infer_instance

/-- **Clause (2) of Stacks 0EZH, as an isomorphism in `D⁺(Ab)`.** In the comparison situation of
Stacks 0EZ3, let `X` be an object of `C` and let `K'` be a bounded below object of the derived
category of abelian sheaves on `C_{τ'}/X` all of whose cohomology sheaves lie in `𝒜'_X`, that
is, an object of `D⁺_{𝒜'_X}(C_{τ'}/X)`. Then the canonical map

`RΓ_{τ'}(X, K') ⟶ RΓ_τ(X, ε_X^{-1}K')`

is an isomorphism. -/
@[stacks 0EZH "(2), as an isomorphism of derived global sections"]
theorem isIso_derivedCohomologyComparison_app_of_weakSerre (S : CohomologyComparison C) (X : C)
    (K : DerivedCategory.Plus (AbelianSheaves S.coarseCoverage.toGrothendieck X))
    (hK : ∀ i : ℤ, S.weakSerre X ((DerivedCategory.Plus.homologyFunctor _ i).obj K)) :
    IsIso ((derivedCohomologyComparison S X).app K) := by
  have := isIso_derivedComparisonUnit_app S X K hK
  infer_instance

/-- **Clause (2) of Stacks 0EZH.** With `X` and `K'` as above, the canonical map

`H^n_{τ'}(X, K') ⟶ H^n_τ(X, ε_X^{-1}K')`

is an isomorphism for every `n`. -/
@[stacks 0EZH "(2)"]
theorem isIso_homology_derivedCohomologyComparison_app_of_weakSerre
    (S : CohomologyComparison C) (X : C)
    (K : DerivedCategory.Plus (AbelianSheaves S.coarseCoverage.toGrothendieck X))
    (hK : ∀ i : ℤ, S.weakSerre X ((DerivedCategory.Plus.homologyFunctor _ i).obj K))
    (n : ℤ) :
    IsIso ((DerivedCategory.Plus.homologyFunctor Ab.{max u v} n).map
      ((derivedCohomologyComparison S X).app K)) := by
  have := isIso_derivedCohomologyComparison_app_of_weakSerre S X K hK
  infer_instance

end Stacks.ComparingTopologies

end
