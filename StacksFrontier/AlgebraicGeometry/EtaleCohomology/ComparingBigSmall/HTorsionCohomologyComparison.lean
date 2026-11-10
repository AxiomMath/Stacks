module

public import
StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.FineTopologyCohomologyComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.HComparisonSituation
import StacksCore.Tactic.StacksAttribute

/-!
# Étale cohomology of torsion sheaves is h cohomology: Stacks 0EWH

Let `B` be a chosen big h site and `X` one of its schemes. Write `π_X` for the projection from the
big étale site over `X` to the small étale site of `X`, `ε_X` for the change of topology from the
étale to the h topology on the big site over `X`, and `a_X = π_X ∘ ε_X`, so that
`a_X⁻¹ = ε_X⁻¹ ∘ π_X⁻¹`. This file proves Stacks 0EWH:

1. `H^q(X_étale, F) = H^q_h(X, a_X⁻¹F)` for a torsion abelian sheaf `F` on `X_étale`;
2. `H^q(X_étale, K) = H^q_h(X, a_X⁻¹K)` for `K` in `D⁺(X_étale)` with torsion cohomology sheaves;
3. (the example) `H^q_étale(X, A) = H^q_h(X, A)` for a torsion abelian group `A`.

## Main definitions

* `AlgebraicGeometry.hCohomologyComparisonIso` — **Stacks 0EWH (1)**.
* `AlgebraicGeometry.hCohomologyComparisonPlusIso` — **Stacks 0EWH (2)**.
* `AlgebraicGeometry.hCohomologyConstantComparisonIso` — **Stacks 0EWH**, the example.

## Implementation notes

These are the instances, at the comparison situation `AlgebraicGeometry.hEtaleCohomologyComparison`
of Stacks 0F0J, of the statements of the module
`ComparingBigSmall.FineTopologyCohomologyComparison`
for a precoverage finer than the étale one. The source deduces the lemma from Stacks 0EWG,
`K ≅ Ra_{X,*}a_X⁻¹K`, by Cohomology on Sites, Remark 08J6, `RΓ(X_étale, Ra_{X,*}-) = RΓ_h(X, -)`.
Here the isomorphism `RΓ(X_étale, K) ≅ RΓ_h(X, a_X⁻¹K)` is the same canonical map, assembled from
the unit `K ⟶ π_{X,*}π_X⁻¹K` (Stacks 0DDI) and the change-of-topology comparison of Stacks 0EZH (2)
at `π_X⁻¹K`, whose cohomology sheaves lie in the classes `𝒜'_X` of Stacks 0F0J.

The h cohomology `H^q_h(X, -)` is the cohomology of global sections over `X` on the localization at
`X` of the h topology of `B`, `Stacks.globalSectionsOver B.precoverage.toGrothendieck X`, and
`ε_X⁻¹` is `Stacks.ComparingTopologies.abelianComparisonPullback B.precoverage
(hAssociatedBigEtaleSite B).precoverage X`, the h sheafification of an étale sheaf on the big site
over `X`. All sheaves take values in `AddCommGrpCat.{u + 1}`; the derived categories are those of
`HasDerivedCategory.standard`, the model in which Stacks 0EZH is stated.

## References

* [Stacks Project, Tag 0EWG](https://stacks.math.columbia.edu/tag/0EWG)
* [Stacks Project, Tag 0EWH](https://stacks.math.columbia.edu/tag/0EWH)
* [Stacks Project, Tag 08J6](https://stacks.math.columbia.edu/tag/08J6)
* [Stacks Project, Tag 0F0J](https://stacks.math.columbia.edu/tag/0F0J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.ComparingTopologies

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable (B : BigHSite.{u}) (X : (hAssociatedBigEtaleSite B).Scheme)

/-- The h sheafification `ε_X⁻¹` is right exact, being a left adjoint; this is the instance for the
comparison situation `hEtaleCohomologyComparison`, stated at its h and étale precoverages. -/
local instance : PreservesFiniteColimits
    (abelianComparisonPullback B.precoverage (hAssociatedBigEtaleSite B).precoverage X) :=
  abelianComparisonPullback_preservesFiniteColimits (hEtaleCohomologyComparison B) X

/-- The h sheafification `ε_X⁻¹` is additive, being a left adjoint. -/
local instance :
    (abelianComparisonPullback B.precoverage (hAssociatedBigEtaleSite B).precoverage X).Additive :=
  abelianComparisonPullback_additive (hEtaleCohomologyComparison B) X

/-- **Stacks 0EWH (1).** Let `X` be a scheme, an object of a big h site `B`, and let `F` be a
torsion abelian sheaf on `X_étale`. For every `q`,

`H^q(X_étale, F) = H^q_h(X, a_X⁻¹F)`,

where `a_X⁻¹F = ε_X⁻¹π_X⁻¹F` is the h sheafification of the pullback of `F` to the big étale site
over `X`. The isomorphism is the canonical one: the degree `q` cohomology, at `F` placed in degree
zero, of `AlgebraicGeometry.derivedGlobalSectionsFineComparisonIso`, the pullback along `a_X` on
derived global sections. -/
@[stacks 0EWH "(1)"]
public def hCohomologyComparisonIso
    (F : Sheaf (SmallEtale.topology (hAssociatedBigEtaleSite B) X.obj X.property)
      AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty.{u + 1}
      (SmallEtale.topology (hAssociatedBigEtaleSite B) X.obj X.property) F)
    (q : ℕ) :
    (((sheafSections (SmallEtale.topology (hAssociatedBigEtaleSite B) X.obj X.property)
        AddCommGrpCat.{u + 1}).obj
        (op (SmallEtale.final (hAssociatedBigEtaleSite B) X.obj X.property))).rightDerived q).obj
        F ≅
      ((Stacks.globalSectionsOver B.precoverage.toGrothendieck X).rightDerived q).obj
        ((abelianComparisonPullback B.precoverage (hAssociatedBigEtaleSite B).precoverage X).obj
          (((SmallEtale.inclusion (hAssociatedBigEtaleSite B) X.obj X.property).sheafPullback
            AddCommGrpCat.{u + 1} (SmallEtale.topology (hAssociatedBigEtaleSite B) X.obj X.property)
            ((hAssociatedBigEtaleSite B).topology.over X)).obj F)) :=
  cohomologyFineComparisonIso (hAssociatedBigEtaleSite B) B.precoverage
    (BigHSite.etalePrecoverage_le_precoverage B)
    (fun X F => (smallEtaleInverseImage_isSheaf_h_and_isIso_unit B X.1 X.2 F).1)
    (BigHSite.properDirectImageComparison B) (BigHSite.exists_properRefinement B) X F hF q

/-- **Stacks 0EWH (2).** Let `X` be a scheme, an object of a big h site `B`, and let `K` be an
object of `D⁺(X_étale)` whose cohomology sheaves are torsion. For every `q`,

`H^q(X_étale, K) = H^q_h(X, a_X⁻¹K)`,

the cohomology of the derived global sections `RΓ(X_étale, K)` and `RΓ_h(X, a_X⁻¹K)`, where
`a_X⁻¹ = ε_X⁻¹ ∘ π_X⁻¹` on `D⁺`. The isomorphism is the canonical one: the degree `q` cohomology of
`AlgebraicGeometry.derivedGlobalSectionsFineComparisonIso`, the pullback along `a_X` on derived
global sections. -/
@[stacks 0EWH "(2)"]
public def hCohomologyComparisonPlusIso
    (K : DerivedCategory.Plus (Sheaf (SmallEtale.topology (hAssociatedBigEtaleSite B) X.obj
      X.property) AddCommGrpCat.{u + 1}))
    (hK : ∀ i : ℤ, Stacks.Torsion.torsionSheafProperty.{u + 1}
      (SmallEtale.topology (hAssociatedBigEtaleSite B) X.obj X.property)
      ((DerivedCategory.Plus.homologyFunctor _ i).obj K))
    (q : ℤ) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        (((sheafSections (SmallEtale.topology (hAssociatedBigEtaleSite B) X.obj X.property)
          AddCommGrpCat.{u + 1}).obj
          (op (SmallEtale.final (hAssociatedBigEtaleSite B) X.obj
            X.property))).rightDerivedFunctorPlus.obj K) ≅
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((Stacks.globalSectionsOver B.precoverage.toGrothendieck X).rightDerivedFunctorPlus.obj
          ((abelianComparisonPullback B.precoverage (hAssociatedBigEtaleSite B).precoverage
              X).mapDerivedCategoryPlus.obj
            (((SmallEtale.inclusion (hAssociatedBigEtaleSite B) X.obj X.property).sheafPullback
              AddCommGrpCat.{u + 1}
              (SmallEtale.topology (hAssociatedBigEtaleSite B) X.obj X.property)
              ((hAssociatedBigEtaleSite B).topology.over X)).mapDerivedCategoryPlus.obj K))) :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q).mapIso
    (derivedGlobalSectionsFineComparisonIso (hAssociatedBigEtaleSite B) B.precoverage
      (BigHSite.etalePrecoverage_le_precoverage B)
      (fun X F => (smallEtaleInverseImage_isSheaf_h_and_isIso_unit B X.1 X.2 F).1)
      (BigHSite.properDirectImageComparison B) (BigHSite.exists_properRefinement B) X K hK)

/-- **Stacks 0EWH, the example.** Let `X` be a scheme, an object of a big h site `B`, and let `A`
be a torsion abelian group. For every `q`,

`H^q_étale(X, A) = H^q_h(X, A)`,

the cohomology of the constant sheaves with value `A` on the small étale site of `X` and on the
h site over `X`. The isomorphism is the canonical one: part (1) at the constant sheaf, followed by
the identification `a_X⁻¹A = A` of constant sheaves (both are left adjoint to global sections). -/
@[stacks 0EWH "example"]
public def hCohomologyConstantComparisonIso (A : AddCommGrpCat.{u + 1}) (hA : IsAddTorsion A)
    (q : ℕ) :
    (((sheafSections (SmallEtale.topology (hAssociatedBigEtaleSite B) X.obj X.property)
        AddCommGrpCat.{u + 1}).obj
        (op (SmallEtale.final (hAssociatedBigEtaleSite B) X.obj X.property))).rightDerived q).obj
        ((constantSheaf (SmallEtale.topology (hAssociatedBigEtaleSite B) X.obj X.property)
          AddCommGrpCat.{u + 1}).obj A) ≅
      ((Stacks.globalSectionsOver B.precoverage.toGrothendieck X).rightDerived q).obj
        ((constantSheaf (B.precoverage.toGrothendieck.over X) AddCommGrpCat.{u + 1}).obj A) :=
  cohomologyConstantFineComparisonIso (hAssociatedBigEtaleSite B) B.precoverage
    (BigHSite.etalePrecoverage_le_precoverage B)
    (fun X F => (smallEtaleInverseImage_isSheaf_h_and_isIso_unit B X.1 X.2 F).1)
    (BigHSite.properDirectImageComparison B) (BigHSite.exists_properRefinement B) X A hA q

end AlgebraicGeometry

end
