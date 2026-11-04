module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.PhTorsionComparison

/-!
# Étale and ph cohomology of torsion sheaves agree (Stacks 0DE6)

Let `B` be a big ph site, `X` an object of it, `ε_X : Sh((Sch/X)_ph) ⟶ Sh((Sch/X)_étale)` the
change of topology, `π_X : Sh((Sch/X)_étale) ⟶ Sh(X_étale)` the projection to the small étale site
and `a_X = π_X ∘ ε_X : Sh((Sch/X)_ph) ⟶ Sh(X_étale)`, so that `a_X⁻¹ = ε_X⁻¹ ∘ π_X⁻¹`. Then

1. `H^q(X_étale, F) = H^q_ph(X, a_X⁻¹F)` for a torsion abelian sheaf `F` on `X_étale`;
2. `H^q(X_étale, K) = H^q_ph(X, a_X⁻¹K)` for `K` in `D⁺(X_étale)` with torsion cohomology sheaves;

and, as an example, `H^q_étale(X, A) = H^q_ph(X, A)` for a torsion abelian group `A`.

## Main results

* `AlgebraicGeometry.phEtaleTorsionCohomologyIso` — **Stacks 0DE6 (1)**.
* `AlgebraicGeometry.phEtaleTorsionDerivedCohomologyIso` — **Stacks 0DE6 (2)**.
* `AlgebraicGeometry.phEtaleTorsionConstantCohomologyIso` — **the example of Stacks 0DE6**.

## Implementation notes

The three isomorphisms are `AlgebraicGeometry.phCohomologyComparisonIso`,
`AlgebraicGeometry.phCohomologyComparisonPlusIso` and
`AlgebraicGeometry.phCohomologyConstantComparisonIso` with their two proper base change inputs
proved; these are the generic comparisons of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.FineTopologyCohomologyComparison`
(`AlgebraicGeometry.cohomologyFineComparisonIso`,
`AlgebraicGeometry.derivedGlobalSectionsFineComparisonIso`,
`AlgebraicGeometry.cohomologyConstantFineComparisonIso`) in the comparison situation of the ph and
étale topologies, `AlgebraicGeometry.phEtaleTorsionComparison` (Stacks 0F0I), whose proper base
change inputs (Stacks 0A3U for sheaves of sets and Stacks 095T) are proved. They are the canonical
maps, the pullback along `a_X` on cohomology: the unit `K ⟶ Ra_{X,*}a_X⁻¹K` (Stacks 0DE5, here in
the form of Stacks 0DDI composed with the change-of-topology comparison of Stacks 0EZH) on derived
global sections, read through `RΓ(X_étale, Ra_{X,*}-) = RΓ_ph(X, -)` — the argument of the source
via Cohomology on Sites, Remark 08J6. `H^q_ph(X, -)` is the `q`-th right derived functor of the
global sections over the final object `X / X` of the ph site over `X`.

Objects of the big ph site are the schemes `X` of the statement; every scheme is one, for a
suitable big ph site.

## References

* [Stacks Project, Tag 0DE6](https://stacks.math.columbia.edu/tag/0DE6)
* [Stacks Project, Tag 0DE5](https://stacks.math.columbia.edu/tag/0DE5)
* [Stacks Project, Tag 0F0I](https://stacks.math.columbia.edu/tag/0F0I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.ComparingTopologies

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable (B : BigPHSite.{u})

/-- The category of abelian sheaves on the small étale site of an object `X` of the big étale site
associated with `B` is Grothendieck abelian. -/
local instance (X : (phAssociatedBigEtaleSite B).Scheme) :
    IsGrothendieckAbelian.{u + 1} (Sheaf (SmallEtale.topology (phAssociatedBigEtaleSite B)
      X.obj X.property) Ab.{u + 1}) :=
  smallEtaleSheaf_isGrothendieckAbelian _ X

variable (X : (phAssociatedBigEtaleSite B).Scheme)

/-- **Stacks 0DE6 (1).** For an object `X` of the big ph site, a torsion abelian sheaf `F` on
`X_étale` and every `q`, `H^q(X_étale, F) = H^q_ph(X, a_X⁻¹F)`, where
`a_X⁻¹F = ε_X⁻¹π_X⁻¹F` is the pullback to the ph site over `X`. The isomorphism is the canonical
one, the pullback along `a_X` on cohomology (`AlgebraicGeometry.cohomologyFineComparisonIso`). -/
@[stacks 0DE6 "(1)"]
public def phEtaleTorsionCohomologyIso
    (F : Sheaf (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property)
      AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty.{u + 1}
      (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property) F)
    (q : ℕ) :
    (((sheafSections (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property)
        AddCommGrpCat.{u + 1}).obj
        (op (SmallEtale.final (phAssociatedBigEtaleSite B) X.obj X.property))).rightDerived q).obj
        F ≅
      ((Stacks.globalSectionsOver (phEtaleTorsionComparison B).fineCoverage.toGrothendieck
          X).rightDerived q).obj
        ((abelianComparisonPullback (phEtaleTorsionComparison B).fineCoverage
            (phEtaleTorsionComparison B).coarseCoverage X).obj
          (((SmallEtale.inclusion (phAssociatedBigEtaleSite B) X.obj X.property).sheafPullback
            AddCommGrpCat.{u + 1}
            (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property)
            ((phAssociatedBigEtaleSite B).topology.over X)).obj F)) :=
  phCohomologyComparisonIso B
    (fun f g g' f' sq _ =>
      Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isProper f g g' f' sq)
    (fun f _ => Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper f) X F hF q

/-- **Stacks 0DE6 (2).** For an object `X` of the big ph site, `K` in `D⁺(X_étale)` with torsion
cohomology sheaves and every `q`, `H^q(X_étale, K) = H^q_ph(X, a_X⁻¹K)`: the degree `q`
cohomology of the derived global sections `RΓ(X_étale, K)` and `RΓ_ph(X, a_X⁻¹K)`, with
`a_X⁻¹ = ε_X⁻¹ ∘ π_X⁻¹` on `D⁺`. The isomorphism is the canonical one, the degree `q` cohomology of
the pullback along `a_X`, `AlgebraicGeometry.derivedGlobalSectionsFineComparisonIso`. -/
@[stacks 0DE6 "(2)"]
public def phEtaleTorsionDerivedCohomologyIso
    (K : DerivedCategory.Plus (Sheaf (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj
      X.property) AddCommGrpCat.{u + 1}))
    (hK : ∀ i : ℤ, Stacks.Torsion.torsionSheafProperty.{u + 1}
      (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property)
      ((DerivedCategory.Plus.homologyFunctor _ i).obj K))
    (q : ℤ) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        (((sheafSections (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property)
          AddCommGrpCat.{u + 1}).obj
          (op (SmallEtale.final (phAssociatedBigEtaleSite B) X.obj
            X.property))).rightDerivedFunctorPlus.obj K) ≅
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((Stacks.globalSectionsOver (phEtaleTorsionComparison B).fineCoverage.toGrothendieck
            X).rightDerivedFunctorPlus.obj
          ((abelianComparisonPullback (phEtaleTorsionComparison B).fineCoverage
              (phEtaleTorsionComparison B).coarseCoverage X).mapDerivedCategoryPlus.obj
            (((SmallEtale.inclusion (phAssociatedBigEtaleSite B) X.obj X.property).sheafPullback
              AddCommGrpCat.{u + 1}
              (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property)
              ((phAssociatedBigEtaleSite B).topology.over X)).mapDerivedCategoryPlus.obj K))) :=
  phCohomologyComparisonPlusIso B
    (fun f g g' f' sq _ =>
      Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isProper f g g' f' sq)
    (fun f _ => Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper f) X K hK q

/-- **Stacks 0DE6, the example.** For an object `X` of the big ph site, a torsion abelian group `A`
and every `q`, `H^q_étale(X, A) = H^q_ph(X, A)`, the cohomology of the constant sheaves with value
`A` on `X_étale` and on the ph site over `X`. The isomorphism is part (1) at the constant sheaf,
which is torsion, followed by the identification `a_X⁻¹A = A` of constant sheaves (both are left
adjoint to global sections); see `AlgebraicGeometry.cohomologyConstantFineComparisonIso`. -/
@[stacks 0DE6 "the example: H^q_et(X, A) = H^q_ph(X, A) for a torsion abelian group A"]
public def phEtaleTorsionConstantCohomologyIso (A : AddCommGrpCat.{u + 1}) (hA : IsAddTorsion A)
    (q : ℕ) :
    (((sheafSections (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property)
        AddCommGrpCat.{u + 1}).obj
        (op (SmallEtale.final (phAssociatedBigEtaleSite B) X.obj X.property))).rightDerived q).obj
        ((constantSheaf (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property)
          AddCommGrpCat.{u + 1}).obj A) ≅
      ((Stacks.globalSectionsOver (phEtaleTorsionComparison B).fineCoverage.toGrothendieck
          X).rightDerived q).obj
        ((constantSheaf ((phEtaleTorsionComparison B).fineCoverage.toGrothendieck.over X)
          AddCommGrpCat.{u + 1}).obj A) :=
  phCohomologyConstantComparisonIso B
    (fun f g g' f' sq _ =>
      Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isProper f g g' f' sq)
    (fun f _ => Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper f) X A hA q

end AlgebraicGeometry

end
