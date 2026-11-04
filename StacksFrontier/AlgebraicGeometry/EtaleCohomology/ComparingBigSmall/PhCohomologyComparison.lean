module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.FineTopologyCohomologyComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.PhComparisonSituation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.ProperEtaleChangeOfTopology

/-!
# Comparing ph and étale cohomology of torsion sheaves

Let `B` be a chosen big ph site, `ε_X` the change of topology from the étale to the ph topology on
the big site over `X`, `π_X` the projection from the big étale site over `X` to the small étale
site of `X`, and `a_X = π_X ∘ ε_X`. Stacks 0DE4 is the specialization of Stacks 0EZF and 0EZA to
the comparison situation of Stacks 0F0I, `AlgebraicGeometry.phEtaleCohomologyComparison`; its four
parts are the ph instances of the four results of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.ProperEtaleChangeOfTopology`.

## Main results

* `AlgebraicGeometry.phComparison_smallEtaleInclusion` — Stacks 0DE4 (1).
* `AlgebraicGeometry.isIso_phHigherSmallEtaleBaseChange` — Stacks 0DE4 (2): the base change map
  `AlgebraicGeometry.higherSmallEtaleFineBaseChange` is an isomorphism.
* `AlgebraicGeometry.isIso_phDerivedComparisonUnit_app` — Stacks 0DE4 (3).
* `AlgebraicGeometry.isIso_phDerivedSmallEtaleBaseChange` — Stacks 0DE4 (4): the base change map
  `AlgebraicGeometry.derivedSmallEtaleFineBaseChange` is an isomorphism.
* `AlgebraicGeometry.isIso_phDerivedSmallEtaleUnit` — Stacks 0DE5, the instance of
  `AlgebraicGeometry.isIso_derivedSmallEtaleFineUnit`.
* `AlgebraicGeometry.phCohomologyComparisonIso`, `AlgebraicGeometry.phCohomologyComparisonPlusIso`
  and `AlgebraicGeometry.phCohomologyConstantComparisonIso` — Stacks 0DE6 (1), (2) and its
  example, the instances of the statements of `ComparingBigSmall/FineTopologyCohomologyComparison`.

## Implementation notes

The inputs are those of Stacks 0F0I: `h0A3U`, the proper base change theorem in degree zero for
sheaves of sets, and `h095T`, Stacks 095T, which gives the comparison of higher direct images
along proper morphisms of Stacks 0DDJ (2). Parts (2) and (4) also deduce from `h095T` that the base
change map of Stacks 0DDJ (2) on `D⁺` is an isomorphism
(`AlgebraicGeometry.isIso_bigSmallEtaleDerivedPlusBaseChange_of_cohomologyCommutesWithBaseChange`).

## References

* [Stacks Project, Tag 0DE4](https://stacks.math.columbia.edu/tag/0DE4)
* [Stacks Project, Tag 0DE5](https://stacks.math.columbia.edu/tag/0DE5)
* [Stacks Project, Tag 0DE6](https://stacks.math.columbia.edu/tag/0DE6)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.ComparingTopologies
open Stacks.Cohomology.Localization

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable (B : BigPHSite.{u})
  (h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback g' f' f g), IsProper f →
      IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w))
  (h095T : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f],
    Stacks.EtaleCohomology.CohomologyCommutesWithBaseChange.{u, 0} f)

/-- The category of abelian sheaves on the small étale site of `X` is Grothendieck abelian. -/
local instance (X : (phAssociatedBigEtaleSite B).Scheme) :
    IsGrothendieckAbelian.{u + 1} (Sheaf (SmallEtale.topology (phAssociatedBigEtaleSite B)
      X.obj X.property) Ab.{u + 1}) :=
  smallEtaleSheaf_isGrothendieckAbelian _ X

include h0A3U h095T

/-- For an object `X` of the big ph site and a torsion abelian sheaf `F` on `X_étale`,
`ε_{X,*}a_X⁻¹F = π_X⁻¹F` — the unit `π_X⁻¹F ⟶ ε_{X,*}ε_X⁻¹π_X⁻¹F` is an isomorphism — and
`R^i ε_{X,*}(a_X⁻¹F) = 0` for `i > 0`. -/
public theorem phComparison_smallEtaleInclusion (X : (phAssociatedBigEtaleSite B).Scheme)
    (F : Sheaf (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property) Ab.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty.{u + 1}
      (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property) F) :
    IsIso ((abelianComparisonAdjunction B.precoverage
        (phAssociatedBigEtaleSite B).precoverage
        (BigPHSite.etalePrecoverage_le_precoverage B) X).unit.app
        (((SmallEtale.inclusion (phAssociatedBigEtaleSite B) X.obj X.property).sheafPullback
          Ab.{u + 1} (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property)
          ((phAssociatedBigEtaleSite B).topology.over X)).obj F)) ∧
      ∀ i : ℕ, 1 ≤ i → IsZero (((abelianComparisonPushforward B.precoverage
          (phAssociatedBigEtaleSite B).precoverage
          (BigPHSite.etalePrecoverage_le_precoverage B) X).rightDerived i).obj
        ((abelianComparisonPullback B.precoverage
          (phAssociatedBigEtaleSite B).precoverage X).obj
          (((SmallEtale.inclusion (phAssociatedBigEtaleSite B) X.obj X.property).sheafPullback
            Ab.{u + 1} (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property)
            ((phAssociatedBigEtaleSite B).topology.over X)).obj F))) :=
  ⟨isIso_comparisonUnit_smallEtaleInclusion
      (phAssociatedBigEtaleSite B) B.precoverage
      (BigPHSite.etalePrecoverage_le_precoverage B)
      (fun X F => (smallEtaleInverseImage_isSheaf_ph_of_properBaseChange B X.1 X.2 F h0A3U).1)
      (properDirectImageComparison_of_cohomologyCommutesWithBaseChange _ h095T)
      (BigPHSite.exists_properRefinement B) X F hF,
    isZero_rightDerived_comparisonPushforward_smallEtaleInclusion
      (phAssociatedBigEtaleSite B) B.precoverage
      (BigPHSite.etalePrecoverage_le_precoverage B)
      (fun X F => (smallEtaleInverseImage_isSheaf_ph_of_properBaseChange B X.1 X.2 F h0A3U).1)
      (properDirectImageComparison_of_cohomologyCommutesWithBaseChange _ h095T)
      (BigPHSite.exists_properRefinement B) X F hF⟩

/-- For a proper morphism `f : X ⟶ Y` of the big ph site and a torsion abelian sheaf `F` on
`X_étale`, the base change map `a_Y⁻¹(R^i f_{small,*}F) ⟶ R^i f_{big,ph,*}(a_X⁻¹F)` is an
isomorphism for all `i`; the map is `AlgebraicGeometry.higherSmallEtaleFineBaseChange`, the degree
`i` cohomology of the derived base change map of part (4). -/
public theorem isIso_phHigherSmallEtaleBaseChange
    {X Y : (phAssociatedBigEtaleSite B).Scheme} (f : X ⟶ Y)
    (hf : IsProper ((phAssociatedBigEtaleSite B).inclusion.map f))
    (F : Sheaf (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property) Ab.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty.{u + 1}
      (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property) F)
    (i : ℕ) :
    IsIso (higherSmallEtaleFineBaseChange (phAssociatedBigEtaleSite B) B.precoverage
      (BigPHSite.etalePrecoverage_le_precoverage B)
      (fun X F => (smallEtaleInverseImage_isSheaf_ph_of_properBaseChange B X.1 X.2 F h0A3U).1)
      (properDirectImageComparison_of_cohomologyCommutesWithBaseChange _ h095T)
      (BigPHSite.exists_properRefinement B) f F i) :=
  isIso_higherSmallEtaleFineBaseChange _ _ _ _ _ _ h095T f hf F hF i

/-- For an object `X` of the big ph site and `L` in `D⁺(X_étale)` with torsion cohomology sheaves,
the map `π_X⁻¹L ⟶ Rε_{X,*}(a_X⁻¹L)` is an isomorphism. -/
public theorem isIso_phDerivedComparisonUnit_app (X : (phAssociatedBigEtaleSite B).Scheme)
    (L : DerivedCategory.Plus
      (Sheaf (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property) Ab.{u + 1}))
    (hL : ∀ i : ℤ, Stacks.Torsion.torsionSheafProperty.{u + 1}
      (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property)
      ((DerivedCategory.Plus.homologyFunctor _ i).obj L)) :
    IsIso ((derivedComparisonUnit (phEtaleCohomologyComparison B h0A3U h095T) X).app
      (((SmallEtale.inclusion (phAssociatedBigEtaleSite B) X.obj X.property).sheafPullback
        Ab.{u + 1} (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property)
        ((phAssociatedBigEtaleSite B).topology.over X)).mapDerivedCategoryPlus.obj L)) :=
  isIso_derivedComparisonUnit_app_smallEtaleInclusion
      (phAssociatedBigEtaleSite B) B.precoverage
    (BigPHSite.etalePrecoverage_le_precoverage B)
    (fun X F => (smallEtaleInverseImage_isSheaf_ph_of_properBaseChange B X.1 X.2 F h0A3U).1)
    (properDirectImageComparison_of_cohomologyCommutesWithBaseChange _ h095T)
      (BigPHSite.exists_properRefinement B) X L hL

/-- For a proper morphism `f : X ⟶ Y` of the big ph site and `L` in `D⁺(X_étale)` with torsion
cohomology sheaves, the base change map `a_Y⁻¹(Rf_{small,*}L) ⟶ Rf_{big,ph,*}(a_X⁻¹L)`,
`AlgebraicGeometry.derivedSmallEtaleFineBaseChange`, is an isomorphism. -/
public theorem isIso_phDerivedSmallEtaleBaseChange
    {X Y : (phAssociatedBigEtaleSite B).Scheme} (f : X ⟶ Y)
    (hf : IsProper ((phAssociatedBigEtaleSite B).inclusion.map f))
    (L : DerivedCategory.Plus
      (Sheaf (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property) Ab.{u + 1}))
    (hL : ∀ i : ℤ, Stacks.Torsion.torsionSheafProperty.{u + 1}
      (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property)
      ((DerivedCategory.Plus.homologyFunctor _ i).obj L)) :
    IsIso (derivedSmallEtaleFineBaseChange (phAssociatedBigEtaleSite B) B.precoverage
      (BigPHSite.etalePrecoverage_le_precoverage B)
      (fun X F => (smallEtaleInverseImage_isSheaf_ph_of_properBaseChange B X.1 X.2 F h0A3U).1)
      (properDirectImageComparison_of_cohomologyCommutesWithBaseChange _ h095T)
      (BigPHSite.exists_properRefinement B) f L) :=
  isIso_derivedSmallEtaleFineBaseChange _ _ _ _ _ _ h095T f hf L hL

/-! ### Stacks 0DE5 and Stacks 0DE6 -/

section Cohomology

variable (X : (phAssociatedBigEtaleSite B).Scheme)

/-- For a torsion abelian sheaf `F` on `X_étale` and every `q`,
`H^q(X_étale, F) = H^q_{ph}(X, a_X⁻¹F)`. The isomorphism is the canonical one, the pullback along
`a_X` on cohomology: see `AlgebraicGeometry.derivedGlobalSectionsFineComparisonIso`, of which it is
the degree `q` cohomology at `F` placed in degree zero. -/
public def phCohomologyComparisonIso
    (F : Sheaf (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property)
      AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty.{u + 1}
      (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property) F)
    (q : ℕ) :
    (((sheafSections (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property)
        AddCommGrpCat.{u + 1}).obj
        (op (SmallEtale.final (phAssociatedBigEtaleSite B) X.obj X.property))).rightDerived q).obj
        F ≅
      ((Stacks.globalSectionsOver
          (phEtaleCohomologyComparison B h0A3U h095T).fineCoverage.toGrothendieck
          X).rightDerived q).obj
        ((abelianComparisonPullback (phEtaleCohomologyComparison B h0A3U h095T).fineCoverage
            (phEtaleCohomologyComparison B h0A3U h095T).coarseCoverage X).obj
          (((SmallEtale.inclusion (phAssociatedBigEtaleSite B) X.obj X.property).sheafPullback
            AddCommGrpCat.{u + 1}
            (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property)
            ((phAssociatedBigEtaleSite B).topology.over X)).obj F)) :=
  cohomologyFineComparisonIso (phAssociatedBigEtaleSite B) B.precoverage _ _
      (properDirectImageComparison_of_cohomologyCommutesWithBaseChange _ h095T) _ X F hF q

/-- For `K` in `D⁺(X_étale)` with torsion cohomology sheaves and every `q`,
`H^q(X_étale, K) = H^q_{ph}(X, a_X⁻¹K)`, the cohomology of the derived global sections. The
isomorphism is the canonical one, the degree `q` cohomology of the pullback along `a_X`,
`AlgebraicGeometry.derivedGlobalSectionsFineComparisonIso`. -/
public def phCohomologyComparisonPlusIso
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
        ((Stacks.globalSectionsOver
            (phEtaleCohomologyComparison B h0A3U h095T).fineCoverage.toGrothendieck
            X).rightDerivedFunctorPlus.obj
          ((abelianComparisonPullback (phEtaleCohomologyComparison B h0A3U h095T).fineCoverage
              (phEtaleCohomologyComparison B h0A3U h095T).coarseCoverage
              X).mapDerivedCategoryPlus.obj
            (((SmallEtale.inclusion (phAssociatedBigEtaleSite B) X.obj X.property).sheafPullback
              AddCommGrpCat.{u + 1}
              (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property)
              ((phAssociatedBigEtaleSite B).topology.over X)).mapDerivedCategoryPlus.obj K))) :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q).mapIso
    (derivedGlobalSectionsFineComparisonIso (phAssociatedBigEtaleSite B) B.precoverage _ _
      (properDirectImageComparison_of_cohomologyCommutesWithBaseChange _ h095T) _ X K
      hK)

/-- For a torsion abelian group `A` and every `q`, `H^q_étale(X, A) = H^q_{ph}(X, A)`, the
cohomology of the constant sheaves. The isomorphism is the canonical one: the pullback along `a_X`
of part (1) at the constant sheaf, followed by the identification `a_X⁻¹A = A` of constant sheaves
(both are left adjoint to global sections). -/
public def phCohomologyConstantComparisonIso (A : AddCommGrpCat.{u + 1}) (hA : IsAddTorsion A)
    (q : ℕ) :
    (((sheafSections (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property)
        AddCommGrpCat.{u + 1}).obj
        (op (SmallEtale.final (phAssociatedBigEtaleSite B) X.obj X.property))).rightDerived q).obj
        ((constantSheaf (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property)
          AddCommGrpCat.{u + 1}).obj A) ≅
      ((Stacks.globalSectionsOver
          (phEtaleCohomologyComparison B h0A3U h095T).fineCoverage.toGrothendieck
          X).rightDerived q).obj
        ((constantSheaf
          ((phEtaleCohomologyComparison B h0A3U h095T).fineCoverage.toGrothendieck.over X)
          AddCommGrpCat.{u + 1}).obj A) :=
  cohomologyConstantFineComparisonIso (phAssociatedBigEtaleSite B) B.precoverage _ _
      (properDirectImageComparison_of_cohomologyCommutesWithBaseChange _ h095T) _ X A hA q

end Cohomology

/-- For an object `X` of the big ph site and `L` in `D⁺(X_étale)` with torsion cohomology sheaves,
the map `L ⟶ Ra_{X,*}a_X⁻¹L` is an isomorphism, where `a_X = π_X ∘ ε_X` and the map is
`AlgebraicGeometry.derivedSmallEtaleFineUnit`. -/
public theorem isIso_phDerivedSmallEtaleUnit (X : (phAssociatedBigEtaleSite B).Scheme)
    (L : DerivedCategory.Plus
      (Sheaf (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property) Ab.{u + 1}))
    (hL : ∀ i : ℤ, Stacks.Torsion.torsionSheafProperty.{u + 1}
      (SmallEtale.topology (phAssociatedBigEtaleSite B) X.obj X.property)
      ((DerivedCategory.Plus.homologyFunctor _ i).obj L)) :
    IsIso (derivedSmallEtaleFineUnit (phAssociatedBigEtaleSite B) B.precoverage
      (BigPHSite.etalePrecoverage_le_precoverage B)
      (fun X F => (smallEtaleInverseImage_isSheaf_ph_of_properBaseChange B X.1 X.2 F h0A3U).1)
      (properDirectImageComparison_of_cohomologyCommutesWithBaseChange _ h095T)
      (BigPHSite.exists_properRefinement B) X L) :=
  isIso_derivedSmallEtaleFineUnit (phAssociatedBigEtaleSite B) B.precoverage
    (BigPHSite.etalePrecoverage_le_precoverage B)
    (fun X F => (smallEtaleInverseImage_isSheaf_ph_of_properBaseChange B X.1 X.2 F h0A3U).1)
    (properDirectImageComparison_of_cohomologyCommutesWithBaseChange _ h095T)
    (BigPHSite.exists_properRefinement B) X L hL


end AlgebraicGeometry

end
