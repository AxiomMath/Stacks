module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.ProperEtaleComparisonSituation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.FineTopologyCohomologyComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.ProperDirectImageComparisonOfBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.HigherDirectImageVanishing
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactCompositionComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactIdentityComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.VanishingConditionInduction

/-!
# Change of topology for torsion sheaves pulled back from the small étale site

Let `E` be a big étale site and `K` a finer precoverage on its underlying category for which the
comparison situation `AlgebraicGeometry.properEtaleCohomologyComparison` of Stacks 0EZ3 is
available. Write `π_X⁻¹` for the inverse image from the small étale site of `X` to the big étale
site over `X`, `ε_X⁻¹` for the change of topology from the étale topology to `K`, and
`a_X⁻¹ = ε_X⁻¹ ∘ π_X⁻¹`. This file specializes the conclusions of Stacks 0EZF and 0EZA to the
classes `𝒜'_X` of torsion sheaves pulled back from the small étale sites; for `K` the ph
topology this is Stacks 0DE4.

## Main results

* `AlgebraicGeometry.isIso_comparisonUnit_smallEtaleInclusion` and
  `AlgebraicGeometry.isZero_rightDerived_comparisonPushforward_smallEtaleInclusion` — part (1):
  `ε_{X,*} a_X⁻¹F = π_X⁻¹F` and `R^i ε_{X,*}(a_X⁻¹F) = 0` for `i > 0`.
* `AlgebraicGeometry.higherSmallEtaleFineBaseChange` and
  `AlgebraicGeometry.isIso_higherSmallEtaleFineBaseChange` — part (2): for `f` proper, the base
  change map `a_Y⁻¹(R^i f_{small,*}F) ⟶ R^i f_{K,*}(a_X⁻¹F)` is an isomorphism.
* `AlgebraicGeometry.isIso_derivedComparisonUnit_app_smallEtaleInclusion` — part (3):
  `π_X⁻¹L ⟶ Rε_{X,*}(a_X⁻¹L)` is an isomorphism for `L ∈ D⁺(X_étale)` with torsion cohomology.
* `AlgebraicGeometry.derivedSmallEtaleFineBaseChange` and
  `AlgebraicGeometry.isIso_derivedSmallEtaleFineBaseChange` — part (4): for `f` proper, the base
  change map `a_Y⁻¹(Rf_{small,*}L) ⟶ Rf_{K,*}(a_X⁻¹L)` is an isomorphism.

## Implementation notes

The base change map of part (4) is the composite of the base change maps of the two squares the
square of `a = π ∘ ε` is pasted from: `ε_Y⁻¹` applied to the base change map of Stacks 0DDJ (2),
`π_Y⁻¹(Rf_{small,*}L) ⟶ Rf_{big,*}(π_X⁻¹L)`
(`AlgebraicGeometry.bigSmallEtaleDerivedPlusBaseChange`), followed by the base change map of the
change of topology, `ε_Y⁻¹(Rf_{big,*}K') ⟶ Rf_{K,*}(ε_X⁻¹K')`
(`Stacks.ComparingTopologies.derivedComparisonBaseChange`). The first is invertible by the proper
base change theorem Stacks 095T, which therefore enters part (4) as the hypothesis `h095T`, and the
second by Stacks 0EZF (2) at `K' = π_X⁻¹L`. The base change map of part (2) is the degree `i`
cohomology of that of part (4) at `F` placed in degree zero, read through the canonical
identifications of `R^i` with the cohomology of the right derived functors on `D⁺` and of the exact
functors `π⁻¹`, `ε⁻¹` with their actions on `D⁺`.

## References

* [Stacks Project, Tag 0DE4](https://stacks.math.columbia.edu/tag/0DE4)
* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
* [Stacks Project, Tag 0EZA](https://stacks.math.columbia.edu/tag/0EZA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.ComparingTopologies
open Stacks.Cohomology.Localization

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable (E : BigEtaleSite.{u}) (K : Precoverage E.Scheme)
  [K.HasIsos] [K.IsStableUnderComposition] [K.HasPullbacks] [K.IsStableUnderBaseChange]
  (hle : E.precoverage ≤ K)
  (hsheaf : ∀ (X : E.Scheme) (F : Sheaf (SmallEtale.topology E X.obj X.property) (Type (u + 1))),
    Presieve.IsSheaf (K.toGrothendieck.over X)
      ((bigEtaleToSmallEtaleMorphism E X.obj X.property).inverseImage.obj F).obj)
  (hR : ProperDirectImageComparison E)
  (hrefine : ∀ (U : E.Scheme) (R : Presieve U), R ∈ K U →
    ∃ S : Presieve U, S ∈ E.precoverage U ∧
      ∀ ⦃V : E.Scheme⦄ (v : V ⟶ U), S v →
        ∃ (W : E.Scheme) (f : W ⟶ V), IsProper (E.inclusion.map f) ∧
          Presieve.singleton f ∈ K V ∧
          ∃ T : Presieve W, T ∈ E.precoverage W ∧ T.FactorsThruAlong R (f ≫ v))

/-- The category of abelian sheaves on the small étale site of `X` is Grothendieck abelian. -/
local instance (X : E.Scheme) :
    IsGrothendieckAbelian.{u + 1} (Sheaf (SmallEtale.topology E X.obj X.property) Ab.{u + 1}) :=
  smallEtaleSheaf_isGrothendieckAbelian E X

/-- The exact functor `π_X⁻¹` commutes with cohomology on `D⁺`: `H^i(π_X⁻¹L) ≅ π_X⁻¹H^i(L)`. -/
public def smallEtaleInclusionHomologyIso (X : E.Scheme)
    (L : DerivedCategory.Plus (Sheaf (SmallEtale.topology E X.obj X.property) Ab.{u + 1}))
    (i : ℤ) :
    (DerivedCategory.Plus.homologyFunctor (Sheaf (E.topology.over X) Ab.{u + 1}) i).obj
        (((SmallEtale.inclusion E X.obj X.property).sheafPullback Ab.{u + 1}
          (SmallEtale.topology E X.obj X.property)
          (E.topology.over X)).mapDerivedCategoryPlus.obj L) ≅
      ((SmallEtale.inclusion E X.obj X.property).sheafPullback Ab.{u + 1}
          (SmallEtale.topology E X.obj X.property) (E.topology.over X)).obj
        ((DerivedCategory.Plus.homologyFunctor _ i).obj L) :=
  (((SmallEtale.inclusion E X.obj X.property).sheafPullback Ab.{u + 1}
    (SmallEtale.topology E X.obj X.property)
    (E.topology.over X)).mapDerivedCategoryHomologyIso i).app L.obj

/-- The cohomology sheaves of `π_X⁻¹L` lie in `𝒜'_X` when those of `L` are torsion. -/
private theorem weakSerre_homology_pullback (X : E.Scheme)
    (L : DerivedCategory.Plus (Sheaf (SmallEtale.topology E X.obj X.property) Ab.{u + 1}))
    (hL : ∀ i : ℤ, Stacks.Torsion.torsionSheafProperty.{u + 1}
      (SmallEtale.topology E X.obj X.property)
      ((DerivedCategory.Plus.homologyFunctor _ i).obj L)) (i : ℤ) :
    smallEtaleTorsionPullbackClass E X (E.topology.over X)
      ((DerivedCategory.Plus.homologyFunctor _ i).obj
        (((SmallEtale.inclusion E X.obj X.property).sheafPullback Ab.{u + 1}
          (SmallEtale.topology E X.obj X.property)
          (E.topology.over X)).mapDerivedCategoryPlus.obj L)) :=
  ⟨_, hL i, ⟨(smallEtaleInclusionHomologyIso E X L i).symm⟩⟩

include hle hsheaf hR hrefine

/-- **Part (1) of Stacks 0DE4, first half**, for a finer precoverage `K`: for a torsion abelian
sheaf `F` on `X_étale`, the unit `π_X⁻¹F ⟶ ε_{X,*}ε_X⁻¹(π_X⁻¹F)` is an isomorphism, that is
`ε_{X,*}a_X⁻¹F = π_X⁻¹F`. -/
public theorem isIso_comparisonUnit_smallEtaleInclusion (X : E.Scheme)
    (F : Sheaf (SmallEtale.topology E X.obj X.property) Ab.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty.{u + 1} (SmallEtale.topology E X.obj X.property) F) :
    IsIso ((abelianComparisonAdjunction K E.precoverage hle X).unit.app
      (((SmallEtale.inclusion E X.obj X.property).sheafPullback Ab.{u + 1}
        (SmallEtale.topology E X.obj X.property) (E.topology.over X)).obj F)) :=
  isIso_abelianComparisonAdjunction_unit_of_weakSerre
    (properEtaleCohomologyComparison E K hle hsheaf hR hrefine) X _ ⟨F, hF, ⟨Iso.refl _⟩⟩

/-- **Part (1) of Stacks 0DE4, second half**, for a finer precoverage `K`: for a torsion abelian
sheaf `F` on `X_étale`, `R^i ε_{X,*}(a_X⁻¹F) = 0` for `i > 0`. This is the vanishing condition
`(V_i)` of Stacks 0EZF, which holds for every `i`. -/
public theorem isZero_rightDerived_comparisonPushforward_smallEtaleInclusion (X : E.Scheme)
    (F : Sheaf (SmallEtale.topology E X.obj X.property) Ab.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty.{u + 1} (SmallEtale.topology E X.obj X.property) F)
    (i : ℕ) (hi : 1 ≤ i) :
    IsZero (((abelianComparisonPushforward K E.precoverage hle X).rightDerived i).obj
      ((abelianComparisonPullback K E.precoverage X).obj
        (((SmallEtale.inclusion E X.obj X.property).sheafPullback Ab.{u + 1}
          (SmallEtale.topology E X.obj X.property) (E.topology.over X)).obj F))) :=
  (properEtaleCohomologyComparison E K hle hsheaf hR hrefine).vanishingCondition_all i X _
    ⟨_, ⟨F, hF, ⟨Iso.refl _⟩⟩, ⟨Iso.refl _⟩⟩ i hi le_rfl

/-- **Part (3) of Stacks 0DE4**, for a finer precoverage `K`: for `L` in `D⁺(X_étale)` with
torsion cohomology sheaves, the map `π_X⁻¹L ⟶ Rε_{X,*}(a_X⁻¹L)` is an isomorphism. This is
Stacks 0EZF (1), `π_X⁻¹L` having its cohomology sheaves `π_X⁻¹H^i(L)` in `𝒜'_X` because `π_X⁻¹` is
exact. -/
public theorem isIso_derivedComparisonUnit_app_smallEtaleInclusion (X : E.Scheme)
    (L : DerivedCategory.Plus (Sheaf (SmallEtale.topology E X.obj X.property) Ab.{u + 1}))
    (hL : ∀ i : ℤ, Stacks.Torsion.torsionSheafProperty.{u + 1}
      (SmallEtale.topology E X.obj X.property)
      ((DerivedCategory.Plus.homologyFunctor _ i).obj L)) :
    IsIso ((derivedComparisonUnit (properEtaleCohomologyComparison E K hle hsheaf hR hrefine) X).app
      (((SmallEtale.inclusion E X.obj X.property).sheafPullback Ab.{u + 1}
        (SmallEtale.topology E X.obj X.property) (E.topology.over X)).mapDerivedCategoryPlus.obj
          L)) :=
  isIso_derivedComparisonUnit_app _ X _ (weakSerre_homology_pullback E X L hL)

/-- **The base change map of part (4) of Stacks 0DE4**, for a finer precoverage `K`: for a
morphism `f : X ⟶ Y` and `L` in `D⁺(X_étale)`, the base change map
`a_Y⁻¹(Rf_{small,*}L) ⟶ Rf_{K,*}(a_X⁻¹L)` of the square of topoi `a_Y ∘ f_K = f_small ∘ a_X`,
`a_X⁻¹ = ε_X⁻¹ ∘ π_X⁻¹`. It is the composite of the base change maps of the two squares that square
is pasted from: `ε_Y⁻¹` applied to the base change map
`π_Y⁻¹(Rf_{small,*}L) ⟶ Rf_{big,*}(π_X⁻¹L)` of Stacks 0DDJ (2),
`AlgebraicGeometry.bigSmallEtaleDerivedPlusBaseChange`, followed by the base change map
`ε_Y⁻¹(Rf_{big,*}π_X⁻¹L) ⟶ Rf_{K,*}(ε_X⁻¹π_X⁻¹L)` of the change of topology of Stacks 0EZF (2),
`Stacks.ComparingTopologies.derivedComparisonBaseChange`. -/
public def derivedSmallEtaleFineBaseChange {X Y : E.Scheme} (f : X ⟶ Y)
    (L : DerivedCategory.Plus (Sheaf (SmallEtale.topology E X.obj X.property) Ab.{u + 1})) :
    (abelianComparisonPullback K E.precoverage Y).rightDerivedFunctorPlus.obj
        (((SmallEtale.inclusion E Y.obj Y.property).sheafPullback Ab.{u + 1}
          (SmallEtale.topology E Y.obj Y.property)
          (E.topology.over Y)).mapDerivedCategoryPlus.obj
          ((E.smallPushforward f Ab.{u + 1}).rightDerivedFunctorPlus.obj L)) ⟶
      (overPushforward K.toGrothendieck f).rightDerivedFunctorPlus.obj
        ((abelianComparisonPullback K E.precoverage X).rightDerivedFunctorPlus.obj
          (((SmallEtale.inclusion E X.obj X.property).sheafPullback Ab.{u + 1}
            (SmallEtale.topology E X.obj X.property)
            (E.topology.over X)).mapDerivedCategoryPlus.obj L)) :=
  (abelianComparisonPullback K E.precoverage Y).rightDerivedFunctorPlus.map
      (bigSmallEtaleDerivedPlusBaseChange E f (bigEtaleOver_topology_eq_of_obj E X)
        (bigEtaleOver_topology_eq_of_obj E Y) L) ≫
    (derivedComparisonBaseChange (properEtaleCohomologyComparison E K hle hsheaf hR hrefine)
      f).app (((SmallEtale.inclusion E X.obj X.property).sheafPullback Ab.{u + 1}
        (SmallEtale.topology E X.obj X.property) (E.topology.over X)).mapDerivedCategoryPlus.obj L)

/-- **Part (4) of Stacks 0DE4**, for a finer precoverage `K`, granted Stacks 095T: for a proper
morphism `f : X ⟶ Y` and `L` in `D⁺(X_étale)` with torsion cohomology sheaves, the base change map
`a_Y⁻¹(Rf_{small,*}L) ⟶ Rf_{K,*}(a_X⁻¹L)`, `AlgebraicGeometry.derivedSmallEtaleFineBaseChange`, is
an isomorphism. Its first factor is invertible by Stacks 0DDJ (2) from Stacks 095T
(`AlgebraicGeometry.isIso_bigSmallEtaleDerivedPlusBaseChange_of_cohomologyCommutesWithBaseChange`)
and its second by Stacks 0EZF (2) at `π_X⁻¹L`, whose cohomology sheaves `π_X⁻¹H^i(L)` lie in
`𝒜'_X`. -/
public theorem isIso_derivedSmallEtaleFineBaseChange
    (h095T : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f],
      Stacks.EtaleCohomology.CohomologyCommutesWithBaseChange.{u, 0} f)
    {X Y : E.Scheme} (f : X ⟶ Y) (hf : IsProper (E.inclusion.map f))
    (L : DerivedCategory.Plus (Sheaf (SmallEtale.topology E X.obj X.property) Ab.{u + 1}))
    (hL : ∀ i : ℤ, Stacks.Torsion.torsionSheafProperty.{u + 1}
      (SmallEtale.topology E X.obj X.property)
      ((DerivedCategory.Plus.homologyFunctor _ i).obj L)) :
    IsIso (derivedSmallEtaleFineBaseChange E K hle hsheaf hR hrefine f L) := by
  have := isIso_bigSmallEtaleDerivedPlusBaseChange_of_cohomologyCommutesWithBaseChange E f
    (bigEtaleOver_topology_eq_of_obj E X) (bigEtaleOver_topology_eq_of_obj E Y) h095T hf L hL
  exact IsIso.comp_isIso' inferInstance <| isIso_derivedComparisonBaseChange_app
    (properEtaleCohomologyComparison E K hle hsheaf hR hrefine) f
    (((SmallEtale.inclusion E X.obj X.property).sheafPullback Ab.{u + 1}
      (SmallEtale.topology E X.obj X.property) (E.topology.over X)).mapDerivedCategoryPlus.obj L)
    (weakSerre_homology_pullback E X L hL)

/-- **The base change map of part (2) of Stacks 0DE4**, for a finer precoverage `K`: for a
morphism `f : X ⟶ Y`, an abelian sheaf `F` on `X_étale` and `i : ℕ`, the base change map
`a_Y⁻¹(R^i f_{small,*}F) ⟶ R^i f_{K,*}(a_X⁻¹F)` on higher direct images. It is the degree `i`
cohomology of the derived base change map `AlgebraicGeometry.derivedSmallEtaleFineBaseChange` at
`F` placed in degree zero, read through the canonical identifications `R^i w(F) = H^i(R⁺w(F[0]))`
(`Stacks.DerivedIndexing.rightDerivedIso`), `H^i(π_Y⁻¹M) = π_Y⁻¹H^i(M)`,
`H^i(R⁺ε_Y⁻¹N) = ε_Y⁻¹H^i(N)` and `R⁺ε_X⁻¹(π_X⁻¹(F[0])) = (ε_X⁻¹π_X⁻¹F)[0]` for the exact functors
`π⁻¹` and `ε⁻¹`. -/
public def higherSmallEtaleFineBaseChange {X Y : E.Scheme} (f : X ⟶ Y)
    (F : Sheaf (SmallEtale.topology E X.obj X.property) Ab.{u + 1}) (i : ℕ) :
    (abelianComparisonPullback K E.precoverage Y).obj
        (((SmallEtale.inclusion E Y.obj Y.property).sheafPullback Ab.{u + 1}
          (SmallEtale.topology E Y.obj Y.property) (E.topology.over Y)).obj
          (((E.smallPushforward f Ab.{u + 1}).rightDerived i).obj F)) ⟶
      ((overPushforward K.toGrothendieck f).rightDerived i).obj
        ((abelianComparisonPullback K E.precoverage X).obj
          (((SmallEtale.inclusion E X.obj X.property).sheafPullback Ab.{u + 1}
            (SmallEtale.topology E X.obj X.property) (E.topology.over X)).obj F)) :=
  let πX := (SmallEtale.inclusion E X.obj X.property).sheafPullback Ab.{u + 1}
    (SmallEtale.topology E X.obj X.property) (E.topology.over X)
  let πY := (SmallEtale.inclusion E Y.obj Y.property).sheafPullback Ab.{u + 1}
    (SmallEtale.topology E Y.obj Y.property) (E.topology.over Y)
  let S := properEtaleCohomologyComparison E K hle hsheaf hR hrefine
  let εX := abelianComparisonPullback S.fineCoverage S.coarseCoverage X
  let εY := abelianComparisonPullback S.fineCoverage S.coarseCoverage Y
  haveI : PreservesFiniteColimits εX := abelianComparisonPullback_preservesFiniteColimits S X
  haveI : PreservesFiniteColimits εY := abelianComparisonPullback_preservesFiniteColimits S Y
  let wS := E.smallPushforward f Ab.{u + 1}
  let Ff := overPushforward K.toGrothendieck f
  let M := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  let H := DerivedCategory.Plus.homologyFunctor (Sheaf (K.toGrothendieck.over Y) Ab.{u + 1})
    (i : ℤ)
  (εY.mapIso (πY.mapIso ((Stacks.DerivedIndexing.rightDerivedIso wS i).app F)) ≪≫
      εY.mapIso ((πY.mapDerivedCategoryHomologyIso (i : ℤ)).app
        (DerivedCategory.Plus.ι.obj (wS.rightDerivedFunctorPlus.obj M))).symm ≪≫
      ((Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso εY (i : ℤ)).app
        (πY.mapDerivedCategoryPlus.obj (wS.rightDerivedFunctorPlus.obj M))).symm).hom ≫
    H.map (derivedSmallEtaleFineBaseChange E K hle hsheaf hR hrefine f M) ≫
    (H.mapIso (Ff.rightDerivedFunctorPlus.mapIso
      (εX.rightDerivedFunctorPlus.mapIso
          ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle πX 0).app F) ≪≫
        ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso εX 0).app
          (πX.obj F)).symm)) ≪≫
      ((Stacks.DerivedIndexing.rightDerivedIso Ff i).app (εX.obj (πX.obj F))).symm).hom

/-- **Part (2) of Stacks 0DE4**, for a finer precoverage `K`, granted Stacks 095T: for a proper
morphism `f : X ⟶ Y` and a torsion abelian sheaf `F` on `X_étale`, the base change map
`a_Y⁻¹(R^i f_{small,*}F) ⟶ R^i f_{K,*}(a_X⁻¹F)`,
`AlgebraicGeometry.higherSmallEtaleFineBaseChange`, is an isomorphism for every `i`: it is the
cohomology of the derived base change map of part (4) at `F` placed in degree zero, read through
isomorphisms. -/
public theorem isIso_higherSmallEtaleFineBaseChange
    (h095T : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f],
      Stacks.EtaleCohomology.CohomologyCommutesWithBaseChange.{u, 0} f)
    {X Y : E.Scheme} (f : X ⟶ Y) (hf : IsProper (E.inclusion.map f))
    (F : Sheaf (SmallEtale.topology E X.obj X.property) Ab.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty.{u + 1} (SmallEtale.topology E X.obj X.property) F)
    (i : ℕ) :
    IsIso (higherSmallEtaleFineBaseChange E K hle hsheaf hR hrefine f F i) := by
  have h := isIso_derivedSmallEtaleFineBaseChange E K hle hsheaf hR hrefine h095T f hf
    ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
    (torsionSheafProperty_homology_singleFunctor E X F hF)
  dsimp only [higherSmallEtaleFineBaseChange]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _)
    (@IsIso.comp_isIso _ _ _ _ _ _ _ (@Functor.map_isIso _ _ _ _ _ _ _ _ h) (Iso.isIso_hom _))

/-! ### Stacks 0DE5 for a finer precoverage -/

/-- **The map `L ⟶ Ra_{X,*}a_X⁻¹L` of Stacks 0DE5**, for a finer precoverage `K` and
`a_X = π_X ∘ ε_X`: the unit `L ⟶ Rπ_{X,*}π_X⁻¹L` of `π_X⁻¹ ⊣ π_{X,*}` on `D⁺`, followed by
`Rπ_{X,*}` of the derived unit `π_X⁻¹L ⟶ Rε_{X,*}ε_X⁻¹π_X⁻¹L` of the change of topology, and by
the identification `Rπ_{X,*} ∘ Rε_{X,*} = R(π_{X,*} ∘ ε_{X,*})`, the direct image `π_{X,*}` being
exact. The first map is the derived functor of the unit `id ⟶ π_{X,*}π_X⁻¹`, which is invertible
(Stacks 0DDI). -/
public def derivedSmallEtaleFineUnit (X : E.Scheme)
    (L : DerivedCategory.Plus (Sheaf (SmallEtale.topology E X.obj X.property) Ab.{u + 1})) :
    L ⟶ (abelianComparisonPushforward K E.precoverage hle X ⋙
        (SmallEtale.inclusion E X.obj X.property).sheafPushforwardContinuous Ab.{u + 1}
          (SmallEtale.topology E X.obj X.property) (E.topology.over X)).rightDerivedFunctorPlus.obj
      ((abelianComparisonPullback
          (properEtaleCohomologyComparison E K hle hsheaf hR hrefine).fineCoverage
          (properEtaleCohomologyComparison E K hle hsheaf hR hrefine).coarseCoverage
          X).mapDerivedCategoryPlus.obj
        (((SmallEtale.inclusion E X.obj X.property).sheafPullback Ab.{u + 1}
          (SmallEtale.topology E X.obj X.property) (E.topology.over X)).mapDerivedCategoryPlus.obj
            L)) :=
  let π := (SmallEtale.inclusion E X.obj X.property).sheafPullback Ab.{u + 1}
    (SmallEtale.topology E X.obj X.property) (E.topology.over X)
  let πs := (SmallEtale.inclusion E X.obj X.property).sheafPushforwardContinuous Ab.{u + 1}
    (SmallEtale.topology E X.obj X.property) (E.topology.over X)
  let η := ((SmallEtale.inclusion E X.obj X.property).sheafAdjunctionContinuous Ab.{u + 1}
    (SmallEtale.topology E X.obj X.property) (E.topology.over X)).unit
  haveI :=
    isIso_smallEtaleInclusion_sheafAdjunction_unit E X (bigEtaleOver_topology_eq_of_obj E X)
  haveI : PreservesFiniteLimits πs :=
    smallEtaleInclusion_sheafPushforward_over_preservesFiniteLimits E X
  haveI : PreservesFiniteColimits πs :=
    smallEtaleInclusion_sheafPushforward_over_preservesFiniteColimits E X
  haveI : πs.Additive := smallEtaleInclusion_sheafPushforward_over_additive E X
  haveI : PreservesFiniteLimits π :=
    smallEtaleInclusion_sheafPullback_over_preservesFiniteLimits E X
  haveI : PreservesFiniteColimits π :=
    smallEtaleInclusion_sheafPullback_over_preservesFiniteColimits E X
  haveI : π.Additive := smallEtaleInclusion_sheafPullback_over_additive E X
  ((Functor.rightDerivedFunctorPlusIdIsoOf (π ⋙ πs) (asIso η).symm).app L).inv ≫
    ((Functor.rightDerivedFunctorPlusCompIsoOfExact π πs _ (Iso.refl _)).app L).inv ≫
    πs.rightDerivedFunctorPlus.map
      ((Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus π).hom.app L ≫
        (derivedComparisonUnit (properEtaleCohomologyComparison E K hle hsheaf hR hrefine) X).app
          (π.mapDerivedCategoryPlus.obj L)) ≫
    ((Functor.rightDerivedFunctorPlusCompIsoOfExact
      (abelianComparisonPushforward K E.precoverage hle X) πs _ (Iso.refl _)).app _).hom

/-- **Stacks 0DE5**, for a finer precoverage `K`: for `L` in `D⁺(X_étale)` with torsion cohomology
sheaves, the map `L ⟶ Ra_{X,*}a_X⁻¹L` is an isomorphism. Its first factor is invertible by
Stacks 0DDI and its middle factor by part (3) of Stacks 0DE4,
`isIso_derivedComparisonUnit_app_smallEtaleInclusion`. -/
public theorem isIso_derivedSmallEtaleFineUnit (X : E.Scheme)
    (L : DerivedCategory.Plus (Sheaf (SmallEtale.topology E X.obj X.property) Ab.{u + 1}))
    (hL : ∀ i : ℤ, Stacks.Torsion.torsionSheafProperty.{u + 1}
      (SmallEtale.topology E X.obj X.property)
      ((DerivedCategory.Plus.homologyFunctor _ i).obj L)) :
    IsIso (derivedSmallEtaleFineUnit E K hle hsheaf hR hrefine X L) := by
  have h := isIso_derivedComparisonUnit_app_smallEtaleInclusion E K hle hsheaf hR hrefine X L hL
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_inv _)
    (@IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_inv _)
      (@IsIso.comp_isIso _ _ _ _ _ _ _
        (@Functor.map_isIso _ _ _ _ _ _ _ _
          (@IsIso.comp_isIso _ _ _ _ _ _ _ (NatIso.isIso_app_of_isIso _ _) h))
        (Iso.isIso_hom _)))

end AlgebraicGeometry

end
