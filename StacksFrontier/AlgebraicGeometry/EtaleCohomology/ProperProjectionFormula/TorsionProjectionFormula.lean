module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperProjectionFormula.RingedBaseChangeComplex
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperProjectionFormula.TorsionPointProjectionFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperProjectionFormula.GeometricPointConservativity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperProjectionFormula.ProjectionMapComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleProperBaseChangeUnbounded
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.KInjectiveRestrictionAlongOverMapEssentiallySmall
import StacksCore.Tactic.StacksAttribute

/-!
# The projection formula for a proper morphism, torsion coefficients (Stacks 0F0G)

Let `f : X ⟶ Y` be a proper morphism of schemes, `Λ` a torsion ring, `E ∈ D(X_étale, Λ)` and
`K ∈ D(Y_étale, Λ)`. [Stacks, Tag 0F0G] asserts that the canonical map of Cohomology on Sites,
Section 21.50 ([Stacks, Tag 0943])

`Rf_*E ⊗^L_Λ K ⟶ Rf_*(E ⊗^L_Λ f^{-1}K)`

is an isomorphism in `D(Y_étale, Λ)`. All complexes are unbounded.

## The proof

The source's. The map is checked on stalks at geometric points `ȳ : Spec Ω ⟶ Y`: derived pullbacks
to geometric points detect isomorphisms
(`Stacks.EtaleCohomology.isIso_of_forall_isIso_etaleRingedDerivedPullback_map`, from
[Stacks, Tag 03PU]). For the cartesian square of `f` and `ȳ`, the pullback of the map along `ȳ`
is identified with the map for the base change `f' : X_ȳ ⟶ Spec Ω`, through the base change map
and the comparisons of [Stacks, Tag 07A4] ([Stacks, Tag 0E48],
`Stacks.Cohomology.ProjectionFormulaOfToposHom.isIso_derivedPullback_map_projectionFormulaMap`).
The base change map is invertible by proper base change ([Stacks, Tag 0F0C],
`Stacks.EtaleCohomology.isIso_etaleModuleDerivedBaseChangeUnbounded_app_of_isProper`), carried from
sheaves of `Λ`-modules to the constant ringed topoi by
`Stacks.EtaleCohomology.isIso_etaleRingedBaseChangeUnitComposite_of_isIso`. This reduces the claim
to `Y` the spectrum of a separably closed field, where it is
`Stacks.EtaleCohomology.isIso_projectionFormulaMap_of_isProper_of_isSepClosed`: the computation of
[Stacks, Tag 0F12] for the proper `Ω`-scheme `X_ȳ`, whose cohomological dimension is finite by
[Stacks, Tag 095U].

## Conventions

`D(X_étale, Λ)` is `DerivedCategory (Stacks.EtaleCohomology.EtaleModules Λ X)` and the map is
`Stacks.EtaleCohomology.etalePushforwardProjectionMap`, the map of [Stacks, Tag 0943] built from
`f^{-1} ⊣ Rf_*` and the comparison of [Stacks, Tag 07A4]. The same statement is proved first on the
derived categories of modules over the constant ringed sites `(X_étale, Λ̲)`, for the map
`Stacks.Cohomology.ProjectionFormulaOfToposHom.projectionFormulaMap` of [Stacks, Tag 0B56] of the
morphism of ringed topoi `Stacks.EtaleCohomology.etaleRingedToposHom`, and transported along
`Stacks.EtaleCohomology.isIso_etalePushforwardProjectionMap_iff`. A torsion ring is a ring whose
additive group is torsion, `IsAddTorsion Λ`.

## Main results

* `Stacks.EtaleCohomology.isIso_squareBaseChangeMap_etaleRingedToposHomSquareTwoIso_of_isProper`:
  proper base change on the constant ringed topoi, unbounded, for a torsion ring.
* `Stacks.EtaleCohomology.isIso_projectionFormulaMap_etaleRingedToposHom_of_isProper`: the
  projection formula on the constant ringed topoi.
* `Stacks.EtaleCohomology.isIso_etalePushforwardProjectionMap_of_isProper`: **[Stacks, Tag 0F0G]**.

## References

* [Stacks Project, Tag 0F0G](https://stacks.math.columbia.edu/tag/0F0G)
* [Stacks Project, Tag 0943](https://stacks.math.columbia.edu/tag/0943)
* [Stacks Project, Tag 0F0C](https://stacks.math.columbia.edu/tag/0F0C)
* [Stacks Project, Tag 0F12](https://stacks.math.columbia.edu/tag/0F12)
* [Stacks Project, Tag 095U](https://stacks.math.columbia.edu/tag/095U)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom Stacks.Cohomology.DerivedPushforward
open Stacks.Cohomology.ProjectionFormulaOfToposHom

attribute [local instance] HasDerivedCategory.standard
attribute [local instance high]
  Stacks.EtaleCohomology.instHasSheafifyCRingedToposEtaleRingedSiteJType
attribute [local instance]
  Stacks.EtaleCohomology.etaleRingedPullbackOnHomotopy_hasLeftDerivedFunctor

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [CommRing Λ]

/-- **Proper base change on the constant ringed topoi, for a torsion ring.** For `f` proper, a
cartesian square `g' ≫ f = f' ≫ g` and `Λ` torsion, the base change map
`Lg^* Rf_* ⟶ Rf'_* L(g')^*` of the 2-commutative square of constant ringed topoi is invertible on
the unbounded derived category: it is the base change map on sheaves of `Λ`-modules
([Stacks, Tag 0F0C]) read through the identifications of `Λ̲`-modules with `Λ`-modules. -/
@[sga "4 XVII 5.2.7" "special case"]
theorem isIso_squareBaseChangeMap_etaleRingedToposHomSquareTwoIso_of_isProper
    (hΛ : IsAddTorsion Λ) {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'} (sq : IsPullback g' f' f g)
    (E : DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (etaleRingedSite.{u, 0} Λ X)).O))) :
    IsIso (squareBaseChangeMap.{u + 1}
      (etaleRingedToposHomSquareTwoIso.{u, 0} Λ f g f' g' sq.w) E) := by
  refine isIso_squareBaseChangeMap_of_isKInjective Λ f g f' g' sq.w (fun J hJ => ?_) E
  have hI : CochainComplex.IsKInjective
      (((etaleModulesEquivalence.{u, 0} Λ X).functor.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J) :=
    have := hJ
    Stacks.Injectives.isKInjective_mapHomologicalComplex_of_isEquivalence _ J
  have hJ' : CochainComplex.IsKInjective
      (((etaleRingedForget.{u, 0} Λ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((etaleModulesEquivalence.{u, 0} Λ X).functor.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj J)) :=
    have := hI
    Stacks.Injectives.isKInjective_mapHomologicalComplex_of_isEquivalence _ _
  exact (isIso_squareBaseChangeMap_iff_of_isKInjective Λ f g f' g' sq.w _ hI).2
    (isIso_etaleRingedBaseChangeUnitComposite_of_isIso Λ f g f' g' sq.w _
      (isIso_complexMap_comp_unit_of_isKInjective Λ f g f' g' sq.w _ hJ'
        (isIso_etaleModuleDerivedBaseChangeUnbounded_app_of_isProper Λ
          (exists_natCast_eq_zero_of_isTorsion Λ hΛ) f sq _)))

/-- **The projection formula on the constant ringed topoi, for a proper morphism and a torsion
ring.** For `f : X ⟶ Y` proper and `Λ` torsion, the map of [Stacks, Tag 0B56]
`Rf_*E ⊗^L_Λ K ⟶ Rf_*(E ⊗^L_Λ Lf^*K)` along the morphism of constant ringed topoi
`(X_étale, Λ̲) ⟶ (Y_étale, Λ̲)` is invertible for all unbounded `E` and `K`. -/
theorem isIso_projectionFormulaMap_etaleRingedToposHom_of_isProper (hΛ : IsAddTorsion Λ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (E : DerivedCategory (EtaleRingedModules.{u, 0} Λ X))
    (K : DerivedCategory (EtaleRingedModules.{u, 0} Λ Y)) :
    IsIso (projectionFormulaMap (etaleRingedToposHom.{u, 0} Λ f) E K) := by
  let := HasDerivedCategory.standard (EtaleRingedModules.{u, 0} Λ X)
  let := HasDerivedCategory.standard (EtaleRingedModules.{u, 0} Λ Y)
  refine isIso_of_forall_isIso_etaleRingedDerivedPullback_map Λ _ fun y => ?_
  have : IsProper (pullback.snd f y.hom) := inferInstance
  exact isIso_derivedPullback_map_projectionFormulaMap.{u + 1}
    (etaleRingedToposHomSquareTwoIso.{u, 0} Λ f y.hom (pullback.snd f y.hom) (pullback.fst f y.hom)
      pullback.condition)
    (isIso_squareBaseChangeMap_etaleRingedToposHomSquareTwoIso_of_isProper Λ hΛ f
      (IsPullback.of_hasPullback f y.hom)) _ _
    (isIso_projectionFormulaMap_of_isProper_of_isSepClosed Λ hΛ y.residueField
      (pullback.snd f y.hom) _ _)

/-- **[Stacks, Tag 0F0G].** Let `f : X ⟶ Y` be a proper morphism of schemes and `Λ` a torsion ring.
For `E ∈ D(X_étale, Λ)` and `K ∈ D(Y_étale, Λ)`, unbounded, the canonical map of
[Stacks, Tag 0943]
`Rf_*E ⊗^L_Λ K ⟶ Rf_*(E ⊗^L_Λ f^{-1}K)`
is an isomorphism in `D(Y_étale, Λ)`. -/
@[stacks 0F0G]
theorem isIso_etalePushforwardProjectionMap_of_isProper (hΛ : IsAddTorsion Λ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (E : DerivedCategory (EtaleModules.{u, 0} Λ X))
    (K : DerivedCategory (EtaleModules.{u, 0} Λ Y)) :
    IsIso (etalePushforwardProjectionMap.{u, 0} Λ f E K) := by
  rw [isIso_etalePushforwardProjectionMap_iff]
  exact isIso_projectionFormulaMap_etaleRingedToposHom_of_isProper Λ hΛ f _ _

end Stacks.EtaleCohomology

end
