module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperProjectionFormula.RingedBaseChangeComplex
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleProperBaseChangeUnboundedBoundedBelow

/-!
# Proper base change on the constant ringed topoi at bounded below torsion objects

For a proper morphism `f : X ⟶ Y`, a cartesian square `g' ≫ f = f' ≫ g` and an object
`E ∈ D(X_étale, Λ)` of sheaves of `Λ`-modules which is bounded below with torsion cohomology
sheaves, the base change map of the 2-commutative square of constant ringed topoi is invertible
at the transported object `Φ E`.

This is the étale statement
`Stacks.EtaleCohomology.isIso_etaleModuleDerivedBaseChangeUnbounded_app_of_isGE_of_isProper`
carried to the ringed topoi as in
`Stacks.EtaleCohomology.isIso_squareBaseChangeMap_etaleRingedToposHomSquareTwoIso_of_isProper`:
at the transport `Φ J` of a K-injective representative `J` of `E` the ringed base change map is
computed by the ringed composite of
`Stacks.EtaleCohomology.isIso_squareBaseChangeMap_iff_of_isKInjective`, which is invertible by
`Stacks.EtaleCohomology.isIso_etaleRingedBaseChangeUnitComposite_of_isIso` because the étale base
change map is invertible at `Ψ Φ J ≅ E`.

## Main results

* `Stacks.EtaleCohomology.isIso_squareBaseChangeMap_of_isGE_of_isProper`.
-/

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

/-- **Proper base change on the constant ringed topoi at a bounded below object with torsion
cohomology.** For `f` proper, a cartesian square `g' ≫ f = f' ≫ g` and `E ∈ D(X_étale, Λ)`
bounded below with torsion cohomology sheaves, the base change map
`Lg^* Rf_* ⟶ Rf'_* L(g')^*` of the square of constant ringed topoi is invertible at `Φ E`. -/
theorem isIso_squareBaseChangeMap_of_isGE_of_isProper
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f] {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    (sq : IsPullback g' f' f g) (E : DerivedCategory (EtaleModules.{u, 0} Λ X)) (a : ℤ)
    (hE : E.IsGE a)
    (hT : ∀ n, IsTorsionEtaleModule.{u, 0} Λ X ((DerivedCategory.homologyFunctor _ n).obj E)) :
    IsIso (squareBaseChangeMap.{u + 1} (etaleRingedToposHomSquareTwoIso.{u, 0} Λ f g f' g' sq.w)
      ((etaleDerivedEquivalence.{u, 0} Λ X).functor.obj E)) := by
  let := HasDerivedCategory.standard (EtaleRingedModules.{u, 0} Λ X)
  obtain ⟨J, hJ, ⟨e⟩⟩ := Stacks.Cohomology.UnboundedComplexes.exists_isKInjective_iso
    (A := EtaleModules.{u, 0} Λ X) DerivedCategory.Qh E
  let e' : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      (((etaleModulesEquivalence.{u, 0} Λ X).functor.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J)) ≅ (etaleDerivedEquivalence.{u, 0} Λ X).functor.obj E :=
    (etaleDerivedEquivalenceFactorsIso.{u, 0} Λ (X := X)).app J ≪≫
    (etaleDerivedEquivalence.{u, 0} Λ X).functor.mapIso
      ((DerivedCategory.quotientCompQhIso _).symm.app J ≪≫ e)
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
  let eV : E ≅ DerivedCategory.Q.obj
      (((etaleRingedForget.{u, 0} Λ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((etaleModulesEquivalence.{u, 0} Λ X).functor.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj J)) :=
    e.symm ≪≫ (DerivedCategory.quotientCompQhIso _).app J ≪≫
      DerivedCategory.Q.mapIso
        (((etaleModulesEquivalence.{u, 0} Λ X).mapHomologicalComplex
          (ComplexShape.up ℤ)).unitIso.app J)
  have hb := (NatTrans.isIso_app_iff_of_iso _ eV).1
    (isIso_etaleModuleDerivedBaseChangeUnbounded_app_of_isGE_of_isProper Λ f sq E a hE hT)
  have h₀ := (isIso_squareBaseChangeMap_iff_of_isKInjective Λ f g f' g' sq.w _ hI).2
    (isIso_etaleRingedBaseChangeUnitComposite_of_isIso Λ f g f' g' sq.w _
      (isIso_complexMap_comp_unit_of_isKInjective Λ f g f' g' sq.w _ hJ' hb))
  have hn := Stacks.CategoryTheory.BaseChange.map_naturality
    (derivedAdjunction (etaleRingedToposHom.{u, 0} Λ f))
    (derivedAdjunction (etaleRingedToposHom.{u, 0} Λ f'))
    (RingedToposHom.TwoIso.derivedPullbackSquareIso.{u + 1}
      (etaleRingedToposHomSquareTwoIso.{u, 0} Λ f g f' g' sq.w)) (Iso.refl _) e'.hom
  have h₁ : IsIso ((derivedPullback (etaleRingedToposHom.{u, 0} Λ g)).map
      ((derivedPushforward (etaleRingedToposHom.{u, 0} Λ f)).map e'.hom) ≫
    Stacks.CategoryTheory.BaseChange.map
      (derivedAdjunction (etaleRingedToposHom.{u, 0} Λ f))
      (derivedAdjunction (etaleRingedToposHom.{u, 0} Λ f'))
      (RingedToposHom.TwoIso.derivedPullbackSquareIso.{u + 1}
        (etaleRingedToposHomSquareTwoIso.{u, 0} Λ f g f' g' sq.w)) (Iso.refl _)
      ((etaleDerivedEquivalence.{u, 0} Λ X).functor.obj E)) := by
    rw [hn]
    exact IsIso.comp_isIso' h₀ inferInstance
  exact (isIso_comp_left_iff _ _).1 h₁

end Stacks.EtaleCohomology

end
