module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackEtale
public import StacksFrontier.CategoryTheory.Localization.AbsoluteLeftDerivedAdjunction
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRingIso
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory

/-!
# Étale base change for the canonical derived direct image of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `g : Y' ⟶ Y` an étale morphism, with
`X' = Y' ×_Y X`, projections `i : X' ⟶ X` and `f' : X' ⟶ Y'`. The derived direct image
`Rf_* = AlgebraicGeometry.Space.derivedModulePushforward f` commutes with restriction along `g`:
`(Rf_* E)|_{Y'} ≅ Rf'_*(E|_{X'})`, naturally in `E`. This is [Stacks, Tag 08GE], which the library
proves for arbitrary right derived functors of the direct image `modulePushforward`
(`AlgebraicGeometry.Space.derivedModulePushforwardEtaleRestrictIso`); this file reads it off for
the canonical `Rf_*`, a right derived functor of `modulePushforward` by
`AlgebraicGeometry.Space.isRightDerivedFunctor_derivedModulePushforward`.

As a consequence, for an étale monomorphism `j : U ⟶ X` (an open immersion) the counit
`(Rj_* E)|_U ⟶ E` of the derived adjunction `(-)|_U ⊣ Rj_*` is an isomorphism.

## Main results

* `AlgebraicGeometry.Space.derivedPushforwardEtaleBaseChangeIso`: the natural isomorphism
  `Rf_* ⋙ (-)|_{Y'} ≅ (-)|_{X'} ⋙ Rf'_*` of functors `D(𝒪_X) ⥤ D(𝒪_{Y'})`.
* `AlgebraicGeometry.Space.derivedModulePushforwardIdIso`: `R(𝟙_X)_* ≅ 𝟭`.
* `AlgebraicGeometry.Space.isIso_etaleDerivedModuleAdjunction_counit_of_mono`: for an étale
  monomorphism the counit of `(-)|_U ⊣ Rj_*` is an isomorphism.

## Implementation notes

Restriction along an étale morphism on derived categories is the functor
`(etaleModulePullback f hf).mapDerivedCategory` induced by the exact restriction functor; it is
the left adjoint of `Rf_*` by `AlgebraicGeometry.Space.etaleDerivedModuleAdjunction`. No new
registration of [Stacks, Tag 08GE] is made.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Square

variable {X Y X' Y' : AlgebraicSpaces B S hS} {i : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y}
  {g : Y' ⟶ Y}

/-- **Étale base change for the canonical derived direct image** ([Stacks, Tag 08GE], read off
`AlgebraicGeometry.Space.derivedModulePushforwardEtaleRestrictIso`). For a cartesian square
`X' = Y' ×_Y X` with `g : Y' ⟶ Y` étale, `(Rf_* E)|_{Y'} ≅ Rf'_*(E|_{X'})`, naturally in `E`. -/
def derivedPushforwardEtaleBaseChangeIso (sq : IsPullback i f' f g) (hg : IsEtale B S hS g.hom) :
    derivedModulePushforward B S hS f ⋙
        (etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory ≅
      (etaleModulePullback.{u, u} B S hS i
          (isEtale_of_isPullback B S hS f' i g f sq.flip hg)).mapDerivedCategory ⋙
        derivedModulePushforward B S hS f' :=
  haveI := Functor.isRightDerivedFunctor_mapDerivedCategory_of_exact
    (etaleModulePullback.{u, u} B S hS i (isEtale_of_isPullback B S hS f' i g f sq.flip hg))
  haveI := Functor.isRightDerivedFunctor_mapDerivedCategory_of_exact
    (etaleModulePullback.{u, u} B S hS g hg)
  derivedModulePushforwardEtaleRestrictIso B S hS sq hg
    (etaleModuleLowerShriekAdjunction B S hS i (isEtale_of_isPullback B S hS f' i g f sq.flip hg))
    (derivedModulePushforward B S hS f) (derivedModulePushforward B S hS f')
    _ _ (derivedModulePushforwardUnit B S hS f) (derivedModulePushforwardUnit B S hS f')
    (etaleModulePullback.{u, u} B S hS i
      (isEtale_of_isPullback B S hS f' i g f sq.flip hg)).mapDerivedCategoryFactorsh.inv
    (etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategoryFactorsh.inv

end Square

/-- Restriction along the identity, on derived categories, is the identity. -/
def etaleRestrictIdIso (X : AlgebraicSpaces B S hS) (h : IsEtale B S hS (𝟙 X : X ⟶ X).hom) :
    (etaleModulePullback.{u, u} B S hS (𝟙 X) h).mapDerivedCategory ≅
      𝟭 (DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :=
  Dualizing.mapDerivedCategoryNatIso _ _ (etaleModulePullbackIdIso B S hS h) ≪≫
    StacksDraft.DerivedRingIso.mapDerivedCategoryIdIso

/-- **The derived direct image along the identity is the identity**: `R(𝟙_X)_*` is right adjoint
to restriction along `𝟙_X`, which is the identity. -/
def derivedModulePushforwardIdIso (X : AlgebraicSpaces B S hS) :
    derivedModulePushforward B S hS (𝟙 X) ≅ 𝟭 (DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :=
  have h : IsEtale B S hS (𝟙 X : X ⟶ X).hom := isEtale_id B S hS X.1
  (((etaleDerivedModuleAdjunction B S hS (𝟙 X) h).ofNatIsoLeft
    (etaleRestrictIdIso B S hS X h)).rightAdjointUniq Adjunction.id)

/-- **The counit of `(-)|_U ⊣ Rj_*` is invertible for an étale monomorphism `j`**, that is for
an open immersion: base change along the cartesian square `U ×_X U = U` identifies
`(Rj_* E)|_U` with `E`. -/
theorem isIso_etaleDerivedModuleAdjunction_counit_of_mono {U X : AlgebraicSpaces B S hS}
    (j : U ⟶ X) (hj : IsEtale B S hS j.hom) [Mono j] :
    IsIso (etaleDerivedModuleAdjunction B S hS j hj).counit := by
  have sq : IsPullback (𝟙 U) (𝟙 U) j j := IsPullback.of_horiz_isIso_mono ⟨rfl⟩
  exact (etaleDerivedModuleAdjunction B S hS j hj).isIso_counit_of_iso
    (derivedPushforwardEtaleBaseChangeIso B S hS sq hj ≪≫
      Functor.isoWhiskerRight (etaleRestrictIdIso B S hS U _) _ ≪≫ Functor.leftUnitor _ ≪≫
      derivedModulePushforwardIdIso B S hS U)

end AlgebraicGeometry.Space

end
