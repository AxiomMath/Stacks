module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardEtaleRestrictionNoShriekData
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedExtLeray

/-!
# Étale base change for the derived direct image `spaceDerivedPushforward`

Let `f : X ⟶ Y` be a morphism of algebraic spaces, `g : Y' ⟶ Y` étale, and `X' = Y' ×_Y X` with
projections `i : X' ⟶ X` and `f' : X' ⟶ Y'`.  Then `Lg^* Rf_* ≅ Rf'_* Li^*`, for the derived
direct image `AlgebraicGeometry.Space.spaceDerivedPushforward`.  This is Stacks 08GE
(`AlgebraicGeometry.Space.derivedModulePushforwardEtaleRestrictIsoOfIsEtale`, for arbitrary
right derived functors of the direct image) specialised to `spaceDerivedPushforward`.

## Main definitions

* `AlgebraicGeometry.Space.spaceDerivedPushforwardEtaleBaseChangeIso`: the isomorphism with the
  étale restrictions `(etaleModulePullback _ _).mapDerivedCategory`.
* `AlgebraicGeometry.Space.spaceDerivedPushforwardPullBaseChangeIso`: the same with the derived
  pullbacks of `AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`.

## References

* [Stacks Project, Tag 08GE](https://stacks.math.columbia.edu/tag/08GE)
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

variable {X Y X' Y' : AlgebraicSpaces B S hS} {i : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y}
  {g : Y' ⟶ Y}

/-- **Étale base change for `AlgebraicGeometry.Space.spaceDerivedPushforward`**
([Stacks, Tag 08GE]).  For a cartesian square `X' = Y' ×_Y X` with `g : Y' ⟶ Y` étale,
`(Rf_* E)|_{Y'} ≅ Rf'_*(E|_{X'})` naturally in `E`, the restrictions being the exact étale
restriction functors on derived categories. -/
def spaceDerivedPushforwardEtaleBaseChangeIso (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    spaceDerivedPushforward B S hS f ⋙ (etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory ≅
      (etaleModulePullback.{u, u} B S hS i
          (isEtale_of_isPullback B S hS f' i g f sq.flip hg)).mapDerivedCategory ⋙
        spaceDerivedPushforward B S hS f' :=
  haveI := Functor.isRightDerivedFunctor_mapDerivedCategory_of_exact
    (etaleModulePullback.{u, u} B S hS i (isEtale_of_isPullback B S hS f' i g f sq.flip hg))
  haveI := Functor.isRightDerivedFunctor_mapDerivedCategory_of_exact
    (etaleModulePullback.{u, u} B S hS g hg)
  derivedModulePushforwardEtaleRestrictIsoOfIsEtale B S hS sq hg
    (spaceDerivedPushforward B S hS f) (spaceDerivedPushforward B S hS f') _ _
    (spaceDerivedPushforwardUnit B S hS f) (spaceDerivedPushforwardUnit B S hS f')
    (etaleModulePullback.{u, u} B S hS i
      (isEtale_of_isPullback B S hS f' i g f sq.flip hg)).mapDerivedCategoryFactorsh.inv
    (etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategoryFactorsh.inv

/-- **Étale base change for `AlgebraicGeometry.Space.spaceDerivedPushforward`, with the derived
pullback.**  For a cartesian square `X' = Y' ×_Y X` with `g : Y' ⟶ Y` étale,
`Lg^* Rf_* ≅ Rf'_* Li^*` as functors `D(𝒪_X) ⥤ D(𝒪_{Y'})`, the derived pullbacks being those of
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`. -/
def spaceDerivedPushforwardPullBaseChangeIso (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    spaceDerivedPushforward B S hS f ⋙ (smallEtaleDerivedPullbackData B S hS).pull g ≅
      (smallEtaleDerivedPullbackData B S hS).pull i ⋙ spaceDerivedPushforward B S hS f' :=
  Functor.isoWhiskerLeft _ (smallEtaleDerivedModulePullbackIsoEtale B S hS g hg) ≪≫
    spaceDerivedPushforwardEtaleBaseChangeIso B S hS sq hg ≪≫
    Functor.isoWhiskerRight (smallEtaleDerivedModulePullbackIsoEtale B S hS i
      (isEtale_of_isPullback B S hS f' i g f sq.flip hg)).symm _

end AlgebraicGeometry.Space
