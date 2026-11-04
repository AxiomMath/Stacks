module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafModulesGrothendieck
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.HigherDirectImages
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# The derived direct image of modules on a ringed space

For a morphism `f : X ⟶ Y` of ringed spaces, degreewise pushforward of complexes of
`𝒪_X`-modules has an everywhere-defined right derived functor on the unbounded derived category,
because every complex of `𝒪_X`-modules admits a K-injective resolution. This file constructs
that functor, `Rf_*`.

## Main definitions

* `AlgebraicGeometry.RingedSpace.pushforwardToDerivedCategory`: degreewise pushforward on the
  homotopy category, followed by localization to the derived category of the target.
* `AlgebraicGeometry.RingedSpace.derivedPushforward`: the derived direct image `Rf_*`.
* `AlgebraicGeometry.RingedSpace.derivedPushforwardUnit`: its canonical comparison with
  degreewise pushforward.

## Main results

* `AlgebraicGeometry.RingedSpace.pushforwardToDerivedCategory_hasRightDerivedFunctor`: the right
  derived functor exists, pointwise, at every object.
* `AlgebraicGeometry.RingedSpace.isIso_derivedPushforwardUnit_app_of_isKInjective`: on a
  K-injective complex the comparison is an isomorphism, so `Rf_*` is computed by pushing forward
  a K-injective resolution degreewise.

## Implementation notes

Both results come from one application of
`Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective`, whose
hypothesis is supplied by the functorial K-injective resolutions of
`Stacks.Injectives.kInjectiveResolutionFunctor`: its first conclusion is the existence of the
derived functor and its second is the computation on K-injective complexes.

The category of `𝒪_X`-modules is written as `SheafOfModules (structureSheafRing X)`, the form the
degreewise pushforward is constructed in. That is the same category as
`StrictlyPerfect.OXMod X`, the form the definitions of perfectness and pseudo-coherence on a
ringed space are stated in, because `structureSheafRing` and
`StrictlyPerfect.structureSheafOfRings` are definitionally equal; so predicates stated in the
latter form apply to the values of `Rf_*` with no comparison in between.

The universe of the derived category is an instance argument on both sides rather than fixed to
the standard choice.

## References

* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public noncomputable section

open CategoryTheory RingedSpaceModuleAdjunction

namespace AlgebraicGeometry.RingedSpace

universe u w

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- Degreewise pushforward of complexes of `𝒪_X`-modules, followed by localization to the
derived category of `𝒪_Y`-modules. Its right derived functor is the derived direct image. -/
public def pushforwardToDerivedCategory
    [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing Y))] :
    HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) :=
  (modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- Every complex of `𝒪_X`-modules admits a K-injective resolution, by the functorial
K-injective resolutions of `Stacks.Injectives.kInjectiveResolutionFunctor`. -/
private theorem exists_quasiIso_isKInjective_oxMod (X : RingedSpace.{u, u}) :
    ∀ K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ,
      ∃ (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (g : K ⟶ I),
        I.IsKInjective ∧ QuasiIso g := fun K =>
  ⟨(Stacks.Injectives.kInjectiveResolutionFunctor _).obj K,
    (Stacks.Injectives.kInjectiveResolutionInclusion _).app K, inferInstance, inferInstance⟩

/-- Degreewise pushforward of complexes of `𝒪_X`-modules has a pointwise right derived functor
at every object, K-injective resolutions existing. -/
public instance pushforwardToDerivedCategory_hasRightDerivedFunctor
    [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing Y))] :
    (pushforwardToDerivedCategory f).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)) := by
  have := (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
    u, w, u, u + 1, u + 1, u + 1} (pushforwardToDerivedCategory f)
    (exists_quasiIso_isKInjective_oxMod X)).1
  infer_instance

/-- The derived direct image `Rf_* : D(𝒪_X) ⥤ D(𝒪_Y)`, the total right derived functor of
degreewise pushforward along the localization of the homotopy category at
quasi-isomorphisms. -/
public def derivedPushforward
    [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing Y))] :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) :=
  (pushforwardToDerivedCategory f).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))

/-- The canonical comparison from degreewise pushforward to the derived direct image. -/
public def derivedPushforwardUnit
    [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing Y))] :
    pushforwardToDerivedCategory f ⟶ DerivedCategory.Qh ⋙ derivedPushforward f :=
  (pushforwardToDerivedCategory f).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))

/-- The derived direct image, with its canonical comparison, is a right derived functor of
degreewise pushforward. -/
public instance derivedPushforward_isRightDerivedFunctor
    [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing Y))] :
    (derivedPushforward f).IsRightDerivedFunctor (derivedPushforwardUnit f)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :=
  inferInstanceAs
    (((pushforwardToDerivedCategory f).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X))
          (ComplexShape.up ℤ))).IsRightDerivedFunctor
      ((pushforwardToDerivedCategory f).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X))
          (ComplexShape.up ℤ))) _)

/-- On a K-injective complex of `𝒪_X`-modules the comparison from the degreewise pushforward to
the derived direct image is an isomorphism: the derived direct image is computed by pushing
forward a K-injective resolution degreewise. -/
public theorem isIso_derivedPushforwardUnit_app_of_isKInjective
    [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing Y))]
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (hI : I.IsKInjective) :
    IsIso ((derivedPushforwardUnit f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    (pushforwardToDerivedCategory f) (exists_quasiIso_isKInjective_oxMod X)).2
    DerivedCategory.Qh _ (derivedPushforwardUnit f) I hI

end AlgebraicGeometry.RingedSpace

end
