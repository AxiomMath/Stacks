module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSheafLevelCechComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.SheafLevelComplexAugmentation

/-!
# The augmentation of the sheaf-level Čech complex at the small étale site

Let `S` be a scheme of a big étale site, let `X` be an object of its small étale site and let
`{U_i → X}` be a family of morphisms of that site.  This file instantiates the augmentation of
`Stacks.CechSite.SheafLevel.augmentationHom` at `(X_étale, 𝒪_X)`: for an `𝒪`-module `ℱ`, a
morphism of cochain complexes of `𝒪`-modules

`ℱ[0] ⟶ AlgebraicGeometry.SmallEtale.sheafLevelCechComplex B S hS E ℱ`

out of the complex concentrated in degree `0`, natural in `ℱ`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.sheafLevelCechAugmentation`: the augmentation, as a morphism of
  cochain complexes.
* `AlgebraicGeometry.SmallEtale.sheafLevelCechAugmentationNatTrans`: the same, natural in the
  `𝒪`-module.

## Implementation notes

The general construction asks for `CategoryTheory.Limits.HasZeroObject` on the `𝒪`-modules,
which `CategoryTheory.HomologicalComplex.single` needs.  It is supplied here by
`CategoryTheory.SheafOfModules.instAbelian`, raised to a local instance at the priority
documented in `AlgebraicGeometry.SmallEtale.enoughInjectives_smallEtaleModules`: with the
module-universe-`max u v r w` instances in the import closure, instance search for `Abelian` on
the modules at module universe `u` commits to them and then fails on the universe constraint.
The raise is `local`, so no global instance is declared.

**This is the augmentation; the quasi-isomorphism statement is elsewhere.**  Nothing in *this*
file asserts the augmentation to be a quasi-isomorphism, because that needs the family to cover
the final object, which the definitions below do not require.  It is
`AlgebraicGeometry.SmallEtale.quasiIso_sheafLevelCechAugmentation` in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleSheafLevelCechExactness.lean`,
and it is what supplies the `[QuasiIso ε]` hypothesis of
`AlgebraicGeometry.SmallEtale.rightDerivedPushforwardIsoHomologyOfAcyclic`.

## References

* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Products of `𝒪`-modules on the small étale site, supplied directly: instance search for
them times out under Lean v4.35.0. -/
local instance : HasProducts.{u} (SheafOfModules.{u} (structureSheaf B S hS)) :=
  fun J => SheafOfModules.hasLimitsOfShape (Discrete J) _

/-- **The augmentation of the sheaf-level Čech complex of a family of morphisms of the small
étale site**: for an `𝒪`-module `ℱ`, the morphism of cochain complexes of `𝒪`-modules from the
complex concentrated in degree `0` at `ℱ` to the sheaf-level Čech complex, whose degree-zero
component sends `ℱ` to the product over `i` of the direct image of its restriction to `U_i`.

The family is not required to be covering, nor finite.  Being a quasi-isomorphism — that is, a
resolution — is not asserted. -/
noncomputable abbrev sheafLevelCechAugmentation {X : SmallEtale B S hS}
    (E : PreZeroHypercover.{u} X) (F : SheafOfModules.{u} (structureSheaf B S hS)) :
    (CochainComplex.single₀ (SheafOfModules.{u} (structureSheaf B S hS))).obj F ⟶
      (sheafLevelCechComplex B S hS E).obj F :=
  Stacks.CechSite.SheafLevel.augmentationHom (structureSheaf B S hS) E F

/-- **The augmentation of the sheaf-level Čech complex at the small étale site, naturally in
the `𝒪`-module.** -/
noncomputable abbrev sheafLevelCechAugmentationNatTrans {X : SmallEtale B S hS}
    (E : PreZeroHypercover.{u} X) :
    CochainComplex.single₀ (SheafOfModules.{u} (structureSheaf B S hS)) ⟶
      sheafLevelCechComplex B S hS E :=
  Stacks.CechSite.SheafLevel.augmentationNatTrans (structureSheaf B S hS) E

end AlgebraicGeometry.SmallEtale

end
