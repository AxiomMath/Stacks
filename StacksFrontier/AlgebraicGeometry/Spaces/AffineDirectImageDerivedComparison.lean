module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishingUnconditional

/-!
# The direct image along an affine morphism of algebraic spaces is its own derived direct image

Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over a scheme `S` of a big fppf site
`B` and let `F` be a quasi-coherent `𝒪_X`-module. The first assertion of Stacks 07U8 is

```
f_*F ≅ Rf_*F,
```

that is, the canonical map from the direct image `f_*F`, placed in degree zero, to the derived
direct image `Rf_*F` is an isomorphism. This file proves it with no hypothesis beyond the
source's.

## Main results

* `AlgebraicGeometry.Space.isIso_rightDerivedFunctorPlusUnit_app_modulePushforward_isAffineHom`:
  **the comparison assertion of Stacks 07U8.**

## Proof

The source reduces, by Equation 69.3.0.1 (Stacks 071Z), to an affine morphism of schemes,
where it is Stacks 02KG. In this library that reduction has already been carried out once, in
the vanishing of the higher direct images along an affine morphism of algebraic spaces,
`AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_isAffineHom` (Stacks 073H):
`R^p f_*F = 0` for `p > 0`. Since `f_*` is a right adjoint
(`AlgebraicGeometry.Space.isRightAdjoint_modulePushforward`) it is left exact, and for a left
exact functor part (2) of Stacks 015C, `Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat`,
makes the vanishing of the positive right derived functors at `F` equivalent to invertibility of
the unit of the right derived functor at `F[0]`. That unit is the canonical map
`f_*F ⟶ Rf_*F`.

## Implementation notes

*Which derived direct image.* `Rf_*` is Mathlib's `CategoryTheory.Functor.rightDerivedFunctorPlus`
of `AlgebraicGeometry.Space.modulePushforward`, on the bounded below derived categories, and the
canonical map is its unit `CategoryTheory.Functor.rightDerivedFunctorPlusUnit`, the spelling of
the scheme case
`Stacks.Tag02KGDerivedComparison.isIso_rightDerivedFunctorPlusUnit_app_of_isAffineHom`
of Stacks 02KG. `F` is the complex `F[0]` of `HomotopyCategory.Plus.singleFunctor`.

*No model of the derived categories is fixed.* The statement is over arbitrary
`[HasDerivedCategory _]` instances on the `𝒪_X`- and `𝒪_Y`-modules, in arbitrary universes: the
right derived functors `CategoryTheory.Functor.rightDerived` that the vanishing is stated with are
built from injective resolutions and do not depend on a model, and
`Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat` is itself model-free.

*The module universe* is the universe `u` of the structure rings, the only one at which
`AlgebraicGeometry.Space.modulePushforward` exists.

*The instance arrangement* is the one of
`StacksFrontier/AlgebraicGeometry/Spaces/AffineHigherPushforwardVanishingUnconditional.lean`:
`CategoryTheory.SheafOfModules.instAbelian` gets a local priority raise, and enough injectives
on the modules of an algebraic space, `AlgebraicGeometry.Space.enoughInjectives_modules`, is a
local instance.

## References

* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 071Z](https://stacks.math.columbia.edu/tag/071Z)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

universe w w' u

namespace AlgebraicGeometry.Space

attribute [local instance] enoughInjectives_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 07U8, `f_*F ≅ Rf_*F`.** Let `f : X ⟶ Y` be an affine morphism of algebraic spaces
over `S` and let `F` be a quasi-coherent `𝒪_X`-module. Then the canonical map from the direct
image `f_*F`, placed in degree zero, to the derived direct image `Rf_*F` is an isomorphism: the
unit of the right derived functor `Rf_*` of `f_*` on bounded below derived categories is
invertible at `F[0]`.

Equivalently `R^p f_*F = 0` for `p > 0`, which is
`AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_isAffineHom` (Stacks 073H, the
reduction of the source to Stacks 02KG through Equation 69.3.0.1); the two are equivalent for the
left exact functor `f_*` by part (2) of Stacks 015C. No model of the derived categories is
fixed. -/
@[stacks 07U8 "f_*F ≅ Rf_*F: the canonical map from the direct image to the derived direct \
image is an isomorphism"]
theorem isIso_rightDerivedFunctorPlusUnit_app_modulePushforward_isAffineHom
    [HasDerivedCategory.{w} (Modules.{u, u} B S hS X.1 X.2)]
    [HasDerivedCategory.{w'} (Modules.{u, u} B S hS Y.1 Y.2)]
    (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) :
    IsIso ((modulePushforward B S hS f).rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj F)) :=
  (Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat (modulePushforward B S hS f) F).2
    fun p hp ↦ isZero_rightDerived_modulePushforward_isAffineHom B S hS f hf F hF p hp

end AlgebraicGeometry.Space

end
