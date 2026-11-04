module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraMorphism
import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherent
import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageAlgebraQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentPushforwardAlgebra

/-!
# The direct-image algebra of an affine morphism of algebraic spaces is quasi-coherent

Let `f : Y ⟶ X` be an *affine* morphism of algebraic spaces over a scheme `S` of a big fppf
site.  Then the sheaf of `𝒪_X`-algebras `f_* 𝒪_Y` is quasi-coherent, with no further
hypothesis, and the direct-image functor of Stacks 081V on the algebraic spaces affine over `X`
therefore takes values in the quasi-coherent `𝒪_X`-algebras rather than in all algebra sheaves.

## Main definitions

* The contravariant direct-image functor `(AffineOver X)ᵒᵖ ⥤ QuasicoherentAlgebra X` of
  Stacks 081V is the base's `AlgebraicGeometry.Space.affineQuasicoherentPushforwardAlgebraFunctor`;
  this file registers it and records its values.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherent_pushforwardAlgebra_of_isAffineHom'`: the direct-image
  algebra of an algebraic space affine over `X` is a quasi-coherent `𝒪_X`-algebra.
* `AlgebraicGeometry.Space.affineQuasicoherentPushforwardAlgebraFunctor_obj` and
  `AlgebraicGeometry.Space.affineQuasicoherentPushforwardAlgebraFunctor_map_right`: the functor
  is the direct-image algebra on objects and
  `AlgebraicGeometry.Space.pushforwardRingMap` on morphisms, both after forgetting
  quasi-coherence.

## Implementation notes

Quasi-coherence is `AlgebraicGeometry.Space.underlyingModule_pushforwardAlgebra`, which
identifies the `𝒪_X`-module underlying `f_* 𝒪_Y` with the direct image of `𝒪_Y`, followed by
the quasi-coherence of the direct image along an affine morphism, Stacks 07U8
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_isAffineHom`), applied to
the structure sheaf of `Y` regarded as a module over itself.  That module is quasi-coherent by
Stacks 03DL(6), `SheafOfModules.isQuasicoherentOnSite_unit`.

The companion `AlgebraicGeometry.Space.isQuasicoherent_pushforwardAlgebra` assumes Stacks 03M9
and concludes for a quasi-compact, quasi-separated morphism.  Neither statement subsumes the
other: an affine morphism is quasi-compact and separated, so the hypothesis on the morphism here
is the stronger one, but the conclusion here is unconditional, Stacks 07U8 being proved while
Stacks 03M9 is not.

`StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherent` is imported
*non-publicly*: its own import closure reaches
`StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffinePushforwardQuasicoherent`, and
re-exporting that changes which `CategoryTheory.Abelian` instance is found downstream.  Nothing
in the statements below mentions that file, so the non-public import suffices.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The direct image of the structure sheaf along an affine morphism of algebraic spaces is a
quasi-coherent algebra.**  For an algebraic space `Y` affine over `X`, the sheaf of
`𝒪_X`-algebras `f_* 𝒪_Y` is quasi-coherent.

The `𝒪_X`-module underlying `f_* 𝒪_Y` is the direct image of `𝒪_Y`, and the direct image along
an affine morphism preserves quasi-coherence by Stacks 07U8. -/
theorem isQuasicoherent_pushforwardAlgebra_of_isAffineHom' {X : AlgebraicSpaces B S hS}
    (Y : Over X) (hY : IsAffineHom B S hS Y.hom.hom) :
    (pushforwardAlgebra B S hS Y).IsQuasicoherent := by
  have h := isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional B S hS Y.hom hY
    (SheafOfModules.unit (structureRingSheaf B S hS Y.left))
    (SheafOfModules.isQuasicoherentOnSite_unit (structureRingSheaf B S hS Y.left))
  rw [← underlyingModule_pushforwardAlgebra B S hS Y.hom] at h
  exact h

add_to_stacks 081V "the direct image functor f ↦ f_* 𝒪_Y on the algebraic spaces affine over X, \
with values in the quasi-coherent 𝒪_X-algebras"
  AlgebraicGeometry.Space.affineQuasicoherentPushforwardAlgebraFunctor

/-- The value of the quasi-coherent direct-image functor on an algebraic space affine over `X`
is the direct-image algebra of that space. -/
theorem affineQuasicoherentPushforwardAlgebraFunctor_obj (X : AlgebraicSpaces B S hS)
    (Y : AffineOver B S hS X) :
    (quasicoherentAlgebraInclusion B S hS X).obj
        ((affineQuasicoherentPushforwardAlgebraFunctor B S hS X).obj (op Y)) =
      pushforwardAlgebra B S hS Y.obj :=
  rfl

/-- The action of the quasi-coherent direct-image functor on a morphism over `X` is the
canonical map on direct-image sheaves of rings. -/
theorem affineQuasicoherentPushforwardAlgebraFunctor_map_right (X : AlgebraicSpaces B S hS)
    {Y Z : AffineOver B S hS X} (f : Y ⟶ Z) :
    ((quasicoherentAlgebraInclusion B S hS X).map
        ((affineQuasicoherentPushforwardAlgebraFunctor B S hS X).map f.op)).right =
      pushforwardRingMap B S hS f.hom :=
  rfl

end AlgebraicGeometry.Space

end
