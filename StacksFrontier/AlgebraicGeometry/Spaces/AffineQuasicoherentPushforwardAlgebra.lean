module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageAlgebraQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs

/-!
# The direct-image algebra of an affine morphism, as a quasi-coherent algebra

Let `f : Y ⟶ X` be an affine morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  This file records that the direct-image algebra `f_* 𝒪_Y` of
`AlgebraicGeometry.Space.pushforwardAlgebra` is then quasi-coherent, and lifts the direct-image
functor `AlgebraicGeometry.Space.affinePushforwardAlgebraFunctor` of Stacks 081V along that fact
so that it lands in `AlgebraicGeometry.Space.QuasicoherentAlgebra` rather than in all algebra
sheaves.

Quasi-coherence of `f_* 𝒪_Y` for a quasi-compact, quasi-separated `f` is
`AlgebraicGeometry.Space.isQuasicoherent_pushforwardAlgebra`, which carries Stacks 03M9 as a
hypothesis; an affine morphism is quasi-compact by
`AlgebraicGeometry.Space.isQuasiCompact_of_isAffineHom'` and quasi-separated by
`AlgebraicGeometry.Space.isQuasiSeparated_of_isAffineHom`, and Stacks 03M9 itself is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_qcqs`.  So nothing here is
conditional.

## Main definitions

* `AlgebraicGeometry.Space.affineQuasicoherentPushforwardAlgebraFunctor` is the direct-image
  functor from the algebraic spaces affine over `X`, contravariantly, to the quasi-coherent
  sheaves of commutative `𝒪_X`-algebras.

## Main results

* `AlgebraicGeometry.Space.affineQuasicoherentPushforwardAlgebraFunctorCompι`: composing the
  lifted functor with the inclusion of the full subcategory returns the direct-image functor
  into all algebra sheaves, so the codomain restriction changes nothing.

## Implementation notes

The quasi-coherence of the direct-image algebra of an affine morphism is
`AlgebraicGeometry.Space.isQuasicoherent_pushforwardAlgebra_of_isAffineHom`, in
`StacksFrontier/AlgebraicGeometry/Spaces/AffineDirectImageAlgebraQuasicoherent.lean`.

No declaration here carries Stacks 081V.  The tag asserts that direct image is an
*anti-equivalence* onto the quasi-coherent algebras and that it is compatible with arbitrary
base change; what is supplied here is only the functor of that assertion with its codomain
restricted to the quasi-coherent algebras, which is the `pushforward` field of
`AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence` and not the structure itself.  The two
facet attributes for the direct-image functor sit on
`AlgebraicGeometry.Space.pushforwardAlgebraMap` and
`AlgebraicGeometry.Space.affinePushforwardAlgebraFunctor` in
`StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraMorphism`.

The codomain restriction rests on the quasi-coherence of `f_* 𝒪_Y`, which is Stacks 03M9; that
is why it is made here rather than in
`StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraMorphism`.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The direct-image functor `Y ↦ Y.hom_* 𝒪_Y` from the algebraic spaces affine over `X`,
contravariantly, to the quasi-coherent sheaves of commutative `𝒪_X`-algebras.

This is `AlgebraicGeometry.Space.affinePushforwardAlgebraFunctor` with its codomain restricted
along `AlgebraicGeometry.Space.isQuasicoherent_pushforwardAlgebra_of_isAffineHom`.  It is the
functor of Stacks 081V with the source and target categories of that tag, but it is *not* shown
to be an anti-equivalence here. -/
def affineQuasicoherentPushforwardAlgebraFunctor (X : AlgebraicSpaces B S hS) :
    (AffineOver B S hS X)ᵒᵖ ⥤ QuasicoherentAlgebra B S hS X :=
  affinePushforwardQuasicoherentAlgebraFunctor B S hS X

/-- Composing the functor into the quasi-coherent algebras with the inclusion of that full
subcategory returns `AlgebraicGeometry.Space.affinePushforwardAlgebraFunctor`: restricting the
codomain changes nothing. -/
def affineQuasicoherentPushforwardAlgebraFunctorCompι (X : AlgebraicSpaces B S hS) :
    affineQuasicoherentPushforwardAlgebraFunctor B S hS X ⋙
        quasicoherentAlgebraInclusion B S hS X ≅
      affinePushforwardAlgebraFunctor B S hS X :=
  ObjectProperty.liftCompιIso _ _ _

end AlgebraicGeometry.Space

end
