module

public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraAntiEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraFullness

/-!
# The direct-image functor of Stacks 081V is fully faithful

Let `X` be an algebraic space over a scheme `S` of a big fppf site.  Stacks 081V asserts an
anti-equivalence between the algebraic spaces affine over `X` and the quasi-coherent sheaves of
commutative `𝒪_X`-algebras, sending `f : Y ⟶ X` to `f_* 𝒪_Y`.
`StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraFaithful` and
`StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraFullness` prove the content of the
faithfulness and fullness halves at the level of morphisms of direct-image algebras.  This file
states them for the functor `AlgebraicGeometry.Space.quasicoherentPushforwardAlgebraFunctor`,
and for its bounded form `AlgebraicGeometry.Space.boundedPushforwardAlgebraFunctor`.

## Main statements

* `AlgebraicGeometry.Space.faithful_affinePushforwardAlgebraFunctor`: the direct-image functor
  is faithful.
* `AlgebraicGeometry.Space.full_affinePushforwardAlgebraFunctor`: the direct-image functor is
  full.
* `AlgebraicGeometry.Space.full_boundedPushforwardAlgebraFunctor`: so is its bounded form.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The direct-image functor `f ↦ f_* 𝒪_Y` of Stacks 081V is faithful.**

This is the faithfulness half of the anti-equivalence clause of the tag, and no more: the functor
is not shown full by this statement — that is
`AlgebraicGeometry.Space.full_affinePushforwardAlgebraFunctor` below — nor essentially surjective,
and nothing is proved about the tag's compatibility with base change.
`AlgebraicGeometry.Space.eq_of_pushforwardRingMap_eq` is the content;
`AlgebraicGeometry.Space.faithful_affinePushforwardAlgebraFunctor_iff` is what strips the two full
subcategories and the opposite category off it.

Restricting the target to the bounded quasi-coherent algebras changes nothing, by
`AlgebraicGeometry.Space.faithful_boundedPushforwardAlgebraFunctor_iff`. -/
@[stacks 081V "faithfulness of the direct image functor f ↦ f_* 𝒪_Y from the algebraic spaces \
affine over X; the corrected anti-equivalence and the base-change compatibility as a whole are \
affineAlgebraAntiEquivalence_bounded"]
theorem faithful_affinePushforwardAlgebraFunctor (X : AlgebraicSpaces B S hS) :
    (quasicoherentPushforwardAlgebraFunctor B S hS X).Faithful :=
  (faithful_affinePushforwardAlgebraFunctor_iff B S hS X).2
    (eq_of_pushforwardRingMap_eq B S hS)

/-- **The direct-image functor `f ↦ f_* 𝒪_Y` of Stacks 081V is full.**

This is the fullness half of the anti-equivalence clause of the tag, and no more: nothing is
proved here about the functor's essential surjectivity, which would need the relative spectrum of
a quasi-coherent algebra, nor about the tag's compatibility with base change.
`AlgebraicGeometry.Space.exists_pushforwardAlgebraMap_eq` is the content;
`AlgebraicGeometry.Space.full_affinePushforwardAlgebraFunctor_iff` is what strips the two full
subcategories and the opposite category off it.

Faithfulness is `AlgebraicGeometry.Space.faithful_affinePushforwardAlgebraFunctor`, so the two
together make the functor fully faithful, and clause (a) of
`AlgebraicGeometry.Space.isEquivalence_boundedPushforwardAlgebraFunctor_iff_bijective` — that
`f ↦ f_*` be bijective — is delivered. -/
@[stacks 081V "fullness of the direct image functor f ↦ f_* 𝒪_Y from the algebraic spaces affine \
over X; the corrected anti-equivalence and the base-change compatibility as a whole are \
affineAlgebraAntiEquivalence_bounded"]
theorem full_affinePushforwardAlgebraFunctor (X : AlgebraicSpaces B S hS) :
    (quasicoherentPushforwardAlgebraFunctor B S hS X).Full :=
  (full_affinePushforwardAlgebraFunctor_iff B S hS X).2 (exists_pushforwardAlgebraMap_eq B S hS)

/-- **The bounded direct-image functor is full.**

Restricting the target to the quasi-coherent algebras whose sections at every étale chart are
fewer than the big fppf site's cutoff changes nothing, the inclusion of the bounded algebras being
the identity on morphisms: this is
`AlgebraicGeometry.Space.full_boundedPushforwardAlgebraFunctor_iff` applied to
`AlgebraicGeometry.Space.full_affinePushforwardAlgebraFunctor`. -/
theorem full_boundedPushforwardAlgebraFunctor (X : AlgebraicSpaces B S hS) :
    (boundedPushforwardAlgebraFunctor B S hS X).Full :=
  (full_boundedPushforwardAlgebraFunctor_iff B S hS X).2
    (full_affinePushforwardAlgebraFunctor B S hS X)

end AlgebraicGeometry.Space

end
