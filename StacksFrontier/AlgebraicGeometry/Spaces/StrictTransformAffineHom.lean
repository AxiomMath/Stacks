module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformProperties

/-!
# The strict transform of an affine morphism is affine

Let `f : X ⟶ A` be a morphism of algebraic spaces over `S`, let `b : A' ⟶ A` be a second one —
in the application the blowing up of `A` in a closed subspace — and let `E` be a subspace of
`A'`.  The strict transform `X'` of `X` with respect to `(b, E)` is a closed subspace of the
base change `X ×_A A'`, and this file proves that when `f` is affine the induced morphism
`X' ⟶ A'` is affine too.

This is the fact the proof of Stacks 0GV6 uses without proof ("the strict transform of an
affine morphism is affine — details omitted") in its reduction of the general quasi-compact
quasi-separated case to the case of finite presentation over `Spec ℤ`: the stratification and
the blowup centres produced for an approximation `X₀` of `X` are pulled back to `X` along the
affine morphism `X ⟶ X₀`, and for the blowups of the strata that pullback is the strict
transform.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_strictTransformPullbackToBlowUp`: the projection
  `X ×_A A' ⟶ A'` is affine when `f` is, being its base change.
* `AlgebraicGeometry.Space.isAffineHom_strictTransformSpaceToBlowUp`: the strict transform
  `X' ⟶ A'` of an affine morphism is affine.

## Implementation notes

No hypothesis is placed on `b` or on `E`: affineness of `X' ⟶ A'` holds for the strict
transform with respect to any pair, because the only two inputs are that `X' ⟶ X ×_A A'` is a
closed immersion — which the definition
`AlgebraicGeometry.Space.strictTransform` provides unconditionally, it being valued in
`AlgebraicGeometry.Space.ClosedSubspaces` — and that `X ×_A A' ⟶ A'` is a base change of `f`.
In particular nothing here needs the strict transform to be cut out by a quasi-coherent ideal,
which for algebraic spaces is available only under the hypotheses discussed in
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransform.lean`.

The three ingredients are Stacks 03WI (affine morphisms are stable under base change,
`AlgebraicGeometry.Space.IsAffineHom.of_isPullback`), Stacks 07U2 (a closed immersion is
affine, `AlgebraicGeometry.Space.isAffineHom_of_isClosedImmersion`) and Stacks 03WH (affine
morphisms compose, `AlgebraicGeometry.Space.isAffineHom_comp`).

## References

* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 03WH](https://stacks.math.columbia.edu/tag/03WH)
* [Stacks Project, Tag 03WI](https://stacks.math.columbia.edu/tag/03WI)
* [Stacks Project, Tag 07U2](https://stacks.math.columbia.edu/tag/07U2)
* [Stacks Project, Tag 0GV6](https://stacks.math.columbia.edu/tag/0GV6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A X A' : AlgebraicSpaces B S hS} (f : X ⟶ A) (b : A' ⟶ A)

/-- **The projection `X ×_A A' ⟶ A'` is affine when `f : X ⟶ A` is**, by Stacks 03WI: it is
the base change of `f` along `b`. -/
theorem isAffineHom_strictTransformPullbackToBlowUp (hf : IsAffineHom B S hS f.hom) :
    IsAffineHom B S hS (strictTransformPullbackToBlowUp B S hS f b).hom :=
  IsAffineHom.of_isPullback (IsPullback.of_hasPullback f.hom b.hom) hf

/-- **The strict transform of an affine morphism is affine.**  For `f : X ⟶ A` affine, any
`b : A' ⟶ A` and any subspace `E` of `A'`, the strict transform `X' ⟶ A'` of `X` with respect
to `(b, E)` is affine: it is the closed immersion `X' ⟶ X ×_A A'`, which is affine by Stacks
07U2, followed by the projection `X ×_A A' ⟶ A'`, which is affine by Stacks 03WI. -/
theorem isAffineHom_strictTransformSpaceToBlowUp (hf : IsAffineHom B S hS f.hom)
    (E : Subfunctor A'.1) :
    IsAffineHom B S hS (strictTransformSpaceToBlowUp B S hS f b E).hom :=
  isAffineHom_comp B S hS _ _
    (isAffineHom_of_isClosedImmersion B S hS _ (strictTransform B S hS f b E).2.2)
    (isAffineHom_strictTransformPullbackToBlowUp B S hS f b hf)

end AlgebraicGeometry.Space

end
