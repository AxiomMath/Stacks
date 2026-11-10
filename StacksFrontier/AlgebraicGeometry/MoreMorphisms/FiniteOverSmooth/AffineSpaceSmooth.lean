module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import StacksCore.Tactic.StacksAttribute

/-!
# Affine `n`-space is smooth of relative dimension `n`

A polynomial ring in `n` variables is standard smooth of relative dimension `n` over its
coefficient ring, because the generators `X_1, …, X_n` and the empty family of relations form a
submersive presentation of dimension `n`. Consequently the projection
`A^n_{Spec A} ⟶ Spec A` is smooth of relative dimension `n`.

This is the source of the smooth morphism in Stacks 052E: a morphism locally of finite type is
factored through affine `n`-space over the base, and the smooth scheme of the conclusion is an
étale neighbourhood of a point of that affine space.

## Main results

* `AlgebraicGeometry.smoothOfRelativeDimension_specMap_C`: the projection
  `Spec R[X_1, …, X_n] ⟶ Spec R` is smooth of relative dimension `n`.
* `AlgebraicGeometry.SmoothOfRelativeDimension.comp_relativeDimension_zero`: composing with a
  morphism smooth of relative dimension `0` — in particular an open immersion or an étale
  morphism — does not change the relative dimension.

## Implementation notes

That `R[X_1, …, X_n]` is standard smooth of relative dimension `n` over `R` is Mathlib's instance
`Algebra.IsStandardSmoothOfRelativeDimension.mvPolynomial_fin`, built from the submersive
presentation `Algebra.SubmersivePresentation.mvPolynomial` (the variables and no relations).

## References

* [Stacks Project, Tag 02G2](https://stacks.math.columbia.edu/tag/02G2)
* [Stacks Project, Tag 052E](https://stacks.math.columbia.edu/tag/052E)
-/

@[expose] public section

open CategoryTheory MvPolynomial

universe u

namespace AlgebraicGeometry

/-- **Stacks 02G2 for affine space.** The projection from affine `n`-space over `Spec A` to
`Spec A` is smooth of relative dimension `n`. -/
theorem smoothOfRelativeDimension_specMap_C (A : Type u) [CommRing A] (n : ℕ) :
    SmoothOfRelativeDimension n
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := Fin n) (R := A)))) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  change (algebraMap A (MvPolynomial (Fin n) A)).IsStandardSmoothOfRelativeDimension n
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  infer_instance

/-- Postcomposing a morphism smooth of relative dimension `n` with one smooth of relative
dimension `0` keeps the relative dimension `n`. -/
theorem SmoothOfRelativeDimension.comp_relativeDimension_zero {X Y Z : Scheme.{u}} (n : ℕ)
    (f : X ⟶ Y) (g : Y ⟶ Z) [SmoothOfRelativeDimension n f]
    [SmoothOfRelativeDimension 0 g] :
    SmoothOfRelativeDimension n (f ≫ g) :=
  inferInstanceAs (SmoothOfRelativeDimension (n + 0) (f ≫ g))

/-- Precomposing a morphism smooth of relative dimension `n` with an étale morphism — in
particular an open immersion — keeps the relative dimension `n`. -/
theorem SmoothOfRelativeDimension.etale_comp {X Y Z : Scheme.{u}} (n : ℕ)
    (f : X ⟶ Y) (g : Y ⟶ Z) [Etale f] [SmoothOfRelativeDimension n g] :
    SmoothOfRelativeDimension n (f ≫ g) := by
  have h : SmoothOfRelativeDimension (0 + n) (f ≫ g) := inferInstance
  rwa [zero_add] at h

end AlgebraicGeometry
