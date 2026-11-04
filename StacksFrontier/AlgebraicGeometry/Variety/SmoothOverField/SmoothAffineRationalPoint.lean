module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.LocalizationAwayPolynomial
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.SmoothRationalPoint

/-!
# A smooth affine domain with a rational point is geometrically integral

Let `k` be a field and let `A` be a smooth `k`-algebra which is a domain and admits a `k`-algebra
homomorphism to `k`. Then `Spec A` is geometrically integral over `Spec k`: it is a variety whose
structure morphism is smooth, and the given homomorphism is a rational point at which smoothness
holds, so [Stacks, Tag 0CDW] applies.

No assumption on `k` is needed — in particular no characteristic and no perfection assumption —
because the smoothness hypothesis is on the algebra itself. For the coordinate ring of an affine
group scheme cut out of affine space by the invertibility of one polynomial, both hypotheses are
available directly: smoothness from
`AlgebraicGeometry.smooth_of_isLocalization_away_mvPolynomial` and the rational point from the
identity element.

## Main results

* `AlgebraicGeometry.geometricallyIntegral_Spec_map_algebraMap_of_rationalPoint`: geometric
  integrality of the spectrum of a smooth affine domain with a rational point.

## Implementation notes

The rational point required by Tag 0CDW is a section of the structure morphism; the section
attached to a `k`-algebra homomorphism `φ : A →ₐ[k] k` is `Spec` of `φ`, and that it is a section
is `AlgHom.comp_algebraMap` read through `Spec`. Smoothness at the image point follows from
smoothness of the structure morphism by
`AlgebraicGeometry.InfinitesimalLifting.smoothAt_of_smooth`, so the point at which the source
statement needs smoothness does not have to be identified.

## References

* [Stacks Project, Tag 0CDW](https://stacks.math.columbia.edu/tag/0CDW)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **The spectrum of a smooth `k`-algebra which is a domain and has a `k`-point is
geometrically integral over `k`.** It is a variety by
`AlgebraicGeometry.isVariety_Spec_map_algebraMap`, its structure morphism is smooth, and `Spec`
of the given `k`-algebra homomorphism is a rational point; so Tag 0CDW applies. -/
theorem geometricallyIntegral_Spec_map_algebraMap_of_rationalPoint (k : Type u) [Field k]
    (A : Type u) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.Smooth k A]
    (φ : A →ₐ[k] k) :
    GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap k A))) :=
  let : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k A))) :=
    smooth_Spec_map_algebraMap k A
  let : IsVariety k (Spec.map (CommRingCat.ofHom (algebraMap k A))) :=
    isVariety_Spec_map_algebraMap k A
  geometricallyIntegral_of_isVariety_of_smoothAt_rationalPoint _
    (Spec.map (CommRingCat.ofHom (φ : A →+* k)))
    (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, φ.comp_algebraMap, CommRingCat.ofHom_id,
      Spec.map_id])
    (InfinitesimalLifting.smoothAt_of_smooth _ _)

end AlgebraicGeometry

end
