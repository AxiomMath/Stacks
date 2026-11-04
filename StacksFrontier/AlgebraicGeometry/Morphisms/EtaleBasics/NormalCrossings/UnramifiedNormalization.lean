module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.UnramifiedLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.EtaleNormalization
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPullback09US

/-!
# The normalization of a normal crossings divisor is unramified

A normal crossings divisor has strict normal crossings on an étale neighbourhood of each of its
points, and the normalization of a strict normal crossings divisor is unramified. Since
unramifiedness is étale local on the source and target, and the normalization of a divisor
commutes with étale localization, the normalization of a normal crossings divisor is unramified.
This is the second clause of condition (2) of Tag 0CBR.

## Main results

* `Stacks.Divisors.unramified_divisorNormalization_of_isNormalCrossingsDivisor`: the
  normalization of a normal crossings divisor is unramified.

## Implementation notes

The étale-local criterion `AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget` asks, at a point `x`
of the source, for a commutative square of étale neighbourhoods on which the morphism has the
property. Here the square is the cartesian square of
`Stacks.Divisors.isPullback_comapNormalizationMap` for a chart on which `D` has strict normal
crossings, chosen around the image of `x` in the divisor; the point of the upper left corner
over `x` exists because in a cartesian square the image of one projection is the preimage of the
image of the opposite side.

## References

* [Stacks Project, Tag 0CBR](https://stacks.math.columbia.edu/tag/0CBR)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Divisors

/-- **The normalization of a normal crossings divisor is unramified.** This is the
unramifiedness clause of condition (2) of Tag 0CBR, under hypothesis (1). -/
theorem unramified_divisorNormalization_of_isNormalCrossingsDivisor {X : Scheme.{u}}
    [IsLocallyNoetherian X] (D : X.IdealSheafData) (h : IsNormalCrossingsDivisor D) :
    Unramified (divisorNormalization D) := by
  rw [unramified_isEtaleLocalOnSourceAndTarget.iff_forall_exists_etale_neighborhood]
  intro x
  obtain ⟨W, g, hW, hg, ⟨q, hq⟩, hsnc⟩ := h.2 ((divisorNormalization D).base x)
  have := hW
  have := hg
  have hsq := isPullback_comapNormalizationMap g D
  have hx : x ∈ Set.range (comapNormalizationMap g D).base := by
    rw [range_eq_preimage_range_of_isPullback hsq, Set.mem_preimage,
      range_eq_preimage_range_of_isPullback (isPullback_comapSubschemeMap g D).flip,
      Set.mem_preimage]
    exact ⟨q, hq⟩
  obtain ⟨u, hu⟩ := hx
  refine ⟨divisorNormalizationScheme (D.comap g), (D.comap g).subscheme,
    comapNormalizationMap g D, comapSubschemeMap g D, divisorNormalization (D.comap g), u,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale.{u}) hsq.flip
      inferInstance, inferInstance, hu,
    hsq.w.symm, unramified_divisorNormalization_of_isStrictNormalCrossingsDivisor _ hsnc⟩

end Stacks.Divisors

end
