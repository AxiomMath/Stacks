module

public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.NormalizationCrossingsEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.StrictNormalizationCrossings
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.UnramifiedNormalization

/-!
# A normal crossings divisor satisfies the normalization criterion

A normal crossings divisor on a locally Noetherian scheme is reduced, its normalization is
unramified, and for every `n ≥ 1` the scheme `Z_n` obtained from the `n`-fold fibre power of the
normalization by deleting the fat diagonal is regular and maps to the ambient scheme by a local
complete intersection morphism whose conormal sheaf is locally free of rank `n`. This is the
implication (1) ⇒ (2) of Tag 0CBR.

## Main results

* `Stacks.Divisors.isNormalizationCrossingsDivisor_of_isNormalCrossingsDivisor`: condition (1)
  of Tag 0CBR implies condition (2).

## Implementation notes

Condition (2) is étale-local on the ambient scheme and a normal crossings divisor is strict on
an étale chart through each of its points, so the statement reduces to the strict case.

## References

* [Stacks Project, Tag 0CBR](https://stacks.math.columbia.edu/tag/0CBR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Divisors

/-- **A normal crossings divisor satisfies the normalization criterion.** This is the
implication (1) ⇒ (2) of Tag 0CBR. -/
theorem isNormalizationCrossingsDivisor_of_isNormalCrossingsDivisor {X : Scheme.{u}}
    [IsLocallyNoetherian X] (D : X.IdealSheafData) (h : IsNormalCrossingsDivisor D) :
    IsNormalizationCrossingsDivisor D := by
  refine isNormalizationCrossingsDivisor_of_forall_etaleChart D
    (isReduced_of_isNormalCrossingsDivisor D h)
    (unramified_divisorNormalization_of_isNormalCrossingsDivisor D h) fun y => ?_
  obtain ⟨W, g, hW, hg, hq, hsnc⟩ := h.2 y
  have := hW
  exact ⟨W, g, hW, hg, hq,
    isNormalizationCrossingsDivisor_of_isStrictNormalCrossingsDivisor (D.comap g) hsnc⟩

end Stacks.Divisors

end
