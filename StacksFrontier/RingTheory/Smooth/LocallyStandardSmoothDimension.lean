module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
public import Mathlib.RingTheory.RingHom.StandardSmooth

/-!
# The dimension of a locally standard smooth algebra over a field

A nonzero algebra `S` over a field `K` which is locally standard smooth of relative dimension `n`
(`RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)`) has Krull dimension `n`:
`Spec S ⟶ Spec K` is smooth of relative dimension `n`, and a nonempty scheme smooth of relative
dimension `n` over a field has dimension `n`
(`AlgebraicGeometry.topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field`).

This gives the dimension one of the generic fibre of a family of smooth curves, the input of the
étale divisor along which the Gysin map of `R² g_!` is taken in the reduction of the weight bound
of Weil II ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Algebra.ringKrullDim_eq_of_locally_isStandardSmoothOfRelativeDimension`.
-/

public section

universe u

open AlgebraicGeometry

/-- **A nonzero locally standard smooth algebra of relative dimension `n` over a field has Krull
dimension `n`.** -/
theorem Algebra.ringKrullDim_eq_of_locally_isStandardSmoothOfRelativeDimension {K S : Type u}
    [Field K] [CommRing S] [Algebra K S] [Nontrivial S] {n : ℕ}
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap K S)) :
    ringKrullDim S = n := by
  have : SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap K S))) :=
    HasRingHomProperty.Spec_iff.2 h
  have : Nonempty (Spec (CommRingCat.of S)) := inferInstanceAs (Nonempty (PrimeSpectrum S))
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field n
    (Spec.map (CommRingCat.ofHom (algebraMap K S)))
