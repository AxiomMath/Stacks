module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.NoetherianSpace

/-!
# Transporting Noetherianness and the dimension bound to the spectrum of an affine chart

Let `X` be a scheme and `U` an affine open of `X`. The results below move two hypotheses — that
the space is Noetherian and of Krull dimension at most one — from `X` to
`PrimeSpectrum Γ(X, U)`, which is where
`Stacks.LiftInvertible.exists_basicOpen_isolating_of_topologicalKrullDim_le_one` states them.

They are used by
`Stacks.LiftInvertible.exists_isAffineOpen_punctured_of_topologicalKrullDim_le_one` on the way
from the dimension bound of [Stacks, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY) to a
star-shaped cover: an isolating neighbourhood of a closed point can only be shrunk to one whose
puncture is again a *basic* open — hence affine — inside an affine chart, and the
punctured-basic-open lemma asks for its hypotheses on the chart's spectrum rather than on `X`.

## Main results

* `Stacks.LiftInvertible.noetherianSpace_primeSpectrum_of_isAffineOpen`: the spectrum of the
  sections over an affine open of a Noetherian scheme is a Noetherian space.
* `Stacks.LiftInvertible.topologicalKrullDim_primeSpectrum_le_of_isAffineOpen`: a bound on the
  Krull dimension of `X` bounds that of the spectrum of the sections over an affine open.

## Implementation notes

Both go through `AlgebraicGeometry.IsAffineOpen.isoSpec`, whose underlying map is a
homeomorphism from the open subspace to the spectrum, and the corresponding subspace statements:
`TopologicalSpace.NoetherianSpace.set` and `topologicalKrullDim_subspace_le`. The dimension
argument is the one Mathlib's `AlgebraicGeometry.IsLocallyArtinian.of_topologicalKrullDim_le_zero`
runs at `n = 0`; it is stated here for an arbitrary bound because Tag 09NY needs `n = 1`.

The bound is taken in `WithBot ℕ∞`, the codomain of `topologicalKrullDim`, so that the statement
applies verbatim to the `topologicalKrullDim X ≤ 1` of Tag 09NY.

## References

* [Stacks Project, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY)
* [Stacks Project, Tag 0055](https://stacks.math.columbia.edu/tag/0055)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.LiftInvertible

/-- **The spectrum of an affine chart of a Noetherian scheme is a Noetherian space.** The chart
is a subspace of `X`, so Noetherian, and `IsAffineOpen.isoSpec` is a homeomorphism onto the
spectrum. -/
theorem noetherianSpace_primeSpectrum_of_isAffineOpen {X : Scheme.{u}} [NoetherianSpace X]
    (U : X.affineOpens) : NoetherianSpace (PrimeSpectrum Γ(X, U.1)) :=
  have : NoetherianSpace (U.1 : Set X) := NoetherianSpace.set _
  (noetherianSpace_iff_of_homeomorph U.2.isoSpec.hom.homeomorph).mp this

/-- **The dimension bound transports to the spectrum of an affine chart.** The chart is a
subspace of `X`, so `topologicalKrullDim_subspace_le` bounds its dimension by that of `X`, and
`IsAffineOpen.isoSpec` identifies it with the spectrum.

This is Mathlib's argument in `AlgebraicGeometry.IsLocallyArtinian.of_topologicalKrullDim_le_zero`
at an arbitrary bound rather than at `0`. -/
theorem topologicalKrullDim_primeSpectrum_le_of_isAffineOpen {X : Scheme.{u}}
    (U : X.affineOpens) {n : WithBot ℕ∞} (h : topologicalKrullDim X ≤ n) :
    topologicalKrullDim (PrimeSpectrum Γ(X, U.1)) ≤ n := by
  show topologicalKrullDim (Spec Γ(X, U.1)) ≤ n
  rw [← IsHomeomorph.topologicalKrullDim_eq _ U.2.isoSpec.hom.homeomorph.isHomeomorph]
  exact (topologicalKrullDim_subspace_le X U).trans h

end Stacks.LiftInvertible

end
