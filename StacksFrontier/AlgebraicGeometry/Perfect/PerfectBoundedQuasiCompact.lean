module

public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentFrom.Affine
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TriangleLemmas
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension

/-!
# A perfect object on a quasi-compact ringed space is bounded above

The cohomology of a perfect object of `D(𝒪_X)` vanishes in all sufficiently large degrees as soon
as `X` is quasi-compact. Perfectness gives a strictly perfect complex near every point, and a
strictly perfect complex is bounded; quasi-compactness is what turns the resulting local bounds
into one global bound.

## Main results

* `AlgebraicGeometry.RingedSpace.exists_isZero_homology_of_isPerfect`: a perfect object on a
  quasi-compact ringed space has vanishing cohomology in all degrees above some integer.
* `AlgebraicGeometry.RingedSpace.compactSpace_restrict_of_isCompact`: a quasi-compact open of a
  ringed space is a quasi-compact ringed space.

## Implementation notes

`AlgebraicGeometry.RingedSpace.exists_isZero_homology_of_isPerfect` involves only the model of
`D(𝒪_X)`: perfectness gives pseudo-coherence
(`Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect`), whose local strictly perfect
approximations are complexes over opens, so no derived category of an open subspace occurs.

## References

* [Stacks Project, Tag 09IN](https://stacks.math.columbia.edu/tag/09IN)
* [Stacks Project, Tag 0FEP](https://stacks.math.columbia.edu/tag/0FEP)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

universe u

namespace AlgebraicGeometry.RingedSpace

/-- **A perfect object on a quasi-compact ringed space has cohomology vanishing in all large
degrees.** That is, there is an integer `b` with `Hⁱ(K) = 0` for every `i > b`. -/
theorem exists_isZero_homology_of_isPerfect {X : RingedSpace.{u, u}} [CompactSpace X.carrier]
    [HasDerivedCategory.{u + 1} (OXMod.{u, u} X)]
    (K : DerivedCategory (OXMod.{u, u} X))
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := X) K) :
    ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj K) := by
  obtain ⟨b, hb⟩ := exists_isZero_homology_of_isPseudoCoherentFrom K 0
    (IsPseudoCoherent.isPseudoCoherentFrom
      (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect K hK) 0)
  exact ⟨b, fun i hi => hb i hi.le⟩

end AlgebraicGeometry.RingedSpace

end
