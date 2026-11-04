module

public import StacksFrontier.RingTheory.Smoothing.LiftingAlongSurjections.GlobalCompleteIntersectionLift
public import StacksFrontier.RingTheory.Smoothing.LiftingAlongSurjections.SyntomicLift
public import StacksFrontier.RingTheory.Smoothing.LiftingAlongSurjections.SmoothLift

/-!
# Lifting syntomic and smooth algebras along a surjection

Let `R → R₀` be a surjective map of commutative rings with kernel `I`. Every syntomic
`R₀`-algebra `A₀` is the special fibre `A/IA` of a syntomic `R`-algebra `A`, and every smooth
`R₀`-algebra is the special fibre of a smooth `R`-algebra.

## Main results

* `Stacks.Smoothing.exists_syntomic_lift_of_surjective`: a syntomic algebra over a quotient of
  the base lifts to a syntomic algebra over the base with the given special fibre.
* `Stacks.Smoothing.exists_smooth_lift_of_surjective`: a smooth algebra over a quotient of the
  base lifts to a smooth algebra over the base with the given special fibre.

## References

* [Stacks Project, Proposition 16.10.4, Tag 07M8](https://stacks.math.columbia.edu/tag/07M8)
-/
