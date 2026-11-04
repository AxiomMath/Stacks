module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinCartierIntersection.FinsumIntersections
public import StacksFrontier.AlgebraicGeometry.Chow.GysinCartierIntersection.IntersectionCoefficient
public import StacksFrontier.AlgebraicGeometry.Chow.GysinCartierIntersection.ClosedSubschemeCycle

/-!
# Gysin pullback of the fundamental cycle of a closed subscheme

Let `X` be locally of finite type over the base scheme of chapter 42 of the Stacks Project, let
`L` be an invertible module on `X` with global section `s`, and let `i : D ⟶ X` be the zero
scheme of `s`. For a closed subscheme `Z ⊆ X` of delta-dimension at most `k + 1` whose
intersection with `D` is an effective Cartier divisor on `Z`, the Gysin homomorphism `i^*` of
`StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction` sends the fundamental cycle `[Z]_{k+1}`
to the class of the fundamental cycle `[D ∩ Z]_k` of the intersection.

## Main results

* `Stacks.Chow.gysinHomomorphismOfInvertible_cycleAssociatedToClosedSubscheme` —
  `i^*[Z]_{k+1} = [D ∩ Z]_k` in `CH_k(D)`.
* `Stacks.Chow.gysinRule_extendCycleGroup_cycleAssociatedToClosedSubscheme` — the same identity
  one level down, between cycles rather than classes.
* `Stacks.Chow.gysinHomomorphism_eq_finsum_intersections` — if no integral closed subscheme
  occurring in a `(k+1)`-cycle lies in `D`, the Gysin class of that cycle is the class of the
  coefficientwise sum of the fundamental cycles of the intersections with `D`.
* `Stacks.Chow.intersectionCycleCoeff_eq_length_quotient_sup` — the coefficient of such an
  intersection cycle at a point of `D`, as a colength in the local ring of `X`.

## Implementation notes

The local input is the length computation of Stacks 02QG,
`Stacks.Chow.length_quotSMulTop_eq_sum_minimal_support`: at a point `z ∈ D` of relative
dimension `k`, with `a ∈ 𝒪_{X,z}` a local equation of `D` coming from a trivialization of `L`,
the length of `M / a M` is the sum over the minimal primes `q` of `Supp(M)` of the length of
`M_q` times the order of vanishing of `a` along `q`. Here `M = 𝒪_{Z,z}`, and the hypothesis that
`D ∩ Z` is an effective Cartier divisor on `Z` is what makes `a` a nonzerodivisor on it.

The section is taken as an element of `L.sections`, from which the global section
`s.eval (.op ⊤) : Γ(L, ⊤)` that the Gysin map consumes is extracted.

Several auxiliary results about relative dimension, the reduced structure on the closure of a
point, and local lengths are stated here rather than kept private, because the companion
statement of Stacks 02TB for the cycle of a coherent sheaf consumes them.

## References

* [Stacks Project, Tag 02TB](https://stacks.math.columbia.edu/tag/02TB)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02QG](https://stacks.math.columbia.edu/tag/02QG)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
-/
