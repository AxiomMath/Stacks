module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumSequence
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.TwoOutOfThree

/-!
# The Euler characteristic of a sum of effective Cartier divisors

Let `Y` be a scheme, proper over a field `k`, and let `D` and `C` be effective Cartier divisors
on `Y`, with `D' = D + C` their sum.  Adding `C` to `D` changes the Euler characteristic of the
structure sheaf of the divisor by the Euler characteristic of the restriction of the ideal sheaf
of `D` to `C`:

`χ(Y, 𝒪_{D'}) - χ(Y, 𝒪_D) = χ(Y, 𝒪_Y(-D)|_C)`.

This is additivity of the Euler characteristic, [Stacks, Tag 08AA], applied to the short exact
sequence `0 ⟶ 𝒪_Y(-D)|_C ⟶ 𝒪_{D'} ⟶ 𝒪_D ⟶ 0` of [Stacks, Tag 0C4T].

## Main results

* `Stacks.Divisors.eulerCharacteristic_sub_eq_of_eq_mul`: the displayed formula.

## Implementation notes

Addition of effective Cartier divisors is multiplication of their ideal sheaves, Mathlib's `Mul`
on `AlgebraicGeometry.Scheme.IdealSheafData`, so the hypothesis is `D' = D * C`; `Add` on ideal
sheaf data is the scheme-theoretic intersection and is not what is meant.  The inclusion
`D ⊆ D'` of closed subschemes, which [Stacks, Tag 0C4T] takes as a hypothesis because the
restriction `𝒪_{D'} ⟶ 𝒪_D` is indexed by a proof of it, is derived here from `D' = D * C` and is
not an argument.

The three terms are spelled as the sequence of [Stacks, Tag 0C4T] spells them: `𝒪_D` is
`AlgebraicGeometry.Scheme.IdealSheafData.closedSubschemeStructureSheaf D`, the structure sheaf of
the closed subscheme pushed forward to `Y`, and `𝒪_Y(-D)|_C` is the pullback of
`Stacks.Divisors.negativeTwist D` along the closed immersion of `C`, pushed forward again.  Both
are `Y.Modules`, which is what `AlgebraicGeometry.eulerCharacteristic` consumes.

**The hypotheses `hfinC`, `hfinD`, `hvanC` and `hvanD` are not the source's.** They are the
hypotheses of `AlgebraicGeometry.eulerCharacteristic_add_of_shortExact_of_outer`, the library's
conditional form of [Stacks, Tag 08AA]: finite dimensionality of the cohomology of the outer two
terms below a bound `N` ([Stacks, Tag 02O6]) and its vanishing from `N` on ([Stacks, Tag 01XJ]).
Neither is in the library for a coherent module on a proper scheme over a field, so nothing
supplies them; see
`StacksFrontier/AlgebraicGeometry/ProperCohomologyFinite/Basic.lean` for Tag 02O6.  The alternating
sum is still well defined without them — `Module.finrank` is `0` on an infinite-dimensional
space — but additivity genuinely fails without finiteness, so they cannot be dropped.

### Relation to [Stacks, Tag 0CA2]

[Stacks, Tag 0CA2] is the two equalities

`χ(X_k, 𝒪_{D'}) - χ(X_k, 𝒪_D) = χ(X_k, 𝒪_X(-D)|_{C_i}) = -(D · C_i) + χ(C_i, 𝒪_{C_i})`

in the situation of [Stacks, Tag 0C61], where the divisors are Cartier on the model `X`, which
lies over a discrete valuation ring and not over `k`, while the Euler characteristics are taken on
the special fibre `X_k`. The theorem below, where the divisors are Cartier on the same scheme
that carries the morphism to `k`, is not an instance of it. The tag is stated and proved, with
the sequence of [Stacks, Tag 0C4T] brought from `X` to `X_k`, as
`Stacks.Models.RegularProperModelSituation.eulerCharacteristic_addComponent` in
`StacksFrontier/AlgebraicGeometry/Curves/Models/ComponentStepEulerCharacteristic.lean`.

## References

* [Stacks Project, Tag 0C4T](https://stacks.math.columbia.edu/tag/0C4T)
* [Stacks Project, Tag 08AA](https://stacks.math.columbia.edu/tag/08AA)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 0CA2](https://stacks.math.columbia.edu/tag/0CA2)
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Divisors

/-- The sum of two effective Cartier divisors contains the first: on ideal sheaf data, where the
sum is the product of the ideals and the order is containment of ideals, `D * C ≤ D`. -/
private theorem idealSheafData_mul_le_left {X : Scheme.{u}} (D C : X.IdealSheafData) :
    D * C ≤ D := by
  rw [Scheme.IdealSheafData.le_def]
  intro U
  change D.ideal U * C.ideal U ≤ D.ideal U
  exact Ideal.mul_le_left

/-- **The Euler characteristic of a sum of effective Cartier divisors.** On a scheme proper over
a field `k`, for effective Cartier divisors `D`, `C` and their sum `D' = D + C`,

`χ(𝒪_{D'}) - χ(𝒪_D) = χ(𝒪_X(-D)|_C)`.

This is the short exact sequence `0 ⟶ 𝒪_X(-D)|_C ⟶ 𝒪_{D'} ⟶ 𝒪_D ⟶ 0` of [Stacks, Tag 0C4T]
together with additivity of the Euler characteristic, [Stacks, Tag 08AA].  The hypotheses `hfinC`
and `hfinD` are the finite dimensionality of [Stacks, Tag 02O6] for the outer two terms below the
bound `N`, and `hvanC`, `hvanD` the vanishing of [Stacks, Tag 01XJ] for them from `N` on; both
are hypotheses of the conditional form of Tag 08AA in the library and neither is in the library.

This is **not** [Stacks, Tag 0CA2]; see the module docstring for the three reasons. -/
theorem eulerCharacteristic_sub_eq_of_eq_mul (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (D D' C : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (hsum : D' = D * C)
    [((Scheme.Modules.pushforward C.subschemeι).obj
      ((Scheme.Modules.pullback C.subschemeι).obj (negativeTwist D))).IsCoherent]
    [D'.closedSubschemeStructureSheaf.IsCoherent]
    [D.closedSubschemeStructureSheaf.IsCoherent] (N : ℕ)
    (hfinC : ∀ n < N, FiniteDimensional k (cohomologyOverField k f
      ((Scheme.Modules.pushforward C.subschemeι).obj
        ((Scheme.Modules.pullback C.subschemeι).obj (negativeTwist D))) n))
    (hfinD : ∀ n < N,
      FiniteDimensional k (cohomologyOverField k f D.closedSubschemeStructureSheaf n))
    (hvanC : ∀ n, N ≤ n → IsZero (cohomologyOverField k f
      ((Scheme.Modules.pushforward C.subschemeι).obj
        ((Scheme.Modules.pullback C.subschemeι).obj (negativeTwist D))) n))
    (hvanD : ∀ n, N ≤ n →
      IsZero (cohomologyOverField k f D.closedSubschemeStructureSheaf n)) :
    eulerCharacteristic k f D'.closedSubschemeStructureSheaf -
        eulerCharacteristic k f D.closedSubschemeStructureSheaf =
      eulerCharacteristic k f ((Scheme.Modules.pushforward C.subschemeι).obj
        ((Scheme.Modules.pullback C.subschemeι).obj (negativeTwist D))) := by
  obtain ⟨g, hz, hex⟩ := addEffectiveCartierDivisor_shortExact D D' C hD
    (hsum ▸ idealSheafData_mul_le_left D C) hsum
  have hadd := eulerCharacteristic_add_of_shortExact_of_outer k f hex N hfinC hfinD hvanC hvanD
  linarith [hadd]

end Stacks.Divisors

end
