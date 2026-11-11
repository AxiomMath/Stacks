module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectProperPushforward
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived direct image of a relatively perfect complex over a Noetherian base

Let `S` be a Noetherian scheme, `f : X ⟶ S` proper, flat and locally of finite presentation, and
`E` an `S`-perfect object of `D(𝒪_X)`. Then `Rf_*E` is perfect. This is the Noetherian case to
which the source reduces [Stacks, Tag 0DJT]; it is proved as
`isPerfect_derivedPushforward_of_isPerfectRelativeTo` in
`StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectProperPushforward`, and recorded here
against the corresponding statements of SGA 6.

## Main results

* `pushforwardTorDimensionResidue_of_isGenuine`: the Tor-dimension half of [Stacks, Tag 08EV]
  for every `S`-perfect object, an alias of
  `pushforwardTorDimensionResidue_of_isGenuineTensorFamily`.
* `isPerfect_derivedPushforward_of_isPerfectRelativeTo_of_isNoetherian`: `Rf_*E` is perfect over
  a Noetherian base.

## References

* [Stacks Project, Tag 0DJT](https://stacks.math.columbia.edu/tag/0DJT)
* [Stacks Project, Tag 08EV](https://stacks.math.columbia.edu/tag/08EV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.RelativelyPerfectProperPushforward

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable [IsNoetherian S] [IsProper f] [Flat f] [LocallyOfFinitePresentation f]

/-- **The Tor-dimension half of [Stacks, Tag 08EV], for every `S`-perfect object**, over a
Noetherian base; see `pushforwardTorDimensionResidue_of_isGenuineTensorFamily`. -/
alias pushforwardTorDimensionResidue_of_isGenuine :=
  pushforwardTorDimensionResidue_of_isGenuineTensorFamily

/-- **Perfectness of `Rf_*E` over a Noetherian base.** Let `S` be a Noetherian scheme, let
`f : X ⟶ S` be a proper, flat morphism locally of finite presentation and let `E` be an
`S`-perfect object of `D(𝒪_X)`. Then `Rf_*E` is a perfect object of `D(𝒪_S)`.

This is an alias of `isPerfect_derivedPushforward_of_isPerfectRelativeTo`. -/
@[sga "6 0 3.1" "special case",
  sga "6 0 4.1" "f proper, special case",
  sga "6 III 2.1" "Case Y = S",
  sga "6 III 2.2" "special case",
  sga "6 III 4.8" "clause (a), case Y = S",
  sga "6 IV 3.3.2" "3.3.2.3, special case",
  sga "6 XIV 2.2" "special case"]
alias isPerfect_derivedPushforward_of_isPerfectRelativeTo_of_isNoetherian :=
  isPerfect_derivedPushforward_of_isPerfectRelativeTo

end Stacks.AlgebraicGeometry.RelativelyPerfectProperPushforward

end
