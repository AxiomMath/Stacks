module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCap42.ExistsRegularSection
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicCascade.RegularGenericValue
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSectionIndependence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Weil divisor class of an invertible module

Let `(S, δ)` be a Chow situation, let `X` be locally of finite type over `S` with `X` integral of
delta-dimension `n`, and let `L` be an invertible `𝒪_X`-module. The *Weil divisor associated to
`L`* is the class

  `c₁(L) ∩ [X] = class of div_L(s) ∈ CH_{n-1}(X)`

of the divisor of zeros and poles of a nonzero meromorphic section `s` of `L`. This is part (2) of
[Stacks, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ); part (1), the cycle `div_L(s)`
itself, is `Stacks.Chow.divisorOfMeromorphicSection` in
`StacksFrontier.AlgebraicGeometry.Chow.MeromorphicCascade.DivisorCycle`.

The class is well defined because two nonzero meromorphic sections differ by a nonzero rational
function, so their divisors differ by a principal divisor, which is rationally equivalent to zero.
That is `Stacks.Chow.mk_divisorOfMeromorphicSectionCycle_eq`, and a section to start from exists
by [Stacks, Tag 02OZ](https://stacks.math.columbia.edu/tag/02OZ) part (1),
`Stacks.ChernCap42.exists_isRegularMeromorphicSection_of_isIntegral`. The two together make the
definition below unconditional: it quantifies over no section, and the section it chooses is
immaterial by the characterizing equality.

## Main definitions

* `Stacks.Chow.firstChernClassCapFundamental` — the class `c₁(L) ∩ [X] ∈ CH_{n-1}(X)`.

## Main results

* `Stacks.Chow.firstChernClassCapFundamental_eq` — the class is represented by `div_L(s)` for
  every nonzero regular meromorphic section `s` of `L`.

## Implementation notes

The source says "`s` is any nonzero meromorphic section". Here that hypothesis appears as
regularity of `s`, which is what lets `div_L(s)` be formed at all
([Stacks, Tag 0BE6](https://stacks.math.columbia.edu/tag/0BE6)); the nonvanishing
`Stacks.Divisors.genericValue L s ≠ 0` of its value in the generic stalk follows from it on an
integral scheme, by
`Stacks.Divisors.genericValue_ne_zero_of_isRegularMeromorphicSection`, and so is not assumed.
The connection is made over `⊤` rather than in the generic stalk: regularity is a monomorphism
condition, so multiplication by `s` is injective on sections over `⊤`, where `1 ≠ 0` because that
ring is the function field (Tag 01X5 (1)); the identification of meromorphic sections with the
generic stalk (Tag 01X5 (2)) is an additive equivalence and carries the nonvanishing across. The
converse implication is
`Stacks.ChernCap42.isRegularMeromorphicSection_of_genericValue_ne_zero`.

## References

* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 02OZ](https://stacks.math.columbia.edu/tag/02OZ)
* [Stacks Project, Tag 0BE6](https://stacks.math.columbia.edu/tag/0BE6)
* [Stacks Project, Tag 02SH](https://stacks.math.columbia.edu/tag/02SH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  [IsIntegral X] (n : ℤ) (hn : schemeDeltaDimension C p = (n : EInt)) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **The Weil divisor class of an invertible module, Stacks 02SJ (2).** On an integral scheme `X`
of delta-dimension `n`, locally of finite type over the base of a Chow situation, the class

  `c₁(L) ∩ [X] ∈ CH_{n-1}(X)`

of the divisor of zeros and poles of a nonzero meromorphic section of `L`.

An invertible module on an integral scheme has a regular meromorphic section with nonzero generic
value (`Stacks.ChernCap42.exists_isRegularMeromorphicSection_of_isIntegral`), and the class of its
divisor cycle does not depend on which one is taken; the characterizing equality is
`Stacks.Chow.firstChernClassCapFundamental_eq`, which should be used in place of this
definition. -/
@[stacks 02SJ "part (2): the Weil divisor class c₁(L) ∩ [X] in CH_{n-1}(X)",
  sga "5 VII 3.9" "partial"]
def firstChernClassCapFundamental : chowGroup C p (n - 1) :=
  QuotientAddGroup.mk (divisorOfMeromorphicSectionCycle C p n hn L
    (ChernCap42.exists_isRegularMeromorphicSection_of_isIntegral X L).choose
    (ChernCap42.exists_isRegularMeromorphicSection_of_isIntegral X L).choose_spec.1)

/-- **The Weil divisor class is the class of `div_L(s)` for every nonzero section,
Stacks 02SJ (2).** In `CH_{n-1}(X)` the class `c₁(L) ∩ [X]` is represented by the divisor cycle
of *any* nonzero regular meromorphic section of `L`, not only by the one
`Stacks.Chow.firstChernClassCapFundamental` chose. This is the well-definedness the source asserts.

The source's nonvanishing of `s` is not assumed: on an integral scheme it follows from
regularity, by `Stacks.Divisors.genericValue_ne_zero_of_isRegularMeromorphicSection`. See the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.DivisorOfInvertibleSheaf`. -/
@[stacks 02SJ "part (2): c₁(L) ∩ [X] is the class of div_L(s) for every nonzero regular
meromorphic section s, so the definition does not depend on the chosen section"]
theorem firstChernClassCapFundamental_eq
    (s : AlgebraicGeometry.MeromorphicSection X.sheaf L)
    (hs : AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L s) :
    firstChernClassCapFundamental C p n hn L =
      QuotientAddGroup.mk (divisorOfMeromorphicSectionCycle C p n hn L s hs) := by
  refine mk_divisorOfMeromorphicSectionCycle_eq C p hn L _ s _ hs ?_
    (genericValue_ne_zero_of_isRegularMeromorphicSection L s hs)
  exact (ChernCap42.exists_isRegularMeromorphicSection_of_isIntegral X L).choose_spec.2

end Stacks.Chow

end
