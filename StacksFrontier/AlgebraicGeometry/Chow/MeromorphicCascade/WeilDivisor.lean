module

public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicCascade.OrderOfVanishing

/-!
# The Weil divisor of a regular meromorphic section

Let `X` be a locally Noetherian integral scheme, let `L` be an invertible `𝒪_X`-module and let `s`
be a regular meromorphic section of `L`. The orders of vanishing of `s` along the prime divisors
of `X` form a Weil divisor

`div_L(s) = ∑_Z ord_{Z, L}(s) [Z] ∈ Div(X)`,

which is part (1) of [Stacks, Tag 0BE6](https://stacks.math.columbia.edu/tag/0BE6). The
finiteness which makes this a divisor at all is Stacks 02SG: `s` generates `L` over some nonempty
open set, so only the prime divisors in the complement contribute.

Both halves are already in the library. `Stacks.Divisors.weilDivisorOfMeromorphicSection` is the
divisor of a meromorphic section given by its value in the generic stalk, with the local
finiteness proved (`Stacks.Divisors.locallyFinite_orderOfVanishing_ne_zero`); this file composes it
with `Stacks.Divisors.genericValue`, so that the input is a global section of the sheaf `𝒦_X(L)`
of meromorphic sections as in the source, and discharges the rank-one hypothesis by
`Stacks.Divisors.isTrivializedNear_of_isInvertible`.

## Main definitions

* `Stacks.Divisors.weilDivisorOfRegularMeromorphicSection` — `div_L(s) ∈ Div(X)` for a regular
  meromorphic section `s` of `L` (Stacks 0BE6 (1)).

## Main results

* `Stacks.Divisors.weilDivisorOfRegularMeromorphicSection_apply` — its coefficient at a prime
  divisor is the order of vanishing there.

## What this is not

No declaration here carries the `@[stacks 0BE6]` attribute. The covering set of that tag has three
members: part (1), the divisor above; and the two halves of part (2), the class of `div_L(s)` in
the Weil divisor class group `Cl(X)` and the independence of that class of the chosen section.
Part (2) needs `Cl(X)` — [Stacks, Tag 0BE4](https://stacks.math.columbia.edu/tag/0BE4), which
requires a `Stacks.Divisors.WeilDivisor`-shaped principal divisor and is not in this library — and
the existence of a regular meromorphic section,
[Stacks, Tag 0BE4](https://stacks.math.columbia.edu/tag/0BE4) resp.
[Stacks, Tag 02OZ](https://stacks.math.columbia.edu/tag/02OZ) (1). Tagging part (1) alone would
report the whole tag as formalized.

## References

* [Stacks Project, Tag 0BE6](https://stacks.math.columbia.edu/tag/0BE6)
* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
* [Stacks Project, Tag 02SG](https://stacks.math.columbia.edu/tag/02SG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Divisors

/-- **The Weil divisor of a regular meromorphic section of an invertible module, Stacks 0BE6
(1).** `div_L(s) = ∑_Z ord_{Z, L}(s) [Z]`, the sum being over the prime divisors of `X`; local
finiteness is Stacks 02SG.

No Stacks attribute is attached; see the module documentation. -/
def weilDivisorOfRegularMeromorphicSection (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : AlgebraicGeometry.MeromorphicSection X.sheaf L)
    (_hs : AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L s) : WeilDivisor X :=
  have := isInvertible_presheaf L
  weilDivisorOfMeromorphicSection (L := L) (isTrivializedNear_of_isInvertible L)
    (genericValue L s)

variable (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X] (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : AlgebraicGeometry.MeromorphicSection X.sheaf L)
  (hs : AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L s)

/-- The coefficient of `div_L(s)` at a prime divisor is the order of vanishing of `s` there. -/
@[simp]
theorem weilDivisorOfRegularMeromorphicSection_apply (Z : PrimeDivisor X) :
    (weilDivisorOfRegularMeromorphicSection X L s hs).val Z =
      orderOfVanishingMeromorphic X L s hs Z :=
  rfl

end Stacks.Divisors

end
