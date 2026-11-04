module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.Trivialization
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicCascade.GenericValue
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicCascade.StalkBasis
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The order of vanishing of a meromorphic section along a prime divisor

Let `X` be a locally Noetherian integral scheme, let `L` be an invertible `𝒪_X`-module and let `s`
be a regular meromorphic section of `L`, that is, a global section of the sheaf `𝒦_X(L)` of
meromorphic sections of `L` which is regular in the sense of
[Stacks, Tag 02OX](https://stacks.math.columbia.edu/tag/02OX). For a prime divisor `Z ⊆ X` with
generic point `ξ` the Stacks Project attaches to `s` the integer

`ord_{Z, L}(s) = ord_{𝒪_{X, ξ}}(s / s_ξ)`,

where `s_ξ` is a generator of the stalk `L_ξ` and `s / s_ξ` is the rational function expressing `s`
in terms of it; the integer does not depend on the choice of `s_ξ`, two generators differing by a
unit of `𝒪_{X, ξ}`.

All of the mathematics is already in `StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder`, which
defines `Stacks.Divisors.orderOfVanishing` for a meromorphic section given by its value in the
generic stalk `L_η` and under the explicit rank-one hypothesis
`Stacks.Divisors.IsTrivializedNear`. This file is the composition of that definition with the two
bridges which have since been proved: `Stacks.Divisors.genericValue`, which passes from a section
of `𝒦_X(L)` to its value in `L_η`, and
`Stacks.Divisors.isTrivializedNear_of_isInvertible`, which discharges the rank-one hypothesis for
an invertible module. The result is the construction of the source, and it is what carries the
`@[stacks 02SF]` attribute.

## Main definitions

* `Stacks.Divisors.orderOfVanishingMeromorphic` — `ord_{Z, L}(s)` for a regular meromorphic
  section `s` of `L` (Stacks 02SF).

## Main results

* `Stacks.Divisors.exists_isCoordinateAt_genericValue` — a regular meromorphic section has a
  coordinate at every point.
* `Stacks.Divisors.orderOfVanishingMeromorphic_eq` — the characterization of `ord_{Z, L}(s)`: it is
  the order of vanishing in `𝒪_{X, ξ}` of any coordinate of `s` at `ξ`. This is what should be
  used in place of the definition.
* `Stacks.Divisors.orderOfVanishingMeromorphic_spec` — the two previous results combined into the
  specification of the source: some generator of `L_ξ` has a coordinate, and every coordinate with
  respect to every generator computes `ord_{Z, L}(s)`. Being a generator of `L_ξ` and being a basis
  of it agree, by `Stacks.Divisors.isStalkBasis_iff_span_eq_top`.

## References

* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
* [Stacks Project, Tag 01X4](https://stacks.math.columbia.edu/tag/01X4)
* [Stacks Project, Tag 02OX](https://stacks.math.columbia.edu/tag/02OX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Divisors

/-- **The order of vanishing of a regular meromorphic section along a prime divisor, Stacks
02SF.** The meromorphic section is a global section `s` of the sheaf `𝒦_X(L)` of meromorphic
sections of `L`; its order along `Z` is the order of vanishing, in the local ring at the generic
point of `Z`, of the rational function expressing the generic value of `s` in terms of a generator
of the stalk of `L` there.

`Stacks.Divisors.orderOfVanishingMeromorphic_eq` is the characterization, and it is what should be
used rather than this definition. -/
@[stacks 02SF, ega "IV 21.6.7" "o_x(f) = mult_x(div f)"]
def orderOfVanishingMeromorphic (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : AlgebraicGeometry.MeromorphicSection X.sheaf L)
    (_hs : AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L s)
    (Z : PrimeDivisor X) : ℤ :=
  orderOfVanishing L (genericValue L s) Z

section

variable (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X] (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : AlgebraicGeometry.MeromorphicSection X.sheaf L)
  (hs : AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L s)

/-- The order of vanishing of a meromorphic section is the order of vanishing of its generic
value, which is the model of a meromorphic section used in
`StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder`. -/
theorem orderOfVanishingMeromorphic_eq_orderOfVanishing (Z : PrimeDivisor X) :
    orderOfVanishingMeromorphic X L s hs Z = orderOfVanishing L (genericValue L s) Z :=
  rfl

omit [IsLocallyNoetherian X] in
/-- A regular meromorphic section of an invertible module has a coordinate at every point: a
rational function expressing its generic value in terms of a basis of the stalk there. This is the
existence half of the specification of Stacks 02SF. -/
theorem exists_isCoordinateAt_genericValue (x : X) :
    ∃ a : X.functionField, IsCoordinateAt L x (genericValue L s) a :=
  have := isInvertible_presheaf L
  exists_isCoordinateAt (isTrivializedNear_of_isInvertible L x) (genericValue L s)

/-- **The characterization of the order of vanishing, Stacks 02SF.** The order of vanishing of a
regular meromorphic section `s` of `L` along a prime divisor `Z` is the order of vanishing in the
local ring at the generic point of `Z` of any coordinate of `s` there.

Together with `Stacks.Divisors.exists_isCoordinateAt_genericValue` this is the specification of
the source: a coordinate exists, and every coordinate computes the same integer. -/
theorem orderOfVanishingMeromorphic_eq {Z : PrimeDivisor X} {a : X.functionField}
    (ha : IsCoordinateAt L Z.genericPoint (genericValue L s) a) :
    orderOfVanishingMeromorphic X L s hs Z = X.ord a Z.genericPoint :=
  have := isInvertible_presheaf L
  orderOfVanishing_eq (isTrivializedNear_of_isInvertible L Z.genericPoint) ha

/-- **The specification of the order of vanishing, Stacks 02SF.** Writing `ξ` for the generic
point of the prime divisor `Z` and `R(X)` for the function field: some generator `m` of the stalk
`L_ξ` admits an `a ∈ R(X)` with `s = a · m` generically, and for every generator `m` of `L_ξ` and
every such `a` the order of vanishing of `s` along `Z` is the order of vanishing of `a` in
`𝒪_{X, ξ}`.

This is the subtype obligation the Stacks Project attaches to the construction, with the generators
quantified over as in the source; `Stacks.Divisors.isStalkBasis_iff_span_eq_top` is what identifies
a generator of `L_ξ` with a basis of it. -/
theorem orderOfVanishingMeromorphic_spec (Z : PrimeDivisor X) :
    (∃ m : L.presheaf.stalk Z.genericPoint,
        Submodule.span ↑(X.presheaf.stalk Z.genericPoint) {m} = ⊤ ∧
        ∃ a : X.functionField,
          genericValue L s = a • toGenericStalk L Z.genericPoint m) ∧
      ∀ m : L.presheaf.stalk Z.genericPoint,
        Submodule.span ↑(X.presheaf.stalk Z.genericPoint) {m} = ⊤ →
        ∀ a : X.functionField, genericValue L s = a • toGenericStalk L Z.genericPoint m →
          orderOfVanishingMeromorphic X L s hs Z = X.ord a Z.genericPoint := by
  refine ⟨?_, fun m hm a ha => orderOfVanishingMeromorphic_eq X L s hs
    ⟨m, (isStalkBasis_iff_span_eq_top L _ m).mpr hm, ha⟩⟩
  obtain ⟨a, m, hm, ha⟩ := exists_isCoordinateAt_genericValue X L s Z.genericPoint
  exact ⟨m, (isStalkBasis_iff_span_eq_top L _ m).mp hm, a, ha⟩

end

end Stacks.Divisors

end
