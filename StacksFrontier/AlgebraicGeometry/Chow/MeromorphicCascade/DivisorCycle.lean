module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.DivisorCycle
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicCascade.WeilDivisor

/-!
# The divisor cycle of a regular meromorphic section

Let `X` be an integral scheme of delta-dimension `n` locally of finite type over the base scheme
`S` of chapter 42 of the Stacks Project, let `L` be an invertible `𝒪_X`-module and let `s` be a
regular meromorphic section of `L`, that is, a global section of the sheaf `𝒦_X(L)` of meromorphic
sections which is regular. Part (1) of
[Stacks, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ) reads the Weil divisor
`div_L(s) = ∑_Z ord_{Z, L}(s) [Z]` as a cycle of delta-dimension `n - 1`, specified by its
coefficients: the value at the generic point of a prime divisor `Z` is `ord_{Z, L}(s)`, and the
value at a point which is no prime divisor's generic point is `0`.

This is `Stacks.Chow.meromorphicDivisorCycleOfInvertible` — which performs the same construction
for a meromorphic section given by its value in the generic stalk `L_η` — composed with
`Stacks.Divisors.genericValue`, the passage from a section of `𝒦_X(L)` to that value. The two
coefficient specifications are the same statement, so the composition is the construction of the
source.

## Main definitions

* `Stacks.Chow.IsDivisorOfMeromorphicSectionCycle` — the coefficient specification of the cycle.
* `Stacks.Chow.divisorOfMeromorphicSection` — the cycle together with that specification
  (Stacks 02SJ (1)).
* `Stacks.Chow.divisorOfMeromorphicSectionCycle` — the cycle alone.

## Main results

* `Stacks.Chow.divisorOfMeromorphicSectionCycle_genericPoint` and
  `Stacks.Chow.divisorOfMeromorphicSectionCycle_eq_zero` — the two coefficient formulas.

## The rest of Tag 02SJ

Part (2) of the tag — the class `c₁(L) ∩ [X] ∈ CH_{n-1}(X)` of the cycle below, and the fact that
it is represented by the divisor cycle of every nonzero meromorphic section — is
`Stacks.Chow.firstChernClassCapFundamental` in
`StacksFrontier.AlgebraicGeometry.Chow.DivisorOfInvertibleSheaf`.

## References

* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 0BE6](https://stacks.math.columbia.edu/tag/0BE6)
* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
* [Stacks Project, Tag 02OZ](https://stacks.math.columbia.edu/tag/02OZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

/-- The coefficient specification of the divisor cycle of a regular meromorphic section: the value
at the generic point of each prime divisor `Z` is `ord_{Z, L}(s)`, and the value at every point
which is no prime divisor's generic point is zero.

This is `Stacks.Chow.IsWeilDivisorCycle` for the coefficient family of
`Stacks.Divisors.orderOfVanishingMeromorphic`. -/
def IsDivisorOfMeromorphicSectionCycle (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] [IsIntegral X] (n : ℤ) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : AlgebraicGeometry.MeromorphicSection X.sheaf L)
    (hs : AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L s)
    (c : CycleGroup C p (n - 1)) : Prop :=
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  IsWeilDivisorCycle C p n (fun Z : PrimeDivisor X => orderOfVanishingMeromorphic X L s hs Z) c

/-- **The divisor cycle of a regular meromorphic section, Stacks 02SJ (1).** The Weil divisor
`div_L(s)` of a regular meromorphic section of an invertible module on an integral scheme of
delta-dimension `n`, read as a cycle of delta-dimension `n - 1`, together with its coefficient
specification.

The coefficient at the generic point of a prime divisor `Z` is the order of vanishing
`ord_{Z, L}(s)` of Stacks 02SF, and the coefficient at a point which is no prime divisor's generic
point is zero; those are the two components of the subtype obligation, and they are available as
`Stacks.Chow.divisorOfMeromorphicSectionCycle_genericPoint` and
`Stacks.Chow.divisorOfMeromorphicSectionCycle_eq_zero`. -/
@[stacks 02SJ "part (1): div_L(s) = ∑_Z ord_{Z, L}(s) [Z] as an element of Z_{n-1}(X), together
with its coefficients"]
def divisorOfMeromorphicSection (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] [IsIntegral X] (n : ℤ)
    (hn : schemeDeltaDimension C p = (n : EInt)) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : AlgebraicGeometry.MeromorphicSection X.sheaf L)
    (hs : AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L s) :
    { c : CycleGroup C p (n - 1) // IsDivisorOfMeromorphicSectionCycle C p n L s hs c } :=
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have := isInvertible_presheaf L
  meromorphicDivisorCycleOfInvertible C p hn L (genericValue L s)

section

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  [IsIntegral X] (n : ℤ) (hn : schemeDeltaDimension C p = (n : EInt)) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : AlgebraicGeometry.MeromorphicSection X.sheaf L)
  (hs : AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L s)

/-- The divisor cycle of a regular meromorphic section, without its coefficient
specification. -/
abbrev divisorOfMeromorphicSectionCycle : CycleGroup C p (n - 1) :=
  (divisorOfMeromorphicSection C p n hn L s hs).val

/-- The coefficient of `div_L(s)` at the generic point of a prime divisor `Z` is the order of
vanishing of `s` along `Z`. -/
@[simp]
theorem divisorOfMeromorphicSectionCycle_genericPoint (Z : PrimeDivisor X) :
    ((divisorOfMeromorphicSectionCycle C p n hn L s hs : CycleGroup C p (n - 1)) :
        AlgebraicCycle X ℤ) Z.genericPoint =
      letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
      orderOfVanishingMeromorphic X L s hs Z :=
  (divisorOfMeromorphicSection C p n hn L s hs).property.1 Z

/-- The divisor cycle vanishes at every point which is not the generic point of a prime
divisor. -/
theorem divisorOfMeromorphicSectionCycle_eq_zero (x : X)
    (hx : ∀ Z : PrimeDivisor X, Z.genericPoint ≠ x) :
    ((divisorOfMeromorphicSectionCycle C p n hn L s hs : CycleGroup C p (n - 1)) :
      AlgebraicCycle X ℤ) x = 0 :=
  (divisorOfMeromorphicSection C p n hn L s hs).property.2 x hx

end

end Stacks.Chow

end
