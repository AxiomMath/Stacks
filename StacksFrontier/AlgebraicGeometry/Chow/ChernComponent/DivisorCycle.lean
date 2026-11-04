module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.Trivialization
public import StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder

/-!
# The divisor cycle of a meromorphic section of an invertible module

Let `X` be an integral scheme of delta-dimension `n` locally of finite type over the base scheme
`S` of chapter 42 of the Stacks Project, let `L` be an invertible `𝒪_X`-module and let `s` be a
nonzero meromorphic section of `L`. Stacks 02SJ turns the Weil divisor
`div_L(s) = ∑_Z ord_{Z, L}(s) [Z]` into a cycle of delta-dimension `n - 1`, specified by its
coefficients: the value at the generic point of a prime divisor `Z` is `ord_{Z, L}(s)`, and the
value at every point which is no prime divisor's generic point is `0`.

Both halves of that passage are already in the library. The divisor is
`Stacks.Divisors.weilDivisorOfMeromorphicSection` (Stacks 0BE6 (1)) and the passage from a Weil
divisor to a cycle of delta-dimension `n - 1` is `Stacks.Chow.weilDivisorCycleOfDeltaDimension`,
which chapter 42 performs with the identical argument for the principal divisor of a rational
function (Stacks 02RO). This file is their composition, together with the discharge of the
rank-one hypothesis for an invertible module by
`Stacks.Divisors.isTrivializedNear_of_isInvertible`.

## Why nothing below carries `@[stacks 02SJ]`

Stacks 02SJ states the construction for a global section `s` of the sheaf `K_X(L)` of meromorphic
sections of `L` which is regular. The model used here is the one of
`StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder`: on an integral scheme `K_X(L)` is the
constant sheaf with value the generic stalk `L_η` (Stacks 01X5 (2)), so a meromorphic section is
an element of `L_η` and regularity is nonvanishing. The declarations below are stated in that
model and in it alone, which is why they carry no `@[stacks 02SJ]` attribute.

The identification itself is no longer the obstruction, and a reader should not set out to prove
it. Stacks 01X5 (2) is `Stacks.AlgebraicGeometry.meromorphicSectionSheafIsoConstant`
(`StacksFrontier/AlgebraicGeometry/MeromorphicConstantModule/Basic.lean:568`, registered
`@[stacks 01X5 "part (2)"]`), with the comparison in the shape this directory uses available as
`Stacks.Divisors.meromorphicSectionsAddEquivGenericStalk`
(`StacksFrontier/AlgebraicGeometry/Chow/MeromorphicSheafComparison/Comparison.lean:188`); and Stacks
02OW (2), on which it rests, is formalized in fifteen places, among them
`StacksFrontier/AlgebraicGeometry/ReducedTotalQuotient/Basic.lean:86`.

Nor is the Chow class of Stacks 02SJ (2) absent any longer. It is
`Stacks.Chow.firstChernClassCapFundamental`, with its characterizing equality
`Stacks.Chow.firstChernClassCapFundamental_eq`
(`StacksFrontier/AlgebraicGeometry/Chow/DivisorOfInvertibleSheaf.lean:87, 102`, both registered
`@[stacks 02SJ]` for part (2)), and the choice of section is legitimate there because Stacks 02OZ
(1) is proved
(`StacksFrontier/AlgebraicGeometry/Divisors/Meromorphic/RegularSectionExistence.lean:194`), with
`Stacks.Divisors.exists_ne_zero_genericStalk` supplying the section in the model used here. The
independence of the class from the section, in this model, is
`Stacks.Chow.mk_chernComponentCycle_eq`
(`StacksFrontier/AlgebraicGeometry/Chow/MeromorphicSectionIndependence.lean:259`).

All of those modules are downstream of this one, so the citations are forward references.

## Main definitions

* `Stacks.Chow.meromorphicDivisorCycle` — the cycle of `div_L(s)` with its coefficient
  specification, for a module trivialized near every point.
* `Stacks.Chow.meromorphicDivisorCycleOfInvertible` — the same for an invertible module, the
  hypothesis being discharged.

## Main results

* `Stacks.Chow.meromorphicDivisorCycle_genericPoint` and
  `Stacks.Chow.meromorphicDivisorCycle_eq_zero` — the two coefficient formulas.

## References

* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 0BE6](https://stacks.math.columbia.edu/tag/0BE6)
* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  [IsIntegral X] [IsLocallyNoetherian X] {n : ℤ}
  (hn : schemeDeltaDimension C p = (n : EInt)) {L : X.Modules}

/-- **The divisor cycle of a meromorphic section**, the construction of Stacks 02SJ (1) in the
generic-stalk model: the Weil divisor `div_L(s) = ∑_Z ord_{Z, L}(s) [Z]` of a meromorphic section
`s ∈ L_η`, read as a cycle of delta-dimension `n - 1` on an integral scheme of delta-dimension
`n`, together with its coefficient specification.

The rank-one hypothesis on `L` is `Stacks.Divisors.IsTrivializedNear` at every point, as
throughout `StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder`; for an invertible module use
`Stacks.Chow.meromorphicDivisorCycleOfInvertible`. The local Noetherianity of `X` is an instance
hypothesis only because `Stacks.Divisors.orderOfVanishing` is stated under it; it follows from
the other hypotheses by `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`.

No Stacks attribute is attached; see the module documentation. -/
def meromorphicDivisorCycle (hL : ∀ x : X, IsTrivializedNear L x)
    (s : L.presheaf.stalk (genericPoint X)) :
    { c : CycleGroup C p (n - 1) //
      IsWeilDivisorCycle C p n (fun Z : PrimeDivisor X => orderOfVanishing L s Z) c } :=
  weilDivisorCycleOfDeltaDimension C p hn (weilDivisorOfMeromorphicSection hL s)

/-- The coefficient of the divisor cycle at the generic point of a prime divisor `Z` is the order
of vanishing of `s` along `Z`. -/
@[simp]
theorem meromorphicDivisorCycle_genericPoint (hL : ∀ x : X, IsTrivializedNear L x)
    (s : L.presheaf.stalk (genericPoint X)) (Z : PrimeDivisor X) :
    ((meromorphicDivisorCycle C p hn hL s).val : AlgebraicCycle X ℤ) Z.genericPoint =
      orderOfVanishing L s Z :=
  (meromorphicDivisorCycle C p hn hL s).property.1 Z

/-- The divisor cycle vanishes at every point which is not the generic point of a prime
divisor. -/
theorem meromorphicDivisorCycle_eq_zero (hL : ∀ x : X, IsTrivializedNear L x)
    (s : L.presheaf.stalk (genericPoint X)) (x : X)
    (hx : ∀ Z : PrimeDivisor X, Z.genericPoint ≠ x) :
    ((meromorphicDivisorCycle C p hn hL s).val : AlgebraicCycle X ℤ) x = 0 :=
  (meromorphicDivisorCycle C p hn hL s).property.2 x hx

/-- The divisor cycle of a meromorphic section of an **invertible** module: the rank-one
hypothesis of `Stacks.Chow.meromorphicDivisorCycle` is discharged by
`Stacks.Divisors.isTrivializedNear_of_isInvertible`.

No Stacks attribute is attached; see the module documentation. -/
def meromorphicDivisorCycleOfInvertible (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (s : L.presheaf.stalk (genericPoint X)) :
    { c : CycleGroup C p (n - 1) //
      IsWeilDivisorCycle C p n (fun Z : PrimeDivisor X => orderOfVanishing L s Z) c } :=
  meromorphicDivisorCycle C p hn (isTrivializedNear_of_isInvertible L) s

end Stacks.Chow

end
