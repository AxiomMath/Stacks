module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.CapProduct
public import StacksFrontier.AlgebraicGeometry.Chow.DivisorOfInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ChernCapDischarge
public import StacksCore.Tactic.StacksAttribute

/-!
# Intersecting with two first Chern classes commutes on divisors

Let `X` be an integral scheme locally of finite type over the base scheme `S` of chapter 42 of the
Stacks Project, of delta-dimension `n`, and let `L` and `N` be invertible `𝒪_X`-modules with
nonzero meromorphic sections `s` and `t`. Stacks 02TH asserts

  `c₁(N) ∩ div_L(s) = c₁(L) ∩ div_N(t)`  in  `CH_{n-2}(X)`.

The source's proof is the key formula of Stacks 0AYC for the situation of Stacks 0AYB built from
`s` and `t`. Both are available with no hypothesis, and
`Stacks.Chow.firstChernClassCapOfInvertible_divisorCycle_comm` assembles them for meromorphic
sections given by their values in the generic stalks `L_η`, `N_η`, on a scheme of
delta-dimension `k + 2`. This file restates that result for the objects of record: the
meromorphic sections are global sections of the sheaves `𝒦_X(L)`, `𝒦_X(N)` of Stacks 01X4, the
divisors are the cycles `div_L(s)`, `div_N(t)` of Stacks 02SJ (1)
(`Stacks.Chow.divisorOfMeromorphicSectionCycle`), the cap products are those of Stacks 02SO
(`Stacks.Chow.firstChernClassCapOfInvertible`), and the delta-dimension is an arbitrary integer
`n`, with the conclusion in `CH_{n-2}(X)`.

The comparison is definitional: `div_L(s)` of Stacks 02SJ (1) is by construction the divisor
cycle of the generic value of `s`, and the only difference is the grading `n - 1` versus
`(n - 2) + 1`, crossed with `Stacks.Chow.cycleGroupOfEq`.

## Main results

* `Stacks.Chow.firstChernClassCapOfInvertible_divisorOfMeromorphicSection_comm` —
  **Stacks 02TH**.

## Implementation notes

The source's "nonzero meromorphic section" is the regularity hypothesis on `s` and `t`, which is
what the divisor cycle `Stacks.Chow.divisorOfMeromorphicSectionCycle` of Stacks 02SJ (1) is
formed from. On an integral scheme the two are equivalent: a regular meromorphic section has
nonzero generic value (`Stacks.Divisors.genericValue_ne_zero_of_isRegularMeromorphicSection`), and
conversely (`Stacks.ChernCap42.isRegularMeromorphicSection_of_genericValue_ne_zero`), the generic
value being the image of the section over `X` under an additive equivalence (Stacks 01X5).

## References

* [Stacks Project, Tag 02TH](https://stacks.math.columbia.edu/tag/02TH)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

open Stacks.Divisors

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  [IsIntegral X]

/-- The divisor cycle `div_L(s)` of Stacks 02SJ (1), on a scheme of delta-dimension `n`, read in
degree `(n - 2) + 1`, is the divisor cycle of the generic value of `s` on the same scheme read as
having delta-dimension `(n - 2) + 2`. -/
theorem cycleGroupOfEq_divisorOfMeromorphicSectionCycle (n : ℤ)
    (hn : schemeDeltaDimension C p = (n : EInt))
    (hn' : schemeDeltaDimension C p = ((n - 2 + 2 : ℤ) : EInt)) (h : n - 1 = n - 2 + 1)
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : AlgebraicGeometry.MeromorphicSection X.sheaf L)
    (hs : AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L s) :
    cycleGroupOfEq h (divisorOfMeromorphicSectionCycle C p n hn L s hs) =
      divisorCycleOfInvertibleSection C p hn' L (genericValue L s) :=
  Subtype.ext rfl

/-- **Stacks 02TH.** Let `X` be integral and locally of finite type over the base scheme `S` of
chapter 42, with `dim_δ(X) = n`, let `L` and `N` be invertible `𝒪_X`-modules, and let `s` and `t`
be nonzero (that is, regular) meromorphic sections of `L` and `N`. Writing `α = div_L(s)` and
`β = div_N(t)` for their divisor cycles of Stacks 02SJ (1),

  `c₁(N) ∩ α = c₁(L) ∩ β`  in  `CH_{n-2}(X)`.

The cycles of degree `n - 1` are read in degree `(n - 2) + 1`, the source of the cap product
`CH_{(n-2)+1} → CH_{n-2}`, by `Stacks.Chow.cycleGroupOfEq`. The proof is the key formula of
Stacks 0AYC, through `Stacks.Chow.firstChernClassCapOfInvertible_divisorCycle_comm`. -/
@[stacks 02TH]
theorem firstChernClassCapOfInvertible_divisorOfMeromorphicSection_comm (n : ℤ)
    (hn : schemeDeltaDimension C p = (n : EInt)) (L N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (s : AlgebraicGeometry.MeromorphicSection X.sheaf L)
    (hs : AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L s)
    (t : AlgebraicGeometry.MeromorphicSection X.sheaf N)
    (ht : AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf N t) :
    firstChernClassCapOfInvertible C p (n - 2) N
        (cycleGroupOfEq (by ring) (divisorOfMeromorphicSectionCycle C p n hn L s hs)) =
      firstChernClassCapOfInvertible C p (n - 2) L
        (cycleGroupOfEq (by ring) (divisorOfMeromorphicSectionCycle C p n hn N t ht)) := by
  have hn' : schemeDeltaDimension C p = ((n - 2 + 2 : ℤ) : EInt) := by
    rw [sub_add_cancel]
    exact hn
  rw [cycleGroupOfEq_divisorOfMeromorphicSectionCycle C p n hn hn',
    cycleGroupOfEq_divisorOfMeromorphicSectionCycle C p n hn hn']
  exact firstChernClassCapOfInvertible_divisorCycle_comm C p hn' L N
    (genericValue_ne_zero_of_isRegularMeromorphicSection L s hs)
    (genericValue_ne_zero_of_isRegularMeromorphicSection N t ht)

end Stacks.Chow

end
