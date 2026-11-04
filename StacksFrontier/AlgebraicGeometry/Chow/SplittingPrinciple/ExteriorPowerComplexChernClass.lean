module

public import Mathlib.Algebra.Ring.NegOnePow
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassComplexLocallyBounded
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.ExteriorPowerChernProduct
public import StacksCore.Tactic.StacksAttribute

/-!
# The total Chern class of an exterior-power complex

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, Stacks 02QL, let `X` be
locally of finite type over `S` and let `V` be a finite locally free `𝒪_X`-module of rank `r`. A
**exterior-power complex** of `V` is a cochain complex `K` with

  `K^n = ⋀^{-n} V`,

so that `K` is concentrated in the cohomological degrees `-r, …, 0` with `K^{-n} = ⋀ⁿ V`; the
Koszul complex of a section of the dual of `V` is one, and that is the only source of them here.
This file computes the total Chern class of such a complex:

  `c(K) = ∏_{n = 0}^{r} c(⋀ⁿ V)^{(-1)ⁿ}`,

the alternating product of
`StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.ExteriorPowerChernProduct`, and reads
Stacks 0FEE off it: the components of `c(K)` vanish in the degrees `1, …, r-1` and the component
in degree `r` is `-(r-1)! c_r(V)`.

## Main results

* `Stacks.Chow.totalChernClassComplex_eq_altExteriorChernProduct` — the identification of the
  alternating product over the *complex*, Stacks 0ESZ, with the alternating product over the
  *exterior powers*, the left-hand side of Stacks 0FEE. This is a reindexing: the degree-`n` term
  of the first is the degree-`(r-n)` term of the second, and the two signs agree because the sign
  of Stacks 0ESZ is that of the cohomological degree.
* `Stacks.Chow.totalChernClassComplex_exteriorPowerComplex_apply` — the two conclusions of
  Stacks 0FEE transported to the complex.
* `Stacks.Chow.totalChernClassComplexLocallyBounded_exteriorPowerComplex_apply` — the same for
  the locally bounded class of Stacks 0ESZ on a quasi-compact scheme, which is the form that the
  Chern classes of an object of `D(𝒪_X)` are defined through.

## Why this is not Stacks 0FEE again

Stacks 0FEE is an identity between elements of `A^*(X)^∧` indexed by the exterior powers of a
module; it says nothing about any complex. What is proved here is that the total Chern class of
Stacks 0ESZ — defined through the alternating class
`Stacks.Chow.alternatingKClass` of the complex in `K_0(Vect(X))` — of a complex whose terms are
the exterior powers of `V` *is* that element. The two products run over opposite orders of the
same factors, and the sign convention of Stacks 0ESZ is the sign of the cohomological degree,
which for `K^{-n} = ⋀ⁿ V` is `(-1)ⁿ`; neither fact is part of Stacks 0FEE.

No Koszul differential is mentioned: only the *terms* of the complex enter the total Chern class
of Stacks 0ESZ, and so the hypothesis here is on the terms alone.

## References

* [Stacks Project, Tag 0FEE](https://stacks.math.columbia.edu/tag/0FEE)
* [Stacks Project, Tag 0ESZ](https://stacks.math.columbia.edu/tag/0ESZ)
* [Stacks Project, Tag 0FEF](https://stacks.math.columbia.edu/tag/0FEF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Finset

universe u

namespace Stacks.Chow

open ChowCohomologySeriesRing

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] {R : ChowCohomologySeriesRing C G sX}

/-! ### Exterior-power complexes -/

/-- A cochain complex is an **exterior-power complex** of `V` when its term in cohomological
degree `n` is the exterior power `⋀^{-n} V`. Only the terms are constrained: the differential is
unconstrained, because the total Chern class of Stacks 0ESZ depends on the terms alone. -/
public def IsExteriorPowerComplex (V : X.Modules) (K : CochainComplex X.Modules ℤ) : Prop :=
  ∀ n : ℤ, K.X n = AlgebraicGeometry.Scheme.Modules.exteriorPower V (-n)

/-- The Koszul-style window: an exterior-power complex of a module of rank `r` has its terms in
the cohomological degrees `-r, …, 0`, provided the exterior powers above `r` and below `0`
vanish. The vanishing is a hypothesis rather than a consequence here; it is what
`Stacks.Chow.totalChernClassComplexLocallyBounded_exteriorPowerComplex_apply` consumes. -/
public theorem isZero_X_outside_of_isExteriorPowerComplex {V : X.Modules} {r : ℕ}
    {K : CochainComplex X.Modules ℤ} (hK : IsExteriorPowerComplex V K)
    (hvanish : ∀ n : ℤ, (n < 0 ∨ (r : ℤ) < n) →
      IsZero (AlgebraicGeometry.Scheme.Modules.exteriorPower V n)) (n : ℤ)
    (hn : n < -(r : ℤ) ∨ -(r : ℤ) + (r : ℤ) < n) : IsZero (K.X n) := by
  rw [hK n]
  exact hvanish (-n) (by omega)

/-! ### The total Chern class of an exterior-power complex -/

/-- **The total Chern class of an exterior-power complex is the alternating product of the total
Chern classes of the exterior powers.** The left-hand side is the class of Stacks 0ESZ on the
window `-r, …, 0`; the right-hand side is the left-hand side of Stacks 0FEE. The proof is the
reindexing `n ↦ r - n` of the two products together with the agreement of the signs: the sign of
Stacks 0ESZ is that of the cohomological degree, and the degree carrying `⋀ⁿ V` is `-n`. -/
public theorem totalChernClassComplex_eq_altExteriorChernProduct
    (D : TotalChernClassSeries C G sX R) {V : X.Modules} (r : ℕ)
    {K : CochainComplex X.Modules ℤ} (hK : IsExteriorPowerComplex V K) :
    totalChernClassComplex C G sX D K (-(r : ℤ)) r = altExteriorChernProduct D V r := by
  classical
  rw [totalChernClassComplex_eq_prod, altExteriorChernProduct]
  set f : ℕ → UnitalSeries R := fun n =>
    (⟨D.ch (AlgebraicGeometry.Scheme.Modules.exteriorPower V (n : ℤ)),
        D.ch_apply_zero (AlgebraicGeometry.Scheme.Modules.exteriorPower V (n : ℤ))⟩ :
      UnitalSeries R) ^ ((-1 : ℤ) ^ n) with hf
  have hrefl : ∏ n ∈ Finset.range (r + 1), f n = ∏ i ∈ Finset.range (r + 1), f (r - i) := by
    refine (Finset.prod_range_reflect f (r + 1)).symm.trans (Finset.prod_congr rfl fun i _ => ?_)
    congr 1
  rw [hrefl]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hir : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hneg : -(r : ℤ) + (i : ℤ) = -((r - i : ℕ) : ℤ) := by
    rw [Nat.cast_sub hir]; ring
  have hbase : K.X (-(r : ℤ) + (i : ℤ))
      = AlgebraicGeometry.Scheme.Modules.exteriorPower V ((r - i : ℕ) : ℤ) := by
    rw [hK, hneg, neg_neg]
  have hexp : (((-(r : ℤ) + (i : ℤ)).negOnePow : ℤ)) = (-1 : ℤ) ^ (r - i) := by
    rw [hneg, Int.negOnePow_neg, Int.coe_negOnePow_natCast]
  rw [hf]
  rw [show (⟨D.ch (K.X (-(r : ℤ) + (i : ℤ))), D.ch_apply_zero (K.X (-(r : ℤ) + (i : ℤ)))⟩ :
        UnitalSeries R)
      = ⟨D.ch (AlgebraicGeometry.Scheme.Modules.exteriorPower V ((r - i : ℕ) : ℤ)),
          D.ch_apply_zero (AlgebraicGeometry.Scheme.Modules.exteriorPower V ((r - i : ℕ) : ℤ))⟩
      from Subtype.ext (congrArg D.ch hbase), hexp]

/-- **Stacks 0FEE for an exterior-power complex.** For `V` finite locally free of rank `r ≥ 1`
with Chern roots, the total Chern class of an exterior-power complex of `V` vanishes in the
degrees `1, …, r-1` and is `-(r-1)! c_r(V)` in degree `r`. Nothing is asserted in the higher
degrees, which is the `+ …` of Stacks 0FEE.

The Chern roots are carried exactly as in `Stacks.Chow.altExteriorChernProduct_apply`: the
hypotheses `hroots` and `hwedge` are the displays `c(V) = ∏ (1 + x_i)` and
`c(⋀ⁿ V) = ∏_{#I = n} (1 + ∑_{i ∈ I} x_i)` of the source's proof, which are the splitting
principle and are not available in this repository. -/
public theorem totalChernClassComplex_exteriorPowerComplex_apply
    (D : TotalChernClassSeries C G sX R) {V : X.Modules} {r : ℕ}
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} V r] (hr : r ≠ 0)
    {K : CochainComplex X.Modules ℤ} (hK : IsExteriorPowerComplex V K)
    (x : Fin r → chowCohomologyComponent C G sX 1)
    (hroots : D.ch V = (∏ i, oneAddDegreeOne R (x i) : UnitalSeries R).1)
    (hwedge : ∀ n ≤ r, D.ch (AlgebraicGeometry.Scheme.Modules.exteriorPower V (n : ℤ))
      = (rootTotalChern R x ((Finset.univ : Finset (Fin r)).powersetCard n)).1) :
    (∀ n, 0 < n → n < r →
        (totalChernClassComplex C G sX D K (-(r : ℤ)) r).1 n = 0) ∧
      (totalChernClassComplex C G sX D K (-(r : ℤ)) r).1 r
        = -(Nat.factorial (r - 1) • D.ch V r) := by
  rw [totalChernClassComplex_eq_altExteriorChernProduct C G sX D r hK]
  exact altExteriorChernProduct_apply D V hr x hroots hwedge

/-- **Stacks 0FEE for the locally bounded total Chern class of an exterior-power complex.** The
locally bounded class of Stacks 0ESZ on a quasi-compact scheme agrees with the class on the window
`-r, …, 0`, so the two conclusions of
`Stacks.Chow.totalChernClassComplex_exteriorPowerComplex_apply` hold for it. This is the form in
which the Chern classes of an object of `D(𝒪_X)` are defined, Stacks 0F9E (1). -/
public theorem totalChernClassComplexLocallyBounded_exteriorPowerComplex_apply [CompactSpace X]
    (D : TotalChernClassSeries C G sX R) {V : X.Modules} {r : ℕ}
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} V r] (hr : r ≠ 0)
    {K : CochainComplex X.Modules ℤ} (hKP : IsLocallyBoundedFiniteLocallyFree K)
    (hK : IsExteriorPowerComplex V K)
    (hvanish : ∀ n : ℤ, (n < 0 ∨ (r : ℤ) < n) →
      IsZero (AlgebraicGeometry.Scheme.Modules.exteriorPower V n))
    (x : Fin r → chowCohomologyComponent C G sX 1)
    (hroots : D.ch V = (∏ i, oneAddDegreeOne R (x i) : UnitalSeries R).1)
    (hwedge : ∀ n ≤ r, D.ch (AlgebraicGeometry.Scheme.Modules.exteriorPower V (n : ℤ))
      = (rootTotalChern R x ((Finset.univ : Finset (Fin r)).powersetCard n)).1) :
    (∀ n, 0 < n → n < r →
        (totalChernClassComplexLocallyBounded C G sX D K hKP).1 n = 0) ∧
      (totalChernClassComplexLocallyBounded C G sX D K hKP).1 r
        = -(Nat.factorial (r - 1) • D.ch V r) := by
  rw [totalChernClassComplexLocallyBounded_eq C G sX D K hKP
    (isZero_X_outside_of_isExteriorPowerComplex hK hvanish)]
  exact totalChernClassComplex_exteriorPowerComplex_apply C G sX D hr hK x hroots hwedge

end Stacks.Chow

end
