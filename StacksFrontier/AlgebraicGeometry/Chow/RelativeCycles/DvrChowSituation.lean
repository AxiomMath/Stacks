module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.UniversallyCatenaryExamples

/-!
# The base situation of chapter 42 over a discrete valuation ring

Let `R` be a discrete valuation ring. Its spectrum has exactly two points, the generic point
`η` — the zero ideal — and the closed point `s` — the maximal ideal — and the function sending
`η` to `1` and `s` to `0` is a dimension function on it in the sense of Stacks 02I8. Together
with Noetherianity and universal catenarity of `Spec R` this makes `(Spec R, δ)` a base
situation of chapter 42 in the sense of Stacks 02QL.

This situation is what lets the dimension theory of chapter 42 — delta-dimension, the
codimension-one criterion of Stacks 02RK, the proper pushforward of Stacks 02R4 and the
principal divisors of Stacks 02RO — be used on a scheme locally of finite type over `R` itself,
rather than only on its fibres, where the situation on the spectrum of a residue field is the
one available.

## Main definitions

* `Stacks.Chow.dvrDimensionFunction` — the dimension function `δ` on `Spec R`.
* `Stacks.Chow.dvrChowSituation` — the base situation `(Spec R, δ)`.

## Main results

* `Stacks.Chow.asIdeal_eq_bot_of_specializes_of_ne` — a nontrivial specialization in the
  spectrum of a discrete valuation ring runs from the zero ideal to the maximal ideal.
* `Stacks.Chow.dvrChowSituation_dimensionFunction_closedPoint`,
  `Stacks.Chow.dvrChowSituation_dimensionFunction_genericPoint` — the two values of `δ`.

## Implementation notes

Universal catenarity of `Spec R` is Stacks 02JB part (4) for the one-dimensional Noetherian
domain `R`, taken in the form
`AlgebraicGeometry.Scheme.isUniversallyCatenary_of_locallyOfFiniteType_over_dimOneDomain`
applied to the identity morphism; the Krull dimension of a discrete valuation ring is one by
`IsDiscreteValuationRing.ringKrullDim_eq_one`.

Both conditions on a dimension function concern a *nontrivial* specialization, and in the
spectrum of a discrete valuation ring there is exactly one: from the zero ideal to the maximal
ideal. So both are the single computation
`Stacks.Chow.asIdeal_eq_bot_of_specializes_of_ne`, and the condition on an immediate
specialization needs nothing beyond the condition on a general one.

The dimension function is written as a test on the prime itself, `δ x = if x = ⊥ then 1 else 0`,
rather than as a test for being the closed point: that is the form in which the two values are
computed, since the generic point of `Spec R` is identified with the zero ideal and the closed
point carries the maximal ideal by definition.

## References

* [Stacks Project, Tag 02I8](https://stacks.math.columbia.edu/tag/02I8)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
* [Stacks Project, Tag 02JB](https://stacks.math.columbia.edu/tag/02JB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The maximal ideal of a discrete valuation ring is nonzero: a discrete valuation ring is not
a field. -/
theorem maximalIdeal_ne_bot_of_isDiscreteValuationRing :
    IsLocalRing.maximalIdeal R ≠ ⊥ :=
  IsDiscreteValuationRing.not_a_field R

/-- **The one nontrivial specialization of the spectrum of a discrete valuation ring.** If `x`
specializes to `y` and the two points are distinct, then `x` is the zero ideal and `y` is not:
a nonzero prime of a discrete valuation ring is maximal, so it admits no strictly larger
prime. -/
theorem asIdeal_eq_bot_of_specializes_of_ne {x y : ↥(Spec (.of R))} (hxy : x ⤳ y)
    (hne : x ≠ y) :
    (x : PrimeSpectrum R).asIdeal = ⊥ ∧ (y : PrimeSpectrum R).asIdeal ≠ ⊥ := by
  have hle : (x : PrimeSpectrum R).asIdeal ≤ (y : PrimeSpectrum R).asIdeal :=
    (PrimeSpectrum.le_iff_specializes x y).mpr hxy
  have hxp : ((x : PrimeSpectrum R).asIdeal).IsPrime := (x : PrimeSpectrum R).2
  have hyp : ((y : PrimeSpectrum R).asIdeal).IsPrime := (y : PrimeSpectrum R).2
  have hxbot : (x : PrimeSpectrum R).asIdeal = ⊥ := by
    by_contra hx
    have hxmax : ((x : PrimeSpectrum R).asIdeal).IsMaximal :=
      Ideal.isMaximal_of_isPrime_of_ne_bot (x : PrimeSpectrum R).asIdeal hx
    exact hne (PrimeSpectrum.ext (hxmax.eq_of_le hyp.ne_top hle))
  exact ⟨hxbot, fun hy ↦ hne (PrimeSpectrum.ext (hxbot.trans hy.symm))⟩

/-- **The dimension function on the spectrum of a discrete valuation ring**, in the sense of
Stacks 02I8: it takes the value `1` at the zero ideal, that is at the generic point, and `0` at
the maximal ideal, that is at the closed point. -/
def dvrDimensionFunction : DimensionFunction (Spec (.of R)) where
  toFun x := if (x : PrimeSpectrum R).asIdeal = ⊥ then 1 else 0
  strictAnti_specializes := by
    intro x y hxy hne
    obtain ⟨hx, hy⟩ := asIdeal_eq_bot_of_specializes_of_ne R hxy hne
    simp [hx, hy]
  step_immediate := by
    intro x y h
    obtain ⟨hx, hy⟩ := asIdeal_eq_bot_of_specializes_of_ne R h.1 h.2.1
    simp [hx, hy]

/-- **Stacks 02QL over a discrete valuation ring.** The base situation of chapter 42 whose base
scheme is the spectrum of a discrete valuation ring `R` and whose dimension function is `1` at
the generic point and `0` at the closed point.

It is an `abbrev` so that its base scheme is reducibly `Spec R`: the cycle groups and
delta-dimensions of a scheme over `R` are formed for this situation, and unification on them has
to see through to `AlgebraicGeometry.Spec`. -/
abbrev dvrChowSituation : ChowSituation.{u} where
  S := Spec (.of R)
  isUniversallyCatenary :=
    Scheme.isUniversallyCatenary_of_locallyOfFiniteType_over_dimOneDomain R
      (IsDiscreteValuationRing.ringKrullDim_eq_one R) (CategoryTheory.CategoryStruct.id _)
  dimensionFunction := dvrDimensionFunction R

/-- The dimension function of `Stacks.Chow.dvrChowSituation` vanishes at the closed point. -/
@[simp]
theorem dvrChowSituation_dimensionFunction_closedPoint :
    (dvrChowSituation R).dimensionFunction (IsLocalRing.closedPoint R) = 0 := by
  change (if (IsLocalRing.maximalIdeal R) = ⊥ then (1 : ℤ) else 0) = 0
  simp [maximalIdeal_ne_bot_of_isDiscreteValuationRing R]

/-- The generic point of the spectrum of a domain is the zero ideal: the generic point
specializes to the zero ideal, so its prime is contained in the zero ideal. -/
theorem asIdeal_genericPoint_spec :
    (genericPoint (Spec (.of R)) : PrimeSpectrum R).asIdeal = ⊥ :=
  le_bot_iff.mp
    ((PrimeSpectrum.le_iff_specializes _ (⟨⊥, inferInstance⟩ : PrimeSpectrum R)).mpr
      (genericPoint_specializes (⟨⊥, inferInstance⟩ : PrimeSpectrum R)))

/-- The dimension function of `Stacks.Chow.dvrChowSituation` is one at the generic point. -/
@[simp]
theorem dvrChowSituation_dimensionFunction_genericPoint :
    (dvrChowSituation R).dimensionFunction (genericPoint (Spec (.of R))) = 1 := by
  change (if (genericPoint (Spec (.of R)) : PrimeSpectrum R).asIdeal = ⊥ then (1 : ℤ) else 0) = 1
  simp

/-- The base scheme of `Stacks.Chow.dvrChowSituation` is the spectrum of `R`. -/
@[simp]
theorem dvrChowSituation_S : (dvrChowSituation R).S = Spec (.of R) := rfl

end Stacks.Chow

end
