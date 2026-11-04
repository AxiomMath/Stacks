module

public import StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreierConstantInertia
public import Mathlib.RingTheory.Polynomial.Quotient

/-!
# The local ring of `k[X]` at `X` as the discrete valuation ring at infinity

For a field `k`, the localization `A₀ = k[X]_(X)` of the polynomial ring at the prime `(X)` is a
discrete valuation ring with fraction field `K = Frac k[X]`, uniformizer `X` and residue field `k`.
Reading `X` as `1/x`, `A₀` is the local ring at `∞` of the rational function field `k(x)`, with
`x = X⁻¹`. A discrete valuation ring of a rational function field `k'(x)` over a finite field `k'`
that does not contain the image of `k'[x]` contains `1/x` in its maximal ideal.

## Main definitions

* `Polynomial.LocalizationAtX`: The localization of `k[X]` at the prime ideal `(X)`.

## Main results

* `Polynomial.isDiscreteValuationRing_localizationAtX`: `k[X]_(X)` is a discrete valuation ring.
* `Polynomial.isFractionRing_localizationAtX`: The fraction field of `k[X]` is the fraction field
  of `k[X]_(X)`.
* `Polynomial.irreducible_algebraMap_X_localizationAtX`: `X` is a uniformizer of `k[X]_(X)`.
* `Polynomial.natCard_residueField_localizationAtX`: The residue field of `k[X]_(X)` has as many
  elements as `k`.
* `Polynomial.exists_eq_inv_X_mem_maximalIdeal`: A discrete valuation ring of `k'(x)` not
  containing the image of `k'[x]` contains `1/x` in its maximal ideal.

## References

* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/
@[expose] public noncomputable section

open Polynomial

namespace Polynomial

variable (k : Type*) [Field k]

/-- The prime ideal `(X)` of `k[X]`. -/
instance isPrime_span_X_polynomial : (Ideal.span {(X : k[X])}).IsPrime :=
  (Ideal.span_singleton_prime X_ne_zero).2 prime_X

/-- The local ring of `k[X]` at `(X)`. -/
abbrev LocalizationAtX : Type _ := Localization.AtPrime (Ideal.span {(X : k[X])})

/-- The local ring of `k[X]` at `(X)` is a discrete valuation ring. -/
theorem isDiscreteValuationRing_localizationAtX : IsDiscreteValuationRing (LocalizationAtX k) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain k[X] (mt
      Ideal.span_singleton_eq_bot.1 X_ne_zero) _

/-- The map from the local ring of `k[X]` at `(X)` to the fraction field of `k[X]`. -/
instance algebraLocalizationAtXFractionRing : Algebra (LocalizationAtX k) (FractionRing k[X]) :=
  (IsLocalization.lift (M := (Ideal.span {(X : k[X])}).primeCompl) (S := LocalizationAtX k)
    (g := algebraMap k[X] (FractionRing k[X])) fun s =>
      IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective k[X] (FractionRing k[X]))).2
        fun h => s.2 (h ▸ Ideal.zero_mem _))).toAlgebra

/-- The maps `k[X] → k[X]_(X) → Frac k[X]` form a scalar tower. -/
instance isScalarTower_localizationAtX :
    IsScalarTower k[X] (LocalizationAtX k) (FractionRing k[X]) :=
  IsScalarTower.of_algebraMap_eq fun a => (IsLocalization.lift_eq _ a).symm

/-- The fraction field of `k[X]` is a fraction field of the local ring of `k[X]` at `(X)`. -/
theorem isFractionRing_localizationAtX : IsFractionRing (LocalizationAtX k) (FractionRing k[X]) :=
  IsFractionRing.isFractionRing_of_isLocalization (Ideal.span {(X : k[X])}).primeCompl _ _
    fun _ hs => mem_nonZeroDivisors_of_ne_zero fun h => hs (h ▸ Ideal.zero_mem _)

/-- `X` is a uniformizer of the local ring of `k[X]` at `(X)`. -/
theorem irreducible_algebraMap_X_localizationAtX :
    haveI := isDiscreteValuationRing_localizationAtX k
    Irreducible (algebraMap k[X] (LocalizationAtX k) X) := by
  have := isDiscreteValuationRing_localizationAtX k
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer,
    ← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {(X : k[X])}) (LocalizationAtX k),
    Ideal.map_span, Set.image_singleton]

/-- The residue field of the local ring of `k[X]` at `(X)` has as many elements as `k`. -/
theorem natCard_residueField_localizationAtX :
    Nat.card (IsLocalRing.ResidueField (LocalizationAtX k)) = Nat.card k := by
  have : (Ideal.span {(X : k[X])}).IsMaximal :=
    (isPrime_span_X_polynomial k).isMaximal (mt Ideal.span_singleton_eq_bot.1 X_ne_zero)
  have e : k[X] ⧸ Ideal.span {(X : k[X])} ≃ k := by
    rw [show Ideal.span {(X : k[X])} = Ideal.span {X - C 0} by simp]
    exact (quotientSpanXSubCAlgEquiv (0 : k)).toEquiv
  exact (Nat.card_congr (IsLocalization.AtPrime.equivQuotMaximalIdeal (Ideal.span {(X : k[X])})
    (LocalizationAtX k)).toEquiv).symm.trans (Nat.card_congr e)

section Infinity

variable {k' : Type*} [Field k'] [Finite k'] {K' : Type*} [Field K'] [Algebra k'[X] K']
  {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A K']
  [IsFractionRing A K']

variable (A) in
/-- The constants `k'` of `K' = k'(x)` lie in every discrete valuation ring of `K'`: they are
integral over `ℤ`. -/
theorem algebraMap_C_mem_range (c : k') :
    algebraMap k'[X] K' (C c) ∈ Set.range (algebraMap A K') :=
  (IsIntegrallyClosed.isIntegral_iff (R := A) (K := K')).1
    ((IsIntegral.of_finite ℤ c).map ((algebraMap k'[X] K').comp C).toIntAlgHom).tower_top

/-- **A discrete valuation ring of `k'(x)` not containing `k'[x]` does not contain `x`.** -/
theorem algebraMap_X_notMem_range
    (hA : ∃ g : k'[X], algebraMap k'[X] K' g ∉ Set.range (algebraMap A K')) :
    algebraMap k'[X] K' X ∉ Set.range (algebraMap A K') := by
  intro hx
  obtain ⟨g, hg⟩ := hA
  apply hg
  let S : Subring K' := (algebraMap A K').range
  have hS : ∀ g : k'[X], algebraMap k'[X] K' g ∈ S := fun g => by
    induction g using Polynomial.induction_on with
    | C a => exact algebraMap_C_mem_range A a
    | add p q hp hq =>
      rw [map_add]
      exact S.add_mem hp hq
    | monomial n a h =>
      rw [pow_succ, ← mul_assoc, map_mul]
      exact S.mul_mem h hx
  exact hS g

/-- **A discrete valuation ring of `k'(x)` not containing `k'[x]` contains `1/x` in its maximal
ideal.** -/
theorem exists_eq_inv_X_mem_maximalIdeal
    (hA : ∃ g : k'[X], algebraMap k'[X] K' g ∉ Set.range (algebraMap A K')) :
    ∃ b : A, algebraMap A K' b = (algebraMap k'[X] K' X)⁻¹ ∧ b ∈ IsLocalRing.maximalIdeal A := by
  rcases ValuationRing.isInteger_or_isInteger A (algebraMap k'[X] K' X) with ⟨r, hr⟩ | ⟨r, hr⟩
  · exact absurd ⟨r, hr⟩ (algebraMap_X_notMem_range hA)
  · refine ⟨r, hr, (IsLocalRing.mem_maximalIdeal _).2 fun hu => ?_⟩
    apply algebraMap_X_notMem_range hA
    refine ⟨(hu.unit⁻¹ : Aˣ), ?_⟩
    rw [map_units_inv, IsUnit.unit_spec, hr, inv_inv]

end Infinity

end Polynomial

end
