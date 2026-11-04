module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.LinearCombination
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppWildCaseReduction

/-!
# The fraction field of a discrete valuation ring has a separable quadratic extension

Let `R` be a discrete valuation ring with fraction field `K` and uniformizer `π`. The polynomial
`X² - X - π⁻¹` over `K` is irreducible and separable, so `K` has a finite separable extension
of degree exactly `2`. This is what turns "degree at most `2`" into the "degree `2`" of
part (1) of [Stacks, Tag 0CDN]: a genus-zero curve that already has a rational point is split by
any extension, and this one is always available.

## Main results

* `IsDiscreteValuationRing.exists_finiteDimensional_isSeparable_finrank_eq_two`: the extension.

## Implementation notes

A root `a` of `X² - X - π⁻¹` gives `y = π a` with `y² - π y - π = 0`, so `y` is integral over `R`,
hence lies in `R`. Then `π ∣ y² = π (y + 1)` forces `π ∣ y`, and writing `y = π c` gives
`π (c² - c) = 1`, making `π` a unit, which it is not. A polynomial of degree two without roots is
irreducible; its derivative `2X - 1` is nonzero in every characteristic (its constant term is
`-1`), so it is separable.

## References

* [Stacks Project, Tag 0CDN](https://stacks.math.columbia.edu/tag/0CDN)
* [Stacks Project, Tag 0CDK](https://stacks.math.columbia.edu/tag/0CDK)
-/

@[expose] public section

open Polynomial

universe u

namespace IsDiscreteValuationRing

/-- For a uniformizer `π` of `R`, the polynomial `X² - X - π⁻¹` has no root in the fraction
field `K`. -/
theorem not_isRoot_X_sq_sub_X_sub_C_inv (R : Type u) (K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] {π : R}
    (hπ : Irreducible π) (a : K) :
    ¬ (X ^ 2 - X - C (algebraMap R K π)⁻¹ : K[X]).IsRoot a := by
  intro ha
  set πK : K := algebraMap R K π with hπKdef
  have hπK : πK ≠ 0 := by
    intro h
    exact hπ.ne_zero ((IsFractionRing.injective R K) (by simpa [πK] using h))
  have ha' : a ^ 2 - a = πK⁻¹ := by
    have ha0 : a ^ 2 - a - πK⁻¹ = 0 := by simpa [Polynomial.IsRoot] using ha
    linear_combination ha0
  set y : K := πK * a with hydef
  have hy : y ^ 2 - πK * y - πK = 0 := by
    calc
      y ^ 2 - πK * y - πK = πK ^ 2 * (a ^ 2 - a) - πK := by rw [hydef]; ring
      _ = πK ^ 2 * πK⁻¹ - πK := by rw [ha']
      _ = 0 := by field_simp; ring
  have hyint : IsIntegral R y := by
    refine ⟨X ^ 2 - C π * X - C π, by monicity!, ?_⟩
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C]
    rw [← hπKdef]
    exact hy
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hyint
  have hbrel : b ^ 2 - π * b - π = 0 := by
    apply IsFractionRing.injective R K
    simp only [map_sub, map_pow, map_mul, map_zero, hb, ← hπKdef]
    exact hy
  have hP : (Ideal.span {π}).IsPrime := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ]
    exact (IsLocalRing.maximalIdeal.isMaximal R).isPrime
  have hdvd : π ∣ b := by
    have hmem : b * b ∈ Ideal.span {π} :=
      Ideal.mem_span_singleton.mpr ⟨b + 1, by linear_combination hbrel⟩
    rcases hP.mem_or_mem hmem with h | h <;> exact Ideal.mem_span_singleton.mp h
  obtain ⟨c, rfl⟩ := hdvd
  have hfac : π * (π * (c ^ 2 - c) - 1) = 0 := by linear_combination hbrel
  have hone : π * (c ^ 2 - c) = 1 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_left hπ.ne_zero)
  exact hπ.not_isUnit (isUnit_of_dvd_one ⟨c ^ 2 - c, hone.symm⟩)

/-- **The fraction field of a discrete valuation ring has a separable extension of degree
exactly two.** For a uniformizer `π`, adjoin a root of `X² - X - π⁻¹`. -/
theorem exists_finiteDimensional_isSeparable_finrank_eq_two (R : Type u) (K : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L),
      FiniteDimensional K L ∧ Algebra.IsSeparable K L ∧ Module.finrank K L = 2 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  set p : K[X] := X ^ 2 - X - C (algebraMap R K π)⁻¹ with hpdef
  have hpmonic : p.Monic := by rw [hpdef]; monicity!
  have hdeg : p.natDegree = 2 := by rw [hpdef]; compute_degree!
  have hirr : Irreducible p :=
    Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; norm_num)
      (not_isRoot_X_sq_sub_X_sub_C_inv R K hπ)
  have hsep : p.Separable := by
    refine (Polynomial.separable_iff_derivative_ne_zero hirr).2 fun hder => ?_
    have h0 := congrArg (fun q : K[X] => q.coeff 0) hder
    simp [hpdef] at h0
  have : Fact (Irreducible p) := ⟨hirr⟩
  refine ⟨AdjoinRoot p, inferInstance, inferInstance, hpmonic.finite_adjoinRoot,
    AdjoinRoot.isSeparable_of_separable hpmonic hsep, ?_⟩
  rw [(AdjoinRoot.powerBasis hpmonic.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]

end IsDiscreteValuationRing

end
