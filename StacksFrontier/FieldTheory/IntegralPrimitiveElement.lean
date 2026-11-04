module

public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# Primitive elements whose minimal polynomial is defined over the base ring

Let `R` be a domain with fraction field `K` and let `L / K` be a finite separable extension.
A primitive element of `L / K` can be rescaled by a nonzero element of `R` so that its minimal
polynomial over `K` is the image of a monic polynomial over `R`.

## Main results

* `IntermediateField.adjoin_simple_smul` — rescaling by a nonzero scalar of the base field does
  not change the simple extension it generates.
* `Polynomial.minpoly_scaleRoots_smul` — the minimal polynomial of a nonzero rescaling is the
  corresponding rescaling of the minimal polynomial.
* `Field.exists_integral_primitive_element_of_isFractionRing` — a finite separable extension of
  the fraction field of a domain `R` has a primitive element whose minimal polynomial is the
  image of a monic polynomial over `R`.

## Implementation notes

The rescaled minimal polynomial is `Polynomial.scaleRoots`, whose coefficients are
`p.coeff i * c ^ (p.natDegree - i)`. Taking `c` to be a common denominator of the coefficients
of the minimal polynomial makes every one of those products integral, because the exponent
`p.natDegree - i` is at least one whenever `i` is below the degree, where alone a denominator
can occur.

## References

* [Stacks Project, Tag 0551](https://stacks.math.columbia.edu/tag/0551)
-/

@[expose] public section

open Polynomial IntermediateField

namespace IntermediateField

/-- Rescaling by a nonzero scalar of the base field does not change the simple extension it
generates. -/
public theorem adjoin_simple_smul {K L : Type*} [Field K] [Field L] [Algebra K L] {c : K}
    (hc : c ≠ 0) (x : L) : K⟮c • x⟯ = K⟮x⟯ := by
  refine le_antisymm ?_ ?_ <;> rw [adjoin_simple_le_iff]
  · rw [Algebra.smul_def]
    exact mul_mem (algebraMap_mem _ c) (mem_adjoin_simple_self K x)
  · have hmem : algebraMap K L c⁻¹ * (c • x) ∈ K⟮c • x⟯ :=
      mul_mem (algebraMap_mem _ c⁻¹) (mem_adjoin_simple_self K (c • x))
    rwa [← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hc, one_smul] at hmem

end IntermediateField

namespace Polynomial

/-- Rescaling an element of a field extension by a nonzero scalar rescales the roots of its
minimal polynomial. -/
public theorem minpoly_scaleRoots_smul {K L : Type*} [Field K] [Field L] [Algebra K L] {c : K}
    (hc : c ≠ 0) {x : L} (hx : IsIntegral K x) :
    (minpoly K x).scaleRoots c = minpoly K (c • x) := by
  have key : ∀ (d : K) (y : L) (q : K[X]), aeval y q = 0 →
      aeval (d • y) (q.scaleRoots d) = 0 := fun d y q hq => by
    simpa only [aeval_def, ← Algebra.smul_def] using
      scaleRoots_eval₂_eq_zero (p := q) (algebraMap K L) (r := y) (s := d) hq
  refine minpoly.unique K (c • x) ((monic_scaleRoots_iff c).mpr (minpoly.monic hx))
    (key c x _ (minpoly.aeval K x)) ?_
  intro q hqmonic hq
  calc ((minpoly K x).scaleRoots c).degree
      = (minpoly K x).degree := degree_scaleRoots _
    _ ≤ (q.scaleRoots c⁻¹).degree :=
        minpoly.min K x ((monic_scaleRoots_iff c⁻¹).mpr hqmonic) <| by
          simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using key c⁻¹ (c • x) q hq
    _ = q.degree := degree_scaleRoots _

end Polynomial

namespace Field

variable {R K L : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- **Primitive elements with integral minimal polynomial.** A finite separable extension `L` of
the fraction field `K` of a domain `R` has a primitive element whose minimal polynomial over `K`
is the image of a monic polynomial over `R`. -/
public theorem exists_integral_primitive_element_of_isFractionRing :
    ∃ (F : R[X]) (β : L), F.Monic ∧ F.map (algebraMap R K) = minpoly K β ∧ K⟮β⟯ = ⊤ := by
  classical
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
  have hint : IsIntegral K α := IsIntegral.of_finite K α
  set P : K[X] := minpoly K α with hPdef
  have hPmonic : P.Monic := minpoly.monic hint
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R)
    (Finset.range (P.natDegree + 1)) P.coeff
  set c : K := algebraMap R K (b : R) with hcdef
  have hc0 : c ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have hlifts : P.scaleRoots c ∈ lifts (algebraMap R K) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    rw [coeff_scaleRoots]
    rcases lt_trichotomy n P.natDegree with hn | hn | hn
    · obtain ⟨r, hr⟩ := hb n (Finset.mem_range.mpr (by lia))
      refine ⟨r * (b : R) ^ (P.natDegree - n - 1), ?_⟩
      have hpow : c ^ (P.natDegree - n) = c * c ^ (P.natDegree - n - 1) := by
        rw [← pow_succ']
        congr 1
        lia
      rw [Algebra.smul_def, ← hcdef] at hr
      rw [map_mul, map_pow, hpow, ← hcdef, ← mul_assoc, hr]
      ring
    · subst hn
      rw [hPmonic.coeff_natDegree, Nat.sub_self, pow_zero, one_mul]
      exact ⟨1, map_one _⟩
    · rw [P.coeff_eq_zero_of_natDegree_lt hn, zero_mul]
      exact ⟨0, map_zero _⟩
  obtain ⟨F, hFmap, -, hFmonic⟩ :=
    lifts_and_natDegree_eq_and_monic hlifts ((monic_scaleRoots_iff c).mpr hPmonic)
  refine ⟨F, c • α, hFmonic, ?_, ?_⟩
  · rw [hFmap, hPdef, minpoly_scaleRoots_smul hc0 hint]
  · rw [IntermediateField.adjoin_simple_smul hc0, hα]

end Field

end
