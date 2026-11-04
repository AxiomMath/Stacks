module

public import StacksFrontier.AlgebraicGeometry.Different.QuasiFiniteSyntomic.UniversalFamilyBaseChange

/-!
# Generic polynomials

For a set `ι` and bounds `N, e`, the generic polynomials `g_j = ∑_E a_{j, E} x^E`, `j ∈ ι`, in
`N` variables of total degree at most `e` have independent coefficients `a_{j, E}`, which are
variables over the ground ring. Every family `p_j` of polynomials of total degree at most `e`
over an algebra `A` is obtained from them by specializing `a_{j, E}` to the coefficient of `x^E`
in `p_j`. These are the parameters of the families realizing the elementary moves of square
presentations.

## Main definitions

* `Stacks.TateMap.genPoly R ι N e j`: the generic polynomial `g_j`.
* `Stacks.TateMap.genSpec R ι N e p`: the specialization of the coefficients to those of `p`.

## Main results

* `Stacks.TateMap.map_genPoly`: specializing turns `g_j` into `p_j`.
-/

@[expose] public section

open MvPolynomial AlgebraicGeometry

universe u v

namespace Stacks.TateMap

variable (R : Type u) [CommRing R] (ι : Type) (N e : ℕ)

/-- The generic polynomial `g_j = ∑_E a_{j, E} x^E` in `N` variables of total degree at most `e`,
with coefficients the variables `a_{j, E}` over `R`. -/
noncomputable def genPoly (j : ι) : MvPolynomial (Fin N) (MvPolynomial (ι × MultiIndex N e) R) :=
  ∑ E : MultiIndex N e, monomial (multiIndexExponent N e E) (X (j, E))

variable {R ι N e}

/-- The specialization of the generic coefficient `a_{j, E}` to the coefficient of `x^E` in
`p_j`. -/
noncomputable def genSpec {A : Type v} [CommRing A] [Algebra R A]
    (p : ι → MvPolynomial (Fin N) A) : MvPolynomial (ι × MultiIndex N e) R →ₐ[R] A :=
  aeval fun jE ↦ coeff (multiIndexExponent N e jE.2) (p jE.1)

/-- **Specializing the generic polynomials.** If every `p_j` has total degree at most `e`, the
specialization of the generic coefficients to the coefficients of the `p_j` turns `g_j` into
`p_j`. -/
theorem map_genPoly {A : Type v} [CommRing A] [Algebra R A] (p : ι → MvPolynomial (Fin N) A)
    (hd : ∀ j, (p j).totalDegree ≤ e) (j : ι) :
    MvPolynomial.map (genSpec (e := e) (R := R) p : MvPolynomial (ι × MultiIndex N e) R →+* A)
      (genPoly R ι N e j) = p j := by
  classical
  refine MvPolynomial.ext _ _ fun m ↦ ?_
  simp only [genPoly, map_sum, MvPolynomial.map_monomial, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial]
  by_cases hcoeff : MvPolynomial.coeff m (p j) = 0
  · rw [hcoeff]
    refine Finset.sum_eq_zero fun E _ ↦ ?_
    by_cases he : multiIndexExponent N e E = m
    · simp [he, genSpec, hcoeff]
    · simp [he]
  · have hm : ∑ i : Fin N, m i ≤ e := by
      have h := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hcoeff)
      simpa [Finsupp.sum_fintype] using h.trans (hd j)
    rw [Finset.sum_eq_single (MultiIndex.ofFinsupp m hm)]
    · simp [genSpec]
    · intro F _ hFE
      have hFm : multiIndexExponent N e F ≠ m := fun he ↦
        hFE (multiIndexExponent_injective N e (he.trans (by simp)))
      simp [hFm]
    · exact fun h ↦ absurd (Finset.mem_univ _) h

end Stacks.TateMap
