module

public import Mathlib
public import StacksFrontier.RingTheory.Derivation.FormallyEtaleExtension

/-!
# The derivation `d/dX` on a finite étale algebra over `k[X]`

Let `k` be a field and `B` a formally étale `k[X]`-algebra. The derivation `d/dX` of `k[X]`
extends uniquely to a `k`-derivation `D` of `B`. When `k` is algebraically closed of
characteristic zero and `B` is a domain finite over `k[X]`, the kernel of `D` is `k`.

These are the first steps towards the statement that the affine line over an algebraically
closed field of characteristic zero has no nontrivial connected finite étale covering.

## Main definitions

* `Polynomial.AffineLineCovering.derivB`: the extension of `d/dX` to `B`.

## Main results

* `Polynomial.AffineLineCovering.derivB_algebraMap`: `D` restricts to `d/dX` on `k[X]`.
* `Polynomial.AffineLineCovering.mem_range_of_derivB_eq_zero`: the kernel of `D` is `k`.

## Implementation notes

For the kernel: the minimal polynomial over the integrally closed ring `k[X]` of an element `z`
with `D z = 0` divides the polynomial whose coefficients are the derivatives of its own
coefficients. That polynomial has smaller degree, so it is zero. In characteristic zero all
coefficients of the minimal polynomial are then constant, so `z` is integral over `k`, and `k`
is algebraically closed.
-/

@[expose] public section

open Polynomial

namespace Polynomial.AffineLineCovering

section Derivation

variable (k : Type*) [Field k] (B : Type*) [CommRing B] [Algebra k B] [Algebra k[X] B]
  [IsScalarTower k k[X] B] [Algebra.FormallyEtale k[X] B]

/-- The derivation `d/dX` of `k[X]`, extended to a formally étale `k[X]`-algebra `B`. -/
noncomputable def derivB : Derivation k B B :=
  Derivation.extendOfFormallyEtale k k[X] B (Polynomial.mkDerivation k (1 : B))

variable {k B}

/-- On the image of `k[X]`, `derivB` is the usual derivative of polynomials. -/
@[simp]
theorem derivB_algebraMap (f : k[X]) :
    derivB k B (algebraMap k[X] B f) = algebraMap k[X] B (derivative f) := by
  rw [derivB, Derivation.extendOfFormallyEtale_algebraMap, Polynomial.mkDerivation_apply,
    Algebra.smul_def, mul_one]

/-- **The derivation `d/dX` of a formally étale `k[X]`-algebra applied to a polynomial
expression.** If `D z = 0` then `D (p(z))` is the polynomial whose coefficients are the
derivatives of those of `p`, evaluated at `z`. -/
theorem derivB_aeval_of_derivB_eq_zero {z : B} (hz : derivB k B z = 0) (p : k[X][X]) :
    derivB k B (aeval z p) = aeval z (p.sum fun n a ↦ monomial n (derivative a)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq, Polynomial.sum_add_index]
    · rw [map_add]
    · intro n; simp
    · intro n a b; rw [derivative_add, map_add]
  | monomial n a =>
    rw [Polynomial.sum_monomial_index, aeval_monomial, aeval_monomial,
      Derivation.leibniz, Derivation.leibniz_pow, hz]
    · simp [smul_eq_mul, mul_comm]
    · simp

/-- **The kernel of `d/dX` on a finite étale domain over `k[X]` is `k`**, for `k` algebraically
closed of characteristic zero. The minimal polynomial of an element `z` with `D z = 0` over the
integrally closed ring `k[X]` divides the polynomial of derivatives of its coefficients, which
has smaller degree; so all its coefficients are constant, `z` is integral over `k`, and `k` is
algebraically closed. -/
theorem mem_range_of_derivB_eq_zero [IsAlgClosed k] [CharZero k] [IsDomain B]
    [Module.Finite k[X] B] [Module.IsTorsionFree k[X] B] {z : B} (hz : derivB k B z = 0) :
    z ∈ Set.range (algebraMap k B) := by
  have hint : IsIntegral k[X] z := Algebra.IsIntegral.isIntegral z
  set P := minpoly k[X] z with hP
  have hmon : P.Monic := minpoly.monic hint
  set Q : k[X][X] := P.sum fun n a ↦ monomial n (derivative a) with hQ
  have hQz : aeval z Q = 0 := by
    rw [← derivB_aeval_of_derivB_eq_zero hz, minpoly.aeval, map_zero]
  have hQcoeff : ∀ n, Q.coeff n = derivative (P.coeff n) := by
    intro n
    rw [hQ, Polynomial.sum_def, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single n]
    · simp
    · intro b _ hb; simp [hb]
    · intro hn
      rw [Polynomial.mem_support_iff, not_not] at hn
      simp [hn]
  have hQdeg : Q.natDegree < P.natDegree := by
    have hpos : 0 < P.natDegree := minpoly.natDegree_pos hint
    refine lt_of_le_of_ne ?_ ?_
    · refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun n hn ↦ ?_
      rw [hQcoeff, Polynomial.coeff_eq_zero_of_natDegree_lt (by exact_mod_cast hn),
        derivative_zero]
    · intro h
      have hlead : Q.coeff P.natDegree = 0 := by
        rw [hQcoeff, Polynomial.coeff_natDegree, hmon.leadingCoeff, derivative_one]
      have hQ0 : Q = 0 := by
        by_contra hQ0
        rw [← h] at hlead
        exact hQ0 (Polynomial.leadingCoeff_eq_zero.mp hlead)
      rw [hQ0, Polynomial.natDegree_zero] at h
      omega
  have hQ0 : Q = 0 :=
    Polynomial.eq_zero_of_dvd_of_natDegree_lt (minpoly.isIntegrallyClosed_dvd hint hQz) hQdeg
  -- every coefficient of the minimal polynomial is constant
  have hconst : P = (P.map (constantCoeff)).map (algebraMap k k[X]) := by
    ext1 n
    rw [Polynomial.coeff_map, Polynomial.coeff_map, constantCoeff_apply, algebraMap_eq,
      ← Polynomial.eq_C_of_derivative_eq_zero]
    rw [← hQcoeff, hQ0, Polynomial.coeff_zero]
  have hkint : IsIntegral k z := by
    refine ⟨P.map constantCoeff, hmon.map _, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap k[X], ← hconst,
      minpoly.aeval]
  have hirr : Irreducible (minpoly k z) := minpoly.irreducible hkint
  exact minpoly.mem_range_of_degree_eq_one k z (IsAlgClosed.degree_eq_one_of_irreducible k hirr)

end Derivation

end Polynomial.AffineLineCovering
