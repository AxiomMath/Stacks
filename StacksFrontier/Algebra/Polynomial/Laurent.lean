module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-!
# Laurent polynomials as a localization, and the polynomials fixed by inversion

A Laurent polynomial ring `R[T;T⁻¹]` is the localization of `R[X]` away from `X`, so it is an
`R[X]`-algebra; the resulting tower over the coefficient ring `R` is a scalar tower, and
`R[T;T⁻¹]` is of finite type over `R`.

Two polynomials have the same image in `R[T;T⁻¹]` up to the inversion `T ↦ T⁻¹` only when both
are one and the same constant.

## Main results

* `LaurentPolynomial.isScalarTower`: `R → R[X] → R[T;T⁻¹]` is a scalar tower.
* `LaurentPolynomial.finiteType`: `R[T;T⁻¹]` is of finite type over `R`.
* `Polynomial.toLaurent_eq_invert_toLaurent_iff`: two polynomials have the same image in
  `R[T;T⁻¹]` up to inversion exactly when both are one and the same constant.
-/

@[expose] public section

universe u

namespace LaurentPolynomial

/-- The Laurent polynomial ring is an algebra over the coefficient ring both directly and
through the polynomial ring: the three form a scalar tower. -/
instance isScalarTower (R : Type u) [CommSemiring R] :
    IsScalarTower R (Polynomial R) (LaurentPolynomial R) :=
  IsScalarTower.of_algebraMap_eq fun c => (Polynomial.toLaurent_C c).symm

/-- The Laurent polynomial ring is of finite type over the coefficient ring. -/
instance finiteType (R : Type u) [CommRing R] :
    Algebra.FiniteType R (LaurentPolynomial R) :=
  Algebra.FiniteType.equiv
    (inferInstanceAs (Algebra.FiniteType R
      (Localization.Away (Polynomial.X : Polynomial R))))
    ((IsLocalization.algEquiv (Submonoid.powers (Polynomial.X : Polynomial R))
      (Localization.Away (Polynomial.X : Polynomial R))
      (LaurentPolynomial R)).restrictScalars R)

end LaurentPolynomial

namespace Polynomial

variable {R : Type u} [CommRing R]

/-- The coefficient of `toLaurent p` at a natural number is the corresponding coefficient of `p`. -/
private theorem coeff_toLaurent_natCast (p : Polynomial R) (n : ℕ) :
    (toLaurent p).coeff (n : ℤ) = p.coeff n := by
  rw [LaurentPolynomial.coeff_toLaurent]
  exact Finsupp.mapDomain_apply Nat.castEmbedding.injective _ n

/-- A polynomial whose image in `R[T;T⁻¹]` is the inversion of the image of another polynomial
is constant. -/
theorem eq_C_coeff_zero_of_toLaurent_eq_invert {p q : Polynomial R}
    (hpq : toLaurent p = LaurentPolynomial.invert (toLaurent q)) :
    p = C (p.coeff 0) := by
  refine Polynomial.ext fun n => ?_
  by_cases hn : n = 0
  · subst n
    simp
  · have hcoeff := congrArg (fun z : LaurentPolynomial R => z.coeff (n : ℤ)) hpq
    rw [LaurentPolynomial.invert_apply] at hcoeff
    have hneg : (toLaurent q).coeff (-(n : ℤ)) = 0 := by
      rw [LaurentPolynomial.coeff_toLaurent]
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨m, hm⟩
      change (m : ℤ) = -(n : ℤ) at hm
      omega
    have hp : p.coeff n = 0 := by
      rw [← coeff_toLaurent_natCast]
      exact hcoeff.trans hneg
    simp [Polynomial.coeff_C, hn, hp]

/-- The constant terms of two polynomials whose images in `R[T;T⁻¹]` agree up to inversion are
equal. -/
theorem coeff_zero_eq_of_toLaurent_eq_invert {p q : Polynomial R}
    (hpq : toLaurent p = LaurentPolynomial.invert (toLaurent q)) :
    q.coeff 0 = p.coeff 0 := by
  have h := congrArg (fun z : LaurentPolynomial R => z.coeff 0) hpq
  rw [LaurentPolynomial.invert_apply, neg_zero] at h
  have h0 := coeff_toLaurent_natCast p 0
  have h1 := coeff_toLaurent_natCast q 0
  push_cast at h0 h1
  rw [← h0, ← h1]
  exact h.symm

/-- Two polynomials have the same image in `R[T;T⁻¹]` up to the inversion `T ↦ T⁻¹` exactly
when both are one and the same constant. -/
theorem toLaurent_eq_invert_toLaurent_iff {p q : Polynomial R} :
    toLaurent p = LaurentPolynomial.invert (toLaurent q) ↔ ∃ c : R, p = C c ∧ q = C c := by
  refine ⟨fun hpq => ⟨p.coeff 0, eq_C_coeff_zero_of_toLaurent_eq_invert hpq, ?_⟩, ?_⟩
  · have hqp : toLaurent q = LaurentPolynomial.invert (toLaurent p) := by
      rw [hpq, LaurentPolynomial.involutive_invert]
    exact (eq_C_coeff_zero_of_toLaurent_eq_invert hqp).trans
      (congrArg C (coeff_zero_eq_of_toLaurent_eq_invert hpq))
  · rintro ⟨c, rfl, rfl⟩
    rw [toLaurent_C, LaurentPolynomial.invert_C]

end Polynomial

end
