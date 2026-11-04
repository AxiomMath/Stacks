module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Regular.Basic
public import Mathlib.Tactic.Algebraize

/-!
# Nonzerodivisors along a flat ring map

A nonzerodivisor of a commutative ring stays a nonzerodivisor in a flat algebra over it. The
statement is about a bare ring map and needs nothing from algebraic geometry, so it lives here,
below every file that uses it.

## Main results

* `AlgebraicGeometry.isRegular_map_of_flat`: a flat ring map carries a nonzerodivisor to a
  nonzerodivisor.
-/

@[expose] public section

namespace AlgebraicGeometry

/-- **A nonzerodivisor stays a nonzerodivisor along a flat ring map.** -/
theorem isRegular_map_of_flat {R A : Type*} [CommRing R] [CommRing A]
    (φ : R →+* A) (hφ : φ.Flat) {t : R} (ht : IsRegular t) :
    IsRegular (φ t) := by
  algebraize [φ]
  let _ : Module.Flat R A := hφ
  apply (Commute.isRegular_iff (fun b => mul_comm (φ t) b)).2
  have hs : IsSMulRegular A (φ t) := IsSMulRegular.of_flat (S := A) ht.left
  simpa only [IsSMulRegular, IsLeftRegular, smul_eq_mul] using hs

end AlgebraicGeometry

end
