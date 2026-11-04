module

public import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.Polynomial.Nilpotent

/-! # Expansion of polynomials -/

@[expose] public section

open Polynomial

namespace Polynomial

/-- Generalization of `Polynomial.isLocalHom_expand`. -/
theorem isLocalHom_expand' (R : Type*) [CommRing R] {p : ℕ} (hp : p ≠ 0) :
    IsLocalHom (expand R p) where
  map_nonunit f := by
    simp only [isUnit_iff_coeff_isUnit_isNilpotent, ne_eq,
      ← coeff_expand_mul' (Nat.pos_of_ne_zero hp) (f := f), mul_zero, and_imp]
    grind [mul_ne_zero]

end Polynomial

/-- Generalization of `Polynomial.of_irreducible_expand`. -/
theorem Irreducible.of_polynomialExpand {R : Type*} [CommRing R] {p : ℕ} (hp : p ≠ 0)
    {f : R[X]} (hf : Irreducible (f.expand R p)) : Irreducible f :=
  have := isLocalHom_expand' R hp
  .of_map hf

/-- If `X ^ e - C z` is irreducible over a commutative ring and `d ∣ e` with `e ≠ 0`,
then `X ^ d - C z` is also irreducible. -/
theorem Irreducible.X_pow_sub_C_of_dvd
    {R : Type*} [CommRing R] {e : ℕ} {z : R} (hez : Irreducible (X ^ e - C z))
    (he0 : e ≠ 0) {d : ℕ} (hde : d ∣ e) : Irreducible (X ^ d - C z) := by
  obtain ⟨f, rfl⟩ := hde
  exact .of_polynomialExpand (by grind : f ≠ 0) (by simpa [← pow_mul, mul_comm])
