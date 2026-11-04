module

public import Mathlib.AlgebraicGeometry.Scheme

/-!
# Integers invertible on a scheme

An integer `n` is invertible on a scheme `S` when its image in `Γ(S, ⊤)` is a unit. This is
inherited by the divisors of `n` (and by every scheme over `S`,
`Stacks.Kummer.isUnit_natCast_of_hom`).

## Main results

* `AlgebraicGeometry.isUnit_natCast_of_dvd`: a divisor of an integer invertible on `S` is
  invertible on `S`.
-/

@[expose] public section

namespace AlgebraicGeometry

/-- A divisor of an integer invertible on `S` is invertible on `S`. -/
theorem isUnit_natCast_of_dvd {S : Scheme} {ℓ n : ℕ} (hℓ : ℓ ∣ n)
    (h : IsUnit ((n : ℕ) : Γ(S, ⊤))) : IsUnit ((ℓ : ℕ) : Γ(S, ⊤)) :=
  isUnit_of_dvd_unit (Nat.cast_dvd_cast hℓ) h

end AlgebraicGeometry

end
