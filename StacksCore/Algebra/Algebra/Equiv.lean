module

public import Mathlib.Algebra.Algebra.Equiv

/-! # Algebra isomorphisms -/

@[expose] public section

namespace AlgEquiv
variable {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S] (e e₁ e₂ : S ≃ₐ[R] S)

variable (R S) in
/-- The underlying `R`-linear map of the identity `R`-algebra equivalence is the identity. -/
@[simp] theorem toLinearMap_one : (1 : S ≃ₐ[R] S).toLinearMap = 1 := rfl

/-- The underlying `R`-linear map of a composition of `R`-algebra equivalences is the
composition of the underlying linear maps. -/
@[simp] theorem toLinearMap_mul : (e₁ * e₂).toLinearMap = e₁.toLinearMap * e₂.toLinearMap := rfl

/-- The function underlying `e.toLinearMap` agrees with `e` itself. -/
@[simp] theorem coe_toLinearMap : ⇑e.toLinearMap = ⇑e := rfl

/-- The underlying `R`-linear map of the `n`-th power of an `R`-algebra equivalence is the
`n`-th power of the underlying linear map. -/
@[simp] theorem toLinearMap_pow
    (n : ℕ) : (e ^ n).toLinearMap = e.toLinearMap ^ n := by ext; simp [Module.End.coe_pow]

end AlgEquiv
