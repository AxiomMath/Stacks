module

public import StacksCore.Algebra.QuadraticAlgebra.TraceNorm

/-! # Standardized Quadratic Algebras-/

@[expose] public section

open Algebra

namespace QuadraticAlgebra
variable {R : Type*} [CommRing R] (a b : R)

/-- If `a₁ = a₂` and `b₁ = b₂`, then `QuadraticAlgebra R a₁ b₁` and `QuadraticAlgebra R a₂ b₂`
are canonically `R`-algebra isomorphic. -/
@[simps]
def congr {a₁ a₂ b₁ b₂ : R} (ha : a₁ = a₂) (hb : b₁ = b₂) :
    QuadraticAlgebra R a₁ b₁ ≃ₐ[R] QuadraticAlgebra R a₂ b₂ where
  toFun z := z.re • 1 + z.im • omega
  invFun z := z.re • 1 + z.im • omega
  map_add' _ _ := by ext <;> simp
  map_mul' _ _ := by ext <;> simp [ha, hb]
  commutes' _ := by ext <;> simp
  left_inv _ := by ext <;> simp
  right_inv _ := by ext <;> simp

/-- Scaling by `u : R` gives an `R`-algebra hom
`QuadraticAlgebra R (u^2 * a) (u * b) →ₐ QuadraticAlgebra R a b` sending `ω ↦ u • ω`. -/
@[simps]
def scale (u : R) : QuadraticAlgebra R (u ^ 2 * a) (u * b) →ₐ[R] QuadraticAlgebra R a b where
  toFun z := z.re • 1 + z.im • u • omega
  map_zero' := by simp
  map_one' := by simp
  map_add' _ _ := by ext <;> simp; ring
  map_mul' _ _ := by ext <;> simp <;> ring
  commutes' _ := by ext <;> simp

/-- Scaling by a unit `u : Rˣ` gives an `R`-algebra equivalence
`QuadraticAlgebra R a b ≃ₐ QuadraticAlgebra R (u^2 * a) (u * b)`. -/
@[simps!]
def scaleUnit (u : Rˣ) : QuadraticAlgebra R a b ≃ₐ[R] QuadraticAlgebra R (u ^ 2 * a) (u * b) :=
  .ofAlgHom ((scale _ _ ↑u⁻¹).comp (congr (by simp [sq, mul_assoc]) (by simp)).toAlgHom)
    (scale a b u) (by ext <;> simp) (by ext <;> simp)

/-- Replacing the generator `ω` by `ω + n` gives an `R`-algebra equivalence
`QuadraticAlgebra R a b ≃ₐ QuadraticAlgebra R (a + b*n - n^2) (b - 2*n)`. -/
@[simps]
def translate (n : R) :
    QuadraticAlgebra R a b ≃ₐ[R] QuadraticAlgebra R (a + b * n - n ^ 2) (b - 2 * n) where
  toFun z := z.re • 1 + z.im • (omega + n • 1)
  invFun z := z.re • 1 + z.im • (omega - n • 1)
  map_add' _ _ := by ext <;> simp; ring
  map_mul' _ _ := by ext <;> simp <;> ring
  commutes' _ := by ext <;> simp
  left_inv _ := by ext <;> simp
  right_inv _ := by ext <;> simp

end QuadraticAlgebra
