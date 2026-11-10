module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.TotalChernClass

/-!
# The Adams eigenvalues of Chern classes and of the Chern character

For a category `𝒞` of schemes, a contravariant functor `A` to graded rings and a first Chern
class `c₁^A : Pic(X) ⟶ A¹(X)`, the second Adams operator `ψ²` scales the degree-`i` part of both
the total Chern class and the Chern character by `2^i`:

`c^A_i(ψ²(α)) = 2^i c^A_i(α)` and `ch^A_i(ψ²(α)) = 2^i ch^A_i(α)`.

This file contains the convolution identity behind the statement for the total Chern class: in a
ring, `2^i • a` times the degree-`j` coefficient of `1 + 2x` is `2^{i + j}` times the product of
`a` with the degree-`j` coefficient of `1 + x`.

## References

* [Stacks Project, Tag 0FIA](https://stacks.math.columbia.edu/tag/0FIA)
* [Stacks Project, Tag 0FI5](https://stacks.math.columbia.edu/tag/0FI5)
* [Stacks Project, Tag 0FI7](https://stacks.math.columbia.edu/tag/0FI7)
* [Stacks Project, Tag 0FI9](https://stacks.math.columbia.edu/tag/0FI9)
* [Stacks Project, Tag 0FEJ](https://stacks.math.columbia.edu/tag/0FEJ)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v v₁ w

namespace Stacks.WeilCohomology

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}

/-! ### Doubling the first Chern classes of a split module -/

/-- For `i + j = n`, the product of `2^i • a` with the degree-`j` coefficient of `1 + 2x` is
`2^n` times the product of `a` with the degree-`j` coefficient of `1 + x`. -/
theorem nsmul_mul_degreeOneFactor {A : Type*} [Ring A] (a x : A) {i j n : ℕ}
    (h : i + j = n) :
    (2 ^ i : ℕ) • a * (if j = 0 then 1 else if j = 1 then 2 • x else 0) =
      (2 ^ n : ℕ) • (a * (if j = 0 then 1 else if j = 1 then x else 0)) := by
  subst h
  match j with
  | 0 => simp
  | 1 =>
      have e1 : (if (1 : ℕ) = 0 then (1 : A) else if (1 : ℕ) = 1 then 2 • x else 0) = 2 • x := by
        simp
      have e2 : (if (1 : ℕ) = 0 then (1 : A) else if (1 : ℕ) = 1 then x else 0) = x := by simp
      rw [e1, e2, smul_mul_assoc, mul_smul_comm, smul_smul, pow_succ]
  | (m + 2) => simp

section

variable {𝔄 : ChernSetup.{u, v, v₁, w} C S}
  (κ : ∀ {X Y : C}, (X ⟶ Y) → (VectorBundleKZero (S.obj Y) →+* VectorBundleKZero (S.obj X)))
  (ψ : ∀ X : C, VectorBundleKZero (S.obj X) →+* VectorBundleKZero (S.obj X))

end

end Stacks.WeilCohomology

end
