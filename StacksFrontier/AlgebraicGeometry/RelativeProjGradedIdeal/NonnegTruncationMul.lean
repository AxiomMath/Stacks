module

public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.NonnegTruncation

/-!
# The truncated multiplication in nonnegative degrees

The nonnegative truncation `Stacks.AlgebraicGeometry.NonnegTruncation.nonnegTruncation` of a
sheaf of graded algebras `A` agrees with `A` in nonnegative degrees, but only propositionally
(`Stacks.AlgebraicGeometry.NonnegTruncation.piece_of_nonneg`). This file records that its
multiplication is that of `A` there, as a heterogeneous equality.

## Main results

* `Stacks.AlgebraicGeometry.NonnegTruncation.heq_mul_app_of_nonneg`: in two nonnegative degrees
  the truncated multiplication is that of `A`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Stacks.AlgebraicGeometry.NonnegTruncation

universe u

variable {S : Scheme.{u}} (A : SheafOfModules.GradedAlgebra.{u, u} S.ringCatSheaf)

/-- **In two nonnegative degrees the truncated multiplication is that of `A`**, the two factors
read in `A` along `piece_of_nonneg`. The two sides live in the degree-`i + j` pieces of the
truncation and of `A`, which agree only propositionally, so the identity is heterogeneous; both
`Int` constructors of each degree being settled turns it into `rfl`. -/
theorem heq_mul_app_of_nonneg {i j : ℤ} (hi : 0 ≤ i) (hj : 0 ≤ j) (U : (S.Opens)ᵒᵖ)
    (x : (piece A i).val.obj U) (y : (piece A j).val.obj U) :
    HEq ((mul A i j).app U x y)
      ((A.mul i j).app U ((eqToHom (piece_of_nonneg A hi)).val.app U x)
        ((eqToHom (piece_of_nonneg A hj)).val.app U y)) := by
  obtain ⟨a, rfl⟩ : ∃ a : ℕ, i = Int.ofNat a := ⟨i.toNat, (Int.toNat_of_nonneg hi).symm⟩
  obtain ⟨b, rfl⟩ : ∃ b : ℕ, j = Int.ofNat b := ⟨j.toNat, (Int.toNat_of_nonneg hj).symm⟩
  rfl

end Stacks.AlgebraicGeometry.NonnegTruncation

end
