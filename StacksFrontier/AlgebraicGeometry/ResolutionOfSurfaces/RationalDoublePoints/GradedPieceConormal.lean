module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Affine
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.QuadraticForm

/-!
# The graded pieces of a local ring are the pieces of the associated graded ring

`IsLocalRing.gradedPiece A n` is `𝔪ⁿ/𝔪ⁿ⁺¹` presented as the quotient of the `A`-module `𝔪ⁿ` by
the submodule `𝔪 • ⊤`. `AssociatedGraded.piece I n` is the same group presented as the quotient
of `Iⁿ` by the preimage of `Iⁿ⁺¹`. The two are not definitionally equal: the denominators are
different submodules of `↥(𝔪ⁿ)`, equal by `Stacks.Conormal.smul_top_eq_comap`. This file
identifies the two presentations.

## Main definitions

* `IsLocalRing.gradedPieceEquivPiece`: the `A`-linear isomorphism
  `IsLocalRing.gradedPiece A n ≃ₗ[A] AssociatedGraded.piece (maximalIdeal A) n`.

## Main results

* `IsLocalRing.gradedPieceEquivPiece_gradedPieceMk`: the isomorphism carries the quotient map
  `IsLocalRing.gradedPieceMk` to the quotient map `Stacks.Conormal.toPiece`.
-/

@[expose] public noncomputable section

universe u

namespace IsLocalRing

variable (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ)

/-- The `A`-linear isomorphism between the graded piece `𝔪ⁿ/𝔪ⁿ⁺¹` of a local ring `A`, presented
as `𝔪ⁿ / 𝔪 • 𝔪ⁿ`, and the degree-`n` piece of the associated graded module of `A` with respect to
`𝔪`. -/
def gradedPieceEquivPiece :
    gradedPiece A n ≃ₗ[A] AssociatedGraded.piece (M := A) (maximalIdeal A) n :=
  (Submodule.quotEquivOfEq _ _
      ((Stacks.Conormal.smul_top_eq_comap (maximalIdeal A) n).trans
        (Stacks.Conormal.ker_toPiece (maximalIdeal A) n).symm)).trans
    ((Stacks.Conormal.toPiece (maximalIdeal A) n).quotKerEquivOfSurjective
      (Stacks.Conormal.toPiece_surjective (maximalIdeal A) n))

/-- For `y ∈ 𝔪ⁿ`, `gradedPieceEquivPiece A n` sends the class of `y` in `gradedPiece A n` to
`Stacks.Conormal.toPiece (maximalIdeal A) n y`. -/
@[simp]
theorem gradedPieceEquivPiece_gradedPieceMk (y : ↥(maximalIdeal A ^ n)) :
    gradedPieceEquivPiece A n (gradedPieceMk A n y)
      = Stacks.Conormal.toPiece (maximalIdeal A) n y :=
  LinearMap.quotKerEquivOfSurjective_apply_mk _
    (Stacks.Conormal.toPiece_surjective (maximalIdeal A) n) y

end IsLocalRing

end
