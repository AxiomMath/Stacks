module

public import StacksFrontier.AlgebraicGeometry.TwistTensor.GradedLaurentMul

/-!
# The graded Laurent recognition isomorphism preserves the algebra unit

Let `R` be a sheaf of `ℤ`-graded algebras on a scheme whose multiplications are isomorphisms and
whose degree-zero piece is invertible, and let `β : R₁ ≅ ℒ`. The recognition isomorphism
`Stacks.AlgebraicGeometry.GradedLaurentRecognition.gradedIso : R ≅ ⨁_n ℒ^{⊗ n}` carries the unit
of `R` to the unit of the Laurent algebra.

## Main results

* `Stacks.AlgebraicGeometry.GradedLaurentRecognition.oneHom_laurent`: the unit morphism of a
  Laurent algebra is the identity of the monoidal unit.
* `Stacks.AlgebraicGeometry.GradedLaurentRecognition.oneHom_comp_pieceIso_zero`: the degreewise
  recognition comparison preserves the graded-algebra unit.
* `Stacks.AlgebraicGeometry.GradedLaurentRecognition.oneHom_comp_gradedIso_app_zero`: the
  recognition isomorphism preserves the graded-algebra unit.

## References

* [Stacks Project, Tag 01O1](https://stacks.math.columbia.edu/tag/01O1)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

universe u

namespace Stacks.AlgebraicGeometry.GradedLaurentRecognition

variable {T : Scheme.{u}}
  (R : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf T.toRingedSpace))
  (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-! ### The unit of a Laurent algebra -/

/-- **The unit morphism of the Laurent algebra `⨁_n ℒ^{⊗ n}` is the identity of the monoidal
unit.** -/
public theorem oneHom_laurent :
    SheafOfModules.GradedAlgebra.oneHom (laurent L)
      = CategoryStruct.id (SheafOfModules.unit (structureRingSheaf T.toRingedSpace)) :=
  (SheafOfModules.unitHomEquiv
    ((laurent L).piece 0)).symm_apply_apply (CategoryStruct.id _)

/-! ### The recognition comparison preserves the unit -/

variable (β : R.piece 1 ≅ L)
  (hmul : ∀ i j : ℤ, IsIso (SheafOfModules.GradedAlgebra.mulSheaf R i j))
  (hinv : Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T)
    (R.piece 0))

/-- **The degreewise recognition comparison preserves the graded-algebra unit**: in degree zero,
`R`'s unit morphism followed by the comparison is the unit morphism of the Laurent algebra. -/
public theorem oneHom_comp_pieceIso_zero :
    SheafOfModules.GradedAlgebra.oneHom R ≫ (pieceIso R L β hmul hinv 0).hom
      = SheafOfModules.GradedAlgebra.oneHom (laurent L) := by
  rw [oneHom_laurent]
  exact (@asIso _ _ _ _ (SheafOfModules.GradedAlgebra.oneHom R)
    (ProjRepresentsF1.isIso_oneHom R (isSheafStruct T) hinv (hmul 0 0))).hom_inv_id

/-- **The recognition isomorphism `gradedIso` preserves the graded-algebra unit.** -/
public theorem oneHom_comp_gradedIso_app_zero :
    SheafOfModules.GradedAlgebra.oneHom R ≫ (gradedIso R L β hmul hinv).hom.app 0
      = SheafOfModules.GradedAlgebra.oneHom (laurent L) :=
  oneHom_comp_pieceIso_zero R L β hmul hinv

end Stacks.AlgebraicGeometry.GradedLaurentRecognition

end
