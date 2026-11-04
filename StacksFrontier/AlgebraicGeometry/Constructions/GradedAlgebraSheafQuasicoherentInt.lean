module

public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraSheafQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraSheafCoproductInt

/-!
# Quasi-coherence of a `ℤ`-graded algebra sheaf from its pieces

`Stacks.RelativeSpec.gradedAlgebraSheaf` is quasi-coherent as soon as every homogeneous piece is:
the underlying module is the coproduct of the pieces
(`Stacks.RelativeSpec.gradedCoprodIntIsoUnderlyingModule`), and a `ℤ`-indexed coproduct of
quasi-coherent modules is quasi-coherent (`Stacks.RelativeSpec.isQuasicoherent_intCoprod`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.RelativeSpec

variable (X : Scheme.{u}) (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
  (hc : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (A.piece i).val.obj W) (b : (A.piece j).val.obj W),
    HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))

/-- **`Stacks.RelativeSpec.gradedAlgebraSheaf` is quasi-coherent as soon as every homogeneous
piece is.**

This is the form the relative spectrum consumes for a grading indexed by `ℤ`, as in
[Stacks, Tag 0FQW]: no vanishing in negative degrees is assumed, and the coproduct hypothesis of
`isQuasicoherent_gradedAlgebraSheaf` is discharged by `isQuasicoherent_intCoprod_piece`. -/
theorem isQuasicoherent_gradedAlgebraSheaf_of_piece
    (hA : ∀ n : ℤ, (A.piece n).IsQuasicoherent) :
    AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf X A hc) :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Stacks.RelativeSpec.gradedCoprodIntIsoUnderlyingModule X A hc)
    (isQuasicoherent_intCoprod X (fun n => A.piece n) hA)

end Stacks.RelativeSpec

end
