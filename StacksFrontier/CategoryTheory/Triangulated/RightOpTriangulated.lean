module

public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
public import Mathlib.CategoryTheory.Triangulated.Opposite.OpOp

/-!
# Contravariant triangulated functors read covariantly

Let `C` and `D` be categories with a shift by `ℤ` and `F : Cᵒᵖ ⥤ D` a functor, the shift of
`Cᵒᵖ` being the one of `CategoryTheory.Pretriangulated.Opposite`. The covariant reading of `F`
is `F.rightOp : C ⥤ Dᵒᵖ`. It is the composite of the triangulated equivalence
`opOp C : C ⥤ Cᵒᵖᵒᵖ` with `F.op : Cᵒᵖᵒᵖ ⥤ Dᵒᵖ`, objectwise by the identity
(`CategoryTheory.Pretriangulated.Opposite.rightOpIsoOpOpComp`). So a commutation of `F` with
the shifts gives one of `F.rightOp`, and if `F` is triangulated so is `F.rightOp`.

This is what makes a natural transformation between two contravariant triangulated functors,
such as the derived internal Hom into a fixed object, available to a dévissage stated for
covariant ones.

## Main definitions

* `CategoryTheory.Pretriangulated.Opposite.rightOpIsoOpOpComp`: `F.rightOp ≅ opOp C ⋙ F.op`.
* `CategoryTheory.Pretriangulated.Opposite.commShiftRightOp`: the commutation of `F.rightOp`
  with the shifts.

## Main results

* `CategoryTheory.Pretriangulated.Opposite.isTriangulated_rightOp`: `F.rightOp` is triangulated
  when `F` is.
-/

@[expose] public section

namespace CategoryTheory.Pretriangulated.Opposite

open Limits

variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
  (F : Cᵒᵖ ⥤ D)

/-- **The covariant reading of a contravariant functor is its opposite after `opOp`**:
`F.rightOp ≅ opOp C ⋙ F.op`, objectwise by the identity. -/
def rightOpIsoOpOpComp : F.rightOp ≅ opOp C ⋙ F.op :=
  NatIso.ofComponents (fun _ => Iso.refl _)

variable [F.CommShift ℤ]

/-- **The covariant reading of a contravariant functor commuting with the shifts commutes with
the shifts**, transported from `opOp C ⋙ F.op` along `rightOpIsoOpOpComp`. -/
noncomputable scoped instance commShiftRightOp : F.rightOp.CommShift ℤ :=
  Functor.CommShift.ofIso (rightOpIsoOpOpComp F).symm ℤ

/-- The identification `rightOpIsoOpOpComp` is compatible with the shifts. -/
noncomputable scoped instance commShift_rightOpIsoOpOpComp_hom :
    NatTrans.CommShift (rightOpIsoOpOpComp F).symm.hom ℤ :=
  Functor.CommShift.ofIso_compatibility (rightOpIsoOpOpComp F).symm ℤ

/-- **The covariant reading of a contravariant triangulated functor is triangulated.** -/
scoped instance isTriangulated_rightOp [Preadditive C] [HasZeroObject C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [Preadditive D] [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [F.IsTriangulated] : F.rightOp.IsTriangulated :=
  Functor.isTriangulated_of_iso (rightOpIsoOpOpComp F).symm

end CategoryTheory.Pretriangulated.Opposite
