module

public import StacksFrontier.AlgebraicGeometry.TensorPowerCoherence.Basic
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.InversePairing

/-!
# The coherent multiplication in degrees `(1, -1)`

`StacksFrontier/AlgebraicGeometry/PicardBaseChange/InversePairing.lean` builds the
multiplication isomorphism `L^{⊗ 1} ⊗_O L^{⊗ -1} ≅ O` by hand, as the braiding followed by the
identification `L^{⊗ 1} ≅ L` and one step of the integer iteration, because the coherent
multiplication of [Stacks, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU) was not
available in this development; its docstring records that Tag 01CU's `mul_comm` and
`mul_one_right` fields *force* the coherent multiplication at `(1, -1)` to be that composite.
Now that the coherent multiplication exists
(`Stacks.SheafOfModules.Invertible.tensorPowerCoherence`), this file proves that identity, so a
statement about `tensorPowerMulIsoNegOne` is a statement about Tag 01CU's own multiplication.

## Main results

* `Stacks.SheafOfModules.Invertible.tensorPowerCoherence_mulIso_one_negOne`: **the coherent
  multiplication isomorphism in degrees `(1, -1)` is `tensorPowerMulIsoNegOne`.**
* `Stacks.SheafOfModules.Invertible.sectionMulNegOne_eq_coherent` and
  `globalSectionsMulNegOne_eq_coherent`: consequently the hand-built products of a section of
  `L` and a section of `L^{⊗ -1}` are the products taken with the coherent multiplication —
  which is the multiplication Tag 0CDX's clause on the global sections of an invertible sheaf
  and its inverse is about.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0CDX](https://stacks.math.columbia.edu/tag/0CDX)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry
open scoped TensorProduct

universe v u w

namespace Stacks.SheafOfModules.Invertible

attribute [local instance_reducible]
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
  Stacks.SheafOfModules.Tensor.ringSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **The coherent multiplication of Tag 01CU in degrees `(1, -1)` is the hand-built
`tensorPowerMulIsoNegOne`.** Only two of the coherence fields are needed: commutativity moves
the negative exponent into the first slot, and the normalization in degree `(n, 1)` identifies
what is left with one step of the integer iteration. -/
theorem tensorPowerCoherence_mulIso_one_negOne
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [_root_.AlgebraicGeometry.SheafOfModules.IsInvertible O hO L] :
    (tensorPowerCoherence O hO L).mulIso 1 (-1) = tensorPowerMulIsoNegOne O hO L := by
  rw [(tensorPowerCoherence O hO L).mul_comm 1 (-1),
    (tensorPowerCoherence O hO L).mul_one_right (-1), tensorPowerMulIsoNegOne]
  apply Iso.ext
  simp only [Iso.trans_hom, Category.assoc]
  rfl

/-- The product of a section of `L` and a section of `L^{⊗ -1}` is their product under the
coherent multiplication of Tag 01CU. -/
theorem sectionMulNegOne_eq_coherent
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [_root_.AlgebraicGeometry.SheafOfModules.IsInvertible O hO L] (U : Cᵒᵖ)
    (s : L.val.obj U) (t : (tensorPower O hO L (-1)).val.obj U) :
    sectionMulNegOne O hO L U s t =
      (((tensorPowerCoherence O hO L).mulIso 1 (-1)).hom.val.app U).hom
        (((Stacks.SheafOfModules.TensorSheafification.toSheafify O hO
          ((PresheafOfModules.tensorObj (O := O) ((tensorPower O hO L 1).val) ((tensorPower O hO L (-1)).val)))).app U).hom
          ((((tensorPowerOneIso O hO L).inv.val.app U).hom s) ⊗ₜ t)) := by
  rw [tensorPowerCoherence_mulIso_one_negOne]
  rfl

/-- The same at the global sections of an invertible sheaf of modules on a scheme, which is the
shape Tag 0CDX's multiplication clause is stated in. -/
theorem globalSectionsMulNegOne_eq_coherent {X : AlgebraicGeometry.Scheme.{w}} (L : X.Modules)
    [_root_.AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    (s : Γ(L, ⊤))
    (t : (tensorPower X.presheaf X.ringCatSheaf.property L (-1)).val.obj (.op ⊤)) :
    globalSectionsMulNegOne L s t =
      (((tensorPowerCoherence X.presheaf X.ringCatSheaf.property L).mulIso 1 (-1)).hom.val.app
            (.op ⊤)).hom
        (((Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf X.ringCatSheaf.property
          ((PresheafOfModules.tensorObj (O := X.presheaf) ((tensorPower X.presheaf X.ringCatSheaf.property L 1).val) ((tensorPower X.presheaf X.ringCatSheaf.property L (-1)).val)))).app (.op ⊤)).hom
          ((((tensorPowerOneIso X.presheaf X.ringCatSheaf.property L).inv.val.app
            (.op ⊤)).hom s) ⊗ₜ t)) :=
  sectionMulNegOne_eq_coherent X.presheaf X.ringCatSheaf.property L (.op ⊤) s t

end Stacks.SheafOfModules.Invertible

end
