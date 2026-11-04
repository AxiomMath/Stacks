module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaUnit
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.HmulProjectionSection

/-!
# Multiplication crosses the left unitor of the tensor product of module sheaves

The projection formula of [Stacks, Tag 0EX3] (c) ends with the left unitor
`𝒪_{X''} ⊗_{𝒪_{X''}} M ≅ M` of the tensor product of module sheaves, and the computation of the
right-hand end of the comparison map of (c) needs multiplication by a global function, acting in
the structure-sheaf factor, to cross it.

It does, and for the only reason available: on a pure tensor the left unitor is `r ⊗ x ↦ r • x`,
multiplication by `c` in the structure-sheaf factor sends `r ⊗ x` to `(c|_U * r) ⊗ x`, and
`(c|_U * r) • x = c|_U • (r • x)` is the associativity of the action.

The analogous statement for the **right** unitor and a morphism in the module factor is proved as
`Stacks.RingedSpace.tensorSheafUnitRightIso_naturality`, and the proof below is that one
transposed: the same two extensionality principles for a sheafified tensor product, the same
section formula for the tensor product of two morphisms, and the section formula for the other
unitor.

## Main results

* `…TopDegreeBaseChange.tensorSheafUnitLeftIso_sectionScalar`: **the left unitor carries
  multiplication by a global function in the structure-sheaf factor to multiplication by that
  function.**

## Implementation notes

*Why the proof is on sections and not transported.* Multiplication by a function in one tensor
factor is not the image of anything under a functor the library has a naturality statement for;
the two sides have to be compared where they are defined, which for a sheafified tensor product
means on pure tensors of local sections, after
`CategoryTheory.PresheafOfModules.sheafification_hom_ext` and
`CategoryTheory.PresheafOfModules.tensorObj_hom_ext`.

*Why multiplication is not written `c • 𝟙`.* The `Γ(X, ⊤)`-linear structure on module sheaves is
not an instance, so a scalar multiple of an identity would need that structure in scope at every
use; `AlgebraicGeometry.IntegralTransformQcoh.sectionScalar` is the multiplication operator
itself. This is the discipline of
`…TopDegreeBaseChange.rightDerived_moduleGlobalSections_map_baseScalar`.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.IntegralTransformQcoh
open RingedSpaceModuleAdjunction PresheafOfModules CategoryTheory.Sheaf
open Stacks.RingedSpace
open scoped CategoryTheory.Prod TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

/-- **The left unitor carries multiplication by a global function in the structure-sheaf factor
to multiplication by that function.** For a scheme `X`, a global function `c` on it and a module
`M`, the unitor `𝒪_X ⊗_{𝒪_X} M ≅ M` intertwines `(multiplication by c) ⊗ 𝟙` with multiplication
by `c`.

On a pure tensor `r ⊗ x` of local sections over `U` the left-hand side is `(c|_U * r) • x` and
the right-hand side is `c|_U • (r • x)`; the identity is `mul_smul`. -/
theorem tensorSheafUnitLeftIso_sectionScalar (X : Scheme.{u}) (c : Γ(X, ⊤)) (M : X.Modules) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
          ((sectionScalar X c (Scheme.unitModule X) ×ₘ 𝟙 M :
            ((Scheme.unitModule X, M) : _ × _) ⟶ (Scheme.unitModule X, M))) ≫
        (tensorSheafUnitLeftIso X.toRingedSpace M).hom =
      (tensorSheafUnitLeftIso X.toRingedSpace M).hom ≫ sectionScalar X c M := by
  refine sheafification_hom_ext (tensorObj_hom_ext fun U r x => ?_)
  have l1 := tensorSheaf_map_unit_tmul X.toRingedSpace
    (sectionScalar X c (Scheme.unitModule X)) (𝟙 M) U r x
  have l2 := tensorSheafUnitLeftIso_hom_tensorSheafUnit_tmul X.toRingedSpace M U
    (Hom.app (sectionScalar X c (Scheme.unitModule X)).val U r) x
  have l3 := tensorSheafUnitLeftIso_hom_tensorSheafUnit_tmul X.toRingedSpace M U r x
  refine Eq.trans (congrArg ((tensorSheafUnitLeftIso X.toRingedSpace M).hom.val.app U) l1)
    (Eq.trans l2 (Eq.trans ?_
      (congrArg (Hom.app (sectionScalar X c M).val U) l3).symm))
  exact mul_smul (α := X.ringCatSheaf.obj.obj U) (β := M.val.obj U)
    (X.presheaf.map U.unop.leTop.op c) r x

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
