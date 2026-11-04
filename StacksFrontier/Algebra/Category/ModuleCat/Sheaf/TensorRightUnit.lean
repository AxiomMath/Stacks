module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactness

/-!
# The structure sheaf is a left unit for the sheafified tensor product

Let `O` be a presheaf of commutative rings on a category `C`. The objectwise tensor product
`PresheafOfModules.tensorObj` of the free presheaf of modules of rank one
`PresheafOfModules.unit` with a presheaf of modules `M` is `M` itself: on sections over `X` it is
the canonical isomorphism `O(X) ⊗_{O(X)} M(X) ≅ M(X)`. Sheafifying, the tensor product
`Stacks.SheafOfModules.Tensor.sheafTensor` of the structure sheaf with a sheaf of modules `F` is
`F`.

## Main definitions

* `Stacks.unitTensorApp`: the unitor `O(X) ⊗_{O(X)} M(X) ≅ M(X)` on sections over `X`.
* `Stacks.unitTensorObjIso`: the presheaf-level unitor `O ⊗ M ≅ M`.
* `Stacks.unitSheafTensorIso`: the sheaf-level unitor `O ⊗_O F ≅ F`.

## References

* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

universe v u w

namespace Stacks

section Presheaf

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- **The unitor of the objectwise tensor product, on sections over one object**:
`O(X) ⊗_{O(X)} M(X) ≅ M(X)`. -/
def unitTensorApp (M : PresheafOfModules.{w} (ringPresheaf O)) (X : Cᵒᵖ) :
    (PresheafOfModules.tensorObj (O := O) (PresheafOfModules.unit (ringPresheaf O)) M).obj X ≅
      M.obj X :=
  (TensorProduct.lid ((ringPresheaf O).obj X) (M.obj X)).toModuleIso

/-- **The structure presheaf is a unit for the objectwise tensor product**: `O ⊗ M ≅ M`,
objectwise the canonical isomorphism `O(X) ⊗_{O(X)} M(X) ≅ M(X)`. -/
def unitTensorObjIso (M : PresheafOfModules.{w} (ringPresheaf O)) :
    PresheafOfModules.tensorObj (O := O) (PresheafOfModules.unit (ringPresheaf O)) M ≅ M :=
  PresheafOfModules.isoMk (unitTensorApp M) fun X _ f => ModuleCat.hom_ext <|
    TensorProduct.ext' fun r y => (M.map_smul f (r : (ringPresheaf O).obj X) y).symm

/-- The unitor of the objectwise tensor product sends `r ⊗ m` to `r · m`. -/
@[simp]
theorem unitTensorApp_hom_tmul (M : PresheafOfModules.{w} (ringPresheaf O)) (X : Cᵒᵖ)
    (r : (ringPresheaf O).obj X) (m : M.obj X) :
    (unitTensorApp M X).hom (r ⊗ₜ[(ringPresheaf O).obj X] m) = r • m :=
  rfl

end Presheaf

section Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {O : Sheaf J CommRingCat.{w}}

/-- **The structure sheaf is a unit for the tensor product of sheaves of modules**:
`O ⊗_O F ≅ F`, the sheafification of the presheaf-level unitor `Stacks.unitTensorObjIso`
followed by the counit of the sheafification adjunction at `F`. -/
def unitSheafTensorIso (F : SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf O)) :
    ((SheafOfModules.Tensor.sheafTensor O).obj
        (SheafOfModules.unit (SheafOfModules.Tensor.ringSheaf O))).obj F ≅ F :=
  (PresheafOfModules.sheafification (𝟙 (SheafOfModules.Tensor.ringSheaf O).obj)).mapIso
      (unitTensorObjIso (O := O.obj) F.val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 (SheafOfModules.Tensor.ringSheaf O).obj)).counit).app F

end Sheaf

end Stacks

end
