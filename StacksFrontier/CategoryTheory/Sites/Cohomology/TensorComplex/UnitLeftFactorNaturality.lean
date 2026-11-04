module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.UnitLeftFactorCollapse

/-!
# Naturality of the collapse of the total tensor complex against the structure sheaf

Let `(C, O)` be a ringed site. The collapse `Tot(O[0] ⊗_O B) ≅ B` of
`AlgebraicGeometry.RingedSite.structureSheafComplexTensorLeftIso` is the left unitor of the
monoidal structure of Tag 0FNG on complexes of `O`-modules, so it is natural in `B`; and on the
local pure tensor of `1` with a section `b` of `B^r` it returns `b`, in whatever spelling `c` of
the total degree `0 + r` the summand is read.

## Main results

All declarations are in the namespace `AlgebraicGeometry.RingedSite`.

* `structureSheafComplexTensorLeftIso_hom_naturality`: naturality.
* `structureSheafComplexTensorLeftIso_hom_f_val_app_tensorComplexSection`: the value on `1 ⊗ b`
  in degree `c = 0 + r`.

## References

* [Stacks Project, Tag 0FNG](https://stacks.math.columbia.edu/tag/0FNG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] ringSheafSectionsCommRing

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **The collapse `Tot(O[0] ⊗_O B) ≅ B` is natural in `B`**: it is the left unitor of the
monoidal structure on complexes. -/
theorem structureSheafComplexTensorLeftIso_hom_naturality
    {B B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (b : B ⟶ B') :
    HomologicalComplex.mapBifunctorMap (𝟙 (structureSheafComplex X)) b
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) ≫
        (structureSheafComplexTensorLeftIso X B').hom =
      (structureSheafComplexTensorLeftIso X B).hom ≫ b := by
  have h := leftUnitor_naturality
    (C := CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) b
  exact h

/-- The collapse `Tot(O[0] ⊗_O B) ≅ B` on the local pure tensor of `1` with a section `b` of
`B^r`, read in an arbitrary degree `c = 0 + r`: it is `b`, transported to degree `c`. -/
theorem structureSheafComplexTensorLeftIso_hom_f_val_app_tensorComplexSection
    (B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (r c : ℤ) (h : 0 + r = c) (W : X.C) (b : (B.X r).val.obj (op W)) :
    ((structureSheafComplexTensorLeftIso X B).hom.f c).val.app (op W)
        (tensorComplexSection X 0 r c h (structureSheafOne X W) b) =
      (B.XIsoOfEq (show r = c by omega)).hom.val.app (op W) b := by
  obtain rfl : c = r := by omega
  exact leftUnitor_hom_f_val_app_one X B c W b

end AlgebraicGeometry.RingedSite

end
