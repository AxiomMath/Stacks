module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensorExact
public import StacksFrontier.CategoryTheory.Monoidal.ReseatConstraints
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalRightUnitorCommShift
public import StacksFrontier.CategoryTheory.Triangulated.ConnectingMorphismNatTrans

/-!
# The right unitor of `D_QCoh(𝒪_X)` commutes with the shift

Let `X` be a scheme. The right unitor `K ⊗ᴸ 𝒪_X ≅ K` of the monoidal category `D_QCoh(𝒪_X)`
(`Stacks.Duality.quasiCoherentDerivedMonoidal`) commutes with the shift in `K`, for the commutation
of `- ⊗ᴸ 𝒪_X` with the shift of `Stacks.Duality.commShift_quasiCoherentDerivedTensorFlipObj`. On
`D(𝒪_X)` this is `Stacks.SheafOfModules.DerivedMonoidal.commShift_canonicalRightUnitor`, and it
passes to `D_QCoh(𝒪_X)` along the faithful inclusion, the monoidal structure of `D_QCoh(𝒪_X)` being
that of `D(𝒪_X)` restricted.

## Main results

* `Stacks.Duality.commShift_rightUnitorNatIso_quasiCoherentDerivedMonoidal`: the right unitor of
  `D_QCoh(𝒪_X)` commutes with the shift.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory

universe u

namespace Stacks.Duality

variable (X : Scheme.{u})

/-- **The right unitor of `D_QCoh(𝒪_X)` commutes with the shift.** -/
theorem commShift_rightUnitorNatIso_quasiCoherentDerivedMonoidal :
    letI := quasiCoherentDerivedMonoidal X
    NatTrans.CommShift (rightUnitorNatIso (quasiCoherentDerivedCategory X)).hom ℤ := by
  let := quasiCoherentDerivedMonoidal X
  let := commShiftDerivedTensorFlipObj X (𝟙_ (quasiCoherentDerivedCategory X)).obj
  have hu₁ : NatTrans.CommShift
      (quasiCoherentDerivedTensorFlipObjCompιIso X (𝟙_ (quasiCoherentDerivedCategory X))).hom ℤ :=
    Functor.CommShift.ofComp_compatibility _ _
  let := Scheme.Modules.canonicalDerivedMonoidal X
  let : (tensorUnitRight (DerivedCategory X.Modules)).CommShift ℤ :=
    commShiftDerivedTensorFlipObj X (𝟙_ (quasiCoherentDerivedCategory X)).obj
  have hD : NatTrans.CommShift (rightUnitorNatIso (DerivedCategory X.Modules)).hom ℤ :=
    Stacks.SheafOfModules.DerivedMonoidal.commShift_canonicalRightUnitor X.sheaf
  have hσ : NatTrans.CommShift (Functor.whiskerLeft
      (DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι
      (rightUnitorNatIso (DerivedCategory X.Modules)).hom) ℤ := inferInstance
  have hu₂ : NatTrans.CommShift
      (Functor.leftUnitor (DerivedCategoryB.derivedCategoryB (A := X.Modules)
          (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ≪≫
        (Functor.rightUnitor (DerivedCategoryB.derivedCategoryB (A := X.Modules)
          (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι).symm).hom ℤ := by
    dsimp only [Iso.trans_hom, Iso.symm_hom]
    infer_instance
  refine Stacks.Triangulated.natTransCommShift_of_whiskerRight_eq ℤ
    (DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι
    (@rightUnitorNatIso _ _ (quasiCoherentDerivedMonoidal X)).hom
    (quasiCoherentDerivedTensorFlipObjCompιIso X (𝟙_ (quasiCoherentDerivedCategory X)))
    (Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm)
    (Functor.whiskerLeft _ (rightUnitorNatIso (DerivedCategory X.Modules)).hom)
    hu₁ hu₂ hσ ?_
  ext K
  let := quasiCoherent_isMonoidal X
  have hρ := @reseat_rightUnitor _ _ (ObjectProperty.fullMonoidalSubcategory _) _ _
    (quasiCoherentCurriedTensorIso X)
    (Iso.refl (DerivedPushforward.derivedStructureSheaf X)) K
  simp only [Functor.whiskerRight_app, rightUnitorNatIso_hom_app, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.trans_inv, Iso.symm_inv, Functor.rightUnitor_hom_app,
    Functor.leftUnitor_inv_app, Category.comp_id, Category.id_comp, ObjectProperty.ι_map]
  rw [show (@MonoidalCategoryStruct.rightUnitor _ _
    (quasiCoherentDerivedMonoidal X).toMonoidalCategoryStruct K).hom = _ from hρ]
  have hw : (@MonoidalCategoryStruct.whiskerLeft _ _
      (ObjectProperty.fullMonoidalSubcategory _).toMonoidalCategoryStruct K _ _
        (𝟙 (DerivedPushforward.derivedStructureSheaf X))).hom = 𝟙 _ := by
    rw [@MonoidalCategory.whiskerLeft_id _ _ (ObjectProperty.fullMonoidalSubcategory _) K _]
    rfl
  show 𝟙 _ ≫ (@MonoidalCategoryStruct.whiskerLeft _ _
      (ObjectProperty.fullMonoidalSubcategory _).toMonoidalCategoryStruct K _ _
        (𝟙 (DerivedPushforward.derivedStructureSheaf X))).hom ≫ (ρ_ K.obj).hom =
    𝟙 _ ≫ (ρ_ K.obj).hom ≫ 𝟙 _
  rw [hw, Category.id_comp]
  exact (Category.id_comp _).trans ((Category.id_comp _).trans (Category.comp_id _)).symm

end Stacks.Duality

end
