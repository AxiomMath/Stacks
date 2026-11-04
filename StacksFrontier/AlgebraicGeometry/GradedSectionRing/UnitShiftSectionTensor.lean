module

public import StacksFrontier.AlgebraicGeometry.GradedSectionRing.CoherentSectionMul
public import StacksFrontier.AlgebraicGeometry.SectionProduct.MonoidalRightUnitorCompare

/-!
# The pure tensor of sections at the localized structure whose unit is a sheafification

Let `O` be a sheaf of commutative rings on a site. The localized monoidal structures
`Stacks.SheafOfModules.monoidalCategory` and `Stacks.SheafInternalHom.monoidalCategory` on sheaves
of `O`-modules share the tensor product, the whiskerings and the associator, and differ only in
the unit object: the first takes `SheafOfModules.unit` and the second the sheafification of the
presheaf unit, as `AlgebraicGeometry.leftUnitor_sheafOfModulesMonoidal_hom` records. At the second
structure, this file computes the pure tensor of a morphism out of the unit and a local section
against the comparison `Stacks.SheafOfModules.tensorObjIso` with the tensor product sheaf of
[Stacks, Tag 01CA].

## Main results

* `Stacks.SheafOfModules.leftUnitor_inv_eq_sheafOfModulesMonoidal`: the two localized left
  unitors differ by the comparison of the two units.
* `Stacks.SheafOfModules.leftUnitor_inv_whiskerRight_tensorObjIso`: the left unit constraint
  against a morphism out of the unit, read through the comparison with the tensor product sheaf.
* `Stacks.SheafOfModules.tensorProductLeftUnitor_inv_val_app`: the inverse of the fixed left unit
  constraint of the tensor product sheaf, on a local section.
* `Stacks.SheafOfModules.tensorObjIso_hom_val_app_whiskerRight`: the pure tensor of a
  global section and a local section reads as `Stacks.SheafOfModules.tensorSectionsAt`.

## Implementation notes

A goal naming the two localized left unitors at once is not type-correct at the transparency at
which the rewriting tactics check their motives, so `rw` rejects it even where the two sides are
definitionally equal. The proofs are therefore composites of `Eq.trans` and `congrArg` with the
motive written out.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite MonoidalCategory
open AlgebraicGeometry
open Stacks.SheafOfModules.TensorSheafification (structureSheaf)
open AlgebraicGeometry.SheafOfModules (unitIso)

universe v u w

namespace Stacks.SheafOfModules

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The localized left unitor at `Stacks.SheafInternalHom.monoidalCategory`, whose unit is the
sheafification of the presheaf unit, is the one at `monoidalCategory`, whose unit is
`SheafOfModules.unit`, followed by the comparison of the two units. -/
theorem leftUnitor_inv_eq_sheafOfModulesMonoidal (M : SheafOfModules.{w} (structureSheaf O hO)) :
    (λ_ M).inv
      = (@MonoidalCategoryStruct.leftUnitor _ _
          (monoidalCategory O hO).toMonoidalCategoryStruct M).inv ≫
        (unitIso O hO).inv ▷ M :=
  have key : ((@MonoidalCategoryStruct.leftUnitor _ _
        (monoidalCategory O hO).toMonoidalCategoryStruct M).inv ≫
      (unitIso O hO).inv ▷ M) ≫ (λ_ M).hom = 𝟙 M :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun φ => (@MonoidalCategoryStruct.leftUnitor _ _
            (monoidalCategory O hO).toMonoidalCategoryStruct M).inv ≫ φ)
          (AlgebraicGeometry.leftUnitor_sheafOfModulesMonoidal_hom O hO M).symm).trans
        (@MonoidalCategoryStruct.leftUnitor _ _
          (monoidalCategory O hO).toMonoidalCategoryStruct M).inv_hom_id)
  ((Iso.comp_hom_eq_id (λ_ M)).mp key).symm

/-- For `s : 𝟙 ⟶ A` the composite `M ⟶ 𝟙 ⊗ M ⟶ A ⊗ M ⟶ A ⊗ₛ M` into the tensor product sheaf,
taken with the left unitor of `Stacks.SheafInternalHom.monoidalCategory`, is the fixed left unit
constraint of the tensor product sheaf followed by the sheafified tensor product of `s` (read at
the unit `SheafOfModules.unit`) with the identity. -/
theorem leftUnitor_inv_whiskerRight_tensorObjIso (A M : SheafOfModules.{w} (structureSheaf O hO))
    (s : 𝟙_ (SheafOfModules.{w} (structureSheaf O hO)) ⟶ A) :
    (λ_ M).inv ≫ (s ▷ M) ≫ (tensorObjIso O hO A M).hom
      = (Invertible.tensorProductLeftUnitor O hO M).inv ≫
          sheafifyTensorHom O hO ((unitIso O hO).inv ≫ s) (𝟙 M) := by
  have h4 : (@MonoidalCategoryStruct.leftUnitor _ _
        (monoidalCategory O hO).toMonoidalCategoryStruct M).inv ≫
      (tensorObjIso O hO (SheafOfModules.unit _) M).hom
      = (Invertible.tensorProductLeftUnitor O hO M).inv :=
    (Iso.inv_comp_eq _).mpr
      (((Iso.comp_inv_eq _).mpr
        (tensorObjIso_leftUnitor O hO M).symm).symm)
  have h3 : (((unitIso O hO).inv ≫ s) ▷ M) ≫ (tensorObjIso O hO A M).hom
      = (tensorObjIso O hO (SheafOfModules.unit _) M).hom ≫
        sheafifyTensorHom O hO ((unitIso O hO).inv ≫ s) (𝟙 M) :=
    (congrArg (fun φ => φ ≫ (tensorObjIso O hO A M).hom)
        (MonoidalCategory.tensorHom_id ((unitIso O hO).inv ≫ s) M).symm).trans
      (tensorObjIso_naturality O hO ((unitIso O hO).inv ≫ s) (𝟙 M))
  have step1 : (λ_ M).inv ≫ (s ▷ M)
      = (@MonoidalCategoryStruct.leftUnitor _ _
          (monoidalCategory O hO).toMonoidalCategoryStruct M).inv ≫
        (((unitIso O hO).inv ≫ s) ▷ M) :=
    (congrArg (fun φ => φ ≫ (s ▷ M)) (leftUnitor_inv_eq_sheafOfModulesMonoidal O hO M)).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun φ => (@MonoidalCategoryStruct.leftUnitor _ _
            (monoidalCategory O hO).toMonoidalCategoryStruct M).inv ≫ φ)
          (MonoidalCategory.comp_whiskerRight (unitIso O hO).inv s M).symm))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun φ => φ ≫ (tensorObjIso O hO A M).hom) step1).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun φ => (@MonoidalCategoryStruct.leftUnitor _ _
              (monoidalCategory O hO).toMonoidalCategoryStruct M).inv ≫ φ)
            h3).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun φ => φ ≫ sheafifyTensorHom O hO ((unitIso O hO).inv ≫ s) (𝟙 M))
              h4)))))

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The inverse of the fixed left unit constraint of the tensor product sheaf sends a section `v`
of `M` over `U` to its pure tensor with the unit section `1`. -/
theorem tensorProductLeftUnitor_inv_val_app (M : SheafOfModules.{w} (structureSheaf O hO))
    (U : Cᵒᵖ) (v : M.val.obj U) :
    (Invertible.tensorProductLeftUnitor O hO M).inv.val.app U v
      = tensorSectionsAt O hO U
          (SheafOfModules.unit (structureSheaf O hO)) M (1 : O.obj U) v :=
  (congrArg
      ((Invertible.tensorProductLeftUnitor O hO M).inv.val.app U)
      (tensorSections_leftUnitorAt O hO U M v).symm).trans
    ((SheafOfModules.comp_val_app_apply
        (Invertible.tensorProductLeftUnitor O hO M).hom
        (Invertible.tensorProductLeftUnitor O hO M).inv U _).symm.trans
      (congrArg (fun φ => SheafOfModules.Hom.val φ |>.app U _)
        (Invertible.tensorProductLeftUnitor O hO M).hom_inv_id))

/-- For `s : 𝟙 ⟶ A` the composite `M ⟶ 𝟙 ⊗ M ⟶ A ⊗ M`, taken with the left unitor of
`Stacks.SheafInternalHom.monoidalCategory`, read on sections over `U` and transported along the
comparison with the tensor product sheaf, is the section `tensorSectionsAt` of that sheaf
determined by the local section of `s` and the given section of `M`. -/
theorem tensorObjIso_hom_val_app_whiskerRight (A M : SheafOfModules.{w} (structureSheaf O hO))
    (s : 𝟙_ (SheafOfModules.{w} (structureSheaf O hO)) ⟶ A) (U : Cᵒᵖ) (v : M.val.obj U) :
    ((λ_ M).inv ≫ (s ▷ M) ≫ (tensorObjIso O hO A M).hom).val.app U v
      = tensorSectionsAt O hO U A M
          (((unitIso O hO).inv ≫ s).val.app U (1 : O.obj U)) v :=
  (congrArg (fun φ => SheafOfModules.Hom.val φ |>.app U v)
      (leftUnitor_inv_whiskerRight_tensorObjIso O hO A M s)).trans
    ((SheafOfModules.comp_val_app_apply _ _ U v).trans
      ((congrArg (fun z => (sheafifyTensorHom O hO ((unitIso O hO).inv ≫ s) (𝟙 M)).val.app U z)
          (tensorProductLeftUnitor_inv_val_app O hO M U v)).trans
        (tensorSections_tensorMapAt O hO U _ A M M
          ((unitIso O hO).inv ≫ s) (𝟙 M) (1 : O.obj U) v)))

end Stacks.SheafOfModules

end
