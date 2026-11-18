module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseChangeUnitor
public import StacksFrontier.Deformation.ToposThickening.DerivedReductionData
public import StacksFrontier.Deformation.ToposThickening.ExtensionRestrictTensor
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorUnitOfSize

/-!
# The unit of extension of scalars is the tensor product with the structure map

Let `f : O ⟶ O₀` be a morphism of sheaves of commutative rings on a site and let `N` be a sheaf
of `O`-modules. The unit of the extension/restriction-of-scalars adjunction of Stacks 03CZ at
`N` is a morphism `N ⟶ (O₀ ⊗_O N)|_O`, and
`Deformation.ComplexLift.restrictExtensionIsoTensorRight` identifies its target with the tensor
product `N ⊗_O O₀|_O`. This file computes the resulting morphism `N ⟶ N ⊗_O O₀|_O`: it is the
inverse of the right unit law `N ≅ N ⊗_O O` of Stacks 06YM followed by tensoring `N` with the
structure map `O ⟶ O₀|_O`. On local sections both descriptions send `n` to `n ⊗ 1`.

This is the compatibility under which the second morphism of the reduction triangle
`K ⊗^L_O I ⟶ K ⟶ K ⊗^L_O O₀` is the unit of the adjunction a
`Deformation.ComplexLift.DerivedReduction` carries, so it is the remaining module-level input
to that datum: the triangle presents its third morphism as `- ⊗_O (O ⟶ O₀)`, whereas the datum
asks for the unit of the base-change adjunction.

## Main results

* `Deformation.ComplexLift.unit_comp_restrictExtensionIsoTensorRight`: the unit of the
  extension/restriction-of-scalars adjunction at `N`, read through
  `Deformation.ComplexLift.restrictExtensionIsoTensorRight`, is the inverse right unitor
  followed by `N ⊗_O -` applied to
  `Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit`.

## Implementation notes

**Everything in sight is sheafified, so the proof is a computation on local sections.** Each of
the four morphisms involved is a sheafification of a morphism of presheaves of modules composed
with a sheafification unit, and the section formulas the tree already carries are exactly what is
needed:
`Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction_unit_app_val_app_apply`
(the adjunction unit is `n ↦ 1 ⊗ n`, read through Mathlib's sheafification unit),
`Stacks.SheafOfModules.tensorSheafUnitRightIso_inv_app` (the inverse right unitor is
`n ↦ n ⊗ 1`, read through the unit of the sealed sheafification
`Stacks.SheafOfModules.Tensor.sheafificationAdjunction`) and
`Stacks.SheafOfModules.Tensor.unit_naturality_apply` (naturality of the sealed unit, which moves a
sheafified morphism past it). What is left after those is the presheaf level, where the braiding
and the whiskering are the braiding and the whiskering of `ModuleCat`: both compute on a pure
tensor by `rfl`, and the only remaining content is that the structure map sends `1` to `1`,
`Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit_val_app_one`.

**Where the two sheafifications meet.** `restrictExtensionIsoTensorRight` is
`Deformation.ComplexLift.restrictExtensionIsoSheafifyLeftTensor`, then the comparison
`Stacks.SheafOfModules.Tensor.sheafificationIso` of Mathlib's sheafification with the sealed one
inside the tensor product, then the braiding. The first factor is `PresheafOfModules.homMk`
applied to the identity of the common underlying abelian presheaf, so on sections it is the
identity, and the sheafification unit of the presheaf extension of scalars is Mathlib's
sheafification unit of `O₀|_O ⊗_{p, O} N`. The comparison carries that unit to the sealed one
(`Stacks.SheafOfModules.Tensor.unit_comp_sheafificationIso_hom_app`), which is where the
adjunction-unit formula meets the unitor formula; `restrictExtensionIsoTensorRight_toSheafify_apply`
below records this, followed by naturality of the sealed unit for the braiding.

**Why the proof is in term form.** `rw` cannot be used on the goal at
all: it mentions both spellings `Deformation.ComplexLift.Stacks.SheafOfModules.Tensor.ringSheaf O`
  and
`Stacks.SheafOfModules.Tensor.ringSheaf O` of the underlying sheaf of rings — the first from the
adjunction, the second from the tensor bifunctor — and although they are definitionally equal,
`Stacks.SheafOfModules.Tensor.ringSheaf` goes through `CategoryTheory.sheafCompose`, a plain
`def`, so the target is reported as not type-correct at `implicit` transparency and every
rewrite fails before it starts. `Eq.trans` and `congrArg` have no motive to check, so the whole
calculation is written with them; the same device is used in
`StacksFrontier/CategoryTheory/Sites/Modules/TensorUnitOfSize.lean` for the same reason.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Tag 0DIY](https://stacks.math.columbia.edu/tag/0DIY)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

open scoped TensorProduct

open Stacks.Sheaves.RingedToposModules (extendRestrictScalarsAdjunction_unit_app_val_app_apply)

universe v' u u'

namespace Deformation.ComplexLift

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O O₀ : Sheaf J CommRingCat.{u}} (f : O ⟶ O₀)

/-- The comparison `(O₀ ⊗_O N)|_O ≅ N ⊗_O O₀|_O` on the image of a local section under the
sheafification unit of the presheaf extension of scalars: the unit of the sealed sheafification
of `N ⊗_O O₀|_O` at the braided section. The comparison `sheafificationIso` carries Mathlib's
sheafification unit to the sealed one, and the braiding moves past the sealed unit by its
naturality. -/
private theorem restrictExtensionIsoTensorRight_toSheafify_apply
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (V : Cᵒᵖ)
    (y : ((restrictUnitOf f).val ⊗ N.val).obj V) :
    (((restrictExtensionIsoTensorRight f).hom.app N).val.app V)
        ((CategoryTheory.toSheafify J (PresheafOfModules.presheaf
          ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings f.hom).obj N.val))).app V y) =
      ((Stacks.SheafOfModules.Tensor.sheafificationAdjunction O).unit.app
          (N.val ⊗ (restrictUnitOf f).val)).app V
        ((β_ (restrictUnitOf f).val N.val).hom.app V y) :=
  (congrArg (fun z ↦ ((((Stacks.SheafOfModules.Tensor.sheafTensorBraiding.{u', v', u} O).app
          (restrictUnitOf f)).hom.app N).val.app V) z)
      (PresheafOfModules.hom_congr_apply'
        (Stacks.SheafOfModules.Tensor.unit_comp_sheafificationIso_hom_app O
          ((restrictUnitOf f).val ⊗ N.val)) V y)).trans
    (Stacks.SheafOfModules.Tensor.unit_naturality_apply (β_ (restrictUnitOf f).val N.val).hom V y)

/-- **The unit of extension of scalars is the tensor product with the structure map.** Read
through the identification `(O₀ ⊗_O N)|_O ≅ N ⊗_O O₀|_O` of
`Deformation.ComplexLift.restrictExtensionIsoTensorRight`, the unit of the
extension/restriction-of-scalars adjunction at a sheaf of `O`-modules `N` is the inverse of the
right unit law `N ≅ N ⊗_O O` followed by tensoring `N` with the canonical morphism
`O ⟶ O₀|_O`. On local sections both sides send `n` to `n ⊗ 1`. -/
theorem unit_comp_restrictExtensionIsoTensorRight
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (extendRestrictAdjunction f).unit.app N ≫ (restrictExtensionIsoTensorRight f).hom.app N =
      (Stacks.SheafOfModules.sheafTensorUnitNatIsoOfSize.{u, v', u'} O).inv.app N ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O).obj N).map
          (Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit
            (ringSheafMapOf J f)) := by
  apply SheafOfModules.Hom.ext
  refine PresheafOfModules.hom_ext fun V ↦ ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  have hsheaf := Stacks.SheafOfModules.structureRingIsSheaf O
  -- The adjunction unit sends a local section `x` of `N` to `1 ⊗ x`.
  have hunit : (((extendRestrictAdjunction f).unit.app N).val.app V) x = _ :=
    extendRestrictScalarsAdjunction_unit_app_val_app_apply J f.hom _ _ N V x
  -- The inverse right unitor sends `x` to `x ⊗ 1`.
  have hunitor : (((Stacks.SheafOfModules.sheafTensorUnitNatIsoOfSize.{u, v', u'} O).inv.app
      N).val.app V) x = _ :=
    Stacks.SheafOfModules.tensorSheafUnitRightIso_inv_app O.obj hsheaf N V x
  -- The structure map `O ⟶ O₀|_O` sends `1` to `1`.
  have hone := Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit_val_app_one
    (ringSheafMapOf J f) V
  -- The braiding takes `1 ⊗ x` to `x ⊗ 1`, and the whiskering takes `x ⊗ 1` to `x ⊗ f 1`.
  have htmul := congrArg (fun z ↦ x ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj V] z)
    hone.symm
  exact (congrArg (fun y ↦ ((restrictExtensionIsoTensorRight f).hom.app N).val.app V y)
      hunit).trans ((restrictExtensionIsoTensorRight_toSheafify_apply f N V _).trans
      ((congrArg (fun z ↦ ((Stacks.SheafOfModules.Tensor.sheafificationAdjunction O).unit.app
          (N.val ⊗ (restrictUnitOf f).val)).app V z) htmul).trans
      ((Stacks.SheafOfModules.Tensor.unit_naturality_apply
          (N.val ◁ (Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit
            (ringSheafMapOf J f)).val) V _).symm.trans
        (congrArg (fun y ↦
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O).obj N).map
            (Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit
              (ringSheafMapOf J f))).val.app V y) hunitor.symm))))

end Deformation.ComplexLift

end
