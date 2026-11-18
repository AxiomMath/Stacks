module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorUnitSections
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsUnitor

/-!
# Two presentations of the right unitor `F ⊗ 𝒪 ≅ F` agree

For a sheaf of modules `F` on `X'`, the right unitor `F ⊗ 𝒪_{X'} ≅ F` has two presentations.

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.tensorFactorObjUnitIso` moves the structure sheaf
  out of the argument slot of `Stacks.SheafOfModules.tensorLeftFunctor` with the symmetry
  `Stacks.SheafOfModules.Invertible.tensorLeftFunctorSwap` and then cancels it on the left with
  `Stacks.SheafOfModules.Invertible.tensorLeftFunctorUnitIso`.
* `Stacks.RingedSpace.tensorSheafUnitRightIso` is the presheaf right unitor carried through
  sheafification; it satisfies the section formula `x ⊗ r ↦ r • x`
  (`Stacks.RingedSpace.tensorSheafUnitRightIso_hom_tensorSheafUnit_tmul`).

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.tensorFactorObjUnitIso_hom_eq`: the two right
  unitors are the same morphism.

## Implementation notes

Both sides are the sealed sheafification `Stacks.SheafOfModules.Tensor.sheafification` of a
morphism of presheaves of modules followed by the counit of
`Stacks.SheafOfModules.Tensor.sheafificationAdjunction` at `F`, so the statement is
`CategoryTheory.braiding_leftUnitor` on presheaves of modules — the braiding followed by the left
unitor is the right unitor — with the sheafification functor applied to it.  The private lemmas
of this file bring both sides to that form: the first unitor reaches the counit through Mathlib's
sheafification counit and `Stacks.SheafOfModules.Tensor.sheafificationIso`
(`Adjunction.leftAdjointUniq_hom_app_counit`), the second through the counit of
`Stacks.SheafOfModules.Tensor.sheafificationForgetAdjunction`, which is the same morphism.

The presheaf `F.val` is ascribed the type
`PresheafOfModules (structureRingPresheaf W.left.presheaf)`: at the spelling
`PresheafOfModules W.left.ringCatSheaf.obj` instance search does not find the monoidal structure on
presheaves of modules, and `λ_ F.val` fails to elaborate.

## References

* [The Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [The Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open AlgebraicGeometry
open Stacks.SheafOfModules.TensorSheafification (sheafify structureRingPresheaf)
open Stacks.SheafOfModules.Invertible (sheafifyForgetIso)
open Stacks.SheafOfModules (sheafifyValIso)

universe u

namespace Stacks.SheafOfModules.Tensor

variable {C : Type*} [Category C] {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- The comparison `forgetCompRestrictScalarsIdIso R` is the identity at every sheaf of modules:
restriction of scalars along the identity does not change a presheaf of modules. -/
private lemma forgetCompRestrictScalarsIdIso_inv_app (A : _root_.SheafOfModules.{u} (ringSheaf R)) :
    (forgetCompRestrictScalarsIdIso R).inv.app A = 𝟙 _ := by
  ext
  rfl

/-- The counit of `sheafificationForgetAdjunction R` is the counit of
`sheafificationAdjunction R`. -/
private lemma sheafificationForgetAdjunction_counit_app
    (A : _root_.SheafOfModules.{u} (ringSheaf R)) :
    (sheafificationForgetAdjunction R).counit.app A =
      (sheafificationAdjunction R).counit.app A := by
  rw [← Adjunction.homEquiv_symm_id, sheafificationForgetAdjunction,
    Adjunction.homEquiv_ofNatIsoRight_symm_apply, Category.id_comp,
    forgetCompRestrictScalarsIdIso_inv_app]
  exact (sheafificationAdjunction R).homEquiv_symm_id A

/-- `sheafificationIso R` intertwines the counits of Mathlib's sheafification adjunction and of
`sheafificationAdjunction R`. -/
private lemma sheafificationIso_inv_app_comp_counit_app
    (A : _root_.SheafOfModules.{u} (ringSheaf R)) :
    (sheafificationIso R).inv.app
        ((_root_.SheafOfModules.forget (ringSheaf R) ⋙
          PresheafOfModules.restrictScalars (𝟙 (ringSheaf R).obj)).obj A) ≫
      (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).counit.app A =
        (sheafificationAdjunction R).counit.app A := by
  rw [sheafificationIso_def, ← Adjunction.leftAdjointUniq_hom_app_counit
    (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj))
    (sheafificationAdjunction R) A,
    Iso.inv_hom_id_app_assoc]

end Stacks.SheafOfModules.Tensor

namespace Stacks.SheafOfModules.Invertible

variable {C : Type*} [Category C] {J : GrothendieckTopology C} (O : Cᵒᵖ ⥤ CommRingCat.{u})
  (hO : Presheaf.IsSheaf J (structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules

/-- `sheafifyForgetIso` at `F` is the counit of the sheafification adjunction at `F`. -/
private lemma sheafifyForgetIso_hom_app
    (F : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (sheafifyForgetIso O hO).hom.app F =
      (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O hO).counit.app F := by
  simp only [sheafifyForgetIso, Iso.trans_hom, NatTrans.comp_app,
    asIso_hom]
  exact Category.id_comp _

/-- `tensorLeftFunctorUnitIso` at `F` is the sheafified presheaf left unitor followed by the counit
of `Stacks.SheafOfModules.Tensor.sheafificationAdjunction` at `F`. -/
private lemma tensorLeftFunctorUnitIso_hom_app
    (F : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (tensorLeftFunctorUnitIso O hO).hom.app F =
      (Tensor.sheafification
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).map
          (λ_ (F.val : PresheafOfModules.{u} (structureRingPresheaf O))).hom ≫
        (Tensor.sheafificationAdjunction
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).counit.app
          F :=
  congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) (sheafifyForgetIso_hom_app O hO F)).trans
    (Tensor.sheafificationIso_inv_app_comp_counit_app
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩ F))

/-- `tensorLeftFunctorObjUnitIso` is the sheafification of the presheaf braiding followed by
the presheaf left unitor, followed by the counit of
`Stacks.SheafOfModules.Tensor.sheafificationAdjunction` at `F`. -/
private lemma tensorLeftFunctorObjUnitIso_hom
    (F : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (tensorLeftFunctorObjUnitIso O hO F).hom =
      (Tensor.sheafification
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).map
          (β_ (F.val : PresheafOfModules.{u} (structureRingPresheaf O))
            ((_root_.SheafOfModules.unit
              (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).val :
                PresheafOfModules.{u} (structureRingPresheaf O))).hom ≫
        (Tensor.sheafification
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).map
          (λ_ (F.val : PresheafOfModules.{u} (structureRingPresheaf O))).hom ≫
        (Tensor.sheafificationAdjunction
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).counit.app
          F :=
  congrArg (_ ≫ ·) (tensorLeftFunctorUnitIso_hom_app O hO F)

end Stacks.SheafOfModules.Invertible

namespace Stacks.SheafOfModules

variable {C : Type*} [Category C] {J : GrothendieckTopology C} (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

/-- `tensorSheafUnitRightIso` is the sheafified presheaf right unitor followed by the counit of
`Stacks.SheafOfModules.Tensor.sheafificationAdjunction` at `A`. -/
private lemma tensorSheafUnitRightIso_hom (A : _root_.SheafOfModules.{u} (Tensor.ringSheaf
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)) :
    (tensorSheafUnitRightIso 𝒪 h𝒪 A).hom =
      (Tensor.sheafification
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).map
          (ρ_ A.val).hom ≫
        (Tensor.sheafificationAdjunction
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).counit.app
          A :=
  congrArg (_ ≫ ·) (Tensor.sheafificationForgetAdjunction_counit_app _ A)

end Stacks.SheafOfModules

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules

/-- The right unitor `F ⊗ 𝒪_{X'} ⟶ F` of the tensor factor is the right unitor
`Stacks.RingedSpace.tensorSheafUnitRightIso` of the tensor product sheaf. -/
theorem tensorFactorObjUnitIso_hom_eq (R : Type u) [CommRing R]
    (W : Over (Spec (CommRingCat.of R)))
    (F : _root_.SheafOfModules.{u} W.left.ringCatSheaf) :
    (tensorFactorObjUnitIso R W F).hom =
      (Stacks.RingedSpace.tensorSheafUnitRightIso W.left.toRingedSpace F).hom := by
  let G : PresheafOfModules.{u} (structureRingPresheaf W.left.presheaf) := F.val
  refine (Stacks.SheafOfModules.Invertible.tensorLeftFunctorObjUnitIso_hom _ (ringSheafCond W.left)
    F).trans ?_
  refine ((Stacks.SheafOfModules.Tensor.sheafification _).map_comp_assoc _ _ _).symm.trans ?_
  refine (congrArg (fun k ↦ (Stacks.SheafOfModules.Tensor.sheafification _).map k ≫ _)
    (braiding_leftUnitor G)).trans ?_
  exact (Stacks.SheafOfModules.tensorSheafUnitRightIso_hom W.left.toRingedSpace.sheaf.obj
    (Stacks.RingedSpace.structureRingSheaf W.left.toRingedSpace).property F).symm

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
