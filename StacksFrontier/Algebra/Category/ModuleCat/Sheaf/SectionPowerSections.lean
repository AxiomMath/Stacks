module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionPowerMorphism
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TwistActionMorphism
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerIntegerCoherence
public import StacksFrontier.AlgebraicGeometry.InverseSection.TensorPowerSection

/-!
# Multiplication by a power of a section, read on sections

Let `O` be a sheaf of commutative rings on a site, `L` an invertible `O`-module in the sense of
[Stacks, Tag 01CS] and `F` an arbitrary `O`-module. Multiplication by a morphism
`t : O ⟶ L^{⊗ n}` is the morphism `Stacks.SheafOfModules.sectionPowerAction`, defined as the
inverse of the right unit constraint followed by left whiskering. This file computes it **on
sections**: over every object it sends `x` to `x ⊗ t(1)`.

Three consequences follow, and all three are steps of the comparison map of
[Stacks, Tag 09MR].

* Multiplication by `t` depends only on the value of `t` on the unit section over the terminal
  object, the counterpart for `sectionPowerAction` of
  `Stacks.SheafOfModules.twistActionHom_congr`.
* Multiplying by `t` and then multiplying the resulting twist by `s : O ⟶ L^{⊗ m}` is
  multiplying by the product morphism `Stacks.SheafOfModules.tensorPowerMulHom` -- **with no
  reindexing comparison**, because the degrees match on the nose.
* The successor rule cutting out the powers of a global section is, on the unit section, the
  product of homogeneous sections of [Stacks, Tag 01CV].

## Main results

* `Stacks.SheafOfModules.SectionPower.tensorSectionHom_app`: multiplication by a morphism out of
  the structure sheaf sends `x` to `x ⊗ t(1)`.
* `Stacks.SheafOfModules.SectionPower.sectionPowerAction_app`: the same for
  `Stacks.SheafOfModules.sectionPowerAction`.
* `Stacks.SheafOfModules.SectionPower.sectionPowerAction_congr`: multiplication by a power
  depends only on the value of the representing morphism over the terminal object.
* `Stacks.SheafOfModules.SectionPower.sectionPowerAction_comp_actionHom`: **multiplying by `t`
  and then by `s` is multiplying by the product.**
* `Stacks.SheafOfModules.SectionPower.sectionPowerAction_comp_actionOf`: the same with the
  second factor given by a global section rather than by a morphism.
* `Stacks.SheafOfModules.SectionPower.sectionPowerSucc_app_one`: **the successor rule, read on
  the unit section**, as the product of homogeneous sections.

## Implementation notes

`Stacks.SheafOfModules.sectionPowerAction` and the middle factor of
`Stacks.SheafOfModules.sectionPowerSucc` are the *same* construction with different targets --
`Stacks.InverseSection.tensorSectionHom` -- so the section formula is proved once, for that, and
specialized twice. Its proof is the inverse of `tensorLeftFunctorObjUnitIso_hom_app` together
with `Stacks.SheafOfModules.tensorSections_tensorMapAt`; the identification of
`(tensorLeftFunctor O hO F).map σ` with the tensor bifunctor applied to `(𝟙 F, σ)` is `rfl`.

`Stacks.SheafOfModules.SectionPower.sheafUnitHomEquiv_symm_app_one` is the sheaf-level
counterpart over an arbitrary site of the presheaf-level
`Stacks.SheafOfModules.unitHomEquiv_symm_app_one` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleLocalSummand.lean`, which is why it
carries a different name: neither subsumes the other.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 09MR](https://stacks.math.columbia.edu/tag/09MR)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite MonoidalCategory
open scoped TensorProduct

universe v u w

namespace Stacks.SheafOfModules.SectionPower

open Stacks.SheafOfModules Stacks.SheafOfModules.TensorSheafification
open Stacks.SheafOfModules.TwistAction

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- **The morphism out of the structure sheaf determined by a global section takes the unit
section to that section.** This is the sheaf-level counterpart, over an arbitrary site, of the
presheaf-level `Stacks.SheafOfModules.unitHomEquiv_symm_app_one`. -/
theorem sheafUnitHomEquiv_symm_app_one (M : SheafOfModules.{w} (structureSheaf O hO))
    (s : M.sections) (U : Cᵒᵖ) :
    (M.unitHomEquiv.symm s).val.app U (1 : O.obj U) = s.eval U := by
  conv_rhs => rw [← M.unitHomEquiv.apply_symm_apply s]
  exact (SheafOfModules.unitHomEquiv_apply_coe M _ U).symm

/-- **Multiplication by a morphism `σ : O ⟶ N` sends a section `x` to `x ⊗ σ(1)`.** -/
theorem tensorSectionHom_app (F N : SheafOfModules.{w} (structureSheaf O hO))
    (σ : SheafOfModules.unit (structureSheaf O hO) ⟶ N) (U : Cᵒᵖ) (x : F.val.obj U) :
    (Stacks.InverseSection.tensorSectionHom O hO F N σ).val.app U x =
      tensorSectionsAt O hO U F N x (σ.val.app U (1 : O.obj U)) := by
  show ((((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (F))).map σ).val.app U
    ((Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso O hO F).inv.val.app U x) = _
  rw [show (Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso O hO F).inv.val.app U x =
      tensorSectionsAt O hO U F (SheafOfModules.unit (structureSheaf O hO)) x
        (1 : O.obj U) from ?_]
  · exact tensorSections_tensorMapAt O hO U F F (SheafOfModules.unit (structureSheaf O hO))
      N (𝟙 F) σ x (1 : O.obj U)
  · have hh : (Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso O hO F).hom.val.app U
        (tensorSectionsAt O hO U F (SheafOfModules.unit (structureSheaf O hO)) x
          (1 : O.obj U)) = x :=
      (tensorLeftFunctorObjUnitIso_hom_app O hO F U x 1).trans (one_smul _ x)
    refine (congrArg
      (fun y => (Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso O hO F).inv.val.app U y)
      hh).symm.trans ?_
    show (((Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso O hO F).hom ≫
      (Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso O hO F).inv).val.app U
      (tensorSectionsAt O hO U F (SheafOfModules.unit (structureSheaf O hO)) x
        (1 : O.obj U))) = _
    exact congrArg (fun morphism => morphism.val.app U
      (tensorSectionsAt O hO U F (SheafOfModules.unit (structureSheaf O hO)) x
        (1 : O.obj U))) (Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso O hO F).hom_inv_id

variable (L : SheafOfModules.{w} (structureSheaf O hO))

/-- **Multiplication by the power of a section represented by `t` sends `x` to `x ⊗ t(1)`.** -/
theorem sectionPowerAction_app
    [((Tensor.sheafTensor.{_, _, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).IsEquivalence]
    (F : SheafOfModules.{w} (structureSheaf O hO)) (n : ℤ)
    (t : SheafOfModules.unit (structureSheaf O hO) ⟶ TensorPower.tensorPower O hO L n)
    (U : Cᵒᵖ) (x : F.val.obj U) :
    (sectionPowerAction O hO L F n t).val.app U x =
      tensorSectionsAt O hO U F (TensorPower.tensorPower O hO L n) x
        (t.val.app U (1 : O.obj U)) :=
  tensorSectionHom_app O hO F (TensorPower.tensorPower O hO L n) t U x

section Terminal

variable [HasTerminal C]

/-- **Multiplication by a power of a section depends only on the value of the representing
morphism on the unit section over the terminal object.** The value over any other object is the
restriction of that one, so this is the counterpart for `sectionPowerAction` of
`Stacks.SheafOfModules.twistActionHom_congr`. -/
theorem sectionPowerAction_congr
    [((Tensor.sheafTensor.{_, _, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).IsEquivalence]
    (F : SheafOfModules.{w} (structureSheaf O hO)) (n : ℤ)
    {t t' : SheafOfModules.unit (structureSheaf O hO) ⟶ TensorPower.tensorPower O hO L n}
    (h : t.val.app (op (⊤_ C)) (1 : O.obj (op (⊤_ C))) =
      t'.val.app (op (⊤_ C)) (1 : O.obj (op (⊤_ C)))) :
    sectionPowerAction O hO L F n t = sectionPowerAction O hO L F n t' := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  rw [sectionPowerAction_app, sectionPowerAction_app,
    unitHom_app_eq_map O hO _ t U, unitHom_app_eq_map O hO _ t' U, h]

end Terminal

variable [Stacks.SheafOfModules.IsInvertible O hO L]
  [((Tensor.sheafTensor.{_, _, w, w, w}
    ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
      L).IsEquivalence]

/-- **Multiplying by `t : O ⟶ L^{⊗ j}` and then multiplying the resulting twist by
`s : O ⟶ L^{⊗ n}` is multiplying by the product morphism.** No reindexing comparison appears:
both sides land in the twist by `L^{⊗ (n + j)}`, and on a section `x` both give
`x ⊗ (s(1) · t(1))`. -/
theorem sectionPowerAction_comp_actionHom
    (F : SheafOfModules.{w} (structureSheaf O hO)) (n j : ℤ)
    (s : SheafOfModules.unit (structureSheaf O hO) ⟶ TensorPower.tensorPower O hO L n)
    (t : SheafOfModules.unit (structureSheaf O hO) ⟶ TensorPower.tensorPower O hO L j) :
    sectionPowerAction O hO L F j t ≫ twistActionHom O hO L F n j s =
      sectionPowerAction O hO L F (n + j) (tensorPowerMulHom O hO L n j s t) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  show (twistActionHom O hO L F n j s).val.app U
    ((sectionPowerAction O hO L F j t).val.app U x) = _
  rw [sectionPowerAction_app, twistActionHom_pure, sectionPowerAction_app, tensorPowerMulHom_apply]

variable [HasTerminal C]

/-- **Multiplying by `t` and then by a global section `σ` of `L^{⊗ n}` is multiplying by the
product morphism of `σ` with `t`.** This is `sectionPowerAction_comp_actionHom` with the second
factor given by a section, which is the form the graded module action of [Stacks, Tag 01CV]
takes. -/
theorem sectionPowerAction_comp_actionOf
    (F : SheafOfModules.{w} (structureSheaf O hO)) (n j : ℤ)
    (σ : (TensorPower.tensorPower O hO L n).val.obj (op (⊤_ C)))
    (t : SheafOfModules.unit (structureSheaf O hO) ⟶ TensorPower.tensorPower O hO L j) :
    sectionPowerAction O hO L F j t ≫ actionOf O hO L F n j σ =
      sectionPowerAction O hO L F (n + j)
        (tensorPowerMulHom O hO L n j
          (globalSectionHom O hO (TensorPower.tensorPower O hO L n) σ) t) :=
  sectionPowerAction_comp_actionHom O hO L F n j _ t

omit [HasTerminal C] in
/-- **The successor rule for the powers of a global section, read on the unit section.** The
morphism `sⁿ⁺¹` obtained from `t` by adjoining one copy of `s` takes the unit section to the
product, in the sense of [Stacks, Tag 01CV], of the value of `t` with the degree-one homogeneous
section attached to `s`. The product of a section of `L^{⊗ n}` with one of `L^{⊗ 1}` is
multiplication by the first power, which is the successor comparison of the defining iteration
(`Stacks.SheafOfModules.TensorPower.coherentMulIso_one_right`). -/
theorem sectionPowerSucc_app_one (s : L.sections) (n : ℤ)
    (t : SheafOfModules.unit (structureSheaf O hO) ⟶ TensorPower.tensorPower O hO L n)
    (U : Cᵒᵖ) :
    (sectionPowerSucc O hO L s n t).val.app U (1 : O.obj U) =
      tensorPowerMulSectionAt O hO U L n 1 (t.val.app U (1 : O.obj U))
        ((TensorPower.tensorPowerOneIso O hO L).inv.val.app U (s.eval U)) := by
  show (TensorPower.tensorPowerSuccIso O hO L n).hom.val.app U
      ((Stacks.InverseSection.tensorSectionHom O hO (TensorPower.tensorPower O hO L n) L
        (L.unitHomEquiv.symm s)).val.app U (t.val.app U (1 : O.obj U))) = _
  rw [tensorSectionHom_app, sheafUnitHomEquiv_symm_app_one]
  show _ = ((TensorPower.coherentMulIso O hO L n 1).hom.val.app U)
    (tensorSectionsAt O hO U (TensorPower.tensorPower O hO L n)
      (TensorPower.tensorPower O hO L 1) (t.val.app U (1 : O.obj U))
      ((TensorPower.tensorPowerOneIso O hO L).inv.val.app U (s.eval U)))
  rw [TensorPower.coherentMulIso_one_right]
  show _ = (TensorPower.tensorPowerSuccIso O hO L n).hom.val.app U
    ((Invertible.tensorProductIso O hO (Iso.refl (TensorPower.tensorPower O hO L n))
      (TensorPower.tensorPowerOneIso O hO L)).hom.val.app U
      (tensorSectionsAt O hO U _ _ (t.val.app U (1 : O.obj U))
        ((TensorPower.tensorPowerOneIso O hO L).inv.val.app U (s.eval U))))
  rw [tensorSections_tensorProductIsoAt]
  congr 2
  symm
  show ((TensorPower.tensorPowerOneIso O hO L).inv ≫
    (TensorPower.tensorPowerOneIso O hO L).hom).val.app U (s.eval U) = _
  rw [Iso.inv_hom_id]
  rfl

end Stacks.SheafOfModules.SectionPower

end
