module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsCancelTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSquareZeroThickening

/-! # Cancelling an extension of scalars inside a tensor product, as sheaves of modules

Let `f : O₁ ⟶ O₂` be a morphism of sheaves of commutative rings on a site `(C, J)`, let `G` be
a sheaf of `O₁`-modules and let `H` be a sheaf of `O₂`-modules. The identity

`G ⊗_{O₁} H|_{O₁} = (O₂ ⊗_{O₁} G) ⊗_{O₂} H`

is `Stacks.FlatChangeOfRings.cancelExtendScalarsTensorSheafIso'`, and
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsCancelTensor` states it for the
underlying sheaves of **abelian groups**: its two sides are modules over different rings, so it
is not literally an isomorphism of sheaves of modules. What is true, and what this file
records, is that the right-hand side *restricted along `f`* is isomorphic to the left-hand side
as a sheaf of `O₁`-modules.

The comparison is assembled from two maps that already exist, so that its formula on pure
tensors comes for free:

* the unit `G ⟶ (O₂ ⊗_{O₁} G)|_{O₁}` of `Stacks.FlatChangeOfRings.extendScalarsAdjunction`,
  tensored on the right with `H|_{O₁}`;
* `Stacks.SheafOfModules.FlatSquareZero.reductionTensorMap` at `q := 𝟙`, which turns the tensor
  product over `O₁` of two sheaves of `O₂`-modules restricted along `f` into the restriction of
  their tensor product over `O₂`.

## Main definitions

* `Stacks.FlatChangeOfRings.cancelExtendScalarsTensorMap`:
  `G ⊗_{O₁} H|_{O₁} ⟶ ((O₂ ⊗_{O₁} G) ⊗_{O₂} H)|_{O₁}` as a morphism of sheaves of
  `O₁`-modules.

## Main results

* `Stacks.FlatChangeOfRings.cancelExtendScalarsTensorMap_tmul`: **the comparison on a pure
  tensor**, `a ⊗ x ↦ unit(a) ⊗ x`, where `unit` is the unit of extension of scalars. A morphism
  out of a tensor product sheaf is determined by its values on the images of pure tensors, so
  this is what makes the comparison composable with the multiplication maps of Stacks 08M4 and
  Stacks 08MQ.
* `Stacks.FlatChangeOfRings.isIso_cancelExtendScalarsTensorMap`: **the comparison is an
  isomorphism.** Its image under `SheafOfModules.toSheaf` is
  `Stacks.FlatChangeOfRings.cancelExtendScalarsTensorSheafIso'`, and that functor reflects
  isomorphisms.

## Implementation notes

**Spellings.** Two pairs of definitionally equal spellings meet here. The ring sheaf of `O` is
written `Stacks.commRingSheafToRingSheaf O`, which is `(sheafCompose J (forget₂ CommRingCat
RingCat)).obj O`, and is definitionally `Stacks.SheafOfModules.Tensor.ringSheaf O`, over which
`Stacks.SheafOfModules.Tensor.sheafTensor` and the pure-tensor lemmas of
`Stacks.SheafOfModules.FlatSquareZero` are stated; the structure map is written
`Stacks.FlatChangeOfRings.ringSheafMap f`, which is
`Stacks.SheafOfModules.FlatSquareZero.ringMap f`. The first of each pair is used because the
surrounding change-of-rings material is phrased that way.

Tensoring on the right by `H` is `(Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj H`, and
the unit of sheafification of the objectwise tensor product is spelled out as the unit of
`PresheafOfModules.sheafificationAdjunction` at `PresheafOfModules.tensorObj`, which is the
spelling `Stacks.SheafOfModules.FlatSquareZero.reductionTensorMap_tmul` is stated at.

**Why invertibility needs the unit on sections.** The identification of the comparison with
the abelian-sheaf isomorphism `Stacks.FlatChangeOfRings.cancelExtendScalarsTensorSheafIso'`
goes through `Stacks.FlatChangeOfRings.presheafCancelComparison'_apply`, so it needs the value
of the unit of `Stacks.FlatChangeOfRings.extendScalarsAdjunction` on sections, namely
`x ↦ 1 ⊗ x`. That is available because that adjunction is built from
`Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction`, the presheaf-level adjunction
supplied as data: the `Nonempty`-wrapped form
`Stacks.PresheafOfModules.ChangeOfRings.changeOfRings_adjoint_restrictScalars` would record
nothing about *which* adjunction `Classical.choice` produced, and an adjunction between a fixed
pair of functors is not unique as data, so no formula for its unit could be proved.

## References

* [Stacks Project, Tag 05V4](https://stacks.math.columbia.edu/tag/05V4)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 08M4](https://stacks.math.columbia.edu/tag/08M4)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe v u w

namespace Stacks.FlatChangeOfRings

open Stacks

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {O₁ O₂ : Sheaf J CommRingCat.{w}} (f : O₁ ⟶ O₂)

/-- **The comparison `G ⊗_{O₁} H|_{O₁} ⟶ ((O₂ ⊗_{O₁} G) ⊗_{O₂} H)|_{O₁}`**, as a morphism of
sheaves of `O₁`-modules: the sheaf-of-modules form of
`Stacks.FlatChangeOfRings.cancelExtendScalarsTensorSheafIso'`, which can only be stated for the
underlying sheaves of abelian groups because its two sides are modules over different rings.

It is the unit of `Stacks.FlatChangeOfRings.extendScalarsAdjunction` tensored on the right with
`H|_{O₁}`, followed by `Stacks.SheafOfModules.FlatSquareZero.reductionTensorMap` at `q := 𝟙`,
which is the canonical map from a tensor product over `O₁` of two restrictions along `f` to the
restriction of the tensor product over `O₂`. Written this way it is `a ⊗ x ↦ unit(a) ⊗ x` on
pure tensors, by `Stacks.FlatChangeOfRings.cancelExtendScalarsTensorMap_tmul`, and it is an
isomorphism, by `Stacks.FlatChangeOfRings.isIso_cancelExtendScalarsTensorMap`. -/
noncomputable def cancelExtendScalarsTensorMap
    (G : SheafOfModules.{w} (commRingSheafToRingSheaf O₁))
    (H : SheafOfModules.{w} (commRingSheafToRingSheaf O₂)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor O₁).flip.obj
        ((SheafOfModules.restrictScalars.{w} (ringSheafMap f)).obj H)).obj G ⟶
      (SheafOfModules.restrictScalars.{w} (ringSheafMap f)).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor O₂).flip.obj
            H).obj ((extendScalars f).obj G)) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor O₁).flip.obj
      ((SheafOfModules.restrictScalars.{w} (ringSheafMap f)).obj H)).map
      ((extendScalarsAdjunction f).unit.app G) ≫
    Stacks.SheafOfModules.FlatSquareZero.reductionTensorMap f ((extendScalars f).obj G)
      ((SheafOfModules.restrictScalars.{w} (ringSheafMap f)).obj H) H (𝟙 _)

open Stacks.SheafOfModules.FlatSquareZero in
/-- **The comparison on a pure tensor**: a section `a ⊗ x` of `G ⊗_{O₁} H|_{O₁}` over an object
`U`, read through the unit of sheafification of the objectwise tensor product, goes to
`unit(a) ⊗ x`, where `unit` is the unit of
`Stacks.FlatChangeOfRings.extendScalarsAdjunction` at `G`.

This is the formula that makes the comparison usable: the unit of sheafification of a tensor
product presheaf is locally surjective, so a morphism out of either tensor product sheaf is
determined by its values on the images of pure tensors. It is
`Stacks.SheafOfModules.FlatSquareZero.tensorRight_map_tmul` followed by
`Stacks.SheafOfModules.FlatSquareZero.reductionTensorMap_tmul` at `q := 𝟙`. -/
theorem cancelExtendScalarsTensorMap_tmul
    (G : SheafOfModules.{w} (commRingSheafToRingSheaf O₁))
    (H : SheafOfModules.{w} (commRingSheafToRingSheaf O₂)) (U : Cᵒᵖ)
    (a : G.val.obj U) (x : H.val.obj U) :
    (cancelExtendScalarsTensorMap f G H).val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf O₁)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₁).obj)).unit.app
          (PresheafOfModules.tensorObj (O := O₁.obj) G.val
            ((SheafOfModules.restrictScalars.{w} (ringSheafMap f)).obj H).val)).app U
            (a ⊗ₜ[O₁.obj.obj U] x)) =
      ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf O₂)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).unit.app
          (PresheafOfModules.tensorObj (O := O₂.obj) ((extendScalars f).obj G).val H.val)).app U
        ((((extendScalarsAdjunction f).unit.app G).val.app U a :
            ((extendScalars f).obj G).val.obj U) ⊗ₜ[O₂.obj.obj U] x) := by
  have h1 := tensorRight_map_tmul O₁ ((SheafOfModules.restrictScalars.{w} (ringSheafMap f)).obj H)
    ((extendScalarsAdjunction f).unit.app G) U a x
  have h2 := reductionTensorMap_tmul f ((extendScalars f).obj G)
    ((SheafOfModules.restrictScalars.{w} (ringSheafMap f)).obj H) H (𝟙 _) U
    (((extendScalarsAdjunction f).unit.app G).val.app U a) x
  exact (congrArg (fun z => (reductionTensorMap f ((extendScalars f).obj G)
    ((SheafOfModules.restrictScalars.{w} (ringSheafMap f)).obj H) H (𝟙 _)).val.app U z) h1).trans h2

open Stacks.SheafOfModules.FlatSquareZero in
/-- **The comparison on a pure tensor, with the unit spelled out**: `a ⊗ x` goes to
`(1 ⊗ a) ⊗ x`, the first factor read through the unit of sheafification of the sectionwise
extension of scalars. This is `Stacks.FlatChangeOfRings.cancelExtendScalarsTensorMap_tmul` with
the unit of `Stacks.FlatChangeOfRings.extendScalarsAdjunction` evaluated, which is available
because that adjunction is built from
`Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction` and so has the unit
`x ↦ 1 ⊗ x`. It is this formula that lets the comparison be identified with
`Stacks.FlatChangeOfRings.cancelExtendScalarsTensorSheafIso'`. -/
private lemma cancelExtendScalarsTensorMap_one_tmul
    (G : SheafOfModules.{w} (commRingSheafToRingSheaf O₁))
    (H : SheafOfModules.{w} (commRingSheafToRingSheaf O₂)) (U : Cᵒᵖ)
    (a : G.val.obj U) (x : H.val.obj U) :
    letI : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := (f.hom.app U).hom.toAlgebra
    letI : Module (O₁.obj.obj U) (((sheafToPresheaf J CommRingCat).obj O₂).obj U) :=
      (f.hom.app U).hom.toModule
    (cancelExtendScalarsTensorMap f G H).val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf O₁)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₁).obj)).unit.app
          (PresheafOfModules.tensorObj (O := O₁.obj) G.val
            ((SheafOfModules.restrictScalars.{w} (ringSheafMap f)).obj H).val)).app U
            (a ⊗ₜ[O₁.obj.obj U] x)) =
      ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf O₂)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).unit.app
          (PresheafOfModules.tensorObj (O := O₂.obj) ((extendScalars f).obj G).val H.val)).app U
        ((PresheafOfModules.Hom.app (toExtendScalarsVal f G) U
            ((1 : O₂.obj.obj U) ⊗ₜ[O₁.obj.obj U] a)) ⊗ₜ[O₂.obj.obj U] x) := by
  exact cancelExtendScalarsTensorMap_tmul f G H U a x

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The morphism of sheaves of modules extending a morphism out of a presheaf of modules
along the unit of sheafification agrees with it on sections. -/
private lemma sheafificationLiftUnitApp
    {R₀ : Cᵒᵖ ⥤ RingCat.{w}} {R : Sheaf J RingCat.{w}} (α : R₀ ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    (P : PresheafOfModules.{w} R₀) (N : SheafOfModules.{w} R)
    (t : P ⟶ (PresheafOfModules.restrictScalars α).obj N.val)
    (U : Cᵒᵖ) (z : P.obj U) :
    ((PresheafOfModules.sheafificationHomEquiv α).symm t).val.app U
        (((PresheafOfModules.sheafificationAdjunction α).unit.app P).app U z) =
      PresheafOfModules.Hom.app t U z :=
  congrArg (fun k => PresheafOfModules.Hom.app k U z)
    ((PresheafOfModules.sheafificationHomEquiv α).apply_symm_apply t)

/-- The morphism of presheaves of `O₁`-modules which
`Stacks.FlatChangeOfRings.cancelExtendScalarsTensorMap` extends along the unit of
sheafification: `Stacks.FlatChangeOfRings.presheafCancelComparison'` followed by the unit of
sheafification of the tensor product over `O₂`.

The target is spelled as a restriction of scalars along the identity because that is what
`PresheafOfModules.sheafificationHomEquiv` expects; restriction of scalars does not change the
underlying presheaf, so this is the same object as the target of
`Stacks.FlatChangeOfRings.presheafCancelComparison'` followed by that unit. -/
private noncomputable def cancelPresheafLift
    (G : SheafOfModules.{w} (commRingSheafToRingSheaf O₁))
    (H : SheafOfModules.{w} (commRingSheafToRingSheaf O₂)) :
    (tensorRightOf O₁
        ((PresheafOfModules.restrictScalars (ringSheafMap f).hom).obj H.val)).obj G.val ⟶
      (PresheafOfModules.restrictScalars (𝟙 (commRingSheafToRingSheaf O₁).obj)).obj
        ((SheafOfModules.restrictScalars.{w} (ringSheafMap f)).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor O₂).flip.obj H).obj
            ((extendScalars f).obj G))).val :=
  presheafCancelComparison' f G H ≫
    (PresheafOfModules.restrictScalars (ringSheafMap f).hom).map
      ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf O₂)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).unit.app
          (PresheafOfModules.tensorObj (O := O₂.obj) ((extendScalars f).obj G).val H.val))

open Stacks.SheafOfModules.FlatSquareZero in
/-- The comparison **is** the extension of `Stacks.FlatChangeOfRings.cancelPresheafLift` along
the unit of sheafification. Both sides are morphisms of sheaves of modules out of a tensor
product sheaf, so they are compared on pure tensors, where both are
`a ⊗ x ↦ (1 ⊗ a) ⊗ x`. -/
private lemma cancelExtendScalarsTensorMap_eq
    (G : SheafOfModules.{w} (commRingSheafToRingSheaf O₁))
    (H : SheafOfModules.{w} (commRingSheafToRingSheaf O₂)) :
    cancelExtendScalarsTensorMap f G H =
      (PresheafOfModules.sheafificationHomEquiv
        (𝟙 (commRingSheafToRingSheaf O₁).obj)).symm (cancelPresheafLift f G H) := by
  apply tensorSheaf_hom_ext O₁ G ((SheafOfModules.restrictScalars.{w} (ringSheafMap f)).obj H)
  intro U a x
  have hL := cancelExtendScalarsTensorMap_one_tmul f G H U a x
  have hR := sheafificationLiftUnitApp (𝟙 (commRingSheafToRingSheaf O₁).obj) _ _
    (cancelPresheafLift f G H) U (a ⊗ₜ[O₁.obj.obj U] x)
  have hP := presheafCancelComparison'_apply f G H U a x
  refine hL.trans (Eq.trans ?_ hR.symm)
  exact congrArg (fun z => ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf O₂)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).unit.app
          (PresheafOfModules.tensorObj (O := O₂.obj)
            ((extendScalars f).obj G).val H.val)).app U z) hP.symm

/-- On underlying presheaves of abelian groups, `Stacks.FlatChangeOfRings.cancelPresheafLift`
is `Stacks.FlatChangeOfRings.presheafCancelComparison'` followed by the unit of sheafification:
the underlying presheaf of abelian groups of the unit of sheafification of a presheaf of
modules is the unit of sheafification of abelian groups, definitionally in this tree. -/
private lemma toPresheaf_map_cancelPresheafLift
    (G : SheafOfModules.{w} (commRingSheafToRingSheaf O₁))
    (H : SheafOfModules.{w} (commRingSheafToRingSheaf O₂)) :
    (PresheafOfModules.toPresheaf (commRingSheafToRingSheaf O₁).obj).map
        (cancelPresheafLift f G H) =
      (PresheafOfModules.toPresheaf (commRingSheafToRingSheaf O₁).obj).map
          (presheafCancelComparison' f G H) ≫
        (sheafificationAdjunction J AddCommGrpCat.{w}).unit.app
          ((PresheafOfModules.toPresheaf (commRingSheafToRingSheaf O₂).obj).obj
            ((tensorRightOf O₂ H.val).obj ((extendScalars f).obj G).val)) := rfl

/-- **The comparison underlies `Stacks.FlatChangeOfRings.cancelExtendScalarsTensorSheafIso'`.**
Both are morphisms of sheaves of abelian groups out of a sheafification, so they are compared
through the sheafification adjunction: on the presheaf of abelian groups underlying the
objectwise tensor product both restrict to
`Stacks.FlatChangeOfRings.presheafCancelComparison'` followed by the unit of sheafification. -/
private lemma toSheaf_map_cancelExtendScalarsTensorMap
    (G : SheafOfModules.{w} (commRingSheafToRingSheaf O₁))
    (H : SheafOfModules.{w} (commRingSheafToRingSheaf O₂)) :
    (SheafOfModules.toSheaf (commRingSheafToRingSheaf O₁)).map
        (cancelExtendScalarsTensorMap f G H) =
      (cancelExtendScalarsTensorSheafIso' f G H).hom := by
  refine (congrArg (SheafOfModules.toSheaf (commRingSheafToRingSheaf O₁)).map
    (cancelExtendScalarsTensorMap_eq f G H)).trans ?_
  refine (PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm _ _).trans ?_
  refine Eq.trans ?_ (cancelExtendScalarsTensorSheafIso'_hom f G H).symm
  apply ((sheafificationAdjunction J AddCommGrpCat.{w}).homEquiv _ _).injective
  refine (Equiv.apply_symm_apply _ _).trans ?_
  refine Eq.trans (toPresheaf_map_cancelPresheafLift f G H) ?_
  exact ((Adjunction.homEquiv_unit (sheafificationAdjunction J AddCommGrpCat.{w}) _ _ _).trans
    ((sheafificationAdjunction J AddCommGrpCat.{w}).unit_naturality _)).symm

/-- **`Stacks.FlatChangeOfRings.cancelExtendScalarsTensorMap` is an isomorphism**, so the
identity `G ⊗_{O₁} H|_{O₁} = (O₂ ⊗_{O₁} G) ⊗_{O₂} H` holds as sheaves of `O₁`-modules and not
merely as sheaves of abelian groups.

The morphism of sheaves of abelian groups underlying it is
`Stacks.FlatChangeOfRings.cancelExtendScalarsTensorSheafIso'`, by
`Stacks.FlatChangeOfRings.toSheaf_map_cancelExtendScalarsTensorMap`, and
`SheafOfModules.toSheaf` reflects isomorphisms. -/
instance isIso_cancelExtendScalarsTensorMap
    (G : SheafOfModules.{w} (commRingSheafToRingSheaf O₁))
    (H : SheafOfModules.{w} (commRingSheafToRingSheaf O₂)) :
    IsIso (cancelExtendScalarsTensorMap f G H) := by
  have h : IsIso ((SheafOfModules.toSheaf (commRingSheafToRingSheaf O₁)).map
      (cancelExtendScalarsTensorMap f G H)) :=
    ⟨(cancelExtendScalarsTensorSheafIso' f G H).inv,
      (congrArg (fun k => k ≫ (cancelExtendScalarsTensorSheafIso' f G H).inv)
          (toSheaf_map_cancelExtendScalarsTensorMap f G H)).trans
        (cancelExtendScalarsTensorSheafIso' f G H).hom_inv_id,
      (congrArg (fun k => (cancelExtendScalarsTensorSheafIso' f G H).inv ≫ k)
          (toSheaf_map_cancelExtendScalarsTensorMap f G H)).trans
        (cancelExtendScalarsTensorSheafIso' f G H).inv_hom_id⟩
  have hr : (SheafOfModules.toSheaf.{w} (commRingSheafToRingSheaf O₁)).ReflectsIsomorphisms :=
    inferInstance
  exact @isIso_of_reflects_iso _ _ _ _ _ _ (cancelExtendScalarsTensorMap f G H)
    (SheafOfModules.toSheaf.{w} (commRingSheafToRingSheaf O₁)) h hr

end Stacks.FlatChangeOfRings

end
