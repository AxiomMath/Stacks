module

public import StacksFrontier.AlgebraicGeometry.DeRham.MixedTensorBaseChangeUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorPureTensors
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSquareZeroThickening
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposUnitStructureMap
public import StacksFrontier.Deformation.ToposThickening.SquareZeroIdealAction

/-!
# The inclusion of the ideal part, on pure tensors

Let `f : O ⟶ O₀` be a morphism of sheaves of commutative rings on a site, `I₀` a sheaf of
`O₀`-modules and `ι : I₀|_O ⟶ O` a morphism of sheaves of `O`-modules. The inclusion of the ideal
part `Deformation.ComplexLift.idealPartIncl f ι`, at an `O`-module `M`, is the composite

`((O₀ ⊗_O M) ⊗_{O₀} I₀)|_O ≅ M ⊗_O I₀|_O ⟶ M ⊗_O O ≅ M`

of the inverse projection formula `Deformation.ComplexLift.idealTensorRightIso`, of `M ⊗ ι` and of
the unit law. All three are built abstractly (sheafification, adjunctions, uniqueness of left
adjoints), so none of them is described on sections by its definition. This file computes them
on the classes of local pure tensors:

* the projection formula sends `m ⊗ i` to `η(m) ⊗ i`, `η : M ⟶ (O₀ ⊗_O M)|_O` the unit of the
  extension/restriction-of-scalars adjunction;
* the action of the ideal sends `m ⊗ i` to `ι(i) • m`;
* hence the inclusion of the ideal part sends `η(m) ⊗ i` to `ι(i) • m`.

These are the section formulas the compatibility of the inclusion of the ideal part with a change
of the thickening (`Deformation.ComplexLift.idealPartIncl_app_comp_unit`) is proved from.

## Main definitions

* `Deformation.ComplexLift.pureTensorClass`: the class in `A ⊗_O B` of the pure tensor `a ⊗ b` of
  local sections, i.e. its image under the sheafification unit.

## Main results

* `Deformation.ComplexLift.sheafTensorBraiding_inv_app_pureTensorClass`: the inverse symmetry of
  the tensor product sends `b ⊗ a` to `a ⊗ b`.
* `Deformation.ComplexLift.idealTensorRightIso_hom_app_pureTensorClass`: the projection formula
  `M ⊗_O I₀|_O ≅ ((O₀ ⊗_O M) ⊗_{O₀} I₀)|_O` sends `m ⊗ i` to `η(m) ⊗ i`.
* `Deformation.ComplexLift.idealAction_app_pureTensorClass`: the action of the ideal sends
  `m ⊗ i` to `ι(i) • m`.
* `Deformation.ComplexLift.idealPartIncl_app_pureTensorClass_unit`: the inclusion of the ideal
  part sends `η(m) ⊗ i` to `ι(i) • m`.

## Implementation notes

The proofs are chains of `Eq.trans` and `congrArg`, as in
`StacksFrontier/Deformation/ToposThickening/ExtensionUnitTensor.lean`, for the reason recorded
there: the goals mention two definitionally equal spellings of the underlying sheaf of rings, and
rewriting fails the motive check. The section formula for the cancellation of a base change is
`Stacks.Cohomology.MixedDerivedTensor.tensorBaseChangeLinearIso_hom_app_val_app_toSheafifyVal`,
whose adjunction unit is that of `Stacks.FlatChangeOfRings.extendScalarsAdjunction`; it agrees
with the unit of `Deformation.ComplexLift.extendRestrictAdjunction` definitionally.

## References

* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
* [Stacks Project, Tag 05V4](https://stacks.math.columbia.edu/tag/05V4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

open scoped TensorProduct

universe v' u u'

namespace Deformation.ComplexLift

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The class in the sheaf tensor product `A ⊗_O B` of the pure tensor `a ⊗ b` of two local
sections over `U`: the image of `a ⊗ₜ b` under the sheafification unit of the presheaf tensor
product. -/
abbrev pureTensorClass (O : Sheaf J CommRingCat.{u})
    (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (U : Cᵒᵖ)
    (a : A.val.obj U) (b : B.val.obj U) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O).obj A).obj B).val.obj U :=
  ((PresheafOfModules.sheafificationAdjunction.{u, v', u, u'} (R :=
          Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
      (PresheafOfModules.tensorObj A.val B.val)).app U (a ⊗ₜ[O.obj.obj U] b)

variable {O O₀ : Sheaf J CommRingCat.{u}}

/-- If `g ≫ h = 𝟙`, then `h` undoes `g` on every local section. -/
private theorem val_app_comp_eq_self {D : Type*} [Category D] {K : GrothendieckTopology D}
    {R : Sheaf K RingCat.{u}} {X Y : SheafOfModules.{u} R} {g : X ⟶ Y} {h : Y ⟶ X}
    (w : g ≫ h = 𝟙 X) (U : Dᵒᵖ) (x : X.val.obj U) :
    (h.val.app U) (g.val.app U x) = x :=
  congrArg (fun k => (k.val.app U) x) w

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The inverse symmetry of the tensor product on a pure tensor**: `b ⊗ a ↦ a ⊗ b`. It is the
section formula for the symmetry,
`Stacks.SheafOfModules.Tensor.sheafTensorBraiding_hom_app_sheafifyUnit_tmul`, read backwards. -/
theorem sheafTensorBraiding_inv_app_pureTensorClass
    (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (U : Cᵒᵖ)
    (a : A.val.obj U) (b : B.val.obj U) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensorBraiding.{u', v', u} O).app A).inv.app B).val.app
        U) (pureTensorClass O B A U b a) = pureTensorClass O A B U a b := by
  have h := Stacks.SheafOfModules.Tensor.sheafTensorBraiding_hom_app_sheafifyUnit_tmul O A B U a b
  refine Eq.trans (congrArg
    (fun y => ((((Stacks.SheafOfModules.Tensor.sheafTensorBraiding.{u', v', u} O).app A).inv.app
      B).val.app U) y) h.symm) ?_
  exact val_app_comp_eq_self
    (((Stacks.SheafOfModules.Tensor.sheafTensorBraiding.{u', v', u} O).app A).hom_inv_id_app B) U _

variable (f : O ⟶ O₀)

/-- **The projection formula on a pure tensor.** The isomorphism
`M ⊗_O I₀|_O ≅ ((O₀ ⊗_O M) ⊗_{O₀} I₀)|_O` of `Deformation.ComplexLift.idealTensorRightIso` sends
`m ⊗ i` to `η(m) ⊗ i`, `η` the unit of the extension/restriction-of-scalars adjunction along `f`.
Its three factors are crossed one at a time: the inverse symmetry gives `i ⊗ m`, the cancellation
of a base change gives `i ⊗ η(m)`, and the symmetry over `O₀` gives `η(m) ⊗ i`. -/
theorem idealTensorRightIso_hom_app_pureTensorClass
    (I₀ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (U : Cᵒᵖ)
    (m : M.val.obj U) (i : I₀.val.obj U) :
    (((idealTensorRightIso f I₀).hom.app M).val.app U)
        (pureTensorClass O M (restrictIdeal f I₀) U m i) =
      pureTensorClass O₀ ((extensionOfScalars f).obj M) I₀ U
        (((extendRestrictAdjunction f).unit.app M).val.app U m) i := by
  have h1 := sheafTensorBraiding_inv_app_pureTensorClass (restrictIdeal f I₀) M U i m
  have h2 :=
    Stacks.Cohomology.MixedDerivedTensor.tensorBaseChangeLinearIso_hom_app_val_app_toSheafifyVal
      f M I₀ U i m
  have h3 := Stacks.SheafOfModules.Tensor.sheafTensorBraiding_hom_app_sheafifyUnit_tmul O₀ I₀
    ((extensionOfScalars f).obj M) U i (((extendRestrictAdjunction f).unit.app M).val.app U m)
  refine Eq.trans (congrArg (fun y =>
      (((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).map
        (((Stacks.SheafOfModules.Tensor.sheafTensorBraiding.{u', v', u} O₀).app I₀).hom.app
          ((extensionOfScalars f).obj M))).val.app U)
      ((((Stacks.Cohomology.MixedDerivedTensor.tensorBaseChangeLinearIso f M).hom.app
        I₀).val.app U) y)) h1) ?_
  refine Eq.trans (congrArg (fun y =>
      (((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).map
        (((Stacks.SheafOfModules.Tensor.sheafTensorBraiding.{u', v', u} O₀).app I₀).hom.app
          ((extensionOfScalars f).obj M))).val.app U) y) h2) ?_
  exact h3

variable {f}

/-- **The action of the ideal on a pure tensor**: `m ⊗ i ↦ ι(i) • m`. Tensoring with `ι` sends
`m ⊗ i` to `m ⊗ ι(i)`, and the unit law sends that to `ι(i) • m`. -/
theorem idealAction_app_pureTensorClass
    {I₀ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)}
    (ι : restrictIdeal f I₀ ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (U : Cᵒᵖ)
    (m : M.val.obj U) (i : I₀.val.obj U) :
    (((idealAction ι).app M).val.app U) (pureTensorClass O M (restrictIdeal f I₀) U m i) =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj U from ι.val.app U i) • m := by
  have h1 := Stacks.SheafOfModules.FlatSquareZero.tensorLeft_map_tmul O M ι U m i
  have h2 := Stacks.SheafOfModules.tensorSheafUnitRightIso_hom_toSheafify_tmul O.obj
    (Stacks.SheafOfModules.structureRingIsSheaf O) M U m (ι.val.app U i)
  exact (congrArg (fun y => (((tensorRightUnitIso O).hom.app M).val.app U) y) h1).trans h2

/-- **The inclusion of the ideal part on a pure tensor**: `η(m) ⊗ i ↦ ι(i) • m`, `η` the unit of
the extension/restriction-of-scalars adjunction along `f`. The class of `η(m) ⊗ i` is the image of
`m ⊗ i` under the projection formula
(`Deformation.ComplexLift.idealTensorRightIso_hom_app_pureTensorClass`), so this is the action of
the ideal on `m ⊗ i` (`Deformation.ComplexLift.idealAction_app_pureTensorClass`). -/
theorem idealPartIncl_app_pureTensorClass_unit
    {I₀ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)}
    (ι : restrictIdeal f I₀ ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (U : Cᵒᵖ)
    (m : M.val.obj U) (i : I₀.val.obj U) :
    (((idealPartIncl f ι).app M).val.app U)
        (pureTensorClass O₀ ((extensionOfScalars f).obj M) I₀ U
          (((extendRestrictAdjunction f).unit.app M).val.app U m) i) =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj U from ι.val.app U i) • m := by
  refine Eq.trans (congrArg (fun y => (((idealPartIncl f ι).app M).val.app U) y)
    (idealTensorRightIso_hom_app_pureTensorClass f I₀ M U m i).symm) ?_
  refine Eq.trans (congrArg (fun y => (((idealAction ι).app M).val.app U) y)
    (val_app_comp_eq_self ((idealTensorRightIso f I₀).hom_inv_id_app M) U
      (pureTensorClass O M (restrictIdeal f I₀) U m i))) ?_
  exact idealAction_app_pureTensorClass ι M U m i

end Deformation.ComplexLift

end
