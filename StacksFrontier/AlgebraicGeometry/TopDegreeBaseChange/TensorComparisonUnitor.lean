module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerConstraints
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparison

/-!
# The right unitor `F ⊗_{𝒪_X} 𝒪_X ≅ F`, at the spelling of the tensor comparison

The invertibility half of conclusion (b) of [Stacks, Tag 0EX3] is run, following the source,
against the value of the canonical map at the structure sheaf on the base.  Reading that value
requires the right unitor of the tensor product of [Stacks, Tag 01CB] *on elements*: the
identification `F ⊗_{𝒪_X} 𝒪_X ≅ F` has to be known to send the local pure tensor `a ⊗ t` to
`t • a`, and its inverse to send `a` to `a ⊗ 1`.

`Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso` is the right unitor and
`Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso_hom_app` is its rule on the image of a pure
tensor under the sheafification unit; both are stated at the object
`((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, _⟩).obj F).obj (SheafOfModules.unit _)`. This
file states them for the tensor comparison and adds the rule for the inverse, which follows by
cancellation.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.unitorSection`: the value on sections `t • a`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.tensorUnitIso`: **the right unitor
  `F ⊗_{𝒪_X} 𝒪_X ≅ F`** at the spelling of this directory, with its two element rules.

## Main results

All of the following live in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `tensorUnitHom_toTensorSheafSection`: **the unitor on a local pure tensor is `a ⊗ t ↦ t • a`.**
* `tensorUnitInv_app_apply`: **the inverse unitor on a section is `a ↦ a ⊗ 1`.**
* `isIso_tensorUnitHom` and `isIso_tensorUnitInv`: both directions are invertible, as instances.

## Implementation notes

*A second right unitor exists and has no element rule.*
`Stacks.SheafOfModules.Invertible.tensorLeftFunctorObjUnitIso`, built in
`EilenbergWattsUnitor.lean` out of the symmetry and the left unitor, is a different term for the
same isomorphism, and nothing computes it on sections.  The one used here is the one that does.

*Why the section of `𝒪_X` is retyped.* The carrier of the module `𝒪_X` over an open *is* the
section ring, but the `RingCat` spelling the module system is indexed by and the `CommRingCat`
spelling that knows the multiplication is commutative are crossed by no instance, so
`unitRingSection` does the retyping once, on a bare variable, as `modSheaf` does in
`StacksFrontier/AlgebraicGeometry/Scheme/QuasiCoherent/TildeTensorSections.lean`.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

noncomputable section

attribute [local instance] moduleOfPresheafRing

variable {X : Scheme.{u}} (A : X.Modules)

/-! ### The value on sections -/

/-- **A section of the structure sheaf, read as an element of the commutative section ring
`Γ(X, W)`.** -/
def unitRingSection (W : (Opens X.carrier)ᵒᵖ) (t : (Scheme.unitModule X).val.obj W) :
    ↑(X.presheaf.obj W) := t

/-- **The value on sections of the right unitor**, `(a, t) ↦ t • a`. -/
def unitorSection (W : (Opens X.carrier)ᵒᵖ) (a : A.val.obj W)
    (t : (Scheme.unitModule X).val.obj W) : A.val.obj W :=
  unitRingSection W t • a

/-- The unit section is the unit of the section ring. -/
theorem unitRingSection_one (W : (Opens X.carrier)ᵒᵖ) :
    unitRingSection W (1 : ↑(X.presheaf.obj W)) = 1 := rfl

/-- The value of the right unitor on a pure tensor with the unit section is the section
itself. -/
theorem unitorSection_one (W : (Opens X.carrier)ᵒᵖ) (a : A.val.obj W) :
    unitorSection A W a (1 : ↑(X.presheaf.obj W)) = a := by
  change unitRingSection W (1 : ↑(X.presheaf.obj W)) • a = a
  rw [unitRingSection_one, one_smul]

/-! ### The unitor -/

/-- **The right unitor of the tensor product of [Stacks, Tag 01CB]**, `F ⊗_{𝒪_X} 𝒪_X ≅ F`, for
the tensor product `Stacks.SheafOfModules.Tensor.sheafTensor`; it is
`Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso`. -/
def tensorUnitIso :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj A).obj
      (Scheme.unitModule X) ≅ A :=
  Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso X.presheaf
    (AlgebraicGeometry.ringSheafCond X) A

/-- The right unitor `F ⊗_{𝒪_X} 𝒪_X ⟶ F`, `a ⊗ t ↦ t • a`. -/
def tensorUnitHom :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj A).obj
      (Scheme.unitModule X) ⟶ A :=
  (tensorUnitIso A).hom

/-- The inverse right unitor `F ⟶ F ⊗_{𝒪_X} 𝒪_X`, `a ↦ a ⊗ 1`. -/
def tensorUnitInv :
    A ⟶ ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj A).obj (Scheme.unitModule X) :=
  (tensorUnitIso A).inv

/-- **The unitor on a local pure tensor is `a ⊗ t ↦ t • a`.** -/
theorem tensorUnitHom_toTensorSheafSection (W : (Opens X.carrier)ᵒᵖ)
    (a : A.val.obj W) (t : (Scheme.unitModule X).val.obj W) :
    ((tensorUnitHom A).val.app W).hom
        (toTensorSheafSection X.toRingedSpace A (Scheme.unitModule X) W
          (a ⊗ₜ[X.presheaf.obj W] t)) = unitorSection A W a t :=
  Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso_hom_app X.presheaf
    (AlgebraicGeometry.ringSheafCond X) A W a t

/-- The unitor and its inverse cancel on sections. -/
theorem tensorUnitInv_tensorUnitHom_apply (W : (Opens X.carrier)ᵒᵖ)
    (z : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj A).obj
        (Scheme.unitModule X)).val.obj W) :
    ((tensorUnitInv A).val.app W).hom (((tensorUnitHom A).val.app W).hom z) = z :=
  congrArg (fun k : ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj A).obj (Scheme.unitModule X) ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj A).obj (Scheme.unitModule X) =>
    (k.val.app W).hom z)
    (tensorUnitIso A).hom_inv_id

/-- **The inverse unitor on a section is `a ↦ a ⊗ 1`.** -/
theorem tensorUnitInv_app_apply (W : (Opens X.carrier)ᵒᵖ) (a : A.val.obj W) :
    ((tensorUnitInv A).val.app W).hom a =
      toTensorSheafSection X.toRingedSpace A (Scheme.unitModule X) W
        (a ⊗ₜ[X.presheaf.obj W] (1 : ↑(X.presheaf.obj W))) := by
  refine Eq.trans ?_ (tensorUnitInv_tensorUnitHom_apply A W
    (toTensorSheafSection X.toRingedSpace A (Scheme.unitModule X) W
      (a ⊗ₜ[X.presheaf.obj W] (1 : ↑(X.presheaf.obj W)))))
  rw [tensorUnitHom_toTensorSheafSection A W a (1 : ↑(X.presheaf.obj W)),
    unitorSection_one A W a]

/-- `a ↦ a ⊗ 1 ↦ 1 • a = a`. -/
theorem tensorUnitInv_tensorUnitHom : tensorUnitInv A ≫ tensorUnitHom A = 𝟙 A :=
  (tensorUnitIso A).inv_hom_id

/-- `a ⊗ t ↦ t • a ↦ (t • a) ⊗ 1 = a ⊗ t`. -/
theorem tensorUnitHom_tensorUnitInv :
    tensorUnitHom A ≫ tensorUnitInv A =
      𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj A).obj (Scheme.unitModule X)) :=
  (tensorUnitIso A).hom_inv_id

/-- The right unitor `tensorUnitHom A` is an isomorphism. -/
instance isIso_tensorUnitHom : IsIso (tensorUnitHom A) :=
  (tensorUnitIso A).isIso_hom

/-- The inverse right unitor `tensorUnitInv A` is an isomorphism. -/
instance isIso_tensorUnitInv : IsIso (tensorUnitInv A) :=
  (tensorUnitIso A).isIso_inv

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
