module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPreservesColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UliftTensorSheaf

/-!
# Comparison of objectwise presheaf tensor products

This computational comparison is used by the affine tensor-section formula. Tensor colimit
preservation is supplied directly by the canonical functor in `TensorPreservesColimits`;
no fixed-factor tensor functor or colimit-transport wrapper is introduced here.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u v w z z₁

namespace Stacks.SheafOfModules.TensorRaised

variable {C : Type u} [Category.{v} C]

/-- The two objectwise tensor products of presheaves of modules in the tree agree. -/
noncomputable def presheafTensorCompare {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    (F : PresheafOfModules.{z} (AlgebraicGeometry.SheafOfModules.ringPresheaf O))
    (G : PresheafOfModules.{z₁} (AlgebraicGeometry.SheafOfModules.ringPresheaf O)) :
    AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorObj F G ≅
      PresheafOfModules.tensorObj F G :=
  PresheafOfModules.isoMk (fun _ ↦ Iso.refl _)
    (by intro X Y f; exact ModuleCat.tensor_ext fun x y ↦ rfl)

end Stacks.SheafOfModules.TensorRaised
