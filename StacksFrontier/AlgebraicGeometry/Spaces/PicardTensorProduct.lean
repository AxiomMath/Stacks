module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctor

/-!
# Tensor products of invertible modules on an algebraic space

Addition in the Picard group `Pic(X)` of an algebraic space `X` (Stacks 01CX) is the tensor
product of invertible `𝒪_X`-modules. This file records the tensor product of two `𝒪_X`-modules
on the small étale site of `X` under the name `AlgebraicGeometry.Space.picardTensorModule`, that it
preserves invertibility, and that the class of a tensor product of invertible modules is the sum of
their classes.

## Main definitions

* `AlgebraicGeometry.Space.picardTensorModule` is `ℒ ⊗_{𝒪_X} 𝒩`.

## Main results

* `AlgebraicGeometry.Space.isInvertibleModule_picardTensorModule`: a tensor product of invertible
  `𝒪_X`-modules is invertible.
* `AlgebraicGeometry.Space.picardClass_add`: the sum in `Pic(X)` of the classes of two
  invertible `𝒪_X`-modules is the class of their tensor product.

## Implementation notes

The tensor product is the one of `AlgebraicGeometry.Space.modulesMonoidalCategory`, taken in
the spelling `Stacks.SheafOfModules.TensorSheafification.tensorSheaf` in which
`Stacks.SheafOfModules.picardClass_tensorSheaf` states that addition of Picard classes is
tensor product; the two agree up to the isomorphism
`AlgebraicGeometry.Space.modulesTensorObjIso`.

These three statements are separated from their consumers because the sheafification instances
they need are at the universe of the schemes, which the sheafification instances of the sheaf
of meromorphic sections (`AlgebraicGeometry.Space.moduleHasWeakSheafify`) are not: with those
in scope instance search for the ones used here does not terminate on a universe constraint.
Everything below is therefore stated once, here, where the meromorphic sheafification
instances are not imported.

## References

* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-- The tensor product `ℒ ⊗_{𝒪_X} 𝒩` of two `𝒪_X`-modules on the small étale site of `X`, in
the spelling in which addition of Picard classes is tensor product. -/
def picardTensorModule (L N : Modules.{u, u} B S hS X hX) : Modules.{u, u} B S hS X hX :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ⟨(structureSheaf B S hS X hX).obj,
        Presheaf.isSheaf_of_isSheaf_comp _ ((structureSheaf B S hS X hX).obj)
          (forget₂ CommRingCat RingCat) ((structureRingPresheaf_isSheaf B S hS X hX))⟩).obj
      (L)).obj (N))

/-- **Stacks 01CT.** The tensor product of two invertible `𝒪_X`-modules is invertible. -/
theorem isInvertibleModule_picardTensorModule (L N : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (hN : IsInvertibleModule (B := B) ⟨X, hX⟩ N) :
    IsInvertibleModule (B := B) ⟨X, hX⟩ (picardTensorModule B S hS hX L N) :=
  have := hL
  have := hN
  Stacks.SheafOfModules.isInvertible_tensorSheaf (structureSheaf B S hS X hX).obj
    (structureRingPresheaf_isSheaf B S hS X hX) L N

/-- **Stacks 01CX.** The sum in `Pic(X)` of the classes of two invertible `𝒪_X`-modules is the
class of their tensor product. -/
theorem picardClass_add (L N : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (hN : IsInvertibleModule (B := B) ⟨X, hX⟩ N) :
    picardClass (B := B) ⟨X, hX⟩ L hL + picardClass (B := B) ⟨X, hX⟩ N hN =
      picardClass (B := B) ⟨X, hX⟩ (picardTensorModule B S hS hX L N)
        (isInvertibleModule_picardTensorModule B S hS hX L N hL hN) :=
  Stacks.SheafOfModules.picardClass_tensorSheaf (structureSheaf B S hS X hX).obj
    (structureRingPresheaf_isSheaf B S hS X hX) L N hL hN
    (isInvertibleModule_picardTensorModule B S hS hX L N hL hN)

end AlgebraicGeometry.Space

end
