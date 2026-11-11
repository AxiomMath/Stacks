module

public import StacksCore.CategoryTheory.Abelian.Images
import StacksCore.Tactic.StacksAttribute

/-!
# The factorisation through the coimage and the image

Let `f : X ⟶ Y` be a morphism in a preadditive category such that the kernel, cokernel, image
and coimage of `f` exist. Then `f` factors uniquely as `X ⟶ Coim(f) ⟶ Im(f) ⟶ Y`: there is
exactly one `φ : Coim(f) ⟶ Im(f)` with `coimage.π f ≫ φ ≫ image.ι f = f`, namely the canonical
comparison `Abelian.coimageImageComparison f`.

## Main results

* `CategoryTheory.Abelian.existsUnique_coimage_π_comp_comp_image_ι`: Stacks 0107.
-/

@[expose] public section

namespace CategoryTheory.Abelian

open Limits

/-- **Stacks 0107.** A morphism `f : X ⟶ Y` of a preadditive category whose kernel, cokernel,
image and coimage exist factors uniquely as `X ⟶ Coim(f) ⟶ Im(f) ⟶ Y`: there is a unique
`φ : Coim(f) ⟶ Im(f)` with `coimage.π f ≫ φ ≫ image.ι f = f`. -/
@[stacks 0107 "existence and uniqueness of the middle map `Coim(f) ⟶ Im(f)`, which is \
`coimageImageComparison f`"]
theorem existsUnique_coimage_π_comp_comp_image_ι {C : Type*} [Category* C] [Preadditive C]
    {X Y : C} (f : X ⟶ Y) [HasKernel f] [HasCokernel f] [HasKernel (cokernel.π f)]
    [HasCokernel (kernel.ι f)] :
    ∃! φ : Abelian.coimage f ⟶ Abelian.image f, coimage.π f ≫ φ ≫ Abelian.image.ι f = f :=
  ⟨coimageImageComparison f, coimage_image_factorisation f,
    fun φ hφ => unique_factorThru f φ hφ⟩

end CategoryTheory.Abelian
