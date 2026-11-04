module

public import StacksFrontier.CategoryTheory.Abelian.GrothendieckGroup
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# The classes of an image and a kernel in `K₀`

For an exact sequence `X₁ → X₂ → X₃` in an abelian category `𝒜`, the image of the first map and
the kernel of the second have the same class in the Grothendieck group `K₀(𝒜)`.

## Main results

* `KZero.mk_image_eq_mk_kernel`.
-/

@[expose] public section

open CategoryTheory Limits

variable (𝒜 : Type*) [Category 𝒜] [Abelian 𝒜]

namespace KZero

variable {𝒜}

/-- For an exact sequence `X₁ → X₂ → X₃`, the image of the first map and the kernel of the second
have the same class in `K₀(𝒜)`. -/
theorem mk_image_eq_mk_kernel (S : ShortComplex 𝒜) (hS : S.Exact) :
    mk 𝒜 (Abelian.image S.f) = mk 𝒜 (kernel S.g) := by
  have := hS.isIso_imageToKernel'
  exact mk_eq_of_iso (Abelian.imageIsoImage S.f ≪≫ asIso (imageToKernel' S.f S.g S.zero))

end KZero
