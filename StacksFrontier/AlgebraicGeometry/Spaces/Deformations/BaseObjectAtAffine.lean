module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistence

/-!
# The affine bases `Spec Aₙ` of the infinitesimal base changes are affine

The objects `AlgebraicGeometry.Space.baseObjectAt F B hS hSn n` of the big fppf category over the
inverse-limit base `Spec A` have underlying scheme `Spec Aₙ`. Since `baseObjectAt` is a
definition, instance search does not see through it; this file records the affineness as an
instance, which the derived sections `RΓ(Spec Aₙ, -)` of
`AlgebraicGeometry.Space.representedAffineDerivedSections` ask for.

## References

* [Stacks Project, Tag 0DIK](https://stacks.math.columbia.edu/tag/0DIK)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace AlgebraicGeometry.Space

variable (F : ℕᵒᵖ ⥤ CommRingCat.{u}) (B : BigFppfSite.{u})
    (hS : B.Contains (limitBase F)) (hSn : ∀ n : ℕ, B.Contains (baseAt F n))

/-- The underlying scheme of the affine base at level `n` is `Spec Aₙ`, an affine scheme. -/
instance isAffine_toScheme_baseObjectAt (n : ℕ) :
    IsAffine ((BigFppfOver.toScheme B (limitBase F) hS).obj (baseObjectAt F B hS hSn n)) :=
  inferInstanceAs (IsAffine (baseAt F n))

end AlgebraicGeometry.Space

end
