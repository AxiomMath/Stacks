module

public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.Relocalization
import StacksCore.Tactic.StacksAttribute

/-!
# The structure map of a localization morphism of ringed topoi is invertible

Let `(C, O)` be a ringed site and `T` an object of `C`. The localization morphism of ringed topoi
`π : (Sh(C/T), O|_T) ⟶ (Sh(C), O)` of Stacks 04IX carries the direct-image form
`π♯ : O ⟶ π_*O|_T` of its structure map; its inverse-image form `π⁻¹O ⟶ O|_T` is the adjunct of
it, `AlgebraicGeometry.RingedToposHom.fSharpInverseImage`. This file shows that this inverse-image
form is the identification `π⁻¹O ≅ O|_T` of the inverse image of the structure sheaf with its
restriction, `AlgebraicGeometry.RingedSite.overInverseImageCommRingIso`, and hence an
isomorphism.

## Main results

* `AlgebraicGeometry.RingedSite.localizationRingedToposHom_fSharpInverseImage`: the
  inverse-image form of the structure map of the localization morphism is the identification
  `π⁻¹O ≅ O|_T`.
* `AlgebraicGeometry.RingedSite.isIso_localizationRingedToposHom_fSharpInverseImage`: the
  inverse-image form of the structure map of the localization morphism is an isomorphism.

## References

* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.RingedSite

universe u v w

variable (X : RingedSite.{u, v, max u v w}) (T : X.C)

/-- The inverse-image form of the structure map of the localization morphism of ringed topoi
`π : (Sh(C/T), O|_T) ⟶ (Sh(C), O)` is the identification `π⁻¹O ≅ O|_T`. -/
theorem localizationRingedToposHom_fSharpInverseImage :
    (X.localizationRingedToposHom T).fSharpInverseImage =
      (X.overInverseImageCommRingIso T).hom :=
  (X.overCommRingFsharpAdjoint_inverseImage T).trans (X.overInverseImageCommRingFsharp_eq T)

/-- The inverse-image form of the structure map of a localization morphism of ringed topoi is an
isomorphism. -/
instance isIso_localizationRingedToposHom_fSharpInverseImage :
    IsIso (X.localizationRingedToposHom T).fSharpInverseImage := by
  rw [localizationRingedToposHom_fSharpInverseImage]
  exact (X.overInverseImageCommRingIso T).isIso_hom

end AlgebraicGeometry.RingedSite

end
