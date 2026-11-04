module

/-
Copyright (c) 2026 the Stacks in Lean authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.Morphism

/-!
# The structure map of a localization morphism is invertible

For a ringed site `X` and an object `U`, the structure map of the localization morphism of
Stacks 04IX is the identification of the inverse image of `O_X` with its restriction to the
slice site over `U`, composed with a map that is the identity. It is therefore an isomorphism.

The fact is recorded here at two spellings, because the two are not interchangeable for instance
search: typeclass resolution runs at reducible transparency, and the structure projection
`(X.localizationMorphism U).fSharpInverseImage` does not reduce to `X.overInverseImageFsharp U`
there, even though the two are definitionally equal at default transparency.

## Main results

* `AlgebraicGeometry.RingedSite.isIso_overInverseImageFsharp`: the identification itself.
* `AlgebraicGeometry.RingedSite.isIso_fSharpInverseImage_localizationMorphism`: the same fact at
  the projection out of `localizationMorphism`, which is the form the chain of Stacks 03EL
  requires as a side condition.

## References

* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, max u v w}) (U : X.C)

/-- **The structure map of the localization of Stacks 04IX is invertible.** It is the
identification `π⁻¹O_X ≅ O_X|_U` of `overInverseImageRingIso` followed by a map that is the
identity, so `overInverseImageFsharp_eq` identifies it with that isomorphism's forward map. -/
public instance isIso_overInverseImageFsharp :
    IsIso (X.overInverseImageFsharp U) := by
  rw [overInverseImageFsharp_eq]
  infer_instance

/-- **The structure map of the localization morphism of ringed topoi is invertible**, at the
spelling the chain of Stacks 03EL asks for: the projection out of `localizationMorphism`.

Stated separately from `isIso_overInverseImageFsharp` on purpose. The projection is the field
`X.overInverseImageFsharp U` by definition, but instance search unfolds only at reducible
transparency and so does not see through it; the previous instance therefore does not fire at
this type. -/
public instance isIso_fSharpInverseImage_localizationMorphism :
    IsIso (X.localizationMorphism U).fSharpInverseImage :=
  X.isIso_overInverseImageFsharp U

end AlgebraicGeometry.RingedSite

end
