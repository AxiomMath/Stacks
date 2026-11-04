module

public import StacksFrontier.AlgebraicGeometry.AlgebraImageSurjective.Algebra

/-!
# The presheaf and sheaf spellings of surjectivity of a morphism of algebra sheaves agree

The statement of [Stacks, Tag 086N] -- which is what [Stacks, Tag 0817] part (2) defers to, twice --
asks for the transition maps of its approximating system to be *surjective*, and spells that at
the level of **presheaves**:

```
def IsSurjective {X : Scheme} {A B : AlgebraSheaf X} (f : A ⟶ B) : Prop :=
  Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) f.right.hom
```

while every statement about algebra sheaves in this repository -- notably
`Stacks.AlgebraicGeometry.FiniteTypeSubalgebras.ImageIsLocallySurjective` and
`Stacks.AlgebraImageSurjective.isLocallySurjective_factorThruImage_algebraSheaf` -- spells it at
the level of **sheaves**, as `Sheaf.IsLocallySurjective f.right`.

The two levels agree definitionally.
`CategoryTheory.Sheaf.IsLocallySurjective` is an `abbrev` -- not a structure, not a definition
with its own constant -- for exactly the presheaf predicate applied to the underlying morphism of
presheaves (`Mathlib/CategoryTheory/Sites/LocallySurjective.lean`, where
`CategoryTheory.Sheaf.isLocallySurjective_sheafToPresheaf_map_iff` is itself proved `by rfl`).  So
the two spellings are the same proposition, and the identification is `Iff.rfl`.  Any
theorem proved at either level is therefore already a theorem at the other.

## Main results

* `Stacks.AlgebraSurjectiveSpelling.isLocallySurjective_right_iff`: the two spellings agree, by
  `Iff.rfl`.
* `Stacks.AlgebraSurjectiveSpelling.presheaf_isLocallySurjective_factorThruImage_right`: the
  statement that the corestriction of a morphism of algebra sheaves to its image is
  locally surjective, restated verbatim at the presheaf spelling of Tag 086N.  This shows the
  identification in use.

## Implementation notes

The topology is written `TopologicalSpace.Opens.grothendieckTopology X` with the scheme coerced
to its carrier, which is the site of `TopCat.Sheaf`, so no transport between sites occurs either.

## References

* [The Stacks Project, Tag 086N](https://stacks.math.columbia.edu/tag/086N)
* [The Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry Stacks.RelativeSpec

universe u

namespace Stacks.AlgebraSurjectiveSpelling

variable {X : Scheme.{u}} {A B : AlgebraSheaf X}

/-- **The presheaf-level surjectivity of Tag 086N of a morphism of algebra sheaves is this
repository's sheaf-level surjectivity.**  `CategoryTheory.Sheaf.IsLocallySurjective` abbreviates
the presheaf predicate at the underlying morphism of presheaves, so the two are one
proposition. -/
theorem isLocallySurjective_right_iff (f : A ⟶ B) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) f.right.hom ↔
      Sheaf.IsLocallySurjective f.right :=
  Iff.rfl

/-- **The corestriction of a morphism of algebra sheaves to its image is locally surjective, at
the presheaf spelling of Tag 086N.**  The content is
`Stacks.AlgebraImageSurjective.isLocallySurjective_factorThruImage_algebraSheaf`; only the
spelling differs, and `isLocallySurjective_right_iff` says it does not. -/
theorem presheaf_isLocallySurjective_factorThruImage_right (φ : A ⟶ B) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) (factorThruImage φ).right.hom :=
  (isLocallySurjective_right_iff _).mpr
    (Stacks.AlgebraImageSurjective.isLocallySurjective_factorThruImage_algebraSheaf φ)

end Stacks.AlgebraSurjectiveSpelling

end
