module

public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.Relocalization
import StacksCore.Tactic.StacksAttribute

/-!
# The relocalization triangle of a ringed site, in the two-field presentation

Let `(C, O)` be a ringed site and `f : V ⟶ U` a morphism of `C`. Restriction along
`Over.map f` is a morphism of ringed topoi `(Sh(C/V), O|_V) ⟶ (Sh(C/U), O|_U)`, the
*relocalization* of Stacks 04IY, and composing it with the localization at `U` gives the
localization at `V` up to the canonical comparison of the two direct images.

Stacks 04IY is proved in
`StacksFrontier/CategoryTheory/Sites/RingedLocalization/Relocalization.lean`. All that is added
here is the inverse-image form of the structure map of the relocalization read on the
*two-field* morphism of ringed topoi of Stacks 01D3 part (2) — the presentation in which the
triangle is stated, because composition of morphisms of ringed topoi exists only for that
structure — where the already-proved
`AlgebraicGeometry.RingedSite.relocalizationMorphism_fSharpInverseImage` states it for the
four-field `Stacks.Sheaves.RingedToposModules.RingedToposHom` and at the `RingCat` level.

## Main results

* `AlgebraicGeometry.RingedSite.relocalizationRingedToposHom_fSharpInverseImage`: the structure
  map of the relocalization, in inverse-image form and at the level of sheaves of commutative
  rings, is the comparison of the inverse image of `O|_U` with its restriction along
  `Over.map f`, followed by the change-of-slice identification of that restriction with `O|_V`.

## Implementation notes

The inverse-image form is not a field of `AlgebraicGeometry.RingedToposHom`: it is
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage`, the image of the stored direct-image
form under the inverse of the hom-set bijection of
`Stacks.Sheaves.ToposPushforward.commRingImageAdjunction`. The structure map of
`relocalizationRingedToposHom` is by construction the image of
`AlgebraicGeometry.RingedSite.overMapInverseImageCommRingIso` under that same bijection, so the
proof is `Equiv.symm_apply_apply` once the two sides are spelled at the adjunction the
definition uses — which is what the `change` does; `rw` cannot reach it, the two spellings being
defeq only at default transparency.

## References

* [Stacks Project, Tag 04IY](https://stacks.math.columbia.edu/tag/04IY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u v w

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, max u v w}) {U V : X.C} (f : V ⟶ U)

/-- **Stacks 04IY.** The structure map of the relocalization along `f : V ⟶ U`, in
inverse-image form and on sheaves of commutative rings, is the canonical comparison of the
inverse image of `O|_U` with its restriction along `Over.map f`, followed by the change-of-slice
identification of that restriction with `O|_V`. -/
@[stacks 04IY "structure map of localization at V/U"]
theorem relocalizationRingedToposHom_fSharpInverseImage :
    (X.relocalizationRingedToposHom f).fSharpInverseImage =
      (restrictionCommRingIso (X.J.over V) (X.J.over U) (Over.map f) (X.O.over U)).hom ≫
        (X.O.pushforwardOverMapIso f).hom := by
  change ((commRingImageAdjunction (X.overMapMorphismOfTopoi f)).homEquiv _ _).symm
      ((commRingImageAdjunction (X.overMapMorphismOfTopoi f)).homEquiv _ _
        (X.overMapInverseImageCommRingIso f).hom) = _
  rw [Equiv.symm_apply_apply]
  rfl

end AlgebraicGeometry.RingedSite

/-! ## The rest of the covering set of Stacks 04IY

The remaining claims of Stacks 04IY are already proved in
`StacksFrontier/CategoryTheory/Sites/RingedLocalization/Relocalization.lean` and in Mathlib; they
are recorded against the tag here rather than restated. -/

add_to_stacks 04IY "relocalization morphism"
  AlgebraicGeometry.RingedSite.relocalizationRingedToposHom

add_to_stacks 04IY "identification with localization at V/U"
  AlgebraicGeometry.RingedSite.overMap_inverseImage_iteratedSlice

add_to_stacks 04IY "structure sheaf under iterated slice"
  AlgebraicGeometry.RingedSite.iteratedSlice_structureSheaf

add_to_stacks 04IY "commutative triangle"
  AlgebraicGeometry.RingedSite.localizationMorphism_comp_relocalizationMorphism

add_to_stacks 04IY "iterated-slice site equivalence"
  CategoryTheory.instIsContinuousOverLeftIteratedSliceForwardOver

end
