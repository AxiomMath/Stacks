module

public import StacksFrontier.AlgebraicGeometry.Groupoids.More.GroupoidSituation
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.PointwiseMaximalLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.PointwiseOpenLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PointwiseBaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# The flat locus in a groupoid slice

In the flat, locally finitely presented groupoid situation the largest open of
`U' ×_{g, U, t} R` on which the induced map `h` to `U` is flat is pulled back from an open of
`U'`.  For a morphism locally of finite presentation the pointwise flat locus is open and is the
largest flat open, and flatness at a point is preserved by arbitrary base change and descends
along a flat one, so `AlgebraicGeometry.exists_open_with_preimage_maximal_locus` applies.

## Main definitions

This file introduces no definitions.

## Main results

* `AlgebraicGeometry.exists_open_with_preimage_maximal_flatLocus` identifies the largest flat
  open with the inverse image of an open of `U'`.

## Implementation notes

The pointwise condition fed to
`AlgebraicGeometry.exists_open_with_preimage_maximal_locus_of_pointwise` is
`AlgebraicGeometry.IsFlatAt`, flatness of the stalk map.  Local finite presentation enters only
through openness of its locus, which is Tag 0399 for the structure sheaf; without it the
pointwise locus can fail to be open, by
`AlgebraicGeometry.exists_flat_locus_not_open`.

Both halves of the base-change hypothesis — preservation of flatness at a point under an
arbitrary base change, and descent along a flat one — are
`AlgebraicGeometry.isFlatAt_iff_of_isPullback`.

## References

* [Stacks Project, Tag 047W](https://stacks.math.columbia.edu/tag/047W)
* [Stacks Project, Tag 0399](https://stacks.math.columbia.edu/tag/0399)
* [Stacks Project, Tag 047C](https://stacks.math.columbia.edu/tag/047C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 047W, case (4).**  In the flat, locally finitely presented groupoid
situation the largest open of `U' ×_{g, U, t} R` on which `h` is flat is the inverse image along
the projection of an open of `U'`. -/
@[stacks 047W "flat"]
public theorem exists_open_with_preimage_maximal_flatLocus
    (D : FlatLocallyFinitelyPresentedGroupoidSituation.{u}) :
    ∃ W : D.U'.Opens,
      IsGreatest {V : D.fiberProduct.Opens | Flat (V.ι ≫ D.h)}
        ((pullback.fst D.g D.groupoid.target.left) ⁻¹ᵁ W) := by
  have : IsZariskiLocalAtSource (@Flat.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Flat)
  let R : MorphismProperty Scheme.{u} := fun _ _ f => Flat f ∧ LocallyOfFinitePresentation f
  exact exists_open_with_preimage_maximal_locus_of_pointwise
    (@Flat.{u}) (@LocallyOfFinitePresentation.{u}) R (fun _ _ _ hf => hf.2)
    (fun _ _ f x => IsFlatAt f.toLRSHom.toShHom x)
    (fun _ _ f (_ : LocallyOfFinitePresentation f) => isOpen_setOf_isFlatAt f)
    (fun _ _ f (_ : LocallyOfFinitePresentation f) x =>
      ⟨fun ⟨U, hxU, hU⟩ => isFlatAt_of_flat_comp_ι f hU hxU, fun hx =>
        ⟨⟨{z | IsFlatAt f.toLRSHom.toShHom z}, isOpen_setOf_isFlatAt f⟩, hx,
          flat_of_subset_setOf_isFlatAt f _ fun _ hz => hz⟩⟩)
    (fun {_ _ _ _ _ _ _ q} _ ⟨(_ : Flat q), _⟩ hp x' => isFlatAt_iff_of_isPullback hp x')
    D.groupoid D.g
    (show R D.groupoid.source.left from ⟨inferInstance, inferInstance⟩)
    (show R D.groupoid.target.left from ⟨inferInstance, inferInstance⟩) inferInstance

end AlgebraicGeometry
