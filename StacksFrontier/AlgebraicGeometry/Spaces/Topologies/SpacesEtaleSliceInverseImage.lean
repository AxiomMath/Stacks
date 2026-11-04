module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleInverseImageUnitors
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSliceSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleStructureSheaf

/-!
# The slice pullback is the spaces-étale inverse image

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let
`φ : V ⟶ U` be a morphism of its spaces-étale site. Sheaves of sets on the slice of that site
at `U` are sheaves on the spaces-étale site of the algebraic space `U` underlying `U`, by
`AlgebraicGeometry.Space.SpacesEtale.sheafOverEquivSmall`, and there are two ways of moving
them from `U` to `V`: the slice pullback
`CategoryTheory.GrothendieckTopology.overMapPullback` along `φ`, and the inverse image of
Stacks 03G2, part (3), along the morphism of algebraic spaces underlying `φ`. This file
identifies them.

## Main definitions

* `AlgebraicGeometry.Space.SpacesEtale.slicePostcomp`: the functor of sites underlying both
  comparisons, namely the slice at `V` read as the spaces-étale site of `V` and then
  postcomposed into the spaces-étale site of `U`.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.overMapPullback_spacesEtaleInverseImageIso`: the slice
  pullback along `φ` and the spaces-étale inverse image along the underlying morphism agree
  through the comparison equivalences at `U` and at `V`.
* `AlgebraicGeometry.Space.SpacesEtale.sheafOverEquivSmall_overMapPullback_iso`: the same
  comparison in the form of an isomorphism onto the inverse image itself, the two comparison
  equivalences being inserted on either side of the slice pullback.

## Implementation notes

Both sides are restriction along a functor of sites: on one side because the comparison
equivalence of `AlgebraicGeometry.Space.SpacesEtale.sheafOverEquivSmall` has restriction along
`AlgebraicGeometry.Space.SpacesEtale.sliceToSmall` for its inverse, and on the other because
Stacks 03LQ —
`AlgebraicGeometry.Space.spacesToposMorphism_inverseImageIso` — rewrites the inverse image of
an étale morphism as restriction along postcomposition. The two functors of sites so obtained
are equal on the nose, because passing from the slice to the spaces-étale site of the slicing
object moves the structure morphism between two slots and changes neither the underlying
algebraic space nor the underlying morphism; so both comparisons are instances of
`CategoryTheory.Functor.sheafPushforwardContinuousComp'` with the identity isomorphism.

The continuity instance for postcomposition is restated here at the morphism
`AlgebraicGeometry.Space.SpacesEtale.toSpaces.map φ` with its own étaleness witness: instance
search cannot supply the witness, which is an explicit non-class argument of
`AlgebraicGeometry.Space.isContinuous_spacesEtalePostcomp`, so a statement about
postcomposition along that particular morphism matches no instance without it.

## References

* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS}

/-- Postcomposition along the morphism of algebraic spaces underlying a morphism of the
spaces-étale site of `X` is continuous for the spaces-étale topologies. -/
instance isContinuous_spacesEtalePostcomp_toSpaces_map {V U : SpacesEtale B S hS X}
    (φ : V ⟶ U) :
    (spacesEtalePostcomp B S hS ((toSpaces B S hS X).map φ)
        (isEtale_toSpaces_map B S hS X φ)).IsContinuous
      (topology B S hS V.obj.left) (topology B S hS U.obj.left) :=
  isContinuous_spacesEtalePostcomp B S hS _ _

/-- The slice of the spaces-étale site of `X` at `V`, read as the spaces-étale site of the
algebraic space `V` and then postcomposed into the spaces-étale site of the algebraic space
`U` along a morphism `φ : V ⟶ U`. Reading the slice at `V` as a slice at `U` along `φ` and
then passing to the spaces-étale site of `U` gives the same functor. -/
noncomputable def slicePostcomp {V U : SpacesEtale B S hS X} (φ : V ⟶ U) :
    Over V ⥤ SpacesEtale B S hS U.obj.left :=
  sliceToSmall B S hS V ⋙
    spacesEtalePostcomp B S hS ((toSpaces B S hS X).map φ) (isEtale_toSpaces_map B S hS X φ)

/-- `AlgebraicGeometry.Space.SpacesEtale.slicePostcomp` is continuous from the localization at
`V` of the spaces-étale topology of `X` to the spaces-étale topology of the algebraic space
`U`, being a composite of two continuous functors of sites. -/
instance isContinuous_slicePostcomp {V U : SpacesEtale B S hS X} (φ : V ⟶ U) :
    (slicePostcomp B S hS φ).IsContinuous
      ((topology B S hS X).over V) (topology B S hS U.obj.left) :=
  Functor.isContinuous_comp _ _ _ (topology B S hS V.obj.left) _

/-- Pushing a slice at `V` forward to a slice at `U` along `φ` and then passing to the
spaces-étale site of `U` is `AlgebraicGeometry.Space.SpacesEtale.slicePostcomp`: both replace
the structure morphism to `X` by the morphism to the algebraic space `U`, which is the
original morphism to `V` composed with the one underlying `φ`. -/
theorem overMap_comp_sliceToSmall {V U : SpacesEtale B S hS X} (φ : V ⟶ U) :
    Over.map φ ⋙ sliceToSmall B S hS U = slicePostcomp B S hS φ := rfl

/-- **The slice pullback is the spaces-étale inverse image.** For a morphism `φ : V ⟶ U` of
the spaces-étale site of `X`, the slice pullback along `φ` and the inverse image of Stacks
03G2, part (3), along the morphism of algebraic spaces underlying `φ` agree through the
comparison equivalences of the slices at `U` and at `V` with the spaces-étale sites of the
algebraic spaces `U` and `V`.

By Stacks 03LQ the inverse image is restriction along postcomposition, and both sides are
therefore restriction along `AlgebraicGeometry.Space.SpacesEtale.slicePostcomp`. -/
noncomputable def overMapPullback_spacesEtaleInverseImageIso {V U : SpacesEtale B S hS X}
    (φ : V ⟶ U) :
    (sheafOverEquivSmall B S hS U (Type (u + 1))).inverse ⋙
        (topology B S hS X).overMapPullback (Type (u + 1)) φ ≅
      spacesEtaleInverseImage B S hS ((toSpaces B S hS X).map φ) ⋙
        (sheafOverEquivSmall B S hS V (Type (u + 1))).inverse := by
  have e₀ : (sheafOverEquivSmall B S hS U (Type (u + 1))).inverse ⋙
        (topology B S hS X).overMapPullback (Type (u + 1)) φ ≅
      (slicePostcomp B S hS φ).sheafPushforwardContinuous (Type (u + 1))
        ((topology B S hS X).over V) (topology B S hS U.obj.left) :=
    @Functor.sheafPushforwardContinuousComp' _ _ _ _ _ _ _ _ _
      (Iso.refl _ : Over.map φ ⋙ sliceToSmall B S hS U ≅ slicePostcomp B S hS φ)
      (Type (u + 1)) _
      ((topology B S hS X).over V) ((topology B S hS X).over U)
      (topology B S hS U.obj.left) _ _ (isContinuous_slicePostcomp B S hS φ)
  have e₁ : spacesEtaleInverseImage B S hS ((toSpaces B S hS X).map φ) ⋙
        (sheafOverEquivSmall B S hS V (Type (u + 1))).inverse ≅
      (spacesEtalePostcomp B S hS ((toSpaces B S hS X).map φ)
          (isEtale_toSpaces_map B S hS X φ)).sheafPushforwardContinuous (Type (u + 1))
        (topology B S hS V.obj.left) (topology B S hS U.obj.left) ⋙
        (sheafOverEquivSmall B S hS V (Type (u + 1))).inverse :=
    Functor.isoWhiskerRight (spacesToposMorphism_inverseImageIso B S hS
      ((toSpaces B S hS X).map φ) (isEtale_toSpaces_map B S hS X φ)) _
  have e₂ : (spacesEtalePostcomp B S hS ((toSpaces B S hS X).map φ)
          (isEtale_toSpaces_map B S hS X φ)).sheafPushforwardContinuous (Type (u + 1))
        (topology B S hS V.obj.left) (topology B S hS U.obj.left) ⋙
        (sheafOverEquivSmall B S hS V (Type (u + 1))).inverse ≅
      (slicePostcomp B S hS φ).sheafPushforwardContinuous (Type (u + 1))
        ((topology B S hS X).over V) (topology B S hS U.obj.left) :=
    @Functor.sheafPushforwardContinuousComp' _ _ _ _ _ _ _ _ _
      (Iso.refl _ : sliceToSmall B S hS V ⋙ spacesEtalePostcomp B S hS
          ((toSpaces B S hS X).map φ) (isEtale_toSpaces_map B S hS X φ) ≅
        slicePostcomp B S hS φ)
      (Type (u + 1)) _
      ((topology B S hS X).over V) (topology B S hS V.obj.left)
      (topology B S hS U.obj.left) _
      (isContinuous_spacesEtalePostcomp_toSpaces_map B S hS φ)
      (isContinuous_slicePostcomp B S hS φ)
  exact e₀ ≪≫ (e₁ ≪≫ e₂).symm

/-- **The slice pullback is the spaces-étale inverse image**, in the form of an isomorphism
onto the inverse image itself: inserting the comparison equivalence at `U` before the slice
pullback along `φ` and the one at `V` after it gives the inverse image of Stacks 03G2,
part (3), along the morphism of algebraic spaces underlying `φ`. -/
noncomputable def sheafOverEquivSmall_overMapPullback_iso {V U : SpacesEtale B S hS X}
    (φ : V ⟶ U) :
    (sheafOverEquivSmall B S hS U (Type (u + 1))).inverse ⋙
        (topology B S hS X).overMapPullback (Type (u + 1)) φ ⋙
        (sheafOverEquivSmall B S hS V (Type (u + 1))).functor ≅
      spacesEtaleInverseImage B S hS ((toSpaces B S hS X).map φ) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (overMapPullback_spacesEtaleInverseImageIso B S hS φ)
      (sheafOverEquivSmall B S hS V (Type (u + 1))).functor ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (spacesEtaleInverseImage B S hS ((toSpaces B S hS X).map φ))
      (sheafOverEquivSmall B S hS V (Type (u + 1))).counitIso ≪≫
    Functor.rightUnitor _

end AlgebraicGeometry.Space.SpacesEtale

end
