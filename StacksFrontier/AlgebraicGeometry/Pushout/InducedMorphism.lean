module

public import StacksFrontier.AlgebraicGeometry.Pushout.ClosedImmersions

/-!
# The morphism between pushouts induced by compatible morphisms on the two pieces

Let `i : Z ⟶ X` and `j : Z ⟶ Y` be closed immersions of schemes and let `f : X' ⟶ X` and
`g : Y' ⟶ Y` be arbitrary morphisms.  An isomorphism `φ : X' ×_X Z ≅ Y' ×_Y Z` over `Z`
identifies the two inverse images of `Z`, so the pulled-back closed immersions have a common
source and `X'` and `Y'` can be glued along it.  The universal property of the glued scheme
then produces a morphism to `Y ⨿_Z X`.

This is the standing situation of [Stacks Project, Tag 0CYY], which compares properties of
that morphism with properties of `f` and `g`.

## Main definitions

* `AlgebraicGeometry.CompatiblePushoutMorphismSituation` is the standing situation.
* `AlgebraicGeometry.CompatiblePushoutMorphismSituation.sourcePushout` is the pushout of the
  two pulled-back closed immersions.
* `AlgebraicGeometry.CompatiblePushoutMorphismSituation.induced` is the induced morphism to
  the pushout of `i` and `j`.

## Implementation notes

The identification of the two inverse images of `Z` is recorded as an isomorphism of scheme
pullbacks together with its compatibility with the two projections to `Z`.  The common source
of the glued data is taken to be the left pullback `X' ×_X Z`; its map to `Y'` is the
projection of the right pullback transported along the isomorphism.  Both maps out of it are
closed immersions, being base changes of `i` and `j`, so the pushout exists by
[Stacks Project, Tag 0B7M].

## References

* [Stacks Project, Tag 0CYY](https://stacks.math.columbia.edu/tag/0CYY)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- The standing situation of [Stacks Project, Tag 0CYY]: two closed immersions `i : Z ⟶ X`
and `j : Z ⟶ Y`, morphisms `f : X' ⟶ X` and `g : Y' ⟶ Y`, and an isomorphism over `Z` between
the two inverse images of `Z`. -/
structure CompatiblePushoutMorphismSituation where
  /-- The common closed subscheme. -/
  Z : Scheme.{u}
  /-- The first target scheme. -/
  X : Scheme.{u}
  /-- The second target scheme. -/
  Y : Scheme.{u}
  /-- The first scheme mapping to `X`. -/
  X' : Scheme.{u}
  /-- The second scheme mapping to `Y`. -/
  Y' : Scheme.{u}
  /-- The first closed immersion. -/
  i : Z ⟶ X
  /-- The second closed immersion. -/
  j : Z ⟶ Y
  /-- The morphism from the first source piece. -/
  f : X' ⟶ X
  /-- The morphism from the second source piece. -/
  g : Y' ⟶ Y
  /-- The morphism `i` is a closed immersion. -/
  [isClosedImmersion_i : IsClosedImmersion i]
  /-- The morphism `j` is a closed immersion. -/
  [isClosedImmersion_j : IsClosedImmersion j]
  /-- The identification between the two inverse images of `Z`. -/
  φ : pullback f i ≅ pullback g j
  /-- The identification of the inverse images of `Z` is a morphism over `Z`. -/
  φ_over : φ.hom ≫ pullback.snd g j = pullback.snd f i

attribute [instance] CompatiblePushoutMorphismSituation.isClosedImmersion_i
  CompatiblePushoutMorphismSituation.isClosedImmersion_j

namespace CompatiblePushoutMorphismSituation

variable (S : CompatiblePushoutMorphismSituation.{u})

/-- The inverse image of `Z` in `X'`, in the situation of [Stacks Project, Tag 0CYY].  It is
also the inverse image of `Z` in `Y'`, through the given identification. -/
abbrev intersection : Scheme.{u} := pullback S.f S.i

/-- The map from the common inverse image of `Z` to `X'`, in the situation of
[Stacks Project, Tag 0CYY]. -/
abbrev toX' : S.intersection ⟶ S.X' := pullback.fst S.f S.i

/-- The map from the common inverse image of `Z` to `Y'`, in the situation of
[Stacks Project, Tag 0CYY].  It uses the given identification of the two inverse images. -/
abbrev toY' : S.intersection ⟶ S.Y' := S.φ.hom ≫ pullback.fst S.g S.j

/-- The map to `X'` out of the common inverse image of `Z` is a closed immersion, being a base
change of `i`.  This is part of the situation of [Stacks Project, Tag 0CYY]. -/
instance isClosedImmersion_toX' : IsClosedImmersion S.toX' := inferInstance

/-- The map to `Y'` out of the common inverse image of `Z` is a closed immersion, being a base
change of `j` composed with an isomorphism.  This is part of the situation of
[Stacks Project, Tag 0CYY]. -/
instance isClosedImmersion_toY' : IsClosedImmersion S.toY' :=
  (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion) S.φ.hom
    (pullback.fst S.g S.j)).2 inferInstance

/-- The scheme obtained by gluing `X'` and `Y'` along their identified inverse images of `Z`,
in the situation of [Stacks Project, Tag 0CYY].  It exists by [Stacks Project, Tag 0B7M]. -/
abbrev sourcePushout : Scheme.{u} := pushout S.toX' S.toY'

/-- The morphism from the glued source to the pushout of `X` and `Y` along `Z`, in the
situation of [Stacks Project, Tag 0CYY].  This is the morphism whose properties that tag
compares with those of `f` and `g`. -/
def induced : S.sourcePushout ⟶ pushout S.i S.j :=
  pushout.desc (S.f ≫ pushout.inl S.i S.j) (S.g ≫ pushout.inr S.i S.j) (by
    simp only [toX', toY', Category.assoc, pullback.condition_assoc]
    rw [← S.φ_over]
    simp only [Category.assoc]
    rw [pushout.condition])

/-- The square relating the first piece of the glued source to the first piece of the glued
target commutes, in the situation of [Stacks Project, Tag 0CYY]. -/
theorem inl_comp_induced :
    pushout.inl S.toX' S.toY' ≫ S.induced = S.f ≫ pushout.inl S.i S.j :=
  pushout.inl_desc _ _ _

/-- The square relating the second piece of the glued source to the second piece of the glued
target commutes, in the situation of [Stacks Project, Tag 0CYY]. -/
theorem inr_comp_induced :
    pushout.inr S.toX' S.toY' ≫ S.induced = S.g ≫ pushout.inr S.i S.j :=
  pushout.inr_desc _ _ _

end CompatiblePushoutMorphismSituation

end AlgebraicGeometry

end
