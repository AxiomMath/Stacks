module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningFlatDeformation

/-!
# From a representable thickening of large-valued algebraic spaces to a thickening subfunctor

`AlgebraicGeometry.Space.IsRepresentableThickeningULift` is a condition on a *morphism* of
presheaves on the big fppf site of `S` with values in `Type (max w u)`: every represented base
change of it is a thickening of schemes. `AlgebraicGeometry.Space.IsThickening` is the
condition of **Stacks 05ZK, part (1)** on a *subfunctor* of an algebraic space valued in
`Type u`. The two are deliberately not counterparts, as the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/LargeValuedSurjective.lean` record, and the statements of
**Stacks 05ZH** — faithfulness, fullness and essential surjectivity of base change along the
inclusion of a thickening — are all phrased with the second.

This file converts the first into the second, so that the Stacks 05ZH statements become
applicable to a morphism carrying the first. The value universe is no obstruction: a
large-valued algebraic space is pointwise `u`-small, hence is the universe lift of an algebraic
space valued in the universe of the site, and the thickening condition descends with it.

## Main results

* `AlgebraicGeometry.Space.exists_isThickening_range_of_isRepresentableThickeningULift`: a
  representable thickening of large-valued algebraic spaces descends to a morphism of algebraic
  spaces in the value universe of the site whose range is a thickening subfunctor of the
  target, compatibly with the descent isomorphisms.

## Implementation notes

The three steps are each already in the library, and the content here is only that they
compose.

Descent of the objects is
`AlgebraicGeometry.Space.exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift`, which rests on
the pointwise smallness `AlgebraicGeometry.Space.small_of_isAlgebraicSpaceULift`; the shrinking
isomorphism `AlgebraicGeometry.Space.shrinkCompUliftFunctorIso` is used directly rather than
the existential, so that the descended morphism can be produced by fullness of the universe
lift of presheaves and the comparison square recorded. Descent of the *condition* along that
square is `AlgebraicGeometry.Space.relative_comp_map_iff`, the universe lift of presheaves
being fully faithful and preserving fibre products; the condition first has to be moved onto
the lifted morphism, which is a base change of the given one along an isomorphism and so is
covered by `AlgebraicGeometry.FormalSpace.inverseImage_isThickening_isStableUnderBaseChange`.

Passing from the descended morphism to a subfunctor is
`AlgebraicGeometry.Space.isThickening_range_of_isClosedImmersion_isSurjective`: a thickening of
schemes is a closed immersion and surjective, both conditions being monotone in the property of
schemes and so transported by `CategoryTheory.MorphismProperty.relative_monotone`, and
surjectivity on the point sets of Stacks 03BU follows from representable surjectivity by
`AlgebraicGeometry.Space.isSurjective_of_presheafSurjective`.

Taking `w := u + 1` is the case of **Stacks 0AIU**, whose stages are fppf sheaves valued in
`Type (u + 1)` and whose transition morphisms carry
`AlgebraicGeometry.Space.IsRepresentableThickeningULift`; what this supplies there is the
`AlgebraicGeometry.Space.IsThickening` datum that the Stacks 05ZH statements take. What is
*not* supplied is the translation of an étale chart: Stacks 05ZH speaks of the spaces-étale
sites `AlgebraicGeometry.Space.SpacesEtale` of algebraic spaces valued in `Type u`, so using it
on a chart of an fppf sheaf still needs the chart and the cartesian square it sits in to be
carried down to that universe and back, and the range factorization
`CategoryTheory.Subfunctor.toRange` to be absorbed into the base-change functor.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe w u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A representable thickening of large-valued algebraic spaces is a thickening subfunctor,
after descent to the value universe of the site.** Let `a : F ⟶ G` be a morphism of presheaves
on the big fppf site of `S` with values in `Type (max w u)`, let `F` and `G` be algebraic
spaces over `S`, and let every represented base change of `a` be a thickening of schemes. Then
`F` and `G` are the universe lifts of algebraic spaces `F'` and `G'` over `S` valued in
`Type u`, the morphism `a` is the universe lift of a morphism `a' : F' ⟶ G'` up to those two
isomorphisms, and the range of `a'` is a thickening of `G'` in the sense of
**Stacks 05ZK, part (1)**.

This is what makes the statements of **Stacks 05ZH** applicable to a transition morphism of the
directed systems of **Stacks 0AIU**, which carry
`AlgebraicGeometry.Space.IsRepresentableThickeningULift` with `w := u + 1` while Stacks 05ZH is
stated at `AlgebraicGeometry.Space.IsThickening`. -/
theorem exists_isThickening_range_of_isRepresentableThickeningULift
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (a : F ⟶ G)
    (hF : IsAlgebraicSpaceULift.{w} B S hS F)
    (hG : IsAlgebraicSpaceULift.{w} B S hS G)
    (ha : IsRepresentableThickeningULift.{w} B S hS a) :
    ∃ (F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (G' : AlgebraicSpaces B S hS)
      (a' : F' ⟶ G'.obj) (eF : F' ⋙ uliftFunctor.{w} ≅ F)
      (eG : G'.obj ⋙ uliftFunctor.{w} ≅ G),
      IsAlgebraicSpace B S hS F' ∧
        ((Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (max w u))).obj
          uliftFunctor.{w}).map a' ≫ eG.hom = eF.hom ≫ a ∧
          IsThickening B S hS G' (Subfunctor.range a') := by
  classical
  let H := (Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (max w u))).obj
          uliftFunctor.{w}
  have _ := small_of_isAlgebraicSpaceULift B S hS hF
  have _ := small_of_isAlgebraicSpaceULift B S hS hG
  let F' := FunctorToTypes.shrink.{u} F
  let G' := FunctorToTypes.shrink.{u} G
  let eF : H.obj F' ≅ F := shrinkCompUliftFunctorIso F
  let eG : H.obj G' ≅ G := shrinkCompUliftFunctorIso G
  let a' : F' ⟶ G' := H.preimage (eF.hom ≫ a ≫ eG.inv)
  -- the lifted descended morphism is a base change of `a` along an isomorphism
  have hsq : IsPullback eF.hom (H.map a') a eG.hom := by
    apply IsPullback.of_horiz_isIso
    simp [a', H.map_preimage]
  have ha' : IsRepresentableThickeningULift.{w} B S hS (H.map a') :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hsq ha
  -- so the thickening condition descends to `a'` itself
  have hthick : (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative yoneda a' :=
    (relative_comp_map_iff yoneda H _ a').mp ha'
  have hF' : IsAlgebraicSpace B S hS F' :=
    (isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS F').mp
      (isAlgebraicSpaceULift_of_iso B S hS eF.symm hF)
  have hG' : IsAlgebraicSpace B S hS G' :=
    (isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS G').mp
      (isAlgebraicSpaceULift_of_iso B S hS eG.symm hG)
  -- a thickening of schemes is a closed immersion and is surjective
  have hclosed : IsClosedImmersion B S hS a' :=
    MorphismProperty.relative_monotone (fun _ _ _ h ↦ h.1) _ hthick
  have hsurj : IsSurjective B S hS a' :=
    isSurjective_of_presheafSurjective B S hS a'
      (MorphismProperty.relative_monotone (fun _ _ _ h ↦ ⟨h.2⟩) _ hthick)
  exact ⟨F', ⟨G', hG'⟩, a', eF, eG, hF', hsq.w.symm,
    isThickening_range_of_isClosedImmersion_isSurjective B S hS hF' ⟨G', hG'⟩ a'
      hclosed hsurj⟩

end AlgebraicGeometry.Space

end
