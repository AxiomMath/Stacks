module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedPointsComparison

/-!
# Properness of a universe lift

Let `S` be a scheme contained in a big fppf site `B`. A morphism of presheaves on the big fppf
site of `S` with values in `Type u`, the universe of the schemes, is proper in the sense of
**Stacks 03ZM** exactly when its universe lift is proper in the sense carried by
`AlgebraicGeometry.Space.IsProperULift`, the form of that condition for presheaves with values
in `Type (max w u)` in which a formal algebraic space lives.

Each of the three conjuncts of Stacks 03ZM transfers on its own, and the two directions are of
different natures. Separatedness and being of finite type are conditions on the presheaves'
sections over objects of the site, so they transfer in both directions at once. Universal
closedness quantifies over all algebraic spaces over `S` mapping to the target, and the
quantifier ranges over a strictly larger collection in the lifted universe; the direction that
discards the extra algebraic spaces is immediate from the comparison of point spaces, and the
direction that produces them is **Stacks 02YS** in the form that a large-valued algebraic space
is the universe lift of a presheaf in the value universe of the site.

## Main results

* `AlgebraicGeometry.Space.isSeparatedULift_whiskerRight_iff`: separatedness transfers.
* `AlgebraicGeometry.Space.universallyClosedULift_whiskerRight_iff`: universal closedness
  transfers.
* `AlgebraicGeometry.Space.isProperULift_whiskerRight_iff`: **Stacks 03ZM** for a universe lift
  is Stacks 03ZM for the morphism it lifts.

## Implementation notes

The separated transfer is the one already used for a single direction in
`StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionProper`: separatedness is the relative
closed-immersion property of the relative diagonal, the relative diagonal of a lift is the lift
of the relative diagonal composed with the comparison isomorphism of fibre products, and a
relative property along `CategoryTheory.yoneda` carried by a fully faithful functor preserving
fibre products is the relative property along `CategoryTheory.uliftYoneda`. Taken as an
equivalence it needs nothing beyond `CategoryTheory.MorphismProperty.relative_respectsIso`,
since `AlgebraicGeometry.Space.relative_comp_map_iff` is already an equivalence.

Being of finite type is `AlgebraicGeometry.Space.isFiniteTypeULift_whiskerRight_iff`, which is
available as an equivalence, so only universal closedness needs work here, and only in the
direction from the lift to the morphism: the condition for the lift, applied to the lift of a
`Type u`-valued algebraic space, gives closedness on points of the lift of the base change,
which is closedness on points of the base change itself by
`AlgebraicGeometry.Space.isClosedMorphismULift_whiskerRight_iff`. The comparison of the lift of
a fibre product with the fibre product of the lifts is
`AlgebraicGeometry.Space.isPullback_whiskerRight`.

## References

* [Stacks Project, Tag 02YS](https://stacks.math.columbia.edu/tag/02YS)
* [Stacks Project, Tag 03HI](https://stacks.math.columbia.edu/tag/03HI)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- `inferInstance` for `HasPullbacks` on presheaves over the big fppf site is a deep instance search
/-- Pullbacks of presheaves on the big fppf site of `S` (instance search times out without
this shortcut). -/
private instance hasPullbacks_presheaf_largeValuedProperTransfer :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type v) := inferInstance

private instance (priority := high) hasPullback_presheaf_largeValuedProperTransfer
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- The universe lift of a morphism of presheaves of `Type u` on the big fppf site of `S` is
separated exactly when the morphism is: the relative diagonal of the lift is the lift of the
relative diagonal composed with the comparison isomorphism of fibre products, and the relative
closed-immersion property along `CategoryTheory.uliftYoneda` is the one along
`CategoryTheory.yoneda` carried by the lifting functor. -/
theorem isSeparatedULift_whiskerRight_iff {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q : F ⟶ G) :
    IsSeparatedULift.{w} B S hS (Functor.whiskerRight q uliftFunctor.{w}) ↔
      IsSeparated B S hS q := by
  let C := BigFppfOver B S hS
  let H := (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (max w u))).obj uliftFunctor.{w}
  let R := MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have hdiag : pullback.diagonal (H.map q) =
      H.map (pullback.diagonal q) ≫ (PreservesPullback.iso H q q).hom := by
    apply pullback.hom_ext <;> simp [← H.map_comp]
  have step : R.relative (uliftYoneda.{w}) (pullback.diagonal (H.map q)) ↔
      R.relative (uliftYoneda.{w}) (H.map (pullback.diagonal q)) := by
    rw [hdiag]
    exact (R.relative (uliftYoneda.{w})).cancel_right_of_respectsIso _ _
  exact step.trans (relative_comp_map_iff yoneda H R (pullback.diagonal q))

/-- The universe lift of a morphism of presheaves of `Type u` on the big fppf site of `S` is
universally closed exactly when the morphism is.

The direction producing the condition for the lift is
`AlgebraicGeometry.Space.universallyClosedULift_whiskerRight_of_universallyClosed`. For the
other direction a `Type u`-valued algebraic space mapping to the target is replaced by its
lift, over which the hypothesis applies; the base change of the lift along the lifted point is
the lift of the base change, so closedness on points descends by
`AlgebraicGeometry.Space.isClosedMorphismULift_whiskerRight_iff`. -/
theorem universallyClosedULift_whiskerRight_iff
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q : F ⟶ G) :
    UniversallyClosedULift.{w} B S hS (Functor.whiskerRight q uliftFunctor.{w}) ↔
      UniversallyClosed B S hS q := by
  refine ⟨fun h Z' hZ'alg g' => ?_,
    universallyClosedULift_whiskerRight_of_universallyClosed B S hS q⟩
  have hclosed := h (Z' ⋙ uliftFunctor.{w})
    ((isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS Z').mpr hZ'alg)
    (Functor.whiskerRight g' uliftFunctor.{w})
  have hpb := isPullback_whiskerRight.{w} B S hS (IsPullback.of_hasPullback g' q)
  exact (isClosedMorphismULift_whiskerRight_iff.{w} B S hS (pullback.fst g' q)).mp
    (isClosedMap_pointsMapULift_of_comp_isIso B S hS hpb.isoPullback.hom
      hpb.isoPullback_hom_fst hclosed)

/-- **Stacks 03ZM for a universe lift.** The universe lift of a morphism of presheaves of
`Type u` on the big fppf site of `S` is proper — separated, of finite type and universally
closed — exactly when the morphism is.

Each conjunct transfers separately: separatedness by
`AlgebraicGeometry.Space.isSeparatedULift_whiskerRight_iff`, being of finite type by
`AlgebraicGeometry.Space.isFiniteTypeULift_whiskerRight_iff` and universal closedness by
`AlgebraicGeometry.Space.universallyClosedULift_whiskerRight_iff`. -/
@[stacks 03ZM "for a universe lift"]
theorem isProperULift_whiskerRight_iff {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q : F ⟶ G) :
    IsProperULift.{w} B S hS (Functor.whiskerRight q uliftFunctor.{w}) ↔
      IsProper B S hS q :=
  and_congr (isSeparatedULift_whiskerRight_iff.{w} B S hS q)
    (and_congr (isFiniteTypeULift_whiskerRight_iff.{w} B S hS q)
      (universallyClosedULift_whiskerRight_iff.{w} B S hS q))

end AlgebraicGeometry.Space

end
