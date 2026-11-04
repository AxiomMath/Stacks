module

public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionChartTwoIso
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange

/-!
# The identity point of a charted self-intersection (Stacks 04XH)

Let `p : U ⟶ 𝒴` be a 1-morphism from the algebraic stack represented by a scheme `U` of the site,
let `P` be a 2-fibre product square over the cospan `(p, p)` — a model of `U ×_𝒴 U` — let `F` be
a presheaf representing its apex and let `c : h_R ⟶ F` be a chart of `F` by a scheme `R` of the
site which is surjective on points. Write `a` and `b` for the two legs of the square read as
morphisms of schemes `R ⟶ U` (`AlgebraicGeometry.Stack.chartLeg`).

Then every point `u` of `U` is hit by a point `r` of `R` with `a r = u` **and** `b r = u`: the
diagonal of the relation `R` lies over the diagonal of `U`, at least on points. This is the point
at which the slicing construction of **Stacks 06MF** is performed.

## Main results

* `AlgebraicGeometry.Stack.pointsHomeomorphScheme_pointsMap_chartLeg`: the map on points of a leg
  `AlgebraicGeometry.Stack.chartLeg`, computed through the representation.
* `AlgebraicGeometry.Stack.exists_point_chartLeg_eq`: the identity point over a given point of
  `U`.

## Implementation notes

The two images in `|𝒴|` of the point `u`, taken through the *same* 1-morphism `p`, are equal by
`rfl`, so **Stacks 04XH**
(`AlgebraicGeometry.Stack.AlgebraicStacks.exists_point_of_isTwoFibreProduct`) lifts the pair
`(u, u)` to a point of `|P.pt|`. That point is transported to a point of the representing
presheaf `F` by `AlgebraicGeometry.Stack.bijective_spacePointMap_representing` and lifted along
the chart by `AlgebraicGeometry.Space.isSurjective_of_presheafSurjective`.

Reading off the two images of the resulting point of `R` as points of the scheme `U` is the same
bookkeeping as in
`AlgebraicGeometry.Stack.AlgebraicStacks.eq_of_specializes_of_isLocallyQuasiFinite_fieldPoint`:
`AlgebraicGeometry.Stack.spacePointMap_representing_naturality` moves the map on points of a leg
across the representation, and
`AlgebraicGeometry.Stack.pointsHomeomorphScheme_representedChartPointMap` identifies the points
of the represented algebraic stack of `U` with those of the scheme `U`.

Surjectivity of `c` is stated in the form the atlas of
`AlgebraicGeometry.IsAlgebraicSpace.exists_atlas` provides it, namely the presheaf-level
inverse-image property of surjective morphisms of schemes.

No `@[stacks]` attribute is claimed: this is **Stacks 04XH** read at one particular square, and
that tag is registered on the general statement.

## References

* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

attribute [local instance] AlgebraicGeometry.Stack.pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒴 : AlgebraicStacks.{u, w} B S hS} (U : BigFppfOver B S hS)
  (p : schemeStack.{u, w} B S hS U ⟶ 𝒴) (P : Bicategory.TwoCommSq p p)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eF : StacksRepresentableCFG.EquivalenceOver P.pt.val.val.p
    (presheafOfCategories (F ⋙ typeToCat)).p)
  (R : BigFppfOver B S hS) (c : yoneda.obj R ⟶ F)

/-- **A leg of a charted square computes the map on points it induces.** If `r` is a point of
the chart `h_R` of the apex, then the image under `chartLeg … leg` of the point of the scheme `R`
below `r` is the point of the scheme `U` below the image of `r` under the leg.

This is `AlgebraicGeometry.Stack.spacePointMap_representing_naturality` read through
`AlgebraicGeometry.Stack.pointsHomeomorphScheme_representedChartPointMap`, with the map on points
of the chart `c` factored out of that of `chartLeg … leg`. -/
theorem pointsHomeomorphScheme_pointsMap_chartLeg
    (leg : P.pt ⟶ schemeStack.{u, w} B S hS U) (r : Space.points B S hS (yoneda.obj R)) :
    (BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p P F eF R c leg)
        (Space.pointsToScheme B S hS R r) =
      pointsHomeomorphScheme B S hS U
        (AlgebraicStacks.pointsMap B S hS leg
          (spacePointMap B S hS F P.pt.val
            (representingEquivalence B S hS F P.pt.val eF).functor
            (Space.pointsMap B S hS (yoneda.obj R) c r))) := by
  rw [← Space.pointsToScheme_pointsMap, Functor.map_preimage,
    ← pointsHomeomorphScheme_representedChartPointMap B S hS U,
    Space.pointsMap_comp B S hS (yoneda.obj R) c
      (representingMap B S hS P.pt.val (schemeStack.{u, w} B S hS U).val F (yoneda.obj U) eF
        (representedChart B S hS U) leg.hom)]
  refine congrArg (pointsHomeomorphScheme B S hS U) ?_
  exact spacePointMap_representing_naturality B S hS F (yoneda.obj U) P.pt.val
    (schemeFibredCategory B S hS U) eF (representedChart B S hS U) leg.hom
    (Space.pointsMap B S hS (yoneda.obj R) c r)

/-- **The identity point of a charted self-intersection.** Let `P` be a 2-fibre product square
over the cospan `(p, p)`, with `p : U ⟶ 𝒴` a 1-morphism out of the algebraic stack represented by
a scheme `U` of the site, charted by a morphism `c : h_R ⟶ F` which is surjective on points.
Then every point `u` of the scheme `U` is the image under *both* legs
`AlgebraicGeometry.Stack.chartLeg` of one point of the scheme `R`.

**Stacks 04XH** lifts the pair `(u, u)`, whose two images in `|𝒴|` under `p` agree trivially, to
a point of `|P.pt|`; that point is pulled back to the representing presheaf and then along the
chart. -/
theorem exists_point_chartLeg_eq (hP : Bicategory.IsTwoFibreProduct P)
    (hcsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c)
    (u : (BigFppfOver.toScheme B S hS).obj U) :
    ∃ r : (BigFppfOver.toScheme B S hS).obj R,
      (BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p P F eF R c P.fst) r = u ∧
        (BigFppfOver.toScheme B S hS).map (chartLeg B S hS U p P F eF R c P.snd) r = u := by
  classical
  let := pointTopology B S hS (schemeFibredCategory B S hS U)
  obtain ⟨z, hz1, hz2⟩ := AlgebraicStacks.exists_point_of_isTwoFibreProduct B S hS P hP
    ((pointsHomeomorphScheme B S hS U).symm u) ((pointsHomeomorphScheme B S hS U).symm u) rfl
  obtain ⟨zF, hzF⟩ := (bijective_spacePointMap_representing B S hS F P.pt.val eF).2 z
  obtain ⟨r, hr⟩ := Space.isSurjective_of_presheafSurjective B S hS c hcsurj zF
  refine ⟨Space.pointsToScheme B S hS R r, ?_, ?_⟩ <;>
    rw [pointsHomeomorphScheme_pointsMap_chartLeg B S hS U p P F eF R c _ r, hr, hzF] <;>
    simp [hz1, hz2]

end AlgebraicGeometry.Stack

end
