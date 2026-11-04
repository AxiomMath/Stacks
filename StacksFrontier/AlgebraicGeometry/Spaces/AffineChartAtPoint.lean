module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# An affine étale chart through a prescribed point of an algebraic space

Stacks 03H6 produces an *affine* surjective étale chart of an algebraic space only when the
space is quasi-compact. Stacks 082H nevertheless says "we may and do assume `Y` is an affine
scheme" for an arbitrary target, after choosing an étale morphism of *pointed* spaces
`(U, u) ⟶ (Y, y)`. What makes that legitimate is the statement proved here: every point of an
algebraic space, quasi-compact or not, lies in the image of an étale morphism from an object
of the site whose underlying scheme is affine.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.exists_affine_etale_chart_at_point`: an affine object of the site
  with an étale morphism to the algebraic space whose image on points contains the prescribed
  point.

## Implementation notes

Surjectivity is dropped, and that is the whole point: a single affine chart cannot be
surjective onto a non-quasi-compact space, while a single affine chart *through* a given point
always exists. The result is therefore not a weakening of Stacks 03H6 but the complementary
statement, and it needs no quasi-compactness hypothesis.

The input is `AlgebraicGeometry.IsAlgebraicSpace.exists_affine_coproduct_atlas`, the form of
Stacks 03FX which keeps the affine summands of the chart as objects of the site together with
their open immersions `j i` into it. Three steps then suffice.

* The chart is surjective on points by Stacks 03H5
  (`AlgebraicGeometry.Space.isSurjective_of_presheafSurjective`), so the prescribed point of
  the space is the image of a point of the chart, and
  `AlgebraicGeometry.Space.pointsToScheme` turns that into a point of the chart's underlying
  scheme.
* That scheme point lies in the image of one summand. This is the second conclusion of
  `AlgebraicGeometry.isOpenImmersion_cover_disjoint_of_iso_sigma`, which is stated for exactly
  the data the atlas supplies: an isomorphism out of a coproduct of schemes together with the
  identities `Sigma.ι _ i ≫ e.hom = (BigFppfOver.toScheme B S hS).map (j i)`.
* The point of the summand needed in the conclusion is the one `w` names under the comparison
  bijection of Stacks 03BX clause (1), and
  `AlgebraicGeometry.Space.pointsToScheme_pointsMap_yoneda` together with injectivity of that
  comparison identifies its image in the chart with the chosen point, whence its image in the
  space is the prescribed one.

Étaleness of the composite `yoneda.map (j i) ≫ f` is not re-derived: it is one of the
conclusions of `AlgebraicGeometry.IsAlgebraicSpace.exists_affine_coproduct_atlas`.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 03H5](https://stacks.math.columbia.edu/tag/03H5)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 082H](https://stacks.math.columbia.edu/tag/082H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An affine étale chart through a prescribed point.** Every point of an algebraic space
over `S` lies in the image on points of an étale morphism from an object of the big fppf site
whose underlying scheme is affine.

No quasi-compactness is assumed and no surjectivity is asserted: Stacks 03H6
(`AlgebraicGeometry.Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover`) gives
an affine chart which is *surjective* and needs the space to be quasi-compact for it, whereas a
single affine chart through one point always exists. This is what licenses the reduction "we
may and do assume `Y` is an affine scheme" in the proof of Stacks 082H, where the target is an
arbitrary algebraic space and only a chart at the chosen point `y` of it is wanted. -/
theorem exists_affine_etale_chart_at_point (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (x : points B S hS F) :
    ∃ (W : BigFppfOver B S hS) (b : yoneda.obj W ⟶ F),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b ∧
      ∃ w : points B S hS (yoneda.obj W),
        pointsMap B S hS (yoneda.obj W) b w = x := by
  obtain ⟨U, f, I, W, j, e, hfSurj, -, hWaffine, hιe, -, hjEtale, -⟩ :=
    IsAlgebraicSpace.exists_affine_coproduct_atlas B S hS F hF
  -- The chart is surjective on points, so the prescribed point comes from one of the chart.
  obtain ⟨y, hy⟩ := isSurjective_of_presheafSurjective B S hS f hfSurj x
  -- The corresponding point of the chart's underlying scheme lies in a single summand.
  obtain ⟨i, w, hjw⟩ :=
    (isOpenImmersion_cover_disjoint_of_iso_sigma e hιe).2.1 (pointsToScheme B S hS U y)
  -- The point of the summand named by `w` maps to the prescribed point of the space.
  obtain ⟨v, hv⟩ := surjective_pointsToScheme B S hS (W i) w
  refine ⟨W i, yoneda.map (j i) ≫ f, hWaffine i, hjEtale i, v, ?_⟩
  have hjv : pointsMap B S hS (yoneda.obj (W i)) (yoneda.map (j i)) v = y :=
    injective_pointsToScheme B S hS U
      (by rw [pointsToScheme_pointsMap_yoneda, hv, hjw])
  rw [pointsMap_comp_apply, hjv, hy]

end AlgebraicGeometry.Space

end
