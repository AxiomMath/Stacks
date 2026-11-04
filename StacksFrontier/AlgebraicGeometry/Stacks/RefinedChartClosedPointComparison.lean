module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedChartFibreSquareClosedPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.RefinedChartDiagonalComparison

/-!
# The refinement comparison of Stacks 0DS9 at a closed point of the refined chart

`AlgebraicGeometry.Stack.hasRelationLocalRingDimension_refinement_diagonal_iff` compares the
invariant of **Stacks 0DSA** measured on a smoothly refined chart `h ≫ f` with the invariant
measured on `f`, and carries two `AlgebraicGeometry.Space.HasClosedChartFibreSquare` hypotheses —
conditions on squares of étale charts of the two base changes presenting the refined relation.
This file discharges both from one hypothesis the source's proof actually produces: that the
point of the refined chart is **closed in that chart**, which is what shrinking the two charts of
Stacks 0DS9 achieves.

## Main results

* `AlgebraicGeometry.Stack.hasRelationLocalRingDimension_refinement_diagonal_iff_of_isClosed`:
  the refinement comparison with the closedness of the chart point as its only extra hypothesis.

## How the two conditions are discharged

Both legs of the refined relation are base changes of `yoneda.map h` for a morphism `h` of the
site, so `AlgebraicGeometry.Space.hasClosedChartFibreSquare_of_isClosed_pointsToScheme` applies
to each, and each time it asks for closedness of the point of the *second* coordinate in the
scheme `U'`:

* for the first leg the second coordinate is the source map of the refined relation, and the
  point is read on the diagonal, where the source map returns the chart point
  (`AlgebraicGeometry.Stack.pointsMap_selfIntersectionSourceMap_diagonal`);
* for the second leg it is the first `U'`-coordinate of the intermediate stage, which on the
  diagonal is again the chart point
  (`AlgebraicGeometry.Stack.geometricPointMap_relationRefinement_coord_eq_of_diagonal`).

So both reduce to closedness of the one point `ν̄'` in `U'`, and that is the hypothesis.

## References

* [Stacks Project, Tag 053M](https://stacks.math.columbia.edu/tag/053M)
* [Stacks Project, Tag 0DS9](https://stacks.math.columbia.edu/tag/0DS9)
* [Stacks Project, Tag 0DSA](https://stacks.math.columbia.edu/tag/0DSA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section ClosedPoint

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} {U U' : BigFppfOver B S hS}
  {f : schemeStack.{u, w} B S hS U ⟶ 𝒳} {h : U' ⟶ U}
  (sq : Bicategory.TwoCommSq f f)
  (Q : Bicategory.TwoCommSq (schemeStackMap.{u, w} B S hS h) sq.fst)
  (T : Bicategory.TwoCommSq (sq.pasteFst Q).snd (schemeStackMap.{u, w} B S hS h))
  (R P W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eR : StacksRepresentableCFG.EquivalenceOver
    sq.pt.val.val.p (presheafOfCategories (R ⋙ typeToCat)).p)
  (eP : StacksRepresentableCFG.EquivalenceOver
    Q.pt.val.val.p (presheafOfCategories (P ⋙ typeToCat)).p)
  (eW : StacksRepresentableCFG.EquivalenceOver
    T.pt.val.val.p (presheafOfCategories (W ⋙ typeToCat)).p)

include eP in
/-- **The refinement comparison of Stacks 0DS9 on the diagonal, from a closed point of the
refined chart.** For a smooth chart `f : U ⟶ 𝒳` of a locally Noetherian algebraic stack, a
smooth refinement `h : U' ⟶ U` of it and a geometric point `ν̄'` of `U'` whose image is a
**closed** point of `U'`, the invariant `2 dim(𝒪_{U', ν̄'}) - dim(𝒪_{W, e'(ν̄')})` of
**Stacks 0DSA** measured on the refined chart equals the invariant
`2 dim(𝒪_{U, h(ν̄')}) - dim(𝒪_{R, e(h(ν̄'))})` measured on the original chart.

This is `AlgebraicGeometry.Stack.hasRelationLocalRingDimension_refinement_diagonal_iff` with its
two `AlgebraicGeometry.Space.HasClosedChartFibreSquare` hypotheses discharged by
`AlgebraicGeometry.Space.hasClosedChartFibreSquare_of_isClosed_pointsToScheme`: each leg of the
refined relation is a base change of `yoneda.map h`, and on the diagonal the second coordinate
of the point is the chart point in both cases.

Closedness is the hypothesis the source's proof reaches by shrinking the two charts, and it is
not removable; what is removed here is only its chart-level formulation.

The comparison equivalence `eP` presenting the intermediate stage `U' ×_{h, U, t} R` does not
appear in the statement — the invariant is read on the refined relation and on the relation —
but the two base changes the proof runs through do, so it is an argument. -/
theorem hasRelationLocalRingDimension_refinement_diagonal_iff_of_isClosed
    (hf : AlgebraicStacks.IsSmooth B S hS f) (hsq : Bicategory.IsTwoFibreProduct sq)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (hhsm : Space.IsSmooth B S hS (yoneda.map h))
    (hQ : Bicategory.IsTwoFibreProduct Q) (hT : Bicategory.IsTwoFibreProduct T)
    (hR : IsAlgebraicSpace B S hS R) (hP : IsAlgebraicSpace B S hS P)
    (hW : IsAlgebraicSpace B S hS W)
    (δ : Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS U f) sq)
    (δ' : Bicategory.TwoCommSq.PreHom
      (selfIntersectionDiagonalSquare B S hS U' (schemeStackMap.{u, w} B S hS h ≫ f))
      (refinedSelfIntersectionSquare B S hS sq Q T))
    (ν : Space.GeometricPoint B S hS (yoneda.obj U'))
    (hν : IsClosed ({Space.pointsToScheme B S hS U' ν.image} :
      Set ((BigFppfOver.toScheme B S hS).obj U')))
    (d : ℤ) :
    HasRelationLocalRingDimension B S hS U' (schemeStackMap.{u, w} B S hS h ≫ f)
        (refinedSelfIntersectionSquare B S hS sq Q T) W
        (PresheafOfCategories.sliceElementsEquivalenceOver U') eW
        (Space.pointsMap B S hS (yoneda.obj U')
          (selfIntersectionDiagonalMap B S hS U' (schemeStackMap.{u, w} B S hS h ≫ f)
            (refinedSelfIntersectionSquare B S hS sq Q T) W
            (PresheafOfCategories.sliceElementsEquivalenceOver U') eW δ') ν.image) d ↔
      HasRelationLocalRingDimension B S hS U f sq R
        (PresheafOfCategories.sliceElementsEquivalenceOver U) eR
        (Space.pointsMap B S hS (yoneda.obj U)
          (selfIntersectionDiagonalMap B S hS U f sq R
            (PresheafOfCategories.sliceElementsEquivalenceOver U) eR δ)
          (Space.pointsMap B S hS (yoneda.obj U') (yoneda.map h) ν.image)) d := by
  -- the scheme morphism underlying `h` is smooth, hence locally of finite type
  let : Smooth ((BigFppfOver.toScheme B S hS).map h) :=
    (Space.isSmooth_yoneda_map_iff B S hS h).1 hhsm
  have hhft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map h) := inferInstance
  -- the diagonal geometric point of the refined relation
  set a := Space.geometricPointMap (selfIntersectionDiagonalMap B S hS U'
    (schemeStackMap.{u, w} B S hS h ≫ f) (refinedSelfIntersectionSquare B S hS sq Q T) W
    (PresheafOfCategories.sliceElementsEquivalenceOver U') eW δ') ν with ha
  -- on the diagonal the source map of the refined relation returns the chart point
  have hsrcimg : (Space.geometricPointMap (relationRefinementRight B S hS sq Q T W eW)
      a).image = ν.image := by
    rw [ha]
    simp only [Space.geometricPointMap_image]
    exact pointsMap_selfIntersectionSourceMap_diagonal B S hS U'
      (schemeStackMap.{u, w} B S hS h ≫ f) (refinedSelfIntersectionSquare B S hS sq Q T) W
      (PresheafOfCategories.sliceElementsEquivalenceOver U') eW δ' ν.image
  -- the closedness input for the first leg
  have hcl₁ : Space.HasClosedChartFibreSquare B S hS (yoneda.map h)
      (relationRefinementFst B S hS sq Q T P W eP eW)
      (relationRefinementRight B S hS sq Q T W eW) a :=
    Space.hasClosedChartFibreSquare_of_isClosed_pointsToScheme B S hS hP hW
      (relationRefinementSnd B S hS sq Q R P eR eP ≫
        selfIntersectionSourceMap B S hS U f sq R
          (PresheafOfCategories.sliceElementsEquivalenceOver U) eR)
      h hhft _ _
      (isPullback_representingMap_refinementSourceBaseChange.{u, w} B S hS sq Q hT R P W hP
        eR eP eW)
      a (by rw [hsrcimg]; exact hν)
  -- the closedness input for the second leg, at the image of the diagonal point
  have hcoord : Space.geometricPointMap (relationRefinementMidFst B S hS sq Q P eP)
      (Space.geometricPointMap (relationRefinementFst B S hS sq Q T P W eP eW) a) =
      Space.geometricPointMap (relationRefinementRight B S hS sq Q T W eW) a :=
    geometricPointMap_relationRefinement_coord_eq_of_diagonal.{u, w} B S hS sq Q T P W eP eW δ' ν
  have hcl₂ : Space.HasClosedChartFibreSquare B S hS (yoneda.map h)
      (relationRefinementSnd B S hS sq Q R P eR eP)
      (relationRefinementMidFst B S hS sq Q P eP)
      (Space.geometricPointMap (relationRefinementFst B S hS sq Q T P W eP eW) a) :=
    Space.hasClosedChartFibreSquare_of_isClosed_pointsToScheme B S hS hR hP
      (selfIntersectionTargetMap B S hS U f sq R
        (PresheafOfCategories.sliceElementsEquivalenceOver U) eR)
      h hhft _ _
      (isPullback_representingMap_refinementTargetBaseChange.{u, w} B S hS sq hQ R P hR
        eR eP).flip
      _ (by rw [hcoord, hsrcimg]; exact hν)
  exact hasRelationLocalRingDimension_refinement_diagonal_iff.{u, w} B S hS sq Q T R P W
    eR eP eW hf hsq h𝒳 hhsm hQ hT hR hP hW δ δ' ν hcl₁ hcl₂ d

end ClosedPoint

end AlgebraicGeometry.Stack

end
