module

public import StacksFrontier.AlgebraicGeometry.Stacks.LocalRingDimensionChartInvariant
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalRingDimensionChartTwoIso
public import StacksFrontier.AlgebraicGeometry.Stacks.RefinedChartClosedPointComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothChartCommonRefinement

/-!
# The chart comparison of Stacks 0DS9

This file proves that the invariant of **Stacks 0DSA** does not depend on the smooth chart, which
is the implication from condition (1) to condition (2) of **Stacks 0DS9**.

## Main results

* `AlgebraicGeometry.Stack.hasChartInvariant_refinement_iff_of_isClosed`: the invariant is
  unchanged by a smooth refinement of the chart, at a point closed in the refined chart.
* `AlgebraicGeometry.Stack.exists_affChart_hasChartInvariant_iff`: the shrinking step — a finite
  type point of a chart lies in an affine open in which it is closed, and the invariant there is
  the invariant of the original chart.
* `AlgebraicGeometry.Stack.hasChartInvariant_congr_of_isClosed`: the comparison at two charts
  with closed points over the same point of `|𝒳|`.
* `AlgebraicGeometry.Stack.hasChartInvariant_congr_of_isFiniteTypePoint`: the comparison at two
  charts with finite type points over the same point of `|𝒳|`.
* `AlgebraicGeometry.Stack.hasLocalRingDimensionAtEveryChart_of_hasLocalRingDimensionAtSomeChart`
  and
  `AlgebraicGeometry.Stack.hasLocalRingDimensionAtSomeChart_iff_hasLocalRingDimensionAtEveryChart`:
  **Stacks 0DS9**, condition (1) implies condition (2) and the equivalence of the two conditions.
* `AlgebraicGeometry.Stack.hasLocalRingDimensionAtSomeChart_unique`: the integer of Stacks 0DSA is
  determined.

## The proof, and where each step comes from

The source's proof has three geometric steps, and they appear here in this order.

1. **Shrinking.** The two points are finite type points, so each is closed in some affine open of
   its chart (`AlgebraicGeometry.Stack.exists_affChart_isClosed_of_isFiniteTypePoint`,
   **Stacks 02J2**). An affine open immersion is smooth, so this is a smooth refinement of the
   chart and the invariant is unchanged by step 3.
2. **A common refinement.** Two charts with *closed* points over the same point of `|𝒳|` admit a
   common smooth refinement with a closed point over both
   (`AlgebraicGeometry.Stack.exists_smoothChart_refining_two_smoothCharts`, which is
   **Stacks 04XH** for the nonempty fibre and **Stacks 06EF**, **Stacks 06EK** for the closed
   point of an étale chart). It delivers a 2-isomorphism of the two composites `W ⟶ 𝒳`, not an
   equality, and `AlgebraicGeometry.Stack.hasRelationLocalRingDimension_congr_twoIso` absorbs it.
3. **The refinement comparison.** Along a smooth refinement the invariant is unchanged at a point
   closed in the refined chart
   (`AlgebraicGeometry.Stack.hasRelationLocalRingDimension_refinement_diagonal_iff_of_isClosed`),
   which is the dimension content of the source's proof: the flat dimension formula of
   **Stacks 00ON** twice and the product identity of **Stacks 0B2M**, **Stacks 0A21** at a closed
   point.

Closedness is used in steps 2 and 3 and nowhere else, and it is what step 1 supplies. The source
notes that the product identity of step 3 fails at a non-closed point, so the shrinking is not a
convenience.

## Implementation notes

Everything is stated with `AlgebraicGeometry.Stack.HasChartInvariant`, which reads the invariant
for every presented self-intersection of the chart; by
`AlgebraicGeometry.Stack.hasChartInvariant_iff_exists` that is the same as reading it for some
one, so the presented self-intersections needed by the refinement comparison may be constructed
freely inside the proofs and never appear in a statement.

The 2-fibre products the refinement comparison needs — `U' ×_{h, U, t} R` and
`(U' ×_{h, U, t} R) ×_{s, U} U'` — are the canonical ones of
`AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks`, and their apexes are
representable by algebraic spaces by **Stacks 04ZP** because each cospan has a leg representable
by algebraic spaces: `sq.fst` because `R` presents its source, and `schemeStackMap h` because
both its source and target are schemes of the site.

## References

* [Stacks Project, Tag 02J2](https://stacks.math.columbia.edu/tag/02J2)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04ZP](https://stacks.math.columbia.edu/tag/04ZP)
* [Stacks Project, Tag 06EF](https://stacks.math.columbia.edu/tag/06EF)
* [Stacks Project, Tag 06EK](https://stacks.math.columbia.edu/tag/06EK)
* [Stacks Project, Tag 0DS9](https://stacks.math.columbia.edu/tag/0DS9)
* [Stacks Project, Tag 0DSA](https://stacks.math.columbia.edu/tag/0DSA)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The two base changes presenting the self-intersection of a refined chart exist, presented
by algebraic spaces.** For a presented self-intersection `(sq, R, eR)` of a chart `f : U ⟶ 𝒳` and
a refinement `h : U' ⟶ U` of the chart by a morphism of the site, there are 2-fibre product
squares `Q` for the cospan `(schemeStackMap h, t)` and `T` for the cospan
`(pr ≫ s, schemeStackMap h)` whose apexes are presented by algebraic spaces.

Each apex is representable by an algebraic space by **Stacks 04ZP**, one leg of each cospan being
representable by algebraic spaces: `sq.fst` because `R` presents its source, and
`schemeStackMap h` because both its source and target are schemes of the site. -/
theorem exists_refinedSelfIntersection_presentation {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {U U' : BigFppfOver B S hS} {f : schemeStack.{u, w} B S hS U ⟶ 𝒳} (h : U' ⟶ U)
    (sq : Bicategory.TwoCommSq f f) (R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hR : IsAlgebraicSpace B S hS R)
    (eR : StacksRepresentableCFG.EquivalenceOver sq.pt.val.val.p
      (presheafOfCategories (R ⋙ typeToCat)).p) :
    ∃ (Q : Bicategory.TwoCommSq (schemeStackMap.{u, w} B S hS h) sq.fst)
      (_hQ : Bicategory.IsTwoFibreProduct Q)
      (T : Bicategory.TwoCommSq (sq.pasteFst Q).snd (schemeStackMap.{u, w} B S hS h))
      (_hT : Bicategory.IsTwoFibreProduct T)
      (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hP : IsAlgebraicSpace B S hS P)
      (_eP : StacksRepresentableCFG.EquivalenceOver Q.pt.val.val.p
        (presheafOfCategories (P ⋙ typeToCat)).p)
      (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hW : IsAlgebraicSpace B S hS W),
      Nonempty (StacksRepresentableCFG.EquivalenceOver T.pt.val.val.p
        (presheafOfCategories (W ⋙ typeToCat)).p) := by
  obtain ⟨P, hP, ⟨eP⟩⟩ : IsRepresentableByAlgebraicSpace B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS
        (schemeStackMap.{u, w} B S hS h) sq.fst).pt.val :=
    isRepresentableByAlgebraicSpace_twoFibreProduct B S hS (schemeStack.{u, w} B S hS U).val
      (schemeStack.{u, w} B S hS U').val sq.pt.val
      (schemeStackMap.{u, w} B S hS h).hom.hom sq.fst.hom.hom
      (isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS sq.fst.hom
        ⟨R, hR, ⟨eR⟩⟩ (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U))
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U')
  obtain ⟨W, hW, heW⟩ : IsRepresentableByAlgebraicSpace B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS
        (sq.pasteFst (twoFibreProductSquareAlgebraicStacks B S hS
          (schemeStackMap.{u, w} B S hS h) sq.fst)).snd
        (schemeStackMap.{u, w} B S hS h)).pt.val :=
    isRepresentableByAlgebraicSpace_twoFibreProduct B S hS
      (schemeStack.{u, w} B S hS U).val
      (twoFibreProductSquareAlgebraicStacks B S hS
        (schemeStackMap.{u, w} B S hS h) sq.fst).pt.val
      (schemeStack.{u, w} B S hS U').val
      (sq.pasteFst (twoFibreProductSquareAlgebraicStacks B S hS
        (schemeStackMap.{u, w} B S hS h) sq.fst)).snd.hom.hom
      (schemeStackMap.{u, w} B S hS h).hom.hom
      (isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS
        (schemeStackMap.{u, w} B S hS h).hom
        (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U')
        (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U))
      ⟨P, hP, ⟨eP⟩⟩
  exact ⟨twoFibreProductSquareAlgebraicStacks B S hS (schemeStackMap.{u, w} B S hS h) sq.fst,
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks.{u, w} B S hS _ _,
    twoFibreProductSquareAlgebraicStacks B S hS _ (schemeStackMap.{u, w} B S hS h),
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks.{u, w} B S hS _ _, P, hP, eP,
    W, hW, heW⟩

/-- **The invariant of Stacks 0DSA is unchanged by a smooth refinement of the chart, at a point
closed in the refined chart.** This is step 3 of the proof of **Stacks 0DS9**, in the form the
chart comparison uses it: the invariant at the refined chart `h ≫ f` and the point `ω` of `U'`
equals the invariant at `f` and the point `h(ω)` of `U`.

The presented self-intersections of the two charts are constructed here, by
`AlgebraicGeometry.Stack.exists_presentedSelfIntersection` for `f` and
`AlgebraicGeometry.Stack.exists_refinedSelfIntersection_presentation` for the refinement, and
`AlgebraicGeometry.Stack.hasChartInvariant_iff_exists` is what lets them be chosen: the
invariant does not depend on them. -/
theorem hasChartInvariant_refinement_iff_of_isClosed {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {U U' : BigFppfOver B S hS} {f : schemeStack.{u, w} B S hS U ⟶ 𝒳} (h : U' ⟶ U)
    (hf : AlgebraicStacks.IsSmooth B S hS f)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (hhsm : Space.IsSmooth B S hS (yoneda.map h))
    (ω : Space.points B S hS (yoneda.obj U'))
    (hω : IsClosed ({Space.pointsToScheme B S hS U' ω} :
      Set ((BigFppfOver.toScheme B S hS).obj U')))
    (d : ℤ) :
    HasChartInvariant.{u, w} B S hS U' (schemeStackMap.{u, w} B S hS h ≫ f) ω d ↔
      HasChartInvariant.{u, w} B S hS U f
        (Space.pointsMap B S hS (yoneda.obj U') (yoneda.map h) ω) d := by
  obtain ⟨sq, hsq, R, hR, ⟨eR⟩⟩ := exists_presentedSelfIntersection.{u, w} B S hS U f
  obtain ⟨Q, hQ, T, hT, P, hP, eP, W, hW, ⟨eW⟩⟩ :=
    exists_refinedSelfIntersection_presentation.{u, w} B S hS h sq R hR eR
  obtain ⟨ν, hν⟩ := Space.exists_geometricRepresentative B S hS (yoneda.obj U') ω
  have hrefsq : Bicategory.IsTwoFibreProduct (refinedSelfIntersectionSquare B S hS sq Q T) :=
    isTwoFibreProduct_refinedSelfIntersectionSquare.{u, w} B S hS hsq Q hQ hT
  have key := hasRelationLocalRingDimension_refinement_diagonal_iff_of_isClosed.{u, w}
    B S hS sq Q T R P W eR eP eW hf hsq h𝒳 hhsm hQ hT hR hP hW
    (Bicategory.twoFibreProductPreHom hsq (selfIntersectionDiagonalSquare B S hS U f))
    (Bicategory.twoFibreProductPreHom hrefsq
      (selfIntersectionDiagonalSquare B S hS U' (schemeStackMap.{u, w} B S hS h ≫ f)))
    ν (by rwa [hν]) d
  rw [hν] at key
  rw [hasChartInvariant_iff_exists.{u, w} B S hS U' (schemeStackMap.{u, w} B S hS h ≫ f) ω d,
    hasChartInvariant_iff_exists.{u, w} B S hS U f
      (Space.pointsMap B S hS (yoneda.obj U') (yoneda.map h) ω) d]
  constructor
  · rintro ⟨T₀, hT₀, Q₀, hQ₀, eQ₀, δ₀, hd⟩
    refine ⟨sq, hsq, R, hR, eR, _, key.1 ?_⟩
    exact (hasRelationLocalRingDimension_transport_twoFibreProduct B S hS U'
      (schemeStackMap.{u, w} B S hS h ≫ f) T₀ (refinedSelfIntersectionSquare B S hS sq Q T)
      Q₀ W (PresheafOfCategories.sliceElementsEquivalenceOver U') eQ₀ eW hT₀ hrefsq δ₀ _ ω d).1 hd
  · rintro ⟨T₀, hT₀, Q₀, hQ₀, eQ₀, δ₀, hd⟩
    refine ⟨refinedSelfIntersectionSquare B S hS sq Q T, hrefsq, W, hW, eW, _, key.2 ?_⟩
    exact (hasRelationLocalRingDimension_transport_twoFibreProduct B S hS U f T₀ sq
      Q₀ R (PresheafOfCategories.sliceElementsEquivalenceOver U) eQ₀ eR hT₀ hsq δ₀ _
      (Space.pointsMap B S hS (yoneda.obj U') (yoneda.map h) ω) d).1 hd

/-- **Step 1 of Stacks 0DS9: shrinking the chart to one in which the point is closed.** A finite
type point `ν` of a smooth chart `g : V ⟶ 𝒳` is a closed point of an affine open `V₀ ⊆ V`, the
restricted chart `V₀ ⟶ 𝒳` is again smooth, and the invariant of Stacks 0DSA is the same there.

The affine open comes from **Stacks 02J2**
(`AlgebraicGeometry.Stack.exists_affChart_isClosed_of_isFiniteTypePoint`), its inclusion is an
affine open immersion hence smooth, and the invariant is unchanged by
`AlgebraicGeometry.Stack.hasChartInvariant_refinement_iff_of_isClosed` — whose closedness
hypothesis is about the point of the *refined* chart, which is exactly what the shrinking
produces. -/
theorem exists_affChart_hasChartInvariant_iff {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (V : BigFppfOver B S hS) (g : schemeStack.{u, w} B S hS V ⟶ 𝒳)
    (hg : AlgebraicStacks.IsSmooth B S hS g)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (ν : Space.points B S hS (yoneda.obj V))
    (hν : AlgebraicGeometry.IsFiniteTypePoint (Space.pointsToScheme B S hS V ν)) :
    ∃ (i : ((BigFppfOver.toScheme B S hS).obj V).affineOpens)
      (ω : Space.points B S hS (yoneda.obj (affChart V i))),
      IsClosed ({Space.pointsToScheme B S hS (affChart V i) ω} :
        Set ((BigFppfOver.toScheme B S hS).obj (affChart V i))) ∧
        Space.pointsMap B S hS (yoneda.obj (affChart V i))
            (yoneda.map (affChartHom V i)) ω = ν ∧
          AlgebraicStacks.IsSmooth B S hS
            (schemeStackMap.{u, w} B S hS (affChartHom V i) ≫ g) ∧
            ∀ d : ℤ, HasChartInvariant.{u, w} B S hS (affChart V i)
                (schemeStackMap.{u, w} B S hS (affChartHom V i) ≫ g) ω d ↔
              HasChartInvariant.{u, w} B S hS V g ν d := by
  obtain ⟨i, ω, hωcl, hων⟩ :=
    exists_affChart_isClosed_of_isFiniteTypePoint B S hS V ν hν
  have hjsm : Space.IsSmooth B S hS (yoneda.map (affChartHom V i)) :=
    (Space.isSmooth_yoneda_map_iff B S hS (affChartHom V i)).2 (smooth_affChartHom V i)
  refine ⟨i, ω, hωcl, hων,
    AlgebraicStacks.isSmooth_comp B S hS _ g
      (isSmooth_schemeStackMap.{u, w} B S hS (affChartHom V i) (smooth_affChartHom V i)) hg,
    fun d => ?_⟩
  rw [hasChartInvariant_refinement_iff_of_isClosed.{u, w} B S hS (affChartHom V i) hg h𝒳
    hjsm ω hωcl d, hων]

/-- **The invariant of Stacks 0DSA agrees at two smooth charts with closed points over the same
point of `|𝒳|`.** This is steps 2 and 3 of the proof of **Stacks 0DS9**: the two charts acquire a
common smooth refinement `W` with a closed point `w` over both
(`AlgebraicGeometry.Stack.exists_smoothChart_refining_two_smoothCharts`), the invariant at `W` and
`w` is the invariant at each of them by
`AlgebraicGeometry.Stack.hasChartInvariant_refinement_iff_of_isClosed`, and the two chart
1-morphisms `W ⟶ 𝒳` so compared — which are 2-isomorphic, not equal — measure the same invariant
by `AlgebraicGeometry.Stack.hasRelationLocalRingDimension_congr_twoIso`. -/
theorem hasChartInvariant_congr_of_isClosed {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (V V' : BigFppfOver B S hS) (g : schemeStack.{u, w} B S hS V ⟶ 𝒳)
    (g' : schemeStack.{u, w} B S hS V' ⟶ 𝒳)
    (hg : AlgebraicStacks.IsSmooth B S hS g) (hg' : AlgebraicStacks.IsSmooth B S hS g')
    (ν : Space.points B S hS (yoneda.obj V)) (ν' : Space.points B S hS (yoneda.obj V'))
    (hν : IsClosed ({Space.pointsToScheme B S hS V ν} :
      Set ((BigFppfOver.toScheme B S hS).obj V)))
    (hν' : IsClosed ({Space.pointsToScheme B S hS V' ν'} :
      Set ((BigFppfOver.toScheme B S hS).obj V')))
    (hsame : pointsMap B S hS (schemeFibredCategory B S hS V).val
          (schemeFibredCategory B S hS V).property 𝒳.val.property g.hom.hom
          (representedChartPointMap B S hS V ν) =
        pointsMap B S hS (schemeFibredCategory B S hS V').val
          (schemeFibredCategory B S hS V').property 𝒳.val.property g'.hom.hom
          (representedChartPointMap B S hS V' ν'))
    (d : ℤ) :
    HasChartInvariant.{u, w} B S hS V g ν d ↔ HasChartInvariant.{u, w} B S hS V' g' ν' d := by
  obtain ⟨W, p, p', w, η, hpsm, hp'sm, -, hwcl, hpw, hp'w⟩ :=
    exists_smoothChart_refining_two_smoothCharts.{u, w} B S hS V V' g g' hg hg' ν ν' hν hν' hsame
  have hleft := hasChartInvariant_refinement_iff_of_isClosed.{u, w} B S hS p hg h𝒳 hpsm w hwcl d
  have hright := hasChartInvariant_refinement_iff_of_isClosed.{u, w} B S hS p' hg' h𝒳 hp'sm w
    hwcl d
  rw [hpw] at hleft
  rw [hp'w] at hright
  refine hleft.symm.trans (Iff.trans ?_ hright)
  have key : ∀ (g₁ g₂ : schemeStack.{u, w} B S hS W ⟶ 𝒳), (g₁ ≅ g₂) →
      HasChartInvariant.{u, w} B S hS W g₁ w d → HasChartInvariant.{u, w} B S hS W g₂ w d := by
    intro g₁ g₂ η hinv T' hT' Q' hQ' eQ' δ'
    obtain ⟨T, hT, Q, -, eQ, δ, hd⟩ := (hasChartInvariant_iff_exists.{u, w} B S hS W g₁ w d).1 hinv
    exact (hasRelationLocalRingDimension_congr_twoIso.{u, w} B S hS W η T hT T' hT' Q Q'
      (PresheafOfCategories.sliceElementsEquivalenceOver W) eQ eQ' δ δ' w d).1 hd
  exact ⟨key _ _ η, key _ _ η.symm⟩

/-- **The image in `|𝒳|` of a point of a refined chart.** For `h : U' ⟶ U` a morphism of the site
and `g : U ⟶ 𝒳` a chart, the image in `|𝒳|` of a point `ω` of `U'` along the refined chart
`h ≫ g` is the image along `g` of `h(ω)`.

This is functoriality of the point map (`AlgebraicGeometry.Stack.pointsMap_comp`) together with
naturality of the identification of the points of a represented algebraic stack with the points
of its scheme (`AlgebraicGeometry.Stack.representedChartPointMap_naturality`). It is what carries
the side condition "`ν` lies over `x`" of the two conditions of Stacks 0DS9 across the shrinking
step. -/
theorem pointsMap_representedChartPointMap_schemeStackMap_comp
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {U U' : BigFppfOver B S hS} (h : U' ⟶ U)
    (g : schemeStack.{u, w} B S hS U ⟶ 𝒳) (ω : Space.points B S hS (yoneda.obj U')) :
    pointsMap B S hS (schemeFibredCategory B S hS U').val
        (schemeFibredCategory B S hS U').property 𝒳.val.property
        (schemeStackMap.{u, w} B S hS h ≫ g).hom.hom
        (representedChartPointMap B S hS U' ω) =
      pointsMap B S hS (schemeFibredCategory B S hS U).val
        (schemeFibredCategory B S hS U).property 𝒳.val.property g.hom.hom
        (representedChartPointMap B S hS U
          (Space.pointsMap B S hS (yoneda.obj U') (yoneda.map h) ω)) := by
  rw [← representedChartPointMap_naturality B S hS h ω]
  exact (pointsMap_comp B S hS (schemeFibredCategory B S hS U').val
    (schemeFibredCategory B S hS U').property
    (schemeFibredCategory B S hS U).property 𝒳.val.property
    (schemeFibredCategoryMap B S hS h).hom g.hom.hom
    (representedChartPointMap B S hS U' ω)).symm

/-- **The invariant of Stacks 0DSA agrees at two smooth charts with finite type points over the
same point of `|𝒳|`** — the chart independence of **Stacks 0DS9**, and the whole content of the
implication from its condition (1) to its condition (2).

Each chart is first shrunk to an affine open in which its point is closed
(`AlgebraicGeometry.Stack.exists_affChart_hasChartInvariant_iff`), which changes neither the
invariant nor the point of `|𝒳|` below it
(`AlgebraicGeometry.Stack.pointsMap_representedChartPointMap_schemeStackMap_comp`), and the two
shrunken charts are then compared by
`AlgebraicGeometry.Stack.hasChartInvariant_congr_of_isClosed`. -/
theorem hasChartInvariant_congr_of_isFiniteTypePoint {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (V V' : BigFppfOver B S hS) (g : schemeStack.{u, w} B S hS V ⟶ 𝒳)
    (g' : schemeStack.{u, w} B S hS V' ⟶ 𝒳)
    (hg : AlgebraicStacks.IsSmooth B S hS g) (hg' : AlgebraicStacks.IsSmooth B S hS g')
    (ν : Space.points B S hS (yoneda.obj V)) (ν' : Space.points B S hS (yoneda.obj V'))
    (hν : AlgebraicGeometry.IsFiniteTypePoint (Space.pointsToScheme B S hS V ν))
    (hν' : AlgebraicGeometry.IsFiniteTypePoint (Space.pointsToScheme B S hS V' ν'))
    (hsame : pointsMap B S hS (schemeFibredCategory B S hS V).val
          (schemeFibredCategory B S hS V).property 𝒳.val.property g.hom.hom
          (representedChartPointMap B S hS V ν) =
        pointsMap B S hS (schemeFibredCategory B S hS V').val
          (schemeFibredCategory B S hS V').property 𝒳.val.property g'.hom.hom
          (representedChartPointMap B S hS V' ν'))
    (d : ℤ) :
    HasChartInvariant.{u, w} B S hS V g ν d ↔ HasChartInvariant.{u, w} B S hS V' g' ν' d := by
  obtain ⟨i, ω, hωcl, hων, hgsm, hinv⟩ :=
    exists_affChart_hasChartInvariant_iff.{u, w} B S hS V g hg h𝒳 ν hν
  obtain ⟨i', ω', hω'cl, hω'ν, hg'sm, hinv'⟩ :=
    exists_affChart_hasChartInvariant_iff.{u, w} B S hS V' g' hg' h𝒳 ν' hν'
  refine (hinv d).symm.trans (Iff.trans ?_ (hinv' d))
  refine hasChartInvariant_congr_of_isClosed.{u, w} B S hS h𝒳 (affChart V i) (affChart V' i')
    (schemeStackMap.{u, w} B S hS (affChartHom V i) ≫ g)
    (schemeStackMap.{u, w} B S hS (affChartHom V' i') ≫ g') hgsm hg'sm ω ω' hωcl hω'cl ?_ d
  rwa [pointsMap_representedChartPointMap_schemeStackMap_comp B S hS (affChartHom V i) g ω,
    pointsMap_representedChartPointMap_schemeStackMap_comp B S hS (affChartHom V' i') g' ω',
    hων, hω'ν]

/-! ### Stacks 0DS9 -/

/-- **Stacks 0DS9, condition (1) implies condition (2).** If some scheme of the site carries a
smooth 1-morphism to a locally Noetherian algebraic stack `𝒳` and a finite type point above the
finite type point `x ∈ |𝒳|` at which the invariant of Stacks 0DSA is `d`, then every such
configuration measures it to be `d`.

This is the chart independence of the invariant,
`AlgebraicGeometry.Stack.hasChartInvariant_congr_of_isFiniteTypePoint`, read through the
restatement of the two conditions in terms of
`AlgebraicGeometry.Stack.HasChartInvariant`. -/
@[stacks 0DS9 "condition (1) implies condition (2)"]
theorem hasLocalRingDimensionAtEveryChart_of_hasLocalRingDimensionAtSomeChart
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (hx : IsFiniteTypePoint.{u, w} B S hS 𝒳 x) (d : ℤ)
    (hd : HasLocalRingDimensionAtSomeChart.{u, w} B S hS 𝒳 h𝒳 x hx d) :
    HasLocalRingDimensionAtEveryChart.{u, w} B S hS 𝒳 h𝒳 x hx d := by
  obtain ⟨V, g, ν, hgsm, hνft, hνx, hinv⟩ :=
    (hasLocalRingDimensionAtSomeChart_iff_exists_hasChartInvariant.{u, w} B S hS 𝒳 h𝒳 x hx d).1 hd
  refine (hasLocalRingDimensionAtEveryChart_iff_forall_hasChartInvariant.{u, w} B S hS 𝒳 h𝒳 x hx
    d).2 fun V' g' ν' hg'sm hν'ft hν'x => ?_
  exact (hasChartInvariant_congr_of_isFiniteTypePoint.{u, w} B S hS h𝒳 V V' g g' hgsm hg'sm
    ν ν' hνft hν'ft (hνx.trans hν'x.symm) d).1 hinv

/-- **Stacks 0DS9.** For a locally Noetherian algebraic stack `𝒳`, a finite type point
`x ∈ |𝒳|` and an integer `d`, the two conditions

1. there *exists* a scheme `U` of the site, a smooth 1-morphism `U ⟶ 𝒳` and a finite type point
   `u ∈ U` above `x` with `2 dim(𝒪_{U,ū}) - dim(𝒪_{R, e(ū)}) = d`, where `R = U ×_𝒳 U`, and
2. *every* such `U`, smooth 1-morphism and finite type point above `x` satisfies that identity

are equivalent. Condition (1) is `AlgebraicGeometry.Stack.HasLocalRingDimensionAtSomeChart`,
which is also the definition of Stacks 0DSA, and condition (2) is
`AlgebraicGeometry.Stack.HasLocalRingDimensionAtEveryChart`.

Condition (2) implies condition (1) because the range of the two quantifiers is nonempty, by
**Stacks 06FX**. The converse is the chart independence of the invariant, which is the content of
the source's proof. -/
@[stacks 0DS9 "the equivalence of the two conditions"]
theorem hasLocalRingDimensionAtSomeChart_iff_hasLocalRingDimensionAtEveryChart
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (hx : IsFiniteTypePoint.{u, w} B S hS 𝒳 x) (d : ℤ) :
    HasLocalRingDimensionAtSomeChart.{u, w} B S hS 𝒳 h𝒳 x hx d ↔
      HasLocalRingDimensionAtEveryChart.{u, w} B S hS 𝒳 h𝒳 x hx d :=
  ⟨hasLocalRingDimensionAtEveryChart_of_hasLocalRingDimensionAtSomeChart.{u, w} B S hS 𝒳 h𝒳 x hx d,
    hasLocalRingDimensionAtSomeChart_of_hasLocalRingDimensionAtEveryChart.{u, w} B S hS 𝒳 h𝒳 x hx d⟩

/-- **The dimension of the local ring of Stacks 0DSA is unique.** At a finite type point of a
locally Noetherian algebraic stack at most one integer satisfies the defining condition.

This is what chart independence buys: the two configurations witnessing the two integers measure
the invariant at a single configuration by
`AlgebraicGeometry.Stack.hasChartInvariant_congr_of_isFiniteTypePoint`, and there the invariant
determines the integer by
`AlgebraicGeometry.Stack.hasRelationLocalRingDimension_unique`. Together with
`AlgebraicGeometry.Stack.exists_hasLocalRingDimensionAtSomeChart` it makes the relation of
Stacks 0DSA single-valued, and satisfied by an integer at every point carrying a smooth chart
with a finite type point above it. -/
theorem hasLocalRingDimensionAtSomeChart_unique (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (hx : IsFiniteTypePoint.{u, w} B S hS 𝒳 x) {d e : ℤ}
    (hd : HasLocalRingDimensionAtSomeChart.{u, w} B S hS 𝒳 h𝒳 x hx d)
    (he : HasLocalRingDimensionAtSomeChart.{u, w} B S hS 𝒳 h𝒳 x hx e) : d = e := by
  obtain ⟨V, g, ν, hgsm, hνft, hνx, hinvd⟩ :=
    (hasLocalRingDimensionAtSomeChart_iff_exists_hasChartInvariant.{u, w} B S hS 𝒳 h𝒳 x hx d).1 hd
  obtain ⟨V', g', ν', hg'sm, hν'ft, hν'x, hinve⟩ :=
    (hasLocalRingDimensionAtSomeChart_iff_exists_hasChartInvariant.{u, w} B S hS 𝒳 h𝒳 x hx e).1 he
  have hinve' : HasChartInvariant.{u, w} B S hS V g ν e :=
    (hasChartInvariant_congr_of_isFiniteTypePoint.{u, w} B S hS h𝒳 V V' g g' hgsm hg'sm
      ν ν' hνft hν'ft (hνx.trans hν'x.symm) e).2 hinve
  obtain ⟨T, hT, Q, hQ, ⟨eQ⟩⟩ := exists_presentedSelfIntersection.{u, w} B S hS V g
  set δ := Bicategory.twoFibreProductPreHom hT (selfIntersectionDiagonalSquare B S hS V g)
  exact hasRelationLocalRingDimension_unique B S hS V g T Q
    (PresheafOfCategories.sliceElementsEquivalenceOver V) eQ
    (Space.pointsMap B S hS (yoneda.obj V)
      (selfIntersectionDiagonalMap B S hS V g T Q
        (PresheafOfCategories.sliceElementsEquivalenceOver V) eQ δ) ν)
    (hinvd T hT Q hQ eQ δ) (hinve' T hT Q hQ eQ δ)

end AlgebraicGeometry.Stack

end
