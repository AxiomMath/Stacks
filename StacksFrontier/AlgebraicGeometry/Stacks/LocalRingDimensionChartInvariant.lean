module

public import StacksFrontier.AlgebraicGeometry.Stacks.LocalRingDimensionChartIndependence
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalRingDimensionSquareIndependence

/-!
# The invariant of Stacks 0DSA at a chart, read independently of the presentation

Conditions (1) and (2) of **Stacks 0DS9** both quantify over the presented self-intersection of
the chart: the 2-fibre product square `T` for the cospan `(g, g)`, the algebraic space `Q`
presenting its apex with its comparison equivalence `eQ`, and the mediating morphism `δ` giving
the diagonal. The invariant does not depend on any of it
(`AlgebraicGeometry.Stack.hasRelationLocalRingDimension_transport_twoFibreProduct`), and a
presentation always exists
(`AlgebraicGeometry.Stack.exists_presentedSelfIntersection`), so over that data the existential
and the universal readings agree.

This file records the universal reading as a predicate on the chart and the point alone, and the
agreement. Both conditions of Stacks 0DS9 are then statements about it, and the chart comparison
of the tag can be proved without the presentation data being mentioned.

## Main definitions

* `AlgebraicGeometry.Stack.HasChartInvariant`: `2 dim(𝒪_{V,ν̄}) - dim(𝒪_{R,e(ν̄)}) = d` read at a
  smooth chart `g : V ⟶ 𝒳` and a point `ν` of `V`, for every presented self-intersection.

## Main results

* `AlgebraicGeometry.Stack.hasChartInvariant_iff_exists`: the universal and the existential
  reading of the presentation data agree.
* `AlgebraicGeometry.Stack.hasLocalRingDimensionAtSomeChart_iff_exists_hasChartInvariant` and
  `AlgebraicGeometry.Stack.hasLocalRingDimensionAtEveryChart_iff_forall_hasChartInvariant`:
  conditions (1) and (2) of Stacks 0DS9, with the presentation quantifier discharged.

## Implementation notes

The comparison equivalence of the chart is **not** quantified over: it is fixed to the canonical
`CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver`, exactly as in the two
conditions of the tag and for the same reason — the module documentation of
`StacksFrontier/AlgebraicGeometry/Stacks/LocalRingDimensionChartIndependence.lean` records the
counterexample which makes a quantified form say something else.

Smoothness of the chart is a hypothesis of the agreement lemma and not of the predicate: it is
what `AlgebraicGeometry.Stack.exists_presentedSelfIntersection` needs, through representability
of the diagonal of an algebraic stack, and it is carried by both conditions of the tag anyway.

## References

* [Stacks Project, Tag 0DS9](https://stacks.math.columbia.edu/tag/0DS9)
* [Stacks Project, Tag 0DSA](https://stacks.math.columbia.edu/tag/0DSA)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The invariant of Stacks 0DSA at a chart and a point of it.** For every presented
self-intersection of the smooth chart `g : V ⟶ 𝒳` — a 2-fibre product square `T` for the cospan
`(g, g)`, an algebraic space `Q` presenting its apex through `eQ`, and a mediating morphism `δ`
giving the diagonal — the invariant `2 dim(𝒪_{V,ν̄}) - dim(𝒪_{Q, e(ν̄)})` read at the diagonal
image of `ν` is `d`.

Quantifying universally loses nothing and assumes nothing: the invariant is independent of all of
that data and a presentation exists, which is
`AlgebraicGeometry.Stack.hasChartInvariant_iff_exists`. -/
def HasChartInvariant {𝒳 : AlgebraicStacks.{u, w} B S hS} (V : BigFppfOver B S hS)
    (g : schemeStack.{u, w} B S hS V ⟶ 𝒳) (ν : Space.points B S hS (yoneda.obj V)) (d : ℤ) :
    Prop :=
  ∀ (T : Bicategory.TwoCommSq g g) (_hT : Bicategory.IsTwoFibreProduct T)
      (Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hQ : IsAlgebraicSpace B S hS Q)
      (eQ : StacksRepresentableCFG.EquivalenceOver
        T.pt.val.val.p (presheafOfCategories (Q ⋙ typeToCat)).p)
      (δ : Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS V g) T),
    HasRelationLocalRingDimension B S hS V g T Q
      (PresheafOfCategories.sliceElementsEquivalenceOver V) eQ
      (Space.pointsMap B S hS (yoneda.obj V)
        (selfIntersectionDiagonalMap B S hS V g T Q
          (PresheafOfCategories.sliceElementsEquivalenceOver V) eQ δ) ν) d

/-- **The presentation quantifier of Stacks 0DS9 may be read either way.** At a smooth chart of
an algebraic stack, some presented self-intersection measures the invariant of Stacks 0DSA to be
`d` exactly when every one does.

Forward is `AlgebraicGeometry.Stack.hasRelationLocalRingDimension_transport_twoFibreProduct`, the
independence of the invariant from the 2-fibre product square, the presenting algebraic space,
its comparison equivalence and the mediating morphism. Backward is
`AlgebraicGeometry.Stack.exists_presentedSelfIntersection`, that a presented self-intersection
exists at all — which is where smoothness and algebraicity of `𝒳` enter. -/
theorem hasChartInvariant_iff_exists {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (V : BigFppfOver B S hS) (g : schemeStack.{u, w} B S hS V ⟶ 𝒳)
    (ν : Space.points B S hS (yoneda.obj V)) (d : ℤ) :
    HasChartInvariant.{u, w} B S hS V g ν d ↔
      ∃ (T : Bicategory.TwoCommSq g g) (_hT : Bicategory.IsTwoFibreProduct T)
        (Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hQ : IsAlgebraicSpace B S hS Q)
        (eQ : StacksRepresentableCFG.EquivalenceOver
          T.pt.val.val.p (presheafOfCategories (Q ⋙ typeToCat)).p)
        (δ : Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS V g) T),
        HasRelationLocalRingDimension B S hS V g T Q
          (PresheafOfCategories.sliceElementsEquivalenceOver V) eQ
          (Space.pointsMap B S hS (yoneda.obj V)
            (selfIntersectionDiagonalMap B S hS V g T Q
              (PresheafOfCategories.sliceElementsEquivalenceOver V) eQ δ) ν) d := by
  constructor
  · intro hall
    obtain ⟨T, hT, Q, hQ, ⟨eQ⟩⟩ := exists_presentedSelfIntersection.{u, w} B S hS V g
    exact ⟨T, hT, Q, hQ, eQ,
      Bicategory.twoFibreProductPreHom hT (selfIntersectionDiagonalSquare B S hS V g),
      hall T hT Q hQ eQ _⟩
  · rintro ⟨T, hT, Q, hQ, eQ, δ, hd⟩ T' hT' Q' hQ' eQ' δ'
    exact (hasRelationLocalRingDimension_transport_twoFibreProduct B S hS V g T T' Q Q'
      (PresheafOfCategories.sliceElementsEquivalenceOver V) eQ eQ' hT hT' δ δ' ν d).1 hd

/-- **Condition (1) of Stacks 0DS9 in terms of the invariant at a chart.** The dimension of the
local ring of Stacks 0DSA is `d` exactly when some scheme of the site carries a smooth
1-morphism to `𝒳` and a finite type point above `x` at which the invariant is `d`. -/
theorem hasLocalRingDimensionAtSomeChart_iff_exists_hasChartInvariant
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (hx : IsFiniteTypePoint.{u, w} B S hS 𝒳 x) (d : ℤ) :
    HasLocalRingDimensionAtSomeChart.{u, w} B S hS 𝒳 h𝒳 x hx d ↔
      ∃ (V : BigFppfOver B S hS) (g : schemeStack.{u, w} B S hS V ⟶ 𝒳)
        (ν : Space.points B S hS (yoneda.obj V)),
        AlgebraicStacks.IsSmooth B S hS g ∧
          AlgebraicGeometry.IsFiniteTypePoint (Space.pointsToScheme B S hS V ν) ∧
            pointsMap B S hS (schemeFibredCategory B S hS V).val
                (schemeFibredCategory B S hS V).property 𝒳.val.property g.hom.hom
                (representedChartPointMap B S hS V ν) = x ∧
              HasChartInvariant.{u, w} B S hS V g ν d := by
  constructor
  · rintro ⟨V, g, T, hT, Q, hQ, eQ, δ, ν, hgsm, hνft, hνx, hd⟩
    exact ⟨V, g, ν, hgsm, hνft, hνx,
      (hasChartInvariant_iff_exists.{u, w} B S hS V g ν d).2 ⟨T, hT, Q, hQ, eQ, δ, hd⟩⟩
  · rintro ⟨V, g, ν, hgsm, hνft, hνx, hinv⟩
    obtain ⟨T, hT, Q, hQ, eQ, δ, hd⟩ := (hasChartInvariant_iff_exists.{u, w} B S hS V g ν d).1 hinv
    exact ⟨V, g, T, hT, Q, hQ, eQ, δ, ν, hgsm, hνft, hνx, hd⟩

/-- **Condition (2) of Stacks 0DS9 in terms of the invariant at a chart.** Every smooth chart
carrying a finite type point above `x` measures the invariant to be `d`. -/
theorem hasLocalRingDimensionAtEveryChart_iff_forall_hasChartInvariant
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (hx : IsFiniteTypePoint.{u, w} B S hS 𝒳 x) (d : ℤ) :
    HasLocalRingDimensionAtEveryChart.{u, w} B S hS 𝒳 h𝒳 x hx d ↔
      ∀ (V : BigFppfOver B S hS) (g : schemeStack.{u, w} B S hS V ⟶ 𝒳)
        (ν : Space.points B S hS (yoneda.obj V)),
        AlgebraicStacks.IsSmooth B S hS g →
          AlgebraicGeometry.IsFiniteTypePoint (Space.pointsToScheme B S hS V ν) →
            pointsMap B S hS (schemeFibredCategory B S hS V).val
                (schemeFibredCategory B S hS V).property 𝒳.val.property g.hom.hom
                (representedChartPointMap B S hS V ν) = x →
              HasChartInvariant.{u, w} B S hS V g ν d := by
  constructor
  · intro hall V g ν hgsm hνft hνx T hT Q hQ eQ δ
    exact hall V g T hT Q hQ eQ δ ν hgsm hνft hνx
  · intro hall V g T hT Q hQ eQ δ ν hgsm hνft hνx
    exact hall V g ν hgsm hνft hνx T hT Q hQ eQ δ

end AlgebraicGeometry.Stack

end
