module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentIngredients
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRepresented

/-!
# A chart by a scheme of the site, read as a chart by the algebraic space it represents

A scheme `U` of the big fppf site gives rise to two algebraic stacks which are equivalent but not
equal: the slice of the site over `U`, `AlgebraicGeometry.Stack.schemeStack`, and the category of
elements of the presheaf `h_U` it represents,
`AlgebraicGeometry.Stack.algebraicSpaceStack (yoneda.obj U)`. The chart that **Stacks 06FX**
produces at a finite type point is a 1-morphism out of the first, while the slicing lemma
**Stacks 06MD** slices a 1-morphism out of an algebraic *space*, hence out of the second. This
file crosses between them.

The comparison is the backward 1-morphism of the representing equivalence of
`CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver`, which identifies the slice of
the site over `U` with the category of elements of `h_U`. The comparison is smooth and
surjective on points, so a smooth chart stays smooth and its image on points is unchanged.

## Main definitions

* `AlgebraicGeometry.Stack.algebraicSpaceStackOfSchemeStack`: the comparison 1-morphism
  `algebraicSpaceStack (yoneda.obj U) ⟶ schemeStack U`.
* `AlgebraicGeometry.Stack.algebraicSpaceStackChart`: a 1-morphism out of `schemeStack U`, read
  as a 1-morphism out of `algebraicSpaceStack (yoneda.obj U)`.

## Main results

* `AlgebraicGeometry.Stack.isSmooth_algebraicSpaceStackOfSchemeStack`: the comparison is smooth
  (**Stacks 075U**), being relatively smooth in the sense of **Stacks 04XB** with representable
  source and target.
* `AlgebraicGeometry.Stack.isSmooth_algebraicSpaceStackChart`: a smooth chart stays smooth after
  crossing.
* `AlgebraicGeometry.Stack.range_pointsMap_algebraicSpaceStackChart`: the image on points is
  unchanged, so a prescribed point of `|𝒳|` in the image of the chart is still in the image of
  the crossed chart.
* `AlgebraicGeometry.Stack.isSurjective_algebraicSpaceStackChart`: surjectivity on points
  likewise survives.

## Implementation notes

The comparison 1-morphism is `AlgebraicGeometry.Stack.equivalenceOverInvMap` at the equivalence
`CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver`, so its three properties are
the three results of `StacksFrontier/AlgebraicGeometry/Stacks/SmoothLocalMorphismRepresented.lean`
about that 1-morphism: representability by algebraic spaces (**Stacks 02ZZ**), relative
smoothness (**Stacks 04XB**, the morphism of representing presheaves being the identity of `h_U`)
and surjectivity on objects (**Stacks 06D4**, with no field extension). Smoothness in the sense
of **Stacks 075U** is then the identity-diagram criterion
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_of_isRelativelySmooth`, and composition
is **Stacks 075V**.

The chart is *pre*composed with the comparison, so no 2-isomorphism has to be transported and
the crossed chart is a composite on the nose.

## References

* [Stacks Project, Tag 02ZZ](https://stacks.math.columbia.edu/tag/02ZZ)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 06D4](https://stacks.math.columbia.edu/tag/06D4)
* [Stacks Project, Tag 06FX](https://stacks.math.columbia.edu/tag/06FX)
* [Stacks Project, Tag 06MD](https://stacks.math.columbia.edu/tag/06MD)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
* [Stacks Project, Tag 075V](https://stacks.math.columbia.edu/tag/075V)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The slice of the site over a scheme `U`, compared with the stack of the algebraic space
`h_U`.** The backward 1-morphism of the representing equivalence
`CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver`. -/
abbrev algebraicSpaceStackOfSchemeStack (U : BigFppfOver B S hS) :
    algebraicSpaceStack.{u, w} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) ⟶
      schemeStack.{u, w} B S hS U :=
  Bicategory.InducedBicategory.mkHom
    (equivalenceOverInvMap B S hS (yoneda.obj U)
      (PresheafOfCategories.sliceElementsEquivalenceOver.{u} U))

/-- **The comparison is smooth.** It is relatively smooth in the sense of **Stacks 04XB** by
`AlgebraicGeometry.Stack.isRelativelySmooth_equivalenceOverInvMap`, the morphism of representing
presheaves it induces being the identity of `h_U`, and the identity-diagram criterion
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_of_isRelativelySmooth` turns that into
smoothness in the sense of **Stacks 075U**. -/
theorem isSmooth_algebraicSpaceStackOfSchemeStack (U : BigFppfOver B S hS) :
    AlgebraicStacks.IsSmooth B S hS (algebraicSpaceStackOfSchemeStack.{u, w} B S hS U) := by
  exact hasPropertyOnSomeSmoothDiagram_of_isRelativelySmooth B S hS _ _
    (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (isRelativelySmooth_equivalenceOverInvMap B S hS
      (𝒳 := (schemeStack.{u, w} B S hS U).val) (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)
      (PresheafOfCategories.sliceElementsEquivalenceOver.{u} U))
    (Space.isSmooth_id B S hS (isAlgebraicSpace_yoneda B S hS U))

/-- **The comparison is surjective on points.** It is surjective on objects in the sense of
**Stacks 06D4** by
`AlgebraicGeometry.Stack.isSurjectiveOnObjects_equivalenceOverInvMap`, and surjectivity on
objects gives surjectivity on points. -/
theorem pointsMap_surjective_algebraicSpaceStackOfSchemeStack (U : BigFppfOver B S hS) :
    Function.Surjective
      (AlgebraicStacks.pointsMap B S hS (algebraicSpaceStackOfSchemeStack.{u, w} B S hS U)) :=
  pointsMap_surjective_of_isSurjectiveOnObjects B S hS
    (algebraicSpaceStackOfSchemeStack.{u, w} B S hS U)
    (isSurjectiveOnObjects_equivalenceOverInvMap B S hS
      (𝒳 := (schemeStack.{u, w} B S hS U).val) (yoneda.obj U)
      (PresheafOfCategories.sliceElementsEquivalenceOver.{u} U))

/-- **A 1-morphism out of a scheme of the site, read as a 1-morphism out of the algebraic space
that scheme represents.** -/
abbrev algebraicSpaceStackChart {𝒳 : AlgebraicStacks.{u, w} B S hS} (U : BigFppfOver B S hS)
    (a : schemeStack.{u, w} B S hS U ⟶ 𝒳) :
    algebraicSpaceStack.{u, w} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) ⟶ 𝒳 :=
  algebraicSpaceStackOfSchemeStack.{u, w} B S hS U ≫ a

/-- **A smooth chart by a scheme of the site stays smooth when read as a chart by the algebraic
space that scheme represents**, the comparison being smooth and smoothness being stable under
composition (**Stacks 075V**). -/
theorem isSmooth_algebraicSpaceStackChart {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (U : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (ha : AlgebraicStacks.IsSmooth B S hS a) :
    AlgebraicStacks.IsSmooth B S hS (algebraicSpaceStackChart.{u, w} B S hS U a) :=
  AlgebraicStacks.isSmooth_comp B S hS _ a
    (isSmooth_algebraicSpaceStackOfSchemeStack.{u, w} B S hS U) ha

/-- **Crossing does not change the image of a chart on points.** The comparison is surjective on
points, so the image of the composite is the image of the chart. In particular a prescribed point
of `|𝒳|` in the image of the chart of **Stacks 06FX** is still in the image of the crossed
chart. -/
theorem range_pointsMap_algebraicSpaceStackChart {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (U : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS U ⟶ 𝒳) :
    Set.range (AlgebraicStacks.pointsMap B S hS
        (algebraicSpaceStackChart.{u, w} B S hS U a)) =
      Set.range (AlgebraicStacks.pointsMap B S hS a) := by
  rw [AlgebraicStacks.pointsMap_comp]
  exact (pointsMap_surjective_algebraicSpaceStackOfSchemeStack.{u, w} B S hS U).range_comp _

/-- **A chart surjective on points stays surjective when read as a chart by the algebraic space
the scheme represents**, the comparison being surjective on points. -/
theorem isSurjective_algebraicSpaceStackChart {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (U : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (ha : IsSurjective B S hS a) :
    IsSurjective B S hS (algebraicSpaceStackChart.{u, w} B S hS U a) := by
  rw [IsSurjective, AlgebraicStacks.pointsMap_comp]
  exact ha.comp (pointsMap_surjective_algebraicSpaceStackOfSchemeStack.{u, w} B S hS U)

end AlgebraicGeometry.Stack

end
