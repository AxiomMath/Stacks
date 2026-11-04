module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopologyRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySchemeMap
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPoints

/-!
# A scheme over `S` as an algebraic stack: its points, and quasi-compactness of its morphisms

A scheme over `S` belonging to the chosen big fppf site represents a category fibred in
groupoids, `AlgebraicGeometry.Stack.schemeFibredCategory`, which is an algebraic stack. This
module records the object and the 1-morphism of the 2-category of algebraic stacks (Stacks 03YP)
that it gives, and the two transfers between the scheme and the stack that a statement about
represented stacks needs:

* the topological space of points of Stacks 04XL of such a stack **is** the topological space of
  the scheme, naturally in the scheme; and
* a morphism of the site whose morphism of representable algebraic spaces is quasi-compact
  induces a 1-morphism which is quasi-compact in the sense of Stacks 050U.

## Main definitions

* `AlgebraicGeometry.Stack.schemeAlgebraicStack`: a scheme over `S` in the site, as an object of
  the 2-category of algebraic stacks.
* `AlgebraicGeometry.Stack.schemeAlgebraicStackMap`: a morphism of the site, as a 1-morphism of
  algebraic stacks.
* `AlgebraicGeometry.Stack.pointsHomeomorphScheme`: the points of a represented algebraic stack,
  with the topology of Stacks 04XL, as a homeomorphism onto the underlying scheme.

## Main results

* `AlgebraicGeometry.Stack.pointsHomeomorphScheme_naturality`: that homeomorphism carries the map
  on points induced by `AlgebraicGeometry.Stack.schemeFibredCategoryMap` to the map on points of
  the underlying schemes.
* `AlgebraicGeometry.Stack.isQuasiCompactMorphism_schemeAlgebraicStackMap`: the 1-morphism of
  algebraic stacks induced by a morphism of the site is quasi-compact in the sense of Stacks 050U
  as soon as the induced morphism of representable algebraic spaces is quasi-compact.

## Implementation notes

The homeomorphism is the composite of two homeomorphisms: the point space of a stack represented by
an algebraic space is the point space of that space
(`AlgebraicGeometry.Stack.isHomeomorph_spacePointMap_representing`, for the chart of the
representing equivalence), and on a represented presheaf the point space is the scheme
(`AlgebraicGeometry.Space.schemePointsHomeomorph`, Stacks 03BX). The representing equivalence for
`AlgebraicGeometry.Stack.schemeFibredCategory` is
`CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver`, the slice over a scheme read
as the category of elements of the presheaf it represents — the same chart through which
`AlgebraicGeometry.Stack.representingMap_schemeFibredCategoryMap` computes the induced morphism
of representing presheaves as `yoneda.map`. Naturality is therefore the composite of that
computation with `AlgebraicGeometry.Space.pointsToScheme_pointsMap`, after the point is
written as a chart point — which is possible because the chart is bijective on points.

Quasi-compactness goes the other way round: the relative property of Stacks 03YK is transported
to the induced 1-morphism by `AlgebraicGeometry.Stack.hasRelativeProperty_schemeFibredCategoryMap`
at `AlgebraicGeometry.Space.quasiCompactProperty`, and Stacks 050T
(`AlgebraicGeometry.Stack.isQuasiCompact_iff_baseChange_quasiCompact`) converts the Stacks 04XB
relative notion into the Stacks 050U one. The locality-at-target instance that naming the relative
property requires is `AlgebraicGeometry.Space.isQuasiCompact_isLocalAtTarget_fppf`, supplied
locally because it is a theorem rather than an instance; the conclusion
`AlgebraicGeometry.Stack.IsQuasiCompact` is the quantifier of Stacks 03YK written out and carries
no instance at all, so nothing of that supply survives into the statement.

No declaration here carries a `@[stacks]` attribute: the two homeomorphisms, Stacks 050T and the
relative property are already registered where they are proved, and neither transfer is an
assertion of the Stacks Project in its own right.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 050T](https://stacks.math.columbia.edu/tag/050T)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A scheme over `S` belonging to the chosen big fppf site, as an object of the 2-category of
algebraic stacks over `S` (**Stacks 03YP**): the category fibred in groupoids it represents,
together with the algebraicity witness
`AlgebraicGeometry.Stack.isAlgebraicStack_schemeFibredCategory`. -/
noncomputable def schemeAlgebraicStack (X : BigFppfOver B S hS) :
    AlgebraicStacks.{u, w} B S hS :=
  ⟨schemeFibredCategory B S hS X, isAlgebraicStack_schemeFibredCategory B S hS X⟩

/-- A morphism of the big fppf category of `S`, as a 1-morphism of the 2-category of algebraic
stacks over `S`: the 1-morphism `AlgebraicGeometry.Stack.schemeFibredCategoryMap` of represented
categories fibred in groupoids, read in the full sub-2-category of algebraic stacks. -/
noncomputable def schemeAlgebraicStackMap {U V : BigFppfOver B S hS} (g : U ⟶ V) :
    schemeAlgebraicStack.{u, w} B S hS U ⟶ schemeAlgebraicStack.{u, w} B S hS V :=
  Bicategory.InducedBicategory.mkHom (schemeFibredCategoryMap B S hS g)

/-- The 1-morphism of algebraic stacks induced by a morphism of the site is the 1-morphism of
categories fibred in groupoids induced by it. -/
theorem schemeAlgebraicStackMap_hom {U V : BigFppfOver B S hS} (g : U ⟶ V) :
    (schemeAlgebraicStackMap.{u, w} B S hS g).hom = schemeFibredCategoryMap B S hS g :=
  rfl

/-! ### The point space of a represented algebraic stack -/

/-- The chart of the representing equivalence of a represented category fibred in groupoids: the
slice over a scheme, read as the category of elements of the presheaf it represents. -/
noncomputable abbrev representedChart (U : BigFppfOver B S hS) :
    StacksRepresentableCFG.EquivalenceOver
      (schemeFibredCategory B S hS U).val.p
      (presheafOfCategories (yoneda.obj U ⋙ typeToCat)).p :=
  CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver U

/-- The canonical map on points of the chart of a represented category fibred in groupoids. -/
noncomputable def representedChartPointMap (U : BigFppfOver B S hS) :
    Space.points B S hS (yoneda.obj U) →
      points B S hS (schemeFibredCategory B S hS U).val
        (schemeFibredCategory B S hS U).property :=
  spacePointMap B S hS (yoneda.obj U) (schemeFibredCategory B S hS U)
    (representingEquivalence B S hS (yoneda.obj U) (schemeFibredCategory B S hS U)
      (representedChart B S hS U)).functor

/-- The canonical map on points of the chart of a represented category fibred in groupoids is
bijective. -/
theorem bijective_representedChartPointMap (U : BigFppfOver B S hS) :
    Function.Bijective (representedChartPointMap B S hS U) :=
  bijective_spacePointMap_representing B S hS (yoneda.obj U)
    (schemeFibredCategory B S hS U) (representedChart B S hS U)

/-- **The points of a represented algebraic stack are the points of its scheme.** The topological
space of points of Stacks 04XL of the category fibred in groupoids represented by a scheme `U`
over `S` in the site is homeomorphic to the underlying topological space of `U`.

This is the composite of two homeomorphisms: the chart of the representing equivalence
is a homeomorphism from the point space of Stacks 03BX of the representable algebraic space, and
that point space is the scheme. -/
noncomputable def pointsHomeomorphScheme (U : BigFppfOver B S hS) :
    letI := pointTopology B S hS (schemeFibredCategory B S hS U)
    @Homeomorph
      (points B S hS (schemeFibredCategory B S hS U).val
        (schemeFibredCategory B S hS U).property)
      ((BigFppfOver.toScheme B S hS).obj U) _ _ :=
  letI := pointTopology B S hS (schemeFibredCategory B S hS U)
  (((isHomeomorph_spacePointMap_representing B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U) (schemeFibredCategory B S hS U)
      (representedChart B S hS U)).homeomorph _).symm.trans
    (Space.schemePointsHomeomorph B S hS U))

/-- On a chart point the homeomorphism is the point map of Stacks 03BX, clause (1). -/
theorem pointsHomeomorphScheme_representedChartPointMap (U : BigFppfOver B S hS)
    (x : Space.points B S hS (yoneda.obj U)) :
    pointsHomeomorphScheme B S hS U (representedChartPointMap B S hS U x) =
      Space.pointsToScheme B S hS U x := by
  let _ := pointTopology B S hS (schemeFibredCategory B S hS U)
  exact congrArg (Space.schemePointsHomeomorph B S hS U)
    (Homeomorph.symm_apply_apply
      ((isHomeomorph_spacePointMap_representing B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U) (schemeFibredCategory B S hS U)
        (representedChart B S hS U)).homeomorph _) x)

/-- **Naturality of the chart point map in the scheme.** The map on points of the 1-morphism of
represented categories fibred in groupoids induced by a morphism of the site acts on chart points
as the map on points of the induced morphism of representable algebraic spaces.

This is `AlgebraicGeometry.Stack.spacePointMap_representing_naturality` with the induced morphism
of representing presheaves computed by
`AlgebraicGeometry.Stack.representingMap_schemeFibredCategoryMap`. -/
theorem representedChartPointMap_naturality {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (x : Space.points B S hS (yoneda.obj U)) :
    pointsMap B S hS (schemeFibredCategory B S hS U).val
        (schemeFibredCategory B S hS U).property
        (schemeFibredCategory B S hS V).property
        (schemeFibredCategoryMap B S hS g).hom (representedChartPointMap B S hS U x) =
      representedChartPointMap B S hS V
        (Space.pointsMap B S hS (yoneda.obj U) (yoneda.map g) x) := by
  have hnat := spacePointMap_representing_naturality B S hS (yoneda.obj U) (yoneda.obj V)
    (schemeFibredCategory B S hS U) (schemeFibredCategory B S hS V)
    (representedChart B S hS U) (representedChart B S hS V)
    (schemeFibredCategoryMap B S hS g) x
  rw [representingMap_schemeFibredCategoryMap] at hnat
  exact hnat.symm

/-- **The identification of the points of a represented algebraic stack with its scheme is
natural.** It carries the map on points induced by
`AlgebraicGeometry.Stack.schemeFibredCategoryMap` at a morphism `g` of the site to the map on
points of the underlying schemes induced by `g`. -/
theorem pointsHomeomorphScheme_naturality {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (z : points B S hS (schemeFibredCategory B S hS U).val
      (schemeFibredCategory B S hS U).property) :
    pointsHomeomorphScheme B S hS V
        (pointsMap B S hS (schemeFibredCategory B S hS U).val
          (schemeFibredCategory B S hS U).property
          (schemeFibredCategory B S hS V).property
          (schemeFibredCategoryMap B S hS g).hom z) =
      (BigFppfOver.toScheme B S hS).map g (pointsHomeomorphScheme B S hS U z) := by
  obtain ⟨x, rfl⟩ := (bijective_representedChartPointMap B S hS U).2 z
  rw [representedChartPointMap_naturality, pointsHomeomorphScheme_representedChartPointMap,
    pointsHomeomorphScheme_representedChartPointMap, Space.pointsToScheme_pointsMap]

/-! ### Quasi-compactness of a 1-morphism induced by a morphism of the site -/

/-- **A morphism of the site with quasi-compact morphism of representable algebraic spaces induces
a 1-morphism which is quasi-compact in the sense of Stacks 04XB.** This is the relative property
of Stacks 03YK at `AlgebraicGeometry.Space.quasiCompactProperty`, transported to the induced
1-morphism by `AlgebraicGeometry.Stack.hasRelativeProperty_schemeFibredCategoryMap`. -/
theorem isQuasiCompact_schemeAlgebraicStackMap {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (hg : Space.IsQuasiCompact B S hS (yoneda.map g)) :
    IsQuasiCompact B S hS (schemeAlgebraicStackMap.{u, w} B S hS g).hom :=
  let _ : (Space.quasiCompactProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isQuasiCompact_isLocalAtTarget_fppf B S hS
  hasRelativeProperty_schemeFibredCategoryMap.{u, u} B S hS
    (Space.quasiCompactProperty B S hS) g hg

/-- **A quasi-compact morphism of schemes of the site is a quasi-compact 1-morphism of the
associated algebraic stacks.** If the morphism `h_U ⟶ h_V` of representable algebraic spaces
attached to `g : U ⟶ V` is quasi-compact (**Stacks 03HE**), then the induced 1-morphism of
algebraic stacks is quasi-compact in the sense of **Stacks 050U**: every base change of it by a
quasi-compact algebraic stack is a quasi-compact algebraic stack.

The passage between the two notions of quasi-compactness is **Stacks 050T**, available because the
induced 1-morphism is representable by algebraic spaces — both its source and its target are
represented. -/
theorem isQuasiCompactMorphism_schemeAlgebraicStackMap {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (hg : Space.IsQuasiCompact B S hS (yoneda.map g)) :
    IsQuasiCompactMorphism.{u, w} B S hS (schemeAlgebraicStackMap.{u, w} B S hS g) :=
  (isQuasiCompact_iff_baseChange_quasiCompact B S hS
    (schemeAlgebraicStackMap.{u, w} B S hS g)
    (isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS g)).1
    (isQuasiCompact_schemeAlgebraicStackMap.{u, w} B S hS g hg)

end AlgebraicGeometry.Stack

end
