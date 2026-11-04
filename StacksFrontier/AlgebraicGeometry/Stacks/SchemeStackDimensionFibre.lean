module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubsetSeparationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionAtFiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionStackSchemeFibre
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionStackTwoIso
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRepresented

/-!
# The dimension of the algebraic stack of a scheme of the site, and of its fibres

A scheme `U` of the big fppf category of `S` has an algebraic stack
`AlgebraicGeometry.Stack.schemeStack`, and a 1-morphism between two such is 2-isomorphic to the
one induced by a morphism of the site (`AlgebraicGeometry.Stack.schemeStackMapIso`). This file
computes the two dimensions of **Stacks 0AFN** and **Stacks 0DRL** on those objects in terms of
the schemes themselves:

* the dimension of `schemeStack U` at a point is the Krull dimension of `U` there, and
* the relative dimension of `h : schemeStack A ⟶ schemeStack V` at a point is the Krull dimension
  at that point of the scheme theoretic fibre of the underlying morphism of schemes.

The second is the counterpart, for the slice model of a scheme as an algebraic stack, of
`AlgebraicGeometry.Stack.relativeStackDimensionAt_algebraicSpaceStackMap_yoneda_map_eq`, which is
stated for the category-of-elements model. Both are needed to transport a dimension formula
proved for a morphism of schemes —
`AlgebraicGeometry.exists_isOpen_nonempty_topologicalKrullDimAt_eq_add_fiber_of_irreducibleSpace`,
the scheme-level step of **Stacks 0DS4** — to the smooth chart of a 2-fibre product of algebraic
stacks, where the charts are produced as objects of the site and so come in the slice model.

## Main results

* `AlgebraicGeometry.Stack.dimensionSubNat_add_zero`: the embedding `dimensionSubNat · 0` of
  `WithBot ℕ∞` in `EInt` is additive.
* `AlgebraicGeometry.Stack.dimensionAtPoint_schemeStack_eq_dimensionSubNat`: the dimension of
  Stacks 0AFN of `schemeStack U` at a chart point is the Krull dimension of `U` there.
* `AlgebraicGeometry.Stack.relativeDimensionAt_schemeStackChart_comp_schemeStackMap_eq`:
  the relative dimension of Stacks 0DRG of the chart of `schemeStack A` followed by the
  1-morphism induced by `γ : A ⟶ V` is the local dimension of the fibre of `γ`.
* `AlgebraicGeometry.Stack.relativeStackDimensionAt_schemeStackMap_eq_dimensionSubNat`: the same
  for the relative dimension of Stacks 0DRL of the induced 1-morphism itself.
* `AlgebraicGeometry.Stack.relativeStackDimensionAt_schemeStack_eq_dimensionSubNat`: the relative
  dimension of Stacks 0DRL of an arbitrary `h : schemeStack A ⟶ schemeStack V` at a chart point
  is the local dimension of the fibre of the morphism of the site underlying `h`.

## Implementation notes

The chart used throughout is `AlgebraicGeometry.Stack.representingStackChart` at the slice
comparison `AlgebraicGeometry.Stack.representedChart` of Stacks 04SW: it is smooth, locally of
finite type and of relative dimension `0` (all three proved), its map on points is
`AlgebraicGeometry.Stack.representedChartPointMap` by
`AlgebraicGeometry.Stack.pointsMap_representingStackChart`, and — this is what makes the fibre
computation possible — its morphism of representing presheaves is the *identity*, by
`AlgebraicGeometry.Stack.representingMap_representingStackChart`. So the representing presheaf
morphism of the composite with `schemeStackMap γ` is `yoneda.map γ` on the nose
(`AlgebraicGeometry.Stack.representingMap_schemeStackMap`), and the chart equation of Stacks 04NM
for `yoneda.map γ`, `AlgebraicGeometry.Space.hasRelativeDimensionAt_yoneda_map_iff`, reads off
the fibre of the morphism of schemes.

Passing from the induced `schemeStackMap γ` to an arbitrary `h` uses
`AlgebraicGeometry.Stack.relativeStackDimensionAt_congr_twoIso`: the relative dimension of
Stacks 0DRL mentions its 1-morphism on the nose, and `h` is only 2-isomorphic to the induced
1-morphism of `AlgebraicGeometry.Stack.siteMap h`.

## References

* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
* [Stacks Project, Tag 0DRG](https://stacks.math.columbia.edu/tag/0DRG)
* [Stacks Project, Tag 0DRH](https://stacks.math.columbia.edu/tag/0DRH)
* [Stacks Project, Tag 0DRJ](https://stacks.math.columbia.edu/tag/0DRJ)
* [Stacks Project, Tag 0DRL](https://stacks.math.columbia.edu/tag/0DRL)
* [Stacks Project, Tag 0DS4](https://stacks.math.columbia.edu/tag/0DS4)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

/-- The embedding `AlgebraicGeometry.Stack.dimensionSubNat · 0` of `WithBot ℕ∞` into `EInt` — the
one the formula of Stacks 0AFN uses on a chart of relative dimension `0` — is additive. Both
monoids have an absorbing bottom element and a top element absorbing everything above the
bottom. -/
theorem dimensionSubNat_add_zero (δ ε : WithBot ℕ∞) :
    dimensionSubNat (δ + ε) 0 = dimensionSubNat δ 0 + dimensionSubNat ε 0 := by
  induction δ using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.bot_add, dimensionSubNat_bot]
    exact (WithBot.bot_add _).symm
  | coe a =>
    induction ε using WithBot.recBotCoe with
    | bot =>
      rw [WithBot.add_bot, dimensionSubNat_bot]
      exact (WithBot.add_bot _).symm
    | coe b =>
      induction a using ENat.recTopCoe <;> induction b using ENat.recTopCoe <;> rfl

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The morphism of representing presheaves of **Stacks 04SW** attached to the 1-morphism of
algebraic stacks induced by a morphism `g : U ⟶ V` of the site is `yoneda.map g`. This is
`AlgebraicGeometry.Stack.representingMap_schemeFibredCategoryMap` read through
`AlgebraicGeometry.Stack.schemeStackMap`, which is that 1-morphism wrapped into the 2-category
of algebraic stacks and so has it as its underlying 1-morphism. -/
theorem representingMap_schemeStackMap {U V : BigFppfOver B S hS} (g : U ⟶ V) :
    representingMap B S hS (schemeStack.{u, w} B S hS U).val
        (schemeStack.{u, w} B S hS V).val (yoneda.obj U) (yoneda.obj V)
        (PresheafOfCategories.sliceElementsEquivalenceOver U)
        (PresheafOfCategories.sliceElementsEquivalenceOver V)
        (schemeStackMap.{u, w} B S hS g).hom = yoneda.map g :=
  representingMap_schemeFibredCategoryMap B S hS g

/-- **The dimension of Stacks 0AFN of the algebraic stack of a scheme of the site is the Krull
dimension of the scheme.** At the point of `|schemeStack U|` named by `q ∈ |U|` the dimension of
Stacks 0AFN is the Krull dimension of `U` at the corresponding scheme point, read in `EInt`
through the embedding `AlgebraicGeometry.Stack.dimensionSubNat · 0`.

The slice comparison of Stacks 04SW represents `schemeStack U` by the algebraic space `U`
represents, so the dimension of Stacks 0AFN is the dimension of Stacks 04N5 of that algebraic
space, by `AlgebraicGeometry.Stack.dimensionAtPoint_eq_dimensionSubNat_zero_of_representing`,
and the latter is the Krull dimension by
`AlgebraicGeometry.Stack.dimensionAtPoint_yoneda_eq_topologicalKrullDimAt`. -/
theorem dimensionAtPoint_schemeStack_eq_dimensionSubNat (U : BigFppfOver B S hS)
    (hU : IsLocallyNoetherianStack.{u, w} B S hS (schemeStack.{u, w} B S hS U))
    (q : Space.points B S hS (yoneda.obj U)) :
    dimensionAtPoint B S hS (schemeStack.{u, w} B S hS U) hU
        (representedChartPointMap B S hS U q) =
      dimensionSubNat (topologicalKrullDimAt ((BigFppfOver.toScheme B S hS).obj U)
        (Space.pointsToScheme B S hS U q)) 0 := by
  rw [dimensionAtPoint_eq_dimensionSubNat_zero_of_representing.{u, w} B S hS
      (schemeStack.{u, w} B S hS U) hU (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
      (representedChart B S hS U) q (representedChartPointMap B S hS U q) rfl,
    dimensionAtPoint_yoneda_eq_topologicalKrullDimAt B S hS U q]

/-- The chart of `AlgebraicGeometry.Stack.schemeStack` carried by the slice comparison of
Stacks 04SW: the 1-morphism to `schemeStack U` from the algebraic stack of the algebraic space
`U` represents. -/
noncomputable abbrev schemeStackChart (U : BigFppfOver B S hS) :
    algebraicSpaceStack.{u, w} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) ⟶
      schemeStack.{u, w} B S hS U :=
  representingStackChart.{u, w} B S hS (schemeStack.{u, w} B S hS U) (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS U) (representedChart B S hS U)

/-- **The chart of a representing equivalence induces the identity on representing presheaves.**
That chart is the backward 1-morphism `AlgebraicGeometry.Stack.equivalenceOverInvMap` of the
comparison, whose morphism of representing presheaves is the identity by
`AlgebraicGeometry.Stack.representingMap_equivalenceOverInvMap`. -/
theorem representingMap_representingStackChart (𝒯 : AlgebraicStacks.{u, w} B S hS)
    (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
    (eZ : StacksRepresentableCFG.EquivalenceOver 𝒯.val.val.p
      (presheafOfCategories (Z ⋙ typeToCat)).p) :
    representingMap B S hS (fibredCategory B S hS Z) 𝒯.val Z Z
        (StacksRepresentableCFG.EquivalenceOver.refl _) eZ
        (representingStackChart.{u, w} B S hS 𝒯 Z hZ eZ).hom = 𝟙 Z :=
  representingMap_equivalenceOverInvMap B S hS Z eZ

/-- **The relative dimension of Stacks 0DRG of the chart of `schemeStack A` followed by the
1-morphism induced by a morphism `γ : A ⟶ V` of the site is the local dimension of the scheme
theoretic fibre of `γ`.**

The morphism of representing presheaves of the chart is the identity
(`AlgebraicGeometry.Stack.representingMap_representingStackChart`) and that of `schemeStackMap γ`
is `yoneda.map γ` (`AlgebraicGeometry.Stack.representingMap_schemeStackMap`), so the composite
induces `yoneda.map γ`; Stacks 0DRH (2) for a target merely represented by an algebraic space
reads the relative dimension of Stacks 0DRG off it, and the chart equation of Stacks 04NM for a
morphism of the site, `AlgebraicGeometry.Space.hasRelativeDimensionAt_yoneda_map_iff`, is the
asserted equation. The value is finite by Stacks 0DRJ, which is what lets the predicate of
Stacks 04NM be turned back into an equation. -/
theorem relativeDimensionAt_schemeStackChart_comp_schemeStackMap_eq
    {A V : BigFppfOver B S hS} (γ : A ⟶ V)
    (hc : AlgebraicStacks.IsLocallyOfFiniteType B S hS
      (schemeStackChart.{u, w} B S hS A ≫ schemeStackMap.{u, w} B S hS γ))
    (a : (BigFppfOver.toScheme B S hS).obj A) :
    relativeDimensionAt.{u, w} B S hS (yoneda.obj A) (isAlgebraicSpace_yoneda B S hS A)
        (schemeStack.{u, w} B S hS V)
        (schemeStackChart.{u, w} B S hS A ≫ schemeStackMap.{u, w} B S hS γ) hc
        ((Space.pointsEquivScheme B S hS A).symm a) =
      topologicalKrullDimAt
        (((BigFppfOver.toScheme B S hS).map γ).fiber
          (((BigFppfOver.toScheme B S hS).map γ) a))
        (((BigFppfOver.toScheme B S hS).map γ).asFiber a) := by
  obtain ⟨d, hd⟩ := exists_relativeDimensionAt_eq_natCast.{u, w} B S hS (yoneda.obj A)
    (isAlgebraicSpace_yoneda B S hS A) (schemeStack.{u, w} B S hS V) _ hc
    ((Space.pointsEquivScheme B S hS A).symm a)
  have hrep : representingMap B S hS (fibredCategory B S hS (yoneda.obj A))
      (schemeStack.{u, w} B S hS V).val (yoneda.obj A) (yoneda.obj V)
      (StacksRepresentableCFG.EquivalenceOver.refl _) (representedChart B S hS V)
      (schemeStackChart.{u, w} B S hS A ≫ schemeStackMap.{u, w} B S hS γ).hom =
      yoneda.map γ := by
    rw [show (schemeStackChart.{u, w} B S hS A ≫ schemeStackMap.{u, w} B S hS γ).hom =
        (schemeStackChart.{u, w} B S hS A).hom ≫ (schemeStackMap.{u, w} B S hS γ).hom from rfl,
      representingMap_comp B S hS (𝒜 := fibredCategory B S hS (yoneda.obj A))
        (ℬ := (schemeStack.{u, w} B S hS A).val) (𝒞 := (schemeStack.{u, w} B S hS V).val)
        (yoneda.obj A) (yoneda.obj A) (yoneda.obj V)
        (StacksRepresentableCFG.EquivalenceOver.refl _) (representedChart B S hS A)
        (representedChart B S hS V) (schemeStackChart.{u, w} B S hS A).hom
        (schemeStackMap.{u, w} B S hS γ).hom,
      representingMap_representingStackChart.{u, w} B S hS (schemeStack.{u, w} B S hS A)
        (yoneda.obj A) (isAlgebraicSpace_yoneda B S hS A) (representedChart B S hS A),
      representingMap_schemeStackMap.{u, w} B S hS γ, Category.id_comp]
  rw [hd]
  refine ((Space.hasRelativeDimensionAt_yoneda_map_iff B S hS γ (d : ℕ∞) a).1 ?_).symm
  have hiff := (relativeDimensionAt_eq_iff_hasRelativeDimensionAt_representingMap.{u, w} B S hS
    (yoneda.obj A) (isAlgebraicSpace_yoneda B S hS A) (schemeStack.{u, w} B S hS V)
    (schemeStackChart.{u, w} B S hS A ≫ schemeStackMap.{u, w} B S hS γ) hc
    (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V) (representedChart B S hS V)
    ((Space.pointsEquivScheme B S hS A).symm a) (d : ℕ∞)).1 hd
  rwa [hrep] at hiff

/-- **The relative dimension of Stacks 0DRL of the 1-morphism induced by a morphism of the site
is the local dimension of the scheme theoretic fibre.** For `γ : A ⟶ V` a morphism of the big
fppf category of `S` whose induced 1-morphism of algebraic stacks is locally of finite type
between locally Noetherian algebraic stacks, and for `a ∈ A`, the relative dimension of
Stacks 0DRL of `schemeStackMap γ` at the point of `|schemeStack A|` named by `a` is the Krull
dimension at `a` of the fibre of `γ` through `a`, read in `EInt`.

This is the chart formula of Stacks 0DRL read on the chart of Stacks 04SW, which is smooth,
locally of finite type and of relative dimension `0`, followed by
`AlgebraicGeometry.Stack.relativeDimensionAt_schemeStackChart_comp_schemeStackMap_eq`. -/
theorem relativeStackDimensionAt_schemeStackMap_eq_dimensionSubNat
    {A V : BigFppfOver B S hS} (γ : A ⟶ V)
    (hγ : AlgebraicStacks.IsLocallyOfFiniteType B S hS (schemeStackMap.{u, w} B S hS γ))
    (hA : IsLocallyNoetherianStack.{u, w} B S hS (schemeStack.{u, w} B S hS A))
    (hV : IsLocallyNoetherianStack.{u, w} B S hS (schemeStack.{u, w} B S hS V))
    (a : (BigFppfOver.toScheme B S hS).obj A) :
    relativeStackDimensionAt.{u, w} B S hS (schemeStackMap.{u, w} B S hS γ) hγ hA hV
        (representedChartPointMap B S hS A ((Space.pointsEquivScheme B S hS A).symm a)) =
      dimensionSubNat
        (topologicalKrullDimAt
          (((BigFppfOver.toScheme B S hS).map γ).fiber
            (((BigFppfOver.toScheme B S hS).map γ) a))
          (((BigFppfOver.toScheme B S hS).map γ).asFiber a)) 0 := by
  have hlft := isLocallyOfFiniteType_representingStackChart.{u, w} B S hS
    (schemeStack.{u, w} B S hS A) (yoneda.obj A) (isAlgebraicSpace_yoneda B S hS A)
    (representedChart B S hS A)
  have hchart : AlgebraicStacks.IsLocallyOfFiniteType B S hS
      (schemeStackChart.{u, w} B S hS A ≫ schemeStackMap.{u, w} B S hS γ) :=
    AlgebraicStacks.isLocallyOfFiniteType_comp B S hS _ _ hlft hγ
  rw [relativeStackDimensionAt_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS
      (𝒯 := schemeStack.{u, w} B S hS A) (𝒳 := schemeStack.{u, w} B S hS V)
      (schemeStackMap.{u, w} B S hS γ) hγ hA hV
      (representedChartPointMap B S hS A ((Space.pointsEquivScheme B S hS A).symm a))
      (isAlgebraicSpace_yoneda B S hS A) (schemeStackChart.{u, w} B S hS A)
      (isSmooth_representingStackChart.{u, w} B S hS (schemeStack.{u, w} B S hS A)
        (yoneda.obj A) (isAlgebraicSpace_yoneda B S hS A) (representedChart B S hS A))
      hlft hchart
      ((Space.pointsEquivScheme B S hS A).symm a)
      (pointsMap_representingStackChart.{u, w} B S hS (schemeStack.{u, w} B S hS A)
        (yoneda.obj A) (isAlgebraicSpace_yoneda B S hS A) (representedChart B S hS A)
        ((Space.pointsEquivScheme B S hS A).symm a))
      0
      (relativeDimensionAt_representingStackChart_eq_zero.{u, w} B S hS
        (schemeStack.{u, w} B S hS A) (yoneda.obj A) (isAlgebraicSpace_yoneda B S hS A)
        (representedChart B S hS A)
        hlft
        ((Space.pointsEquivScheme B S hS A).symm a)),
    relativeDimensionAt_schemeStackChart_comp_schemeStackMap_eq.{u, w} B S hS γ hchart a]

/-- **The relative dimension of Stacks 0DRL of a 1-morphism of the algebraic stacks of two
schemes of the site is the local dimension of the scheme theoretic fibre of the underlying
morphism of schemes.** For `h : schemeStack A ⟶ schemeStack V` locally of finite type between
locally Noetherian algebraic stacks and `a ∈ A`, the relative dimension of Stacks 0DRL of `h` at
the point of `|schemeStack A|` named by `a` is the Krull dimension at `a` of the fibre of
`AlgebraicGeometry.Stack.siteMap h` through `a`, read in `EInt`.

A 1-morphism of represented algebraic stacks is only 2-isomorphic to the one induced by the
morphism of the site underlying it, and the relative dimension of Stacks 0DRL mentions its
1-morphism on the nose; `AlgebraicGeometry.Stack.relativeStackDimensionAt_congr_twoIso` is what
bridges that gap, after which this is
`AlgebraicGeometry.Stack.relativeStackDimensionAt_schemeStackMap_eq_dimensionSubNat`. -/
theorem relativeStackDimensionAt_schemeStack_eq_dimensionSubNat
    {A V : BigFppfOver B S hS} (h : schemeStack.{u, w} B S hS A ⟶ schemeStack.{u, w} B S hS V)
    (hh : AlgebraicStacks.IsLocallyOfFiniteType B S hS h)
    (hA : IsLocallyNoetherianStack.{u, w} B S hS (schemeStack.{u, w} B S hS A))
    (hV : IsLocallyNoetherianStack.{u, w} B S hS (schemeStack.{u, w} B S hS V))
    (a : (BigFppfOver.toScheme B S hS).obj A) :
    relativeStackDimensionAt.{u, w} B S hS h hh hA hV
        (representedChartPointMap B S hS A ((Space.pointsEquivScheme B S hS A).symm a)) =
      dimensionSubNat
        (topologicalKrullDimAt
          (((BigFppfOver.toScheme B S hS).map (siteMap B S hS h)).fiber
            (((BigFppfOver.toScheme B S hS).map (siteMap B S hS h)) a))
          (((BigFppfOver.toScheme B S hS).map (siteMap B S hS h)).asFiber a)) 0 := by
  have hmap : AlgebraicStacks.IsLocallyOfFiniteType B S hS
      (schemeStackMap.{u, w} B S hS (siteMap B S hS h)) :=
    AlgebraicStacks.isLocallyOfFiniteType_of_twoIso B S hS
      (Bicategory.InducedBicategory.isoHom (schemeStackMapIso B S hS h)) hh
  rw [relativeStackDimensionAt_congr_twoIso.{u, w} B S hS (schemeStackMapIso B S hS h) hh hmap
    hA hV (representedChartPointMap B S hS A ((Space.pointsEquivScheme B S hS A).symm a))]
  exact relativeStackDimensionAt_schemeStackMap_eq_dimensionSubNat.{u, w} B S hS
    (siteMap B S hS h) hmap hA hV a

end AlgebraicGeometry.Stack

end
