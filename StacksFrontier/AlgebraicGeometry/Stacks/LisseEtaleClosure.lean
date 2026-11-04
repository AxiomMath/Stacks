module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleInclusion
public import StacksFrontier.AlgebraicGeometry.Stacks.PresentationLift
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismComp
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismCompGeneral

/-!
# The smooth objects of an algebraic stack are closed under smooth morphisms

**Stacks 07AK** (1), in the étale case of **Stacks 0788** (1), asks that an object of an algebraic
stack `𝒳` with a morphism to a smooth object, lying over a smooth morphism of schemes, be itself
smooth. That condition is
`AlgebraicGeometry.Stack.LisseEtale.ClosedUnderSmoothMorphisms`, the single hypothesis carried by
everything in `StacksFrontier/AlgebraicGeometry/Stacks/LisseEtaleInclusion.lean`.

This file discharges it, with no hypothesis.

## Main results

* `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_isSmooth_comp`: a composite of smooth
  1-morphisms of categories fibred in groupoids is smooth.
* `AlgebraicGeometry.Stack.LisseEtale.closedUnderSmoothMorphisms`: the closure condition holds
  for every algebraic stack over `S`.

## Implementation notes

This is the lisse-étale sibling of
`AlgebraicGeometry.Stack.FlatFppf.closedUnderFlatMorphisms` and has the same shape, with
`AlgebraicGeometry.Space.IsSmooth` in place of `AlgebraicGeometry.Space.IsFlat` and with no
local-finite-presentation clause to carry: smoothness of an object `x` of `𝒳` is smoothness of
the 1-morphism `x : U → 𝒳` of the 2-Yoneda lemma
(`AlgebraicGeometry.Stack.smoothObject`, a declaration of **Stacks 0787**), read as the
existential smooth-diagram criterion of **Stacks 06FM**. So for `φ : x ⟶ y` lying over
`q : U ⟶ V` the statement is that `x : U → 𝒳` is smooth as soon as `y : V → 𝒳` is and `q` is a
smooth morphism of schemes, and the proof is the factorization `x ≅ (q : U → V) ≫ (y : V → 𝒳)`
of `AlgebraicGeometry.Stack.objectMorphismFactorIso` together with closure of smoothness under
composition:

1. `q` is a smooth morphism of schemes, so `h_q : h_U ⟶ h_V` is a smooth morphism of algebraic
   spaces (**Stacks 03MJ** for a morphism of the site,
   `AlgebraicGeometry.Space.isSmooth_yoneda_map_iff`), so the 1-morphism
   `(Sch/U)_fppf ⟶ (Sch/V)_fppf` it induces has the relative property of **Stacks 03YK** at
   smoothness (`AlgebraicGeometry.Stack.hasRelativeProperty_schemeFibredCategoryMap`), so — the
   target being an algebraic stack by **Stacks 026O** — it is smooth in the sense of
   **Stacks 06FN**;
2. the composite `(q : U → V) ≫ (y : V → 𝒳)` is therefore smooth, by **Stacks 06FP**
   (`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_comp_of_precomp`);
3. and `x : U → 𝒳` is 2-isomorphic to that composite, so it passes the same test — the *same*
   diagram works, with its filler whiskered by the 2-cell, which is the four lines step 3 takes
   below.

Two instances on smoothness of morphisms of algebraic spaces are supplied locally rather than
globally: stability under base change is **Stacks 03ZE**, and locality at the target for the
fppf precoverage is **Stacks 0429** for the fpqc precoverage carried across
`AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage` by
`CategoryTheory.MorphismProperty.IsLocalAtTarget.of_le`.

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 03ZD](https://stacks.math.columbia.edu/tag/03ZD)
* [Stacks Project, Tag 03ZE](https://stacks.math.columbia.edu/tag/03ZE)
* [Stacks Project, Tag 0429](https://stacks.math.columbia.edu/tag/0429)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FN](https://stacks.math.columbia.edu/tag/06FN)
* [Stacks Project, Tag 06FP](https://stacks.math.columbia.edu/tag/06FP)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A composite of smooth 1-morphisms of categories fibred in groupoids is smooth**, smoothness
being the existential smooth-diagram criterion of **Stacks 06FM** at smoothness of morphisms of
algebraic spaces over `S`. This is
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_comp_of_precomp`
(**Stacks 06FP**) at that property; it is the sibling of
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_isFlat_comp` and is left untagged for the
same reason: it is stated for arbitrary categories fibred in groupoids, while the tag names the
statement for algebraic stacks. -/
theorem hasPropertyOnSomeSmoothDiagram_isSmooth_comp
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : HasPropertyOnSomeSmoothDiagram B S hS (fun _ _ k => Space.IsSmooth B S hS k) f)
    (hg : HasPropertyOnSomeSmoothDiagram B S hS (fun _ _ k => Space.IsSmooth B S hS k) g) :
    HasPropertyOnSomeSmoothDiagram B S hS (fun _ _ k => Space.IsSmooth B S hS k) (f ≫ g) :=
  have : (spaceProperty B S hS
      (fun _ _ k => Space.IsSmooth B S hS k)).IsStableUnderBaseChange :=
    Space.isSmooth_isStableUnderBaseChange B S hS
  hasPropertyOnSomeSmoothDiagram_comp_of_precomp B S hS
    (fun _ _ k => Space.IsSmooth B S hS k)
    (fun hX hY hZ p q hp hq => Space.isSmooth_comp B S hS hX hY hZ p q hp hq)
    (fun hX hY hZ p q hp hq => Space.isSmooth_comp B S hS hX hY hZ p q hp hq) f g hf hg

namespace LisseEtale

variable (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- **The closure condition of Stacks 07AK (1) holds for the smooth objects of any algebraic
stack.** An object of `𝒳` with a morphism to a smooth object, lying over a smooth morphism of
schemes, is smooth.

This discharges the one hypothesis of everything Stacks 0788 (1) asserts beyond full faithfulness
of the inclusion of the lisse-étale site; see the implementation notes of this module. -/
theorem closedUnderSmoothMorphisms : ClosedUnderSmoothMorphisms.{u, w} B S hS 𝒳 := by
  have hBC : (Stack.spaceProperty B S hS
      (fun _ _ k => Space.IsSmooth B S hS k)).IsStableUnderBaseChange :=
    Space.isSmooth_isStableUnderBaseChange B S hS
  have hLT : (Stack.spaceProperty B S hS
      (fun _ _ k => Space.IsSmooth B S hS k)).IsLocalAtTarget
        (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  intro x y φ hsmooth hy
  -- the morphism of schemes `φ` lies over induces a smooth morphism of representable spaces
  have hqsmooth : Space.IsSmooth B S hS (yoneda.map (𝒳.val.val.p.map φ)) :=
    (Space.isSmooth_yoneda_map_iff B S hS (𝒳.val.val.p.map φ)).mpr hsmooth
  have hqdiag : HasPropertyOnSomeSmoothDiagram B S hS
      (fun _ _ k => Space.IsSmooth B S hS k)
      (schemeFibredCategoryMap B S hS (𝒳.val.val.p.map φ)) :=
    hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty B S hS
      (fun _ _ k => Space.IsSmooth B S hS k)
      (isAlgebraicStack_schemeFibredCategory.{u, w} B S hS (𝒳.val.val.p.obj y))
      (schemeFibredCategoryMap B S hS (𝒳.val.val.p.map φ))
      (isRepresentableByAlgebraicSpaces_overMapBased B S hS (𝒳.val.val.p.map φ))
      (hasRelativeProperty_schemeFibredCategoryMap B S hS
        (Stack.spaceProperty B S hS (fun _ _ k => Space.IsSmooth B S hS k))
        (𝒳.val.val.p.map φ) hqsmooth)
  -- the composite `U → V → 𝒳` is smooth, by Stacks 06FP
  have hcomp := hasPropertyOnSomeSmoothDiagram_isSmooth_comp B S hS
    (schemeFibredCategoryMap B S hS (𝒳.val.val.p.map φ))
    (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := y) rfl)) hqdiag hy
  -- and `x : U → 𝒳` is 2-isomorphic to it, so the same diagram serves, with its filler whiskered
  obtain ⟨U, V, hU, hV, a, b, h, ⟨η⟩, ha, hasurj, hb, hPh⟩ := hcomp
  exact ⟨U, V, hU, hV, a, b, h,
    ⟨η ≪≫ Bicategory.whiskerLeftIso a (objectMorphismFactorIso B S hS 𝒳.val φ).symm⟩,
    ha, hasurj, hb, hPh⟩

end LisseEtale

end AlgebraicGeometry.Stack

end
