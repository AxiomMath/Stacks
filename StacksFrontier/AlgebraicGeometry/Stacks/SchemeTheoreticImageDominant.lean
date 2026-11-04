module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Dominant
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionSchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionSchemeTheoreticImageDense
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionStackLocalConstancy
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeTheoreticImagePointsClosure
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointSmoothChart
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStackDimensionFibre

/-!
# Dominance of the charts of a 1-morphism over its scheme theoretic image

Let `f : 𝒯 ⟶ 𝒳` be a quasi-compact 1-morphism of algebraic stacks over `S` and let `𝒵 ↪ 𝒳` be
its scheme theoretic image (**Stacks 0CMI**). The proof of **Stacks 0DS4** compares `𝒯` with a
smooth chart `𝒱 ⟶ 𝒵` through a chart of the 2-fibre product `𝒯 ×_𝒵 𝒱`, and the dimension
formula it ends on — for a dominant morphism of schemes — needs that chart to be *dominant* over
`𝒱`. This file supplies that dominance, in three steps:

1. the factorization `𝒯 ⟶ 𝒵` has dense image on points, which is **Stacks 0CML** read through the
   topological embedding of the closed immersion `𝒵 ⟶ 𝒳`;
2. hence the first projection of a 2-fibre product `𝒯 ×_𝒵 𝒱` has dense image on `|𝒱|`, as soon
   as `𝒱 ⟶ 𝒵` is open on points — which a smooth chart is;
3. hence, for charts that are algebraic stacks of schemes of the site, the underlying morphism of
   schemes is dominant.

## Main results

* `AlgebraicGeometry.Stack.dense_range_pointsMap_substackFactorizationHom`: step 1.
* `AlgebraicGeometry.Stack.dense_range_pointsMap_fst_of_isTwoFibreProduct`: step 2.
* `AlgebraicGeometry.Stack.isDominant_siteMap_of_dense_range`: step 3.

## Implementation notes

Step 1 is where quasi-compactness of `f` is used, through **Stacks 0CML**
`AlgebraicGeometry.Stack.range_pointsMap_eq_closure_of_isSchemeTheoreticImage`: without it the
points of the scheme theoretic image need not be the closure of the image of `|f|`. The inclusion
of the image is a closed immersion, so it is a closed map and a topological embedding on points
(**Stacks 0H20**); a closed continuous map commutes with closures of images, and an injective one
may then be cancelled.

Step 2 is **Stacks 04XH**, the surjectivity of `|𝒯 ×_𝒵 𝒱| ⟶ |𝒯| ×_{|𝒵|} |𝒱|`: a nonempty open
subset of `|𝒱|` has open nonempty image in `|𝒵|`, which meets the dense image of `|𝒯|`, and a
point of `|𝒯|` and one of the open subset with the same image in `|𝒵|` lift to the 2-fibre
product. Openness of `|𝒱| ⟶ |𝒵|` is all that is asked of the chart; for a smooth one it is
`AlgebraicGeometry.Stack.isOpenMap_pointsMap_of_isSmooth`.

Step 3 is the homeomorphism `AlgebraicGeometry.Stack.pointsHomeomorphScheme` between the points
of `schemeStack U` and the scheme `U`, which carries a 1-morphism to the morphism of the site
underlying it by `AlgebraicGeometry.Stack.pointsHomeomorphScheme_pointsMap`.

## References

* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 0CMI](https://stacks.math.columbia.edu/tag/0CMI)
* [Stacks Project, Tag 0CML](https://stacks.math.columbia.edu/tag/0CML)
* [Stacks Project, Tag 0DS4](https://stacks.math.columbia.edu/tag/0DS4)
* [Stacks Project, Tag 0H20](https://stacks.math.columbia.edu/tag/0H20)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The factorization of a quasi-compact 1-morphism through its scheme theoretic image is
dominant on points.** For `f : 𝒯 ⟶ 𝒳` quasi-compact and `P` cutting out the scheme theoretic
image `𝒵` of Stacks 0CMI, the image of `|𝒯| ⟶ |𝒵|` is dense.

By Stacks 0CML the image of `|𝒵|` in `|𝒳|` is the closure of the image of `|f|`, and `|f|` is the
composite of `|𝒯| ⟶ |𝒵|` with that inclusion. The inclusion is a closed immersion, so it is a
continuous closed map and commutes with closures of images, and it is injective, being a
topological embedding by Stacks 0H20; cancelling it leaves the closure of the image of
`|𝒯| ⟶ |𝒵|` equal to all of `|𝒵|`. -/
theorem dense_range_pointsMap_substackFactorizationHom
    {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒯 ⟶ 𝒳)
    (hfQC : IsQuasiCompactMorphism B S hS f)
    {P : ObjectProperty 𝒳.val.val.obj} (hP : IsSchemeTheoreticImage f P) :
    @Dense _
      (pointTopology B S hS (fullSubcategoryAlgebraicStack 𝒳 P hP.isAlgebraicStack).val)
      (Set.range (AlgebraicStacks.pointsMap B S hS
        (factorsThroughSubstackHom f hP.isAlgebraicStack hP.2.1))) := by
  let := pointTopology B S hS 𝒳.val
  let := pointTopology B S hS 𝒯.val
  let := pointTopology B S hS (fullSubcategoryAlgebraicStack 𝒳 P hP.isAlgebraicStack).val
  set i := fullSubcategoryInclusion 𝒳 P hP.isAlgebraicStack with hi
  set g := factorsThroughSubstackHom f hP.isAlgebraicStack hP.2.1 with hg
  have hci : AlgebraicStacks.IsClosedImmersion B S hS i := hP.1.2.choose_spec
  have himm : AlgebraicStacks.IsImmersion B S hS i :=
    AlgebraicStacks.isImmersion_of_isClosedImmersion B S hS i hci
  have hinj : Function.Injective (AlgebraicStacks.pointsMap B S hS i) :=
    (AlgebraicStacks.isEmbedding_pointsMap_of_isImmersion B S hS i himm).injective
  have hclosed : IsClosedMap (AlgebraicStacks.pointsMap B S hS i) :=
    AlgebraicStacks.isClosedMap_pointsMap_of_isClosedImmersion B S hS i hci
  have hcont : Continuous (AlgebraicStacks.pointsMap B S hS i) :=
    continuous_pointsMap B S hS _ 𝒳.val i.hom.hom
  have hcomp : AlgebraicStacks.pointsMap B S hS f =
      AlgebraicStacks.pointsMap B S hS i ∘ AlgebraicStacks.pointsMap B S hS g :=
    (AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS
      (factorsThroughSubstackIso f hP.isAlgebraicStack hP.2.1).inv).trans
      (AlgebraicStacks.pointsMap_comp B S hS g i)
  have hrange := range_pointsMap_eq_closure_of_isSchemeTheoreticImage B S hS f hfQC hP
  rw [hcomp, Set.range_comp, hclosed.closure_image_eq_of_continuous hcont,
    ← Set.image_univ] at hrange
  exact dense_iff_closure_eq.2 (Set.image_injective.2 hinj hrange).symm

end AlgebraicGeometry.Stack

end
