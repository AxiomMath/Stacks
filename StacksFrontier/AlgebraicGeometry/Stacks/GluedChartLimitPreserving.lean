module

public import StacksFrontier.AlgebraicGeometry.Stacks.CoproductChartPropertyDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.LimitPreservingFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingObjectsFinitePresentation

/-!
# Limit preservation on objects of a 1-morphism out of a coproduct

Let `𝒴` be a category fibred in groupoids over the big fppf site of `S`, let `W` be an object of
the site which is, in schemes, the coproduct of a family `Z i` of objects of the site, and let
`g : (Sch/W)_{fppf} ⟶ 𝒴` be a 1-morphism representable by algebraic spaces whose restriction
along each summand inclusion is 2-isomorphic to a given `f i : (Sch/Z i)_{fppf} ⟶ 𝒴`. This file
proves that `g` is limit preserving on objects in the sense of **Stacks 06CU** as soon as every
`f i` is.

The condition of Stacks 06CU is universal over the objects of the source, so it does not pass to
`g` from a single member of the family: an affine object of the site mapping to `∐ Z i` need not
land in one summand. What is used instead is **Stacks 06CX**, which for a 1-morphism
representable by algebraic spaces identifies limit preservation on objects with local finite
presentation in the sense of **Stacks 03YK**, and the chart-free descent of a source-local
relative property along the summand inclusions,
`AlgebraicGeometry.Stack.relativeProperty_of_isColimit_of_forall`. Local finite presentation of
morphisms of algebraic spaces is fppf, hence étale, local on the source (**Stacks 06EV**).

## Main results

* `AlgebraicGeometry.Stack.isLimitPreservingOnObjects_of_isColimit_of_forall`: limit preservation
  on objects descends from the summands to a 1-morphism out of the coproduct.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 06CX](https://stacks.math.columbia.edu/tag/06CX)
* [Stacks Project, Tag 06EV](https://stacks.math.columbia.edu/tag/06EV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Limit preservation on objects descends from the summands to a 1-morphism out of a
coproduct of objects of the site.** Let `W` be an object of the big fppf site over `S` which is,
in schemes, the coproduct of a family `Z i` of objects of the site, let
`g : (Sch/W)_{fppf} ⟶ 𝒴` be a 1-morphism into a category fibred in groupoids over the big fppf
site of `S`, representable by algebraic spaces, and let `f i : (Sch/Z i)_{fppf} ⟶ 𝒴` be
1-morphisms with `schemeFibredCategoryMap (jj i) ≫ g` 2-isomorphic to `f i` for every `i`. If
every `f i` is limit preserving on objects (**Stacks 06CU**), then so is `g`.

Nothing is assumed about `𝒴` beyond being fibred in groupoids. The condition is traded for local
finite presentation in the sense of **Stacks 03YK** by **Stacks 06CX** on both sides, and there
it descends along the summand inclusions by
`AlgebraicGeometry.Stack.relativeProperty_of_isColimit_of_forall`, local finite presentation of
morphisms of algebraic spaces being fppf — hence, by **Stacks 0DFC**, étale — local on the
source. -/
theorem isLimitPreservingOnObjects_of_isColimit_of_forall
    {𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} {I : Type u}
    (Z : I → BigFppfOver B S hS) (W : BigFppfOver B S hS) (jj : ∀ i, Z i ⟶ W)
    (hW : IsColimit (Cofan.mk ((BigFppfOver.toScheme B S hS).obj W)
      (fun i => (BigFppfOver.toScheme B S hS).map (jj i))))
    (g : schemeFibredCategory B S hS W ⟶ 𝒴)
    (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom)
    (f : ∀ i, schemeFibredCategory B S hS (Z i) ⟶ 𝒴)
    (hfg : ∀ i, Nonempty (schemeFibredCategoryMap B S hS (jj i) ≫ g ≅ f i))
    (hf : ∀ i, BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS
      (schemeFibredCategory B S hS (Z i)) 𝒴 (f i)) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS
      (schemeFibredCategory B S hS W) 𝒴 g := by
  have : (Space.locallyOfFinitePresentationProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isLocallyOfFinitePresentation_isLocalAtTarget_fppf.{u, u} B S hS
  have : (Space.locallyOfFinitePresentationProperty B S hS).IsLocalAtSource
      (Space.Topology.etale.precoverage.{u, u} B S hS) :=
    MorphismProperty.IsLocalAtSource.of_le
      (Space.Topology.precoverage_etale_le_fppf.{u, u} B S hS)
  refine (isLimitPreservingOnObjects_iff_isLocallyOfFinitePresentation B S hS
    (schemeFibredCategory B S hS W) 𝒴 g hg).mpr ?_
  refine relativeProperty_of_isColimit_of_forall B S hS Z W jj g
    (Space.locallyOfFinitePresentationProperty B S hS) hW hg (fun i => ?_)
  exact (isLimitPreservingOnObjects_iff_isLocallyOfFinitePresentation B S hS
    (schemeFibredCategory B S hS (Z i)) 𝒴 (schemeFibredCategoryMap B S hS (jj i) ≫ g)
    (isRepresentableByAlgebraicSpaces_comp B S hS (schemeFibredCategoryMap B S hS (jj i)) g
      (isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS (jj i)) hg)).mp
    (BigFppfOver.isLimitPreservingOnObjects_of_iso B S hS (hfg i).some.symm (hf i))

end AlgebraicGeometry.Stack

end
