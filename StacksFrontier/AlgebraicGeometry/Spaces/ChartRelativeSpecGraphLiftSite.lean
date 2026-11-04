module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecAtlasRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecGraphLift

/-!
# The morphism into a relative spectrum over a chart as a morphism of the site

`AlgebraicGeometry.Space.chartOverRelativeSpecLift` is the morphism
`T ⟶ \underline{Spec}_{V}(A|_V)` of *schemes over `chartScheme V`* which an algebra `A ⟶ f_* 𝒪_Y`
on the base determines at a scheme object `T` of the big fppf category presenting a space over `X`
above the chart `V`. This file forms it as a morphism of the **big fppf category over `S`**, into
the site object `AlgebraicGeometry.Space.chartRelativeSpecSite`.

## Main definitions

* `AlgebraicGeometry.Space.chartOverRelativeSpecSiteHom`: the morphism
  `T ⟶ AlgebraicGeometry.Space.chartRelativeSpecSite A V` of the big fppf category over `S`.

## Main results

* `AlgebraicGeometry.Space.toScheme_map_chartOverRelativeSpecSiteHom`: its underlying morphism of
  schemes is the lift.
* `AlgebraicGeometry.Space.chartOverRelativeSpecSiteHom_comp_siteMapOver`: it lies over the chart,
  that is, composing it with the structural morphism of the site object to the chart returns the
  morphism `T ⟶ V` the data provides.

## Implementation notes

Containment of the underlying scheme of the relative spectrum in the site is a hypothesis, as it is
for `AlgebraicGeometry.Space.chartRelativeSpecSite`; at the two hypotheses of Definition 0822 it is
`AlgebraicGeometry.Space.contains_chartRelativeSpec_integralClosureSheaf_pushforwardAlgebra`.

## References

* [Stacks Project, Tag 021S](https://stacks.math.columbia.edu/tag/021S)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 081X](https://stacks.math.columbia.edu/tag/081X)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS} (f : Y ⟶ X) (p : Z ⟶ X) (τ : Z ⟶ Y)
    (hτ : τ ≫ f = p) (hp : yoneda.relativelyRepresentable p.hom)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (ι : A ⟶ pushforwardAlgebra B S hS (Over.mk f))
    (V : SmallEtale B S hS X.1) (T : BigFppfOver B S hS)
    (t : T ⟶ (SmallEtale.toOver B S hS X.1).obj V) (z : yoneda.obj T ⟶ Z.1)
    (hz : z ≫ p.hom = yoneda.map t ≫ V.obj.hom) (hA : A.IsQuasicoherent)
    (hV : B.Contains (chartRelativeSpec B S hS X A hA V))

/-- **The morphism `T ⟶ \underline{Spec}_{V}(A|_V)` as a morphism of the big fppf category over
`S`.**

It is `AlgebraicGeometry.Space.chartOverRelativeSpecLift` read through
`AlgebraicGeometry.BigFppfOver.siteHomOver`: the triangle over `S` which a morphism of the
category has to satisfy is the statement that the lift lies over the chart,
`AlgebraicGeometry.Space.chartOverRelativeSpecLift_comp`. -/
def chartOverRelativeSpecSiteHom : T ⟶ chartRelativeSpecSite B S hS X A hA V hV :=
  BigFppfOver.siteHomOver B S hS ((SmallEtale.toOver B S hS X.1).obj V) hV
    (chartRelativeSpecToChart B S hS X A hA V) t
    (chartOverRelativeSpecLift B S hS f p τ hτ hp A ι V T t z hz hA).left
    (chartOverRelativeSpecLift_comp B S hS f p τ hτ hp A ι V T t z hz hA)

/-- The morphism of schemes underlying
`AlgebraicGeometry.Space.chartOverRelativeSpecSiteHom` is the lift. -/
@[simp]
theorem toScheme_map_chartOverRelativeSpecSiteHom :
    (BigFppfOver.toScheme B S hS).map
        (chartOverRelativeSpecSiteHom B S hS f p τ hτ hp A ι V T t z hz hA hV) =
      (chartOverRelativeSpecLift B S hS f p τ hτ hp A ι V T t z hz hA).left :=
  rfl

/-- **The morphism of the site lies over the chart**: composed with the structural morphism of
`AlgebraicGeometry.Space.chartRelativeSpecSite` to the chart it is the morphism `T ⟶ V` the data
provides. -/
@[simp]
theorem chartOverRelativeSpecSiteHom_comp_siteMapOver :
    chartOverRelativeSpecSiteHom B S hS f p τ hτ hp A ι V T t z hz hA hV ≫
        BigFppfOver.siteMapOver B S hS ((SmallEtale.toOver B S hS X.1).obj V) hV
          (chartRelativeSpecToChart B S hS X A hA V) =
      t :=
  BigFppfOver.siteHomOver_comp_siteMapOver B S hS ((SmallEtale.toOver B S hS X.1).obj V) hV
    (chartRelativeSpecToChart B S hS X A hA V) t
    (chartOverRelativeSpecLift B S hS f p τ hτ hp A ι V T t z hz hA).left
    (chartOverRelativeSpecLift_comp B S hS f p τ hτ hp A ι V T t z hz hA)

end AlgebraicGeometry.Space

end
