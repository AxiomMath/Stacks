module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceCompositeZero
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDifferentialsShortExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsChartRestriction
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 06BI reduced to a triangle of schemes of the site

Stacks 06BI asserts that for a **formally smooth** `f : X ⟶ Y` and any `g : Y ⟶ B` the
transitivity sequence of Stacks 05Z8

```
0 ⟶ f^*Ω_{Y/B} ⟶ Ω_{X/B} ⟶ Ω_{X/Y} ⟶ 0
```

is short exact.  Beyond the three clauses of Stacks 05Z8 this adds monomorphy of the first map
`AlgebraicGeometry.Space.pullbackDifferentialsMap`, which is the comparison map of Stacks 04CX
of the square with top edge `f`, right edge `g`, left edge `f ≫ g` and bottom edge `𝟙 B`.

`AlgebraicGeometry.Space.triangleDifferentials_shortExact` proves it granted
`AlgebraicGeometry.Space.PullbackDifferentialsMapChartComparison`, a *chartwise* hypothesis:
over a commuting diagram of étale scheme charts it asks for monomorphy of the restriction of the
comparison map to be implied by monomorphy of the chart morphisms' own canonical map of
Stacks 01UV.  This file removes the chartwise shape of that input, exactly as
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsBaseChangeChartReduction.lean` removes
it for Stacks 05ZC and Stacks 05ZD: what is left is one statement mentioning no algebraic space,
no chart and no étale morphism,

> for a composable pair `ψ : U ⟶ V`, `χ : V ⟶ W` of schemes of the big fppf site over `S`, the
> first map of the transitivity sequence of the pair read as *represented* algebraic spaces is a
> monomorphism as soon as the canonical map of Stacks 01UV of the pair of schemes is.

That statement is `AlgebraicGeometry.Space.IsSchemeTriangleDifferentialsMono` below.  It is the
monomorphy twin of `AlgebraicGeometry.Space.IsSchemeSquareDifferentialsIso`: the square there is
cartesian and its bottom edge is arbitrary, the square here has bottom edge an identity, and
monomorphy — unlike invertibility, which Morphisms, Lemma 01V0 supplies outright — has to be
assumed of the scheme-level map, because it holds only under a hypothesis on `ψ` (formal
smoothness; see
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_mono_of_formallySmoothAffineLocally`).

The localization step is carried out here in full and nothing of it is assumed: Stacks 02X1,
applied twice by `AlgebraicGeometry.Space.exists_etale_chart_diagram`, produces a commuting
diagram of étale charts of `X`, `Y` and `B` whose chart of `X` is surjective, and
`AlgebraicGeometry.Space.mono_modulePullback_map_of_mono_chartComparison` identifies the
restriction of the comparison map to that chart with the chart triangle's own comparison map.

## Main definitions

* `AlgebraicGeometry.Space.IsSchemeTriangleDifferentialsMono`: the one statement Stacks 06BI
  still needs — monomorphy of the comparison map of Stacks 04CX of a triangle of schemes of the
  site, read as a triangle of represented algebraic spaces, from monomorphy of the canonical map
  of Stacks 01UV of the same triangle of schemes.

## Main results

* `AlgebraicGeometry.Space.pullbackDifferentialsMapChartComparison_of_schemeTriangle`: the
  chartwise input of Stacks 06BI follows from that statement alone.
* `AlgebraicGeometry.Space.triangleDifferentials_shortExact_of_schemeTriangle`: **Stacks 06BI
  from that statement alone.**  No clause of Stacks 04CU and no sections-level identification is
  carried.

## Implementation notes

The chart diagram of `AlgebraicGeometry.Space.exists_etale_chart_diagram` is consumed in the
shape `AlgebraicGeometry.Space.mono_modulePullback_map_of_mono_chartComparison` asks for, with
the chart of `B` serving as the chart of the bottom-left corner of both columns: the left column
`f ≫ g : X ⟶ B` and the right column `g : Y ⟶ B` have the same target, so one chart of `B` does
for both and the bottom edge of the chart square is the identity.  That is why the hypothesis is
a statement about a *triangle* `ψ`, `χ` of schemes rather than about a square.

The commutativity `hUV'` of the left column's chart square is not part of the chart diagram: it
is derived from the other two, the chart square of `f` and the chart square of `g` pasted along
the chart of `Y`.

## References

* [Stacks Project, Tag 06BI](https://stacks.math.columbia.edu/tag/06BI)
* [Stacks Project, Tag 05Z8](https://stacks.math.columbia.edu/tag/05Z8), the transitivity
  sequence and its three clauses.
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX), the comparison map of a
  commutative square and its uniqueness.
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU), the étale localization
  of the sheaf of differentials.
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV), the canonical map for
  schemes.
* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1), the lifting of a chart
  along a morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The one statement Stacks 06BI still needs.**  For a composable pair `ψ : U ⟶ V`,
`χ : V ⟶ W` of schemes of the big fppf site over `S`, the first map
`(ψ)^*Ω_{V/W} ⟶ Ω_{U/W}` of the transitivity sequence of Stacks 05Z8 of the pair read as
*represented* algebraic spaces is a monomorphism as soon as the canonical map of Stacks 01UV of
the pair of schemes is.

No algebraic space, no chart and no étale morphism occurs.  This is the monomorphy twin of
`AlgebraicGeometry.Space.IsSchemeSquareDifferentialsIso`: there the square is cartesian and
Morphisms, Lemma 01V0 makes the scheme-level map invertible outright, so nothing is assumed of
it; here the scheme-level map is a monomorphism only under a hypothesis on `ψ`, so monomorphy of
it is the hypothesis. -/
abbrev IsSchemeTriangleDifferentialsMono : Prop :=
  ∀ (U V W : BigFppfOver B S hS) (ψ : U ⟶ V) (χ : V ⟶ W),
    Mono (Scheme.Hom.relativeDifferentialsMap ((BigFppfOver.toScheme B S hS).map ψ)
      ((BigFppfOver.toScheme B S hS).map χ)
      ((BigFppfOver.toScheme B S hS).map ψ ≫ (BigFppfOver.toScheme B S hS).map χ)
      (𝟙 ((BigFppfOver.toScheme B S hS).obj W)) (Category.comp_id _).symm) →
    Mono (pullbackDifferentialsMap B S hS (schemeSpaceMap ψ) (schemeSpaceMap χ))

variable {X Y Z : AlgebraicSpaces B S hS}

/-- **The chartwise input of Stacks 06BI follows from
`AlgebraicGeometry.Space.IsSchemeTriangleDifferentialsMono` alone.**

Given a commuting diagram of étale scheme charts of `X`, `Y` and `B` over `ψ` and `χ`, the chart
of `B` serves as the chart of the target of both columns, so the chart square of the comparison
map has bottom edge the identity and is the triangle `ψ`, `χ`;
`AlgebraicGeometry.Space.mono_modulePullback_map_of_mono_chartComparison` then identifies the
restriction of the comparison map along the chart of `X` with the comparison map of that
triangle. -/
theorem pullbackDifferentialsMapChartComparison_of_schemeTriangle
    (hscheme : IsSchemeTriangleDifferentialsMono B S hS) (f : X ⟶ Y) (g : Y ⟶ Z) :
    PullbackDifferentialsMapChartComparison B S hS f g := by
  intro U V W a b c ψ χ haEtale hbEtale hcEtale _haSurj hsqψ hsqχ hmono
  let aX : schemeSpace U ⟶ X := ObjectProperty.homMk a
  let bY : schemeSpace V ⟶ Y := ObjectProperty.homMk b
  let cZ : schemeSpace W ⟶ Z := ObjectProperty.homMk c
  have haX : IsEtale B S hS aX.hom := isEtale_of_presheaf_etale B S hS haEtale
  have hbY : IsEtale B S hS bY.hom := isEtale_of_presheaf_etale B S hS hbEtale
  have hcZ : IsEtale B S hS cZ.hom := isEtale_of_presheaf_etale B S hS hcEtale
  have hUV : bY ≫ g = schemeSpaceMap χ ≫ cZ := ObjectProperty.hom_ext _ hsqχ.symm
  have htop : aX ≫ f = schemeSpaceMap ψ ≫ bY := ObjectProperty.hom_ext _ hsqψ.symm
  have hUV' : aX ≫ (f ≫ g) = (schemeSpaceMap ψ ≫ schemeSpaceMap χ) ≫ cZ := by
    rw [← Category.assoc, htop, Category.assoc, hUV, Category.assoc]
  exact mono_modulePullback_map_of_mono_chartComparison B S hS f g (f ≫ g)
    bY (schemeSpaceMap χ) cZ aX (schemeSpaceMap ψ ≫ schemeSpaceMap χ) cZ
    (schemeSpaceMap ψ) (𝟙 (schemeSpace W)) hbY hcZ haX hcZ
    hUV hUV' (Category.comp_id _).symm htop
    (isSheafOfDifferentialsMap_pullbackDifferentialsMap B S hS f g)
    (hscheme U V W ψ χ hmono)

/-- **Stacks 06BI**, granted only
`AlgebraicGeometry.Space.IsSchemeTriangleDifferentialsMono` — the case of a triangle of schemes
of the site.

For a formally smooth `f : X ⟶ Y` and any `g : Y ⟶ B` the transitivity sequence
`0 ⟶ f^*Ω_{Y/B} ⟶ Ω_{X/B} ⟶ Ω_{X/Y} ⟶ 0` of Stacks 05Z8 is short exact.  The étale
localization is carried out in
`AlgebraicGeometry.Space.pullbackDifferentialsMapChartComparison_of_schemeTriangle` and nothing
of it is assumed. -/
theorem triangleDifferentials_shortExact_of_schemeTriangle
    (hscheme : IsSchemeTriangleDifferentialsMono B S hS) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : FormallySmooth f.hom) :
    ∃ h : pullbackDifferentialsMap B S hS f g ≫ toRelativeDifferentials B S hS f g = 0,
      (ShortComplex.mk _ _ h).ShortExact :=
  triangleDifferentials_shortExact B S hS f g hf
    (pullbackDifferentialsMapChartComparison_of_schemeTriangle B S hS hscheme f g)

end AlgebraicGeometry.Space

end
