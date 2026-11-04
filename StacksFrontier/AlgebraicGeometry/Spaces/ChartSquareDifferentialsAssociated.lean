module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceDerivationSchemeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleLocalization

/-!
# The inverse image of `Ω_{Y/B}` on a square of étale scheme charts, as an associated module

Let `q : Y ⟶ Bb` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, and let

```
W --k--> V
|        |
w        v
v        v
Y --q--> Bb
```

be a commuting square in which `W` and `V` are objects of the big fppf site, `k` is a morphism
of the site and the two vertical arrows are étale.  This file identifies the inverse image of
`Ω_{Y/B}` along `w`, and along a further morphism `r : T ⟶ W` of the site, with the module
`Mᵃ` of [Stacks Project, Tag 03DU] (4) of a *Zariski* module on the scheme underlying `T`:

`(r ≫ w)^*Ω_{Y/Bb} ≅ ((r_{sch})^*Ω_{W/V})ᵃ`.

Three isomorphisms of the library compose to give it, and nothing else is needed:

* [Stacks Project, Tag 04CU], `AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso`,
  identifies `w^*Ω_{Y/Bb}` with the spaces-level `Ω` of the morphism of represented algebraic
  spaces of `k`;
* [Stacks Project, Tag 04CS] in its *named* form,
  `AlgebraicGeometry.Space.representedAssociatedDifferentialsIso`, identifies that with the
  associated module of the Zariski `Ω_{W/V}` — the tag's own
  `AlgebraicGeometry.Space.sheafOfDifferentialsSchemeComparison` produces its isomorphism inside
  a `Nonempty`, which a consumer reading sections through it cannot use;
* `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` carries the inverse image
  along a morphism of represented algebraic spaces of an associated module to the associated
  module of the Zariski inverse image, with no quasi-coherence hypothesis.

## Why this is wanted

It is the source half of the comparison which step (II) of [Stacks Project, Tag 04AM] needs.
The action of the acting sheaf of [Stacks Project, Tag 061D] on the sheaf of lifts is
constructed over an étale scheme chart in
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheafAction`, and the acting object
there — `AlgebraicGeometry.Space.ChartLiftPresentation.ActionSection` — has the *Zariski* module
`a^*Ω_{W/V}` of the chart square as its source, while
`AlgebraicGeometry.Space.liftActionSheaf` has the small-étale `a^*Ω_{Y/Bb}`.  Exhibiting the
latter, restricted to the chart, as the associated module of the former is what turns the two
geometric comparisons into a comparison of acting groups: the passage from an isomorphism of
associated modules to a bijection of *morphisms* is
`AlgebraicGeometry.Space.representedAssociatedModuleHomEquivLinearMap`
(`StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModuleFullyFaithful`), which carries
nothing — the small étale half of [Stacks Project, Tag 0GN7] holding unconditionally over an
arbitrary scheme.

That comparison is complete.  `AlgebraicGeometry.Space.chartDifferentialsAssociatedCotangentIso`
(`StacksFrontier.AlgebraicGeometry.Spaces.ChartSquareDifferentialsChartPullback`) restates the
composite below at a chart of the source and at the `Stacks.Smooth.pullbackCotangentSheaf`
spelling the chart presentation of a lifting problem uses, and
`AlgebraicGeometry.Space.ChartLiftPresentation.actionSectionEquiv`
(`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftActionSheafActionSection`) is the finished
identification of the sections of the acting sheaf at the presented chart with
`AlgebraicGeometry.Space.ChartLiftPresentation.ActionSection`.

## Main definitions

* `AlgebraicGeometry.Space.chartSquareDifferentialsAssociatedIso`: **`w^*Ω_{Y/Bb} ≅ (Ω_{W/V})ᵃ`
  over a square of étale charts.**
* `AlgebraicGeometry.Space.chartPullbackDifferentialsAssociatedIso`: the same pulled back along
  a further morphism `r : T ⟶ W` of the site, as a composite of two inverse images.
* `AlgebraicGeometry.Space.chartCompositeDifferentialsAssociatedIso`: **the same at a single
  morphism `c : T ⟶ Y` of algebraic spaces presented as `r ≫ w`**, which is the form the chart
  presentation of a lifting problem supplies: there the composite is the reduction of the
  presented lift followed by the chart of `Y`, and the hypothesis `hc` is the clause of
  `AlgebraicGeometry.Space.IsChartLift` saying that the lift agrees with `a` on the closed
  subscheme of the chart.

## Implementation notes

No `@[stacks]` attribute is claimed.  Tags 04CU and 04CS are registered at the two isomorphisms
composed here, and Tag 03LU's composition comparison at
`AlgebraicGeometry.Space.modulePullbackCompIso`; what this file adds is their composite in the
spelling the chart presentation of a lifting problem produces.

The composite is assembled from the three isomorphisms with no rewriting and no computation of
any factor: each is applied at the module and morphism arguments the next one expects, so the
whole file checks in under a second.  In particular the comparison of the two inverse images is
moved by `CategoryTheory.Functor.mapIso` rather than by `rw`, and the change of the composite
morphism is a single `eqToIso` on `c`, formed outside the inverse-image functor so that no
transport has to be crossed underneath it.

`AlgebraicGeometry.Space.schemeSpaceMap` and
`AlgebraicGeometry.Space.representedSpaceMap` are the same morphism of represented algebraic
spaces, both being `CategoryTheory.ObjectProperty.homMk (yoneda.map g)`; the statements below are
written at the former, which is the spelling
`AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso` and
`AlgebraicGeometry.Space.representedAssociatedDifferentialsIso` are stated in, and the latter
appears only inside the proof term, where
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` wants it.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] BigFppfSite.hasPullbacks_schemes

variable {Bb Y : AlgebraicSpaces B S hS} {W V : BigFppfOver B S hS}

/-- **The inverse image of `Ω_{Y/Bb}` along an étale scheme chart of `Y` is the associated module
of the Zariski sheaf of differentials of the chart square.**  For a commuting square
`w ≫ q = k ≫ v` of algebraic spaces whose vertical arrows `w : W ⟶ Y` and `v : V ⟶ Bb` are
étale charts by objects of the big fppf site,

`w^*Ω_{Y/Bb} ≅ (Ω_{W/V})ᵃ`.

This is [Stacks Project, Tag 04CU] followed by the named form of [Stacks Project, Tag 04CS]. -/
def chartSquareDifferentialsAssociatedIso (q : Y ⟶ Bb)
    (w : schemeSpace W ⟶ Y) (v : schemeSpace V ⟶ Bb) (k : W ⟶ V)
    (hw : IsEtale B S hS w.hom) (hv : IsEtale B S hS v.hom)
    (hsq : w ≫ q = schemeSpaceMap k ≫ v) :
    (modulePullback B S hS w).obj (sheafOfDifferentials B S hS q) ≅
      (representedAssociatedModule B S hS W (schemeSpace W).property).obj
        (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k)) :=
  sheafOfDifferentialsEtaleLocalizationIso B S hS q w (schemeSpaceMap k) v hw hv hsq ≪≫
    representedAssociatedDifferentialsIso B S hS k

/-- **The same, pulled back along a further morphism of the site.**  For `r : T ⟶ W`,

`r^*w^*Ω_{Y/Bb} ≅ ((r_{sch})^*Ω_{W/V})ᵃ`,

by `AlgebraicGeometry.Space.chartSquareDifferentialsAssociatedIso` followed by
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso`, which needs no
quasi-coherence. -/
def chartPullbackDifferentialsAssociatedIso (q : Y ⟶ Bb)
    (w : schemeSpace W ⟶ Y) (v : schemeSpace V ⟶ Bb) (k : W ⟶ V)
    (hw : IsEtale B S hS w.hom) (hv : IsEtale B S hS v.hom)
    (hsq : w ≫ q = schemeSpaceMap k ≫ v) {T : BigFppfOver B S hS} (r : T ⟶ W) :
    (modulePullback B S hS (schemeSpaceMap r)).obj
        ((modulePullback B S hS w).obj (sheafOfDifferentials B S hS q)) ≅
      (representedAssociatedModule B S hS T (schemeSpace T).property).obj
        ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).obj
          (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k))) :=
  (modulePullback B S hS (representedSpaceMap B S hS r)).mapIso
      (chartSquareDifferentialsAssociatedIso B S hS q w v k hw hv hsq) ≪≫
    representedAssociatedModulePullbackIso B S hS r
      (relativelyRepresentable_yoneda_map B S hS r) _

/-- **The inverse image of `Ω_{Y/Bb}` along a morphism of represented algebraic spaces which
factors through an étale chart square is an associated module.**  For `c : T ⟶ Y` with
`c = r ≫ w`,

`c^*Ω_{Y/Bb} ≅ ((r_{sch})^*Ω_{W/V})ᵃ`.

This is the form a chart presentation of a lifting problem supplies: `c` is the reduction of the
presented lift to the closed subscheme of the chart followed by the chart of `Y`, and the
factorization `hc` is what the lift clause of `AlgebraicGeometry.Space.IsChartLift` provides.
The two inverse images of
`AlgebraicGeometry.Space.chartPullbackDifferentialsAssociatedIso` are collapsed into one by
[Stacks Project, Tag 03LU], `AlgebraicGeometry.Space.modulePullbackCompIso`. -/
def chartCompositeDifferentialsAssociatedIso (q : Y ⟶ Bb)
    (w : schemeSpace W ⟶ Y) (v : schemeSpace V ⟶ Bb) (k : W ⟶ V)
    (hw : IsEtale B S hS w.hom) (hv : IsEtale B S hS v.hom)
    (hsq : w ≫ q = schemeSpaceMap k ≫ v) {T : BigFppfOver B S hS} (r : T ⟶ W)
    (c : schemeSpace T ⟶ Y) (hc : c = schemeSpaceMap r ≫ w) :
    (modulePullback B S hS c).obj (sheafOfDifferentials B S hS q) ≅
      (representedAssociatedModule B S hS T (schemeSpace T).property).obj
        ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).obj
          (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map k))) :=
  eqToIso (congrArg
      (fun g : schemeSpace T ⟶ Y =>
        (modulePullback B S hS g).obj (sheafOfDifferentials B S hS q)) hc) ≪≫
    ((modulePullbackCompIso B S hS (schemeSpaceMap r) w).app
      (sheafOfDifferentials B S hS q)).symm ≪≫
    chartPullbackDifferentialsAssociatedIso B S hS q w v k hw hv hsq r

end AlgebraicGeometry.Space

end
