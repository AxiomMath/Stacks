module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModulePullbackSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams

/-!
# Base change of the chart restriction of a quasi-coherent module

Let `a : X ⟶ Z` be a morphism of algebraic spaces over a scheme `S` of a big fppf site, let `G`
be a quasi-coherent `𝒪_Z`-module, let `V` be an étale scheme chart of `Z` and `W` an étale
scheme chart of `X`, and let `g` be a morphism of the underlying objects of the site which
commutes with the two chart structure morphisms through `a`.  This file proves that the Zariski
inverse image along `g` of the restriction `G|_V` is the restriction `(a^*G)|_W` of the inverse
image, where the restriction to a chart is the sheaf of modules
`AlgebraicGeometry.Space.restrictToChart` on the chart's scheme.

This is the compatibility of the chart restriction of Stacks 03M0 with the inverse image of
Stacks 03LW, and it is what
`AlgebraicGeometry.Space.ChartRestrictionBaseChange` of
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/ModuleFiniteness.lean` asks for.

## Main results

* `AlgebraicGeometry.Space.chartSmallEtaleRestrictionBaseChangeIso`: the same compatibility for
  the small étale reading of the chart restriction.
* `AlgebraicGeometry.Space.restrictToChartBaseChangeIso`: **the base change of the chart
  restriction of a quasi-coherent module.**

## Implementation notes

The statement is transported from the parallel construction
`AlgebraicGeometry.Space.restrictToChartScheme`, for which it is available, across the
identification `AlgebraicGeometry.Space.restrictToChartIsoRestrictToChartScheme` of the two
readings of the chart restriction.

The route is the one the source takes.  Both chart restrictions are chart
restrictions at the identity chart of a *represented* algebraic space, by
`AlgebraicGeometry.Space.restrictToChartSchemeIsoIdEtaleChart`, where the base change along an
arbitrary morphism of the big fppf category is
`AlgebraicGeometry.Space.restrictToChartSchemeBaseChangeIso`; what
remains is to identify the inverse image along the represented morphism of the small étale
restriction of `G` to `V` with the small étale restriction of `a^*G` to `W`, and that is the
commuting-square comparison `AlgebraicGeometry.Space.chartModuleRestrictionBaseChangeIso`, which
costs nothing beyond the composition comparison of Stacks 03LU.  The quasi-coherence of `a^*G`
which the second application of
`AlgebraicGeometry.Space.restrictToChartSchemeIsoIdEtaleChart` needs is Stacks 03GA along an
arbitrary morphism,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`.

**Every component is named, and none of them is a choice.**  The base-change step is not
`Nonempty.some` of
`AlgebraicGeometry.Space.nonempty_restrictToChartScheme_baseChange_of_isQuasicoherent`, which
would leave the isomorphism below with no description whatever: the witness that proof produces
is explicit and is the declaration
`AlgebraicGeometry.Space.restrictToChartSchemeBaseChangeIso`, so this isomorphism is a composite
of named isomorphisms and nothing else.

### What is still missing: a description of the isomorphism

A consumer that needs the *naturality in the stage* of the chart-sections identification
`AlgebraicGeometry.Space.chartRestrictionSheafTopEquiv` — Stacks 07SI does, for its two colimit
hypotheses — needs to know what this isomorphism *is*, and that is still not available.  It
cannot be a formula on sections: the left-hand side is a Zariski *pullback* of modules, a left
adjoint, whose sections no formula computes.  So the statement has to be the adjunct, and it
should be an equality of **morphisms of sheaves of modules** and descend to sections only
afterwards; the sections-level map a consumer eventually reads it at is
`AlgebraicGeometry.Space.chartPullbackSectionMap`, which does have value lemmas
(`AlgebraicGeometry.Space.modulePullbackSections_val` and
`AlgebraicGeometry.Space.sectionsMap_modulePullbackSections_val`).

What that costs: the five components below expand into seventeen distinct named
isomorphisms.  The substantial one is
`AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso`, inside
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` — which says the
associated-module functor of Stacks 03DU commutes with the Zariski pullback; its content on
sections is the base-change statement for sections of a module, which is of the same order as
the tags this file is an input to, not a lemma about this composite.  **It is
proved**, at arbitrary coefficients and with no quasi-coherence hypothesis:
`AlgebraicGeometry.SmallEtale.unit_comp_associatedModuleObjBaseChangeIso` is its adjunct square
and `AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso_hom_val_app_unit` its reading
on sections, both in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleMorphismBaseChange.lean`, the
general shape being `SheafOfModules.unit_comp_pullbackSquareIso_hom_app`.

**The three factors that look like obstructions are not obstructions, and what shows this is
the direction each of them is used in.**  The isomorphism below is
built with `AlgebraicGeometry.Space.restrictToChartSchemeBaseChangeIso` taken `.symm`, so what
occurs in its `hom` is that isomorphism's **inverse**; and in that inverse both adjunction maps
appear *forward*.  Read in order, the inverse is the Zariski-pullback image of
`AlgebraicGeometry.Space.restrictToChartSchemeIdEtaleChartIso`, then the **unit** of the
associated-module adjunction at the Zariski pullback
(`AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent`), then the unit of the represented
equivalence, then two comparisons of restriction functors, and finally the **counit**
(`AlgebraicGeometry.SmallEtale.isIso_counit`).  So the claim that those two admit no formula on
sections in either direction, true as it stands, is beside the point for this composite: neither
of them is inverted on the route a consumer takes, and the injectivity argument
`AlgebraicGeometry.SmallEtale.bijective_counit_val_app_of_isAffine` is not needed.

The third, `AlgebraicGeometry.Space.representedModulePullbackIso`, now has its adjunct square
outright, in both directions:
`AlgebraicGeometry.Space.unit_comp_representedModulePullbackIso_hom` and
`AlgebraicGeometry.Space.unit_comp_representedModulePullbackIso_inv` in
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModulePullbackBaseChange.lean`.  It is
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom` at the two now-named composite adjunctions
of that square, and it needs **no** value lemma for the comparison of right adjoints
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso`, which enters the equation by
name alone.  The expensive half of that factor is a cost of the
sections route and not of this one.

### What actually blocks the description

The adjunct of the isomorphism below is free and therefore says nothing on its own.  Its `hom` is
a morphism out of a Zariski pullback, so it is determined by
`unit ≫ g_*(hom)`; but `g_*` is a functor, so that composite is the composite of `g_*` of the
five named factors, which is the definition again.  A description is a statement that this
composite **equals something given independently** — and the thing it should equal is the chart
restriction of the unit `G ⟶ a_*a^*G` of Stacks 03LU, that is a morphism

  `restrictToChart G V ⟶ g_*(restrictToChart (a^*G) W)`.

**That morphism exists**, as `AlgebraicGeometry.Space.restrictToChartPushforwardHom` in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionPushforwardComparison.lean`, so its
absence is not what blocks.

**What blocks is one factor of the composite below**, and what isolates it is
`AlgebraicGeometry.Space.homEquiv_restrictToChartBaseChangeIso_hom` in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionBaseChangeAdjunct.lean`: four of the five
factors cost nothing in the adjunct — the pullback-image factor by
`CategoryTheory.Adjunction.homEquiv_naturality_left`, the three after the represented base change
by `CategoryTheory.Adjunction.homEquiv_naturality_right` — so the adjunct is the two readings of
the chart restriction, then the adjunct of the inverse of
`AlgebraicGeometry.Space.restrictToChartSchemeBaseChangeIso`, then the direct image of
`AlgebraicGeometry.Space.restrictToChartBaseChangeEtaleTail`.

Of those two remaining pieces the represented one is formal, for the reason the previous section
gives, and **it is now taken**:
`AlgebraicGeometry.Space.homEquiv_restrictToChartSchemeBaseChangeIso_inv` in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeRestrictionBaseChangeAdjunct.lean` is the
adjunct of the inverse of `AlgebraicGeometry.Space.restrictToChartSchemeBaseChangeIso`, and
`AlgebraicGeometry.Space.homEquiv_restrictToChartBaseChangeIso_hom_peeled` is the adjunct of the
isomorphism below with that substitution made.  So of the seventeen isomorphisms the adjunct now
costs nothing on every one except those inside
`AlgebraicGeometry.Space.restrictToChartBaseChangeEtaleTail`.

The obstruction is the other.  `AlgebraicGeometry.Space.restrictToChartPushforwardHom` is
built from the chart component of the unit of Stacks 03D7 **at `a`**, and nothing in the
represented half knows about `a`: it speaks only of the represented morphism of `g`.  The passage
from the one to the other happens in exactly one factor,
`AlgebraicGeometry.Space.chartSmallEtaleRestrictionBaseChangeIso`, which is
`AlgebraicGeometry.Space.chartModuleRestrictionBaseChangeIso` — two instances of the composition
comparison `AlgebraicGeometry.Space.modulePullbackCompIso` of Stacks 03LU.  So the comparison
needs the value of that comparison on the chart component of the unit of Stacks 03D7, which is
the compatibility recorded as missing in three places and named in those words by the "What is
not proved" section of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartBaseChangeEtaleSquareComparison.lean`.  Its adjunct
square is not what is missing —
`AlgebraicGeometry.Space.unit_comp_whiskerRight_modulePullbackCompIso_hom` is it — but the
passage from that square to a chart component is.

The square of charts is *not* assumed cartesian; the two charts are chosen independently and
only the commutation of the square is used.  Quasi-coherence of `G` is used twice over, once for
each application of the represented statement.

The module universe is the universe `u` of the structure rings, which is where
`AlgebraicGeometry.Scheme.Modules` of the chart scheme and the represented base-change statement
both live.

## References

* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Base change of the chart restriction -/

variable {X Z : AlgebraicSpaces B S hS}

/-- The inverse image along a represented morphism of étale chart objects of the small étale
restriction of `G` to a chart `V` of `Z` is the small étale restriction, to a chart `W` of `X`,
of the inverse image of `G` along `a`.

This is the commuting-square comparison `chartModuleRestrictionBaseChangeIso`, read through the
identification of the chart restriction of modules with the small étale restriction. -/
def chartSmallEtaleRestrictionBaseChangeIso (a : X ⟶ Z)
    (G : Modules.{u, u} B S hS Z.obj Z.property)
    (V : SmallEtale B S hS Z.obj) (W : SmallEtale B S hS X.obj)
    (g : W.obj.left ⟶ V.obj.left)
    (hg : yoneda.map g ≫ V.obj.hom = W.obj.hom ≫ a.hom) :
    (modulePullback B S hS (representedSpaceMap B S hS g)).obj
        (chartSmallEtaleRestriction B S hS Z G V) ≅
      chartSmallEtaleRestriction B S hS X ((modulePullback B S hS a).obj G) W :=
  (modulePullback B S hS (chartSpaceMapOver B S hS g)).mapIso
      (chartModuleRestrictionIsoChartSmallEtaleRestriction B S hS Z G V).symm ≪≫
    (chartModuleRestrictionBaseChangeIso B S hS a g hg).app G ≪≫
    chartModuleRestrictionIsoChartSmallEtaleRestriction B S hS X
      ((modulePullback B S hS a).obj G) W

/-- **The base change of the chart restriction of a quasi-coherent module.**  For a morphism
`a : X ⟶ Z` of algebraic spaces, a quasi-coherent `𝒪_Z`-module `G`, an étale scheme chart `V` of
`Z` and an étale scheme chart `W` of `X` joined by a morphism `g` of the underlying objects of
the site over `a`, the Zariski inverse image of `G|_V` along `g` is the restriction `(a^*G)|_W`
of the inverse image.

This is the compatibility of Stacks 03M0 with Stacks 03LW.  The square of charts is not assumed
cartesian.

**The isomorphism is a named composite of five named isomorphisms**, not a composite
involving `Nonempty.some`; what it does is still undescribed, and the implementation notes of
this file record what a statement of that would have to be and why the three factors that look
like obstructions are not obstructions — none of them is inverted on the route this composite
takes, and the one that is a comparison of left adjoints now has its adjunct square.

**The morphism the adjunct has to be compared with exists**; the adjunct of the composite
being formally free, this comparison is what a description needs.  It is
`AlgebraicGeometry.Space.restrictToChartPushforwardHom` in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionPushforwardComparison.lean`, assembled
from the chart components of the unit of the Stacks 03D7 adjunction, and its value on sections is
described by `AlgebraicGeometry.Space.chartRestrictionPushforwardHom_val_app`.  What remains
undone is the comparison itself: that the adjunct of this isomorphism *is* that morphism.

**Four of the five factors are discharged, and the fifth is the obstruction.**
`AlgebraicGeometry.Space.homEquiv_restrictToChartBaseChangeIso_hom` in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionBaseChangeAdjunct.lean` reduces the adjunct
to the adjunct of the represented base-change isomorphism, which is formal, together with the
direct image of `AlgebraicGeometry.Space.restrictToChartBaseChangeEtaleTail`; the obstruction is
the action of that tail on the chart component of the unit of Stacks 03D7, which is the
compatibility of the comparisons of Stacks 03LU and 03LW with that chart component.  See the
implementation notes of this file and of that one.

**It duplicates `AlgebraicGeometry.Space.chartRestrictionBaseChangeIso`** of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionBaseChangeConstruction.lean`, statement
for statement, under the same binders and in the same order; the two differ only in the route
taken through the identity chart.  They ought to be one declaration and are not merged because
neither module reaches the other through its `public import`s, and the merge would need a new
import edge.  The edge
`ChartRestrictionBaseChangeConstruction → ChartRestrictionBaseChange` adds 2 modules to that
module's closure of 4645 and the opposite edge adds 878 to this one's of 3769, so the merge is
cheap in exactly one direction.  Neither isomorphism is a choice, both going
through `AlgebraicGeometry.Space.restrictToChartSchemeBaseChangeIso`, so whichever survives will
have the same description to make. -/
def restrictToChartBaseChangeIso (a : X ⟶ Z)
    (G : Modules.{u, u} B S hS Z.obj Z.property) (hG : G.IsQuasicoherentOnSite)
    (V : SmallEtale B S hS Z.obj) (W : SmallEtale B S hS X.obj)
    (g : W.obj.left ⟶ V.obj.left)
    (hg : yoneda.map g ≫ V.obj.hom = W.obj.hom ≫ a.hom) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).obj
        (restrictToChart B S hS Z.property G V) ≅
      restrictToChart B S hS X.property ((modulePullback B S hS a).obj G) W :=
  (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).mapIso
      (restrictToChartIsoRestrictToChartScheme B S hS Z.property G V ≪≫
        restrictToChartSchemeIsoIdEtaleChart B S hS Z G hG V) ≪≫
    (restrictToChartSchemeBaseChangeIso g
      (chartSmallEtaleRestriction B S hS Z G V)
      (isQuasicoherentOnSite_chartSmallEtaleRestriction B S hS Z G hG V)).symm ≪≫
    (restrictToChartSchemeFunctor B S hS (yoneda.obj (chartFppfObject B S hS X W))
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (chartFppfObject B S hS X W))
      (idEtaleChart B S hS (chartFppfObject B S hS X W))).mapIso
        (chartSmallEtaleRestrictionBaseChangeIso B S hS a G V W g hg) ≪≫
    (restrictToChartSchemeIsoIdEtaleChart B S hS X ((modulePullback B S hS a).obj G)
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS a G hG) W).symm ≪≫
    (restrictToChartIsoRestrictToChartScheme B S hS X.property
      ((modulePullback B S hS a).obj G) W).symm

end AlgebraicGeometry.Space

end
