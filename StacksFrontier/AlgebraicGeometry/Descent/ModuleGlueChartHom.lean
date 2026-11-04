module

public import StacksFrontier.AlgebraicGeometry.Descent.ModuleGlueChartAdjunct
public import StacksFrontier.AlgebraicGeometry.Descent.ModuleGlueChartIso
public import StacksFrontier.AlgebraicGeometry.Descent.ZariskiModuleChartComparison

/-!
# The chart comparisons of a glued module, as morphisms rather than on sections

`Stacks.SheafOfModules.ModulesGlueData` records the comparison of its glued module with its
chart modules twice: as the isomorphism of sheaves of modules
`...ModulesGlueData.chartIso`, and — read over an open `V` of the base inside the image of a
chart — as the isomorphism of modules of sections `...ModulesGlueData.chartSectionsIso`. The
statement that the comparisons for two different charts are **related to one another** by the
transition of the datum, which is what a construction of a morphism *out of* the glued module
needs, is available only in the second form: `...ModulesGlueData.trans_chartSectionsIso` and
`...ModulesGlueData.trans_chartAdjunct` are equations between maps on sections, because a
`ModulesGlueData` carries its transitions as linear equivalences of modules of sections and
nothing more.

This file converts that relation into an **equation of morphisms of sheaves of modules** for the
data built by `Stacks.SheafOfModules.ModulesGlueData.ofChartIso`, whose transitions do come from
morphisms.

## Why `ofChartIso` and not an arbitrary datum

For an arbitrary `ModulesGlueData` there is nothing to convert: `trans i j` is a family of linear
equivalences on sections indexed by the opens of the base, and no morphism of sheaves of modules
is given from which it comes. For `...ModulesGlueData.ofChartIso` there is: the transition is the
sections map of `AlgebraicGeometry.ofChartIsoHom` of the given comparison `β i j` of the chart
modules over the overlap of the two chart images, which is a morphism of the restrictions of the
two pushforwards. So the conversion is available exactly where a glueing argument produces its
datum from comparisons of the chart modules, which is the only way this repository produces one.

## The three steps are the ones a sibling file already uses

The passage is `AlgebraicGeometry.descentTransPullback_chartAdjunct` of
`StacksFrontier/AlgebraicGeometry/Descent/ZariskiModuleGlueDescent.lean` with the datum of a descent
datum replaced by the datum of a family of chart comparisons:
`AlgebraicGeometry.app_comp_localApp` turns the equation on sections over one open into an
equation of sections maps, `AlgebraicGeometry.restrictFunctor_map_comp_eq` assembles those over
all opens inside `V` into the equation of morphisms of restrictions, and
`AlgebraicGeometry.localAppFun_restrictLocal_le` is what makes the sections map over a smaller
open independent of the ambient open it is read at. Nothing else is used, and in particular no
new descent theory: the content is entirely `...ModulesGlueData.trans_chartAdjunct`.

## Main results

* `Stacks.SheafOfModules.ModulesGlueData.ofChartIso_restrictFunctor_map_chartAdjunct`: **the
  comparisons of the module glued by `...ModulesGlueData.ofChartIso` with its chart modules are
  related to one another by the given comparisons `β`, as an equation of morphisms of the
  restrictions to an open of the base inside the overlap of two chart images.** This is
  `...ModulesGlueData.ofChartIso_trans_chartSectionsIso` with the equation on sections replaced
  by an equation of morphisms of sheaves of modules.
* `...ModulesGlueData.ofChartIso_restrictLocal_chartAdjunct_apply`: the same at one open, as an
  equation of sections maps — the intermediate step, named because a consumer that works over a
  single open wants it rather than the morphism.

## No tag is claimed

Nothing here states a clause of a tag: the file restates a comparison this repository already
has, at the level of morphisms instead of sections.

## References

* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Tag 01NV](https://stacks.math.columbia.edu/tag/01NV)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

open AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

variable {S : Scheme.{u}} {ι : Type u} {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ S)
  [∀ i, IsOpenImmersion (f i)] (mod : ∀ i, (Y i).Modules)

namespace ModulesGlueData

variable (β : ∀ i j : ι,
    chartModule f mod i (inf_le_left : chartOverlap f i j ≤ (f i).opensRange) ≅
      chartModule f mod j (inf_le_right : chartOverlap f i j ≤ (f j).opensRange))
  (hcoc : ∀ i j k : ι,
    chartModuleRestrict f mod (chartTripleOverlap_le_fst f i j k) (β i j).hom ≫
        chartModuleRestrict f mod (chartTripleOverlap_le_snd f i j k) (β j k).hom =
      chartModuleRestrict f mod (chartTripleOverlap_le_out f i j k) (β i k).hom)

/-- **The comparisons of the glued module with the chart modules are related by the given
comparisons `β`, read as an equation of sections maps over one open.** Over an open `V'` of the
base inside an open `V` inside the overlap of the images of the `i`-th and the `j`-th chart,
reading a section of the glued module in the `i`-th chart and then applying the restriction to
`V` of `AlgebraicGeometry.ofChartIsoHom` of `β i j` gives the same as reading it in the `j`-th
chart.

This is `...ModulesGlueData.trans_chartAdjunct` for the datum, with its transition identified
with the sections map of the restricted comparison: the transition of
`...ModulesGlueData.ofChartIso` *is* that sections map, and
`AlgebraicGeometry.localAppFun_restrictLocal_le` moves it from the overlap to `V`. -/
theorem ofChartIso_restrictLocal_chartAdjunct_apply (i j : ι) {V V' : S.Opens}
    (hV : V ≤ chartOverlap f i j) (hV' : V' ≤ V)
    (s : ToType ((ofChartIso f mod β hcoc).glued.val.obj (op V'))) :
    localAppFun (restrictLocal (ofChartIsoHom f mod i j (β i j)).hom hV) V' hV'
        (((ofChartIso f mod β hcoc).chartAdjunct i).app V' s) =
      ((ofChartIso f mod β hcoc).chartAdjunct j).app V' s :=
  (localAppFun_restrictLocal_le (ofChartIsoHom f mod i j (β i j)).hom hV hV' _).symm.trans
    ((ofChartIso f mod β hcoc).trans_chartAdjunct i j
      ((hV'.trans hV).trans inf_le_left) ((hV'.trans hV).trans inf_le_right) s)

/-- **The comparisons of the module glued by `...ModulesGlueData.ofChartIso` with its chart
modules are related to one another by the given comparisons `β`, as an equation of morphisms of
sheaves of modules.** Over an open `V` of the base inside the overlap of the images of the `i`-th
and the `j`-th chart, the restriction to `V` of the transposed `i`-th comparison, followed by the
restriction to `V` of `AlgebraicGeometry.ofChartIsoHom` of `β i j`, is the restriction to `V` of
the transposed `j`-th comparison.

This is `...ModulesGlueData.ofChartIso_trans_chartSectionsIso` with the equation on sections
replaced by an equation of morphisms, which is the form in which a glueing argument whose local
data are morphisms of inverse images can consume it: a morphism of sheaves of modules *is* its
family of sections maps, so the two statements carry the same information, and the conversion is
`AlgebraicGeometry.app_comp_localApp` followed by
`AlgebraicGeometry.restrictFunctor_map_comp_eq`. -/
theorem ofChartIso_restrictFunctor_map_chartAdjunct (i j : ι) {V : S.Opens}
    (hV : V ≤ chartOverlap f i j) :
    (Scheme.Modules.restrictFunctor V.ι).map ((ofChartIso f mod β hcoc).chartAdjunct i) ≫
        restrictLocal (ofChartIsoHom f mod i j (β i j)).hom hV =
      (Scheme.Modules.restrictFunctor V.ι).map ((ofChartIso f mod β hcoc).chartAdjunct j) :=
  restrictFunctor_map_comp_eq _ _ _ fun _V' hV' =>
    app_comp_localApp hV' _ _ _
      (ofChartIso_restrictLocal_chartAdjunct_apply f mod β hcoc i j hV hV')

end ModulesGlueData

end Stacks.SheafOfModules

end
