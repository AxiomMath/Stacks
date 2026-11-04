module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction

/-!
# Restriction of an étale pullback to the identity chart of the source

Let `g : U ⟶ U'` be a morphism of the big fppf site over `S` whose morphism of schemes `T_g` is
étale, so that the induced morphism `h_U ⟶ h_{U'}` of represented algebraic spaces is étale and
the pullback of modules along it is plain restriction of sections (Stacks 03LW,
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`).  An `𝒪_{h_{U'}}`-module `M` can
then be read on the Zariski site of the scheme underlying `U` in two ways: restrict `M` to the
étale chart `AlgebraicGeometry.Space.etaleHomChart` of `h_{U'}` cut out by `g`, or pull `M` back
to `h_U` and restrict the result to the identity chart
`AlgebraicGeometry.Space.selfChart` of `h_U`.

This file proves that the two are **the same module**, not merely isomorphic ones, and deduces
the comparison in the form the pullback of Stacks 03LU takes.

## Main results

* `AlgebraicGeometry.Space.chartRestrictionPresheaf_etaleModulePullback_selfChart`: the
  identification before sheafification, which is where all the content is.
* `AlgebraicGeometry.Space.restrictToChart_etaleModulePullback_selfChart`: **the restriction to
  the identity chart of `h_U` of the étale pullback of `M` is the restriction of `M` to the
  chart `g`**, as an equality of sheaves of modules on the scheme underlying `U`.
* `AlgebraicGeometry.Space.representedZariskiRestriction_etaleModulePullback`: the same
  statement in the spelling of
  `AlgebraicGeometry.Space.representedZariskiRestriction`.
* `AlgebraicGeometry.Space.restrictToChartModulePullbackSelfChartIso`: the comparison for the
  pullback of modules of Stacks 03LU, obtained from the equality by Stacks 03LW.

## Implementation notes

The identification is an equality because both sides are the Zariski sheafification of one and
the same presheaf of modules.  Three things hold on the nose, and the first two are the two
halves recorded in `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedZariskiRestriction.lean`:
the index functor of the identity chart of `h_U`, composed with postcomposition along the
morphism of spaces (`AlgebraicGeometry.Space.chartOpens_selfChart_comp_smallEtalePostcomp`), is
the index functor of the chart `g`; the two change-of-scalars maps are the same term
(`AlgebraicGeometry.Space.chartRestrictionRingHom_selfChart_eq_etaleHomChart`); and the étale
pullback is itself a `CategoryTheory.SheafOfModules.pushforward` along that postcomposition with
the identity as its structure map, so what remains is the collapse of two presheaf pushforwards
into one together with the commutation of the universe lift of the sections with a pushforward.

That last step is `Stacks.SheafOfModules.pushforward_ulift_pushforward_id` of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeRestrictionEtalePullback.lean`, which states it
for four bare pieces of data; the definitional check it performs is therefore small enough to
instantiate, whereas instantiating the collapse directly at the chart runs the check through the
whole of `AlgebraicGeometry.Space.restrictToChart`.

What makes the instantiation go through here is that the presheaf being sheafified is named:
`AlgebraicGeometry.Space.chartRestrictionPresheaf` carries, inside its own definition, the two
categories of presheaves of modules that the pushforward needs.  Spelling the same presheaf out
as `CategoryTheory.PresheafOfModules.pushforward` of a lifted module in the *statement* of a
lemma does not elaborate at all: the structure sheaf of the small étale site is named there
through `Stacks.SheafOfModules.Tensor.ringSheaf` of the structure sheaf of
`AlgebraicGeometry.Space.smallEtaleRingedSite`, and instance search does not find
`CategoryTheory.Category (CategoryTheory.PresheafOfModules ...)` for that spelling — the
obstruction recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleRestriction.lean`.  So the identification is
stated at `chartRestrictionPresheaf` and transported under the sheafification by a single
`congrArg`, as in `AlgebraicGeometry.Space.restrictToChartScheme_etaleModulePullback_idEtaleChart`.

The two sheafification instances for the Zariski site of the scheme underlying `U` are restated
from its essential smallness exactly as in `AlgebraicGeometry.Space.restrictToChart`; both
classes are propositions, so which term is used is immaterial.

What is **not** here is the identification of the restriction to the chart `g` with the Zariski
pullback along `T_g` of the restriction to the identity chart of `h_{U'}`.  That is the chartwise
comparison `AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison`, which is only a
morphism; it is an isomorphism for a quasi-coherent module by the conditions of Stacks 03M0, and
those are stated for `AlgebraicGeometry.Space.restrictToChartScheme`, the parallel construction
of `StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleRestriction.lean`, which is not
definitionally equal to `AlgebraicGeometry.Space.restrictToChart` — the change-of-scalars map of
the latter carries a `CategoryTheory.eqToHom` which the former does not.  So the represented case
of `AlgebraicGeometry.Space.ChartRestrictionBaseChange` does not follow from what is below.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 060S](https://stacks.math.columbia.edu/tag/060S)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe m u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U U' : BigFppfOver B S hS}

/-- **The presheaf of modules underlying the two restrictions is the same.**  Let `g : U ⟶ U'`
be a morphism of the big fppf site with étale morphism of schemes.  The sections of the étale
pullback of `M` over the Zariski opens of `U`, read as étale charts of `h_U`, are the sections of
`M` over those opens read as étale charts of `h_{U'}` through `g`, over the same ring of regular
functions.

Both sides are a pushforward of presheaves of modules; the index functors agree by
`AlgebraicGeometry.Space.chartOpens_selfChart_comp_smallEtalePostcomp` and the changes of scalars
by `AlgebraicGeometry.Space.chartRestrictionRingHom_selfChart_eq_etaleHomChart`, so this is the
collapse of two pushforwards into one, which is
`Stacks.SheafOfModules.pushforward_ulift_pushforward_id`. -/
theorem chartRestrictionPresheaf_etaleModulePullback_selfChart (g : U ⟶ U')
    (hg : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map g))
    (hU : IsAlgebraicSpace B S hS (yoneda.obj U))
    (hU' : IsAlgebraicSpace B S hS (yoneda.obj U'))
    (M : Modules.{u, m} B S hS (yoneda.obj U') hU') :
    chartRestrictionPresheaf B S hS hU
        ((etaleModulePullback B S hS (schemeSpaceMap g)
          (isEtale_schemeSpaceMap B S hS U g hg)).obj M) (selfChart B S hS U) =
      chartRestrictionPresheaf B S hS hU' M (etaleHomChart B S hS U g hg) :=
  Stacks.SheafOfModules.pushforward_ulift_pushforward_id
    (F := chartOpens B S hS (selfChart B S hS U))
    (G := smallEtalePostcomp B S hS (schemeSpaceMap g)
      (isEtale_schemeSpaceMap B S hS U g hg))
    (K := (smallEtaleRingedSite B S hS (yoneda.obj U) hU).J)
    (L := (smallEtaleRingedSite B S hS (yoneda.obj U') hU').J)
    (R := Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (yoneda.obj U') hU').O)
    (hcont := smallEtaleRingedSite_isContinuous_smallEtalePostcomp B S hS
      (schemeSpaceMap g) (isEtale_schemeSpaceMap B S hS U g hg))
    (chartRestrictionRingHom B S hS hU' (etaleHomChart B S hS U g hg)) M

/-- **The restriction to the identity chart of `h_U` of the étale pullback of `M` is the
restriction of `M` to the chart cut out by `g`.**  Let `g : U ⟶ U'` be a morphism of the big fppf
site whose morphism of schemes is étale and let `M` be an `𝒪_{h_{U'}}`-module.  Then the two
readings of `M` on the Zariski site of the scheme underlying `U` — restrict the étale pullback of
`M` to the identity chart `AlgebraicGeometry.Space.selfChart` of `h_U`, or restrict `M` itself to
the chart `AlgebraicGeometry.Space.etaleHomChart` of `h_{U'}` — are equal, not merely isomorphic.

No hypothesis on `M` is needed: both sides are the Zariski sheafification of the single presheaf
of `AlgebraicGeometry.Space.chartRestrictionPresheaf_etaleModulePullback_selfChart`. -/
theorem restrictToChart_etaleModulePullback_selfChart (g : U ⟶ U')
    (hg : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map g))
    (hU : IsAlgebraicSpace B S hS (yoneda.obj U))
    (hU' : IsAlgebraicSpace B S hS (yoneda.obj U'))
    (M : Modules.{u, m} B S hS (yoneda.obj U') hU') :
    restrictToChart B S hS hU
        ((etaleModulePullback B S hS (schemeSpaceMap g)
          (isEtale_schemeSpaceMap B S hS U g hg)).obj M) (selfChart B S hS U) =
      restrictToChart B S hS hU' M (etaleHomChart B S hS U g hg) := by
  let : HasSheafify
      (Opens.grothendieckTopology ((BigFppfOver.toScheme B S hS).obj U))
      AddCommGrpCat.{max u m} :=
    hasSheafifyEssentiallySmallSite _ _
  let : (Opens.grothendieckTopology
        ((BigFppfOver.toScheme B S hS).obj U)).WEqualsLocallyBijective
      AddCommGrpCat.{max u m} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  exact congrArg
    (PresheafOfModules.sheafification
      (𝟙 ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf.obj)).obj
    (chartRestrictionPresheaf_etaleModulePullback_selfChart B S hS g hg hU hU' M)

/-- `AlgebraicGeometry.Space.restrictToChart_etaleModulePullback_selfChart` in the spelling of
`AlgebraicGeometry.Space.representedZariskiRestriction`: the comparison of the modules of the
algebraic space represented by `U` with the modules of the representing scheme, applied to the
étale pullback of `M`, is the restriction of `M` to the chart `g`. -/
theorem representedZariskiRestriction_etaleModulePullback (g : U ⟶ U')
    (hg : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map g))
    (hU : IsAlgebraicSpace B S hS (yoneda.obj U))
    (hU' : IsAlgebraicSpace B S hS (yoneda.obj U'))
    (M : Modules.{u, u} B S hS (yoneda.obj U') hU') :
    representedZariskiRestriction B S hS U hU
        ((etaleModulePullback B S hS (schemeSpaceMap g)
          (isEtale_schemeSpaceMap B S hS U g hg)).obj M) =
      restrictToChart B S hS hU' M (etaleHomChart B S hS U g hg) :=
  restrictToChart_etaleModulePullback_selfChart B S hS g hg hU hU' M

/-- **The comparison for the pullback of modules of Stacks 03LU.**  For a morphism `g : U ⟶ U'`
of the big fppf site whose morphism of schemes is étale, the restriction to the identity chart of
`h_U` of the pullback of `M` along the represented morphism of algebraic spaces is isomorphic to
the restriction of `M` to the chart cut out by `g`.

This is `AlgebraicGeometry.Space.restrictToChart_etaleModulePullback_selfChart` preceded by
Stacks 03LW, `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`, which replaces the
pullback of Stacks 03LU by étale restriction. -/
noncomputable def restrictToChartModulePullbackSelfChartIso (g : U ⟶ U')
    (hg : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map g))
    (hU : IsAlgebraicSpace B S hS (yoneda.obj U))
    (hU' : IsAlgebraicSpace B S hS (yoneda.obj U'))
    (M : Modules.{u, u} B S hS (yoneda.obj U') hU') :
    restrictToChart B S hS hU ((modulePullback B S hS (schemeSpaceMap g)).obj M)
        (selfChart B S hS U) ≅
      restrictToChart B S hS hU' M (etaleHomChart B S hS U g hg) :=
  restrictToChartIso B S hS hU
      ((modulePullbackIsoEtaleModulePullback B S hS (schemeSpaceMap g)
        (isEtale_schemeSpaceMap B S hS U g hg)).app M) (selfChart B S hS U) ≪≫
    eqToIso (restrictToChart_etaleModulePullback_selfChart B S hS g hg hU hU' M)

end AlgebraicGeometry.Space

end
