module

public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.EtaleBase
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModule
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts

/-!
# The target chart does not matter for relative flatness of a module on an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site, let `F`
be an `𝒪_X`-module and let `U` be an étale scheme chart of `X`.  Flatness of `F` over `Y` at a
point of `U` is read on a commuting square of étale scheme charts of `f`
(`AlgebraicGeometry.Space.ChartDiagram`): the restriction `F|_U` is flat, at that point, over
the chart `V` of `Y` through which the square sends `U`.  This file proves that the condition
does not depend on `V` nor on the morphism `U ⟶ V`: the relative flat locus of `F|_U` is one
and the same subset of `U` for every square with source chart `U`.

Two étale charts `V`, `V'` of `Y` receiving `U` have a common refinement `V ×_Y V'`, which is
again an étale chart of `Y` because an étale chart is a representable morphism all of whose
represented base changes are étale; this is
`AlgebraicGeometry.Space.SmallEtale.prodObj`.  The two projections are étale morphisms of
schemes, and `U` maps to the refinement compatibly with its two given morphisms, so both
readings of the condition agree with the reading over `V ×_Y V'` by Stacks 05B9,
`AlgebraicGeometry.isFlatOverAt_comp_iff_of_etale`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.flatLocus_restrictToChart_eq`: the relative flat locus of the
  restriction of `F` to an étale scheme chart `U` of `X` is independent of the chart of `Y` and
  of the morphism of charts through which flatness over `Y` is read.
* `AlgebraicGeometry.Space.isFlatOverOnChartDiagram_iff_of_source_eq`: consequently the
  condition `AlgebraicGeometry.Space.IsFlatOverOnChartDiagram` defining
  `AlgebraicGeometry.Space.IsFlatOver` of Stacks 05VV on one commuting square of étale scheme
  charts depends on the square only through its chart of `X`.

## Implementation notes

**This is not Stacks 05VU, and no declaration here carries that tag.**  Stacks 05VU asserts
that the condition of its clause (1) — *there exists* a commuting square of étale scheme charts
through a point of `|X|` on which `F` is flat over the target — is equivalent to flatness of the
geometric stalk `F_{x̄}` over the étale local ring `𝒪_{Y, ȳ}`, and hence that the condition
depends on neither chart of the square.  What is proved here is the independence of the chart of
`Y` only.  Independence of the chart of `X` is a strictly stronger statement and is *false* for
a general `𝒪_X`-module: for two étale charts `U`, `U'` of `X` the modules `F|_U` and `F|_{U'}`
are unrelated unless `F` is cartesian on the small étale site, and chartwise quasi-coherence of
the restrictions — which is all that the consumers of this predicate assume, and all that
Stacks 05VU's hypothesis amounts to in this development — does not give cartesianity.  The
missing input is, precisely, the comparison identifying `F|_{U'}` with the pullback along
`U' ⟶ U` of `F|_U`, equivalently the comparison of `AlgebraicGeometry.Space.restrictToChart`
with the chartwise pullback `AlgebraicGeometry.Space.chartModuleRestriction` of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleChartModuleGlueing.lean`, which *is* cartesian
for free by `AlgebraicGeometry.Space.chartModuleRestrictionComp`.  That comparison *is*
available for a module quasi-coherent on the small étale site, as
`AlgebraicGeometry.Space.nonempty_restrictToChartScheme_chartBaseChange` of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeRestrictionEtalePullback.lean` read through the
identification of the two readings,
`AlgebraicGeometry.Space.restrictToChartIsoRestrictToChartScheme` of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionReadingsIso.lean`.  What is unavailable is
the comparison under chartwise quasi-coherence alone, which is the hypothesis this file works
under; the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/GeometricStalkBaseChange.lean` record the same gap.

For a *quasi-coherent* module the comparison is not needed to obtain independence of the chart
of `X`: Stacks 05VU identifies the condition at a point of a chart with flatness of the
geometric stalk there, which mentions no chart, and
`AlgebraicGeometry.Space.isFlatOver_iff_forall_isFlatOverAtGeometricPoint` of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleGeometricPointCriterion.lean` draws that
conclusion.  What is false is the statement for a module carrying no hypothesis beyond
chartwise quasi-coherence of its restrictions, which is all this file assumes.

The quasi-coherence hypothesis is the chartwise one:
`AlgebraicGeometry.isFlatOverAt_comp_iff_of_etale` needs the module on the source scheme to be
quasi-coherent, and the module on the source scheme is
`AlgebraicGeometry.Space.restrictToChart`.  It is taken as an explicit hypothesis rather than
as an instance, as it is in
`StacksFrontier/AlgebraicGeometry/Spaces/FlatFiniteTypeModuleLocus.lean`.

The common refinement is `AlgebraicGeometry.Space.SmallEtale.prodObj`, whose underlying object
of the big fppf site is a represented base change; the morphism from `U` into it is the
universal morphism `CategoryTheory.Functor.relativelyRepresentable.lift'` of that base change,
which is available because `U` is itself an object of the big fppf site even though it is not an
étale chart of `Y`.  Étaleness of the two projections is read off
`AlgebraicGeometry.Space.etale_of_comp_etale_chart`, part (2) of Stacks 03EC, rather than from
the base change, so that the two projections are treated alike.

The module universe is the universe of the structure rings, as it must be for
`AlgebraicGeometry.Space.restrictToChart` to land in `AlgebraicGeometry.Scheme.Modules` of the
chart; this is the convention of `AlgebraicGeometry.Space.IsFlatOver`.

## References

* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 05B9](https://stacks.math.columbia.edu/tag/05B9)
* [Stacks Project, Tag 03EC](https://stacks.math.columbia.edu/tag/03EC)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The chart of the target is immaterial.** Let `F` be a module on an algebraic space `X`,
let `U` be an étale scheme chart of `X` whose restriction `F|_U` is quasi-coherent, and let
`h : U ⟶ V` and `h' : U ⟶ V'` be two morphisms into étale scheme charts of `Y` making the square
over `f : X ⟶ Y` commute.  Then `F|_U` has the same relative flat locus over `V` as over `V'`.

This is the independence of the chart of `Y` in clause (1) of Stacks 05VU; independence of the
chart of `X` is a different matter, see the implementation notes. -/
theorem flatLocus_restrictToChart_eq (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y}
    (F : Modules.{u, u} B S hS X hX) (U : SmallEtale B S hS X)
    (hqc : (restrictToChart B S hS hX F U).IsQuasicoherent)
    {V V' : SmallEtale B S hS Y}
    (h : (SmallEtale.toOver B S hS X).obj U ⟶ (SmallEtale.toOver B S hS Y).obj V)
    (h' : (SmallEtale.toOver B S hS X).obj U ⟶ (SmallEtale.toOver B S hS Y).obj V')
    (hcomm : U.1.hom ≫ f = yoneda.map h ≫ V.1.hom)
    (hcomm' : U.1.hom ≫ f = yoneda.map h' ≫ V'.1.hom) :
    _root_.AlgebraicGeometry.flatLocus ((BigFppfOver.toScheme B S hS).map h)
        (restrictToChart B S hS hX F U) =
      _root_.AlgebraicGeometry.flatLocus ((BigFppfOver.toScheme B S hS).map h')
        (restrictToChart B S hS hX F U) := by
  have := hqc
  -- The common refinement `V ×_Y V'` of the two charts of `Y`, with its two projections.
  set W : SmallEtale B S hS Y := SmallEtale.prodObj B S hS Y V V'
  set p : W ⟶ V := SmallEtale.prodFst B S hS Y V V'
  set q : W ⟶ V' := SmallEtale.prodSnd B S hS Y V V'
  -- The morphism from `U` into the refinement induced by the two given morphisms.
  have hboth : yoneda.map h ≫ V.1.hom = yoneda.map h' ≫ V'.1.hom := hcomm.symm.trans hcomm'
  set l : (SmallEtale.toOver B S hS X).obj U ⟶ (SmallEtale.toOver B S hS Y).obj W :=
    V.property.rep.lift' h h' hboth
  -- Reading over `V₀` through a projection `W ⟶ V₀` agrees with reading over `W`, since the
  -- projection is étale by part (2) of Stacks 03EC.
  have key : ∀ (V₀ : SmallEtale B S hS Y) (p₀ : W ⟶ V₀)
      (g : (SmallEtale.toOver B S hS X).obj U ⟶ (SmallEtale.toOver B S hS Y).obj V₀),
      l ≫ (SmallEtale.toOver B S hS Y).map p₀ = g →
      _root_.AlgebraicGeometry.flatLocus ((BigFppfOver.toScheme B S hS).map g)
          (restrictToChart B S hS hX F U) =
        _root_.AlgebraicGeometry.flatLocus ((BigFppfOver.toScheme B S hS).map l)
          (restrictToChart B S hS hX F U) := by
    intro V₀ p₀ g hg
    have : Etale ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS Y).map p₀)) :=
      etale_of_comp_etale_chart B S hS W.property V₀.property (CostructuredArrow.w p₀.hom)
    rw [← hg, Functor.map_comp]
    exact Set.ext fun u => _root_.AlgebraicGeometry.isFlatOverAt_comp_iff_of_etale _ _ _ u
  rw [key V p h (V.property.rep.lift'_fst h h' hboth),
    key V' q h' (V.property.rep.lift'_snd h h' hboth)]

/-- The chartwise condition defining `AlgebraicGeometry.Space.IsFlatOver` of Stacks 05VV on one
commuting square of étale scheme charts depends on the square only through its chart of `X`. -/
theorem isFlatOverOnChartDiagram_iff_of_source_eq (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y}
    (F : Modules.{u, u} B S hS X hX)
    (hqc : ∀ U : SmallEtale B S hS X, (restrictToChart B S hS hX F U).IsQuasicoherent)
    (d d' : ChartDiagram B S hS X Y f) (hU : d.U = d'.U) :
    IsFlatOverOnChartDiagram B S hS hX F d ↔ IsFlatOverOnChartDiagram B S hS hX F d' := by
  obtain ⟨U, V, h, hcomm⟩ := d
  obtain ⟨U', V', h', hcomm'⟩ := d'
  subst hU
  have hset := flatLocus_restrictToChart_eq B S hS hX F U (hqc U) h h' hcomm hcomm'
  exact ⟨fun hflat u => (Set.ext_iff.mp hset u).mp (hflat u),
    fun hflat u => (Set.ext_iff.mp hset u).mpr (hflat u)⟩

end AlgebraicGeometry.Space

end
