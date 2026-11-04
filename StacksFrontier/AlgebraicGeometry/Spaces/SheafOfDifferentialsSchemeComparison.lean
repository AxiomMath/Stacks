module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteEquivalenceTransport
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.CotangentSheafComparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Relative
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentials
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleLocalization

/-!
# The invertibility clause of Stacks 04CS for a morphism of schemes of the site

Let `S` be a scheme and let `α : U ⟶ V` be a morphism of the big fppf site over `S`.  Read as a
morphism of represented algebraic spaces, `α` has a sheaf of differentials
`AlgebraicGeometry.Space.sheafOfDifferentials` on the small étale site of `U`; the scheme `U`
also has the Zariski sheaf of relative differentials `Ω_{U/V}` of Stacks 01US, and the
associated-module functor of Stacks 03DU (4) carries the latter onto the small étale site.
Stacks 04CS asserts that the canonical comparison of the two is an isomorphism — the final
sentence of Stacks 04CU reads that way.

That clause is the single input which Stacks 04CV
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_sheafOfDifferentials`) and Stacks 04G9
(`AlgebraicGeometry.Space.formallyUnramified_iff_isZero_sheafOfDifferentials`) need.  This
file states it once, for an arbitrary morphism of schemes of the site and with no mention of a
morphism of algebraic spaces or of a chart, and derives from it the weaker form that Stacks 04G9
needs; `StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeTransport.lean` proves it,
which discharges that input for both tags.

## Main definitions

* `AlgebraicGeometry.Space.SheafOfDifferentialsSchemeComparison`: the invertibility clause of
  Stacks 04CS for every morphism of schemes of the site, the input of
  Stacks 04CV.
* `AlgebraicGeometry.Space.SheafOfDifferentialsSchemeVanishing`: that clause read at zero
  objects, the input of Stacks 04G9.
* `AlgebraicGeometry.Space.SchemeDifferentialsComparison`: the same clause spelled as a family
  of isomorphisms rather than as a `Prop`, which is the form the chart statement below consumes.

## Main results

* `AlgebraicGeometry.Space.faithful_representedModulePushforward` and
  `AlgebraicGeometry.Space.isZero_of_isZero_representedModulePushforward`: transport of modules
  along the equivalence of the small étale site of a scheme of the site with the small étale
  site of the algebraic space it represents is faithful, being the functor of an equivalence,
  and so reflects zero objects.
* `AlgebraicGeometry.Space.isZero_of_isZero_representedAssociatedModule`: the small-étale module
  attached to a *quasi-coherent* module on a scheme of the site is a zero object only if that
  module is.  Beyond the transport this is the unit of the associated-module adjunction being an
  isomorphism at the quasi-coherent modules, Stacks 070S (2) in the form
  `AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent`, which this tree proves with no
  hypothesis.
* `AlgebraicGeometry.Space.sheafOfDifferentialsSchemeVanishing_of_comparison`: **the clause
  implies the vanishing comparison** `Ω^{spaces}_α = 0 ↔ Ω_{U/V} = 0` of Stacks 04G9's carried
  hypothesis.  The sheaf of relative differentials of a morphism of schemes is quasi-coherent
  (Stacks 08S2), which is what makes the reflection applicable.
* `AlgebraicGeometry.Space.modulePullbackSheafOfDifferentialsChartIso`: granted that family, the
  restriction of `Ω_{X/Y}` to an étale chart of a commuting square is the small-étale module
  associated to the scheme-level sheaf of relative differentials of the square's scheme
  morphism — Stacks 04CU read through Stacks 04CS.

## What else is carried, and why none of it is this statement

Two statements in this tree are shadows of Stacks 04CS, and it is worth recording precisely how
each stands to the statement here.  One of them is no longer a hypothesis of anything; the other
is *not* a restatement of the statement here and does not follow from it.

* `AlgebraicGeometry.Space.SheafOfDifferentialsSchemeSiteComparison`
  (`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSmoothFiniteLocallyFree.lean:175`)
  transports *finite local freeness*, clause (2) of Stacks 03DL, across the two sites.  It is
  **no longer a hypothesis**: it is proved as
  `AlgebraicGeometry.Space.sheafOfDifferentialsSchemeSiteComparison`
  (`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSmoothFiniteLocallyFree.lean:199`)
  from the statement here together with Stacks 05VG for that clause at `τ = étale`,
  `AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOnSite_associatedModule`
  (`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleFiniteLocallyFree.lean:277`),
  which holds for every finite locally free module and not merely for the free ones, and
  Stacks 03DM at the comparison equivalence of Stacks 03DX (2),
  `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_representedSmallEtaleModule_iff`.
* `AlgebraicGeometry.Space.PullbackDifferentialsMapChartComparison`
  (`StacksFrontier/AlgebraicGeometry/Spaces/RelativeDifferentialsShortExact.lean`) is about
  *monomorphy of a map*: that monomorphy of the Zariski comparison map `ψ^*Ω_{U/V} ⟶ Ω_{U/W}` of
  a morphism of schemes of the site passes to the comparison map of Stacks 04CX of that morphism
  read between represented algebraic spaces over the base.  The statement here is a family of
  isomorphisms of objects with no compatibility asserted with that map, so no form of it
  transfers monomorphy.  The chart of `X`, the diagram of three charts and the étale base it
  used to quantify over are all gone:
  `AlgebraicGeometry.Space.mono_map_pullbackDifferentialsMap_iff_of_etaleChart`
  (`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsChartMonoReduction.lean`) proves
  the chart part from Stacks 05Z7 and the étale-localization clause of Stacks 04CU, and
  `AlgebraicGeometry.Space.mono_pullbackDifferentialsMap_of_etaleBase`
  (`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsMapTransport.lean`) proves the
  base part from the étale-base step of Stacks 04CU for the comparison map.  What remains
  granted is implied by the single naturality square
  `AlgebraicGeometry.Space.SchemeDifferentialsComparisonMapNaturality`
  (`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeComparisonMap.lean`).

## Implementation notes

**Stacks 04CS itself is now proved, schemes-side.**
`AlgebraicGeometry.SmallEtale.differentialsIso` in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleDifferentialsIso.lean` is the
canonical isomorphism `(Ω_{X/Y})^a ≅ Ω_{X_étale/Y_étale}` for a morphism of schemes of a big
étale site, with `AlgebraicGeometry.SmallEtale.postcomp_differentialsIso_hom` for its
compatibility with the universal derivations and
`AlgebraicGeometry.SmallEtale.isIso_universalDifferentialsComparison` saying that the comparison
map `c''` of this development is the invertible one.  There `Ω_{X_étale/Y_étale}` is
`AlgebraicGeometry.SmallEtale.sheafOfDifferentials`, the module of differentials of
`(AlgebraicGeometry.smallEtaleRingedToposHom B f).fSharpInverseImage` on the small étale site of
the *scheme* `X`.

`SheafOfDifferentialsSchemeComparison` below is not literally that statement: it names
`AlgebraicGeometry.Space.sheafOfDifferentials` of `schemeSpaceMap α`, the module of differentials
on the small étale site of the represented algebraic *space*.  **The transport between the two is
carried out in `StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeTransport.lean`,
and `AlgebraicGeometry.Space.sheafOfDifferentialsSchemeComparison` there proves the statement
below**, so neither it nor
`AlgebraicGeometry.Space.SheafOfDifferentialsSchemeVanishing` is carried by anything any more.
The transport carries no content about derivations: the equivalence
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence` identifies the two small étale sites
and its comparison of structure sheaves `AlgebraicGeometry.Space.representedStructureMap` is the
identity, and what the two sides have to be compared through is not the two morphisms of small
étale ringed topoi but the two descriptions of the class of relative derivations — the chartwise
pullbacks of regular functions on one side, the global functions pulled back along the
base-change projections on the other, both of which are pullbacks of regular functions along the
projection from a fibre product.

**Two spellings of the clause.**  `SheafOfDifferentialsSchemeComparison` is a `Prop`, asserting
`Nonempty` of the family of isomorphisms; `SchemeDifferentialsComparison` is that family itself.
The `Prop` form is the one `AlgebraicGeometry.Space.sheafOfDifferentialsSchemeComparison` of
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeTransport.lean` proves, and the
one every consumer of the clause as a hypothesis takes; the family form is what
`AlgebraicGeometry.Space.modulePullbackSheafOfDifferentialsChartIso` below needs, an
isomorphism being chosen there and not merely asserted to exist.

The vanishing comparison is derived, rather than carried alongside, because an isomorphism of
modules and the vanishing of one of them are not interchangeable: an additive functor carries a
zero object to a zero object, but reflecting zero objects needs faithfulness, and the
associated-module functor is faithful only on the quasi-coherent modules (Stacks 06VE (1)).  The
two steps are separated here for that reason.

## References

* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS), the comparison of the
  differentials of a morphism of schemes on its small Zariski and small étale sites.
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU), whose final sentence is
  that comparison read on a square of étale charts.
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU), the associated module on
  the small étale site and its right adjoint.
* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE), full faithfulness of the
  associated-module functor on the quasi-coherent modules.
* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2), quasi-coherence of the
  sheaf of relative differentials of a morphism of schemes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Transport of modules along the equivalence of small étale sites is faithful.**  It is the
functor of the equivalence of module categories that reindexing along an equivalence of ringed
sites provides, `Stacks.SheafOfModules.reindexEquivalence`: both are the pushforward along the
comparison of the two structure sheaves, which is the identity. -/
instance faithful_representedModulePushforward (U : BigFppfOver B S hS) :
    (representedModulePushforward B S hS U).Faithful :=
  Equivalence.faithful_functor (Stacks.SheafOfModules.reindexEquivalence
    (J' := SmallEtale.topology B S hS (yoneda.obj U))
    (representedSmallEtaleEquivalence B S hS U)
    (_root_.AlgebraicGeometry.SmallEtale.structureSheaf (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property))

/-- **Transport along the equivalence of small étale sites reflects zero objects.**  A module on
the small étale site of the scheme underlying `U` whose transport to the small étale site of the
algebraic space `yoneda.obj U` is a zero object is itself one: the transport is faithful, so it
reflects the vanishing of the identity. -/
theorem isZero_of_isZero_representedModulePushforward (U : BigFppfOver B S hS)
    {N : SheafOfModules.{u} (_root_.AlgebraicGeometry.SmallEtale.structureSheaf
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property)}
    (hN : IsZero ((representedModulePushforward B S hS U).obj N)) : IsZero N :=
  (IsZero.iff_id_eq_zero N).mpr
    ((representedModulePushforward B S hS U).map_injective (hN.eq_of_src _ _))

/-- **The small-étale module attached to a quasi-coherent module on a scheme of the site is a
zero object only if the module is.**

The transport along the equivalence of the two small étale sites reflects zero objects by
`AlgebraicGeometry.Space.isZero_of_isZero_representedModulePushforward`, which leaves the
associated-module functor of Stacks 03DU (4) on the small étale site of the scheme.  Its right
adjoint, restriction to the small Zariski site, carries the zero object to a zero object, and
the unit of the adjunction is an isomorphism at a quasi-coherent module — Stacks 070S (2),
`AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent`, proved here with no hypothesis — so the
module is a zero object too. -/
theorem isZero_of_isZero_representedAssociatedModule (U : BigFppfOver B S hS)
    (hU : IsAlgebraicSpace B S hS (yoneda.obj U))
    (M : ((BigFppfOver.toScheme B S hS).obj U).Modules)
    (hM : SheafOfModules.IsQuasicoherent M)
    (hzero : IsZero ((representedAssociatedModule B S hS U hU).obj M)) : IsZero M := by
  have h1 : IsZero ((_root_.AlgebraicGeometry.SmallEtale.associatedModule
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U)
      U.left.property).obj M) :=
    isZero_of_isZero_representedModulePushforward B S hS U hzero
  have hadd : (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).Additive :=
    inferInstance
  have h2 := Functor.map_isZero (_root_.AlgebraicGeometry.SmallEtale.restrictModule
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property) h1
  have hiso := _root_.AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⟨M, hM⟩
  exact h2.of_iso (@asIso _ _ _ _ _ hiso)

/-- The invertibility clause of Stacks 04CS, for every morphism `α : U ⟶ V` of schemes of the
big fppf site over `S`: the sheaf of differentials of `α` read as a morphism of represented
algebraic spaces — the module of differentials on the small étale site of `U` — is the
small-étale module attached by Stacks 03DU (4) to the Zariski sheaf of relative differentials
`Ω_{U/V}` of Stacks 01US.

This development has the comparison map of Stacks 04CS and its canonicity, but not this
invertibility; it is the one input carried by Stacks 04CV and, through
`AlgebraicGeometry.Space.sheafOfDifferentialsSchemeVanishing_of_comparison`, by Stacks 04G9.
The statement mentions no morphism of algebraic spaces and no chart: it is about morphisms of
schemes alone. -/
abbrev SheafOfDifferentialsSchemeComparison : Prop :=
  ∀ (U V : BigFppfOver B S hS) (α : U ⟶ V),
    Nonempty (sheafOfDifferentials B S hS (schemeSpaceMap α) ≅
      (representedAssociatedModule B S hS U (schemeSpace U).property).obj
        (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map α)))

/-- The vanishing comparison of Stacks 04CS for the morphisms of schemes of the big fppf site
of `S`: for every such morphism `ψ : U ⟶ V`, the sheaf of differentials of `ψ` read as a
morphism of represented algebraic spaces — the module of differentials on the small étale site
of `U` — is a zero object exactly when the scheme-level sheaf of relative differentials
`Ω_{U/V}` of Stacks 01US is.

This is the invertibility clause of Stacks 04CS, which this development has only as a
comparison map, read off at zero objects.  It mentions no morphism of algebraic spaces, no
chart and no square, so it is not an instance of any statement about `Ω_{X/Y}`; the chart-square
form that the proof of Stacks 04G9 consumes,
`AlgebraicGeometry.Space.SheafOfDifferentialsChartComparison`, is derived from it by
Stacks 04CU in `AlgebraicGeometry.Space.sheafOfDifferentialsChartComparison_of_schemeVanishing`. -/
abbrev SheafOfDifferentialsSchemeVanishing : Prop :=
  ∀ (U V : BigFppfOver B S hS) (ψ : U ⟶ V),
    IsZero (sheafOfDifferentials B S hS (schemeSpaceMap ψ)) ↔
      IsZero (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map ψ))

/-- **The invertibility clause of Stacks 04CS implies the vanishing comparison carried by
Stacks 04G9.**  For a morphism `α` of schemes of the site, the spaces-level sheaf of
differentials of `α` vanishes exactly when the scheme-level sheaf of relative differentials
`Ω_{U/V}` does.

One direction is the isomorphism together with the additivity of the associated-module functor.
The other also needs that functor to reflect zero objects, which it does at a quasi-coherent
module by `AlgebraicGeometry.Space.isZero_of_isZero_representedAssociatedModule`; `Ω_{U/V}` is
quasi-coherent by Stacks 08S2,
`AlgebraicGeometry.Scheme.Hom.isQuasicoherent_relativeDifferentials`. -/
theorem sheafOfDifferentialsSchemeVanishing_of_comparison
    (hcomparison : SheafOfDifferentialsSchemeComparison B S hS) :
    SheafOfDifferentialsSchemeVanishing B S hS := by
  intro U V α
  obtain ⟨e⟩ := hcomparison U V α
  have hadd : (representedAssociatedModule B S hS U (schemeSpace U).property).Additive :=
    additive_representedAssociatedModule B S hS U _
  refine ⟨fun hz => ?_, fun hz => ?_⟩
  · exact isZero_of_isZero_representedAssociatedModule B S hS U _ _
      (Scheme.Hom.isQuasicoherent_relativeDifferentials _) (hz.of_iso e.symm)
  · exact (Functor.map_isZero
      (representedAssociatedModule B S hS U (schemeSpace U).property) hz).of_iso e

/-- **Stacks 04CS.**  For a morphism `α : U ⟶ V` of the big fppf category over `S`, the
spaces-level sheaf of differentials of `α` — the sheafification on the small étale site of the
presheaf of sectionwise Kähler differentials of `α^{-1}𝒪`, Stacks 04CT — is the small-étale
module associated to the Zariski sheaf of relative differentials `Ω_{U/V}` of Stacks 01US.

This is `AlgebraicGeometry.Space.SheafOfDifferentialsSchemeComparison` above with the
isomorphism chosen rather than merely asserted to exist, which is what
`AlgebraicGeometry.Space.modulePullbackSheafOfDifferentialsChartIso` below needs.  It is the form
in which consumers of Stacks 04CS take it as a hypothesis; the `Prop` form is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeTransport.lean`, and the
registration of Stacks 04CS sits there and not here. -/
abbrev SchemeDifferentialsComparison :=
  ∀ (U V : BigFppfOver B S hS) (α : U ⟶ V),
    sheafOfDifferentials B S hS (schemeSpaceMap α) ≅
      (representedAssociatedModule B S hS U (schemeSpace U).property).obj
        (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map α))

/-- **Stacks 04CU read through Stacks 04CS.**  In a commuting square of étale charts over a
morphism `f : X ⟶ Y` of algebraic spaces whose horizontal arrow is the morphism of schemes `ψ`,
the restriction of `Ω_{X/Y}` to the chart is the small-étale module associated to the
scheme-level sheaf of relative differentials of `ψ`.

The restriction is the spaces-level sheaf of differentials of `ψ` by Stacks 04CU,
`AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso`, which this development
proves; the comparison `AlgebraicGeometry.Space.SchemeDifferentialsComparison` is what identifies
that with the associated module. -/
noncomputable def modulePullbackSheafOfDifferentialsChartIso
    (h : SchemeDifferentialsComparison B S hS) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {U V : BigFppfOver B S hS} (ψ : U ⟶ V) (a : schemeSpace U ⟶ X) (b : schemeSpace V ⟶ Y)
    (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom)
    (hcomm : a ≫ f = schemeSpaceMap ψ ≫ b) :
    (modulePullback B S hS a).obj (sheafOfDifferentials B S hS f) ≅
      (representedAssociatedModule B S hS U (schemeSpace U).property).obj
        (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map ψ)) :=
  sheafOfDifferentialsEtaleLocalizationIso B S hS f a (schemeSpaceMap ψ) b ha hb hcomm ≪≫
    h U V ψ

end AlgebraicGeometry.Space

end
