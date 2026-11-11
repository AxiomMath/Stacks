module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDefinition
public import StacksFrontier.RingTheory.PseudoCoherentMap.Absolute
public import StacksFrontier.RingTheory.PseudoCoherentMap.Flat

/-!
# Relative pseudo-coherence over a flat, finitely presented morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is flat and locally
of finite presentation, and let `E` be an object of `D_QCoh(𝒪_X)`.  Then relative
pseudo-coherence of `E` over `Y` is *moot*: on every commuting square of affine étale scheme
charts

```
U ⟶ V
↓    ↓
X ⟶ Y
```

the complex `RΓ(U, E)` of `𝒪_X(U)`-modules is pseudo-coherent relative to the ring `𝒪_Y(V)`
exactly when it is pseudo-coherent over `𝒪_X(U)` itself, the target `𝒪_Y(V)` playing no role.

This is the étale localization of Stacks 0DII: relative pseudo-coherence on an algebraic space
is tested on exactly those squares (`AlgebraicGeometry.Space.IsRelativelyPseudoCoherent`, Stacks
0CSY), and on one square the statement is Stacks 0DHQ for the ring map `𝒪_Y(V) → 𝒪_X(U)`, which
is flat and of finite presentation and so pseudo-coherent by Stacks 067J.

## Main results

* `AlgebraicGeometry.Space.isRelativelyPseudoCoherentFrom_iff_forall_chart`: for `f` flat and
  locally of finite presentation, relative `m`-pseudo-coherence of `E` over `Y` is absolute
  `m`-pseudo-coherence of `RΓ(U, E)` over `𝒪_X(U)` on every square of affine étale charts.
* `AlgebraicGeometry.Space.isRelativelyPseudoCoherent_iff_forall_chart`: the same in all
  degrees at once, which is the shape of the source statement.

## What is proved, and what the right-hand side says

The source's right-hand side reads "`E` is pseudo-coherent on `X`", the absolute condition of
Stacks 08FT on the small étale ringed site of `X`, and its proof is "by étale localization and
the definitions we may assume `X` and `Y` are schemes", after which it cites Stacks 09UU — in
this library the scheme case
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherent_iff_of_flat_of_locallyOfFinitePresentation`.

**The right-hand side here is the absolute condition read on the charts, not
`AlgebraicGeometry.RingedSite.IsPseudoCoherent` of
`AlgebraicGeometry.Space.smallEtaleRingedSite`,** and that is deliberate: the two are not known
to be equivalent in this development, so writing the site-level predicate here would be an
assertion the proof does not support.

What the site-level right-hand side needs.  Both
sides of the source statement are étale-local by construction, so the whole of the gap sits at
one affine chart `U`: it is the identification of
`AlgebraicGeometry.RingedSite.IsPseudoCoherentFrom` on the small étale site over `U` with
`m`-pseudo-coherence of `RΓ(U, E)` over the ring `𝒪_X(U)`.  Its four steps stand as follows.

* **The crossing from the slice at `U` to the small étale site of the scheme `U` is closed.**
  It is `AlgebraicGeometry.Space.isPseudoCoherentFrom_chartSchemeReindex_iff` with its
  all-degrees companion `AlgebraicGeometry.Space.isPseudoCoherent_chartSchemeReindex_iff`
  (`StacksFrontier/AlgebraicGeometry/Spaces/ChartPseudoCoherentTransport.lean`), which carry both
  clauses of Stacks 08FT (3) along the composite of Stacks 04M0
  (`AlgebraicGeometry.Space.chartLocalizationReindex`, built from
  `AlgebraicGeometry.Space.SmallEtale.chartLocalizationEquivalence`) with the comparison of a
  representable algebraic space and its scheme
  (`AlgebraicGeometry.Space.representedSchemeReindex`, built from
  `AlgebraicGeometry.Space.representedSmallEtaleEquivalence`), in both directions and with no
  mathematical hypothesis.  The two meet because the chart space *is* the Yoneda algebraic space
  of the chart's object, `AlgebraicGeometry.Space.chartRingedSite_eq_representedRingedSite`, an
  `rfl`; and the target `AlgebraicGeometry.Space.representedSchemeRingedSite` is
  `AlgebraicGeometry.smallEtaleRingedSite` of the chart's scheme over
  `AlgebraicGeometry.associatedBigEtaleSite B`, which is the site Stacks 08HE and Stacks 071Q
  are stated on;
* from the small étale site of the scheme `U` to its small Zariski site, **Stacks 08HE is closed
  in both directions and unconditionally**:
  `AlgebraicGeometry.SmallEtale.pseudoCoherentToAssociatedModule_of_slice_exact` is clause
  (1) ⇒ (2), `AlgebraicGeometry.SmallEtale.associatedModuleToPseudoCoherent` is clause (2) ⇒ (1),
  and `AlgebraicGeometry.SmallEtale.pseudoCoherentIffAssociatedModule`
  (`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtalePseudoCoherentDescent.lean`)
  carries the bare `@[stacks 08HE]`.  **Its input is now supplied too.**  Both clauses speak of
  `ε^*E₀` for an object `E₀` of `D(𝒪_U)` on the small *Zariski* site, whereas at a chart the
  object in hand is the restriction of `E` to the small *étale* site; an `E₀` with
  `ε^*E₀ ≅ E|_U` is produced by essential surjectivity of `ε^*` on `D_QCoh`, which is
  Stacks 071Q, which is proved unconditionally as
  `AlgebraicGeometry.SmallEtale.derivedAssociatedModule_isEquivalence`
  (`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleDerivedEquivalence.lean`,
  section `Unconditional`, with quasi-inverse `Rε_*` corestricted to `D_QCoh`,
  `AlgebraicGeometry.SmallEtale.derivedRestrictModuleQcoh`).  What that step consumes is
  quasi-coherence of the chart-reindexed `E`, which crosses the two comparisons by
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_chartSmallEtaleRestriction_iff` and
  `Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff`;
* on the affine scheme `U` the condition on the *ringed space* is `m`-pseudo-coherence of the
  complex of modules, by Stacks 08E7,
  `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_tilde_iff`, with the object-level form
  `AlgebraicGeometry.RingedSpace.isPseudoCoherent_derivedTilde_iff` and the avatar
  `AlgebraicGeometry.RingedSpace.exists_isPseudoCoherent_iso_mapDerivedCategory_tilde`; the
  canonical avatar is derived global sections, `AlgebraicGeometry.derivedTilde` and
  `AlgebraicGeometry.derivedGlobalSectionsQuasicoherent` being mutually quasi-inverse
  equivalences `D(A) ≌ D_QCoh(𝒪_{Spec A})` by
  `AlgebraicGeometry.StandardModel.derivedTilde_isEquivalence` and
  `...derivedGlobalSectionsQuasicoherent_isEquivalence`.  Applying it at an affine chart carries
  the identification of the chart with the spectrum of its ring, which is
  `AlgebraicGeometry.Scheme.isoSpec` and
  `AlgebraicGeometry.isPseudoCoherentFrom_of_derivedPullback_iso`.

**All four steps are closed.**  The fourth, the one that names `RΓ(U, E)`, is closed in
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/AffineSmallEtaleTopSectionsOnSite.lean` and
assembled
in `StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/
RelativeAbsoluteChartDictionary.lean`; the section "The route to 0DII" below explains
why the chain has the shape it has.

One of the closures above deserves its own account, because it is the seam between the last two
bullets.  Clause (1) of Stacks 08HE is
`AlgebraicGeometry.RingedSite.IsPseudoCoherentFrom` at
`AlgebraicGeometry.Scheme.zariskiRingedSite`, indexed by objects of the site and covering sieves;
Stacks 08E7 is about `AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom`, indexed by points and
opens.  The implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/PseudoCoherent/CoherentCohomology.lean` record that the one
statement relating the two predicates is for the site of *opens* of a ringed space and does not
reach the small étale site of an algebraic space; what follows is how the seam at a scheme is
closed.

The two *categories* are not the obstruction: they are the same type by `rfl`, through
`AlgebraicGeometry.Scheme.zariskiRingedSite_ringSheaf` and
`Stacks.DerivedQCoh.oxMod_eq_sheafOfModules`
(`StacksFrontier/AlgebraicGeometry/DerivedQCoh/StructureSheafSpelling.lean`), and the ringed site of
the opens of a space is the same data as `zariskiRingedSite` — see
`AlgebraicGeometry.RingedSpace.ringedSite` and `Stacks.RingedSpace.toRingedSite`.

Nor are the two `IsStrictlyPerfect` structures: they agree, by
`StrictlyPerfect.isStrictlyPerfect_iff_site` and its scheme form
`AlgebraicGeometry.Scheme.isStrictlyPerfect_zariskiRingedSite_iff`
(`StacksFrontier/Topology/Sheaves/Cohomology/StrictlyPerfect/SiteComparison.lean`).  Both predicates
are the same boundedness clause together with a termwise retract clause, and
`StrictlyPerfect.finiteFreeIsoFree` identifies the two spellings of a finite free module.

Nor is that comparison **at a slice**, which is the form the bridge actually needs — the
comparison above is stated at a space `X`, while the bridge works with `X.ringSheaf.over V`
against `X.restrict V.isOpenEmbedding`, and a module over the slice sheaf of rings is not of the
form `OXMod Y` for any ringed space `Y`.  Strict perfectness crosses that slice equivalence in
both directions, by `StrictlyPerfect.isStrictlyPerfect_equivRestrict_functor` and
`...equivRestrict_inverse`, along
`AlgebraicGeometry.RingedSpace.PseudoCoherence.sheafOfModulesEquivRestrict`; and
`StrictlyPerfect.mapHomologicalComplex_equivRestrict_overFunctor` identifies the result with
`restrictComplex` on the nose, by `rfl`.

**The bridge is closed.**  It is
`AlgebraicGeometry.Scheme.isPseudoCoherentFrom_zariskiRingedSite_iff`: Stacks 08FT (3) at
`AlgebraicGeometry.Scheme.zariskiRingedSite` and Stacks 08CB (3) at
`AlgebraicGeometry.Scheme.toRingedSpace` are the same condition.  Its two halves were proved
from opposite directions and at two spellings of the site, which are equal by `rfl`:
`AlgebraicGeometry.RingedSpace.PseudoCoherence.isPseudoCoherentFrom_ringedSite` gives space to
site, and `AlgebraicGeometry.Scheme.isPseudoCoherentFrom_toRingedSpace_of_zariskiRingedSite`
gives site to space, the indexing there being a covering sieve of the final object together with
`TopologicalSpace.Opens.mem_grothendieckTopology` and
`AlgebraicGeometry.RingedSpace.PseudoCoherence.exists_restrict_approximation_of_slice`.

The two halves compose only because `Stacks.SheafOfModules.ringedSite S.sheaf` and
`AlgebraicGeometry.Scheme.zariskiRingedSite` are the same ringed site by `rfl` — checked, not
assumed.  The strict-perfectness comparison both halves rest on is proved once, in
`StacksFrontier/Topology/Sheaves/Cohomology/PseudoCoherence/RingedSiteComparison.lean`; the
statements of the same thing in
`StacksFrontier/Topology/Sheaves/Cohomology/StrictlyPerfect/SiteComparison.lean` are that proof
read in the reversed orientation.

So of the four steps this section opened with, three are closed: the seam just described;
Stacks 08HE, whose clause (2) ⇒ (1) Stacks 071Q supplies the input for; and the crossing from
the slice at a chart to the small étale site of the chart's scheme.

## The route to 0DII

The site-level statement — the one this file does not make — is
`AlgebraicGeometry.Space.isRelativelyPseudoCoherent_iff_isPseudoCoherent`
(`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/
RelativeAbsoluteChartDictionary.lean`), which carries the bare `@[stacks 0DII]`; the one statement
about a single affine scheme it rests on is
`AlgebraicGeometry.isPseudoCoherentFrom_derivedSectionsOverTop_iff`
(`StacksFrontier/AlgebraicGeometry/PseudoCoherent/AffineSmallEtaleTopSectionsOnSite.lean`).  The
rest
of this section describes the route: it explains the shape of the chain, and in particular why
every link is per-degree.  Sections 2 and 3 below are
closed outright, and of the three comparisons of section 1 the crossing of `ε` is closed too —
**and so are the whole of (ii) and the whole of (i)**, the last link of (i) being
`AlgebraicGeometry.Space.derivedChartTransportSectionsChartIso`
(`StacksFrontier/AlgebraicGeometry/Spaces/ChartTransportDerivedChartSections.lean`), whose bullet
below explains why the "spelling pincer" is not an obstruction.

**Two further things are proved.**

* **The assembly over the covering sieve of affine squares is proved**, in both directions and in
  both degree forms, in the file `RelativeAbsoluteSiteAssembly.lean` of the directory
  `StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/`.
  `AlgebraicGeometry.Space`
  `.isRelativelyPseudoCoherentFrom_iff_isPseudoCoherentFrom_of_chartDictionary`
  and its all-degrees companion
  `AlgebraicGeometry.Space.isRelativelyPseudoCoherent_iff_isPseudoCoherent_of_chartDictionary`
  are the tag's own statement, granted the pointwise dictionary at one affine chart which that
  file names `AlgebraicGeometry.Space.ChartPseudoCoherenceDictionaryFrom` — item (iii) of the
  display below, with no quantification over coverings left in it.  It is one application of
  `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_locally_general` at the covering sieve of
  `AlgebraicGeometry.Space.generate_affineChartDiagram_mem_topology` in one direction and one of
  `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_derivedRestriction` in the other; it is not
  an induction, and it checks in under two seconds.
* **The first step of (iii) is proved too**: the restriction of scalars that (i) carries is
  absorbed on the `Prop` side in
  `StacksFrontier/AlgebraicGeometry/Spaces/ChartDerivedSectionsPseudoCoherentAtTop.lean`, by
  `AlgebraicGeometry.Space.isPseudoCoherentFrom_chartDerivedSections_iff_chartTransportTop` and
  its all-degrees companion: pseudo-coherence of `RΓ(U, E)` over `𝒪_X(U)` **is**
  pseudo-coherence of the derived chart transport of `E` at the whole of the chart's scheme, over
  the ring of sections of `𝒪` there.  See the last bullet of (i) below for the route.

So what is left is the pointwise dictionary at one affine chart, and section 1 below now states
what it has been reduced to.  Four further facts come first.

* **(i) now reaches `RΓ(U, E)` itself, at the whole of the chart's scheme.**  The chain of
  `ChartTransportDerivedChartSections.lean` is composed at `Z = ⊤` by
  `AlgebraicGeometry.Space.chartDerivedSectionsTransportTopIso`
  (`StacksFrontier/AlgebraicGeometry/Spaces/ChartDerivedSectionsTransportAtTop.lean`): for an
  object `E` of `D_QCoh(𝒪_X)`, `AlgebraicGeometry.Space.chartDerivedSections … U E` — the
  complex both sides of 0DII are about — is the derived chart transport of `E` at the whole of
  the chart's scheme, read over `𝒪_X(U)` along the isomorphism of rings of sections induced by
  `AlgebraicGeometry.Space.openChartOfComparisonTopIso`.  Its general form,
  `AlgebraicGeometry.Space.derivedChartSectionsTransportAppIso`, takes the object `Z` and an
  isomorphism between the chart the comparisons attach to `Z` and `U` as parameters, so the
  specialization to `⊤` is an application and not a further elaboration.
  The obstruction to composing the chain with the `⊤`-specialization is not the concrete
  `Z = AlgebraicGeometry.SmallEtale.opensObj … ⊤`: at an **abstract** `Z` the
  composite exceeds 200,000 heartbeats at `whnf` just the same, as long as it is stated on
  *functors* — what the elaborator is then asked for is the identification of the two
  `CategoryTheory.HasDerivedCategory` data on the two spellings of one ring of sections, and not
  the identification of the rings, which is `rfl` and cheap.  Stated on **objects** the composite
  checks in under a second at any `Z`, the concrete one included.  What the chain did need and
  did not have is a `HasDerivedCategory` instance for the modules of sections of `𝒪_X` at a
  chart, `AlgebraicGeometry.Space.hasDerivedCategoryStandard_spaceChartSections`, at the
  `AlgebraicGeometry.Space.SmallEtale` spelling of the chart's type.
  The restriction of scalars it carries is not removed, and is harmless only on the `Prop` side.
  **That absorption is proved**, in
  `StacksFrontier/AlgebraicGeometry/Spaces/ChartDerivedSectionsPseudoCoherentAtTop.lean`:
  `AlgebraicGeometry.Space.isPseudoCoherentFrom_derivedChartSections_iff_chartTransportDerived`
  and `AlgebraicGeometry.Space.isPseudoCoherent_derivedChartSections_iff_chartTransportDerived`
  absorb it at an arbitrary `Z` and an arbitrary isomorphism of charts, and
  `...isPseudoCoherentFrom_chartDerivedSections_iff_chartTransportTop` and
  `...isPseudoCoherent_chartDerivedSections_iff_chartTransportTop` are those applied at `⊤`.
  Reaching the `RingEquiv` of `𝒪_X.ringSheaf.obj.map e.hom.op` as
  `CategoryTheory.Iso.ringCatIsoToRingEquiv` at `CategoryTheory.asIso` of that map does exceed
  200,000 heartbeats at `whnf`; that does not establish that no route does.
  `RingEquiv.ofBijective` of the map itself has that map as its
  `RingEquiv.toRingHom` with nothing to unify, and
  `StacksDraft.PseudoCoherence.pseudoCoherent_iff_of_ringEquiv` — which supplies **both** clauses
  of Stacks 064Q at once, in every universe — then applies; the bijectivity is
  `CategoryTheory.ConcreteCategory.bijective_of_isIso`, with its `IsIso` taken as
  `CategoryTheory.Iso.isIso_hom` of `𝒪_X.ringSheaf.obj.mapIso (CategoryTheory.Iso.op e)` rather
  than from instance search, which reaching `CategoryTheory.Functor.map_isIso` re-derives
  `IsIso e.hom.op` at the wrong `CategoryTheory.Category` instance for the chart's type and fails.
  The whole file checks in under a second at the default ceiling.
  (`PseudoCoherence.pseudoCoherentFrom_and_pseudoCoherent_iff_restrictScalars_derived`, which
  takes a plain ring map and would also serve, is `private` to
  `StacksFrontier/Homology/PseudoCoherent/Relative/Localization.lean` and so is not usable from
  outside it; no visibility change is needed, the route above needing nothing that is not already
  public.)

* **Stacks 071Q is proved, unconditionally.**
  `AlgebraicGeometry.SmallEtale.derivedAssociatedModule_isEquivalence`
  (`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleDerivedEquivalence.lean`,
  in its `Unconditional` section, so that the `[….IsEquivalence]` binders of the earlier
  `section Equivalence` are out of scope) carries the bare `@[stacks 071Q]`, and its
  quasi-inverse is the source's own `Rε_*`,
  `AlgebraicGeometry.SmallEtale.derivedRestrictModuleQcoh`, built from
  `AlgebraicGeometry.SmallEtale.isQuasicoherent_homology_derivedRestrictModule` and
  `AlgebraicGeometry.SmallEtale.derivedAssociatedModule_mem`.  Its only remaining binders are
  the two derived-category models.  The route through
  `[(AlgebraicGeometry.SmallEtale.derivedQcohOnSiteComparison B S hS).IsEquivalence]` is not the
  route taken: `AlgebraicGeometry.SmallEtale.isEquivalence_derivedAssociatedModule`, the
  hypothesis-carrying deduction, is only a statement about that comparison.
* **The crossing between the slice at a chart and the small étale site of the chart's scheme is
  proved**, in both directions and in both degree forms:
  `AlgebraicGeometry.Space.isPseudoCoherentFrom_chartSchemeReindex_iff` and
  `AlgebraicGeometry.Space.isPseudoCoherent_chartSchemeReindex_iff`
  (`StacksFrontier/AlgebraicGeometry/Spaces/ChartPseudoCoherentTransport.lean`), with the two
  intermediate layers `...isPseudoCoherentFrom_chartLocalizationReindex_iff` /
  `...isPseudoCoherent_chartLocalizationReindex_iff` (the slice at the chart against Stacks 04M0)
  and `...isPseudoCoherentFrom_representedSchemeReindex_iff` /
  `...isPseudoCoherent_representedSchemeReindex_iff` (the representable space against its
  scheme).  See the first bullet of the previous section.

* **Comparison (ii) is proved, in both halves.**  The crossing of `ε` is
  `AlgebraicGeometry.SmallEtale.derivedModuleSectionsRestrictModuleIso`
  (`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/`, file
  `SmallEtaleDerivedSectionsOverObject.lean`); the seam between module-valued derived sections
  at `⊤` on the small Zariski *site* and derived global sections
  on the ringed *space* is `AlgebraicGeometry.derivedGlobalSectionsOverEvaluationIso`
  (`StacksFrontier/AlgebraicGeometry/DerivedGlobalSectionsZariskiSite.lean`), and the two composed
  are `AlgebraicGeometry.SmallEtale.derivedModuleSectionsGlobalSectionsOverIso`
  (`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/`, file
  `SmallEtaleDerivedGlobalSectionsOverBase.lean`).  See the (ii) entry of the display below for
  what each one says and for the two restrictions of scalars the
  composite carries.

* **The last two legs of the chain on the scheme side are proved.**  From the small Zariski
  *site* of an affine chart to its ringed *space* in all degrees — not only in a fixed degree —
  is `AlgebraicGeometry.Scheme.isPseudoCoherent_zariskiRingedSite_iff`
  (`StacksFrontier/AlgebraicGeometry/PseudoCoherent/ZariskiRingedSiteAllDegrees.lean`), the
  all-degrees companion of `...isPseudoCoherentFrom_zariskiRingedSite_iff`, got by collapsing
  both predicates to the conjunction over all degrees of their fixed-degree clause.  And from
  the ringed space to a *named* complex of modules is
  `AlgebraicGeometry.isPseudoCoherent_restrictFunctor_iff_derivedSectionsUnbounded`
  (`StacksFrontier/AlgebraicGeometry/PseudoCoherent/AffineOpenSectionsDictionary.lean`): for `E`
  with
  quasi-coherent cohomology and `U` an affine open of a scheme `X`, `E|_U` is pseudo-coherent on
  the ringed space `U` exactly when `RΓ(U, E)` is pseudo-coherent over `Γ(X, U)`.  That is
  Stacks 08E7 after Stacks 06Z0 at an affine open (`...affineDerivedSectionsPresentation`, which
  is where `AlgebraicGeometry.IsAffineOpen.isoSpec` enters) and Stacks 09VA at an isomorphism;
  its reusable half is `AlgebraicGeometry.isPseudoCoherent_pushforwardTilde_iff`.
  So the chart-side complex of modules is named, on the *scheme* side.  What section 1 below needs
  is not the identification with `chartDerivedSections`: that is proved, as the first bullet
  of this section records.

### 1. The derived-sections dictionary at an affine chart — the one mathematical gap

Everything the chain needs between the small étale site of `X` and a complex of modules is
proved, the identification of *which* complex of modules included.  Running the chain at an
affine chart `U` with `T = chartScheme U` and `A = 𝒪_X(U) = Γ(T, 𝒪_T)` gives, from
`m`-pseudo-coherence on the slice at `U`:
`m`-pseudo-coherence on the small étale site of `T` (the chart transport); hence of the `E₀` of
`D_QCoh(𝒪_T)` with `ε^*E₀ ≅ E|_U` that Stacks 071Q produces, on the small Zariski site of `T`
(Stacks 08HE); hence on the ringed space `T`
(`AlgebraicGeometry.Scheme.isPseudoCoherentFrom_zariskiRingedSite_iff`); hence of a complex of
`A`-modules (Stacks 08E7, `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_tilde_iff`, after
`AlgebraicGeometry.Scheme.isoSpec`).

**The complex of `A`-modules which comes out is `RΓ(U, E)`, and the two are related at a chart
of an algebraic space.**  `AlgebraicGeometry.Space.chartDerivedSectionsTransportTopIso`
(`StacksFrontier/AlgebraicGeometry/Spaces/ChartDerivedSectionsTransportAtTop.lean`) relates exactly
those two objects at a chart of an algebraic space — `AlgebraicGeometry.Space.chartDerivedSections
… U E`, which is `RΓ(U, E)` on the small étale site of the *space*, against the derived chart
transport at the whole of the chart's scheme, read over `𝒪_X(U)` along
`AlgebraicGeometry.Space.openChartOfComparisonTopIso` — and the restriction of scalars it carries
is absorbed on the `Prop` side by
`AlgebraicGeometry.Space.isPseudoCoherentFrom_chartDerivedSections_iff_chartTransportTop`
(`StacksFrontier/AlgebraicGeometry/Spaces/ChartDerivedSectionsPseudoCoherentAtTop.lean`), with its
all-degrees companion.

**What is left is therefore a statement about one affine scheme, with no chart and no algebraic
space in it.**  The absorption above turns item (iii) of the display below into: for `T` the
affine scheme of the chart and `F` the chart-reindexed object on its small étale site,

```lean
PseudoCoherence.IsPseudoCoherentFrom
    ((chartTransportDerived B S hS X U (chartSchemeTopObject B S hS X U)).obj E.obj) m ↔
  (representedSchemeRingedSite B S hS ((SmallEtale.toOver B S hS X.1).obj U)
    ).IsPseudoCoherentFrom F m
```

— the left-hand side being `RΓ(T_étale, ⊤; F)` as a complex of `𝒪(⊤)`-modules, since
`AlgebraicGeometry.Space.chartTransportDerived` is the two reindexings followed by derived
sections at the given object; and the right-hand side being item (iii)'s own right-hand side
after `AlgebraicGeometry.Space.isPseudoCoherentFrom_chartSchemeReindex_iff`, which crosses the
slice at `U` to the small étale site of `T` in both directions.  That statement is exactly
Stacks 08HE followed by `AlgebraicGeometry.Scheme.isPseudoCoherentFrom_zariskiRingedSite_iff` and
Stacks 08E7 at an affine scheme, with Stacks 071Q supplying the `E₀`.

**The composition of those legs is proved, in a fixed degree**, as
`AlgebraicGeometry.isPseudoCoherentFrom_associatedModuleOfSheaf_iff_derivedSectionsUnbounded_top`
(`StacksFrontier/AlgebraicGeometry/PseudoCoherent/AffineSmallEtaleTopSectionsDictionary.lean`): for
`T` affine and `E₀` an object of `D(𝒪_T)` with quasi-coherent cohomology, `m`-pseudo-coherence of
`ε^*E₀` on the small étale site of `T` is `m`-pseudo-coherence of the complex `RΓ(T, E₀)` of
`Γ(T, 𝒪_T)`-modules.  It is Stacks 08HE in a fixed degree followed by the fixed-degree Zariski
comparison and by `AlgebraicGeometry.isPseudoCoherentFrom_iff_derivedSectionsUnbounded_top`, which
is the second of the two seams below discharged.

**The fixed degree is not a convenience; it is forced.**  The all-degrees forms of these legs
cannot be composed into anything the assembly of
section 2 consumes: the locality criterion it runs over,
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_locally_general`, exists in a fixed degree
only — `StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/LocalNature.lean` has no
all-degrees companion of it, and an all-degrees locality criterion is not a formal consequence,
the all-degrees clause of Stacks 08FT (3) asking for **one** complex good in every degree.  So
every link of this chain has to be available degree by degree, and Stacks 08E7 at an affine open
is formalized in a fixed degree in
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/AffineOpenSectionsDictionaryFrom.lean` as well as
in all degrees.

Of the two seams recorded here, **the second is discharged and the first is not**.
`AlgebraicGeometry.isPseudoCoherentFrom_restrictFunctor_iff_derivedSectionsUnbounded` is stated at
an affine *open* of a scheme, so applying it at `⊤` carries the restriction along `⊤.ι`; that is
crossed in `...isPseudoCoherentFrom_iff_derivedSectionsUnbounded_top` by Stacks 09VA at an
isomorphism, `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_pushforward_isIso_iff`,
together with `AlgebraicGeometry.Scheme.Modules.restrictFunctorCompPushforwardIso` read on derived
categories.  `IsIso ⊤.ι` is **not** an instance and has to be taken as
`AlgebraicGeometry.Scheme.topIso_hom` rewritten into `CategoryTheory.Iso.isIso_hom`; substituting
that equation with `▸` fails to compute a motive, the morphism occurring in the types of both
functors of the composite.  The first seam stands:
`AlgebraicGeometry.Space.chartTransportDerived` is built from
`Stacks.DerivedFunctor.totalRightDerived` of the restriction functor and from
`AlgebraicGeometry.Space.chartSliceReindex`, where
`...isPseudoCoherentFrom_chartSchemeReindex_iff` is stated at
`CategoryTheory.Functor.mapDerivedCategory` of the restriction functor and at
`AlgebraicGeometry.Space.chartLocalizationReindex`.  For the first half of it
`Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived`
(`StacksFrontier/AlgebraicGeometry/ClosedImmersion/DerivedPushforwardComparison.lean`) is the
general
bridge — for an exact functor, the functor induced on derived categories *is* the chosen total
right derived functor, by uniqueness of right derived functors — and its target is
`Stacks.DerivedFunctor.totalRightDerived` character for character; `chartSliceReindex` is an
`abbrev` for `chartLocalizationReindex` with its domain ascribed, so the second half is a
spelling.  Neither has been applied here.

**What the reduced hypothesis still owes, precisely.**  Writing `T = chartScheme U` and `F` for
the chart-reindexed object on the small étale site of `T`, three things:

1. Stacks 071Q applied at `F`: an object `E₀` of `D(𝒪_T)` with quasi-coherent cohomology together
   with `ε^*E₀ ≅ F`.  This needs `F` to have quasi-coherent cohomology, which has to be carried
   from `E : D_QCoh(𝒪_X)` through `SheafOfModules.overFunctor` and the two reindexings.
2. The identification of the left-hand side above with `RΓ(T, E₀)`, which is comparison (ii) —
   `AlgebraicGeometry.SmallEtale.derivedModuleSectionsRestrictModuleIso` at `V = ⊤`, whose
   right-hand side is Zariski-side sections of `Rε_*F`, plus the unit of Stacks 071Q to turn
   `Rε_*ε^*E₀` into `E₀` — together with the restriction of scalars that comparison carries,
   absorbed on the `Prop` side by `StacksDraft.PseudoCoherence.pseudoCoherent_iff_of_ringEquiv` as
   in `ChartDerivedSectionsPseudoCoherentAtTop.lean`.  Note that the route through
   `AlgebraicGeometry.derivedGlobalSectionsOver` is **longer**: no declaration of the library
   relates
   `derivedGlobalSectionsOver` to `AlgebraicGeometry.derivedSectionsUnbounded` at `⊤`, the nearest
   being the non-natural, `isoSpec`-transported
   `AlgebraicGeometry.IsAffineOpen.nonempty_iso_derivedSectionsSpec`.
3. The first seam above.

Granted 1–3, the display is
`...isPseudoCoherentFrom_associatedModuleOfSheaf_iff_derivedSectionsUnbounded_top` and nothing
else.

`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections`, which is what
`chartDerivedSections` is, occurs in more than the files that spell it that way, and meets
geometric objects there.  That declaration is an `abbrev`
whose body — `(SheafOfModules.evaluation O (op U)).mapHomotopyCategory (.up ℤ) ⋙
DerivedCategory.Qh`, right-derived — is shared character for character with
`Stacks.Cohomology.HypercohomologyEdge.derivedSections`
(`StacksFrontier/CategoryTheory/Sites/Cohomology/HypercohomologyEdge/EdgeMorphism.lean`) and with
`Stacks.DerivedFunctor.totalRightDerived`
of `SheafOfModules.evaluation`
(`StacksFrontier/CategoryTheory/Sites/Cohomology/UnboundedDerivedFunctor/LeftTExactness.lean`), the
three differing only in
which instance supplies `CategoryTheory.Functor.HasRightDerivedFunctor`.  At those spellings the
functor meets geometry in many places, pseudo-coherence included:
`AlgebraicGeometry.affineOpenHypercohomologyIso`
(`StacksFrontier/AlgebraicGeometry/Cohomology/AffineOpenHypercohomologyEdge.lean`),
`AlgebraicGeometry.derivedSectionsUnboundedιIso`
(`StacksFrontier/AlgebraicGeometry/PseudoCoherent/DerivedSectionsUnbounded.lean`), and
`AlgebraicGeometry.finite_homology_derivedSections_of_isPseudoCoherent`
(`StacksFrontier/AlgebraicGeometry/FormalGeometry/Completion/FormalFunctionsPseudoCoherent.lean`),
which is a finiteness
statement about `(derivedSections (structureSheafRing X.toRingedSpace) U.1).obj K` for an affine
open of a scheme.  What is genuinely absent is narrower, and is stated step by step below: the
crossing of the chart transport, at an étale chart of an algebraic space.

What is owed is therefore one isomorphism, factoring into three comparisons of total right
derived functors of sections, of which (ii) is proved and (i) is proved except for its last
link — the naming of its left-hand side; see
`StacksFrontier/AlgebraicGeometry/Spaces/ChartTransportDerivedSections.lean` and the analysis in
the last bullet of (i) below:

```lean
-- (i) derived sections cross the chart transport: evaluation at `U` on the small étale site of
--     `X` *itself* — which is what `chartDerivedSections` is — against evaluation at the final
--     object on the small étale site of the scheme `T`, by way of the slice at `U` and along
--     `chartLocalizationReindex` and `representedSchemeReindex`.  The target functor is
--     `HomologyComparison.derivedSections (smallEtaleRingedSite (associatedBigEtaleSite B) T hT
--       ).ringSheaf ⊤`; no abbreviation for it exists, but it does exist, by
--     `AlgebraicGeometry.SmallEtale.hasRightDerivedFunctor_moduleSections` (the sheaf of rings
--     there being `structureSheaf` by `rfl`, `smallEtaleRingedSite_ringSheaf`).
--
--     (i) factors into three steps, all three of which are closed as *statements about functors*;
--     **what is left is the heartbeat cost of composing them, and two one-step consequences,
--     recorded in the last two bullets**.
--     It is *not* a typing question, as the last bullet records.
--
--     * **The slice is crossed, and by an equality of underived functors.**  For any sheaf of
--       rings `R` on any site and any object `U`,
--       `SheafOfModules.overFunctor R U ⋙
--          SheafOfModules.evaluation (R.over U) (op (Over.mk (𝟙 U)))
--            = SheafOfModules.evaluation R (op U)`
--       is `rfl`, in that generality: the final object of `Over U` is `Over.mk (𝟙 U)`, the
--       localized structure sheaf takes the value `R.obj.obj (op U)` there by
--       `AlgebraicGeometry.RingedSite.over_O_obj_obj`, and the restriction functor is
--       `SheafOfModules.pushforward (𝟙 _)`.  It is also already in the
--       tree, and in a stronger form than the display above: `overEvaluationIso` of
--       `StacksFrontier/AlgebraicGeometry/ProEtale/DerivedCompleteSections.lean` is **public, and
--       already general in the object of the slice**.  It is
--       `AlgebraicGeometry.RingedSite.overEvaluationIso R U V` for an arbitrary `V : Over U`,
--       concluding `SheafOfModules.evaluation R (op V.left)`, with proof `Iso.refl _`.  So
--       nothing has to be exposed and no specialization to the final object is involved: the
--       slice crossing delivers sections of `𝒪_X` at `V.left` for **every** `V`, which is what
--       makes the next two bullets collapse.
--     * **The two reindexings are crossed at the underived level too, and also by an equality**:
--       for `e : C' ≌ C` continuous in both directions and `R` a sheaf of rings on `C`,
--       `(Stacks.SheafOfModules.reindexEquivalence e R).functor ⋙
--          SheafOfModules.evaluation (Stacks.SheafOfModules.reindexRing J' e R) (op W)
--            = SheafOfModules.evaluation R (op (e.functor.obj W))`
--       is `rfl` — the transport being `SheafOfModules.pushforward` along `e.functor` with the
--       identity structure map, which is why the two structure sheaves agreeing on the nose
--       (`reindexRing_chartLocalizationEquivalence`,
--       `reindexRing_representedSmallEtaleEquivalence`) is enough.
--       Composed with the previous bullet at `V = e.functor.obj W` this is an equality of
--       *underived* functors,
--       `overFunctor 𝒪_X U ⋙ chartLocalizationReindex ⋙ Γ(W, -)
--          = Γ((e.functor.obj W).left, -)`,
--       and no comparison of evaluation at two isomorphic objects is needed to reach it: the
--       chart that comes out is `(e.functor.obj W).left`, whatever that is, and both sides of
--       0DII quantify over charts.  No natural isomorphism
--       `Γ(A', -) ≅ Γ(A, -) ⋙ ModuleCat.restrictScalars (R.obj.map θ.hom.op).hom` for `θ : A ≅ A'`
--       is needed at that point; and one **exists**, in exactly that shape and
--       that generality, for any morphism of any site and not only for an isomorphism:
--       `Stacks.Cohomology.HypercohomologyEdge.sectionsRestrict O g` for `g : U' ⟶ U` is
--       `Γ(U, -) ⟶ Γ(U', -) ⋙ Res_ρ`, with its derived companion
--       `...derivedSectionsRestrict` (`RΓ(U, -) ⟶ RΓ(U', -) ⋙ R Res_ρ`, through the universal
--       property of the derived functor) and its degreewise form
--       `...derivedSectionsRestrictHomology`, all in the file `SectionsRestriction.lean` of
--       `StacksFrontier/CategoryTheory/Sites/Cohomology/HypercohomologyEdge/`.
--       What is *not* proved there is only that these are isomorphisms when `g` is, which is a
--       one-step consequence; and `AlgebraicGeometry.evaluationRestrictScalarsIso` is not the
--       statement, and not the nearest thing to it.
--       The chart that the composite names is identified by an *equality* of charts, not an
--       isomorphism: `AlgebraicGeometry.Space.openChart_eq_chartLocalization_opensObj`
--       (`StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeModuleSections.lean`) says that
--       `(chartLocalizationEquivalence.functor.obj
--          (representedSmallEtaleEquivalence.inverse.obj (SmallEtale.opensObj … V))).left
--            = openChart B S hS X.1 A V`
--       for a Zariski open `V` of the chart's scheme — i.e. for the composite of *both*
--       reindexings at once.  At `V = ⊤` the result is `openChart … ⊤`, which is **not** the
--       chart `A` and is not `rfl`: it is only isomorphic to it, `openChart` going through
--       `CategoryTheory.Functor.preimage`, as the implementation notes of
--       `StacksFrontier/AlgebraicGeometry/Spaces/CoherentChartSchemeRestriction.lean` record.  So
--       one application of `derivedSectionsRestrict` at an isomorphism of charts, carrying one
--       `ModuleCat.restrictScalars` along a ring isomorphism, is what closes the last gap — and
--       that restriction of scalars is harmless on the Prop side, by
--       `PseudoCoherence.isPseudoCoherentFrom_restrictScalars_ringEquiv` and
--       `StacksDraft.PseudoCoherence.isModulePseudoCoherent_restrictScalars_of_ringEquiv`.
--       **That lemma is already public and nothing has to be exposed.**  The copy in
--       `StacksFrontier/Homology/PseudoCoherent/Relative/Presentation.lean` is `private`, but the
--       same statement is
--       public in `StacksFrontier/Homology/PseudoCoherent/Relative/Localization.lean`, at both
--       rings
--       in `Type u` and the modules at `u`, which is the shape a chart of a `Scheme.{u}` needs.
--       (A third, also `private`, copy sits in
--       `StacksFrontier/Homology/PseudoCoherent/Relative/Finite.lean`.)
--     * **The passage to the derived functors is available for the whole of (i) at once, and the
--       three steps collapse into one.**  `AlgebraicGeometry.Space.computesSecond_overFunctor`
--       (`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleSliceKInjective.lean`) is stated for
--       an **arbitrary** additive
--       functor `G` out of the `𝒪_F|_U`-modules on the slice, into any abelian category with a
--       derived category; `AlgebraicGeometry.Space.computesSecond_overFunctor_evaluation` is only
--       its specialization at `G = Γ(Over.mk (𝟙 U), -)`.  Its input,
--       `AlgebraicGeometry.Space.isKInjective_overFunctor`, is the preservation of
--       K-injectives; it is proved, from
--       `Stacks.Cohomology.Localization.isKInjective_over_of_essentiallySmall`.  So
--       `Stacks.Cohomology.LerayUnbounded.derivedCompIsoOfComputes` applies directly at
--       `F = overFunctor 𝒪_X U` and
--       `G = chartLocalizationReindex ⋙ representedSchemeReindex ⋙ Γ(Z, -)`, with `e = Iso.refl`
--       and `H = F ⋙ G` — the shape `AlgebraicGeometry.Space.derivedSectionsOverFunctorIso`
--       already uses — and `Stacks.Injectives.derivedPrecompIso` (which does have consumers, the
--       two isos of `StacksFrontier/AlgebraicGeometry/Spaces/ChartDerivedSectionsTransport.lean`)
--       then splits `R G` into the
--       two derived reindexings followed by `RΓ(Z, -)`.  `totalRightDerivedPrecompIso` is not
--       needed.
--       **This is proved, in exactly that shape**, in
--       `StacksFrontier/AlgebraicGeometry/Spaces/ChartTransportDerivedSections.lean`:
--       `AlgebraicGeometry.Space.derivedChartTransportSectionsIso` is
--       `derivedCompIsoOfComputes` at `F = overFunctor 𝒪_X U`, at the whole of `G` at once and at
--       `H = F ⋙ G`, with the underived input `chartTransportSectionsIso`;
--       `AlgebraicGeometry.Space.derivedChartTransportSectionsSplitIso` is `derivedPrecompIso` at
--       Stacks 04M0; and `AlgebraicGeometry.Space.derivedChartTransportIso` composes the two with
--       `AlgebraicGeometry.Space.derivedSectionsRepresentedSchemeReindexIso`.  All
--       three check in under a second at the default heartbeat ceiling.
--     * **What blocks the last link of (i) is a spelling pincer on `U`, and it is
--       neither the heartbeat cost of the composite nor a typing dilemma over `G`.**  The ring
--       identification
--       `(chartRingedSite B S hS X U).ringSheaf.obj.obj (op W)
--          = 𝒪_X.ringSheaf.obj.obj (op (e.functor.obj W).left)`
--       is `rfl` and *cheap* (0.2 s), and so are the induced equalities of `ModuleCat`s and of
--       the two functor categories — so the `ModuleCat` ring spellings and their `Category`
--       instances are **not** the obstruction.  What times out at
--       `whnf`/`isDefEq` after 200 000 heartbeats is the *collapsed* functor equality proved by
--       `rfl` in one step; it must be reached as `overEvaluationIso` applied to the `rfl`
--       of the reindexing (`chartLocalizationReindex ⋙ Γ(W, -) = Γ(e.functor.obj W, -)`, which is
--       itself `rfl` and cheap), never asserted directly.
--     * **The typing question over `U` is a pincer, and both of its jaws are compiled.**
--       `𝒪_X.ringSheaf.over U` does **not** elaborate at both
--       spellings of `U`: at `U : SmallEtale B S hS X.1` the term
--       `(smallEtaleRingedSite B S hS X.1 X.2).ringSheaf.over U` fails with
--       `failed to synthesize Category.{u, u + 1} (Over U)`, because `CategoryTheory.Over` carries
--       the free universe of the `PUnit` of its `CategoryTheory.Comma` and the goal asks search to
--       solve `max (u + 1) ?w =?= u + 1`.  (The *module documentation* of
--       `StacksFrontier/AlgebraicGeometry/Spaces/ChartTransportSections.lean` records this too.)
--       Pinning that category does
--       not repair it: a local
--       `Category.{u, u + 1} (Over U)` got by `inferInstanceAs` from
--       `((smallEtaleRingedSite …).over U).C` does not elaborate — the declaration fails after
--       21 s on the very goal it would supply.
--       At `U : (smallEtaleRingedSite B S hS X.1 X.2).C` the slice sheaf of rings *is* writable,
--       and that is the spelling
--       `StacksFrontier/AlgebraicGeometry/Spaces/ChartTransportDerivedSections.lean` works at.  But
--       there the other jaw closes: `SmallEtale.chartLocalizationEquivalence B S hS X.1 U` cannot
--       be written, its codomain needing the same `Category (Over U)`, so the chart that the
--       transport names cannot be mentioned; and the identification
--       `(representedSchemeRingedSite …).ringSheaf.obj.obj (op Z)
--          = 𝒪_X.ringSheaf.obj.obj (op chart)`
--       exceeds 200 000 heartbeats at the `.C` spelling while being **inside** the default ceiling
--       at `U : SmallEtale B S hS X.1` (compiled in both).
--     * **The last link of (i) is proved.**  That link — that the right derived functor of the
--       transport's sections *is* `RΓ(chart, -)` — does **not** need the slice sheaf of rings and
--       the chart written in one statement.
--       It is `AlgebraicGeometry.Space.derivedChartTransportChartIso`, with the
--       whole chain `AlgebraicGeometry.Space.derivedChartTransportSectionsChartIso`
--       (`StacksFrontier/AlgebraicGeometry/Spaces/ChartTransportDerivedChartSections.lean`); the
--       chain then meets `U` itself through
--       `AlgebraicGeometry.Space.derivedChartSectionsTopIso`, which is
--       `Stacks.Cohomology.HypercohomologyEdge.derivedSectionsRestrictIso` at
--       `AlgebraicGeometry.Space.openChartOfComparisonTopIso` and carries a restriction of
--       scalars that is not removable.  The two requirements do not have to be met in one
--       *statement*: the two
--       spellings of `U` are definitionally equal, a projection of a structure literal, so a
--       declaration stated at either spelling applies at the other with no transport, no
--       `eqToHom` and no new pinned instance — for instance
--       `AlgebraicGeometry.Space.derivedChartTransportIso` applied at
--       `U : SmallEtale B S hS X.1` and at `AlgebraicGeometry.Space.chartTransportSectionsIso`
--       applied at the `.C` spelling.  What the spellings restrict is only what may be *written*:
--       a statement that writes `CategoryTheory.Over U` needs `.C`, a statement that writes the
--       chart needs the other, and the two can sit in two declarations of one file.  So the
--       codomain ascription — sections at the chart read into the ring the transport produces,
--       `AlgebraicGeometry.Space.chartSectionsCrossed` — is made at
--       `U : SmallEtale B S hS X.1`, where the ring identification is cheap, and the derived
--       statement at the `.C` spelling, where the slice is writable; one additivity instance is
--       restated across the two, because
--       `CategoryTheory.Functor.Additive` of a `SheafOfModules.evaluation` is matched through the
--       type argument of `Opposite.op` and so is keyed to the spelling of the chart's type.  No
--       heartbeat ceiling is raised.
--     * Two things are out of reach in that file, and the first of the two is
--       diagnosed differently by the file that pays it; see the (i) bullet of the display above.
--       Composing the chain with the `⊤`-specialization *inside* it exceeds 200 000 heartbeats
--       at `whnf`, and that file's note attributes this to the concrete
--       `Z = AlgebraicGeometry.SmallEtale.opensObj … ⊤`.  It is not that: the same composite
--       exceeds the ceiling at an abstract `Z` as well, whenever it is stated on *functors*, and
--       it is inside the ceiling at the concrete `Z` when stated on *objects* — what is
--       expensive is the identification of the two `CategoryTheory.HasDerivedCategory` data, not
--       the ring identification, which is `rfl` and cheap at either `Z`.
--       The second holds as stated: the slice instances cannot be
--       *stated* at `U : SmallEtale B S hS X.1` at all — `(…).over U`, `(…).J.over U` and
--       `Over U` all fail there with `failed to synthesize Category.{u, u + 1} (Over U)` — which
--       is why they are re-enabled from the existing declarations and never restated.
--       It is narrower than "`(smallEtaleRingedSite …).over U` is unwritable at that spelling",
--       though: `AlgebraicGeometry.Space.isPseudoCoherentFrom_chartSchemeReindex_iff` and its
--       all-degrees companion are stated at `U : SmallEtale B S hS X.1` and write that term
--       both in an instance binder and in the conclusion, and
--       `StacksFrontier/AlgebraicGeometry/Spaces/ChartPseudoCoherentTransport.lean` compiles.  What
--       fails at that spelling
--       is the elaboration of `Over U` itself, hence of anything whose *own* type needs
--       `Category.{u, u + 1} (Over U)` to be synthesized rather than carried.
--       Second, restating the chart-side files is not harmless but destructive: changing the one
--       `variable` line
--       of `StacksFrontier/AlgebraicGeometry/Spaces/ChartPseudoCoherentTransport.lean` to the `.C`
--       spelling takes that file
--       from compiling to fifteen `failed to synthesize Category.{u, u + 1} (Over U)` — at
--       `isContinuous_chartLocalization_ringedSite`,
--       `isContinuous_chartLocalizationInverse_ringedSite`, `chartLocalizationPhi`,
--       `chartLocalizationSymmPhi`, their two `_unit` compatibilities,
--       `hasSheafify_chartLocalization` and the declarations after them — plus two `whnf`/
--       `isDefEq` heartbeat timeouts and a failing `rfl` in `additive_chartLocalizationReindex`.
--       `CategoryTheory.Over U` is taken over whichever `CategoryTheory.Category` instance is in
--       scope for the type of `U` — `AlgebraicGeometry.RingedSite.category`, a projection of a
--       structure instance, at the `.C` spelling, against the instance of
--       `AlgebraicGeometry.Space.SmallEtale` at the other — and the explicitly universe-pinned
--       `@`-applications of that file resolve only at the second.  The two types are
--       definitionally equal and the *statements* are unchanged either way; what changes is what
--       instance search can do with them.  So the chart-side declarations must stay at
--       `U : SmallEtale B S hS X.1`; the *new* declarations of the derived layer are at the `.C`
--       spelling, which is possible because they never mention the chart.
chartDerivedSections B S hS X hX U E ≅
  (HomologyComparison.derivedSections
      (smallEtaleRingedSite (associatedBigEtaleSite B) T hT).ringSheaf ⊤).obj
    ((representedSchemeReindex B S hS _).mapDerivedCategory.obj
      ((chartLocalizationReindex B S hS ⟨X, hX⟩ U).mapDerivedCategory.obj
        ((SheafOfModules.overFunctor
          (smallEtaleRingedSite B S hS X hX).ringSheaf U).mapDerivedCategory.obj E.obj)))

-- (ii) derived sections cross `ε`: `RΓ(T_étale, ε^*E₀) ≅ RΓ(T_Zar, E₀)` for `E₀` with
--      quasi-coherent cohomology.  This is Stacks 0D6I at the final object together with the
--      unit of Stacks 071Q.  **The crossing of `ε` itself is proved, module-valued**, as
--      `AlgebraicGeometry.SmallEtale.derivedModuleSectionsRestrictModuleIso`
--      (`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/`, file
--      `SmallEtaleDerivedSectionsOverObject.lean`), beside the
--      cohomology-group form `...cohomologyOverObjectRestrictModuleIso` and the group-valued
--      functor `...derivedSectionsOverObject`, which lands in `DerivedCategory AddCommGrpCat`
--      The module-valued `RΓ(U, -)` it is stated through exists by
--      `...hasRightDerivedFunctor_moduleSections`.
--      It carries a `ModuleCat.restrictScalars` on the étale side, and that is not an artefact:
--      `AlgebraicGeometry.SmallEtale.structureMap` at an open `V` is
--      `(AlgebraicGeometry.Scheme.Opens.topIso V).inv`, NOT the identity, so `𝒪_S(V)` and
--      `𝒪(ε(V))` are isomorphic rings and not equal ones — not even definitionally, their object
--      universes differing — and sections over `ε(V)` are `𝒪_S(V)`-modules only after transport,
--      without which (ii) cannot be stated.
--      **The second half of (ii) is proved as well, and with it the whole of (ii).**  The
--      right-hand side below is written `(derivedGlobalSectionsQuasicoherent A).obj E₀`, and
--      `derivedGlobalSectionsQuasicoherent` is built from
--      `AlgebraicGeometry.derivedGlobalSectionsOver (𝟙 (Spec A))`, a derived functor on the
--      ringed *space*, whereas what the crossing of `ε` delivers is module-valued derived
--      sections at `⊤` on the small Zariski *site*.  That is crossed by
--      `AlgebraicGeometry.derivedGlobalSectionsOverEvaluationIso`
--      (`StacksFrontier/AlgebraicGeometry/DerivedGlobalSectionsZariskiSite.lean`): the two
--      underived
--      functors are built from the same raw material — `AlgebraicGeometry.globalSectionsOver`
--      *is* `SheafOfModules.evaluation X.ringCatSheaf (op ⊤)` followed by the restriction of
--      scalars along `A ≅ Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)`, by `rfl` — so the content is only that a
--      total right derived functor postcomposed with an exact functor derives the composite,
--      which is
--      `Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedMapDerivedCategoryIso`,
--      restriction of scalars being exact.  It is stated for any `f : X ⟶ Spec A` and not only
--      for the identity of `Spec A`.
--      The two halves composed are
--      `AlgebraicGeometry.SmallEtale.derivedModuleSectionsGlobalSectionsOverIso`
--      (`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/`, file
--      `SmallEtaleDerivedGlobalSectionsOverBase.lean`).  It is
--      stated with `Rε_*` where the display below has `ε^*`; passing between the two is the unit
--      of Stacks 071Q, `AlgebraicGeometry.SmallEtale.derivedAssociatedModule_isEquivalence`, and
--      is the only thing between that composite and the display.  **Two** restrictions of scalars
--      survive in it, and neither is removable: the one on the étale side described just above,
--      and the one from `𝒪_S(⊤)` to the base ring `A`.
--      `AlgebraicGeometry.derivedSectionsBaseIso`
--      (`StacksFrontier/AlgebraicGeometry/ProperSupportCoherent/ExtFinitenessLeray.lean`)
--      is **not** this statement: it
--      crosses to `derivedGlobalSectionsOver (𝟙 (Spec A))` from
--      `derivedSectionsOverOpen`, the `Opens`-indexed ringed-space functor, not from the
--      ringed-site one.
RΓ(T_étale, (associatedModuleOfSheaf _ T hT).mapDerivedCategory.obj E₀) ≅
  (derivedGlobalSectionsQuasicoherent A).obj E₀

-- (iii) and hence, with Stacks 08E7, that `RΓ(U, E)` is the avatar: the statement the two sides
--       of 0DII actually have to be compared through.
PseudoCoherence.IsPseudoCoherentFrom (chartDerivedSections B S hS X hX U E) m ↔
  ((smallEtaleRingedSite B S hS X hX).over U).IsPseudoCoherentFrom
    ((SheafOfModules.overFunctor (smallEtaleRingedSite B S hS X hX).ringSheaf U
      ).mapDerivedCategory.obj E.obj) m
```

A nearby statement of the library is **not** a substitute.  Stacks 08H0 (2) for an affine algebraic
space, `AlgebraicGeometry.Space.derivedCoheratorIsoAssociatedDerivedGlobalSections`
(`StacksFrontier/AlgebraicGeometry/Spaces/AffineDerivedCoheratorGlobalSections.lean`), does say
`RQ_X ≅ (-)^~ ∘ RΓ(X, -)` with its own `RΓ(X, -)`,
`AlgebraicGeometry.Space.derivedModuleGlobalSectionsSmallEtale`; but it carries the
associated-module equivalence and a coherator as hypotheses, it says nothing about
pseudo-coherence, and — decisively — it takes `D(𝒪_X)` at `HasDerivedCategory.{u}`, from
`AlgebraicGeometry.Space.isGrothendieckAbelian_modules`, whereas this file and
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/RelativeDefinition.lean` take it
at `CategoryTheory.HasDerivedCategory.standard`, which is `{u + 1}`.  The two models are
inequivalent and the modules on the small étale site of an algebraic space are not known to be
Grothendieck abelian at `u + 1`, so the one cannot be exchanged for the other.

### 2. The covering sieve of affine squares, and the assembly over it

The run over this covering is in the file `RelativeAbsoluteSiteAssembly.lean` of the directory
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/`;
what follows is the account of its inputs, which that file's documentation does not repeat.

Both sides of 0DII are étale-local by construction, so the site-level predicate has to be
recovered from the chartwise one over an affine étale cover.  The local-nature input is available:
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_locally_general`
(`StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/LocalNature.lean`) is general in
all three universes and so does reach the small étale site of an algebraic space, and the
converse restriction is `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_derivedRestriction`
(`StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/Restriction.lean`).  The covering
those
two have to be run over **is available too**.

The two fit together with nothing in between, which is worth saying because it fixes the shape
(iii) has to be stated at.  The hypothesis of `...isPseudoCoherentFrom_of_locally_general` is,
verbatim,

`∀ U : X.C, ∃ S : Presieve U, Sieve.generate S ∈ X.J U ∧ ∀ ⦃V⦄ (f : V ⟶ U), S f →
  (X.over V).IsPseudoCoherentFrom ((SheafOfModules.overFunctor X.ringSheaf V
    ).mapDerivedCategory.obj E) m`

— that is, the right-hand side of (iii) quantified over a covering sieve, at the `X.C` spelling
of the object and with the slice written `X.over V`.  So (iii) must be stated at that spelling
to be usable here, and the covering to supply is
`AlgebraicGeometry.Space.generate_affineChartDiagram_mem_topology`.  Two nearby presieves are
**not** it: `AlgebraicGeometry.BigFppfOver.smallEtaleAffinePresieve` with
`...generate_smallEtaleAffinePresieve_mem`
(`StacksFrontier/AlgebraicGeometry/EtaleCohomology/FppfEtaleComparison/`, file
`QuasiCoherentPushforward.lean`) covers an object of
the small étale site of a *scheme* `S` over `B.toBigEtaleSite`, not an object of the small étale
site of an algebraic space, and it says nothing about the square over `f`; and
`AlgebraicGeometry.BigFppfOver.affineOverPresieve` in the same file is on the big site.

The relative condition is tested on *squares* `U ⟶ V` of affine charts, so a chartwise
statement at every affine chart of `X` needs the charts that sit in such a square to generate a
covering sieve of every object.  That is exactly Stacks 03G2 in the form
`AlgebraicGeometry.Space.generate_affineChartDiagram_mem_topology`
(`StacksFrontier/AlgebraicGeometry/Spaces/AffineChartDiagramCofinal.lean`): for `f : X ⟶ Y` a
morphism of `AlgebraicGeometry.Space.AlgebraicSpaces` and any `U : SmallEtale B S hS X.1`, the
presieve of those `Z ⟶ U` with `chartScheme Z` affine which are the source chart of a
commuting square `AlgebraicGeometry.Space.ChartDiagram` over `f` whose chart of `Y` is affine
generates a covering sieve of `U`; the condition `Q` on the chart of `Y` is a parameter, so
`fun _ => True` recovers the bare statement.  Its family form is
`AlgebraicGeometry.Space.exists_affine_chartDiagram_ofArrows`.  The square is carried by
`ChartDiagram`, whose `comm` field is `Z.obj.hom ≫ f = yoneda.map g ≫ V.obj.hom`, the symmetric
spelling of the commutation the definition of
`AlgebraicGeometry.Space.IsRelativelyPseudoCoherentFrom` quantifies over; the two differ by
`Eq.symm` and by substituting the `d.U = Z` of the presieve.

The mathematics is the source's own "by étale localization we may assume `X` and `Y` are
schemes", and the proof does it as follows.  Take a surjective étale atlas
`b : yoneda.obj V ⟶ Y` from `IsAlgebraicSpace.exists_atlas` and lift it along
`U.obj.hom ≫ f` by Stacks 02X1,
`AlgebraicGeometry.Space.exists_surjective_etale_presentation_lift`, applied at the
*representable* algebraic space of `U` (`AlgebraicGeometry.Space.isAlgebraicSpace_yoneda`);
this is the base change of the chart `b`, which is representable, and not a base change of `f`,
so no representability of `f` is used.  The lift is a surjective étale `W₀ ⟶ U` of the site
together with `α : W₀ ⟶ V` making one global square commute.  Restricting that square
(`AlgebraicGeometry.Space.ChartDiagram.restrictOpens`) to an affine open `P` of `V` and an
affine open `O` of `W₀` inside the preimage of `P` gives a square of affine charts, and the two
applications of `AlgebraicGeometry.Scheme.isBasis_affineOpens` — first at the image point in
`V`, then at the point of `W₀` inside the preimage — make those restrictions jointly surjective
over `W₀`, hence, with surjectivity of `W₀ ⟶ U`, over `U`.

Two consequences for the assembly.  First, the covering is indexed by pairs of affine opens,
not by the affine charts of `X`: an affine chart of `X` need not map into a single affine chart
of `Y`, so the squares are not indexed by their source charts and only cofinality is available.
Second, the statement needs `Y` to be an algebraic space — the atlas is what is lifted —
whereas `AlgebraicGeometry.Space.IsRelativelyPseudoCoherentFrom` takes `Y` as a bare presheaf;
the site-level theorem will therefore carry an `IsAlgebraicSpace` hypothesis on `Y` that the
definition does not.  That is not a weakening: it is the source's own "morphism of algebraic
spaces".

`AlgebraicGeometry.Space.smallBaseChange` (Stacks 03G2 (4)) is **not** the tool, and the
proof does not use it: it carries charts of the target to charts of the source along a morphism
it requires to be relatively representable, which a morphism of algebraic spaces need not be,
and here it is the chart morphism and not `f` that is representable.

### 3. The all-degrees form

0DII as stated is the plain pseudo-coherence of Stacks 08FT (3), not the fixed-degree one, and
that clause asks for **one** complex which is `m`-pseudo-coherent for every `m` — which a family
of degreewise statements does not provide; the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartPseudoCoherentTransport.lean` say so of the chart
transport, which is why that file carries its own all-degrees companions.  **Three things on the
all-degrees side of the chain are proved**, and the list below says where each one is.

* The quantifier swap is
  `AlgebraicGeometry.RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom`
  (`StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/Summands.lean`), the forward
  direction of Stacks 08FU (2).  Its one input,
  `AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_of_iso_general`, is public, so the
  swap is stated there with the same binders, universes and proof term as the file's own
  `private` copy of it.
* Both companions exist.  `AlgebraicGeometry.RingedSite.isPseudoCoherent_of_locally_general` is
  in `StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/Summands.lean`, beside the swap
  rather than beside the fixed-degree locality statement, because it is the swap that it needs and
  that file imports `StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/LocalNature.lean`
  and not the other way round; its hypothesis is the degreewise local one, with the covering sieve
  allowed to depend on the degree, which is what the fixed-degree statement can be fed.
  `AlgebraicGeometry.RingedSite.isPseudoCoherent_derivedRestriction_general` is in
  `StacksFrontier/AlgebraicGeometry/PseudoCoherentSites/RestrictionGeneral.lean` beside
  `...isPseudoCoherentFrom_derivedRestriction_general`, and needs no swap at all: the complex-level
  input `AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_restrictComplex_general`
  (`StacksFrontier/AlgebraicGeometry/PseudoCoherentSites/RestrictionGeneral.lean`) is already stated
  at
  one complex and an arbitrary degree, so the single complex that pseudo-coherence provides
  restricts directly.
* Stacks 08HE in all degrees is
  `AlgebraicGeometry.SmallEtale.pseudoCoherentIffAssociatedModule_allDegrees`
  (`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/`, file
  `SmallEtalePseudoCoherentDescent.lean`).
  Once the swap is public this is the fixed-degree tag with the swap applied on *both* sites —
  once to unfold the Zariski side into its degrees, once to reassemble the étale side out of
  them — so it needs no new mathematics.  It carries no `@[stacks 08HE]` attribute:
  the bare one sits on the fixed-degree form, which is the tag's own statement.

None of section 3 is mathematics; all of it is stating what is proved at the shape the capstone
needs.

Accordingly the two `@[stacks 0DII]` attributes in this file carry clause strings naming the
localization that is proved here: the right-hand side they state is the chartwise condition, not
the site-level predicate.  The bare attribute sits on
`AlgebraicGeometry.Space.isRelativelyPseudoCoherent_iff_isPseudoCoherent`, in
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/
RelativeAbsoluteChartDictionary.lean` — the unconditional algebraic-space statement whose
right-hand side *is* the site-level predicate.  Section 3 above and the derived-sections dictionary
of "The route to 0DII" are discharged there; the scheme case keeps its own clause string.

## Implementation notes

Both sides quantify over the same squares, so everything happens on one square, in
`AlgebraicGeometry.Space.relativePseudoCoherence_chart_iff`: there the two clauses of Stacks
0DHQ, `PseudoCoherence.relativelyPseudoCoherent_iff_pseudoCoherent`, are read at the ring map
`𝒪_Y(V) → 𝒪_X(U)`.  Its hypothesis is that the ring map be pseudo-coherent, and on a square of
*affine* charts `AlgebraicGeometry.HasRingHomProperty.appTop` turns flatness and local finite
presentation of the scheme morphism into `Module.Flat` and `Algebra.FinitePresentation` of the
map of section rings, after which Stacks 067J,
`Algebra.PseudoCoherent.of_flat_of_finitePresentation`, concludes.  This is the same device by
which the definition of relative pseudo-coherence gets its `Algebra.FiniteType` instance from
"`f` is locally of finite type", so no finiteness hypothesis is imposed beyond the source's own
"`f` is flat and locally of finite presentation".

Local finite type, which the definition of the relative notion takes as an argument, is not a
separate hypothesis: it is Stacks 0464, that is
`AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation`, applied to
local finite presentation.

The derived categories are the ones of `CategoryTheory.HasDerivedCategory.standard`, made a
local instance as in
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/RelativeDefinition.lean`, and
`AlgebraicGeometry.Space.hasRightDerivedFunctor_chartSections` is a local instance for the same
reason: it is what makes `RΓ(U, -)` exist.

## References

* [Stacks Project, Tag 0DII](https://stacks.math.columbia.edu/tag/0DII)
* [Stacks Project, Tag 09UU](https://stacks.math.columbia.edu/tag/09UU)
* [Stacks Project, Tag 0DHQ](https://stacks.math.columbia.edu/tag/0DHQ)
* [Stacks Project, Tag 067J](https://stacks.math.columbia.edu/tag/067J)
* [Stacks Project, Tag 0CSY](https://stacks.math.columbia.edu/tag/0CSY)
* [Stacks Project, Tag 0CSX](https://stacks.math.columbia.edu/tag/0CSX)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08FU](https://stacks.math.columbia.edu/tag/08FU)
* [Stacks Project, Tag 08H0](https://stacks.math.columbia.edu/tag/08H0)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
* [Stacks Project, Tag 0464](https://stacks.math.columbia.edu/tag/0464)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
* [Stacks Project, Tag 08E7](https://stacks.math.columbia.edu/tag/08E7)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 06VT](https://stacks.math.columbia.edu/tag/06VT)
* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08DB](https://stacks.math.columbia.edu/tag/08DB)
* [Stacks Project, Tag 07A5](https://stacks.math.columbia.edu/tag/07A5)
* [Stacks Project, Tag 0D6H](https://stacks.math.columbia.edu/tag/0D6H)
* [Stacks Project, Tag 0D6I](https://stacks.math.columbia.edu/tag/0D6I)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)

attribute [local instance] hasRightDerivedFunctor_chartSections

variable [HasSheafify (smallEtaleRingedSite B S hS X hX).J AddCommGrpCat.{u}]
    [(smallEtaleRingedSite B S hS X hX).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)

/-! ### One square of affine étale charts -/

/-- **Stacks 0DHQ on one square of affine étale charts.** Let `f : X ⟶ Y` be flat and locally of
finite presentation, and let `U ⟶ V` be a morphism of étale scheme charts over `f` with both
charts affine.  Then the complex `RΓ(U, E)` of `𝒪_X(U)`-modules is `m`-pseudo-coherent relative
to `𝒪_Y(V)` exactly when it is `m`-pseudo-coherent over `𝒪_X(U)`, and pseudo-coherent relative
to `𝒪_Y(V)` exactly when it is pseudo-coherent over `𝒪_X(U)`.

The scheme morphism of the square is flat and locally of finite presentation by the defining
chart conditions of `AlgebraicGeometry.Space.IsFlat` and
`AlgebraicGeometry.Space.IsLocallyOfFinitePresentation`, so with both charts affine
`AlgebraicGeometry.HasRingHomProperty.appTop` makes `𝒪_Y(V) → 𝒪_X(U)` a flat ring map of finite
presentation; Stacks 067J makes it pseudo-coherent, and Stacks 0DHQ applies. -/
theorem relativePseudoCoherence_chart_iff
    (hflat : IsFlat B S hS f) (hfp : IsLocallyOfFinitePresentation B S hS f)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X hX) (m : ℤ)
    (U : SmallEtale B S hS X) (V : SmallEtale B S hS Y)
    (g : (SmallEtale.toOver B S hS X).obj U ⟶ (SmallEtale.toOver B S hS Y).obj V)
    (hc : yoneda.map g ≫ V.obj.hom = U.obj.hom ≫ f)
    (hU : IsAffine (chartScheme U)) (hV : IsAffine (chartScheme V)) :
    letI := hU
    letI := hV
    letI : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g) :=
      isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfp _ _ U.obj.hom V.obj.hom
        g U.property V.property hc
    letI : Algebra ((structurePresheaf B S hS Y).obj (op V))
        ((structurePresheaf B S hS X).obj (op U)) :=
      (((BigFppfOver.toScheme B S hS).map g).appTop.hom).toAlgebra
    letI : Algebra.FiniteType ((structurePresheaf B S hS Y).obj (op V))
        ((structurePresheaf B S hS X).obj (op U)) :=
      HasRingHomProperty.appTop (@LocallyOfFiniteType) ((BigFppfOver.toScheme B S hS).map g)
        inferInstance
    (PseudoCoherence.IsRelativelyPseudoCoherentFrom
        (R := (structurePresheaf B S hS Y).obj (op V))
        (chartDerivedSections B S hS X hX U E) m ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
        (chartDerivedSections B S hS X hX U E) m) ∧
    (PseudoCoherence.IsRelativelyPseudoCoherent
        (R := (structurePresheaf B S hS Y).obj (op V))
        (chartDerivedSections B S hS X hX U E) ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherent
        (chartDerivedSections B S hS X hX U E)) := by
  let := hU
  let := hV
  let : _root_.AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map g) :=
    hflat _ _ U.obj.hom V.obj.hom g U.property V.property hc
  let : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map g) :=
    hfp _ _ U.obj.hom V.obj.hom g U.property V.property hc
  let : Algebra ((structurePresheaf B S hS Y).obj (op V))
      ((structurePresheaf B S hS X).obj (op U)) :=
    (((BigFppfOver.toScheme B S hS).map g).appTop.hom).toAlgebra
  let : Module.Flat ((structurePresheaf B S hS Y).obj (op V))
      ((structurePresheaf B S hS X).obj (op U)) :=
    HasRingHomProperty.appTop (@_root_.AlgebraicGeometry.Flat)
      ((BigFppfOver.toScheme B S hS).map g) inferInstance
  let : Algebra.FinitePresentation ((structurePresheaf B S hS Y).obj (op V))
      ((structurePresheaf B S hS X).obj (op U)) :=
    HasRingHomProperty.appTop (@LocallyOfFinitePresentation)
      ((BigFppfOver.toScheme B S hS).map g) inferInstance
  exact PseudoCoherence.relativelyPseudoCoherent_iff_pseudoCoherent
    (Algebra.PseudoCoherent.of_flat_of_finitePresentation _ _)
    (chartDerivedSections B S hS X hX U E) m

/-! ### Stacks 0DII by étale localization -/

/-- **Stacks 0DII in a fixed degree, by étale localization.** Let `f : X ⟶ Y` be a flat morphism
of algebraic spaces over `S` which is locally of finite presentation, let `E` be an object of
`D_QCoh(𝒪_X)` and let `m` be an integer.  Then `E` is `m`-pseudo-coherent relative to `Y` if and
only if, on every commuting square of affine étale scheme charts `U` of `X` and `V` of `Y` over
`f`, the complex `RΓ(U, E)` is `m`-pseudo-coherent over the ring `𝒪_X(U)`.

Relative `m`-pseudo-coherence is by definition the relative condition on those same squares, so
the two sides differ square by square only, and on one square the equivalence is
`AlgebraicGeometry.Space.relativePseudoCoherence_chart_iff`. -/
@[stacks 0DII "the fixed-degree etale-chart localization: relative m-pseudo-coherence over Y is \
m-pseudo-coherence of RGamma(U, E) over O_X(U) on every square of affine etale charts"]
theorem isRelativelyPseudoCoherentFrom_iff_forall_chart
    (hflat : IsFlat B S hS f) (hfp : IsLocallyOfFinitePresentation B S hS f)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X hX) (m : ℤ) :
    IsRelativelyPseudoCoherentFrom B S hS X hX f
        (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfp) E m ↔
      ∀ (U : SmallEtale B S hS X) (V : SmallEtale B S hS Y)
          (g : (SmallEtale.toOver B S hS X).obj U ⟶ (SmallEtale.toOver B S hS Y).obj V),
          yoneda.map g ≫ V.obj.hom = U.obj.hom ≫ f →
          IsAffine (chartScheme U) → IsAffine (chartScheme V) →
        StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
          (chartDerivedSections B S hS X hX U E) m :=
  forall₅_congr fun U V g hc hU => forall_congr' fun hV =>
    (relativePseudoCoherence_chart_iff B S hS X hX f hflat hfp E m U V g hc hU hV).1

/-- **Stacks 0DII by étale localization.** Let `f : X ⟶ Y` be a flat morphism of algebraic
spaces over `S` which is locally of finite presentation and let `E` be an object of
`D_QCoh(𝒪_X)`.  Then `E` is pseudo-coherent relative to `Y` if and only if, on every commuting
square of affine étale scheme charts `U` of `X` and `V` of `Y` over `f`, the complex `RΓ(U, E)`
is pseudo-coherent over the ring `𝒪_X(U)` — the target playing no role.

This is the all-degrees clause of
`AlgebraicGeometry.Space.relativePseudoCoherence_chart_iff` on each of the squares that relative
pseudo-coherence of Stacks 0CSY is tested on; see "What is proved, and what the right-hand side
says" in the module docstring for the sense in which the right-hand side is the absolute
condition. -/
@[stacks 0DII "the etale-chart localization: pseudo-coherence relative to Y is pseudo-coherence \
of RGamma(U, E) over O_X(U) on every square of affine etale charts"]
theorem isRelativelyPseudoCoherent_iff_forall_chart
    (hflat : IsFlat B S hS f) (hfp : IsLocallyOfFinitePresentation B S hS f)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X hX) :
    IsRelativelyPseudoCoherent B S hS X hX f
        (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfp) E ↔
      ∀ (U : SmallEtale B S hS X) (V : SmallEtale B S hS Y)
          (g : (SmallEtale.toOver B S hS X).obj U ⟶ (SmallEtale.toOver B S hS Y).obj V),
          yoneda.map g ≫ V.obj.hom = U.obj.hom ≫ f →
          IsAffine (chartScheme U) → IsAffine (chartScheme V) →
        StacksDraft.PseudoCoherence.IsPseudoCoherent
          (chartDerivedSections B S hS X hX U E) :=
  let key := fun U V g hc hU hV =>
    (relativePseudoCoherence_chart_iff B S hS X hX f hflat hfp E 0 U V g hc hU hV).2
  ⟨fun h U V g hc hU hV => (key U V g hc hU hV).mp fun m => h m U V g hc hU hV,
    fun h m U V g hc hU hV => (key U V g hc hU hV).mpr (h U V g hc hU hV) m⟩

end AlgebraicGeometry.Space

end
