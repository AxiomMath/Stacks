module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EquivariantQuasicoherentPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientPrestackPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.Composition
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.TransitionReindexComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackQuasicoherentMissingInputs
public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcHomSheafRefinement
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteLocalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteLocalizationExtensions
public import StacksFrontier.Deformation.Groupoid.Loops
public import StacksFrontier.CategoryTheory.Sites.Glueing.SheafConditionLocalOnCover

/-!
# The backward functor of Stacks 06WT: its module-level data, and what remains of it

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `A` over a
scheme `S` of a big fppf site, and let `[U/_pR]` be its pointwise quotient
(`AlgebraicGeometry.Stack.quotientPrestack`).  In the proof of Stacks 06WT the *backward*
functor `QCoh(U, R, s, t, c) ⟶ QCoh(𝒪_{[U/_pR]})` is constructed by hand: a quasi-coherent
module `(𝒢, α)` on the groupoid is sent to the module `ℱ` with

```
ℱ(T, u) = Γ(T, u_small^* 𝒢),
```

where `(T, u)` runs over the objects of `[U/_pR]` — a test object `T` of the site together with
a `T`-point `u` of the object space `U` — and `u_small^*` is the inverse image of `𝒪`-modules
along `u`, read on small étale sites.  The source then verifies quasi-coherence of `ℱ` through
Stacks 06WI and *omits* the verification that the two functors are quasi-inverse.

This module lands the data of that formula which does not depend on the packaging:

* the morphism of algebraic spaces `u : T ⟶ U` that a `T`-point of `U` is
  (`AlgebraicGeometry.Space.yonedaSectionHom`), with its two naturality laws;
* the module `u_small^*𝒢` (`AlgebraicGeometry.Stack.prestackPointModule`), the morphism it
  induces (`…prestackPointMap`), the module read on the representing scheme
  (`…prestackPointSchemeModule`) and its global sections (`…prestackPointSections`) — the
  right-hand side of the displayed formula, at the ring `Γ(T, 𝒪_T)` the structure sheaf of
  `[U/_pR]` takes at `(T, u)`;
* the transition morphisms the formula has to carry in order to be a module on `[U/_pR]` at all:
  `AlgebraicGeometry.Space.groupoidPullbackTransitionAt` along an arrow into the arrow space,
  `AlgebraicGeometry.Space.groupoidPullbackTransitionBaseChange` with a base change in front, and
  the two of them at the representable algebraic space of a test object —
  `AlgebraicGeometry.Stack.prestackArrowTransition` and
  `AlgebraicGeometry.Stack.prestackTransition`, the second attached to a morphism of `[U/_pR]` in
  the `(f, a)` form of Stacks 02XV;
* the naturality of both transitions in the groupoid module, which is what makes the family
  functorial in `(𝒢, α)` and is where the compatibility field of
  `AlgebraicGeometry.Space.QuasicoherentModule.Hom` is consumed;
* the *unit* half of the coherence of the transition — along the unit arrow of the groupoid the
  transition is the identity — which is where the `unit` field of
  `AlgebraicGeometry.Space.QuasicoherentModule` is consumed;
* the *composition* half of that coherence — the transition along a composite of two morphisms is
  the composite of the two transitions — which is where the `cocycle` field of
  `AlgebraicGeometry.Space.QuasicoherentModule` is consumed, read at a composable pair of arrows
  into the arrow space, together with the compatibility of the Stacks 03LU comparison with a
  composite base change.

## Main definitions

* `AlgebraicGeometry.Space.yonedaSectionHom`: a section of an algebraic space over a test object,
  read as a morphism out of the representable algebraic space of that object.
* `AlgebraicGeometry.Space.groupoidPullbackTransitionAt`: the transition morphism of a groupoid
  module reindexed along an arrow into the arrow space, with its two endpoints named, and
  `AlgebraicGeometry.Space.groupoidPullbackTransitionBaseChange`: the same after a base change.
  Both at a general test space.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.arrowComp`: the composite of a composable pair of
  arrows into the arrow space, which at the representable algebraic space of a test object is the
  composite of two `T`-points of the arrow space in the groupoid of `T`-points.
* `AlgebraicGeometry.Stack.prestackPointModule`: `u_small^*𝒢`, and
  `AlgebraicGeometry.Stack.prestackPointMap`: the morphism of those a morphism of groupoid
  modules induces — the backward functor's action on morphisms.
* `AlgebraicGeometry.Stack.prestackPointSchemeModule` and
  `AlgebraicGeometry.Stack.prestackPointSections`: `u_small^*𝒢` read on the representing scheme,
  and `Γ(T, u_small^*𝒢)`.
* `AlgebraicGeometry.Stack.prestackArrowTransition` and
  `AlgebraicGeometry.Stack.prestackTransition`: the two transitions at the representable
  algebraic space of a test object.
* `AlgebraicGeometry.Stack.prestackPointModuleFunctor`: the formula as a functor in the groupoid
  module, at a fixed object of `[U/_pR]`.
* `AlgebraicGeometry.Stack.prestackPointSectionsFunctor`: **the comparison of global sections**,
  which turns an `𝒪`-module on the small étale site of `h_T` into a `Γ(T, 𝒪_T)`-module and a
  morphism of those into a `Γ(T, 𝒪_T)`-linear map, and
  `AlgebraicGeometry.Stack.prestackPointSectionsFunctorAt`: the two composed, the values of the
  backward functor at one object of `[U/_pR]` as a functor in `(𝒢, α)`.
* `AlgebraicGeometry.Stack.prestackArrowTransitionSections`: the restriction map of the backward
  functor along a morphism of `[U/_pR]` over the identity of the test object, on global sections.
* `AlgebraicGeometry.Stack.PrestackBackwardFunctor`: **the residue**, the packaging of the
  displayed formula into a functor into `QCoh(𝒪_{[U/_pR]})`.

## Main results

* `AlgebraicGeometry.Space.representedSpaceMap_comp_yonedaSectionHom` and
  `AlgebraicGeometry.Space.yonedaSectionHom_comp`: the two naturality laws of a section read as a
  morphism of algebraic spaces — in the test object and in the target space.  The second of them
  is what identifies `(t ∘ a)^*𝒢` and `(s ∘ a)^*𝒢` with the two values of
  `prestackPointModule`, and so is what makes `prestackArrowTransition` typecheck.
* `AlgebraicGeometry.Space.groupoidPullbackTransitionAt_naturality` and
  `AlgebraicGeometry.Space.groupoidPullbackTransitionBaseChange_naturality`: both transitions are
  natural in the groupoid module.  These are the statements that make the family functorial in
  `(𝒢, α)` rather than merely defined for each one, and the second of them is the naturality of
  the backward functor's restriction map.
* `AlgebraicGeometry.Space.groupoidPullbackTransitionAt_identityArrow`: **the unit law.**  Along
  the unit arrow of the groupoid at a morphism into the object space the transition is the
  identity; the unit condition of Stacks 0441 at the unit arrow itself is enough, by
  `AlgebraicGeometry.Space.TransitionUnit.comp`.  The identity morphism of `[U/_pR]` at an object
  `(T, w)` is the one whose arrow component is the unit arrow at `w`, so this is the identity law
  of the backward functor's restriction map.
* `AlgebraicGeometry.Space.groupoidPullbackTransitionAt_comp` and
  `AlgebraicGeometry.Space.groupoidPullbackTransitionBaseChange_comp`: **the composition law.**
  Along an arrow which the cocycle condition presents as a composite the transition is the
  composite of the two transitions, and the same with a base change in front, which is the
  restriction map of the backward functor.  Two inputs go into the second: the cocycle condition
  of Stacks 0441, through the first, and
  `AlgebraicGeometry.Space.modulePullbackCompIso_inv_comp_map_comp`, the compatibility of the
  composition comparison of Stacks 03LU with a composite base change.
  `AlgebraicGeometry.Space.transitionCocycle_arrowComp` discharges the cocycle hypothesis of both
  from the `cocycle` field of `AlgebraicGeometry.Space.QuasicoherentModule`, through
  `AlgebraicGeometry.Space.TransitionCocycle.comp`, exactly as the unit law goes through
  `AlgebraicGeometry.Space.TransitionUnit.comp`; the two laws with that hypothesis discharged are
  `AlgebraicGeometry.Space.groupoidPullbackTransitionAt_arrowComp` and
  `AlgebraicGeometry.Space.groupoidPullbackTransitionBaseChange_arrowComp`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.arrowComp_yonedaSectionHom`: at the representable
  algebraic space of a test object the composite of a composable pair of arrows is the composite
  of the two `T`-points in the groupoid of `T`-points of Stacks 043W.  This is what makes the
  cocycle law above the `cocycle` field *read at a pair of `T`-points of the arrow space*, which
  is the form the backward functor needs.
* `AlgebraicGeometry.Stack.prestackArrowTransition_eq` and
  `AlgebraicGeometry.Stack.prestackTransition_eq`: the two transitions at a representable
  algebraic space are those general constructions, which is what carries the two naturality laws
  to them.  Their docstrings record why the naturality square is proved at a general test space
  and transported rather than restated at the representable one.
* `AlgebraicGeometry.Stack.prestackPointSections_eq`: the right-hand side of the displayed
  formula is the comparison of global sections applied to the inverse image, on the nose.  This
  is what makes the functor in the groupoid module a functor of *the source's* values.
* `AlgebraicGeometry.Stack.isQuasicoherentOnSite_prestackPointModule`: the module of the formula
  is quasi-coherent, by Stacks 03GA.  This is the hypothesis every base change of the Zariski
  restriction asks for, and — through
  `AlgebraicGeometry.Stack.isQuasicoherent_prestackPointSchemeModule`, the same statement for the
  module read on the representing scheme — the hypothesis of Stacks 03DT.
* `AlgebraicGeometry.Stack.isSheaf_fppf_quasiCoherentPresheaf_prestackPointSchemeModule` and
  `AlgebraicGeometry.Stack.isSheaf_localizedFppf_prestackPointSections`: **Stacks 03DT at the
  module of the formula**, over the schemes over `T` and then — across the equivalence of sites of
  Stacks 06WI — on the localization of `[U/_pR]` at the object `(T, w)`.  Both carry no
  hypothesis; the hypothesis of Stacks 03DT is the theorem
  `AlgebraicGeometry.fpqcDescentOfQuasicoherentHoms`.
* `AlgebraicGeometry.Stack.isSheaf_fppf_of_prestackPointSections`: **item 2 of "What remains,
  precisely", discharged.**  A presheaf on the site of `[U/_pR]` which is a sheaf for some
  inherited associated topology and whose restriction to each slice is the formula's
  pullback-sections presheaf is a sheaf for the inherited fppf topology.  Its two hypotheses are
  item 1's output and nothing more.
* `AlgebraicGeometry.Stack.pointwiseQuotientGroupoidEquivalence_of_prestackBackwardFunctor`:
  a backward functor which is an equivalence is
  `AlgebraicGeometry.Stack.PointwiseQuotientGroupoidEquivalence`, the one remaining hypothesis of
  the carrier of Stacks 06WT.  This is the source's own logic — the backward functor together
  with the verification it omits — and it is why the residue is stated as a functor and not as a
  bare `Nonempty` of an equivalence.

## What remains, precisely

`AlgebraicGeometry.Stack.PrestackBackwardFunctor` is the residue, and it is three things, none of
which is a citation:

1. **The presheaf of modules.**  The values `prestackPointSections G M T w` have to be assembled
   into a presheaf of `𝒪_{[U/_pR]}`-modules on the site of `[U/_pR]`, with restriction along a
   morphism of `[U/_pR]` given by `prestackTransition` followed by the comparison of global
   sections.  Between `prestackTransition` and that restriction map sits the *coherence* of the
   transition, of which there are two halves, and **both are now proved**: the identity half is
   `AlgebraicGeometry.Space.groupoidPullbackTransitionAt_identityArrow`, from the `unit` field of
   `AlgebraicGeometry.Space.QuasicoherentModule`, and the composition half is
   `AlgebraicGeometry.Space.groupoidPullbackTransitionBaseChange_comp` — with its cocycle
   hypothesis discharged from the `cocycle` field,
   `AlgebraicGeometry.Space.groupoidPullbackTransitionBaseChange_arrowComp`.  Neither half is a
   citation; the source constructs the backward functor by hand and states neither.

   What is left of this step is therefore the *packaging* and not the coherence.  Of that
   packaging the **comparison of global sections is proved**: it is
   `AlgebraicGeometry.Stack.prestackPointSectionsFunctor`, the functor which restricts an
   `𝒪`-module on the small étale site of `h_T` to the Zariski site of the representing scheme
   and takes global sections over `Γ(T, 𝒪_T)`, and it turns a morphism of such modules into a
   `Γ(T, 𝒪_T)`-linear map of sections because it is a functor.  With it the formula is a functor
   in the groupoid module at each object of `[U/_pR]`
   (`AlgebraicGeometry.Stack.prestackPointSectionsFunctorAt`), whose value is
   `prestackPointSections G M T w` on the nose
   (`AlgebraicGeometry.Stack.prestackPointSections_eq`), and the restriction map along a morphism
   *over the identity of `T`* — by Stacks 02XV those are exactly the `T`-points of the arrow
   space, and over the identity no base change intervenes — is
   `AlgebraicGeometry.Stack.prestackArrowTransitionSections`.

   What is left is the restriction map along a morphism with a nontrivial arrow of the site.
   Reading `AlgebraicGeometry.Stack.prestackTransition` on global sections through the Zariski
   restriction means carrying that restriction across the base change along `f`, which is
   `AlgebraicGeometry.Space.representedZariskiRestrictionBaseChangeIso` (its quasi-coherence
   hypothesis is discharged by `AlgebraicGeometry.Stack.isQuasicoherentOnSite_prestackPointModule`,
   Stacks 03GA).  That comparison is
   `AlgebraicGeometry.Space.restrictToChartSchemeBaseChangeIso`, a *named* isomorphism and not a
   witness chosen through `Nonempty.some` out of a `Nonempty` of an isomorphism, so the base
   change on this route is determined by its arguments and laws about it are statable: no identity
   law and no composition law is a statement with a truth value about an arbitrary chosen
   isomorphism.  Its unit and composition coherences are not
   proved, and would need coherences of
   `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso`, of which the development has
   none.

   A route to the sections which does not pass through the Zariski comparison at all is also
   available, and it is the one to build the restriction map from: the `sections` field of the
   residue asks only for an `≃+`, the global sections of a chart restriction are canonically the
   sections of the module over the chart
   (`AlgebraicGeometry.Space.restrictToChartTopSectionsEquiv`, from
   `AlgebraicGeometry.Space.restrictToChartIsoChartRestrictionSheaf` and
   `AlgebraicGeometry.Space.chartRestrictionSheaf_obj`), and a morphism of the site acts on
   sections over a chart by `AlgebraicGeometry.Space.modulePullbackChartSection`.  The restriction
   map built that way is `AlgebraicGeometry.Stack.prestackTransitionSections` of
   `StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/QuotientPrestackBackwardSections.lean`, whose
   module documentation names what its identity and composition laws still need.

   A second, independent wall sits on the same side.  No *law* relating the maps on sections may
   be restated at the representable algebraic space of a test object, because every such law is
   an equation whose two sides are `≫` of morphisms of `AlgebraicGeometry.Space.Modules` there.
   At each of three strengths this fails with the elaborator's
   recursion budget exhausted: a `rw` with `CategoryTheory.Functor.map_comp`, the same step in
   term mode, and even the bare formation of a `CategoryTheory.NatTrans` between two functors
   landing in `AlgebraicGeometry.Space.Modules` at `AlgebraicGeometry.Space.yonedaSpace`.  So the
   unit and composition laws of the restriction map, and the naturality of
   `AlgebraicGeometry.Stack.prestackArrowTransitionSections` in the groupoid module, have to be
   consumed from the general-test-space statements listed under "Main results" and never rewritten
   at `h_T`; `AlgebraicGeometry.Stack.prestackArrowTransition_eq` and
   `AlgebraicGeometry.Stack.prestackTransition_eq` are what carry them.

   Both coherence laws are stated at a *general* test space, and transported to the
   representable algebraic space of a test object by
   `AlgebraicGeometry.Stack.prestackArrowTransition_eq` and
   `AlgebraicGeometry.Stack.prestackTransition_eq` rather than restated there.  That is the same
   discipline the naturality laws follow, and for the same reason: a composition law
   written out at `AlgebraicGeometry.Space.yonedaSpace` exhausts the elaborator's `whnf` budget
   and then the kernel's, every category instance in sight carrying
   `AlgebraicGeometry.isAlgebraicSpace_yoneda` inside a small étale ringed site.  Two further
   results are recorded for a consumer who works there: the composable pair and its composite
   are a pair of `T`-points of the arrow space and their composite in the groupoid of `T`-points
   (`AlgebraicGeometry.GroupoidInAlgebraicSpaces.arrowComp_yonedaSectionHom`), and the source of
   that composite agrees with the source of the second point only propositionally, so the two
   sides of the law there are joined by
   `AlgebraicGeometry.Space.groupoidPullbackTransitionBaseChange_comp_pullbackTransport`.
2. **The sheaf condition** for the inherited fppf topology, which is fppf descent for the sections
   of a quasi-coherent module.  **This step is proved**, over the presheaf of item 1 and
   with no other hypothesis: it is
   `AlgebraicGeometry.Stack.isSheaf_fppf_of_prestackPointSections`.

   The analogue one level down — for the presheaf of Stacks 03DS on the schemes over a fixed
   scheme — is `AlgebraicGeometry.quasiCoherentPresheaf_isSheaf_fppf` of
   `StacksFrontier/AlgebraicGeometry/Descent/PullbackSectionsSheaf/Basic.lean`, which is Stacks
   03DT. That one carries the hypothesis `AlgebraicGeometry.FpqcDescentOfQuasicoherentHoms`, the
   full-faithfulness half of Stacks 023T, and **the hypothesis is a theorem**:
   `AlgebraicGeometry.fpqcDescentOfQuasicoherentHoms` of
   `StacksFrontier/AlgebraicGeometry/Descent/FpqcHomSheafRefinement.lean`, unconditional, with the
   unconditional consequence already proved as
   `AlgebraicGeometry.quasiCoherentPresheaf_isSheaf_fppf'`.  The effectivity half of Stacks 023T
   is unconditional too,
   `AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage`.

   What that buys, read at the module of the formula, is three statements with no hypothesis.  The
   module read on the representing scheme is quasi-coherent
   (`AlgebraicGeometry.Stack.isQuasicoherent_prestackPointSchemeModule`, from Stacks 03GA and the
   Zariski restriction), so Stacks 03DT applies to it over the schemes over `T`
   (`AlgebraicGeometry.Stack.isSheaf_fppf_quasiCoherentPresheaf_prestackPointSchemeModule`) and on
   `(Sch/T)_fppf`; and the equivalence of sites of Stacks 06WI carries the second to the
   localization of `[U/_pR]` at the object `(T, w)`
   (`AlgebraicGeometry.Stack.isSheaf_localizedFppf_prestackPointSections`).  The last of those
   needs no narrowing of the universes — Stacks 06WI and its dense-subsite instance hold at
   morphisms in `Type w`, and those of `[U/_pR]` are in `Type (u + 1)`.

   The remaining input of the assembly is item 1's presheaf together with the identification of
   its restriction to each slice with the source's formula there, which is item 1's own content
   and not a further mathematical step.  What is *not* available is the stronger form in which the
   identification is replaced by quasi-coherence —
   `AlgebraicGeometry.FibredSite.isSheafFppfOfQuasicoherentOnSite_siteKind`, the first input
   of Stacks 0EM8 — and the obstruction there is a universe: that statement is
   proved at `Category.{u} 𝒳` and module universe `u`, because the transport of quasi-coherence
   across the equivalence of sites (`Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff`,
   through `Stacks.SheafOfModules.hasGlobalPresentation_map`) carries the index type of a global
   presentation across verbatim and so forces one pair of universes for the two sites, while
   `[U/_pR]` has morphisms in `Type (u + 1)`.
3. **Quasi-coherence**, which the source gets from Stacks 06WI.  Unlike items 1 and 2 this one is
   *available*: Stacks 06WI is
   `AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_iff_forall_objectInverseImage` in
   `StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/Descent/FibredSiteLocalization.lean`,
   proved unconditionally and carrying the tag.  The docstrings of
   `StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/QuotientStackQuasicoherentModules.lean` and of
   `…/QuotientStackQuasicoherentMissingInputs.lean` say that the backward functor "is not a
   citation either", because the source "proves its quasi-coherence through Stacks 06WI"; that is
   right about the construction and should not be read as saying that Stacks 06WI is missing,
   which it is not.

## The module universes, and why they are the ones below

`AlgebraicGeometry.Space.modulePullback` — the inverse image `u_small^*` of the displayed formula
— exists only between `AlgebraicGeometry.Space.Modules.{u, u}`, module universe `u`, and the
underlying module of a groupoid module is there for the same reason (the transition `α` is a
morphism between its values).  So `prestackPointModule` is at module universe `u`, and that is
forced rather than chosen.

The *sections* then land in `Type u` as well, and the ring they are a module over is
`Γ(T, 𝒪_T)`, the value of the structure sheaf of `[U/_pR]` at `(T, u)` — this is what
`AlgebraicGeometry.Space.representedZariskiRestriction` is for, and why
`prestackPointSchemeModule` goes through the representing *scheme*: the global sections of an
`𝒪`-module on the small étale site of the algebraic space `h_T` are a module over the global
section ring of that site, which is not `Γ(T, 𝒪_T)` on the nose, while the sections of its
restriction to the Zariski site of `T` are.

The residue below is stated at module universe `u + 1`, not `u`, because that is the module
universe of `AlgebraicGeometry.Stack.PointwiseQuotientGroupoidEquivalence`: Stacks 06WH, which
the reduction of the carrier rests on, preserves quasi-coherence only at `max u v w m`, and for
`[U/_pR]` that is `max (u + 1) m`.  The lift of the sections from `Type u` to `Type (u + 1)` is
therefore part of the packaging, and it is why the pinning field of the residue is stated against
`ULift` of `prestackPointSections`.

## No tag is registered here

Every declaration below is a *component* of Stacks 06WT — the backward functor is one of the two
functors of its proof — so none of them carries `@[stacks 06WT]`, which belongs on a declaration
proving the whole clause.  That attribute sits on
`AlgebraicGeometry.Stack.nonempty_quasicoherentEquivalenceGroupoid_of_missingInputs`, and nothing
here alters it.

## References

* [Stacks Project, Tag 02XV](https://stacks.math.columbia.edu/tag/02XV)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 025Z](https://stacks.math.columbia.edu/tag/025Z)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 0EM8](https://stacks.math.columbia.edu/tag/0EM8)
* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 043Z](https://stacks.math.columbia.edu/tag/043Z)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 04P9](https://stacks.math.columbia.edu/tag/04P9)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 06WH](https://stacks.math.columbia.edu/tag/06WH)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe u

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for discrete limits of presheaves on the big fppf site times out otherwise
/-- Discrete limits of presheaves on the big fppf site, given directly: instance search for
them times out under Lean v4.35.0. -/
local instance (priority := high)
    hasLimitsOfShape_discrete_presheaf_QuotientPrestackBackwardTransition
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S} (J : Type) :
    Limits.HasLimitsOfShape (Discrete J) ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u) :=
  inferInstance

/-- Pullbacks of presheaves on the big fppf site, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_QuotientPrestackBackwardTransition
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S} :
    Limits.HasPullbacks ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_QuotientPrestackBackwardTransition
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {X Y Z : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Limits.HasLimit (Limits.cospan f g) :=
  hasPullbacks_presheaf_QuotientPrestackBackwardTransition.has_limit _

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A section is a morphism out of a representable algebraic space.**  A `T`-point of an
algebraic space `X`, for `T` a test object of the big fppf site, read as a morphism of algebraic
spaces `h_T ⟶ X` out of the representable algebraic space of `T` (Stacks 025Z,
`AlgebraicGeometry.Space.yonedaSpace`).

This is the `u` of the formula `ℱ(T, u) = Γ(T, u_{small}^*𝒢)` of Stacks 06WT: an object of the
pointwise quotient `[U/_pR]` over `T` is a `T`-point of the object space, and the inverse image
the formula takes is along the morphism of algebraic spaces it is. -/
def yonedaSectionHom (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    (w : X.1.obj (op T)) : yonedaSpace B S hS T ⟶ X :=
  ObjectProperty.homMk (yonedaEquiv.symm w)

/-- The underlying morphism of presheaves of `AlgebraicGeometry.Space.yonedaSectionHom` is the
Yoneda transpose of the section. -/
@[simp] theorem yonedaSectionHom_hom (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    (w : X.1.obj (op T)) :
    (yonedaSectionHom B S hS X T w).hom = yonedaEquiv.symm w := rfl

/-- **Naturality in the test object.**  Restricting a section along an arrow `g : T' ⟶ T` of the
site precomposes its morphism of algebraic spaces with the morphism of representable algebraic
spaces of `g`. -/
theorem representedSpaceMap_comp_yonedaSectionHom (X : AlgebraicSpaces B S hS)
    {T' T : BigFppfOver B S hS} (g : T' ⟶ T) (w : X.1.obj (op T)) :
    representedSpaceMap B S hS g ≫ yonedaSectionHom B S hS X T w =
      yonedaSectionHom B S hS X T' (X.1.map g.op w) := by
  refine ObjectProperty.hom_ext _ ?_
  simpa only [yonedaSectionHom, ObjectProperty.FullSubcategory.comp_hom, schemeSpaceMap_hom,
    ObjectProperty.homMk_hom] using
    yonedaEquiv_symm_naturality_left g X.1 w

/-- **Naturality in the space.**  Pushing a section forward along a morphism `f : X ⟶ Y` of
algebraic spaces postcomposes its morphism of algebraic spaces with `f`.

This is what identifies the inverse images `(a ≫ t)^*𝒢` and `(a ≫ s)^*𝒢` along a `T`-point `a`
of the arrow space of a groupoid with the inverse images along the two endpoints of `a`, and so
is what makes `AlgebraicGeometry.Stack.prestackArrowTransition` typecheck. -/
theorem yonedaSectionHom_comp {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (T : BigFppfOver B S hS) (w : X.1.obj (op T)) :
    yonedaSectionHom B S hS X T w ≫ f = yonedaSectionHom B S hS Y T (f.hom.app (op T) w) := by
  refine ObjectProperty.hom_ext _ ?_
  simpa [yonedaSectionHom] using yonedaEquiv_symm_naturality_right T f.hom w

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {A : AlgebraicSpaces C S hS}

/-! ### The module of the formula -/

/-- **`u_small^*𝒢`, the inverse image inside the formula of Stacks 06WT.**  For an object
`(T, w)` of the pointwise quotient `[U/_pR]` — a test object `T` together with a `T`-point `w` of
the object space — the inverse image of the underlying module of a quasi-coherent module on the
groupoid along the morphism of algebraic spaces `w` is.

The module universe is `u` on both sides, and that is forced:
`AlgebraicGeometry.Space.modulePullback` exists only between
`AlgebraicGeometry.Space.Modules.{u, u}`. -/
def prestackPointModule (G : GroupoidInAlgebraicSpaces C S hS A)
    (M : Space.QuasicoherentModule C S hS G) (T : BigFppfOver C S hS)
    (w : G.objects.1.obj (op T)) :
    Space.Modules.{u, u} C S hS (yoneda.obj T) (isAlgebraicSpace_yoneda C S hS T) :=
  (Space.modulePullback C S hS (Space.yonedaSectionHom C S hS G.objects T w)).obj M.F.obj

/-- **The formula is functorial in the groupoid module.**  A morphism of quasi-coherent modules
on the groupoid induces, at each object of the pointwise quotient, a morphism of the inverse
images: the inverse image of its underlying morphism of modules. -/
def prestackPointMap (G : GroupoidInAlgebraicSpaces C S hS A)
    {M N : Space.QuasicoherentModule C S hS G} (φ : M ⟶ N) (T : BigFppfOver C S hS)
    (w : G.objects.1.obj (op T)) :
    prestackPointModule G M T w ⟶ prestackPointModule G N T w :=
  (Space.modulePullback C S hS (Space.yonedaSectionHom C S hS G.objects T w)).map φ.hom

/-- `u_small^*𝒢` read on the representing scheme: the restriction of an `𝒪`-module on the small
étale site of the representable algebraic space `h_T` to the Zariski site of the scheme under
`T`, `AlgebraicGeometry.Space.representedZariskiRestriction`.

This step is what puts the sections of the formula over the ring `Γ(T, 𝒪_T)` that the structure
sheaf of `[U/_pR]` takes at `(T, w)`; the global sections of the small étale site are a module
over its global section ring, which is not that ring on the nose. -/
def prestackPointSchemeModule (G : GroupoidInAlgebraicSpaces C S hS A)
    (M : Space.QuasicoherentModule C S hS G) (T : BigFppfOver C S hS)
    (w : G.objects.1.obj (op T)) :
    ((BigFppfOver.toScheme C S hS).obj T).Modules :=
  Space.representedZariskiRestriction C S hS T (isAlgebraicSpace_yoneda C S hS T)
    (prestackPointModule G M T w)

/-- **`Γ(T, u_small^*𝒢)`, the right-hand side of the formula of Stacks 06WT**, as a module over
`Γ(T, 𝒪_T)`.

This is the value the backward functor's module has to take at the object `(T, w)` of the
pointwise quotient.  Its module universe is `u`, inherited from
`AlgebraicGeometry.Stack.prestackPointModule`; the residue
`AlgebraicGeometry.Stack.PrestackBackwardFunctor` is stated at `u + 1` and pins the sections
against `ULift` of this, for the reason given in the module documentation. -/
def prestackPointSections (G : GroupoidInAlgebraicSpaces C S hS A)
    (M : Space.QuasicoherentModule C S hS G) (T : BigFppfOver C S hS)
    (w : G.objects.1.obj (op T)) :
    ModuleCat.{u} Γ((BigFppfOver.toScheme C S hS).obj T,
      (⊤ : ((BigFppfOver.toScheme C S hS).obj T).Opens)) :=
  ModuleCat.of _ Γ(prestackPointSchemeModule G M T w,
    (⊤ : ((BigFppfOver.toScheme C S hS).obj T).Opens))

/-! ### The formula as a functor, and the comparison of global sections -/

/-- **The formula of Stacks 06WT as a functor in the groupoid module**, at a fixed object
`(T, w)` of the pointwise quotient: forget the transition morphism and take the inverse image
along the morphism of algebraic spaces that `w` is.

Writing the family as a *functor* rather than as a map on objects together with
`AlgebraicGeometry.Stack.prestackPointMap` is what keeps the identity and composition laws of
the backward functor's action on morphisms out of reach of the elaboration hazard recorded at
`AlgebraicGeometry.Stack.prestackArrowTransition_eq`: stated by hand they are equations between
composites `≫` of morphisms of `AlgebraicGeometry.Space.Modules` at the representable algebraic
space of a test object, which exceeds the elaborator's recursion budget, while here they are the
functor laws of a composite of two functors and so are never written out. -/
def prestackPointModuleFunctor (G : GroupoidInAlgebraicSpaces C S hS A)
    (T : BigFppfOver C S hS) (w : G.objects.1.obj (op T)) :
    Space.QuasicoherentModule C S hS G ⥤
      Space.Modules.{u, u} C S hS (yoneda.obj T) (isAlgebraicSpace_yoneda C S hS T) :=
  Space.QuasicoherentModule.forget G ⋙
    Space.modulePullback C S hS (Space.yonedaSectionHom C S hS G.objects T w)

/-- The functor of the formula takes the value `AlgebraicGeometry.Stack.prestackPointModule`. -/
@[simp] theorem prestackPointModuleFunctor_obj (G : GroupoidInAlgebraicSpaces C S hS A)
    (M : Space.QuasicoherentModule C S hS G) (T : BigFppfOver C S hS)
    (w : G.objects.1.obj (op T)) :
    (prestackPointModuleFunctor G T w).obj M = prestackPointModule G M T w :=
  rfl

/-- The functor of the formula acts on morphisms by
`AlgebraicGeometry.Stack.prestackPointMap`. -/
@[simp] theorem prestackPointModuleFunctor_map (G : GroupoidInAlgebraicSpaces C S hS A)
    {M N : Space.QuasicoherentModule C S hS G} (φ : M ⟶ N) (T : BigFppfOver C S hS)
    (w : G.objects.1.obj (op T)) :
    (prestackPointModuleFunctor G T w).map φ = prestackPointMap G φ T w :=
  rfl

/-- **The comparison of global sections of the backward functor of Stacks 06WT.**  An
`𝒪`-module on the small étale site of the representable algebraic space `h_T` has, after
restriction to the Zariski site of the representing scheme
(`AlgebraicGeometry.Space.representedZariskiRestrictionFunctor`), a module of global sections
over the ring `Γ(T, 𝒪_T)`, and a morphism of such modules has a `Γ(T, 𝒪_T)`-linear map of
global sections.

This is the comparison the right-hand side of the formula `ℱ(T, u) = Γ(T, u_{small}^*𝒢)` needs
in order to be a module over the value `Γ(T, 𝒪_T)` of the structure sheaf of `[U/_pR]` at
`(T, w)`: the global sections of an `𝒪`-module on the small étale site of `h_T` are a module
over the global section ring of *that* site, which is not `Γ(T, 𝒪_T)` on the nose, while the
sections of the Zariski restriction are. -/
def prestackPointSectionsFunctor (T : BigFppfOver C S hS) :
    Space.Modules.{u, u} C S hS (yoneda.obj T) (isAlgebraicSpace_yoneda C S hS T) ⥤
      ModuleCat.{u} Γ((BigFppfOver.toScheme C S hS).obj T,
        (⊤ : ((BigFppfOver.toScheme C S hS).obj T).Opens)) :=
  Space.representedZariskiRestrictionFunctor C S hS T (isAlgebraicSpace_yoneda C S hS T) ⋙
    moduleGlobalSections ((BigFppfOver.toScheme C S hS).obj T)

/-- **The right-hand side of the formula of Stacks 06WT is the global-sections comparison at
the inverse image.**  The value `Γ(T, u_{small}^*𝒢)` is the global-sections comparison
`AlgebraicGeometry.Stack.prestackPointSectionsFunctor` applied to
`AlgebraicGeometry.Stack.prestackPointModule`, on the nose. -/
theorem prestackPointSections_eq (G : GroupoidInAlgebraicSpaces C S hS A)
    (M : Space.QuasicoherentModule C S hS G) (T : BigFppfOver C S hS)
    (w : G.objects.1.obj (op T)) :
    prestackPointSections G M T w =
      (prestackPointSectionsFunctor T).obj (prestackPointModule G M T w) :=
  rfl

/-- **The value of the backward functor at an object of the pointwise quotient, as a functor in
the groupoid module.**  The composite of the formula
(`AlgebraicGeometry.Stack.prestackPointModuleFunctor`) with the global-sections comparison
(`AlgebraicGeometry.Stack.prestackPointSectionsFunctor`): the assignment
`(𝒢, α) ↦ Γ(T, w_{small}^*𝒢)` together with its action on morphisms of quasi-coherent modules
on the groupoid, which is `Γ(T, 𝒪_T)`-linear.

This is the functoriality in `(𝒢, α)` of the values of the backward functor of Stacks 06WT.
What is *not* here is the functoriality in `(T, w)`, which is the restriction map and is item 1
of "What remains, precisely" in the module documentation. -/
def prestackPointSectionsFunctorAt (G : GroupoidInAlgebraicSpaces C S hS A)
    (T : BigFppfOver C S hS) (w : G.objects.1.obj (op T)) :
    Space.QuasicoherentModule C S hS G ⥤
      ModuleCat.{u} Γ((BigFppfOver.toScheme C S hS).obj T,
        (⊤ : ((BigFppfOver.toScheme C S hS).obj T).Opens)) :=
  prestackPointModuleFunctor G T w ⋙ prestackPointSectionsFunctor T

/-- The functor of the values of the backward functor at `(T, w)` takes the value
`AlgebraicGeometry.Stack.prestackPointSections`, which is the source's formula. -/
@[simp] theorem prestackPointSectionsFunctorAt_obj (G : GroupoidInAlgebraicSpaces C S hS A)
    (M : Space.QuasicoherentModule C S hS G) (T : BigFppfOver C S hS)
    (w : G.objects.1.obj (op T)) :
    (prestackPointSectionsFunctorAt G T w).obj M = prestackPointSections G M T w :=
  rfl

/-- **The module of the formula is quasi-coherent.**  The inverse image of a quasi-coherent
`𝒪`-module along an arbitrary morphism of algebraic spaces is quasi-coherent (Stacks 03GA), and
the underlying module of a quasi-coherent module on the groupoid is quasi-coherent by
definition.

This is the hypothesis every base-change comparison of the Zariski restriction asks for — see
`AlgebraicGeometry.Space.representedZariskiRestrictionBaseChangeIso` — so it is what lets the
restriction map of the backward functor be read on the representing schemes at all. -/
theorem isQuasicoherentOnSite_prestackPointModule
    (G : GroupoidInAlgebraicSpaces C S hS A) (M : Space.QuasicoherentModule C S hS G)
    (T : BigFppfOver C S hS) (w : G.objects.1.obj (op T)) :
    (prestackPointModule G M T w).IsQuasicoherentOnSite :=
  Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite C S hS
    (Space.yonedaSectionHom C S hS G.objects T w) M.F.obj M.F.property

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

universe u

attribute [local instance high]
  AlgebraicGeometry.Space.hasLimitsOfShape_discrete_presheaf_QuotientPrestackBackwardTransition
  AlgebraicGeometry.Space.hasPullbacks_presheaf_QuotientPrestackBackwardTransition
  AlgebraicGeometry.Space.hasPullback_presheaf_QuotientPrestackBackwardTransition

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : AlgebraicSpaces B S hS}

/-! ### The composite of a composable pair of arrows -/

/-- **The composite of a composable pair of arrows into the arrow space.**  For an algebraic
space `P` and two morphisms `a₁`, `a₂ : P ⟶ R` whose endpoints match — the source of `a₁` is the
target of `a₂` — the pair is a `P`-point of the space of composable pairs of arrows, and this is
the arrow the composition morphism of the groupoid sends it to.

This is `AlgebraicGeometry.GroupoidInAlgebraicSpaces.groupoidCompose` read on the chosen fibre
product rather than on the presheaf of composable pairs; the two agree by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.arrowComp_hom`, which is what identifies the
composite below with the composite of the two arrows in the groupoid of `P`-points. -/
def arrowComp (G : GroupoidInAlgebraicSpaces B S hS A) {P : AlgebraicSpaces B S hS}
    (a₁ a₂ : P ⟶ G.arrows) (h : a₁ ≫ G.source = a₂ ≫ G.target) : P ⟶ G.arrows :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS G.source G.target).lift a₁ a₂ h ≫ G.comp

/-- The composite of a composable pair of arrows has the target of the first, by the commuting
square of the cartesian square of Stacks 04P9. -/
@[simp] theorem arrowComp_comp_target (G : GroupoidInAlgebraicSpaces B S hS A)
    {P : AlgebraicSpaces B S hS} (a₁ a₂ : P ⟶ G.arrows)
    (h : a₁ ≫ G.source = a₂ ≫ G.target) :
    arrowComp G a₁ a₂ h ≫ G.target = a₁ ≫ G.target := by
  rw [arrowComp, Category.assoc, comp_comp_target, ← Category.assoc,
    (AlgebraicSpaces.isPullback_fiberProduct B S hS G.source G.target).lift_fst]

/-- The composite of a composable pair of arrows has the source of the second, by the commuting
square of the cartesian square of Stacks 043Z. -/
@[simp] theorem arrowComp_comp_source (G : GroupoidInAlgebraicSpaces B S hS A)
    {P : AlgebraicSpaces B S hS} (a₁ a₂ : P ⟶ G.arrows)
    (h : a₁ ≫ G.source = a₂ ≫ G.target) :
    arrowComp G a₁ a₂ h ≫ G.source = a₂ ≫ G.source := by
  rw [arrowComp, Category.assoc, comp_comp_source, ← Category.assoc,
    (AlgebraicSpaces.isPullback_fiberProduct B S hS G.source G.target).lift_snd]

/-- **The composite of a composable pair of arrows is their composite in the groupoid of
`P`-points.**  On underlying presheaves it is
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.groupoidCompose`, whose value at a point of a test
object is the composite in the evaluated groupoid
(`AlgebraicGeometry.GroupoidInAlgebraicSpaces.groupoidCompose_eval`).  So the cocycle law read at
the composite below is the cocycle law read at a composable pair of points of the arrow space. -/
theorem arrowComp_hom (G : GroupoidInAlgebraicSpaces B S hS A) {P : AlgebraicSpaces B S hS}
    (a₁ a₂ : P ⟶ G.arrows) (h : a₁ ≫ G.source = a₂ ≫ G.target) :
    (arrowComp G a₁ a₂ h).hom =
      groupoidCompose G a₁.hom a₂.hom
        (congrArg (fun m : P ⟶ G.objects => m.hom) h) := by
  have key : ((AlgebraicSpaces.isPullback_fiberProduct B S hS G.source G.target).lift
        a₁ a₂ h).hom =
      CategoryTheory.Limits.pullback.lift a₁.hom a₂.hom
        (congrArg (fun m : P ⟶ G.objects => m.hom) h) := by
    apply CategoryTheory.Limits.pullback.hom_ext
    · rw [CategoryTheory.Limits.pullback.lift_fst]
      exact congrArg (fun m : P ⟶ G.arrows => m.hom)
        ((AlgebraicSpaces.isPullback_fiberProduct B S hS G.source G.target).lift_fst a₁ a₂ h)
    · rw [CategoryTheory.Limits.pullback.lift_snd]
      exact congrArg (fun m : P ⟶ G.arrows => m.hom)
        ((AlgebraicSpaces.isPullback_fiberProduct B S hS G.source G.target).lift_snd a₁ a₂ h)
  exact congrArg (fun m => m ≫ G.comp.hom) key

/-- **The composite of a composable pair of `T`-points of the arrow space is their composite in
the groupoid of `T`-points.**  Read at the representable algebraic space of a test object, the
composite of a composable pair of arrows is
`Deformation.GroupoidInFunctors.compose` — the composition of the groupoid of `T`-points of
Stacks 043W — applied to the two points.

This is what makes the cocycle law supplied by
`AlgebraicGeometry.Space.transitionCocycle_arrowComp` the cocycle condition of Stacks 0441 *read
at a pair of `T`-points of the arrow space*, which is the form the backward functor of
Stacks 06WT needs: a morphism of `[U/_pR]` over the identity of `T` is a `T`-point of the arrow
space, and the arrow component of a composite of two such is the composite of the two points. -/
theorem arrowComp_yonedaSectionHom (G : GroupoidInAlgebraicSpaces B S hS A)
    (T : BigFppfOver B S hS) (a₁ a₂ : G.arrows.1.obj (op T))
    (h : G.source.hom.app (op T) a₁ = G.target.hom.app (op T) a₂)
    (h' : Space.yonedaSectionHom B S hS G.arrows T a₁ ≫ G.source =
      Space.yonedaSectionHom B S hS G.arrows T a₂ ≫ G.target) :
    arrowComp G (Space.yonedaSectionHom B S hS G.arrows T a₁)
        (Space.yonedaSectionHom B S hS G.arrows T a₂) h' =
      Space.yonedaSectionHom B S hS G.arrows T
        (G.toGroupoidInFunctors.compose (op T) a₁ a₂ h) := by
  refine ObjectProperty.hom_ext _ (yonedaEquiv.injective ?_)
  have hpt (a : G.arrows.1.obj (op T)) :
      (Space.yonedaSectionHom B S hS G.arrows T a).hom.app (op T) (𝟙 T) = a := by simp
  have key := groupoidCompose_eval G
    (Space.yonedaSectionHom B S hS G.arrows T a₁).hom
    (Space.yonedaSectionHom B S hS G.arrows T a₂).hom
    (congrArg (fun m : Space.yonedaSpace B S hS T ⟶ G.objects => m.hom) h') (op T) (𝟙 T)
  refine (congrArg yonedaEquiv (arrowComp_hom G _ _ h')).trans ?_
  refine (((yonedaEquiv_apply _).trans key).trans ?_).trans
    (Equiv.apply_symm_apply yonedaEquiv
      (G.toGroupoidInFunctors.compose (op T) a₁ a₂ h)).symm
  exact Deformation.GroupoidInFunctors.compose_congr _ _ _ _ (hpt a₁) (hpt a₂)

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

namespace AlgebraicGeometry.Space

universe u

/-! ### The transition morphisms, at a general test space -/

/-- **The transition morphism of a groupoid module reindexed along an arrow into the arrow space,
with its two endpoints named.**  For an algebraic space `P` and a morphism `a : P ⟶ R` into the
arrow space, `AlgebraicGeometry.Space.groupoidPullbackTransition` is a morphism
`(a ≫ t)^*ℱ ⟶ (a ≫ s)^*ℱ`; this is that morphism transported to any two morphisms `x`, `y` of
`P` into the object space which `a` has as its target and its source.

It is stated at a general `P` on purpose.  The use below is at `P = h_T` the representable
algebraic space of a test object, and at that `P` neither this definition's naturality in the
module nor the laws of the composite can be elaborated: the proof terms carry
`AlgebraicGeometry.isAlgebraicSpace_yoneda` inside every small étale ringed site they mention,
and the elaborator exhausts its recursion budget comparing them.  At a general `P` nothing
unfolds and the proofs are the generic row-composite pastings.

The composite is written at `CategoryTheory.comp₃`, for the reason recorded at
`AlgebraicGeometry.Space.transitionPair`: unfolded to a chain of `≫` the two
`AlgebraicGeometry.Space.pullbackTransport` factors drive the kernel into their `Eq.rec`. -/
def groupoidPullbackTransitionAt (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
    (F : Space.Modules.{u, u} B S hS G.objects.1 G.objects.2)
    (α : (Space.modulePullback B S hS G.target).obj F ⟶
      (Space.modulePullback B S hS G.source).obj F)
    {P : AlgebraicSpaces B S hS} (a : P ⟶ G.arrows) {x y : P ⟶ G.objects}
    (hx : a ≫ G.target = x) (hy : a ≫ G.source = y) :
    (Space.modulePullback B S hS x).obj F ⟶ (Space.modulePullback B S hS y).obj F :=
  comp₃ (Space.pullbackTransport F hx.symm)
    (Space.groupoidPullbackTransition B S hS G F α a)
    (Space.pullbackTransport F hy)

/-- `AlgebraicGeometry.Space.groupoidPullbackTransitionAt` read as an equation, so that a
consumer which has to see through it does so propositionally and factor by factor. -/
theorem groupoidPullbackTransitionAt_eq₃ (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
    (F : Space.Modules.{u, u} B S hS G.objects.1 G.objects.2)
    (α : (Space.modulePullback B S hS G.target).obj F ⟶
      (Space.modulePullback B S hS G.source).obj F)
    {P : AlgebraicSpaces B S hS} (a : P ⟶ G.arrows) {x y : P ⟶ G.objects}
    (hx : a ≫ G.target = x) (hy : a ≫ G.source = y) :
    groupoidPullbackTransitionAt B S hS G F α a hx hy =
      comp₃ (Space.pullbackTransport F hx.symm)
        (Space.groupoidPullbackTransition B S hS G F α a)
        (Space.pullbackTransport F hy) :=
  rfl

/-- **The retargeted reindexing is natural in the groupoid module.**  This is where the
compatibility of a morphism of groupoid modules with the two transition morphisms is consumed. -/
theorem groupoidPullbackTransitionAt_naturality (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
    {M N : Space.Modules.{u, u} B S hS G.objects.1 G.objects.2}
    {α : (Space.modulePullback B S hS G.target).obj M ⟶
      (Space.modulePullback B S hS G.source).obj M}
    {β : (Space.modulePullback B S hS G.target).obj N ⟶
      (Space.modulePullback B S hS G.source).obj N}
    (φ : M ⟶ N)
    (hφ : α ≫ (Space.modulePullback B S hS G.source).map φ =
      (Space.modulePullback B S hS G.target).map φ ≫ β)
    {P : AlgebraicSpaces B S hS} (a : P ⟶ G.arrows) {x y : P ⟶ G.objects}
    (hx : a ≫ G.target = x) (hy : a ≫ G.source = y) :
    (Space.modulePullback B S hS x).map φ ≫
          groupoidPullbackTransitionAt B S hS G N β a hx hy =
      groupoidPullbackTransitionAt B S hS G M α a hx hy ≫
        (Space.modulePullback B S hS y).map φ := by
  rw [groupoidPullbackTransitionAt_eq₃, groupoidPullbackTransitionAt_eq₃]
  exact comp₃_naturality (Space.pullbackTransport_naturality φ hx.symm)
    (Space.groupoidPullbackTransition_naturality B S hS G φ hφ a)
    (Space.pullbackTransport_naturality φ hy)

/-- **A row of three transports of inverse images along equal morphisms, returning to where it
started, is the identity.**  Every factor is an `eqToHom`, so the row is the `eqToHom` of the
composite equality, which is a reflexivity. -/
theorem pullbackTransport_comp₃_id (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T X : AlgebraicSpaces B S hS} (F : Modules.{u, u} B S hS X.1 X.2) {f g h : T ⟶ X}
    (p : f = g) (q : g = h) (r : h = f) :
    comp₃ (pullbackTransport F p) (pullbackTransport F q) (pullbackTransport F r) =
      𝟙 ((modulePullback B S hS f).obj F) := by
  subst p
  subst q
  simp [pullbackTransport, comp₃]

/-- **The unit law of the retargeted reindexing**: along the unit arrow of the groupoid at a
morphism `x` into the object space, the transition is the identity.

This is the `unit` field of `AlgebraicGeometry.Space.QuasicoherentModule` — the unit condition of
Stacks 0441 — read at `x ≫ e` through `AlgebraicGeometry.Space.TransitionUnit.comp`, which is
what makes the condition at the unit arrow itself suffice.  It is one of the two coherence laws
the backward functor of Stacks 06WT needs: the identity morphism of `[U/_pR]` at an object
`(T, w)` is the one whose arrow component is the unit arrow at `w`, so this says that the
backward functor's restriction map along an identity is an identity. -/
theorem groupoidPullbackTransitionAt_identityArrow (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
    (M : QuasicoherentModule B S hS G) {P : AlgebraicSpaces B S hS} (x : P ⟶ G.objects)
    (hx : (x ≫ GroupoidInAlgebraicSpaces.identityArrow G) ≫ G.target = x)
    (hy : (x ≫ GroupoidInAlgebraicSpaces.identityArrow G) ≫ G.source = x) :
    groupoidPullbackTransitionAt B S hS G M.F.obj M.alpha
        (x ≫ GroupoidInAlgebraicSpaces.identityArrow G) hx hy =
      𝟙 ((modulePullback B S hS x).obj M.F.obj) := by
  have hu : TransitionUnit B S hS M.F.obj M.alpha
      (x ≫ GroupoidInAlgebraicSpaces.identityArrow G) :=
    TransitionUnit.comp B S hS M.F.obj M.alpha
      ((GroupoidInAlgebraicSpaces.identityArrow_comp_target G).trans
        (GroupoidInAlgebraicSpaces.identityArrow_comp_source G).symm)
      (fun _ => M.unit) x rfl
  rw [groupoidPullbackTransitionAt_eq₃, groupoidPullbackTransition_eq_transitionReindex,
    hu (hx.trans hy.symm), pullbackTransport_comp₃_id]

/-- **The transition morphism of a groupoid module along an arrow of the arrow space, after a
base change.**  For `g : Q ⟶ P` a morphism of algebraic spaces, `x : P ⟶ U` and `a : Q ⟶ R` an
arrow whose target is `g ≫ x`, the inverse image along `g` of `x^*ℱ` is carried to `y^*ℱ` for `y`
the source of `a`: the composition comparison of Stacks 03LU, the transport along the target
condition, and the retargeted reindexing above.

This is the shape of the restriction map of the backward functor of Stacks 06WT: `Q = h_{T'}`,
`P = h_T`, `g` the represented arrow of `f : T' ⟶ T`, and `a` the `T'`-point of the arrow space
that the morphism of `[U/_pR]` carries. -/
def groupoidPullbackTransitionBaseChange (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
    (F : Space.Modules.{u, u} B S hS G.objects.1 G.objects.2)
    (α : (Space.modulePullback B S hS G.target).obj F ⟶
      (Space.modulePullback B S hS G.source).obj F)
    {Q P : AlgebraicSpaces B S hS} (g : Q ⟶ P) (x : P ⟶ G.objects) (a : Q ⟶ G.arrows)
    {y : Q ⟶ G.objects} (hx : a ≫ G.target = g ≫ x) (hy : a ≫ G.source = y) :
    (Space.modulePullback B S hS g).obj ((Space.modulePullback B S hS x).obj F) ⟶
      (Space.modulePullback B S hS y).obj F :=
  comp₃ ((Space.modulePullbackCompIso B S hS g x).hom.app F)
    (Space.pullbackTransport F hx.symm)
    (groupoidPullbackTransitionAt B S hS G F α a rfl hy)

/-- `AlgebraicGeometry.Space.groupoidPullbackTransitionBaseChange` read as an equation. -/
theorem groupoidPullbackTransitionBaseChange_eq₃ (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
    (F : Space.Modules.{u, u} B S hS G.objects.1 G.objects.2)
    (α : (Space.modulePullback B S hS G.target).obj F ⟶
      (Space.modulePullback B S hS G.source).obj F)
    {Q P : AlgebraicSpaces B S hS} (g : Q ⟶ P) (x : P ⟶ G.objects) (a : Q ⟶ G.arrows)
    {y : Q ⟶ G.objects} (hx : a ≫ G.target = g ≫ x) (hy : a ≫ G.source = y) :
    groupoidPullbackTransitionBaseChange B S hS G F α g x a hx hy =
      comp₃ ((Space.modulePullbackCompIso B S hS g x).hom.app F)
        (Space.pullbackTransport F hx.symm)
        (groupoidPullbackTransitionAt B S hS G F α a rfl hy) :=
  rfl

/-- **The base-changed transition is natural in the groupoid module.**  The three squares pasted
are the naturality of the composition comparison of Stacks 03LU, the naturality of the transport
along an equality of morphisms, and
`AlgebraicGeometry.Space.groupoidPullbackTransitionAt_naturality`. -/
theorem groupoidPullbackTransitionBaseChange_naturality (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
    {M N : Space.Modules.{u, u} B S hS G.objects.1 G.objects.2}
    {α : (Space.modulePullback B S hS G.target).obj M ⟶
      (Space.modulePullback B S hS G.source).obj M}
    {β : (Space.modulePullback B S hS G.target).obj N ⟶
      (Space.modulePullback B S hS G.source).obj N}
    (φ : M ⟶ N)
    (hφ : α ≫ (Space.modulePullback B S hS G.source).map φ =
      (Space.modulePullback B S hS G.target).map φ ≫ β)
    {Q P : AlgebraicSpaces B S hS} (g : Q ⟶ P) (x : P ⟶ G.objects) (a : Q ⟶ G.arrows)
    {y : Q ⟶ G.objects} (hx : a ≫ G.target = g ≫ x) (hy : a ≫ G.source = y) :
    (Space.modulePullback B S hS g).map ((Space.modulePullback B S hS x).map φ) ≫
          groupoidPullbackTransitionBaseChange B S hS G N β g x a hx hy =
      groupoidPullbackTransitionBaseChange B S hS G M α g x a hx hy ≫
        (Space.modulePullback B S hS y).map φ := by
  rw [groupoidPullbackTransitionBaseChange_eq₃, groupoidPullbackTransitionBaseChange_eq₃]
  exact comp₃_naturality ((Space.modulePullbackCompIso B S hS g x).hom.naturality φ)
    (Space.pullbackTransport_naturality φ hx.symm)
    (groupoidPullbackTransitionAt_naturality B S hS G φ hφ a rfl hy)

/-! ### The composition law of the two transitions -/

section Cocycle

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
  (F : Space.Modules.{u, u} B S hS G.objects.1 G.objects.2)
  (α : (Space.modulePullback B S hS G.target).obj F ⟶
    (Space.modulePullback B S hS G.source).obj F)

/-- `AlgebraicGeometry.Space.groupoidPullbackTransitionAt` as a chain of `≫`, with its middle
factor read as `AlgebraicGeometry.Space.modulePullbackReindex`, the reindexing of the
inverse-image calculus.

This is the shape in which the reindexing calculus of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EquivariantQuasicoherentPullback.lean` consumes a
row composite, and it is obtained by instantiating the generic `CategoryTheory.comp₃_eq` rather
than by unfolding `CategoryTheory.comp₃` at these types: the direct `rfl` is a kernel timeout,
for the reason recorded at `AlgebraicGeometry.Space.transitionPair`. -/
theorem groupoidPullbackTransitionAt_eq_comp {P : AlgebraicSpaces B S hS} (a : P ⟶ G.arrows)
    {x y : P ⟶ G.objects} (hx : a ≫ G.target = x) (hy : a ≫ G.source = y) :
    groupoidPullbackTransitionAt B S hS G F α a hx hy =
      pullbackTransport F hx.symm ≫
        modulePullbackReindex (M := F) (a := G.target) (b := G.source) a α ≫
        pullbackTransport F hy :=
  (groupoidPullbackTransitionAt_eq₃ B S hS G F α a hx hy).trans
    ((comp₃_eq _ _ _).trans
      (comp₃_congr rfl (groupoidPullbackTransition_eq_transitionReindex B S hS G F α a) rfl))

/-- **The cocycle law, read between two canonical transports.**  If the transition morphism
satisfies the cocycle law at a triple `a₁`, `a₂`, `c` of morphisms into the arrow space, then the
reindexing along `c`, read between the transports identifying its two endpoints with a pair of
morphisms `X`, `Z` into the object space, is the two reindexings along `a₁` and `a₂` in a row.

The two outer morphisms are kept abstract so that the statement can be instantiated at a
composite — at `X = (g₂ ≫ g₁) ≫ x` for the base-changed transition below — without any
associativity reconciliation appearing inside a transport, which is where it is expensive. -/
theorem modulePullbackReindex_transport_cocycle {P : AlgebraicSpaces B S hS}
    {a₁ a₂ c : P ⟶ G.arrows} {X Z : P ⟶ G.objects} (hcX : X = c ≫ G.target)
    (hcZ : c ≫ G.source = Z) (hX : X = a₁ ≫ G.target)
    (hm : a₁ ≫ G.source = a₂ ≫ G.target) (hZ : a₂ ≫ G.source = Z)
    (hcoc : TransitionCocycle B S hS (U := G.objects) (V := G.arrows)
      (a := G.target) (b := G.source) F α a₁ a₂ c) :
    pullbackTransport F hcX ≫
        modulePullbackReindex (M := F) (a := G.target) (b := G.source) c α ≫
        pullbackTransport F hcZ =
      pullbackTransport F hX ≫
        modulePullbackReindex (M := F) (a := G.target) (b := G.source) a₁ α ≫
        pullbackTransport F hm ≫
        modulePullbackReindex (M := F) (a := G.target) (b := G.source) a₂ α ≫
        pullbackTransport F hZ := by
  have hcoc' := hcoc (hcX.symm.trans hX) hm (hcZ.trans hZ.symm)
  rw [transitionReindex_eq_modulePullbackReindex] at hcoc'
  rw [hcoc', transitionComposite_eq_comp,
    Stacks.AlgebraicGeometry.EquivariantQuasicoherentPullback.comp_transport_merge₂
      _ _ _ _ _ _ _ _ _ (pullbackTransport_comp F hcX (hcX.symm.trans hX) hX)
      (pullbackTransport_comp F (hcZ.trans hZ.symm).symm hcZ hZ)]

/-- **The composition law of the retargeted reindexing**: along a morphism `c` into the arrow
space which the cocycle law presents as the composite of `a₁` and `a₂`, the transition is the
composite of the transitions along `a₁` and along `a₂`.

This is the composition half of the coherence of the transition morphism of the backward functor
of Stacks 06WT, at a general test space.  The unit half is
`AlgebraicGeometry.Space.groupoidPullbackTransitionAt_identityArrow`, and the two are exactly
parallel: that one consumes the `unit` field of
`AlgebraicGeometry.Space.QuasicoherentModule` through
`AlgebraicGeometry.Space.TransitionUnit.comp`, this one consumes the `cocycle` field through
`AlgebraicGeometry.Space.TransitionCocycle.comp` — see
`AlgebraicGeometry.Space.transitionCocycle_arrowComp`, which discharges `hcoc` from that
field. -/
theorem groupoidPullbackTransitionAt_comp {P : AlgebraicSpaces B S hS}
    {a₁ a₂ c : P ⟶ G.arrows} {x y z : P ⟶ G.objects}
    (hx : a₁ ≫ G.target = x) (hy : a₁ ≫ G.source = y)
    (hy' : a₂ ≫ G.target = y) (hz : a₂ ≫ G.source = z)
    (hcx : c ≫ G.target = x) (hcz : c ≫ G.source = z)
    (hcoc : TransitionCocycle B S hS (U := G.objects) (V := G.arrows)
      (a := G.target) (b := G.source) F α a₁ a₂ c) :
    groupoidPullbackTransitionAt B S hS G F α c hcx hcz =
      groupoidPullbackTransitionAt B S hS G F α a₁ hx hy ≫
        groupoidPullbackTransitionAt B S hS G F α a₂ hy' hz := by
  rw [groupoidPullbackTransitionAt_eq_comp, groupoidPullbackTransitionAt_eq_comp,
    groupoidPullbackTransitionAt_eq_comp,
    modulePullbackReindex_transport_cocycle B S hS G F α hcx.symm hcz hx.symm
      (hy.trans hy'.symm) hz hcoc,
    ← pullbackTransport_comp F hy hy'.symm (hy.trans hy'.symm)]
  simp only [Category.assoc]

/-- **The retargeted reindexing commutes with base change.**  Reindexing the transition along an
arrow `a` further along a morphism `k` of algebraic spaces is the transition along `k ≫ a`.

This is `AlgebraicGeometry.Space.modulePullbackReindex_transport_sandwich`, which is the
associativity coherence of the composition comparison of Stacks 03LU, read on the retargeted
reindexing. -/
theorem groupoidPullbackTransitionAt_reindex {P P' : AlgebraicSpaces B S hS} (k : P' ⟶ P)
    (a : P ⟶ G.arrows) {x y : P ⟶ G.objects} (hx : a ≫ G.target = x)
    (hy : a ≫ G.source = y) (hx' : (k ≫ a) ≫ G.target = k ≫ x)
    (hy' : (k ≫ a) ≫ G.source = k ≫ y) :
    modulePullbackReindex (M := F) (a := x) (b := y) k
        (groupoidPullbackTransitionAt B S hS G F α a hx hy) =
      groupoidPullbackTransitionAt B S hS G F α (k ≫ a) hx' hy' := by
  rw [groupoidPullbackTransitionAt_eq_comp, groupoidPullbackTransitionAt_eq_comp,
    modulePullbackReindex_transport_sandwich (modulePullbackCompIsoAssoc B S hS) a
      hx.symm hy F α k (k ≫ a) rfl hx'.symm hy']

end Cocycle

/-- **Compatibility of the Stacks 03LU comparison with a composite base change.**  Let
`g₁ : P' ⟶ P` and `g₂ : Q ⟶ P'`, let `x : P ⟶ U`, and let `φ : (g₁ ≫ x)^*ℱ ⟶ y^*ℱ`.  Inverting
the comparison for `g₂ ≫ g₁`, taking the inverse image along `g₂` of the comparison for `g₁`
followed by `φ`, and then the comparison for `g₂`, is the comparison for `(g₂ ≫ g₁)` followed by
the reindexing of `φ` along `g₂`.

This is the half of the composition law of the backward functor's restriction map that does not
come from the cocycle condition: the restriction map of Stacks 06WT is the comparison of Stacks
03LU followed by the action of an arrow, so its composition law needs the comparison to be
compatible with a composite of base changes.  The content is the associativity coherence
`AlgebraicGeometry.Space.modulePullbackCompIsoAssoc`.

A trailing morphism `σ` is carried along so that the statement can be rewritten into a row whose
last factor is itself a composite, which is the shape the base-changed transition has. -/
theorem modulePullbackCompIso_inv_comp_map_comp (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {Q P' P U : AlgebraicSpaces B S hS} (g₂ : Q ⟶ P') (g₁ : P' ⟶ P)
    (x : P ⟶ U) (F : Modules.{u, u} B S hS U.1 U.2) {y : P' ⟶ U}
    (φ : (modulePullback B S hS (g₁ ≫ x)).obj F ⟶ (modulePullback B S hS y).obj F)
    {N : Modules.{u, u} B S hS Q.1 Q.2}
    (σ : (modulePullback B S hS (g₂ ≫ y)).obj F ⟶ N) :
    (modulePullbackCompIso B S hS g₂ g₁).inv.app ((modulePullback B S hS x).obj F) ≫
        (modulePullback B S hS g₂).map
          ((modulePullbackCompIso B S hS g₁ x).hom.app F ≫ φ) ≫
        ((modulePullbackCompIso B S hS g₂ y).hom.app F ≫ σ) =
      (modulePullbackCompIso B S hS (g₂ ≫ g₁) x).hom.app F ≫
        modulePullbackReindex (M := F) (a := g₁ ≫ x) (b := y) g₂ φ ≫ σ := by
  have h := (modulePullbackCompIsoAssoc B S hS).hom_app g₂ g₁ x F
  simp only [modulePullbackReindex, Functor.map_comp]
  simp only [Category.assoc]
  rw [← Iso.app_inv (modulePullbackCompIso B S hS g₂ g₁) ((modulePullback B S hS x).obj F),
    Iso.inv_comp_eq, Iso.app_hom, ← reassoc_of% h, Iso.hom_inv_id_app_assoc]

section CocycleBaseChange

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
  (F : Space.Modules.{u, u} B S hS G.objects.1 G.objects.2)
  (α : (Space.modulePullback B S hS G.target).obj F ⟶
    (Space.modulePullback B S hS G.source).obj F)

/-- `AlgebraicGeometry.Space.groupoidPullbackTransitionBaseChange` is the comparison of
Stacks 03LU followed by the retargeted reindexing, as an equation.  The transport along the target
condition is absorbed into the reindexing. -/
theorem groupoidPullbackTransitionBaseChange_eq_comp {Q P : AlgebraicSpaces B S hS} (g : Q ⟶ P)
    (x : P ⟶ G.objects) (a : Q ⟶ G.arrows) {y : Q ⟶ G.objects}
    (hx : a ≫ G.target = g ≫ x) (hy : a ≫ G.source = y) :
    groupoidPullbackTransitionBaseChange B S hS G F α g x a hx hy =
      (modulePullbackCompIso B S hS g x).hom.app F ≫
        groupoidPullbackTransitionAt B S hS G F α a hx hy := by
  rw [groupoidPullbackTransitionBaseChange_eq₃, comp₃_eq,
    groupoidPullbackTransitionAt_eq_comp, groupoidPullbackTransitionAt_eq_comp,
    ← Category.assoc (pullbackTransport F hx.symm),
    pullbackTransport_comp F hx.symm (Eq.refl (a ≫ G.target)).symm hx.symm]

/-- **The composition law of the backward functor's restriction map, at a general test space.**
Let `g₁ : Q ⟶ P` and `g₂ : Q' ⟶ Q` be morphisms of algebraic spaces, `x : P ⟶ U`, and let `a₁`
and `a₂` be arrows with `t(a₁) = g₁ ≫ x`, `s(a₁) = y`, `t(a₂) = g₂ ≫ y` and `s(a₂) = z`.  Let
`c` be an arrow with `t(c) = (g₂ ≫ g₁) ≫ x` and `s(c) = z` which the cocycle law presents as the
composite of `g₂ ≫ a₁` and `a₂`.  Then the base-changed transition along `g₂ ≫ g₁` and `c` is the
inverse image along `g₂` of the one along `g₁` and `a₁`, followed by the one along `g₂` and `a₂`,
with the comparison of Stacks 03LU for the composite in front.

This is the composition law of the restriction map of the module
`ℱ(T, u) = Γ(T, u_{small}^*𝒢)` of Stacks 06WT: `Q' = h_{T''}`, `Q = h_{T'}`, `P = h_T`, the two
`g` the represented arrows of a composable pair of the site, and `a₁`, `a₂` the arrow components
of the two morphisms of `[U/_pR]`.  Together with
`AlgebraicGeometry.Space.groupoidPullbackTransitionAt_identityArrow` it is the coherence of the
transition, which is item 1 of "What remains, precisely" in the module documentation.

Two halves go into it: the cocycle law of the groupoid module, through
`AlgebraicGeometry.Space.groupoidPullbackTransitionAt_comp`, and the compatibility of the
Stacks 03LU comparison with a composite base change, through
`AlgebraicGeometry.Space.modulePullbackCompIso_inv_comp_map_comp`.

The proof is a term-mode chain and not a `rw` script on purpose.  Each step is cheap on its own,
but a `rw` script accumulates `Eq.mpr` motives which must reconcile `(g₂ ≫ g₁) ≫ x` with
`g₂ ≫ g₁ ≫ x` underneath an `CategoryTheory.eqToHom`, and that reconciliation is a kernel
timeout; in a chain of `Eq.trans` and `congrArg` it never arises. -/
theorem groupoidPullbackTransitionBaseChange_comp {Q' Q P : AlgebraicSpaces B S hS}
    (g₂ : Q' ⟶ Q) (g₁ : Q ⟶ P) (x : P ⟶ G.objects) {y : Q ⟶ G.objects} {z : Q' ⟶ G.objects}
    {a₁ : Q ⟶ G.arrows} {a₂ c : Q' ⟶ G.arrows}
    (hx₁ : a₁ ≫ G.target = g₁ ≫ x) (hy₁ : a₁ ≫ G.source = y)
    (hx₂ : a₂ ≫ G.target = g₂ ≫ y) (hy₂ : a₂ ≫ G.source = z)
    (hc : c ≫ G.target = (g₂ ≫ g₁) ≫ x) (hcz : c ≫ G.source = z)
    (hcoc : TransitionCocycle B S hS (U := G.objects) (V := G.arrows)
      (a := G.target) (b := G.source) F α (g₂ ≫ a₁) a₂ c) :
    groupoidPullbackTransitionBaseChange B S hS G F α (g₂ ≫ g₁) x c hc hcz =
      (modulePullbackCompIso B S hS g₂ g₁).inv.app ((modulePullback B S hS x).obj F) ≫
        (modulePullback B S hS g₂).map
            (groupoidPullbackTransitionBaseChange B S hS G F α g₁ x a₁ hx₁ hy₁) ≫
          groupoidPullbackTransitionBaseChange B S hS G F α g₂ y a₂ hx₂ hy₂ :=
  have e₁ : (g₂ ≫ a₁) ≫ G.target = g₂ ≫ g₁ ≫ x := by rw [Category.assoc, hx₁]
  have e₂ : (g₂ ≫ a₁) ≫ G.source = g₂ ≫ y := by rw [Category.assoc, hy₁]
  ((groupoidPullbackTransitionBaseChange_eq_comp B S hS G F α (g₂ ≫ g₁) x c hc hcz).trans
    (congrArg (fun m => (modulePullbackCompIso B S hS (g₂ ≫ g₁) x).hom.app F ≫ m)
      ((groupoidPullbackTransitionAt_comp B S hS G F α e₁ e₂ hx₂ hy₂ hc hcz hcoc).trans
        (congrArg (fun m => m ≫ groupoidPullbackTransitionAt B S hS G F α a₂ hx₂ hy₂)
          (groupoidPullbackTransitionAt_reindex B S hS G F α g₂ a₁ hx₁ hy₁
            e₁ e₂).symm)))).trans
    ((modulePullbackCompIso_inv_comp_map_comp B S hS g₂ g₁ x F
          (groupoidPullbackTransitionAt B S hS G F α a₁ hx₁ hy₁)
          (groupoidPullbackTransitionAt B S hS G F α a₂ hx₂ hy₂)).symm.trans
      (comp₃_congr rfl
        (congrArg (fun m => (modulePullback B S hS g₂).map m)
          (groupoidPullbackTransitionBaseChange_eq_comp B S hS G F α g₁ x a₁ hx₁ hy₁).symm)
        (groupoidPullbackTransitionBaseChange_eq_comp B S hS G F α g₂ y a₂ hx₂ hy₂).symm))

/-- **The base-changed transition re-ended along an equality of source morphisms.**  Following it
by the canonical identification of the inverse images along two equal morphisms into the object
space is the same transition with its source condition composed with that equality.

This is the adapter a consumer at the representable algebraic space of a test object needs: the
source of the composite of two `T`-points of the arrow space agrees with the source of the second
only propositionally (Stacks 043W, `Deformation.PointwiseGroupoid.source_comp`), so the two sides
of a composition law stated there land in inverse images along two morphisms which are equal and
not identical. -/
theorem groupoidPullbackTransitionBaseChange_comp_pullbackTransport
    {Q P : AlgebraicSpaces B S hS} (g : Q ⟶ P) (x : P ⟶ G.objects) (a : Q ⟶ G.arrows)
    {y y' : Q ⟶ G.objects} (hx : a ≫ G.target = g ≫ x) (hy : a ≫ G.source = y) (e : y = y') :
    groupoidPullbackTransitionBaseChange B S hS G F α g x a hx hy ≫
        pullbackTransport F e =
      groupoidPullbackTransitionBaseChange B S hS G F α g x a hx (hy.trans e) := by
  rw [groupoidPullbackTransitionBaseChange_eq_comp,
    groupoidPullbackTransitionBaseChange_eq_comp, groupoidPullbackTransitionAt_eq_comp,
    groupoidPullbackTransitionAt_eq_comp, Category.assoc, Category.assoc, Category.assoc,
    pullbackTransport_comp F hy e (hy.trans e)]

end CocycleBaseChange

/-! ### The cocycle condition of the groupoid module, read at a composable pair of arrows -/

/-- **The cocycle field of a quasi-coherent module on the groupoid, read at a composable pair of
arrows into the arrow space.**  The cocycle condition of Stacks 0441 is stated at the space of
composable pairs of arrows, along its two projections and the composition; a composable pair
`a₁`, `a₂ : P ⟶ R` is a `P`-point of that space, and precomposing the condition with it gives the
condition at `a₁`, `a₂` and their composite.

This is `AlgebraicGeometry.Space.TransitionCocycle.comp`, the stability of the cocycle law under
precomposition, and it is what discharges the `hcoc` hypothesis of
`AlgebraicGeometry.Space.groupoidPullbackTransitionAt_comp` and of
`AlgebraicGeometry.Space.groupoidPullbackTransitionBaseChange_comp`.  At `P` the representable
algebraic space of a test object the composable pair is a composable pair of `T`-points of the
arrow space and the composite is their composite in the groupoid of `T`-points, by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.arrowComp_hom`. -/
theorem transitionCocycle_arrowComp (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
    (M : QuasicoherentModule B S hS G) {P : AlgebraicSpaces B S hS} (a₁ a₂ : P ⟶ G.arrows)
    (h : a₁ ≫ G.source = a₂ ≫ G.target) :
    TransitionCocycle B S hS (U := G.objects) (V := G.arrows) (a := G.target) (b := G.source)
      M.F.obj M.alpha a₁ a₂ (GroupoidInAlgebraicSpaces.arrowComp G a₁ a₂ h) :=
  TransitionCocycle.comp B S hS M.F.obj M.alpha
    (GroupoidInAlgebraicSpaces.comp_comp_target G)
    (GroupoidInAlgebraicSpaces.firstArrow_comp_source G)
    (GroupoidInAlgebraicSpaces.comp_comp_source G) (fun _ _ _ => M.cocycle)
    ((AlgebraicSpaces.isPullback_fiberProduct B S hS G.source G.target).lift a₁ a₂ h)
    ((AlgebraicSpaces.isPullback_fiberProduct B S hS G.source G.target).lift_fst a₁ a₂ h)
    ((AlgebraicSpaces.isPullback_fiberProduct B S hS G.source G.target).lift_snd a₁ a₂ h) rfl

/-- **The composition law of the retargeted reindexing of a quasi-coherent module on the
groupoid.**  `AlgebraicGeometry.Space.groupoidPullbackTransitionAt_comp` with its cocycle
hypothesis discharged from the `cocycle` field, at the composite of a composable pair of
arrows. -/
theorem groupoidPullbackTransitionAt_arrowComp (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
    (M : QuasicoherentModule B S hS G) {P : AlgebraicSpaces B S hS} (a₁ a₂ : P ⟶ G.arrows)
    (h : a₁ ≫ G.source = a₂ ≫ G.target) {x y z : P ⟶ G.objects}
    (hx : a₁ ≫ G.target = x) (hy : a₁ ≫ G.source = y)
    (hy' : a₂ ≫ G.target = y) (hz : a₂ ≫ G.source = z)
    (hcx : GroupoidInAlgebraicSpaces.arrowComp G a₁ a₂ h ≫ G.target = x)
    (hcz : GroupoidInAlgebraicSpaces.arrowComp G a₁ a₂ h ≫ G.source = z) :
    groupoidPullbackTransitionAt B S hS G M.F.obj M.alpha
        (GroupoidInAlgebraicSpaces.arrowComp G a₁ a₂ h) hcx hcz =
      groupoidPullbackTransitionAt B S hS G M.F.obj M.alpha a₁ hx hy ≫
        groupoidPullbackTransitionAt B S hS G M.F.obj M.alpha a₂ hy' hz :=
  groupoidPullbackTransitionAt_comp B S hS G M.F.obj M.alpha hx hy hy' hz hcx hcz
    (transitionCocycle_arrowComp B S hS G M a₁ a₂ h)

/-- **The composition law of the backward functor's restriction map, with the cocycle hypothesis
discharged.**  `AlgebraicGeometry.Space.groupoidPullbackTransitionBaseChange_comp` at the
composite of the restriction of the first arrow and the second, whose cocycle law is the
`cocycle` field of the groupoid module.

This is the composition half of the coherence of the restriction map of Stacks 06WT, stated with
no hypothesis beyond the data of the two morphisms being composed. -/
theorem groupoidPullbackTransitionBaseChange_arrowComp (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
    (M : QuasicoherentModule B S hS G) {Q' Q P : AlgebraicSpaces B S hS} (g₂ : Q' ⟶ Q)
    (g₁ : Q ⟶ P) (x : P ⟶ G.objects) {y : Q ⟶ G.objects} {z : Q' ⟶ G.objects}
    {a₁ : Q ⟶ G.arrows} {a₂ : Q' ⟶ G.arrows}
    (hx₁ : a₁ ≫ G.target = g₁ ≫ x) (hy₁ : a₁ ≫ G.source = y)
    (hx₂ : a₂ ≫ G.target = g₂ ≫ y) (hy₂ : a₂ ≫ G.source = z)
    (h : (g₂ ≫ a₁) ≫ G.source = a₂ ≫ G.target)
    (hc : GroupoidInAlgebraicSpaces.arrowComp G (g₂ ≫ a₁) a₂ h ≫ G.target = (g₂ ≫ g₁) ≫ x)
    (hcz : GroupoidInAlgebraicSpaces.arrowComp G (g₂ ≫ a₁) a₂ h ≫ G.source = z) :
    groupoidPullbackTransitionBaseChange B S hS G M.F.obj M.alpha (g₂ ≫ g₁) x
        (GroupoidInAlgebraicSpaces.arrowComp G (g₂ ≫ a₁) a₂ h) hc hcz =
      (modulePullbackCompIso B S hS g₂ g₁).inv.app
          ((modulePullback B S hS x).obj M.F.obj) ≫
        (modulePullback B S hS g₂).map
            (groupoidPullbackTransitionBaseChange B S hS G M.F.obj M.alpha g₁ x a₁ hx₁ hy₁) ≫
          groupoidPullbackTransitionBaseChange B S hS G M.F.obj M.alpha g₂ y a₂ hx₂ hy₂ :=
  groupoidPullbackTransitionBaseChange_comp B S hS G M.F.obj M.alpha g₂ g₁ x hx₁ hy₁ hx₂ hy₂
    hc hcz (transitionCocycle_arrowComp B S hS G M (g₂ ≫ a₁) a₂ h)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {A : AlgebraicSpaces C S hS}

/-! ### The transition morphisms of the backward functor -/

/-- **The transition along a `T`-point of the arrow space.**  A `T`-point `a` of the arrow space
`R` is an arrow of the groupoid from its source to its target, and this is the action of that
arrow on the modules of the formula: `AlgebraicGeometry.Space.groupoidPullbackTransitionAt` at
the representable algebraic space of `T`, whose two endpoint conditions are the two instances of
`AlgebraicGeometry.Space.yonedaSectionHom_comp` at the target and at the source of the groupoid.

This is the half of the backward functor's restriction map that the ordinary inverse image does
not supply: the morphisms of `[U/_pR]` over the identity of `T` are exactly the `T`-points of
`R`, and this is the action of one of them. -/
def prestackArrowTransition (G : GroupoidInAlgebraicSpaces C S hS A)
    (M : Space.QuasicoherentModule C S hS G) (T : BigFppfOver C S hS)
    (a : G.arrows.1.obj (op T)) :
    prestackPointModule G M T (G.target.hom.app (op T) a) ⟶
      prestackPointModule G M T (G.source.hom.app (op T) a) :=
  Space.groupoidPullbackTransitionAt C S hS G M.F.obj M.alpha
    (Space.yonedaSectionHom C S hS G.arrows T a)
    (Space.yonedaSectionHom_comp C S hS G.target T a)
    (Space.yonedaSectionHom_comp C S hS G.source T a)

/-- **The transition attached to a morphism of the pointwise quotient.**  By Stacks 02XV a
morphism `(T', w') ⟶ (T, w)` of `[U/_pR]` is an arrow `f : T' ⟶ T` of the site together with an
arrow `w' ⟶ w|_{T'}` of the groupoid of `T'`-points, that is (Stacks 043W) a `T'`-point `a` of
the arrow space with `s(a) = w'` and `t(a) = w|_{T'}`; `ha` is the second of those two equations
and the conclusion reads the first off `a`.

The morphism is `AlgebraicGeometry.Space.groupoidPullbackTransitionBaseChange` at the represented
arrow of `f`: the composition comparison of Stacks 03LU along `f`, the transport along the target
condition, and the action of `a`.  This is the restriction map the module
`ℱ(T, w) = Γ(T, w_small^*𝒢)` of Stacks 06WT must carry, before global sections are taken.

Its coherence — the identity and composition laws — is proved at a general test space, by
`AlgebraicGeometry.Space.groupoidPullbackTransitionAt_identityArrow` and
`AlgebraicGeometry.Space.groupoidPullbackTransitionBaseChange_comp`, and carried here by
`AlgebraicGeometry.Stack.prestackTransition_eq`; what is *not* done is the packaging of the
values into a presheaf, which is item 1 of "What remains, precisely" in the module
documentation. -/
def prestackTransition (G : GroupoidInAlgebraicSpaces C S hS A)
    (M : Space.QuasicoherentModule C S hS G) {T' T : BigFppfOver C S hS} (f : T' ⟶ T)
    (w : G.objects.1.obj (op T)) (a : G.arrows.1.obj (op T'))
    (ha : G.target.hom.app (op T') a = G.objects.1.map f.op w) :
    (Space.modulePullback C S hS (Space.representedSpaceMap C S hS f)).obj
        (prestackPointModule G M T w) ⟶
      prestackPointModule G M T' (G.source.hom.app (op T') a) :=
  Space.groupoidPullbackTransitionBaseChange C S hS G M.F.obj M.alpha
    (Space.representedSpaceMap C S hS f) (Space.yonedaSectionHom C S hS G.objects T w)
    (Space.yonedaSectionHom C S hS G.arrows T' a)
    (((Space.yonedaSectionHom_comp C S hS G.target T' a).trans
        (congrArg (Space.yonedaSectionHom C S hS G.objects T') ha)).trans
      (Space.representedSpaceMap_comp_yonedaSectionHom C S hS G.objects f w).symm)
    (Space.yonedaSectionHom_comp C S hS G.source T' a)

/-! ### The specializations, pinned by equation -/

/-- **The transition along a `T`-point of the arrow space is the retargeted reindexing at the
representable algebraic space of `T`**, as an equation.

This is what carries `AlgebraicGeometry.Space.groupoidPullbackTransitionAt_naturality` — the
naturality in the groupoid module, which is where the compatibility field of
`AlgebraicGeometry.Space.QuasicoherentModule.Hom` is consumed — to this transition.  The
naturality square is *not* restated at this instance, and the obstruction is mechanical: forming the
composite `≫` of two morphisms of `AlgebraicGeometry.Space.Modules` at the representable algebraic
space of a test object exceeds the elaborator's recursion budget, every category instance in sight
carrying `AlgebraicGeometry.isAlgebraicSpace_yoneda` inside a small étale ringed site.  That is why
the naturality is proved at a variable test space, where nothing unfolds, and transported by this
equation rather than restated. -/
theorem prestackArrowTransition_eq (G : GroupoidInAlgebraicSpaces C S hS A)
    (M : Space.QuasicoherentModule C S hS G) (T : BigFppfOver C S hS)
    (a : G.arrows.1.obj (op T)) :
    prestackArrowTransition G M T a =
      Space.groupoidPullbackTransitionAt C S hS G M.F.obj M.alpha
        (Space.yonedaSectionHom C S hS G.arrows T a)
        (Space.yonedaSectionHom_comp C S hS G.target T a)
        (Space.yonedaSectionHom_comp C S hS G.source T a) :=
  rfl

/-- **The transition attached to a morphism of the pointwise quotient is the base-changed
reindexing at the represented arrow**, as an equation, carrying
`AlgebraicGeometry.Space.groupoidPullbackTransitionBaseChange_naturality` to it.  See
`AlgebraicGeometry.Stack.prestackArrowTransition_eq` for why the naturality is proved at a
variable test space and transported rather than restated here. -/
theorem prestackTransition_eq (G : GroupoidInAlgebraicSpaces C S hS A)
    (M : Space.QuasicoherentModule C S hS G) {T' T : BigFppfOver C S hS} (f : T' ⟶ T)
    (w : G.objects.1.obj (op T)) (a : G.arrows.1.obj (op T'))
    (ha : G.target.hom.app (op T') a = G.objects.1.map f.op w) :
    prestackTransition G M f w a ha =
      Space.groupoidPullbackTransitionBaseChange C S hS G M.F.obj M.alpha
        (Space.representedSpaceMap C S hS f) (Space.yonedaSectionHom C S hS G.objects T w)
        (Space.yonedaSectionHom C S hS G.arrows T' a)
        (((Space.yonedaSectionHom_comp C S hS G.target T' a).trans
            (congrArg (Space.yonedaSectionHom C S hS G.objects T') ha)).trans
          (Space.representedSpaceMap_comp_yonedaSectionHom C S hS G.objects f w).symm)
        (Space.yonedaSectionHom_comp C S hS G.source T' a) :=
  rfl

/-- **The action of a `T`-point of the arrow space on the sections of the formula.**  The
global-sections comparison applied to `AlgebraicGeometry.Stack.prestackArrowTransition`: a
`Γ(T, 𝒪_T)`-linear map from the sections of the formula at the target of `a` to its sections at
the source of `a`.

This is the restriction map of the backward functor of Stacks 06WT along a morphism of
`[U/_pR]` *over the identity of `T`* — by Stacks 02XV those are exactly the `T`-points of the
arrow space — and over the identity no base change intervenes, so the map is the comparison of
global sections and nothing else.  The restriction map along a morphism with a nontrivial
arrow of the site is `AlgebraicGeometry.Stack.prestackTransition`, whose reading on global
sections is item 1 of "What remains, precisely" in the module documentation. -/
def prestackArrowTransitionSections (G : GroupoidInAlgebraicSpaces C S hS A)
    (M : Space.QuasicoherentModule C S hS G) (T : BigFppfOver C S hS)
    (a : G.arrows.1.obj (op T)) :
    prestackPointSections G M T (G.target.hom.app (op T) a) ⟶
      prestackPointSections G M T (G.source.hom.app (op T) a) :=
  (prestackPointSectionsFunctor T).map (prestackArrowTransition G M T a)

/-! ### The residue -/

/-- **The residue of the backward functor of Stacks 06WT**: the formula
`ℱ(T, u) = Γ(T, u_{small}^*𝒢)` packaged as a functor into the quasi-coherent modules on the
pointwise quotient.

The `functor` field is the backward functor itself, and the `sections` field pins it to the
source's formula: at every object `(T, w)` of `[U/_pR]` the sections of the module it produces
are `AlgebraicGeometry.Stack.prestackPointSections`, which is `Γ(T, u_small^*𝒢)` by
construction.  Without that field the structure would be satisfied by any functor at all, the
constant one at the zero module included, so the pinning is what makes it a statement about the
source's backward functor rather than about the existence of some functor.

The pinning is at the level of the underlying additive groups, and `ULift` appears because the
two sides are at different module universes — `u` for the formula, which
`AlgebraicGeometry.Space.modulePullback` forces, and `u + 1` for the quasi-coherent modules on
`[U/_pR]`, which Stacks 06WH forces (see "The module universes" in the module documentation).

What the structure does *not* pin is the restriction maps, which are determined by the sheaf once
the objects are: the datum they must agree with is
`AlgebraicGeometry.Stack.prestackTransition`, defined above, followed by the comparison of global
sections.  Its coherence — both halves — is proved above as well; what a full packaging still
needs is item 1 of "What remains, precisely" minus that coherence, together with items 2 and
3. -/
structure PrestackBackwardFunctor (G : GroupoidInAlgebraicSpaces C S hS A) where
  /-- The backward functor of the source's proof. -/
  functor : Space.QuasicoherentModule C S hS G ⥤
    FibredSite.quasicoherentModules.{u, u + 1, u + 1, u + 1} C S hS (quotientPrestack G).p
      (isFiberedInGroupoids_quotientPrestack G)
  /-- Its values are the sections of the source's formula. -/
  sections : ∀ (M : Space.QuasicoherentModule C S hS G) (T : BigFppfOver C S hS)
      (w : G.objects.1.obj (op T)),
      ((functor.obj M).obj.val.presheaf.obj (op (prestackPoint G T w).1)) ≃+
        ULift.{u + 1} (prestackPointSections G M T w)

/-- **The backward functor together with the verification the source omits is Stacks 06WT on the
pointwise quotient.**

Stacks 06WT builds a forward and a backward functor between the quasi-coherent modules on
`[U/_pR]` and the quasi-coherent modules on the groupoid and then says "we omit the verification
that the functors constructed above are quasi-inverse to each other".  Read on the backward
functor, that verification is exactly that it is an equivalence — its quasi-inverse then being
the source's forward functor — and this is the implication the source's proof makes from it:
`AlgebraicGeometry.Stack.PointwiseQuotientGroupoidEquivalence`, the one remaining hypothesis of
the carrier of Stacks 06WT.

This is why the residue above is a functor and not a `Nonempty` of an equivalence: the
hypothesis `D.functor.IsEquivalence` is about the source's own backward functor, pinned by the
`sections` field, and not about an unrelated equivalence of the two categories. -/
theorem pointwiseQuotientGroupoidEquivalence_of_prestackBackwardFunctor
    (G : GroupoidInAlgebraicSpaces C S hS A) (D : PrestackBackwardFunctor G)
    (hD : D.functor.IsEquivalence) :
    PointwiseQuotientGroupoidEquivalence G :=
  ⟨D.functor.asEquivalence.symm⟩

/-! ### The sheaf condition for the inherited fppf topology

This is item 2 of "What remains, precisely", and it is fppf descent for the sections of a
quasi-coherent module.  Three statements, each with no hypothesis beyond the data: the module of
the formula read on the representing scheme is quasi-coherent, so Stacks 03DT applies to it both
over the schemes over `T` and on `(Sch/T)_fppf`; and the equivalence of sites of Stacks 06WI
carries the second to the localization of `[U/_pR]` at the object `(T, w)`.  The last statement
assembles the slices into the inherited fppf sheaf condition on the whole of `[U/_pR]`, over the
presheaf of item 1. -/

/-- **The module of the formula, read on the representing scheme, is quasi-coherent.**  The
inverse image `w_small^*𝒢` is quasi-coherent on the small étale site of `h_T`
(`AlgebraicGeometry.Stack.isQuasicoherentOnSite_prestackPointModule`, Stacks 03GA), and the
Zariski restriction of a quasi-coherent `𝒪`-module on a represented algebraic space is a
quasi-coherent sheaf of modules on the representing scheme.

This is the hypothesis Stacks 03DT asks for, so it is what makes the sheaf condition of the
backward functor of Stacks 06WT available at all. -/
instance isQuasicoherent_prestackPointSchemeModule (G : GroupoidInAlgebraicSpaces C S hS A)
    (M : Space.QuasicoherentModule C S hS G) (T : BigFppfOver C S hS)
    (w : G.objects.1.obj (op T)) :
    SheafOfModules.IsQuasicoherent (prestackPointSchemeModule G M T w) :=
  Space.isQuasicoherent_representedZariskiRestriction C S hS T _
    (isQuasicoherentOnSite_prestackPointModule G M T w)

/-- **Stacks 03DT at the module of the formula, over the schemes over `T`, with no hypothesis.**
The presheaf of Stacks 03DS of `w_small^*𝒢` read on the representing scheme — which sends
`f : T' ⟶ T` to `Γ(T', f^*w_small^*𝒢)` — satisfies the sheaf condition for every fppf covering.

This is item 2 of "What remains, precisely" in the form it takes one level down, and it carries
no hypothesis: `AlgebraicGeometry.quasiCoherentPresheaf_isSheaf_fppf` is conditional on
`AlgebraicGeometry.FpqcDescentOfQuasicoherentHoms`, the full-faithfulness half of Stacks 023T,
and that condition is the theorem `AlgebraicGeometry.fpqcDescentOfQuasicoherentHoms`, so the
unconditional form `AlgebraicGeometry.quasiCoherentPresheaf_isSheaf_fppf'` is what is used
here. -/
theorem isSheaf_fppf_quasiCoherentPresheaf_prestackPointSchemeModule
    (G : GroupoidInAlgebraicSpaces C S hS A) (M : Space.QuasicoherentModule C S hS G)
    (T : BigFppfOver C S hS) (w : G.objects.1.obj (op T)) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over ((BigFppfOver.toScheme C S hS).obj T))
      (quasiCoherentPresheafFunctor ((BigFppfOver.toScheme C S hS).obj T)
        (prestackPointSchemeModule G M T w)) :=
  quasiCoherentPresheaf_isSheaf_fppf' _ _

/-- **The sheaf condition of the backward functor at one object of `[U/_pR]`, with no
hypothesis.**  Transported across the equivalence of sites `[U/_pR]_fppf/(T, w) ≌ (Sch/T)_fppf`
of Stacks 06WI, the pullback-sections presheaf of the module of the formula is a sheaf for the
localization at `(T, w)` of the inherited fppf topology.

The sheaf condition on `(Sch/T)_fppf` is Stacks 03DT on the big fppf site of `T`, which
`AlgebraicGeometry.BigFppfOver.isSheaf_sectionsPresheafOfModules_baseOverTopology` has with no
hypothesis, and the transport is `CategoryTheory.Functor.op_comp_isSheaf` at the functor of
Stacks 06WI, which is a dense subsite inclusion for the two localized fppf topologies.

Nothing here needs the universes to be narrowed: the equivalence of sites of Stacks 06WI and
its dense-subsite instance hold for a fibred category with objects in `Type v` and morphisms in
`Type w`, which is why this applies to `AlgebraicGeometry.Stack.quotientPrestack`, whose
morphisms are in `Type (u + 1)`. -/
theorem isSheaf_localizedFppf_prestackPointSections
    (G : GroupoidInAlgebraicSpaces C S hS A) (M : Space.QuasicoherentModule C S hS G)
    (T : BigFppfOver C S hS) (w : G.objects.1.obj (op T)) :
    Presheaf.IsSheaf
      (FibredSite.localizedTopology' C S hS (quotientPrestack G).p (prestackPoint G T w).1)
      ((FibredSite.localizationEquivalence' C S hS (quotientPrestack G).p
          (isFiberedInGroupoids_quotientPrestack G) (prestackPoint G T w).1).functor.op ⋙
        (BigFppfOver.sectionsPresheafOfModules C ((BigFppfOver.toScheme C S hS).obj T)
          T.left.2 (prestackPointSchemeModule G M T w)).presheaf) :=
  Functor.op_comp_isSheaf _ _
    (BigFppfOver.topology C
      (FibredSite.baseScheme' C S hS (quotientPrestack G).p (prestackPoint G T w).1)
      (FibredSite.contains_baseScheme' C S hS (quotientPrestack G).p (prestackPoint G T w).1))
    ⟨_, BigFppfOver.isSheaf_sectionsPresheafOfModules_baseOverTopology C _ _ .fppf
      (prestackPointSchemeModule G M T w)⟩

/-- **Item 2 of "What remains, precisely": the sheaf condition of the backward functor of
Stacks 06WT for the inherited fppf topology.**  A presheaf on the site of `[U/_pR]` which is a
sheaf for *some* inherited associated topology, and which at every object `(T, w)` restricts —
across the equivalence of sites of Stacks 06WI — to the pullback-sections presheaf of the module
of the formula, is a sheaf for the inherited fppf topology.

The two hypotheses are exactly what item 1 produces and nothing more: a presheaf assembled from
the values `Γ(T, w_small^*𝒢)`, and the identification of its restriction to each slice with the
source's formula there.  The sheaf condition itself is discharged here: slice by slice it is
`AlgebraicGeometry.Stack.isSheaf_localizedFppf_prestackPointSections`, and
`CategoryTheory.SiteGlueing.isSheaf_of_coversTop_of_isSheaf_over_anyCategory'` assembles the
slices, the family of all objects of `[U/_pR]` covering the final object for the coarser topology
(`Stacks.SheafOfModules.coversTop_ulift_self`).  Every object of `[U/_pR]` is a
`AlgebraicGeometry.Stack.prestackPoint`, by
`AlgebraicGeometry.Stack.exists_prestackPoint` at its own image, so quantifying the hypothesis
over `(T, w)` loses nothing.

This is the source's own argument, one level up: the restriction to a slice is an `𝓗^a` by the
essential-surjectivity half of Stacks 03DX (1), and `𝓗^a` is an fppf sheaf by Stacks 03DT.  Here
the restriction is the pullback-sections presheaf on the nose rather than up to that
identification, so only Stacks 03DT is consumed. -/
theorem isSheaf_fppf_of_prestackPointSections (G : GroupoidInAlgebraicSpaces C S hS A)
    (M : Space.QuasicoherentModule C S hS G) (τ : SiteKind)
    (P : ((quotientPrestack G).obj)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (hP : Presheaf.IsSheaf
      (BigFppfOver.associatedTopology C S hS (quotientPrestack G).p τ) P)
    (hP' : ∀ (T : BigFppfOver C S hS) (w : G.objects.1.obj (op T)),
      ((Over.forget (prestackPoint G T w).1).op ⋙ P) ≅
        (FibredSite.localizationEquivalence' C S hS (quotientPrestack G).p
            (isFiberedInGroupoids_quotientPrestack G) (prestackPoint G T w).1).functor.op ⋙
          (BigFppfOver.sectionsPresheafOfModules C ((BigFppfOver.toScheme C S hS).obj T)
            T.left.2 (prestackPointSchemeModule G M T w)).presheaf) :
    Presheaf.IsSheaf
      (BigFppfOver.associatedTopology C S hS (quotientPrestack G).p .fppf) P := by
  refine CategoryTheory.SiteGlueing.isSheaf_of_coversTop_of_isSheaf_over_anyCategory'
    (BigFppfOver.associatedTopology C S hS (quotientPrestack G).p .fppf)
    (Stacks.SheafOfModules.coversTop_ulift_self.{u + 1, u + 1, u + 1}
      (BigFppfOver.associatedTopology C S hS (quotientPrestack G).p τ)) P hP ?_
  intro i
  obtain ⟨w, hw⟩ :=
    exists_prestackPoint G ((quotientPrestack G).p.obj i.down) ⟨i.down, rfl⟩
  rw [show i.down = (prestackPoint G ((quotientPrestack G).p.obj i.down) w).1 from
    congrArg Subtype.val hw]
  exact (Presheaf.isSheaf_of_iso_iff
      (hP' ((quotientPrestack G).p.obj i.down) w)).mpr
    (isSheaf_localizedFppf_prestackPointSections G M _ w)

end AlgebraicGeometry.Stack

end
