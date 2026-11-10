module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleExactAssociatedModule
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePseudoCoherentSpellings
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 08HE, stated: the two obligations that remain, as Lean statements

Stacks 08HE says that for a scheme `S` and an object `E` of `D(𝒪_S)` the following are
equivalent: (1) `E` is `m`-pseudo-coherent, and (2) `ε^*E` is `m`-pseudo-coherent on the small
étale site, where `ε` is the morphism of ringed sites of Stacks 08H7.

Clause (1) ⇒ (2) is proved in this development, with no hypothesis, in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtalePseudoCoherentForward.lean`;
clause (2) ⇒ (1), and so the equivalence, is not.  This module exists so that what remains is a
*statement* in Lean rather than a remark in a comment: the equivalence and each of its two
implications are written out below as `Prop`-valued definitions, elaborated at the two sites' own
universes, at an arbitrary object `E` and an arbitrary integer `m`.  Anything later claiming to
close 08HE can be checked against them.

## What this module settles about the statement itself

`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtalePseudoCoherentSpellings.lean`
records in a comment that clause (2) becomes expressible once the ringed sites are spelled
reducibly, and displays the statement carrying one hypothesis,
`[PreservesFiniteLimits (associatedModuleOfSheaf B S hS)]`.  Two corrections, both machine
checked here:

* That display is **incomplete**.  `CategoryTheory.Functor.mapDerivedCategory` needs its functor
  to be additive and to preserve finite *colimits* as well as finite limits; those two are
  instances
  (`AlgebraicGeometry.SmallEtale.additive_associatedModuleOfSheaf` and
  `AlgebraicGeometry.SmallEtale.preservesFiniteColimits_associatedModuleOfSheaf`), so the display
  happened to elaborate, but it understated what clause (2) rests on.
* That hypothesis is now **unnecessary**.  It is the exactness assertion of Stacks 08H8, proved
  in `SmallEtaleExactAssociatedModule.lean` and supplied there as an instance.  The statements
  below therefore carry no hypothesis at all beyond the two derived-category models, which is
  strictly less than the comment claims is needed.

## Main definitions

* `AlgebraicGeometry.SmallEtale.PseudoCoherentIffAssociatedModule`: the equivalence of Stacks
  08HE, as a proposition.
* `AlgebraicGeometry.SmallEtale.PseudoCoherentToAssociatedModule`: its implication (1) ⇒ (2).
* `AlgebraicGeometry.SmallEtale.AssociatedModuleToPseudoCoherent`: its implication (2) ⇒ (1).
* `AlgebraicGeometry.SmallEtale.pseudoCoherentIff_of_imp`: the equivalence follows from the two
  implications.  This is the only thing proved here, and it is bookkeeping; it is stated so that
  the two obligations are visibly the whole of 08HE and not a proper part of it.

## What each obligation needs

Both implications reduce to one missing comparison, and it is the same one.

`AlgebraicGeometry.RingedSite.IsPseudoCoherentComplexFrom` asks, at every object of the site, for
a covering over each member `V` of which a strictly perfect complex maps to the restriction
`E|_V`.  To transport that datum across `ε` one needs the *localized* comparison

```
ε^* ⋙ (- |_{ε(U)})  ≅  (- |_U) ⋙ (ε_U)^*
```

identifying restriction-after-pullback with pullback-after-restriction, so that a strictly
perfect complex over a Zariski slice becomes one over the corresponding étale slice — strict
perfectness itself being carried by Stacks 08H3,
`AlgebraicGeometry.RingedToposHom.isStrictlyPerfect_pullbackModules`.

That comparison exists in this development for a morphism of ringed sites in a *single* universe,
as `AlgebraicGeometry.RingedSite.Hom.localizedPullbackToposSquare`
(`StacksFrontier/CategoryTheory/Sites/Modules/LocalizationRingedSites/PullbackToposSquare.lean`).
It does not apply to `ε`, whose source site has its objects in `Type (u + 1)` and its morphisms and
sections in `Type u`, so that `AlgebraicGeometry.RingedSite.Hom` cannot even hold `ε` — which is
why `ε` is an `AlgebraicGeometry.RingedSite.HomGeneral`.  Porting it is a transport of the same
kind as
`AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesToposIsoGeneral`
(`StacksFrontier/CategoryTheory/Sites/Modules/RingedToposModulesPullbackToposGeneral.lean`), which
is the first step of it and is proved; what is left is the localization half, namely the localized
morphism of ringed sites at independent universes together with the 2-isomorphism of Stacks 04J0
for it.

That route is not the one taken.  Because `ε` is flat (the exactness assertion of Stacks 08H8,
`AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModule`), the pullback on complexes
is the termwise functor, so clause (2) can be read through
`CategoryTheory.Functor.mapDerivedCategory` of an additive functor and the localization machinery
above is not required.  The comparison square that replaces it is available, as
`AlgebraicGeometry.SmallEtale.associatedModuleOverIso`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/`
`SmallEtaleOpenCoverQuasicoherence.lean`).
`CategoryTheory.Limits.PreservesFiniteLimits` of
`AlgebraicGeometry.SmallEtale.opensToSmallEtale` is available there too, as an instance.

`PseudoCoherentToAssociatedModule` is discharged **with no hypothesis** by
`AlgebraicGeometry.SmallEtale.pseudoCoherentToAssociatedModule_of_slice_exact`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtalePseudoCoherentForward.lean`),
which carries the `@[stacks 08HE]` attribute for clause (1) ⇒ (2).  Its name records the input it
consumes, not a hypothesis it carries: left exactness of the pullback along the *slice* structure
map is proved in that same file, as
`AlgebraicGeometry.SmallEtale.preservesFiniteLimits_pullback_sliceStructureMap`, so the theorem
takes only `E` and `m`.

Clause (2) ⇒ (1), and hence `PseudoCoherentIffAssociatedModule`, remains unproved.  The source
proves it by induction on `n - m`, `n` being the top nonvanishing cohomological degree, in five
steps.  Here is the status of each one in the library: only results proved in the library
count.

1. **Stacks 08H8, to place `E` in `D⁻(𝒪_S)`.**  **Available.**  Zero detection along `ε^*` holds
   for an arbitrary `𝒪_S`-module, as
   `AlgebraicGeometry.SmallEtale.isZero_of_isZero_associatedModule_zariskiModules`
   (`SmallEtaleAssociatedModuleReflectsZero.lean`): the two presentations of `ε` in this
   development — `toZariskiRingedSiteHom`, a morphism of ringed sites, and
   `toZariskiAbstractRingedToposHom`, a two-field morphism of ringed topoi — are the same
   morphism of ringed topoi by `rfl`, which carries the hypothesis-free
   `AlgebraicGeometry.SmallEtale.isZero_of_isZero_toZariskiModulePullback` over to `ε^*` itself
   and drops the quasi-coherence hypothesis of
   `AlgebraicGeometry.SmallEtale.isZero_of_isZero_associatedModule`.

   At the level of the derived category the consequence is
   `AlgebraicGeometry.SmallEtale.isZero_homology_associatedModule_iff`
   (`SmallEtaleDerivedReflectsZero.lean`): `Hⁿ(ε^*E)` vanishes exactly when `Hⁿ(E)` does, by
   exactness of `ε^*` through `CategoryTheory.Functor.mapDerivedCategoryHomologyIso`.
2. **Stacks 08FX, top cohomology of an `m`-pseudo-coherent object is of finite type.**
   **Available** at `AlgebraicGeometry.Scheme.zariskiRingedSite`.
   `AlgebraicGeometry.RingedSite.isFiniteType_homology`
   (`StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriekAndPerfection/`
   `TopCohomologyFiniteness.lean`) is stated at `RingedSite.{u, u, w}`, and all seven of its
   typeclass hypotheses are found at that site.
3. **Stacks 08HD, that a module whose associated module is of finite type is of finite type.**
   **Available for a quasi-coherent `𝓕`**, which is the case this chain consumes;
   **absent in general**.  The forward direction of the tag is proved for every `𝓕`,
   `AlgebraicGeometry.SmallEtale.isFiniteTypeOnSite_associatedModule`; the converse for a
   quasi-coherent `𝓕` is
   `AlgebraicGeometry.SmallEtale.isFiniteTypeOnSite_of_isFiniteTypeOnSite_associatedModule`
   (`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleFiniteTypeDescent.lean`),
   with the Mathlib-side form
   `AlgebraicGeometry.SmallEtale.isFiniteType_of_isFiniteTypeOnSite_associatedModule` beside it.
   Neither carries a `@[stacks 08HD]` attribute: the tag quantifies over an arbitrary
   `𝒪_S`-module and its general converse is still open.

   The route is the production of the `tᵢ`: descending a finite generating family of `ε^*𝓕`
   over an étale object to sections of `𝓕` over the image open.  For a quasi-coherent `𝓕` the
   sections are available — `AlgebraicGeometry.SmallEtale.associatedModulePresheafIso`
   identifies `Γ(W, 𝓕^a)` with the pullback sections of Stacks 03DS, and
   `AlgebraicGeometry.SmallEtale.bijective_restrictionBaseChange_of_isQuasicoherentOnSite`
   makes those `Γ(W) ⊗_{𝒪_S(U)} Γ(U, 𝓕)` between affine objects — so a generator is a finite
   sum `Σ bᵢ ⊗ mᵢ` and the `mᵢ` are the `tᵢ`.  That descent is **proved**, with the geometry of
   the site factored out of it, in
   `StacksFrontier/AlgebraicGeometry/Topologies/CartesianFlatSectionsDescent.lean`:

   * `Stacks.PresheafOfModules.mem_span_of_forall_restrict_mem_span` — membership in the span of
     a finite family of sections descends along a finite family of arrows whose restriction maps
     on rings are jointly faithfully flat and over which the presheaf of modules is cartesian;
   * `Stacks.PresheafOfModules.module_finite_sections_of_locally_generates` — at an object every
     covering sieve of which contains such a family
     (`Stacks.PresheafOfModules.HasFlatCartesianRefinement`), finitely many sections generating
     the module on the members of *some covering* already make the sections over the object
     itself a finite module over its ring of sections.  This is exactly the `tᵢ`, and the
     cartesian hypothesis it consumes is 03DX (2) in the shape the library states it,
     `Stacks.PresheafOfModules.restrictionBaseChange`.

   That refinement hypothesis is discharged for the **small affine étale site** of a scheme, in
   `StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleAffineFlatRefinement.lean`:
   `AlgebraicGeometry.SmallEtale.hasFlatCartesianRefinement_affineChartRings`, from
   `Stacks.Sites.exists_finite_flat_refinement` at
   `AlgebraicGeometry.SmallAffineEtale.precoverage` — whose coverings are finite and flat over
   the schemes by `AlgebraicGeometry.SmallEtale.smallAffineEtale_covering_finite_flat` — and
   `AlgebraicGeometry.SmallEtale.faithfullyFlat_pi_affineChartRings`.  Reading the engine through
   it gives `AlgebraicGeometry.SmallEtale.module_finite_sections_affineChart_of_locally_generates`.
   The affine subsite is the route, and not the small étale site itself, because there is **no**
   finite affine refinement for the latter: the scheme-side analogue of
   `AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_etale_ofArrows_le` does not exist,
   and the two statements closest to it (`exists_affine_mem_sieve_mem_range`,
   `exists_finite_affine_refinement_smallEtale` in
   `StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleCoveringsRefine.lean`) are
   `private` and of the wrong shape.

   Four further steps lie between that engine and the
   statement.  All four are assembled, in
   `StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/`
   `SmallEtaleAffineFiniteTypeSections.lean`
   and
   `StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleFiniteTypeDescent.lean`:

   * The cartesian hypothesis of
     `module_finite_sections_affineChart_of_locally_generates`, at a quasi-coherent module, is
     `AlgebraicGeometry.SmallEtale.bijective_restrictionBaseChange_affineChartModule`.  It is
     proved directly — it is the statement the proof of
     `bijective_restrictionBaseChange_of_isQuasicoherentOnSite` reaches one step before its
     conclusion — rather than by inverting
     `Stacks.PresheafOfModules.bijective_restrictionBaseChange_of_restriction`, which is proved
     by `:= h` but stated only from the subsite to the ambient site.
   * The transport of the finite-type datum to the affine subsite is
     `Stacks.SheafOfModules.generates_pushforward`: `PresheafOfModules.Generates` is a statement
     about covering sieves, so it transports along a *cocontinuous* functor and the whole input
     is `CategoryTheory.Functor.IsCocontinuous.cover_lift`.  Reading the covering of
     `SheafOfModules.IsFiniteTypeOnSite` and the sections of
     `Stacks.SheafOfModules.exists_generates_of_hasFiniteGlobalGenerators_over` through it gives
     `AlgebraicGeometry.SmallEtale.module_finite_sections_affineChartModule_of_isFiniteTypeOnSite`.
   * The identification `Γ(ε(U), ε^*𝓕) ≅ Γ(U, 𝓕)` over `Γ(S, U) ≅ 𝒪(ε(U))` is not assembled
     from `isIso_sectionsUnit` and `associatedModuleIsoSectionsPresheaf` after all: the unit of
     the associated-module adjunction is already an isomorphism at a quasi-coherent module,
     `AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent`, and its component at an open `U` is
     that identification, the ring map being `AlgebraicGeometry.Scheme.Opens.topIso` through
     `AlgebraicGeometry.SmallEtale.structureMap_hom_app`.  Finiteness descends along it by
     `Stacks.module_finite_compHom_of_surjective`, giving
     `AlgebraicGeometry.SmallEtale.module_finite_sections_affineOpen_of_isFiniteTypeOnSite`.
   * The last step is
     `Stacks.AlgebraicGeometry.FiniteTypeBridge.isFiniteType_of_finite_sections`
     (`StacksFrontier/AlgebraicGeometry/Coherent/IdealSheafFiniteTypeBridge.lean`) followed by
     `Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType`.

   The lemma this route proves is the one 0DII consumes — a *quasi-coherent* `𝓕`, read at an
   affine chart — and not the general 08HE (2) ⇒ (1) input; the general statement of Stacks 08HD
   for an arbitrary `𝒪_S`-module stays open.  **Where its quasi-coherence is spent.**
   The hypothesis is used in exactly three places, and *not* in zero-detection, which step 1
   freed of it:

   * `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent`
     (Stacks 03DV (2)), which needs a presentation on an affine cover;
   * through that, the cartesian hypothesis
     `AlgebraicGeometry.SmallEtale.bijective_restrictionBaseChange_affineChartModule`
     (Stacks 03DX), whose proof goes by
     `Stacks.SheafOfModules.exists_finite_globalPresentation_cover` — the finite global
     presentation is the whole of what quasi-coherence buys, and the faithfully-flat span-descent
     engine of `StacksFrontier/AlgebraicGeometry/Topologies/CartesianFlatSectionsDescent.lean`
     *consumes* cartesianness as a hypothesis and cannot prove it;
   * `AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent`, used to identify `Γ(U, 𝓕)` with
     `Γ(ε(U), ε^*𝓕)`.  There is nothing to generalize here: the predicate it discharges,
     `AlgebraicGeometry.SmallEtale.UnitIsoOnQuasicoherent`, is by definition quantified over the
     full subcategory of quasi-coherent modules, and even *monomorphy* of the unit is proved
     only there (`mono_unit_app_associatedModuleAdjunction`).

   So this route cannot be freed of the hypothesis; the general converse needs a different
   one, and it is the source's.  Stacks factors `ε^*` as `ε⁻¹` followed by extension of scalars
   along `ε⁻¹𝒪_S ⟶ 𝒪`, which is the same factorization that freed zero-detection — and in this
   development that factorization is free, `toZariskiModulePullback` being
   `inverseImageModules ⋙ extendScalarsFSharp` by `rfl`.  Along it the general converse needs two
   local descriptions of sections, **both of which are proved**, and then an assembly, which is
   not:

   * **Proved.** `AlgebraicGeometry.SmallEtale.exists_sieve_imageOpen_section`
     (`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/`
     `SmallEtaleImageOpenSurjective.lean`):
     a section of `ε⁻¹F` over an object `V` of the small étale site is, on a covering sieve of
     `V`, the image of a section of `F` over the **image open** `im V` — which is an open because
     étale morphisms are open (Stacks 03WT).  This is the step of the source's proof that produces
     the `tᵢ ∈ 𝓕(U)`, `U` being that image open.  Only the *injective* half of the same comparison
     was named before (`injective_toSheafify_imageOpenPresheaf`), because zero-detection needs
     sections only to be separated.  It is stated for a sheaf of *sets*; the identification it is
     read through on the module side is that the inverse image of a sheaf of modules has the same
     sections as the inverse image of its underlying sheaf of sets, which is
     `Stacks.Sheaves.ToposPullback.pullbackModuleAb` holding those sections by definition and is
     the device `AlgebraicGeometry.SmallEtale.isZero_of_isZero_inverseImageModules` already runs
     on.
   * **Proved.** The elementary-tensor half:
     `Stacks.Sheaves.RingedToposModules.exists_sieve_changeOfRings_section`
     (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ExtendScalarsLocalSections.lean`) — a section
     of `Stacks.Sheaves.RingedToposModules.extendScalars` over `V` is, on a covering sieve of `V`,
     the image of a section of the *sectionwise* tensor product `A₂(W) ⊗_{A₁(W)} L(W)`, and such a
     section is a finite sum of elementary tensors by the construction of the tensor product.
     `extendScalars` is `changeOfRings` followed by `PresheafOfModules.sheafification`
     (`forget_map_extendRestrictScalarsAdjunction_unit_app`) and the sheafification unit is
     locally surjective; the content of the statement is having that said at the `extendScalars`
     spelling, where instance search does not find it.  Note that every
     `extendScalars`-and-generation lemma in the tree
     (`extendScalars_exists_finite_generators`, `extendScalars_isLocallyGeneratedBy`,
     `generatingSections_leftAdjoint_restrictScalars`) is left-adjoint formal nonsense and
     preserves only; this one is not about generation at all.
   * **Missing.** The assembly: a *common* open over which finitely many of the resulting `tᵢ`
     generate, and then epimorphy of `𝒪_U^{⊕N} ⟶ 𝓕|_U` from epimorphy of its image under `ε^*`.
     The last step is the only one already hypothesis-free, by
     `AlgebraicGeometry.SmallEtale.reflectsEpimorphisms_associatedModule`.

   Note that the faithful-flatness input of the
   factorization is proved and unconditional
   (`AlgebraicGeometry.SmallEtale.locallyFaithfullyFlat_imageSectionsRestriction`) and that the
   commutative-algebra half of flat descent of finiteness is available at full strength —
   Mathlib's `Module.Finite.of_finite_tensorProduct_of_faithfullyFlat` and this development's
   `Stacks.finite_of_finite_extendScalars`.  What `LocallyFaithfullyFlat` has no lemma about is
   descending *generation*: its entire payload in the library is injectivity of the unit, hence
   zero-detection.

   The **derived-level** form of this step — the one the induction actually applies, which takes
   the finite-type conclusion that step 2 produces on the *étale* side at `Hⁿ(ε^*E)` and returns
   it on the Zariski side at `Hⁿ(E)` — is proved in
   `StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/`
   `SmallEtaleDerivedFiniteTypeDescent.lean`
   as
   `SmallEtale.isFiniteTypeOnSite_homology_of_isFiniteTypeOnSite_homology_associatedModule`
   and, in the `SheafOfModules.IsFiniteType` spelling that Stacks 08FX produces and the
   induction consumes,
   `AlgebraicGeometry.SmallEtale.isFiniteType_homology_of_isFiniteType_homology_associatedModule`.
   Its one further input is the iso-invariance of clause (5) of Stacks 03DL, needed to cross
   `CategoryTheory.Functor.mapDerivedCategoryHomologyIso` at `ε^*` (`Hⁿ(ε^*E) ≅ ε^*(Hⁿ(E))`); that
   is `Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_of_iso`
   (`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedFiniteTypeOnCharts.lean`), beside
   `hasFiniteGlobalGenerators_of_iso`, which it is built from.  Both derived-level
   statements carry the quasi-coherence of `Hⁿ(E)` as a hypothesis, for the same reason as the
   module-level one, and neither carries a tag.
4. **The local lift of a surjection `𝒪_S^{⊕t} → H^n(E)` to a map of complexes
   `𝒪_S^{⊕t}[-n] → E`.**  **Available at an affine chart**, as
   `AlgebraicGeometry.exists_lift_truncGEπ_zero_cofan_of_isAffineOpen`
   (`StacksFrontier/AlgebraicGeometry/Cohomology/AffineOpenTruncationLift.lean`); the source omits
   its details.  The nearest machinery in the library lifts *through* a strictly perfect
   approximation rather than *into* `E` — `RingedSite.exists_coveringSieve_lift_homotopy_general`
   (Stacks 08FQ) — and is not what is used.  This step needs three
   things, and all three are available and composed.

   * **The edge map, and the obstruction it carries.**  For `E` in `D^{≤n}` the obstruction to
     lifting a global section of `Hⁿ(E)` over `U` to a hypercohomology class is the edge map
     `Hⁿ(RΓ(U, E)) → H⁰(U, Hⁿ(E))` of the hypercohomology spectral sequence, whose image is the
     subgroup `E_∞^{0,n}`; in general the lift exists only after shrinking `U`.  **At an affine
     chart with quasi-coherent cohomology nothing is shrunk**: the edge map is an *isomorphism*
     there, by `AlgebraicGeometry.isIso_hypercohomologyEdge_app_of_isAffineOpen`
     (`StacksFrontier/AlgebraicGeometry/Cohomology/AffineOpenHypercohomologyEdge.lean`), which is
     Stacks 0BKZ at the basis of affine opens with its two hypotheses discharged — enough
     objects from `AlgebraicGeometry.Scheme.isBasis_affineOpens`, and Serre vanishing
     (Stacks 01XB) from
     `AlgebraicGeometry.isZero_rightDerived_evaluation_homologyFunctor_of_isAffineOpen`.  That
     statement is about the edge morphism
     `Stacks.Cohomology.HypercohomologyEdge.hypercohomologyEdge`, built from the sheafification
     unit, and not about
     `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedHomologyComparison`, built
     from the universal property of a right derived functor: the two have the same type, the
     library identifies them nowhere, and only the first carries Stacks 0BKZ.

     **The affineness of the chart is irreducible, and that is demonstrated rather than
     asserted.**  It enters step 4 at exactly one point — Serre vanishing, Stacks 01XB, in the
     form `AlgebraicGeometry.isZero_rightDerived_evaluation_of_isAffineOpen`, which is what
     `AlgebraicGeometry.isIso_hypercohomologyEdge_app_of_isAffineOpen` consumes and hence what
     `AlgebraicGeometry.isZero_homology_derivedSectionsOverObject_of_isAffineOpen` and the two
     `Subsingleton` forms beside it rest on; nothing else in step 4 uses it, and the
     hypothesis-free *statement* of the lift elaborates perfectly well.  But that vanishing cannot
     be had at a general chart: for `U` quasi-compact, the vanishing of the degree-one right
     derived functor of `SheafOfModules.evaluation` at every quasi-coherent module **implies that
     `U` is affine**, by the Serre criterion of Stacks 01XF,
     `Stacks.SerreCriterion.isAffine_of_forall_isZero_H1_ideal`
     (`StacksFrontier/AlgebraicGeometry/SerreAffinenessCriterion/VanishingCriterion.lean`), whose
     hypothesis is that vanishing on the ideal subobjects alone.  So dropping the hypothesis from
     the vanishing step would prove every quasi-compact scheme affine.  Step 4 is therefore
     *correctly* stated at an affine chart, and "step 4 at all charts" is not a thing to build:
     what carries the conclusion to all charts is the locality reduction of Stacks 08FU (3) read
     through the slice identification, item 2 of the list below.  (In particular
     `AlgebraicGeometry.SmallAffineEtale.inclusion_isSpecialCocontinuous`, the
     affine-charts-to-all-charts route used elsewhere in this development, does **not** apply:
     it is about the small affine étale subsite of the small étale site, not the Zariski site of
     a scheme, and what it gives is an equivalence of sheaf topoi — which transports sheaves and
     says nothing about whether a hypercohomology group vanishes at a non-affine open.  Its
     Zariski analogue `AlgebraicGeometry.SmallAffineZariski.inclusion_isSpecialCocontinuous` is
     in the tree and is no more use here for the same reason.)
   * **The truncation half.**  **Available.**  The distinguished triangle
     `τ^{<n}E ⟶ E ⟶ τ^{≥n}E ⟶ (τ^{<n}E)[1]` is Mathlib's
     `CategoryTheory.Triangulated.TStructure.triangleLTGE` with `triangleLTGE_distinguished`;
     the identification of `τ^{≥n}E` with `Hⁿ(E)` placed in degree `n`, for `E` in `D^{≤n}`, is
     this development's `DerivedCategory.truncGELTIsoHomologyFunctorCompSingleFunctor`
     (`StacksFrontier/Algebra/Homology/DerivedCategory/TruncGELTSingle.lean`) read through
     `CategoryTheory.Triangulated.TStructure.isLE_iff_isIso_truncLTι_app`; and the factorization
     of a map whose composite with the connecting map vanishes is Mathlib's
     `CategoryTheory.Pretriangulated.Triangle.coyoneda_exact₃`.  Turning the derived lift back
     into the chain map that `AlgebraicGeometry.RingedSite.IsPseudoCoherentComplexFrom` asks for
     is `AlgebraicGeometry.RingedSite.exists_coveringSieve_complexMap` (Stacks 08FR part (1)),
     which is stated at module universe `0`.
   * **The Hom computation.**  **Available**, for one copy of the unit.  Turning a
     hypercohomology class into a morphism of the derived category needs
     `Hom_{D(𝒪)}(𝒪^{⊕t}[-n], E) ≅ Hⁿ(RΓ(U, E))^{⊕t}`; apart from this, **no statement
     in this development computes derived Hom out of the unit module, or out of a finite free
     module, as hypercohomology** — the `free`-versus-sections material that exists,
     `Stacks.Cohomology.FreeYoneda.sectionsAddEquiv` and
     `Stacks.Cohomology.FreeYoneda.cohomologyPresheafIsoSections`
     (`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedSections/FreeYonedaSections.lean`),
     being about abelian sheaf cohomology and not about `SheafOfModules` derived Hom, and
     `SheafOfModules.liftPow` and `SheafOfModules.powMk` being module-level.

     It is
     `Stacks.Sites.ExtensionByZero.nonempty_homologyDerivedSectionsAddEquiv`
     (`StacksFrontier/CategoryTheory/Sites/Modules/SectionsOverObjectDerivedCategory.lean`):
     `Hⁿ(RΓ(U, E)) ≅ Hom_{D(𝒪)}(j_{U!}𝒪_U, E⟦n⟧)` for every object `E` of `D(𝒪)` on a
     `AlgebraicGeometry.RingedSite.{u, u, u}`, with
     `Stacks.Sites.ExtensionByZero.homologyDerivedSectionsAddEquivOfIsKInjective` the canonical
     brick behind it at a K-injective complex and
     `Stacks.Sites.ExtensionByZero.subsingleton_hom_singleExtensionByZeroUnit_of_isZero` the
     vanishing form the lifting step consumes.  The route taken is **not** the identification of
     two right derived functors of isomorphic functors, which this paragraph used to prescribe:
     the corepresentation of `Γ(U, -)` by `j_{U!}𝒪_U` is already carried through complexes by
     `Stacks.Sites.ExtensionByZero.sectionsOverObjectHomologyAddEquiv`
     (`StacksFrontier/CategoryTheory/Sites/Modules/SectionsOverObjectHomotopyCategory.lean`, over
     Stacks 0G1V in the additive form `coyonedaExtensionByZeroUnitIso`), which identifies
     `Hⁿ(Γ(U, M^•))` with `Hom_{K(𝒪)}((j_{U!}𝒪_U)[0], M^•⟦n⟧)` for an arbitrary complex; evaluating
     it at a K-injective complex turns both sides into derived-category data at once, by
     `Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective` on the left and
     `CochainComplex.IsKInjective.Qh_map_bijective` (Stacks 0A64) on the right.  No `Ext` and no
     uniqueness-of-derived-functors argument is used.  The universe bookkeeping does not arise in
     the case 0DII needs: on `AlgebraicGeometry.Scheme.zariskiRingedSite` the objects, morphisms,
     ring sections and modules all live in one universe `u`.

     The `⊕t` form of the vanishing is
     `Stacks.Sites.ExtensionByZero.subsingleton_hom_cofan_singleExtensionByZeroUnit_of_isZero`,
     out of the universal property of the coproduct, stated at a colimiting
     `CategoryTheory.Limits.Cofan` and an arbitrary index type.

     **The residue of this bullet is discharged.**  The derived sections in it are
     `Stacks.Cohomology.Localization.derivedSectionsOverObject`, valued in `D(Ab)` — the module
     structure is forgotten *before* deriving — whereas the affine edge isomorphism of the first
     bullet is about `Stacks.Cohomology.HypercohomologyEdge.derivedSections`, the right derived
     functor of `SheafOfModules.evaluation` itself, valued in `D(Mod Γ(U, 𝒪))`.  The library
     compared the two nowhere.  It does now:
     `Stacks.Cohomology.HypercohomologyEdge.derivedSectionsForgetModuleIso`, with the degreewise
     form `homologyDerivedSectionsForgetModuleIso` that a consumer actually uses, in
     `StacksFrontier/CategoryTheory/Sites/Cohomology/HypercohomologyEdge/`
     `DerivedSectionsUnderlyingGroups.lean`.
     Forgetting the module structure commutes with the right derived functor because
     `forget₂ (ModuleCat R) AddCommGrpCat` is exact, and the general brick for that was already
     in the tree —
     `Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedMapDerivedCategoryIso`
     (`R(F) ⋙ G.mapDerivedCategory ≅ R(F ⋙ G)` for exact `G`) — so the comparison is that brick
     at `F = SheafOfModules.evaluation` and `G = forget₂`, the composite being
     `Stacks.Cohomology.Localization.sectionsOverObject` by definition.  No analogue of
     `Stacks.Cohomology.ForgetModule.sectionsForgetComparison_isIso` (Stacks 0D6J (2)) had to be
     reproved: that statement compares sheaves of modules with abelian *sheaves* and is a
     different thing.
   **The three bullets are composed.**  The composition is in two files.
   `AlgebraicGeometry.isZero_homology_derivedSectionsOverObject_of_isAffineOpen` and the two
   `Subsingleton` forms beside it
   (`StacksFrontier/AlgebraicGeometry/Cohomology/AffineOpenHypercohomologyVanishing.lean`) read the
   affine edge isomorphism of the first bullet through the comparison just named and feed it to
   the vanishing lemmas of the third, giving: over an affine open, if `Hᵠ(F)` vanishes then every
   morphism `(j_{U!}𝒪_U)^{⊕t} ⟶ F⟦q⟧` of `D(𝒪_S)` is zero.  Then
   `AlgebraicGeometry.exists_lift_truncGEπ_zero_cofan_of_isAffineOpen`
   (`StacksFrontier/AlgebraicGeometry/Cohomology/AffineOpenTruncationLift.lean`) applies that at
   `F = τ^{<0}(E⟦n⟧)`, whose degree-`1` cohomology vanishes because the truncation is `≤ -1`, and
   concludes the lift.  The truncation half is
   `CategoryTheory.Triangulated.TStructure.exists_lift_truncGEπ_of_subsingleton`
   (`StacksFrontier/CategoryTheory/Triangulated/TruncGELift.lean`), which is `coyoneda_exact₃` along
   `TStructure.triangleLTGE`; Mathlib's own one-sided constructors `liftTruncLT` and
   `descTruncGE` do not apply, since they need an amplitude bound on the source rather than a
   vanishing obstruction.  The truncation degree is `0` and the shift is put on `E`, which is why
   no shift of the source coproduct appears.  Quasi-coherence of the cohomology of the truncation,
   which the affine edge isomorphism needs, is
   `AlgebraicGeometry.isQuasicoherent_homology_truncLT`, read off
   `AlgebraicGeometry.isQuasicoherent_homology_truncLE`.

   The identification of `τ^{≥0}(E⟦n⟧)` with `Hⁿ(E)` placed in degree zero, which is what turns a
   surjection `𝒪^{⊕t} → Hⁿ(E)` into the `g` this lift consumes, is **proved**:
   `DerivedCategory.truncGEZeroShiftIsoSingleHomology`
   (`StacksFrontier/Algebra/Homology/DerivedCategory/TruncGEOfIsLESingle.lean`), beside the
   unshifted form `DerivedCategory.truncGEIsoSingleHomologyOfIsLE`.  Both are
   `DerivedCategory.truncGELTIsoHomologyFunctorCompSingleFunctor` read through
   `CategoryTheory.Triangulated.TStructure.isLE_iff_isIso_truncLTι_app`: being `≤ n` is exactly
   what makes `τ^{<n+1}E ⟶ E` invertible, which removes the inner truncation of the one-step
   `τ^{≥q}τ^{<q+1}`.

   The step does not need the chain map that
   `AlgebraicGeometry.RingedSite.IsPseudoCoherentComplexFrom` asks for, namely
   `AlgebraicGeometry.RingedSite.exists_coveringSieve_complexMap` (Stacks 08FR part (1)), which is
   stated at module universe `0`.  This matters, because there is no route to 08FR (1) at a free
   module universe: the induction concludes
   `X.IsPseudoCoherentFrom E m` from the *derived-level* Stacks 08FV, whose own proof does the
   chain-level work internally, and the first vertex of its triangle arrives with a strictly
   perfect representative (see the induction bullet below).  No chain map out of `E` is ever
   needed, so 08FR (1) is not on the critical path for clause (2) ⇒ (1).
5. **Stacks 08FV, two-out-of-three in a distinguished triangle.**  **Available**, at independent
   universes, as
   `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_distinguished_{one,two,three}_general`
   (`StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/DistinguishedTriangles.lean`).

So steps 1, 2 and 5 are available; step 3 is available for a quasi-coherent `𝓕`, at the module
level and at the derived level, and open in general; and step 4 is available at an affine chart,
its three parts composed into a single lifting statement and read out of a finite free module on
an affine scheme.  An affine chart is where step 4 *belongs*: its affineness hypothesis is not a
convenience, and the demonstration of that is in step 4 above.

**What remains**, and in this order:

* the **boundedness** step: `m`-pseudo-coherence together with finite coverings puts `E` in
  `D⁻(𝒪_S)`, which is where the induction on `n - m` starts.  **Available with no proviso on the
  small étale site of a quasi-compact scheme**, as
  `AlgebraicGeometry.SmallEtale.exists_isLE_Q_obj_of_isPseudoCoherentComplexFrom` and its affine
  specialisation `…_of_isAffine`
  (`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleBoundedAbove.lean`), read
  off the general `AlgebraicGeometry.RingedSite.exists_isLE_Q_obj_of_isPseudoCoherentComplexFrom`
  (`StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/BoundedAboveDescent.lean`), which
  still carries the finite-refinement hypothesis explicitly: every covering presieve of the
  starting object admits a finite subfamily still covering the final object.  That proviso is not
  cosmetic — the conclusion is false on the Zariski site of a non-quasi-compact scheme.  Two
  remarks on discharging it, both machine-checked.

  * The route is **not** `Stacks.Sites.exists_finite_flat_refinement` at
    `AlgebraicGeometry.SmallAffineEtale.precoverage`, and not the affine subsite at all.  The
    proviso does not ask the members of the subfamily to be affine, only to be finitely many and
    to lie in the given presieve, so no finite *affine* refinement is needed — which is just as
    well, there being none for the small étale site.  What discharges it is
    `AlgebraicGeometry.SmallEtale.exists_finite_subfamily_coversTop`
    (`StacksFrontier/AlgebraicGeometry/Topologies/Etale/FiniteCoversTopRefinement.lean`): the
    members of a covering presieve of the small étale site are jointly surjective
    (`exists_mem_arrows_mem_range`) and have **open** images — each is étale, hence flat and
    locally of finite presentation, hence universally open — so over a quasi-compact space
    finitely many of them already cover, and a jointly surjective family generates a covering
    sieve (`mem_topology_of_jointlySurjective`).  Over the final object, which the small étale
    site has for every `S` (`SmallEtale.finalIsTerminal`, unlike the affine subsite, which needs
    `S` affine), that is `CoversTop` by `coversTop_iff_of_isTerminal`.  What the proviso costs is
    quasi-compactness of `S`, not affineness.
  * Applying it here needs **two generalities of the general theorem**, without which it could
    not be applied to this site however it was proved.  The small étale ringed site is
    `RingedSite.{u + 1, u, u}`, not `RingedSite.{u, u, u}`, so the site universes are free there
    (the module universe still has to match the universe of the
    ring's sections, because `Stacks.SheafOfModules.isZero_of_coversTop` is stated that way, and
    on this site both are `u`).  And its derived category is a `HasDerivedCategory` hypothesis, as
    in this module, not the *standard* localization model declared as a local instance, which would
    be visible in the statement, where it does not elaborate within the heartbeat budget.

  The two halves of the general proof are as follows.  The per-member half is in
  `StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/BoundedAbove.lean`: a complex with
  finitely many nonzero terms has cohomology vanishing above a degree
  (`CochainComplex.exists_isZero_homologyFunctor_obj_of_finite`, which is the boundedness clause
  of `IsStrictlyPerfect` separated from the direct-summand clause so as to need none of its
  sheafification instances), hence so does the restriction of an `m`-pseudo-coherent complex to
  each member of its witnessing covering
  (`RingedSite.exists_isZero_homology_restrictComplex_of_isPseudoCoherentComplexFrom`),
  and over a **finite** family the degree can be taken uniform
  (`AlgebraicGeometry.RingedSite.exists_bound_isZero_homology_restrictComplex_of_finite`).  The
  descent half is `AlgebraicGeometry.RingedSite.exists_isZero_homology_of_coversTop`, with
  `exists_isLE_Q_obj_of_coversTop` beside it reading the bound as `D⁻`: zero-detection for
  sheaves of modules along a family covering the final object is
  `Stacks.SheafOfModules.isZero_of_coversTop`
  (`StacksFrontier/CategoryTheory/Sites/Cohomology/TorAmplitude/IntervalDescent.lean`), and the
  identification of `Hʲ(E|_V)` with `(HʲE)|_V` needs no named natural isomorphism — the library
  has none — because `CategoryTheory.ShortComplex.mapHomologyIso` at the exact
  `SheafOfModules.overFunctor` suffices objectwise, which is how
  `AlgebraicGeometry.RingedSite.isZero_homology_restrictComplex` and
  `AlgebraicGeometry.RingedSite.isGE_Q_obj_restrictComplex` are already proved.  The descent half
  is stated at `RingedSite.{u, u, u}`, because `isZero_of_coversTop` wants the module sections in
  the universe of the ring's sections; the per-member half keeps the module universe free;
* the **induction assembly** on `n - m`, which is what consumes steps 1–5 and 08FV.  Its **base
  case is available**: if `Hʲ(E)` vanishes for every `j ≥ m` then `E` is `m`-pseudo-coherent, by
  the zero complex, which is strictly perfect.  That is
  `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_isZero_homology`
  (`StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/TrivialRange.lean`), with
  `IsStrictlyPerfect.zero_complex` beside it.  The same fact was already in the tree as
  `isPseudoCoherentFrom_of_isLE` inside
  `StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/DerivedTensorProduct.lean`, but
  `private` and at module universe `0`, which does not reach the Zariski site of a scheme; the
  public form keeps the module universe free and asks for vanishing of the cohomology sheaves
  rather than `DerivedCategory.IsLE`, so it needs nothing of the canonical t-structure.

  The induction needs four further things: the identification of `τ^{≥0}(E⟦n⟧)` with `Hⁿ(E)` in
  degree zero; the production of the surjection `𝒪^{⊕t} → Hⁿ(E)` from the finite-type conclusion
  of step 3; the cohomology of the cone in degrees `≥ n`; and the recursion itself.  **All four are
  available.**

  * The **identification** is `DerivedCategory.truncGEZeroShiftIsoSingleHomology`, named at the end
    of step 4 above.  Read through it, a morphism `φ : 𝒪^{⊕t} ⟶ Hⁿ(E)` of modules becomes the
    morphism `DerivedCategory.singleMapTruncGEZeroShift E n φ` into `τ^{≥0}(E⟦n⟧)` that the lift
    consumes, and `DerivedCategory.epi_homologyMap_singleMapTruncGEZeroShift` says it is epic on
    `H⁰` when `φ` is epic — the single functor in degree zero has `H⁰ ∘ single 0 ≅ 𝟭`.
  * The **surjection** is `SheafOfModules.exists_coversTop_epi_free_of_isFiniteType`
    (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FiniteTypeLocalFreeSurjection.lean`): a module
    of finite type admits, over each member of a family covering the terminal object, an
    epimorphism from a free module on a finite index type.  Its hypothesis is exactly the
    `SheafOfModules.IsFiniteType` that step 3's derived-level statement
    `isFiniteType_homology_of_isFiniteType_homology_associatedModule` produces.  Note the shape of
    the conclusion: the epimorphism is onto the restriction `Hⁿ(E)|_V`, not onto `Hⁿ(E)` — which is
    why the chain below is run through the locality reduction and not on `S` itself.
  * The **cone cohomology** is
    `DerivedCategory.HomologySequence.isZero_homology_obj₃_of_epi_top`
    (`StacksFrontier/Homology/DerivedCategory/PerfectApproximation.lean`) — if the first two
    vertices of a distinguished triangle have no cohomology in degrees `> n` and the first morphism
    is epic on `Hⁿ`, the third vertex has none in any degree `≥ n`.  It is stated for an arbitrary
    abelian category with a derived category, carries no sheaf hypotheses, and substitutes with no
    recovery cost.  `AlgebraicGeometry.RingedSite.exists_distTriang_isZero_homology_obj₃_of_epi`
    is it packaged with `Pretriangulated.distinguished_cocone_triangle`, so that a *morphism* with
    those properties yields the *triangle* the recursion wants.
  * The **recursion** is `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_descentStep`
    (`StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/TopDegreeInduction.lean`).  It
    is stated with the standing hypotheses of the step abstracted into a predicate `P` on objects of
    `D(O)` — in this application `P E` is "`ε^*E` is `m`-pseudo-coherent and the cohomology
    sheaves of `E` are quasi-coherent" — because the step is not a statement about `E` alone and
    `P` has to be carried from `E` to the cone for the recursion to continue.  Given that every
    `E` satisfying `P` with cohomology vanishing above some `n ≥ m` admits a distinguished
    triangle with second vertex `E`, `m`-pseudo-coherent first vertex, and third vertex satisfying
    `P` with no cohomology in degrees `≥ n`, every `E` satisfying `P` with cohomology vanishing
    above some degree is `m`-pseudo-coherent.  The measure is `(n + 1 - m).toNat`, the bottom is
    the base case named above, and each step concludes by Stacks 08FV part (2).

  Two further ingredients the recursion needs are also proved.  The **first vertex** of its triangle
  is `𝒪^{⊕t}` placed in degree `n`, and that it is `m`-pseudo-coherent for every `m` is
  `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_singleFunctor_obj_free`
  (`StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/SingleFreeStrictlyPerfect.lean`),
  through `IsStrictlyPerfect.single_obj` and
  `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_Q_obj_of_isStrictlyPerfect` — the last of
  which existed only as a `private` declaration in
  `StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/Summands.lean` and is recomposed
  there from its public ingredients.  And the **shift bookkeeping** that returns the lift to the
  object is `DerivedCategory.epi_homologyMap_shiftBack_of_lift`: a lift `f : K ⟶ E⟦n⟧` of any `g`
  epic on `H⁰` gives `K⟦-n⟧ ⟶ E` epic on `Hⁿ`, which is the hypothesis the cone computation wants.

  **That the pieces fit is itself checked**, by
  `AlgebraicGeometry.RingedSite.exists_distTriang_free_of_lift`
  (`StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/TopDegreeInductionStep.lean`):
  from `E` in `D^{≤n}`, an epimorphism `φ : 𝒪^{⊕t} ⟶ Hⁿ(E)` with `t` finite, and a lift of
  `singleMapTruncGEZeroShift E n φ` along `E⟦n⟧ ⟶ τ^{≥0}(E⟦n⟧)`, it returns the whole triangle
  datum that `isPseudoCoherentFrom_of_descentStep` asks of its step — distinguished, second vertex
  `E`, first vertex `m`-pseudo-coherent for every `m`, third vertex with no cohomology in degrees
  `≥ n` — apart from `P` of the third vertex, which is not a consequence of the triangle and is
  item 4 of the list below.  So the only inputs the step still lacks are the two geometric ones,
  items 2 and 3.

  **What is left between these pieces and the narrow form 0DII consumes**, in order.  The chain is
  not missing a step of the source's argument; what it is missing is the geometry that puts
  the source's "the question is local, so assume `S` affine" into Lean.

  1. **The locality reduction is available** and is not a gap: Stacks 08FU part (3),
     `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_locally_general`
     (`StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/LocalNature.lean`), at
     independent site, morphism and module universes.  It reduces `X.IsPseudoCoherentFrom E m` to
     `(X.over V).IsPseudoCoherentFrom (E|_V) m` over a covering, which is the right shape: the
     surjection of step 3 is only onto `Hⁿ(E)|_V`.
  2. **The slice of a scheme's Zariski ringed site at an open is that open's Zariski ringed
     site**: this is **proved**, as
     `AlgebraicGeometry.Scheme.zariskiOverRingedSiteHom`
     (`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/ZariskiRingedSiteOpenSlice.lean`) —
     a morphism of ringed sites whose underlying functor is an equivalence of sites and whose
     structure map is the identity.

     The *transport of `IsPseudoCoherentFrom` across it* is **proved** too, in
     `StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/`
     `ZariskiRingedSiteOpenSliceTransport.lean`:
     `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_pushforwardPushforwardEquivalence_inverse`
     moves the predicate along an arbitrary equivalence of ringed sites, and
     `AlgebraicGeometry.Scheme.isPseudoCoherentFrom_zariskiOver_of_toScheme` reads that at the open
     slice.  The capstone is
     `AlgebraicGeometry.Scheme.isPseudoCoherentFrom_zariskiRingedSite_of_locally_toScheme`
     (`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/`
     `ZariskiRingedSiteOpenSliceLocality.lean`): pseudo-coherence on a scheme is local on open
     subschemes, with nothing transported appearing in either the hypothesis or the conclusion.  So
     the affine-chart statements can now be fed to the locality reduction, and that join is
     machine-checked rather than asserted.

     Two spellings are reconciled rather than duplicated.  Mathlib's own
     `AlgebraicGeometry.Scheme.Modules.overEquiv` *is* the `F` the engine wants, by `rfl`
     (`AlgebraicGeometry.Scheme.zariskiOver_modulesEquiv`), once the orientation is fixed: the
     engine's `F` runs `Mod(𝒪_V) ⥤ Mod(𝒪_X|_V)`, so the site equivalence it wants is
     `(Opens.overEquivalence V).symm`, which is exactly Mathlib's choice.  In that orientation
     Mathlib's `φ` is `𝟙` by `rfl` and H₁ is `rfl`, and H₂ comes free from
     `Stacks.SheafOfModules.InternalHom.unit_of_counit` — the inverse structure map being unique
     (`psiOfIso_eq`).  Keeping Mathlib's `ψ` as *data* and deriving the propositions is what avoids
     a second equivalence between the same two module categories; replacing `ψ` by `psiOfIso`
     instead is what breaks the `rfl`, since `psiOfIso` inverts through `CategoryTheory.inv`, and
     that spelling is reconciled separately as `zariskiOverPsi_eq_psiOfIso`.

     The *other* conjunct of `P` across the slice is **proved** too, in
     `StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/`
     `ZariskiRingedSiteOpenSliceQuasicoherent.lean`:
     `AlgebraicGeometry.Scheme.isQuasicoherent_homology_modulesOverEquiv_overFunctor` carries
     quasi-coherence of `Hʲ(E)` to quasi-coherence of `Hʲ` of the reading of `E|_V` as a complex of
     `𝒪_V`-modules — the very object the capstone's hypothesis is about — so both conjuncts of `P`
     now meet on one object over each member of the covering.  This is a different statement from
     the cone propagation of item 4, which is about the cone of the induction's triangle and not
     about the slice identification.
     `Scheme.isPseudoCoherentFrom_zariskiRingedSite_of_locally_toScheme_quasicoherent`
     is the capstone with the local hypothesis weakened accordingly: over `V` the quasi-coherence
     conjunct may be *assumed*, because it is discharged from the corresponding assumption on `E`.
     The capstone itself is unchanged — the obligation is discharged, not moved.

     Nothing of quasi-coherence is reproved there.  Mathlib already identifies the composite
     `SheafOfModules.overFunctor X.ringCatSheaf V ⋙ (Scheme.Modules.overEquiv V).functor` with
     `AlgebraicGeometry.Scheme.Modules.restrictFunctor V.ι`
     (`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`), and restriction along an open immersion
     preserves quasi-coherence (`Scheme.Modules.isQuasicoherent_restrictFunctor`); the passage from
     modules to the derived category is `mapDerivedCategoryCompHomologyFunctorIso` at the two
     functors, both exact.  The two private near-misses in the tree are no use: the pair
     `overRestrictIso`/`overRestrictFunctor` in
     `StacksFrontier/AlgebraicGeometry/Scheme/FunctorialityQuasiCoherent/Basic.lean` is `private`,
     and `isQuasicoherent_over_of_restrict` is not in the library.

     **Running the induction on `V.toScheme`.**  Instantiating the ε-side machinery
     at the open subscheme is free; what is *not* in the tree is a statement restricting the
     ε-conjunct of `P` from `X` to `V`, and that is the missing step.

     Free: every ε-side file takes `(B : BigEtaleSite) (S : Scheme) (hS : B.Contains S)` with `S`
     an *ordinary parameter* and no affineness, noetherian or separatedness hypothesis anywhere on
     the path, and the big site containing `X` contains every open subscheme of it —
     `AlgebraicGeometry.BigEtaleOver.contains_opens`, which is `Scheme.size_lt_of_isOpenImmersion`,
     Stacks 000R (3).  So `AlgebraicGeometry.SmallEtale.AssociatedModuleToPseudoCoherent`
     elaborates at `V.toScheme`, applied to exactly the transported restriction the capstone hands
     over; this is machine-checked.  The structure map, the associated-module functor, its
     additivity and both exactness instances, and the unit comparison `ε_V^*𝒪_V ≅ 𝒪` are all
     instances at an arbitrary `(B, S, hS)`.  No universe shifts: `V.toScheme : Scheme.{u}`, so the
     étale site at `V` is again `RingedSite.{u + 1, u, u}` with sections in `Type u`.  What is owed
     is one further `HasDerivedCategory` binder, as a family over `V : X.Opens`, for
     `SheafOfModules.{u} (structureSheaf B V.toScheme _)` — the étale site's objects live in
     `Type (u + 1)`, so the global `SheafOfModules.hasDerivedCategory` does not fire, exactly as at
     `X` — together with the four sheafify and `WEqualsLocallyBijective` hypotheses of
     `isPseudoCoherentFrom_of_descentStep` at `V.toScheme.zariskiRingedSite` and its slices, which
     are `hasSheafifyEssentiallySmallSite` and
     `GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall` one-liners.  (Note that
     `isPseudoCoherentFrom_of_descentStep` has not been *applied* anywhere yet, at `X` or at `V`;
     those four are owed at either.)

     Not free: quasi-compactness.  The boundedness bullet above costs it, and an open subscheme of
     a quasi-compact scheme need not be quasi-compact; but the capstone lets the covering be
     chosen, `AlgebraicGeometry.Scheme.affineZeroHypercover_sieve₀_mem`
     (`StacksFrontier/AlgebraicGeometry/Cohomology/TruncationTowerInput.lean`) covers every open of
     a scheme by the affine opens below it, and `SmallEtaleBoundedAbove.lean` has the `[IsAffine S]`
     form beside the quasi-compact one.  That is also what step 4 wants, it being stated at an
     affine chart.

     **The one piece of real work left here** is the ε-conjunct across the slice:
     `IsPseudoCoherentFromSmallEtale B X hX E m` to
     `IsPseudoCoherentFromSmallEtale B V.toScheme _ (E|_V) m`.  Nothing restricts that predicate
     today — it occurs only in `SmallEtaleConePropagation.lean` and
     `SmallEtaleConePropagationQuasicoherent.lean`.  All four ingredients are available: 08FU (3) in
     the restricting direction at free universes
     (`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_derivedRestriction`, written so as to
     reach a `RingedSite.{u + 1, u, u}`); the crossover `X_étale/V ≅ V_étale` as an equivalence of
     ringed sites *on the nose*, `AlgebraicGeometry.SmallEtale.reindexRing_localizationEquivalence`
     by `rfl`, which is the shape
     `isPseudoCoherentFrom_pushforwardPushforwardEquivalence_inverse` consumes; the module-level
     comparison `(f^*𝓕)^a ≅ (𝓕^a)|_{Y_étale}`,
     `AlgebraicGeometry.SmallEtale.associatedModuleObjRestrictIso`, with the open-specific
     `associatedModuleOverIso` beside it; and the derived-level lift of such a comparison, which is
     the pattern of the quasi-coherence transport above.  So it is one file of the size of
     `ZariskiRingedSiteOpenSliceQuasicoherent.lean` and no new mathematics — but it is not written,
     and until it is, only the quasi-coherence conjunct crosses the slice.
  3. **`j_{⊤!}𝒪 ≅ 𝒪`**: this is **proved**, in
     `StacksFrontier/CategoryTheory/Sites/Modules/ExtensionByZeroUnitAtTerminal.lean` and
     `StacksFrontier/CategoryTheory/Sites/Modules/SingleExtensionByZeroUnitFreeCofan.lean`, and
     composed with the affine-chart lift in
     `AlgebraicGeometry.exists_lift_truncGEπ_zero_single_free_of_isAffineOpen_top`
     (`StacksFrontier/AlgebraicGeometry/Cohomology/AffineSchemeTruncationLiftFree.lean`): on a
     scheme whose total space is an affine open, a morphism out of `𝒪^{⊕ι}[0]` into `τ^{≥0}F` lifts
     with nothing shrunk.
  4. **The propagation of `P` to the cone on the étale side is available**; the quasi-coherence
     conjunct of `P` on the cone is not.  `ε^*` is exact, so it carries the triangle
     `𝒪^{⊕t}[-n] ⟶ E ⟶ C` to a distinguished triangle, `ε^*(𝒪^{⊕t}[-n])` is strictly perfect, and
     Stacks 08FV part (1) then makes `ε^*C` `m`-pseudo-coherent.  That composition is proved,
     in two files.

     `StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/`
     `ConePropagationAlongAnExactFunctor.lean`
     has it for an arbitrary exact additive `F : Mod(O) ⥤ Mod(O')` carrying the unit to the unit,
     at independent object and morphism universes:
     `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_mapDerivedCategory_obj₃_of_distinguished`
     is Stacks 08FV part (1) read through `F` — `CategoryTheory.Functor.mapDerivedCategory` of an
     exact functor carries `CategoryTheory.Functor.IsTriangulated`, so Mathlib's
     `CategoryTheory.Functor.map_distinguished` supplies the triangle and no triangulated
     structure has to be built — and
     `AlgebraicGeometry.RingedSite.exists_distTriang_free_of_lift_mapDerivedCategory` is
     `exists_distTriang_free_of_lift` with that conclusion added, i.e. the whole triangle datum
     the recursion asks of its step with the `F`-half of `P` discharged on the third vertex.
     Strict perfectness of the image of the first
     vertex is **not** carried by Stacks 08H3
     (`AlgebraicGeometry.RingedToposHom.isStrictlyPerfect_pullbackModules`), whose hypothesis is a
     `AlgebraicGeometry.RingedToposHom` and which therefore does not apply to a bare functor, but
     by `SheafOfModules.isStrictlyPerfect_map`, which is what 08H3 itself is proved from.

     `StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleConePropagation.lean`
     reads those at `ε`, as `SmallEtale.isPseudoCoherentFromSmallEtale_obj₃_of_distinguished`
     and `AlgebraicGeometry.SmallEtale.exists_distTriang_free_of_lift_smallEtale`, whose
     conclusions are literally
     `AlgebraicGeometry.SmallEtale.IsPseudoCoherentFromSmallEtale` of the third vertex.  The unit
     comparison `ε^*𝒪_S ≅ 𝒪` they need is `SmallEtale.associatedModuleRingSheafUnitIso`,
     `SheafOfModules.pullbackObjUnitToUnit` of `AlgebraicGeometry.SmallEtale.structureMap` — the
     associated-module functor of Stacks 03DU (4) *is* a `SheafOfModules.pullback`, and that map
     is an isomorphism because the underlying functor of sites is final.  The three functor-level
     typeclass hypotheses are passed explicitly there, for the reason recorded at
     `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_mapDerivedCategory_of_hypotheses`.

     The *other* conjunct of `P` — that the cohomology sheaves of the cone are quasi-coherent — is
     **proved** as well, and **unconditionally**:
     `AlgebraicGeometry.isQuasicoherent_homology_obj₃_of_distinguished_zariskiRingedSite`
     (`StacksFrontier/AlgebraicGeometry/PseudoCoherent/QuasicoherentConePropagation.lean`), with the
     general triangle form in
     `StacksFrontier/Algebra/Homology/DerivedCategory/SerreSubcategoryCone.lean` and the fused datum
     carrying *both* conjuncts in
     `AlgebraicGeometry.SmallEtale.exists_distTriang_free_of_lift_smallEtale_quasicoherent`
     (`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/`
     `SmallEtaleConePropagationQuasicoherent.lean`).  It needed no hypothesis at the induction
     site: the triangle lemma asks for quasi-coherence at the two other vertices, and on the
     induction step's triangle the first vertex is `𝒪_S^{⊕t}` in a single degree, whose cohomology
     is quasi-coherent for free.

     Two things are worth recording about it.  The closure property
     `Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre` did suffice, but
     the long exact sequence did not have to be assembled:
     `derivedCategoryB_mem_obj₂_of_distinguished` already reads a weak Serre subcategory along a
     triangle at the *middle* vertex, and the cone form is that statement applied to `T.rotate`.
     And a triangle bound existentially cannot be conjoined with another — two theorems each
     producing "some" triangle never give the one
     triangle the recursion needs — so the fused datum additionally exports
     `Nonempty (T.obj₁ ≅ 𝒪_S^{⊕t}[n])`, a strengthening, which is what makes it reusable.
  5. The **finite-refinement proviso** of the boundedness step is **discharged**; see the
     boundedness bullet above for the route.  It is an explicit hypothesis of
     `AlgebraicGeometry.RingedSite.exists_isLE_Q_obj_of_isPseudoCoherentComplexFrom`, and it is
     removed at the small étale site of a quasi-compact scheme by
     `AlgebraicGeometry.SmallEtale.exists_isLE_Q_obj_of_isPseudoCoherentComplexFrom`.
  6. Not needed: `exists_coveringSieve_complexMap`
     (Stacks 08FR (1)) at a free module universe.  See the end of step 4.

## References

* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08H3](https://stacks.math.columbia.edu/tag/08H3)
* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)

## A second analysis of clause (2) ⇒ (1)

This section is a second, independent account of the same obligation; it is not reconciled with
the sections above.

`PseudoCoherentToAssociatedModule` is discharged **unconditionally** by
`AlgebraicGeometry.SmallEtale.pseudoCoherentToAssociatedModule_of_slice_exact`, which carries the
`@[stacks 08HE]` attribute for clause (1) ⇒ (2).  It is not conditional on left exactness of the
pullback along the slice structure map, despite the name of the theorem.  Its statement carries no
hypothesis beyond the two derived-category models: the `_of_slice_exact` in the name refers to
`AlgebraicGeometry.SmallEtale.preservesFiniteLimits_pullback_sliceStructureMap`, which is a
**theorem proved in that same file**, not a hypothesis of the one that consumes it.

Clause (2) ⇒ (1), and hence `PseudoCoherentIffAssociatedModule`, remains unproved.  What it is
reduced to, and what of that is now available, is recorded in the next section.

## Clause (2) ⇒ (1): what it is reduced to

The proof of the converse is the induction of Stacks 09VA on the *cohomological gap*: given that
`H^j E` vanishes above `m + k` and that `ε^*E` is `m`-pseudo-coherent, one finds locally a
strictly perfect complex concentrated in the top degree mapping to `E`, whose cone has gap
`k - 1`, and recurses.  Three inputs of that induction are available, two of them proved for the
purpose:

* **The base case.**
  `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_Q_of_isFiniteType_homology_general`
  (`StacksFrontier/AlgebraicGeometry/PseudoCoherentSites/CyclesLiftGeneral.lean`): finite type of
  `H^p` plus vanishing above `p` gives `p`-pseudo-coherence, on any ringed site.
* **The reduction "we may assume `E` is bounded above", which is what produces the natural number
  the induction runs on.**
  `AlgebraicGeometry.SmallEtale.boundedOpens_mem_grothendieckTopology`
  (`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleSliceBoundedAbove.lean`):
  the opens of `S` carrying a bound on the top nonvanishing degree of `E` cover every open of
  `S`.  It rests on
  `AlgebraicGeometry.SmallEtale.isZero_over_of_isZero_over_associatedModule`
  (`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleSliceConservativity.lean`),
  the **localization to a Zariski slice of the zero-detection assertion of Stacks 08H8**.
* **Taking pseudo-coherence apart.**
  `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_derivedRestriction`
  (`StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/Restriction.lean`), Stacks 08FU
  (3) at independent universes, which is what carries clause (2) from `S` to a slice.

**Two inputs are missing**, and they are the whole of what is left.

1. *Finite type descends along `ε` on a Zariski slice*: for an open `V` of `S` and an
   `𝒪_S`-module `𝓕`, finite type of `(ε^*𝓕)|_{ε(V)}` should give finite type of `𝓕|_V`.  This is
   the localization of Stacks 08HD (2) ⇒ (1),
   `AlgebraicGeometry.SmallEtale.isFiniteTypeOnSite_of_associatedModule`, to a slice.  Unlike the
   zero-detection assertion it does **not** follow formally from the global statement — a
   monomorphism does not carry finite type to its source — so it has to be obtained by re-running
   the geometric argument of 08HD with the opens restricted to those below `V`; every input of
   that argument (`AlgebraicGeometry.SmallEtale.exists_imageOpen_generates`,
   `exists_mem_arrows_mem_range`, `imageOpen_le_imageOpen`) is public and applies verbatim, the
   image open of an étale object over `ε(V)` being automatically an open below `V`.
2. *A form of the induction hypothesis that is stable under passing to a slice.*  The induction
   cannot change the ambient site the way the fppf descent of Stacks 09UF
   (`StacksFrontier/AlgebraicGeometry/PseudoCoherent/FppfDescent.lean`) changes the scheme: the
   cone whose gap has dropped lives on a slice, and
   `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_locally_general` asks for
   pseudo-coherence on the slices of whichever ringed site is ambient.  So the induction has to
   run on a pair of ringed sites together with the comparison functor and its slice factors —
   the data of
   `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_mapDerivedCategory_of_hypotheses`,
   *plus* the reflection property of item 1 at every slice — and that bundle has to be closed
   under slicing.  Closure is possible: slices of slices are depth-one slices again, through
   `CategoryTheory.Over.iteratedSliceEquiv` and `Stacks.SheafOfModules.sliceEquiv`, and the
   universes match because a ringed site of the shape `RingedSite.{max a b, b, w}` has its
   slices of that shape again.  Both the small Zariski ringed site (`RingedSite.{u, u, u}`) and
   the small étale ringed site (`RingedSite.{u + 1, u, u}`) are of that shape.

-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u d d'

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  [HasDerivedCategory.{d}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (structureSheaf B S hS))]
  (E : DerivedCategory
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)))
  (m : ℤ)

/-- **Clause (1) of Stacks 08HE**: the object `E` of `D(𝒪_S)` is `m`-pseudo-coherent, in the
sense of Stacks 08FT part (3) on the small Zariski ringed site of `S`. -/
public abbrev IsPseudoCoherentFromZariski : Prop :=
  S.zariskiRingedSite.IsPseudoCoherentFrom E m

/-- **Clause (2) of Stacks 08HE**: the pullback `ε^*E` of `E` along the morphism of ringed sites
`ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` of Stacks 08H7 is `m`-pseudo-coherent on the small étale site
of `S`.

The derived functor is `CategoryTheory.Functor.mapDerivedCategory` of the associated-module
functor of Stacks 03DU (4), which exists because that functor is additive, right exact and — by
the exactness assertion of Stacks 08H8,
`AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModuleOfSheaf` — left exact.  This
is the sense in which `ε` "is flat hence defines a pullback on complexes of modules". -/
public abbrev IsPseudoCoherentFromSmallEtale : Prop :=
  (smallEtaleRingedSite B S hS).IsPseudoCoherentFrom
    ((@Functor.mapDerivedCategory.{d, d'}
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O))
      _ _ inferInstance (SheafOfModules.{u} (structureSheaf B S hS)) _ _ inferInstance
      (associatedModuleOfSheaf B S hS)
      (inferInstance : (associatedModuleOfSheaf B S hS).Additive)
      (inferInstance : PreservesFiniteLimits (associatedModuleOfSheaf B S hS))
      (inferInstance : PreservesFiniteColimits (associatedModuleOfSheaf B S hS))).obj E) m

/-- **Stacks 08HE**, as a proposition: `E` is `m`-pseudo-coherent on the small Zariski site of `S`
if and only if `ε^*E` is `m`-pseudo-coherent on the small étale site.

This is not proved: its forward half is, and its converse half
`AlgebraicGeometry.SmallEtale.AssociatedModuleToPseudoCoherent` is not.  It is written out so
that the obligation is a checkable Lean statement; see the module documentation for what each
implication needs. -/
public def PseudoCoherentIffAssociatedModule : Prop :=
  IsPseudoCoherentFromZariski S E m ↔ IsPseudoCoherentFromSmallEtale B S hS E m

/-- **The implication (1) ⇒ (2) of Stacks 08HE**, as a proposition: if `E` is `m`-pseudo-coherent
then so is `ε^*E`.

This proposition is proved, with no hypothesis, by
`AlgebraicGeometry.SmallEtale.pseudoCoherentToAssociatedModule_of_slice_exact`; it is the
direction whose proof in the source pulls a local strictly perfect approximation back along `ε`,
and the comparison that transport needs is named in the module documentation. -/
public def PseudoCoherentToAssociatedModule : Prop :=
  IsPseudoCoherentFromZariski S E m → IsPseudoCoherentFromSmallEtale B S hS E m

/-- **The implication (2) ⇒ (1) of Stacks 08HE**, as a proposition: if `ε^*E` is
`m`-pseudo-coherent then so is `E`.

This proposition is proved, with no hypothesis, by
`AlgebraicGeometry.SmallEtale.associatedModuleToPseudoCoherent`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtalePseudoCoherentDescent.lean`),
which discharges the derived-category models of the slices by
`CategoryTheory.HasDerivedCategory.standard`; those models are a device of its proof and not
part of this statement. -/
public def AssociatedModuleToPseudoCoherent : Prop :=
  IsPseudoCoherentFromSmallEtale B S hS E m → IsPseudoCoherentFromZariski S E m

/-- The equivalence of Stacks 08HE is exactly its two implications: nothing further is needed to
assemble them.  This is bookkeeping, and it is recorded so that the two obligations above are
visibly the whole of the tag. -/
public theorem pseudoCoherentIff_of_imp
    (h₁ : PseudoCoherentToAssociatedModule B S hS E m)
    (h₂ : AssociatedModuleToPseudoCoherent B S hS E m) :
    PseudoCoherentIffAssociatedModule B S hS E m :=
  ⟨h₁, h₂⟩

end AlgebraicGeometry.SmallEtale

end
