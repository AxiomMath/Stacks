module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceMiddleExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceMiddleExactnessAt
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceSplitting
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 05ZB: the conormal sequence of an immersion with a left inverse is split exact

Let `i : Z ⟶ X` be an immersion of algebraic spaces over an algebraic space `Bb`, with structure
morphism `b : X ⟶ Bb`.  Stacks 05ZA attaches to it the canonical sequence
```
  0 ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/Bb} ⟶ Ω_{Z/Bb} ⟶ 0
```
and Stacks 05ZB says that if `i` (étale locally) has a left inverse over `Bb`, that sequence is
(étale locally) **split exact**.

Both halves of that conclusion are available separately: exactness is Stacks 05ZA, and the
splitting is `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceSplitting.lean`.  **This file
states the conclusion of Stacks 05ZB as one statement**, globally and étale locally, and records
exactly which clause of it is still open and what it would take.

## The generality: a closed subspace with a left inverse

The two halves are proved at different generalities.  The splitting
(`AlgebraicGeometry.Space.isSplitEpi_pullbackDifferentialsMap_of_retraction`) holds for an
*arbitrary* morphism `i` with a left inverse — splitness of the second arrow uses nothing but the
left inverse.  Exactness (`AlgebraicGeometry.Space.conormalSequence_exact`) is proved for a
**closed subspace** `Z ⊆ X`, which is the case the tag's own proof reduces the immersion case to;
the transport of that clause onto `AlgebraicGeometry.Space.conormalSequenceFirstMapOfImmersion`
over the ambient open of Stacks 04CE is not done.

Both are available at the canonical inclusion of `Z` with every hypothesis discharged, which is
why the two registrations below carry nothing but the tag's own left inverse: exactness has
already been read at the registered first arrow `AlgebraicGeometry.Space.conormalSequenceFirstMap`
in `AlgebraicGeometry.Space.conormalSequence_exact`, and splitness of the second arrow is stated
at `AlgebraicGeometry.Space.pullbackDifferentialsMap`, which does not mention the first arrow at
all — so no transport between the `i^*𝓘` and `𝒞_{Z/X}` spellings arises here, and this file is
checked in seconds.  The implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceMiddleExactness.lean` record what that
transport costs where it does arise.

So the conjunction is stated here at the closed-subspace generality: a closed subspace `Z` of `X`
and a left inverse over `Bb` of its inclusion.  Nothing is weakened by that choice: it is the
exactness clause's own generality, and the alternative — stating the conjunction at an arbitrary
immersion — would have to carry the exactness as a hypothesis, which is the one thing a
registration of this tag must not do.

## Main results

* `AlgebraicGeometry.Space.conormalSequence_splitExact`: **Stacks 05ZB, the global clause,
  unconditionally.**  At a bundled closed subspace whose inclusion has a left inverse over `Bb`,
  the conormal sequence of Stacks 05ZA — written at its registered first arrow
  `AlgebraicGeometry.Space.conormalSequenceFirstMap`, whose source is the conormal module
  `𝒞_{Z/X}` — is exact at its middle term and its second arrow is a split epimorphism.  This is
  where the global clause of the tag is registered.
* `AlgebraicGeometry.Space.conormalSequence_splitExact_of_etale`: **Stacks 05ZB, the étale-local
  clause, unconditionally**, for the restriction along an étale `φ : X' ⟶ X`: the restricted
  sequence is exact at its middle term and its second arrow is a split epimorphism, and so is the
  inverse image along the induced étale `a : Z' ⟶ Z` of the second arrow of the unrestricted
  sequence.  This is where the étale-local clause of the tag is registered.
* `AlgebraicGeometry.Space.conormalSequenceAt_splitExact` and
  `AlgebraicGeometry.Space.conormalSequenceAt_splitExact_of_etale`: the same two statements with
  the inclusions explicit parameters and the kernel of the structure map of each described by the
  hypotheses `hi` and `hker`.  Kept because the étale-local form instantiates the global one at
  the restricted data; the two registrations above discharge all of `hi`, `hker` and `hclosed` at
  the canonical inclusion, from the two halves of
  `AlgebraicGeometry.Space.mem_definingIdealAt_iff`
  (`AlgebraicGeometry.Space.structureSharpKillsDefiningIdeal_subspaceInclusion` and
  `AlgebraicGeometry.Space.structureSharpKernelLeDefiningIdeal_subspaceInclusion`) and part (4)
  of Stacks 02YU (`AlgebraicGeometry.Space.isClosedImmersion_subspaceInclusion`), by way of
  `AlgebraicGeometry.Space.conormalSequence_exact`.
* `AlgebraicGeometry.Space.nonempty_conormalSequence_splitting_iff_mono`: **the exact residue of
  Stacks 05ZB**, with no hypothesis beyond the left inverse.  Under the hypotheses above the
  sequence admits a `CategoryTheory.ShortComplex.Splitting` — Mathlib's full split-exactness, a
  retraction of the first arrow and a section of the second arrow summing to the identity — **if
  and only if** the first arrow is a monomorphism.  So the whole of what is left of this tag is
  the single clause "the first arrow is injective", and nothing else about the splitting is
  missing.  `AlgebraicGeometry.Space.nonempty_conormalSequenceAt_splitting_iff_mono` is the same
  equivalence with the inclusion an explicit parameter.

## What is not proved: injectivity of the first arrow

The `0 ⟶` at the left end of the sequence — that
`AlgebraicGeometry.Space.conormalSequenceFirstMap` is a monomorphism — is **not** proved here
for algebraic spaces, and it is **not** a consequence of the splitting.  That it does not follow
is shown by
`AlgebraicGeometry.Space.nonempty_conormalSequence_splitting_iff_mono` itself: injectivity of
the first arrow is *equivalent* to the full splitting, so it cannot be a consequence of the half
of the splitting that is proved.  Concretely, Mathlib's
`CategoryTheory.ShortComplex.Splitting.ofExactOfSection` takes `Mono S.f` as a hypothesis
alongside the exactness and the section, and that hypothesis is not removable: in any abelian
category take `S.X₁ := M ⊕ N`, `S.X₂ := M`, `S.X₃ := 0`, `S.f` the projection and `S.g := 0`;
the complex is exact at `S.X₂` — the kernel of `S.g` and the image of `S.f` are both all of
`M` — and `S.g` is a split epimorphism, while `S.f` is not a monomorphism.

**For schemes the clause is proved**, with no hypothesis beyond the left inverse:
`Stacks.ConormalSequenceSplit.mono_conormalDifferential_of_retraction` of
`StacksFrontier/AlgebraicGeometry/ConormalSequenceSplit/ShortExact.lean`, and with it the whole of
the scheme analogue of this tag —
`Stacks.ConormalSequenceSplit.conormalShortComplexSplitting_of_retraction` produces a
`CategoryTheory.ShortComplex.Splitting` of the sequence of Stacks 01UZ, and
`Stacks.ConormalSequenceSplit.isIso_conormalDifferential_of_section` is the final assertion of
Stacks 0474.  So the result the source's proof reduces to *is* available here; what is missing is
only its transport to algebraic spaces.  Its proof is stalkwise and rests on
`KaehlerDifferential.kerCotangentToTensor` being injective in the presence of an algebra section
(Stacks 02HP, recorded in full as
`KaehlerDifferential.split_exact_kerCotangentToTensor_mapBaseChange_of_section` of
`StacksFrontier/RingTheory/Kaehler/Basic.lean`), whose own engine is Mathlib's
`Algebra.derivationOfSectionOfKerSqZero`, the derivation `x ↦ x - g (f x)`.

**The étale-localization route — the source's own proof — is open, and every comparison it needs
but one is proved.**  Each of the following is proved here, with no carried hypothesis:

* Stacks 04CS, `AlgebraicGeometry.Space.sheafOfDifferentialsSchemeComparison`
  (`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeTransport.lean`), built from
  `AlgebraicGeometry.Space.schemeDifferentialsIso` and
  `AlgebraicGeometry.SmallEtale.differentialsIso`
  (`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleDifferentialsIso.lean`): for
  a morphism of schemes of the site the spaces-level `Ω` *is* the associated module of the
  scheme-level `Ω`.
* Stacks 04CU on a square of étale charts,
  `AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso`
  (`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsEtaleLocalization.lean`):
  `a^*Ω_{X/Y} ≅ Ω_{U/V}` for étale `a` and `b` with `a ≫ f = ψ ≫ b`.
* Part (1) of Stacks 04G2 at immersion generality,
  `AlgebraicGeometry.Space.conormalModuleOfImmersionRepresentedIso`
  (`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleSchemeAgreementImmersion.lean`): for an
  immersion of schemes of the site the spaces-level conormal module is the associated module of
  `Stacks.Conormal.conormalSheaf`.
* The descent step,
  `AlgebraicGeometry.Space.QuasiCoherentDescent.modulePullback_map_injective_of_isEtaleCovering`
  (`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/HomDescent.lean`), which needs
  only an `IsEtaleCovering` — no quasi-coherence and no surjective scheme chart.

So every *module* in sight is identified with its scheme-level counterpart and monomorphy
descends.  **What is missing is the arrow**, and part of that is now proved.

The scheme-level arrow is `Stacks.ConormalSequenceRight.conormalDifferential`, which
`StacksFrontier/AlgebraicGeometry/ConormalSequenceSplit/ShortExact.lean` reaches through `open`;
`Stacks.ConormalSequenceSplit.mono_conormalDifferential_of_retraction` and
`Stacks.ConormalSequenceSplit.conormalShortComplexSplitting_of_retraction`, named above, are the
statements that live in the splitting namespace itself.

Both arrows are adjoint transposes — the spaces-level one by
`AlgebraicGeometry.Space.submoduleTranspose`, which is *definitionally*
`((modulePullbackAdjunction B S hS f).homEquiv I M).symm`, the scheme-level one by
`(Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).homEquiv _ _).symm`.  So the
first thing an identification of the two arrows needs is that the two **transpositions**
correspond, and that is proved, in two links, in
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModuleHomEquivTransport.lean`:

* `AlgebraicGeometry.SmallEtale.homEquiv_symm_associatedModuleBaseChange`: the Zariski
  transposition of `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction` and the
  small-étale transposition of the two schemes correspond under
  `AlgebraicGeometry.SmallEtale.associatedModule`, over
  `AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso`;
* `AlgebraicGeometry.Space.homEquiv_symm_representedModulePullback`: that small-étale
  transposition and the spaces-level transposition of Stacks 03LU correspond under
  `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`, over
  `AlgebraicGeometry.Space.representedModulePullbackIso`.

Both rest on `Stacks.CategoryTheory.homEquiv_transport`
(`StacksFrontier/CategoryTheory/Adjunction/HomEquivTransport.lean`), which says that for an
isomorphism of the two composite left adjoints round a square of adjunctions the two hom-set
bijections correspond, with the correction being the mate of the conjugate of that isomorphism —
so the correction is determined, not chosen.

**What that leaves, named precisely.**  Three things, in order.

1. The two links meet on the small étale site of the *scheme*, because the second is stated with
   the **inverse** of the identification of sites as its vertical left adjoint: that is the
   direction `AlgebraicGeometry.Space.representedModulePullbackIso` is stated in, and the
   functor-direction isomorphism
   `SheafOfModules.pullback (representedSchemeStructureMapRing B S hS g) ⋙
   (representedSmallEtaleModuleEquivalence B S hS T').functor ≅
   (representedSmallEtaleModuleEquivalence B S hS T).functor ⋙ modulePullback B S hS φ`
   **is proved**, as `AlgebraicGeometry.Space.representedModulePullbackFunctorIso`:
   `AlgebraicGeometry.Space.representedModuleObjPullbackIso` is that statement at one module
   with no naturality, and what closes the gap is
   `AlgebraicGeometry.Space.isIso_representedModulePullbackMate` — the comparison of right
   adjoints attached to `AlgebraicGeometry.Space.representedModulePullbackIso` is invertible,
   the square's two vertical functors being the two halves of an equivalence
   (`Stacks.CategoryTheory.isIso_transportMate`) — after which both sides are left adjoints of
   one functor.  **This step is complete**, in
   `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedAssociatedModuleHomEquivTransport.lean`,
   and the two squares are *not* composed by chaining the two statements above: stacking the
   first square on the second — whose two vertical functors are the two halves of an
   equivalence — gives a single square of adjunctions whose two vertical left adjoints are
   `AlgebraicGeometry.Space.representedAssociatedModule` upstairs and downstairs, so
   `Stacks.CategoryTheory.homEquiv_transport` applies to it directly and nothing has to be
   identified.  Its comparison of the two composite left adjoints is
   `AlgebraicGeometry.Space.schemePullbackRepresentedAssociatedModuleSquareIso`, assembled from
   `AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso` and
   `AlgebraicGeometry.Space.representedModulePullbackFunctorIso`; the correspondence of the two
   transpositions is `AlgebraicGeometry.Space.homEquiv_representedAssociatedModulePullback` and
   `AlgebraicGeometry.Space.homEquiv_symm_representedAssociatedModulePullback`, and of the two
   units `AlgebraicGeometry.Space.unit_representedAssociatedModulePullback`.
   `representedAssociatedModulePullbackIso` is that comparison at one module with no
   naturality, and the two spellings `(BigFppfOver.toScheme B S hS).obj T` and `T.left.obj` of
   the underlying scheme do go together, by `rfl`, with no device needed.

   **Two spellings decide whether the composed statement elaborates.**  The square's two vertical adjunctions have to be *named definitions*: with
   `CategoryTheory.Adjunction.comp` written out underneath the hom-set bijection the statement
   exceeds the heartbeat budget, and introducing the pieces as reducible `abbrev`s exceeds it
   too.  The comparison of right adjoints has to be *written out*: naming it exhausts the
   elaborator's **recursion depth** — not the heartbeat budget — and this development raises
   neither limit.  With both right the module checks in 0.6 s warm.
2. The ideal sheaf read as the Zariski module the transposition is applied to.  **This step is
   proved**, in `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedZariskiDefiningIdeal.lean`.
   What it is *not* is an equality — or an isomorphism — of
   `AlgebraicGeometry.Space.definingIdealSheaf` with a
   `AlgebraicGeometry.Scheme.IdealSheafData`, and the implementation notes of
   `StacksFrontier/AlgebraicGeometry/Spaces/DefiningIdealSheafSubmoduleBridge.lean` explain why
   there could not be one — the two are submodules of the structure sheaves of *different*
   sites.  What there is, built out of the chart-Zariski ideal isomorphisms
   `AlgebraicGeometry.Space.chartZariskiKernelIdealSheafSelfChartIsoIdealSheaf` and
   `AlgebraicGeometry.Space.chartZariskiIdealSheafSelfChartIsoIdealSheaf`
   (`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedChartZariskiIdeal.lean`) and
   `AlgebraicGeometry.Space.representedAssociatedModuleChartZariskiIdealSheafIso`
   (`StacksFrontier/AlgebraicGeometry/Spaces/ChartPushSelfChart.lean`), is the following — all of
   it in the namespace `AlgebraicGeometry.Space`, written without that prefix where the name
   would otherwise not fit on a line.

   * `chartZariskiIdealSheaf_selfChart_kernelIdealSheaf_eq_definingIdealOfHom` — an **equality
     of submodules of `𝒪_V`** with no hypothesis on `j`: the Zariski restriction
     of the spaces-side sheaf of ideals to the identity chart *is*
     `Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom` of the underlying morphism
     of schemes, which is the sheaf of ideals
     `Stacks.ConormalSequenceRight.conormalDifferentialTranspose` is a morphism out of;
     `AlgebraicGeometry.Space.chartZariskiIdealSheaf_selfChart_eq_definingIdealOfHom` is the same
     for the defining ideal sheaf of the closed subspace a represented closed immersion cuts out;
   * `AlgebraicGeometry.Space.representedSmallEtaleRestrictionDefiningIdealSheafIso` — the
     defining ideal sheaf read on the small étale site of the representing scheme *is* the
     associated module of that Zariski ideal sheaf.  This is the spelling the transposition of
     step 1 consumes, `AlgebraicGeometry.Space.homEquiv_symm_representedModulePullback` being
     stated at `(representedSmallEtaleModuleEquivalence …).inverse.obj M`;
     `AlgebraicGeometry.Space.representedAssociatedModuleDefiningIdealOfHomIso` is the forward
     direction, and
     `AlgebraicGeometry.Space.representedSmallEtaleRestrictionIdealSheafIso` /
     `AlgebraicGeometry.Space.representedAssociatedModuleIdealSheafIso` are the two of them with
     the Zariski side named as the categorical `Stacks.ClosedImmersion.idealSheaf`;
   * `AlgebraicGeometry.Space.chartSectionsRingHom_mem_definingIdealAt_selfChart_iff` — the
     sections form, with the Zariski restriction eliminated from the statement: a regular
     function on a Zariski open `W` lands in `AlgebraicGeometry.Space.definingIdealAt` over the
     étale chart `W` cuts out exactly when `j` kills it on sections.

   What that file does **not** state is the compatibility of the two étale-site readings with
   the inclusions into the structure sheaf; its "What is not proved" section names the missing
   ingredient, which is the cognate of the one input part (2) of Stacks 04G2 is waiting on.  The
   sections form above is what stands in for it.
3. The derivation read at both ends: that the two transposes agree on sections, `f ↦ d f`
   followed by the unit on one side (`kernelIdealUnitDifferential_val_app_apply`) and
   `f ↦ 1 ⊗ d f` on the other (`conormalDifferentialTranspose_val_app`), through
   `AlgebraicGeometry.Space.schemeDifferentialsIso`.  **The derivation half of this step is
   proved**, in `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceDerivationBothEnds.lean`,
   together with the pinning that reduces a comparison of the two *arrows* to a comparison of
   their *values*.

   * `Stacks.CategoryTheory.unit_transport` — the half of step 1 that step 1 did not supply:
     round a square of adjunctions the two **units** correspond, which is
     `Stacks.CategoryTheory.homEquiv_transport` read at the identity.  Instantiated at the two
     joins as `AlgebraicGeometry.SmallEtale.unit_associatedModuleBaseChange` and
     `AlgebraicGeometry.Space.unit_representedModulePullback`.  Both arrows being identified are
     the adjoint transpose of a derivation *followed by the unit*, so this is what compares what
     follows the derivation.
   * `AlgebraicGeometry.Space.pullbackUnitDerivation_postcomp_map_map` — for **any** comparison
     `Φ : Ω_{Y/Bb} ⟶ N` carrying the universal derivation to a derivation `E`, the derivation
     `d_{Y/Bb}` followed by the unit of `f^* ⊣ f_*`, read through `f_*f^*Φ`, is `E` followed by
     that same unit.  Nothing beyond `Φ`'s own compatibility and the naturality of the unit is
     used; and because `Φ` is arbitrary the comparison composes, which the join needs — it wants
     the composite isomorphism of
     `AlgebraicGeometry.Space.sheafOfDifferentialsSchemeComparison`, not only its first factor.
   * `AlgebraicGeometry.Space.pullbackUnitDerivation_postcomp_schemeDifferentialsIso` and
     `AlgebraicGeometry.Space.kernelIdealUnitDifferential_val_app_apply_schemeDifferentialsIso`
     — that lemma at `AlgebraicGeometry.Space.schemeDifferentialsIso`: the spaces-side value
     formula *is* the unit of `φ^* ⊣ φ_*` applied to the transported scheme-side universal
     differential of the section, which is exactly the shape
     `Stacks.ConormalSequenceRight.conormalDifferentialTranspose_val_app` is written in.
   * the two pinnings — each transpose is the unique morphism out of its ideal sheaf with its
     value formula (`AlgebraicGeometry.Space.eq_kernelIdealUnitDifferential_of_val_app_apply`
     and `Stacks.ConormalSequenceRight.eq_conormalDifferentialTranspose_of_val_app`), and
     `AlgebraicGeometry.Space.submoduleTranspose_eq_kernelConormalFirstMap_of_val_app_apply`
     carries that up to the arrow, the spaces-side mirror of
     `Stacks.ConormalSequenceRight.conormalDifferential_unique`.  The latter is stated through
     `AlgebraicGeometry.Space.submoduleTranspose` and not through the hom-set bijection written
     out: both a `rfl` identifying `kernelConormalFirstMap` with the written-out transpose and
     the same statement phrased with `CategoryTheory.Adjunction.homEquiv` exhaust
     the heartbeat budget in that module, exactly as the implementation notes of
     `AlgebraicGeometry.Space.submoduleTranspose` predict.

   **The first thing step 3 requires is proved**, in
   `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceDerivationSchemeComparison.lean`:
   `pullbackUnitDerivation_postcomp_map_map` fed the *composite* isomorphism of
   `AlgebraicGeometry.Space.sheafOfDifferentialsSchemeComparison` rather than only its first
   factor.  That isomorphism is named there as
   `AlgebraicGeometry.Space.representedAssociatedDifferentialsIso` — the tag's own
   `sheafOfDifferentialsSchemeComparison` produces it inside a `Nonempty`, which a consumer that
   must read a derivation through it cannot use — its compatibility with the universal
   derivations is `AlgebraicGeometry.Space.postcomp_representedAssociatedDifferentialsIso`
   (`AlgebraicGeometry.Space.postcomp_schemeDifferentialsHom` followed by
   `AlgebraicGeometry.SmallEtale.postcomp_differentialsIso_inv`), and the two consequences are
   `AlgebraicGeometry.Space.pullbackUnitDerivation_postcomp_representedAssociatedDifferentialsIso`
   and
   `kernelIdealUnitDifferential_val_app_apply_representedAssociatedDifferentialsIso` (in the
   namespace `AlgebraicGeometry.Space`, written without the prefix so that it fits).
   The latter is the spaces-side value formula of the first arrow written over the associated
   module of the Zariski `Ω_{U/V}`, which is the module
   `Stacks.ConormalSequenceRight.conormalDifferentialTranspose` is a morphism into.

   **What the arrow identification still owes, named precisely.**  Steps 1, 2 and 3 are
   complete, and so is the first of the four things the join owes; three remain.

   * The *sources*, consumed.  **This is now done**, in
     `StacksFrontier/AlgebraicGeometry/Spaces/AssociatedModuleChartPushTranspose.lean`.  Step 2
     identifies the sources
     (`AlgebraicGeometry.Space.representedAssociatedModuleDefiningIdealOfHomIso`), and
     the value comparison needs to know what that identification does to a *section*, which the
     identification itself cannot say:
     `AlgebraicGeometry.Space.associatedModuleChartPushSelfChartIso`, which it is built from, is
     the *inverse of the counit* of the associated-module adjunction.  But a morphism **out of**
     `𝓝^a` is determined by its transpose along that adjunction — its composite with the unit —
     and the transpose lives on *Zariski* sections.  Transposed, the counit contributes nothing
     at all: its own transpose is the identity, by the right triangle identity
     (`unit_comp_restrictModule_map_associatedModuleRestrictModuleIso_hom`, in the namespace
     `AlgebraicGeometry.SmallEtale`).
     So the comparison at the identity chart transposes to the transport of
     `AlgebraicGeometry.Space.chartPush_selfChart`
     (`unit_comp_restrictModule_map_associatedModuleChartPushSelfChartIso_hom`); the comparison
     for a sheaf of ideals transposes to the canonical sections map
     `AlgebraicGeometry.Space.chartZariskiIdealSheafIsoChartPush`
     (`unit_comp_restrictModule_map_associatedModuleChartZariskiIdealSheafSelfChartIso_hom`); and
     on a section that is `AlgebraicGeometry.Space.chartSectionsRingHom`
     (`associatedModuleChartZariskiIdealSheafSelfChartIso_transpose_val_app_apply` — all three in
     the namespace `AlgebraicGeometry.Space`).  Since the comparison of scalars is a *ring* map
     defined on all of `Γ(V, W)`, that last statement **is** the inclusion-compatibility of the
     two étale-site readings of the ideal sheaf with the inclusions into the structure sheaf.
     What the join still has to do with it is the one
     step transposition leaves: compare the two morphisms out of `𝓝^a` by
     `CategoryTheory.Adjunction.hom_ext_of_unit_comp_map`, which turns that comparison into the
     Zariski-sections statement above.
   * The *target*, the coborder move:
     `Stacks.ConormalSequenceRight.coborderPullbackDifferentialsIso`, which moves the
     scheme-side target from the coborder neighbourhood to the ambient scheme.
   * The *base*.  `AlgebraicGeometry.Space.representedAssociatedDifferentialsIso`, like
     Stacks 04CS, is about `Ω` of a morphism of *schemes of the site*, whereas Stacks 05ZB's
     base `Bb` is an arbitrary algebraic space.  Getting from one to the other is Stacks 04CU
     proper, `AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso`, on a square of
     étale charts — so the identification is at a chart of `Bb` as well as of `X`.
   * The *descent*.  Even with the arrow identified at a represented closed immersion, the
     monomorphy has to be carried to an arbitrary closed subspace along an étale covering.  The
     ingredient is `modulePullback_map_injective_of_isEtaleCovering`, and the proof template is
     `AlgebraicGeometry.Space.mono_conormalMap_universalThickening`
     (`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceUnramifiedPairSplitting.lean`),
     which proves monomorphy of a *different* conormal map from étale-local retractions in
     exactly this way.

## The third route: Stacks 02HP inside the small étale topos, and what it still needs

The arrow identification above is the source's route and the second route below reduces this
tag's clause to that of Stacks 05ZX.  There is a third, which needs neither: transport the
*derivation* of Stacks 02HP into the small étale topos directly.  Its bookkeeping is
carried out as follows.

**What has to be produced, exactly.**  `AlgebraicGeometry.Space.conormalSequenceFirstMap` is
`AlgebraicGeometry.Space.submoduleTranspose` of the morphism
`AlgebraicGeometry.Space.conormalSequenceIdealDifferential : 𝓘 ⟶ i_*i^*Ω_{X/B}`, and the
identity of `i^*𝓘` is `submoduleTranspose` of the unit `𝓘 ⟶ i_*i^*𝓘`.  Since
`submoduleTranspose` is a bijection, a retraction `r` of the first arrow is the same thing as a
`B`-derivation `D : 𝒪_X ⟶ i_*𝒞_{Z/X}` whose restriction to `𝓘` is **the unit of `i^* ⊣ i_*`**
— the transpose of `r` under Equation (0619),
`AlgebraicGeometry.Space.derivationDirectImageEquiv`.  That derivation is `a ↦ a - g^♯(i^♯ a)`,
and a retraction makes the first arrow a monomorphism.

**The base may be taken to be `Z` itself, and then `hgb` is not needed.**  The first arrow over
`B` followed by the inverse image along `i` of the canonical map `Ω_{X/B} ⟶ Ω_{X/Z}` of
Stacks 05Z8 — `AlgebraicGeometry.Space.toRelativeDifferentials`, over the structure morphism
`g : X ⟶ Z` — is the first arrow over `Z`.  So monomorphy over `B` follows from monomorphy over
`Z`, and over `Z` the left inverse `g` *is* the structure morphism, so that it is a morphism
over the base is `hg` itself and the tag's `hgb` plays no part.  This also says something about
the tag: its injectivity clause holds for any left inverse of `i`, over `B` or not.

**Why the derivation cannot be written on the small étale site of `X`.**  `g^♯(i^♯ a)` is a
section of `𝒪_X` over `h^{-1}U` for `h = g ≫ i`, not over `U`, and there is no morphism
`h^{-1}U ⟶ U` of the site: `a` and `g^♯(i^♯a)` can be compared only near `Z`.  The place where
they can be compared is `i_*i⁻¹𝒪_X`, whose unit `η : 𝒪_X ⟶ i_*i⁻¹𝒪_X` is available, and there the
comparison is a *split surjection*: `i_*(i♯) : i_*i⁻¹𝒪_X ⟶ i_*𝒪_Z` has the section `i_*(s)`
for `s` the section of `AlgebraicGeometry.Space.inverseImageStructureSharpSection`
(`StacksFrontier/AlgebraicGeometry/Spaces/InverseImageStructureSharpSection.lean`), which a left
inverse of `i` supplies.  `η ≫ i_*(i♯) = i^♯` is
`AlgebraicGeometry.Space.unit_comp_map_structureSharpInverseImage`.

**The generic half is proved, and needs no square-zero hypothesis.**
`PresheafOfModules.splitSurjectionDerivation`
(`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/SplitSurjectionDerivation.lean`) is
Stacks 02HP's derivation for a split surjection `π : A ⟶ Q` of presheaves of commutative rings
with coefficients in any `A`-module annihilated by the kernel of `π`: the difference
`δ x = x - sec (π x)` satisfies `δ (x * y) = x * δ y + sec (π y) * δ x` *exactly*, and the gap
between that and the Leibniz rule is `δ y * δ x`, which the coefficients kill.  So what replaces
the square-zero hypothesis of `AlgebraicGeometry.Space.liftDifference` is that the kernel
annihilate the coefficients — automatic for a module restricted along `π`.  The resulting
derivation of `i_*i⁻¹𝒪_X` is carried to one of `𝒪_X` by precomposition with `η`,
`Stacks.Sheaves.RingedToposModules.derivationPrecompRing`, and no transposition of derivations
along an inverse image (Stacks 08TQ) is needed anywhere.

**The coefficient map is built, and with it every datum the derivation consumes.**  All
three pieces below are proved, and the generic engine takes the kernel of the split surjection as
a *family of sections* rather than as a module —
see the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/SplitSurjectionIdealDerivation.lean` for why
nothing else is affordable here.

* **The kernel.**  The identification of `i⁻¹𝓘` with the kernel of
  `AlgebraicGeometry.Space.structureSharpInverseImage` needs no local-generation statement: it is
  exactness of the inverse image and nothing else.  It is
  `StacksFrontier/AlgebraicGeometry/Spaces/InverseImageDefiningIdealKernel.lean` (the short exact
  sequence of Stacks 03MB carried through `i⁻¹` and then `i_*`, read on sections) together with
  `StacksFrontier/AlgebraicGeometry/Spaces/DirectImageIdealKernelBridge.lean`, which moves the
  reading from the direct-image form of the structure map to the inverse-image form across the
  direct image of the counit `i⁻¹i_*𝒪_Z ≅ 𝒪_Z` — invertible by part (1) of Stacks 04E5.  The
  sections of `i_*i⁻¹𝓘` are exactly the kernel of the split surjection:
  `AlgebraicGeometry.Space.injective_directImageInverseImageIdealIota`,
  `AlgebraicGeometry.Space.exists_directImageInverseImageIdealIota` and
  `AlgebraicGeometry.Space.directImageInverseImageIdealIota_eq_zero`.
* **The canonical map `i⁻¹𝓘 ⟶ 𝒞_{Z/X}`.**  `AlgebraicGeometry.Space.conormalDirectImageNu`
  (`StacksFrontier/AlgebraicGeometry/Spaces/ConormalDirectImageUnit.lean`), the second factor of
  the unit of Stacks 03LU at `𝓘` — the direct image of the unit of
  `Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction` — with its additivity,
  semilinearity and naturality.  That the unit of Stacks 03LU is that factor preceded by the
  unit of Stacks 03D3 is
  `Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules_unit_app`, which is
  `CategoryTheory.Adjunction.comp_unit_app`.
* **The two units agree.**  `AlgebraicGeometry.Space.directImageInverseImageIdealIota_unit`:
  the unit of Stacks 03D3 at `𝓘` followed by the inclusion `i_*i⁻¹𝓘 ⟶ i_*i⁻¹𝒪_X` **is** the
  inclusion `𝓘 ⊆ 𝒪_X` followed by `η`.  Naturality of the first unit at `𝓘.ι`, plus
  `Stacks.Sheaves.RingedToposModules.unit_app_unit_val_app_eq_commRingUnit`.

The split surjection itself and the base of the derivation are
`AlgebraicGeometry.Space.directImageInverseImageStructureSharpSection_comp_hom` and
`AlgebraicGeometry.Space.conormalSplitBase_comp_apply`
(`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSplitDerivation.lean`); the second is
`AlgebraicGeometry.Space.inverseImageStructureSharpSection_fixes` pushed forward along `i_*`
and transposed by the naturality of `η`, and it uses no compatibility of `g` with an ambient
base — which is the Lean form of the statement that this clause holds for *any* left inverse.

**This route is complete, and proves the tag.**  Its four steps are carried out in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceSplitMono.lean`, and
`AlgebraicGeometry.Space.nonempty_conormalSequence_splitting` and
`AlgebraicGeometry.Space.nonempty_conormalSequence_splitting_of_etale` there register the tag on
the full `CategoryTheory.ShortComplex.Splitting`, both globally and étale-locally.  What they
supply beyond this file is `AlgebraicGeometry.Space.mono_conormalSequenceFirstMap`, the
injectivity clause, which `AlgebraicGeometry.Space.nonempty_conormalSequence_splitting_iff_mono`
below turns into the splitting.  In order:

1. `AlgebraicGeometry.Space.conormalSplitIdealDerivation` instantiates
   `PresheafOfModules.splitIdealDerivation` at the data above, with `hnuSmul` the declaration
   `AlgebraicGeometry.Space.conormalDirectImageNu_smul_structureSharp`.
2. `AlgebraicGeometry.Space.conormalSplitDerivation` carries it to a derivation of `𝒪_X` by
   `Stacks.Sheaves.RingedToposModules.derivationPrecompRing` along `η`.
3. Its restriction to `𝓘` *is* the unit of Stacks 03LU:
   `AlgebraicGeometry.Space.conormalSplitDerivation_d_unit`.  The one piece this needed was the
   unit of Stacks 03LU at `𝓘` read on sections, which is
   `AlgebraicGeometry.Space.modulePullbackAdjunction_unit_definingIdealSheaf_val_app` in
   `StacksFrontier/AlgebraicGeometry/Spaces/ConormalDirectImageUnitSections.lean` — its own module,
   because the three equations it joins hold of two different spellings of the morphism of
   ringed topoi of the inclusion and only one closure reconciles them; the implementation notes
   there explain this.
4. Equation (0619) then gives the retraction
   `AlgebraicGeometry.Space.conormalSequenceIdealPullbackMap_comp_derivationDirectImageEquiv_symm`,
   hence `AlgebraicGeometry.Space.mono_conormalSequenceFirstMap_of_retraction` over the base `Z`,
   and `AlgebraicGeometry.Space.mono_conormalSequenceFirstMap` over an arbitrary base by composing
   with the inverse image along `i` of `AlgebraicGeometry.Space.toRelativeDifferentials` of
   Stacks 05Z8.

None of it is mathematical, and `hgb` plays no part in the injectivity: it enters
only to identify `Ω_{X/B}` with `Ω_{X/(g ≫ i ≫ b)}`.

**A refinement of the paragraph below.**  "A global left inverse does not restrict to
a left inverse of the immersion restricted to an étale chart" is true of an *arbitrary* chart
and false of the charts pulled back along `g`: for any `q : V ⟶ Z`, the inverse image
`U := X ×_{g, Z} V` has `Z ×_X U = V`, by `i ≫ g = 𝟙`, and the projection `U ⟶ V` is a left
inverse of the restricted immersion over `B` — the fibre-product square being exactly the
square `Stacks 04CU` wants.  Taking `q` étale and surjective makes `U ⟶ X` étale and
surjective, so a global left inverse *does* give left inverses on a covering of `X` and on the
original covering of `Z`.  What that does not give is a *representable* `U`: `U ⟶ V` is a base
change of `g`, which is not representable in general (for `Z` a point of a non-schematic `X` it
is representable exactly when `X` is a scheme), and charting `U` destroys the left inverse
again.  So the obstruction to the source's own route is representability of the ambient chart,
not existence of the left inverse.

A further step is needed for the *global* reading of the tag, and it is worth recording because
it is not obvious: **a global left inverse does not restrict to a left inverse of the immersion
restricted to an étale chart.**  For `φ : X' ⟶ X` étale and `Z' = Z ×_X X'`, a left inverse
`X' ⟶ Z'` would be a pair `(h, g ∘ φ)` with `φ ∘ h = i ∘ g ∘ φ`, and `𝟙_{X'}` does not satisfy
that equation.  What a global left inverse does give on a chart is a retraction *modulo `𝓘²`*:
the two morphisms `X' ⟶ X` given by `φ` and by `i ∘ g ∘ φ` agree on `Z'`, so on the first-order
neighbourhood of `Z'` in `X'` the unique lifting property of the étale `φ` produces a retraction
onto `Z'`.  That is the hypothesis shape of Stacks 02HP
(`KaehlerDifferential.split_exact_kerCotangentToTensor_mapBaseChange_of_section`, which takes a
section of `P ⧸ I² ⟶ S`) rather than of
`Stacks.ConormalSequenceSplit.mono_conormalDifferential_of_retraction`, which takes a genuine
left inverse.  So the global reading additionally needs that lifting together with a scheme- or
ring-level monomorphy statement fed from a modulo-`𝓘²` retraction.  For the tag's parenthetical
reading — `i` has a left inverse étale locally — no lifting is needed: on a chart which is a
scheme the scheme-level result applies on the nose, and only the arrow identification
above is wanted.

## The second route to the injectivity clause, and what it needs

The arrow identification is the source's own route.  There is a second one — transporting
Stacks 02HP to algebraic spaces instead of reducing to it on charts — and it is worth recording
what it needs, because most of its ingredients are available.

The statement to aim at is not a monomorphy statement but a **retraction**: a morphism
`r : i^*Ω_{X/Bb} ⟶ 𝒞_{Z/X}` with `conormalSequenceFirstMap ≫ r = 𝟙`.  Transposed along
`i^* ⊣ i_*` — which is `AlgebraicGeometry.Space.derivationDirectImageEquiv`, Equation (0619) —
such an `r` is a `Bb`-derivation `D` of `𝒪_X` with values in `i_*𝒞_{Z/X}` whose restriction to
the defining ideal sheaf is the unit `𝓘 ⟶ i_*i^*𝓘`; that is exactly the content of
`AlgebraicGeometry.Space.submoduleTranspose_eq_kernelConormalFirstMap_of_val_app_apply` read on
the other side.  Ring-side `D` is `a ↦ a - g^♯(i^♯ a)`, Mathlib's
`Algebra.derivationOfSectionOfKerSqZero`.

**Two things that route does *not* need.**

* It does not need part (3) of Stacks 04CN in general.  The unit `𝓘 ⟶ i_*𝒞_{Z/X}` is an
  isomorphism for a **first-order thickening**, and that *is* proved here:
  `AlgebraicGeometry.Space.isIso_unit_definingIdealSheaf_of_isFirstOrderThickening`, packaged as
  `AlgebraicGeometry.Space.firstOrderConormalModuleIso` with the resulting inclusion
  `AlgebraicGeometry.Space.firstOrderConormalModuleι`
  (`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleFirstOrderIdeal.lean`).
* It does not need a new "difference of two maps is a derivation" statement.  That is proved as
  `AlgebraicGeometry.Space.liftDifference` with its four defining equations
  (`StacksFrontier/AlgebraicGeometry/Spaces/LiftDifferenceDerivation.lean`, Stacks 0618), for two
  morphisms of sheaves of rings into `𝒪_X` agreeing after `i^♯`; and the identification of the
  two sources that lets the difference be formed at all — the two morphisms into `𝒪_X` having a
  priori different inverse-image structure sheaves — is
  `AlgebraicGeometry.Space.structureSharpOfRestrictEq`
  (`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/StructureSheafEquivalence.lean`).

**What it does need, and why it is not obviously cheaper.**  `liftDifference` is stated for a
closed subspace which is a first-order thickening, and `Z ⊆ X` is not one; the two morphisms
`X ⟶ X` whose difference `D` is — the identity and `g ≫ i` — agree only on `Z`, and they induce
the same morphism of small étale topoi only after `X` is replaced by the first-order
neighbourhood `Z ⊆ Z' ⊆ X`, where Stacks 05ZM makes the two topoi agree.  Two things are then
open.

* The neighbourhood `Z'` itself.  This development builds it only at a chart
  (`AlgebraicGeometry.Space.firstOrderInfinitesimalNeighbourhood` of Stacks 05ZV); as a closed
  subspace cut out by `𝓘²` it needs the surjectivity half of Stacks 03MB, which the "What is
  not proved" section of
  `StacksFrontier/AlgebraicGeometry/Spaces/ClosedSubspaceIdealBijection.lean` records as absent.
  `AlgebraicGeometry.Space.IsFirstOrderNeighbourhood` is the property carried as a hypothesis
  instead.
* The comparison `𝒞_{Z/X} ⟶ 𝒞_{Z/Z'}`.  The derivation built on `Z'` retracts
  `conormalSequenceFirstMap` only *after* that comparison, so the route delivers
  `conormalSequenceFirstMap ≫ r' = ` that comparison, and injectivity of the first arrow then
  needs the comparison to be a monomorphism.  That is the open half of Stacks 05ZX, isolated as
  `AlgebraicGeometry.Space.isIso_conormalMap_firstOrderNeighbourhood_iff_mono`
  (`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleFirstOrderNeighbourhood.lean`); the
  surjectivity half is `AlgebraicGeometry.Space.epi_conormalMap_firstOrderNeighbourhood`.

So this route reduces the injectivity clause of Stacks 05ZB to the injectivity clause of
Stacks 05ZX, which is not an advance on the arrow identification but is a different wall.

`AlgebraicGeometry.Space.nonempty_conormalSequence_splitting_iff_mono` is what makes this a
single named clause rather than a vague gap.  No statement below carries it as a hypothesis.

## References

* [Stacks Project, Tag 05ZB](https://stacks.math.columbia.edu/tag/05ZB), this file's subject.
* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA), the conormal sequence
  whose split exactness is asserted.
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU), part (4), for `hclosed`.
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU) and
  [Tag 04CO](https://stacks.math.columbia.edu/tag/04CO), the étale localization the source's proof
  goes through, whose invertibility clause the étale-local statement below consumes through
  `AlgebraicGeometry.Space.isSplitEpi_map_pullbackDifferentialsMap_of_etale`.
* [Stacks Project, Tag 010G](https://stacks.math.columbia.edu/tag/010G),
  `CategoryTheory.ShortComplex.Splitting.ofExactOfSection`, the splitting criterion used below.
* [Stacks Project, Tag 0474](https://stacks.math.columbia.edu/tag/0474) and
  [Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ), this tag for morphisms of schemes, which
  the source's proof reduces to and which is proved in
  `StacksFrontier/AlgebraicGeometry/ConormalSequenceSplit/ShortExact.lean` — including the
  injectivity clause that is open here.
* [Stacks Project, Tag 02HP](https://stacks.math.columbia.edu/tag/02HP), the injectivity of
  `KaehlerDifferential.kerCotangentToTensor` in the presence of a section, which that proof rests
  on.
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN), part 3, the
  identification of the conormal module with `𝓘/𝓘²`.  The direct route to the injectivity clause
  needs only the first-order case of it, which is proved as
  `AlgebraicGeometry.Space.firstOrderConormalModuleIso` — see "The second route to the
  injectivity clause" above.
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618), the difference of two
  lifts as a derivation, and [Tag 0619](https://stacks.math.columbia.edu/tag/0619), the
  adjointness step, which that second route runs on.
* [Stacks Project, Tag 05ZX](https://stacks.math.columbia.edu/tag/05ZX), the comparison
  `𝒞_{Z/X} ⟶ 𝒞_{Z/Z'}` with the first-order neighbourhood, whose injectivity clause that second
  route reduces this tag's injectivity clause to.
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU) proper, on a square of
  étale charts, which the arrow identification needs for an arbitrary base `Bb`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X X' Bb Zs Zs' : AlgebraicSpaces B S hS}

/-- **Stacks 05ZB, the global clause, as one statement.**  Let `Z ⊆ X` be a closed subspace of an
algebraic space over `Bb` with structure morphism `b : X ⟶ Bb`, let `i` be a closed immersion with
target `X` whose structure map has the defining ideal sheaf of `Z` for its kernel, and let
`g : X ⟶ Zs` be a left inverse of `i` over `Bb`.  Then the conormal sequence of Stacks 05ZA
```
  𝒞_{Z/X} ⟶ i^*Ω_{X/Bb} ⟶ Ω_{Z/Bb} ⟶ 0
```
is exact at its middle term and its second arrow is a split epimorphism.

The two clauses are `AlgebraicGeometry.Space.conormalSequenceAt_exact` and
`AlgebraicGeometry.Space.isSplitEpi_pullbackDifferentialsMap_of_retraction`; exactness at the
right term is the epimorphism underlying the split epimorphism, and the vanishing of the composite
is the short complex itself.  Injectivity of the first arrow is not among them; see the module
docstring and `AlgebraicGeometry.Space.nonempty_conormalSequenceAt_splitting_iff_mono`.

**This is the general form, with the inclusion an explicit parameter**, kept because
`AlgebraicGeometry.Space.conormalSequenceAt_splitExact_of_etale` instantiates it at the restricted
data.  The tag is registered on `AlgebraicGeometry.Space.conormalSequence_splitExact`, which is
this statement at the canonical inclusion with `hi`, `hker` and `hclosed` all discharged. -/
theorem conormalSequenceAt_splitExact (Z : ClosedSubspaces B S hS X.1) (b : X ⟶ Bb) (i : Zs ⟶ X)
    (hi : StructureSharpKillsDefiningIdeal B S hS Z i)
    (hker : StructureSharpKernelLeDefiningIdeal B S hS Z i)
    (hclosed : IsClosedImmersion B S hS i.hom) (g : X ⟶ Zs) (hg : i ≫ g = 𝟙 Zs)
    (hgb : g ≫ i ≫ b = b) :
    (ShortComplex.mk _ _
          (conormalSequenceFirstMapAt_comp_pullbackDifferentialsMap_eq_zero B S hS Z b i
            hi)).Exact ∧
      IsSplitEpi (pullbackDifferentialsMap B S hS i b) :=
  ⟨conormalSequenceAt_exact B S hS Z b i hi hker hclosed,
    isSplitEpi_pullbackDifferentialsMap_of_retraction B S hS i b g hg hgb⟩

/-- **Stacks 05ZB, the global clause, unconditionally.**  Let `Z ⊆ X` be a closed subspace of an
algebraic space over `Bb` with structure morphism `b : X ⟶ Bb`, and let `g : X ⟶ Z` be a left
inverse over `Bb` of the inclusion of `Z`.  Then the conormal sequence of Stacks 05ZA
```
  𝒞_{Z/X} ⟶ i^*Ω_{X/Bb} ⟶ Ω_{Z/Bb} ⟶ 0
```
is exact at its middle term and its second arrow is a split epimorphism.

**No hypothesis beyond the left inverse is carried**, and the sequence is the one Stacks 05ZA
states: the first arrow is `AlgebraicGeometry.Space.conormalSequenceFirstMap`, whose source is the
conormal module `𝒞_{Z/X}` of Stacks 04CN.  The exactness clause is
`AlgebraicGeometry.Space.conormalSequence_exact`, which is
`AlgebraicGeometry.Space.conormalSequenceAt_splitExact`'s first component at the canonical
inclusion with its three hypotheses discharged — the two halves of
`AlgebraicGeometry.Space.mem_definingIdealAt_iff` and part (4) of Stacks 02YU — and read at
`conormalSequenceFirstMap`; the splitness clause is unchanged by that reading, since
`AlgebraicGeometry.Space.pullbackDifferentialsMap` does not mention the first arrow.

The hypothesis is satisfiable: at the top closed subspace the inclusion is an isomorphism, and its
inverse is a left inverse over `Bb`; the retraction is written out in the proof of
`AlgebraicGeometry.Space.isZero_conormalModule_top` of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/LiftingSheaf.lean`. -/
@[stacks 05ZB "the global clause at the inclusion of a bundled subspace `Z ⊆ X` having a left \
inverse over `B`: the conormal sequence of 05ZA is exact at its middle term `i^*Ω_{X/B}` and \
its second arrow is a split epimorphism, hence also an epimorphism, which is exactness at the \
right term; the vanishing of the composite is the short complex itself.  Stated at the \
canonical inclusion and at the registered first arrow `conormalSequenceFirstMap`, with no \
hypothesis beyond the left inverse, which is the tag's own datum.  The injectivity clause at \
the left end of the sequence is the subject of \
`nonempty_conormalSequence_splitting_iff_mono`, which shows it equivalent to the full \
`ShortComplex.Splitting`.  The general form with the inclusion an explicit parameter is \
`conormalSequenceAt_splitExact`, and the same clause at an arbitrary closed immersion, with no \
bundled subspace anywhere, is `conormalSequenceKernel_splitExact_of_isClosedImmersion`; at the \
generality the tag is stated at, an arbitrary immersion with a left inverse over `B`, the \
sequence is split exact in full by `nonempty_conormalSequenceOfImmersion_splitting`"]
theorem conormalSequence_splitExact (Z : ClosedSubspaces B S hS X.1) (b : X ⟶ Bb)
    (g : X ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
    (hg : subspaceInclusion B S hS X Z ≫ g = 𝟙 (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
    (hgb : g ≫ subspaceInclusion B S hS X Z ≫ b = b) :
    (ShortComplex.mk _ _
          (conormalSequenceFirstMap_comp_pullbackDifferentialsMap_eq_zero B S hS Z b)).Exact ∧
      IsSplitEpi (pullbackDifferentialsMap B S hS (subspaceInclusion B S hS X Z) b) :=
  ⟨conormalSequence_exact B S hS Z b,
    isSplitEpi_pullbackDifferentialsMap_of_retraction B S hS (subspaceInclusion B S hS X Z) b g
      hg hgb⟩

/-- **Stacks 05ZB, the étale-local clause, as one statement.**  Let `φ : X' ⟶ X` be étale, let
`Z' ⊆ X'` be a closed subspace, let `i' : Zs' ⟶ X'` be a closed immersion whose structure map has
the defining ideal sheaf of `Z'` for its kernel, let `a : Zs' ⟶ Zs` be étale with
`i' ≫ φ = a ≫ i`, and let `g' : X' ⟶ Zs'` be a left inverse of `i'` over `Bb`.  Then

* the restricted conormal sequence, the sequence of Stacks 05ZA at `i'` over `φ ≫ b`, is exact at
  its middle term, and its second arrow is a split epimorphism;
* the inverse image along `a` of the second arrow of the unrestricted sequence is a split
  epimorphism too.

The first two clauses are `AlgebraicGeometry.Space.conormalSequenceAt_splitExact` at the
restricted data; the third is
`AlgebraicGeometry.Space.isSplitEpi_map_pullbackDifferentialsMap_of_etale`, which is where the
étale-localization clause of Stacks 04CU is consumed.  As there, étaleness is assumed of `φ` and
of `a` separately rather than `Z'` being assumed to be the preimage of `Z`, which is weaker: in
the situation of the source `a` is a base change of `φ`.

**This is the general form, with both inclusions explicit parameters.**  The tag is registered on
`AlgebraicGeometry.Space.conormalSequence_splitExact_of_etale`, which is this statement at the two
canonical inclusions with `hi'`, `hker'` and `hclosed'` all discharged. -/
theorem conormalSequenceAt_splitExact_of_etale (Z' : ClosedSubspaces B S hS X'.1) (b : X ⟶ Bb)
    (i : Zs ⟶ X) (φ : X' ⟶ X) (hφ : IsEtale B S hS φ.hom) (i' : Zs' ⟶ X') (a : Zs' ⟶ Zs)
    (ha : IsEtale B S hS a.hom) (hsq : i' ≫ φ = a ≫ i)
    (hi' : StructureSharpKillsDefiningIdeal B S hS Z' i')
    (hker' : StructureSharpKernelLeDefiningIdeal B S hS Z' i')
    (hclosed' : IsClosedImmersion B S hS i'.hom) (g' : X' ⟶ Zs') (hg' : i' ≫ g' = 𝟙 Zs')
    (hg'b : g' ≫ i' ≫ φ ≫ b = φ ≫ b) :
    (ShortComplex.mk _ _
          (conormalSequenceFirstMapAt_comp_pullbackDifferentialsMap_eq_zero B S hS Z' (φ ≫ b) i'
            hi')).Exact ∧
        IsSplitEpi (pullbackDifferentialsMap B S hS i' (φ ≫ b)) ∧
      IsSplitEpi ((modulePullback B S hS a).map (pullbackDifferentialsMap B S hS i b)) :=
  have h := conormalSequenceAt_splitExact B S hS Z' (φ ≫ b) i' hi' hker' hclosed' g' hg' hg'b
  ⟨h.1, h.2,
    isSplitEpi_map_pullbackDifferentialsMap_of_etale B S hS i b φ hφ i' a ha hsq g' hg' hg'b⟩

/-- **Stacks 05ZB, the étale-local clause, unconditionally.**  Let `Z ⊆ X` and `Z' ⊆ X'` be closed
subspaces, let `φ : X' ⟶ X` be étale, let `a : Z' ⟶ Z` be étale with `i' ≫ φ = a ≫ i` for the two
inclusions, and let `g' : X' ⟶ Z'` be a left inverse of the inclusion of `Z'` over `Bb`.  Then

* the restricted conormal sequence, the sequence of Stacks 05ZA at `Z' ⊆ X'` over `φ ≫ b`, is
  exact at its middle term, and its second arrow is a split epimorphism;
* the inverse image along `a` of the second arrow of the unrestricted sequence is a split
  epimorphism too.

**No hypothesis beyond the étale-local data of the tag is carried**: `φ`, `a` and the square they
sit in, and the left inverse `g'`.  The first clause is
`AlgebraicGeometry.Space.conormalSequence_exact` at `Z' ⊆ X'` over `φ ≫ b`, so it is stated at the
registered first arrow `AlgebraicGeometry.Space.conormalSequenceFirstMap` with the source read as
`𝒞_{Z'/X'}`; the other two are the corresponding clauses of
`AlgebraicGeometry.Space.conormalSequenceAt_splitExact_of_etale`, which do not mention the first
arrow.  As there, étaleness is assumed of `φ` and of `a` separately rather than `Z'` being assumed
to be the preimage of `Z`, which is weaker: in the situation of the source `a` is a base change
of `φ`. -/
@[stacks 05ZB "the étale-local clause: for closed subspaces `Z ⊆ X` and `Z' ⊆ X'` joined by an \
étale `φ : X' ⟶ X` and an étale `a : Z' ⟶ Z` over it, with the inclusion of `Z'` admitting a left \
inverse over `B`, the restricted conormal sequence of 05ZA is exact at its middle term and its \
second arrow is a split epimorphism, and so is the inverse image along `a` of the second arrow of \
the unrestricted sequence — which is where the étale-localization clause of 04CU is consumed.  \
Stated at the two canonical inclusions and at the registered first arrow \
`conormalSequenceFirstMap`, with no hypothesis beyond the étale-local data of the tag.  As in the \
global clause, the injectivity clause at the left end of the sequence is the subject of \
`nonempty_conormalSequence_splitting_iff_mono`.  The general form with both inclusions explicit \
parameters is `conormalSequenceAt_splitExact_of_etale`"]
theorem conormalSequence_splitExact_of_etale (Z : ClosedSubspaces B S hS X.1)
    (Z' : ClosedSubspaces B S hS X'.1) (b : X ⟶ Bb) (φ : X' ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (a : (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
    (ha : IsEtale B S hS a.hom)
    (hsq : subspaceInclusion B S hS X' Z' ≫ φ = a ≫ subspaceInclusion B S hS X Z)
    (g' : X' ⟶ (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (hg' : subspaceInclusion B S hS X' Z' ≫ g' =
      𝟙 (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (hg'b : g' ≫ subspaceInclusion B S hS X' Z' ≫ φ ≫ b = φ ≫ b) :
    (ShortComplex.mk _ _
          (conormalSequenceFirstMap_comp_pullbackDifferentialsMap_eq_zero B S hS Z'
            (φ ≫ b))).Exact ∧
        IsSplitEpi (pullbackDifferentialsMap B S hS (subspaceInclusion B S hS X' Z')
          (φ ≫ b)) ∧
      IsSplitEpi ((modulePullback B S hS a).map
        (pullbackDifferentialsMap B S hS (subspaceInclusion B S hS X Z) b)) :=
  ⟨conormalSequence_exact B S hS Z' (φ ≫ b),
    isSplitEpi_pullbackDifferentialsMap_of_retraction B S hS
      (subspaceInclusion B S hS X' Z') (φ ≫ b) g' hg' hg'b,
    isSplitEpi_map_pullbackDifferentialsMap_of_etale B S hS (subspaceInclusion B S hS X Z) b φ hφ
      (subspaceInclusion B S hS X' Z') a ha hsq g' hg' hg'b⟩

/-- A short complex that is exact, has a split epimorphic second arrow and a monic first arrow
admits a splitting. -/
private theorem nonempty_splitting_of_exact_of_isSplitEpi {C : Type*} [Category C] [Preadditive C]
    [Balanced C] (T : ShortComplex C) (hT : T.Exact) [IsSplitEpi T.g] (hmono : Mono T.f) :
    Nonempty T.Splitting :=
  ⟨ShortComplex.Splitting.ofExactOfSection _ hT (section_ T.g) (IsSplitEpi.id T.g) hmono⟩

/-- **Stacks 05ZB's injectivity clause, isolated as an equivalence: the sequence is split exact in
Mathlib's full sense exactly when its first arrow is injective.**  Under the hypotheses of
`AlgebraicGeometry.Space.conormalSequenceAt_splitExact` — a closed subspace `Z ⊆ X` and a left
inverse `g` of `i` over `Bb` — the conormal sequence of Stacks 05ZA admits a
`CategoryTheory.ShortComplex.Splitting`, that is a retraction `r` of the first arrow and a section
`s` of the second arrow with `r ≫ f + g ≫ s = 𝟙`, **if and only if** its first arrow is a
monomorphism.

Both directions are unconditional: no hypothesis beyond those of
`AlgebraicGeometry.Space.conormalSequenceAt_splitExact` is carried, and neither direction is a
registration of the tag.  Forwards is `CategoryTheory.ShortComplex.Splitting.mono_f`; backwards is
`CategoryTheory.ShortComplex.Splitting.ofExactOfSection` of Stacks 010G, fed with the
exactness and the section.

This shows that injectivity of the first arrow does not follow from the splitting:
it is equivalent to the full splitting, and the full splitting is therefore not available from
exactness and a section of the second arrow alone.  The hypothesis is satisfiable — at `Zs := X`,
`i := 𝟙 X` the defining ideal sheaf is zero and the first arrow is a monomorphism between zero
objects — so this is an equivalence between two things that can both hold, not a vacuous one. -/
theorem nonempty_conormalSequenceAt_splitting_iff_mono (Z : ClosedSubspaces B S hS X.1)
    (b : X ⟶ Bb) (i : Zs ⟶ X) (hi : StructureSharpKillsDefiningIdeal B S hS Z i)
    (hker : StructureSharpKernelLeDefiningIdeal B S hS Z i)
    (hclosed : IsClosedImmersion B S hS i.hom) (g : X ⟶ Zs) (hg : i ≫ g = 𝟙 Zs)
    (hgb : g ≫ i ≫ b = b) :
    Nonempty (ShortComplex.mk _ _
          (conormalSequenceFirstMapAt_comp_pullbackDifferentialsMap_eq_zero B S hS Z b i
            hi)).Splitting ↔
      Mono (conormalSequenceFirstMapAt B S hS Z b i hi) := by
  have : IsSplitEpi (pullbackDifferentialsMap B S hS i b) :=
    isSplitEpi_pullbackDifferentialsMap_of_retraction B S hS i b g hg hgb
  exact ⟨fun h ↦ h.some.mono_f, nonempty_splitting_of_exact_of_isSplitEpi _
    (conormalSequenceAt_exact B S hS Z b i hi hker hclosed)⟩

/-- **Stacks 05ZB's injectivity clause at the canonical inclusion, isolated as an equivalence**:
at a bundled closed subspace `Z ⊆ X`
whose inclusion has a left inverse over `Bb`, the conormal sequence of Stacks 05ZA admits a
`CategoryTheory.ShortComplex.Splitting` — a retraction of the first arrow and a section of the
second arrow summing to the identity — **if and only if** its first arrow
`AlgebraicGeometry.Space.conormalSequenceFirstMap` is a monomorphism.

This is `AlgebraicGeometry.Space.nonempty_conormalSequenceAt_splitting_iff_mono` at the canonical
inclusion, so that the isolation of the remaining clause carries no hypothesis beyond the left
inverse either, and is stated at the arrow Stacks 05ZA's sequence begins with. -/
theorem nonempty_conormalSequence_splitting_iff_mono (Z : ClosedSubspaces B S hS X.1)
    (b : X ⟶ Bb) (g : X ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
    (hg : subspaceInclusion B S hS X Z ≫ g = 𝟙 (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
    (hgb : g ≫ subspaceInclusion B S hS X Z ≫ b = b) :
    Nonempty (ShortComplex.mk _ _
          (conormalSequenceFirstMap_comp_pullbackDifferentialsMap_eq_zero B S hS Z b)).Splitting ↔
      Mono (conormalSequenceFirstMap B S hS Z b) := by
  have : IsSplitEpi (pullbackDifferentialsMap B S hS (subspaceInclusion B S hS X Z) b) :=
    isSplitEpi_pullbackDifferentialsMap_of_retraction B S hS (subspaceInclusion B S hS X Z) b g
      hg hgb
  exact ⟨fun h ↦ h.some.mono_f, nonempty_splitting_of_exact_of_isSplitEpi _
    (conormalSequence_exact B S hS Z b)⟩

end AlgebraicGeometry.Space

end
