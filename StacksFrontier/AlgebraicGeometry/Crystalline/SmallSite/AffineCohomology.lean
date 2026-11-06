module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import StacksFrontier.AlgebraicGeometry.Crystalline.DeRhamComplex
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ChaoticSubsite
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LocallyQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleComparison

/-!
# Crystalline cohomology in the affine case: the complex `M(0) → M(1) → M(2) → ⋯`

Fix a global crystalline situation `(p, (S, I, γ), X)` with `X` and `S` affine, say `X = Spec C`
and `S = Spec A`, and let `F` be a sheaf of `𝒪_{X/S}`-modules on the small crystalline site
`Cris(X/S)`.  The source's section on cohomology in the affine case chooses a polynomial algebra
`P` over `A` with a surjection `P → C`, forms the `p`-adically completed divided power envelopes
`D(n)` of the kernels of the surjections `P ⊗_A ⋯ ⊗_A P → C` out of the `(n + 1)`-fold tensor
powers, sets `T(n)_e = Spec(D(n)/p^e D(n))`, observes that each `(X, T(n)_e, δ(n))` is an object
of `Cris(X/S)`, and puts

`M(n) = lim_e Γ((X, T(n)_e, δ(n)), F)`,  `n = 0, 1, 2, 3, …`,

a cosimplicial module over the cosimplicial ring `D(0), D(1), D(2), …`.  [Stacks, Tag 07JN]
asserts that, under two hypotheses on `F`, the complex `M(0) → M(1) → M(2) → ⋯` computes
`RΓ(Cris(X/S), F)`; [Stacks, Tag 07LF] deduces that
`H^j(Cris(X/S), F ⊗_{𝒪_{X/S}} Ω^i_{X/S}) = 0` for every `i > 0` and every `j ≥ 0`.

This file writes both statements down.  Neither is proved and **no tag attribute is placed**; the
section "What is and is not proved" below says exactly what is missing for each.  What is built
here is everything the two statements are about: the sheaf `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` at the
coefficient universe in which the cohomology of `Cris(X/S)` exists, the two hypotheses of
[Stacks, Tag 07JN], the cosimplicial module `M(•)` attached to a cosimplicial system of
thickenings of the whole space, and the complex `M(0) → M(1) → M(2) → ⋯`.

## Main definitions

Everything below lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `abelianSheaf` — the abelian sheaf underlying a sheaf of `𝒪_{X/S}`-modules, read in
  `AddCommGrpCat.{u + 1}`, the coefficient universe in which `H^j(Cris(X/S), -)` exists.
* `tensorDifferentialForms` — the presheaf of `𝒪_{X/S}`-modules `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` on
  `Cris(X/S)`, and `tensorDifferentialFormsSheaf` the abelian sheaf it generates, which is what
  `H^j(Cris(X/S), F ⊗_{𝒪_{X/S}} Ω^i_{X/S})` is the cohomology of.
* `IsWholeSpaceSystem` — the condition that a cosimplicial system of objects of `Cris(X/S)`
  consists of thickenings of the whole of `X`, that is, lies in the subcategory `𝒞` of
  [Stacks, Tag 07JK].
* `sectionSystem` and `cosimplicialSections` — **the cosimplicial module `M(•)`**: in degree `n`
  the limit over `e` of the sections of `F` over `(X, T(n)_e, δ(n))`.
* `sectionsComplex` — **the complex `M(0) → M(1) → M(2) → ⋯`**, the alternating coface map
  complex of `M(•)`.
* `ComputesCohomology` — **the conclusion of [Stacks, Tag 07JN]**: the complex
  `M(0) → M(1) → M(2) → ⋯` computes `RΓ(Cris(X/S), F)`, in the graded form available here, namely
  that its cohomology in every degree `j` is `H^j(Cris(X/S), F)`.
* `Vanishing07LF` — **the statement of [Stacks, Tag 07LF]** in full, hypotheses included.

## Main results

* `tensorDifferentialForms_obj` — the sections of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` over an object
  `(U, T, δ)` of `Cris(X/S)` are `F(U, T, δ) ⊗_{Γ(T, 𝒪_T)} Ω^i_{X/S}(U, T, δ)`.
* `tensorDifferentialFormsZeroIso` — `F ⊗_{𝒪_{X/S}} Ω^0_{X/S} = F`, which is why
  [Stacks, Tag 07LF] has to assume `i > 0`.
* `cosimplicialSections_obj` — `M(n)` is the limit over `e` of the sections of `F` over
  `(X, T(n)_e, δ(n))`, and `sectionsComplex_X` — the degree-`n` term of the complex is `M(n)`.
* `vanishing07LF_iff_isZero_rightDerivedGlobalSections` — the vanishing asserted by
  [Stacks, Tag 07LF] is the vanishing of the right derived global sections
  `R^j Γ(Cris(X/S), F ⊗_{𝒪_{X/S}} Ω^i_{X/S})`.
* `subsingleton_cohomology_tensorDifferentialForms_zero_iff` — in degree zero the vanishing is the
  vanishing of the global sections of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}`.

## What is and is not proved

**No tag attribute is placed in this file**, which only writes the two propositions down: the
first as the predicate `ComputesCohomology` applied to a carried system of thickenings, the
second as the proposition `Vanishing07LF`.

Nothing is proved here about [Stacks, Tag 07LF].  [Stacks, Tag 07JN] is proved, and tagged, in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/WholeSpaceSystemCohomology.lean`:
`...SmallSite.computesCohomology_wholeSpaceSystem_of_isSurjectiveComparison` asserts
`ComputesCohomology (wholeSpaceSystem S hp) (abelianSheaf F)` under the affine setting and
hypotheses (1) and (2) of the tag, and under nothing else.  The numbered list below records
the route; each item says where it stands.

`Vanishing07LF` is the complete statement of [Stacks, Tag 07LF]: it quantifies over the affine
situation, over the sheaf `F` and over `i > 0` and `j ≥ 0`, and carries the two hypotheses of
[Stacks, Tag 07JN] as `IsLocallyQuasiCoherent` and
`CohomologyRestriction.IsSurjectiveComparison`.  Nothing in its formulation is deferred.

`ComputesCohomology` is the complete *conclusion* of [Stacks, Tag 07JN], but the statement of
that tag is about one specific cosimplicial system of thickenings — the `(X, T(n)_e, δ(n))` built
from a polynomial presentation of `C`.  That system is constructed as
`Crystalline.GlobalCrystallineSituation.SmallSite.wholeSpaceSystem` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AffineCosimplicialSystem.lean`, assuming `X`
and `S` affine and `p` nilpotent on `Γ(X, ⊤)`; so `ComputesCohomology` applies to it, and the
predicate is proved for it in `WholeSpaceSystemCohomology.lean`.  `ComputesCohomology` is a predicate on a system carried as a parameter, and
the statement of [Stacks, Tag 07JN] is: for the source's system, and for `F` satisfying the two
hypotheses, the predicate holds.  It is emphatically *not* asserted anywhere for an arbitrary
system, for which it is false (a constant system satisfies `IsWholeSpaceSystem` and computes the
wrong groups).

Much of the machinery the source's proof of [Stacks, Tag 07JN] runs on *is* in the library, on
the affine ring-theoretic side, where it is stated for a
`Crystalline.AffineCrystallineSituation` ([Stacks, Tag 07MD]) — a divided power triple `(A, I, γ)`
with a map `A/I → C` — and for the little affine crystalline category
`Crystalline.CrystallineThickening` and its completion
`Crystalline.CompletedCrystallineThickening`, both with the chaotic topology:

* [Stacks, Tag 07JM], `Stacks.Cohomology.nonempty_addEquiv_sheafH_homology_powerCechComplex`: on a
  chaotic site with an object `X` every object maps to and in which the powers `X^{n + 1}` exist,
  the cohomology of an abelian sheaf is the cohomology of `𝓕(X) → 𝓕(X × X) → ⋯`.  This is the
  engine of the proof.  It asks the site to be small, and not to have products of pairs: its
  proof forms no product but the powers of `X`.  This is what makes the engine applicable to `Cris^∧(C/A)`, where the powers of the generator are the `D(n)` of
  [Stacks, Tag 07L4] but coproducts of arbitrary pairs are unavailable.
* [Stacks, Tag 07JL], `Crystalline.completedCrystallineToposMorphism` and
  `Crystalline.abelianSheafPushforward`, with `Crystalline.finiteLevelSections` the inverse system
  `e ↦ Γ(T_e, F)` whose limit the direct image is in the source — that identification is not
  proved in this library, see item 2 below: the morphism of topoi along which the source
  passes from `Cris(C/A)` to `Cris^∧(C/A)`, where the object `D` lives.
* [Stacks, Tag 07L4], `Crystalline.completedEnvelope_isCoproduct`: `D(n)` is the `(n + 1)`-fold
  coproduct of `D` in `Cris^∧(C/A)`, with `Crystalline.tensorPowerEnvelopeThickening` the object
  `D(n)` and `Crystalline.completedEnvelopeCoprojection` the coprojections.
* [Stacks, Tag 07KI], `Crystalline.exists_hom_from_completedPolynomialEnvelope`: `D` is a
  generator, every completed thickening receiving a morphism from it.
* [Stacks, Tag 07LA], `Crystalline.id_completedTensorCompletedForms_homotopic_zero`: for `i > 0`
  the cosimplicial module `M_* ⊗̂_{D(*)} Ω^i_{D(*)}` is homotopic to zero.  This is the engine of
  the proof of [Stacks, Tag 07LF].
* [Stacks, Tag 07JK],
  `Crystalline.GlobalCrystallineSituation.SmallSite.chaoticCohomologyComparisonIso`: the
  comparison `H^j(𝒞, F|_𝒞) ≅ H^j(Cris(X/S), F)` for the chaotic topology on `𝒞`, the last step
  of the source's proof.

The route, item by item.  Items 1 to 4 are the route to [Stacks, Tag 07JN], and all four are
complete; items 5 and 6 are the extra input [Stacks, Tag 07LF] needs, and are still missing.

1. The cosimplicial system of thickenings `(X, T(n)_e, δ(n))` as objects of the global site, in
   `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AffineCosimplicialSystem.lean`:
   `Crystalline.GlobalCrystallineSituation.SmallSite.wholeSpaceSystem` is `D(n)` and its
   coprojections carried across
   `Crystalline.GlobalCrystallineSituation.wholeSiteEquivLittleAffine`, and
   `Crystalline.GlobalCrystallineSituation.SmallSite.isWholeSpaceSystem_wholeSpaceSystem` is the
   proof that it is an `IsWholeSpaceSystem`.  So `ComputesCohomology` below applies to a
   constructed system.
2. The vanishing `R^p g_*(F|_𝒞) = 0` for `p ≥ 1`, `g` the morphism of topoi of
   [Stacks, Tag 07JL].  The source derives it in two moves: hypothesis (2), together with the
   vanishing of `H^1(T', 𝒦)` on an affine `T'`, makes the transition maps of the inverse systems
   `e ↦ Γ(T_e, F)` of [Stacks, Tag 07JL] surjective; and a system with surjective transition maps
   has vanishing derived limits in positive degrees.

   The **second** move is in
   `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CompletedPushforwardVanishing.lean`:
   `Crystalline.isZero_firstDerivedLimit_finiteLevelSections` and
   `Crystalline.isZero_homology_rightDerivedLimit_finiteLevelSections` for the affine-side system
   `Crystalline.finiteLevelSections`, and
   `Crystalline.GlobalCrystallineSituation.SmallSite.isZero_firstDerivedLimit_sectionSystem` and
   `...isZero_homology_rightDerivedLimit_sectionSystem` for the systems of level sections whose
   limits are the terms `M(n)` below.  Two things remain.

   The **first** move is proved too.  Hypothesis (2) is `CohomologyRestriction.IsSurjectiveComparison`: local
   surjectivity of `c_f : f^*F_{T'} ⟶ F_T`.  The source passes from it to surjectivity of
   `F_{T'} ⟶ f_*F_T`, calling the two equivalent; the comparison
   `Crystalline.GlobalCrystallineSituation.Thickening.range_moduleComparison_app` bounds the
   image of the `f`-map by the image of `c_f` — the opposite inclusion.  The needed inclusion is
   `...CohomologyRestriction.range_moduleComparison_app_eq_range_map_restrictOpenMap` and the
   implication itself `...isLocallySurjective_moduleFMap_of_isIso_toX`, both in
   `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/FMapSurjectivity.lean`, which carry no
   extra hypothesis for a closed immersion inside `𝒞`; the general form is
   `PresheafOfModules.range_homEquivSymm_app_eq_range_appₛₗ` of
   `StacksFrontier/Algebra/Category/ModuleCat/Presheaf/PullbackSectionsCollapse.lean`.

   A description of the pullback of a presheaf of modules as a tensor product is not needed for
   this step.  That description exists in full generality, as `Stacks.PullbackColimit.pullbackObjIso` of
   `StacksFrontier/Algebra/Category/ModuleCat/Presheaf/PullbackColimit.lean`, and it is not what the
   step needs: the step is about an image, which the adjunction already determines, so it goes
   through with only fullness of the functor of sites and surjectivity of the ring map, in
   `RingCat` generality.  That matters because the colimit route additionally wants
   `CommRingCat`-valued presheaves, and `moduleComparison` is declared over the `RingCat`-valued
   `crisRing`.

   The global surjectivity the source actually consumes, `Γ(T', F_{T'}) ⟶ Γ(T, F_T)` for affine
   `T'`, follows and is
   `...CohomologyRestriction.surjective_sections_fmapModuleRestriction_of_isIso_toX` of
   `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/FMapGlobalSurjectivity.lean`, under
   hypotheses (1) and (2) of the tag and nothing else.  Everything it assembles is
   available: the kernel of a map of quasi-coherent modules is quasi-coherent
   (`Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel`), the direct image along a closed
   immersion is quasi-coherent
   (`...AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom`, [Stacks, Tag 02KG]), `H^1`
   of a quasi-coherent module on an affine vanishes
   (`Crystalline.GlobalCrystallineSituation.SmallSite.isZero_cohomology_restriction_of_isAffine`
   and `Stacks.Cohomology.AffineOpen.isZero_hgroup_of_isAffine`, [Stacks, Tag 07JJ] and
   [Stacks, Tag 01XB]), and a surjection of quasi-coherent modules over an affine open is
   surjective on sections (`Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen`); the ambient
   scheme of an object over the whole of an affine `X` is affine by
   `...SmallSite.isAffine_target_of_isAffine_source`.  The one remaining piece is a
   bridge rather than mathematics — those results are stated for `Scheme.Modules` over
   `X.ringCatSheaf` while the `f`-map lives in presheaves of modules over `crisRing`, and that the
   `f`-map of the structure presheaf is the comorphism of `T ⟶ T'` is
   `...CohomologyRestriction.sectionsIso_inv_restrictionFMap_apply`.

   Second, the vanishing is first obtained in the `R^p lim` spelling; the identification of
   `R^p g_*` with `R^p lim_e` is the computation half of [Stacks, Tag 07JL], the other half being
   the morphism of topoi.  Its cofinality input, the initiality of the finite-level diagram in the
   structured-arrow category that computes the right Kan extension, is
   `StacksFrontier/AlgebraicGeometry/Crystalline/AffineCrystallineSite/FiniteLevelCofinality.lean`,
   and with it the computation half of [Stacks, Tag 07JL] is proved in
   `StacksFrontier/AlgebraicGeometry/Crystalline/AffineCrystallineSite/CompletedToposMorphism.lean`.
   The divided-power gluing behind `HasBinaryProducts (Thickening S)` is
   `StacksFrontier/AlgebraicGeometry/Crystalline/DividedPowerGluing.lean`.  In
   `kernelSubmoduleIsLimit` there the implicit argument `(f := f)` is written out, because the
   `KernelFork.ofι` argument is otherwise solved only inside its own `by` block, after `ext` has
   run on a goal containing metavariables.

   **The vanishing holds in the `g_*` spelling and not merely in the `R^p lim` one.**  It
   is
   `Crystalline.isZero_rightDerived_abelianSheafPushforward_of_surjective` of
   `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LevelLimitNaturality.lean`, for an
   abelian sheaf whose level restrictions are surjective; and the surjectivity it asks for is
   derived from hypotheses (1) and (2) of [Stacks, Tag 07JN] by
   `...SmallSite.surjective_affineSections_finiteLevelSystem_transition` of
   `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LevelRestrictionSurjectivity.lean`.
3. Smallness of the sites: **settled**, in `SmallSite/CompletedCechDescent.lean`.  The sizes do
   **not** agree on the affine side — an object of
   `Cris^∧(C/A)` bundles a `DividedPowerRing`, hence its own carrier, so the objects form a
   `Type (max u v (t + 1))` while the morphisms form a `Type t`, exactly the global mismatch.  It
   dissolves for an unrelated reason: Lean's `SmallCategory` requires only that objects and
   morphisms share a universe, not that the category be a small set, and `CategoryTheory.AsSmall`
   always arranges that — here with common universe the very coefficient universe of
   `Crystalline.abelianSheafPushforward`, so nothing is lost.  [Stacks, Tag 07JM] is already *run*
   on that model, as `Crystalline.nonempty_addEquiv_sheafH_homology_powerCechComplex_generator`,
   over the site `Crystalline.CompletedSmallSite` with
   `Crystalline.completedSmallSheafToposEquivalence` identifying the two sheaf topoi.  Note that
   only the *morphisms* are `t`-small, by Mathlib's `small_self`, a morphism type being a
   `Type t`; `Small.{t}` of the objects is not claimed, and is false.
4. The descent of [Stacks, Tag 07JM] to `𝒞` reduces to one proposition.  Two of its three
   ingredients are proved in `SmallSite/CompletedDirectImageLevels.lean`: the two finite-level diagrams
   are the same diagram, not merely cofinal ones (`Crystalline.uniformLevelSystem` with
   `diagram_uniformLevelSystem` and `finiteLevelSections_uniformLevelSystem`, both `rfl`), and the
   comparison is natural in `B` (`Crystalline.directImageIsoLevelLimit`, an isomorphism of
   functors, carried to the direct image of [Stacks, Tag 07JL] by
   `Crystalline.abelianDirectImageIsoLevelLimitPresheaf`).  So this tag's coefficient presheaf *is*
   `g_*(F|_𝒞)`, by `...SmallSite.levelLimitSectionsIsoDirectImage`, and
   `...SmallSite.computesCohomology_wholeSpaceSystem_of_directImage` gives [Stacks, Tag 07JN] for
   `wholeSpaceSystem` conditional on `...SmallSite.IsDirectImageCohomologyComparison`, namely
   `H^j(𝒞^∧, g_*(F|_𝒞)) ≅ H^j(Cris(X/S), F)`.  That proposition is the source's two remaining
   moves: the Leray degeneration, which needs the *derived* half of [Stacks, Tag 07JL]
   (`R^p g_* ≅ R^p lim_e`, which the degree-zero isomorphism does not upgrade to) and
   `EnoughInjectives` for the chaotic abelian sheaves on the affine-side sites; and the transport of
   the cohomology of `𝒞` across `wholeSiteEquivLittleAffine` and the small model, which needs an
   equivalence-invariance lemma for `Sheaf.H`.

   All three inputs are supplied — the first by `Crystalline.lerayPushforwardRightDerivedSectionsIso` and
   `Crystalline.sheafHAddEquivPushforward_of_surjective` of `SmallSite/LevelLimitNaturality.lean`,
   which run the Leray degeneration off the vanishing of item 2 rather than off an isomorphism of
   derived functors; the second by running the engine on the small model, as item 3 records; the
   third by `Stacks.ChaoticSite.sheafHAddEquivOfEquivalence` through
   `Crystalline.smallSheafHAddEquivCompletedChaotic` and
   `...SmallSite.littleChaoticCohomologyComparison` of `SmallSite/AffineChaoticCohomology.lean`.
   So `...SmallSite.isDirectImageCohomologyComparison_of_leray` and
   `...SmallSite.isCompletedLerayComparison_of_surjective` discharge the proposition, and
   `...SmallSite.computesCohomology_wholeSpaceSystem_of_isSurjectiveComparison` of
   `SmallSite/WholeSpaceSystemCohomology.lean` is [Stacks, Tag 07JN].

   The geometry of the descent: it runs from `Cris^∧(C/A)`, where the generator `D` of
   [Stacks, Tag 07KI] lives, to `𝒞`, along the morphism of topoi of [Stacks, Tag 07JL].  `𝒞`
   itself has no weakly terminal object, for the reason recorded in
   `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AffineGlobalLimits.lean`, so the engine
   cannot be run on it directly.

For [Stacks, Tag 07LF] the proof of the source needs, besides [Stacks, Tag 07JN]:

5. [Stacks, Tag 07KM] part (1), that `Ω_{X/S}` is locally quasi-coherent, is now in the library,
   as `Crystalline.GlobalCrystallineSituation.crysDifferentials_isLocallyQuasiCoherent` of
   `StacksFrontier/AlgebraicGeometry/Crystalline/DifferentialsLocallyQuasicoherent.lean`, where it
   carries the tag; this note previously said it was absent.  Part (2), the surjectivity of the
   comparison map along a closed immersion, is, as
   `Crystalline.GlobalCrystallineSituation.isLocallySurjective_moduleComparison`, but on the big
   crystalline category and for `Ω_{X/S}` rather than for `F ⊗ Ω^i_{X/S}`.  Together these give
   the two hypotheses of [Stacks, Tag 07JN] for `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}`, which is the first
   step of the proof.
6. The identification of `M(n)` for `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` with
   `lim_e (M(n)_e ⊗_{D(n)} Ω^i_{D(n)})`, which needs (1).

## Implementation notes

The coefficient universe of the cohomology of `Cris(X/S)` is `u + 1`, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Cohomology.lean`: the objects of the site
form a `Type (u + 1)` while its morphisms form a `Type u`, and sheafification of
`AddCommGrpCat.{u}`-valued presheaves on it is not available.  A sheaf of `𝒪_{X/S}`-modules has
its modules in `Type u`, so its underlying abelian sheaf is pushed up one universe by
`AddCommGrpCat.uliftFunctor`, which preserves limits of every size and therefore carries sheaves
to sheaves.  Universe lifting is an equivalence onto a full subcategory of abelian groups and in
particular carries the zero group to the zero group, so the vanishing statements below say what
they should.

`F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` is formed as the *presheaf* tensor product and then sheafified.  This
is the sheaf the source means: `Ω_{X/S}` is modelled in this library as a presheaf of modules and
is not a sheaf — over an object `(U, T, δ)` its restriction to `T` has the divided power
differentials `Ω_{T/S,δ}` as its associated sheaf, which is [Stacks, Tag 07IZ] — and
sheafification turns a presheaf tensor product into the tensor product of the sheafifications, so
sheafifying `F ⊗ Ω^i_{X/S}` gives the tensor product of `F` with the sheaf of crystalline
`i`-forms either way.  Sheafification is applied to the underlying abelian presheaf rather than to
the presheaf of modules, the two agreeing because the forgetful functor from sheaves of modules to
abelian sheaves commutes with sheafification; the abelian sheaf is what the cohomology functor
consumes.

The cosimplicial system of thickenings is carried as a
`CategoryTheory.SimplicialObject (ℕ ⥤ CrystallineThickening S)`: contravariant in the simplicial
direction because `D(0) → D(1) → D(2) → ⋯` is a cosimplicial *ring*, so the spectra go the other
way and `(X, T(n)_e, δ(n))` is simplicial in `n` as an object of `Cris(X/S)`; and covariant in
`e`, because `D(n)/p^e` is a quotient of `D(n)/p^{e + 1}` and so `T(n)_e ⟶ T(n)_{e + 1}` is a
closed immersion.  Taking sections of a presheaf reverses the first direction and the second, so
`M(n) = lim_e Γ((X, T(n)_e, δ(n)), F)` is cosimplicial in `n`, as the source says.

## References

* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Tag 07JK](https://stacks.math.columbia.edu/tag/07JK)
* [Stacks Project, Tag 07KM](https://stacks.math.columbia.edu/tag/07KM)
* [Stacks Project, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
* [Stacks Project, Tag 07J4](https://stacks.math.columbia.edu/tag/07J4)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07MD](https://stacks.math.columbia.edu/tag/07MD)
* [Stacks Project, Tag 07KI](https://stacks.math.columbia.edu/tag/07KI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Opposite Simplicial

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}}

/-! ### The sheaf `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` -/

/-- **The abelian sheaf underlying a sheaf of `𝒪_{X/S}`-modules on the small crystalline site**,
read at the coefficient universe `u + 1` in which `H^j(Cris(X/S), -)` exists.  Universe lifting
preserves limits of every size, so it carries abelian sheaves to abelian sheaves. -/
def abelianSheaf (F : SheafOfModules.{u} (structureSheaf S)) :
    Sheaf (smallTopology S) AddCommGrpCat.{u + 1} :=
  (sheafCompose (smallTopology S) AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
    ((SheafOfModules.toSheaf (structureSheaf S)).obj F)

/-- **The presheaf of `𝒪_{X/S}`-modules `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` on the small crystalline
site**, the tensor product of a presheaf of `𝒪_{X/S}`-modules with the presheaf of crystalline
`i`-forms of [Stacks, Tag 07J4].  Its sections over an object are the tensor product of the
sections of the two factors there, by `tensorDifferentialForms_obj`. -/
def tensorDifferentialForms
    (M : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) (i : ℕ) :
    PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat) :=
  M ⊗ crysDifferentialForms S i

/-- **The sections of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` over an object `(U, T, δ)` of `Cris(X/S)` are
`F(U, T, δ) ⊗_{Γ(T, 𝒪_T)} Ω^i_{X/S}(U, T, δ)`.** -/
theorem tensorDifferentialForms_obj
    (M : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) (i : ℕ)
    (A : (CrystallineThickening S)ᵒᵖ) :
    (tensorDifferentialForms M i).obj A = M.obj A ⊗ (crysDifferentialForms S i).obj A :=
  PresheafOfModulesOfCommRing.tensorObj_obj _ _ A

/-- **`F ⊗_{𝒪_{X/S}} Ω^0_{X/S} = F`.**  The crystalline forms of degree zero are the structure
sheaf, `crysFormsZeroIso`, which is the unit of the tensor product of presheaves of modules.  This
is why [Stacks, Tag 07LF] has to assume `i > 0`: in degree zero its conclusion would be the
vanishing of `H^j(Cris(X/S), F)` itself, which is false. -/
def tensorDifferentialFormsZeroIso
    (M : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) :
    tensorDifferentialForms M 0 ≅ M :=
  whiskerLeftIso M (crysFormsZeroIso S).symm ≪≫ ρ_ M

/-- **The abelian sheaf `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` on the small crystalline site**, the
sheafification of the underlying abelian presheaf of the tensor product, read at the coefficient
universe `u + 1`.  This is the sheaf whose cohomology [Stacks, Tag 07LF] asserts to vanish. -/
def tensorDifferentialFormsSheaf (F : SheafOfModules.{u} (structureSheaf S)) (i : ℕ) :
    Sheaf (smallTopology S) AddCommGrpCat.{u + 1} :=
  (presheafToSheaf (smallTopology S) AddCommGrpCat.{u + 1}).obj
    ((PresheafOfModules.toPresheaf _).obj
        (tensorDifferentialForms
          (F.val : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i) ⋙
      AddCommGrpCat.uliftFunctor.{u + 1, u})

/-! ### The statement of [Stacks, Tag 07LF] -/

/-- **The statement of [Stacks, Tag 07LF].**  With `X` and `S` affine, for a sheaf of
`𝒪_{X/S}`-modules `F` on the small crystalline site which is locally quasi-coherent and whose
comparison morphisms along closed immersions are surjective — the two hypotheses of
[Stacks, Tag 07JN] — the cohomology groups

`H^j(Cris(X/S), F ⊗_{𝒪_{X/S}} Ω^i_{X/S})`

vanish for every `i > 0` and every `j ≥ 0`.

This is a proposition, not a theorem: nothing below proves it, and the module docstring lists the
ingredients its proof is missing. -/
def Vanishing07LF (S : GlobalCrystallineSituation.{u}) : Prop :=
  IsAffine S.X → IsAffine S.S.scheme →
    ∀ F : SheafOfModules.{u} (structureSheaf S), IsLocallyQuasiCoherent F →
      CohomologyRestriction.IsSurjectiveComparison F.val →
        ∀ i j : ℕ, 0 < i → Subsingleton (cohomology S (tensorDifferentialFormsSheaf F i) j)

/-- **The vanishing asserted by [Stacks, Tag 07LF] is the vanishing of the right derived global
sections** `R^j Γ(Cris(X/S), F ⊗_{𝒪_{X/S}} Ω^i_{X/S})`, cohomology on the small crystalline site
being the right derived functor of global sections. -/
theorem vanishing07LF_iff_isZero_rightDerivedGlobalSections (S : GlobalCrystallineSituation.{u}) :
    Vanishing07LF S ↔
      (IsAffine S.X → IsAffine S.S.scheme →
        ∀ F : SheafOfModules.{u} (structureSheaf S), IsLocallyQuasiCoherent F →
          CohomologyRestriction.IsSurjectiveComparison F.val →
            ∀ i j : ℕ, 0 < i →
              IsZero (((globalSections S).rightDerived j).obj
                (tensorDifferentialFormsSheaf F i))) := by
  simp only [Vanishing07LF, subsingleton_cohomology_iff_isZero_rightDerivedGlobalSections]

/-- **In degree zero the vanishing of [Stacks, Tag 07LF] is the vanishing of the global sections
of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}`**, since `H^0(Cris(X/S), -) = Γ(Cris(X/S), -)`. -/
theorem subsingleton_cohomology_tensorDifferentialForms_zero_iff
    (F : SheafOfModules.{u} (structureSheaf S)) (i : ℕ) :
    Subsingleton (cohomology S (tensorDifferentialFormsSheaf F i) 0) ↔
      IsZero ((globalSections S).obj (tensorDifferentialFormsSheaf F i)) := by
  rw [subsingleton_cohomology_iff_isZero_rightDerivedGlobalSections]
  exact Iso.isZero_iff
    (((globalSections S).rightDerivedZeroIsoSelf).app (tensorDifferentialFormsSheaf F i))

/-! ### The cosimplicial module `M(•)` and the complex `M(0) → M(1) → M(2) → ⋯` -/

/-- **The condition that a cosimplicial system of objects of `Cris(X/S)` consists of thickenings
of the whole of `X`**, that is, lies in the subcategory `𝒞` of [Stacks, Tag 07JK].  The source's
objects `(X, T(n)_e, δ(n))` have this property, their map to `X` being the identity. -/
def IsWholeSpaceSystem (T : SimplicialObject (ℕ ⥤ CrystallineThickening S)) : Prop :=
  ∀ n e : ℕ, IsOverWholeSpace S ((T.obj (op ⦋n⦌)).obj e)

/-- The inverse system `e ↦ Γ((X, T(n)_e, δ(n)), F)` of sections of a presheaf over the levels of
the `n`-th member of a cosimplicial system of thickenings, as a functor of `n`.  Its limit in each
degree is the cosimplicial module `M(•)`. -/
def sectionSystem (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    (F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    SimplexCategory ⥤ (ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1}) where
  obj n := (T.obj (op n)).op ⋙ F
  map φ := Functor.whiskerRight (NatTrans.op (T.map φ.op)) F
  map_id n := by ext e; simp
  map_comp φ ψ := by ext e; simp

/-- **The cosimplicial module `M(•)` of the source's section on cohomology in the affine case**:
in degree `n` it is `M(n) = lim_e Γ((X, T(n)_e, δ(n)), F)`.  The simplicial direction of the
system of thickenings is reversed by taking sections, so this is cosimplicial. -/
def cosimplicialSections (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    (F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    CosimplicialObject AddCommGrpCat.{u + 1} :=
  sectionSystem T F ⋙ lim

/-- **`M(n)` is the limit over `e` of the sections of `F` over `(X, T(n)_e, δ(n))`.** -/
theorem cosimplicialSections_obj (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    (F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ) :
    (cosimplicialSections T F).obj ⦋n⦌ = limit ((T.obj (op ⦋n⦌)).op ⋙ F) := rfl

/-- **The complex `M(0) → M(1) → M(2) → ⋯`** of the source's section on cohomology in the affine
case: the alternating coface map complex of the cosimplicial module `M(•)`. -/
def sectionsComplex (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    (F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    CochainComplex AddCommGrpCat.{u + 1} ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).obj
    (cosimplicialSections T F)

/-- **The degree-`n` term of the complex `M(0) → M(1) → M(2) → ⋯` is `M(n)`.** -/
theorem sectionsComplex_X (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    (F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ) :
    (sectionsComplex T F).X n = (cosimplicialSections T F).obj ⦋n⦌ := rfl

/-- **The conclusion of [Stacks, Tag 07JN]**: the complex `M(0) → M(1) → M(2) → ⋯` *computes*
`RΓ(Cris(X/S), F)`, in the graded form in which crystalline cohomology is available here, namely
that its cohomology in degree `j` is `H^j(Cris(X/S), F)` for every `j`.

This is a predicate on the pair consisting of the cosimplicial system of thickenings and the
abelian sheaf.  [Stacks, Tag 07JN] asserts it for the system `(X, T(n)_e, δ(n))` attached to a
polynomial presentation of `C` and for a sheaf satisfying the hypotheses `IsLocallyQuasiCoherent`
and `CohomologyRestriction.IsSurjectiveComparison`; that system is not constructed in this
library, and the predicate is false for a general system, so nothing below asserts it. -/
def ComputesCohomology (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) : Prop :=
  ∀ j : ℕ, Nonempty ((sectionsComplex T F.obj).homology j ≅ (cohomologyFunctor S j).obj F)

/-- In degree zero the conclusion of [Stacks, Tag 07JN] says that the cohomology of the complex
`M(0) → M(1) → M(2) → ⋯` in degree zero is the global sections `Γ(Cris(X/S), F)`, since
`H^0(Cris(X/S), -) = Γ(Cris(X/S), -)`. -/
theorem computesCohomology_zero_iso (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (h : ComputesCohomology T F) :
    Nonempty ((sectionsComplex T F.obj).homology 0 ≅ (globalSections S).obj F) :=
  ⟨(h 0).some ≪≫ (cohomologyFunctorZeroIso S).app F⟩

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
