module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafIsos
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalRestrictionTensor
public import StacksFrontier.Algebra.Homology.RestrictScalarsHomology
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.StandardCoverVanishing
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FormsRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SheafCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SheafifySections
public import StacksFrontier.CategoryTheory.Sites.CechComplexCoefficientChange

/-!
# [Stacks, Tag 07JJ] for the coefficient sheaf `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` of [Stacks, Tag 07LF]

Fix a global crystalline situation `(p, (S, I, γ), X)` and a sheaf of `𝒪_{X/S}`-modules `F` on the
small crystalline site which is **locally quasi-coherent** — hypothesis (1) of
[Stacks, Tag 07JN].  This module proves, for every `i : ℕ`,

`...SmallSite.Vanishing07JJ S (...SmallSite.tensorDifferentialFormsSheaf F i)`,

the conclusion of [Stacks, Tag 07JJ] for the coefficient sheaf `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` of
[Stacks, Tag 07LF]: for every object `(U, T, δ)` of `Cris(X/S)` with `T` affine and every `p > 0`,

`H^p(Cris(X/S)/(U, T, δ), F ⊗_{𝒪_{X/S}} Ω^i_{X/S}) = 0`.

The route is the one
`...SmallSite.vanishing07JJ_tensorDifferentialFormsSheaf_of_isZero_cechHomology` reduces the
statement to, and the work is to exhibit, over an object with affine ambient scheme `T`, a Zariski
sheaf on `T` with vanishing positive-degree Čech cohomology on a standard open cover and a
Zariski-locally bijective morphism to it from the restriction of the presheaf tensor product.  The
sheaf is the associated sheaf, over the restriction of `𝒪_{X/S}` to the opens of `T`, of

`W ↦ F(A|_W) ⊗_{Γ(W, 𝒪_T)} Ω^i_{X/S}(A|_W)`,

and the morphism is its sheafification unit, read at the coefficient universe `u + 1`.  Its
quasi-coherence comes from [Stacks, Tag 03L6] through [Stacks, Tag 0GMW], and its Čech vanishing
from [Stacks, Tag 01X9].

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `restrictedCommRing` and `restrictedCommRingSheaf` — the restriction of `𝒪_{X/S}` to the opens
  of the ambient scheme of an object, as a presheaf and then as a sheaf of **commutative** rings.
  `Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheaf` is its underlying sheaf
  of rings, by `toRingCat_restrictedCommRingSheaf`.
* `restrictedModule` — the restriction to `T` of a presheaf of `𝒪_{X/S}`-modules on `Cris(X/S)`,
  spelled over `restrictedCommRing`.
* `restrictedCoefficientSheaf` — the restriction `F_T` of a sheaf of `𝒪_{X/S}`-modules, at the
  `CategoryTheory.Sheaf.toRingCat` spelling of the sheaf of rings.
* `tensorRestriction` and `tensorRestrictionSheaf` — the restriction to `T` of
  `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` as a presheaf of modules over the restriction of `𝒪_{X/S}`, and its
  associated sheaf.

## Main results

* `restrictedModule_tensorObj` — **restriction to `T` commutes with the objectwise tensor product**
  of presheaves of modules, for Mathlib's monoidal tensor product, which is the one
  `...SmallSite.tensorDifferentialForms` is built with.
* `isQuasicoherentOnSite_tensorRestrictionSheaf` — **the associated sheaf of the restriction of
  `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` is quasi-coherent**, for a locally quasi-coherent `F`.
* `isZero_cechHomology_tensorRestrictionSheaf` and `isZero_cechHomology_ulift` — the vanishing of
  its positive-degree Zariski Čech cohomology on a standard open cover of an affine `T`, at the
  module universe `u` and then at the coefficient universe `u + 1`.
* `vanishing07JJ_tensorDifferentialFormsSheaf` — **the conclusion of [Stacks, Tag 07JJ] for
  `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}`**, with `IsLocallyQuasiCoherent F` the only hypothesis.

## What is and is not proved

`vanishing07JJ_tensorDifferentialFormsSheaf` is proved in full.  The **only** hypothesis carried
is `hF : ...SmallSite.IsLocallyQuasiCoherent F`, which is hypothesis (1) of [Stacks, Tag 07JN];
there is no affineness assumption on `X` or `S`, no hypothesis on `i`, and nothing about the
crystal condition or about surjectivity of comparison maps.  So the hypothesis `h` of
`...SmallSite.vanishing07JJ_tensorDifferentialFormsSheaf_of_isZero_cechHomology` is discharged,
and `...SmallSite.Vanishing07JJ` is **unconditional** for the coefficient sheaf of
[Stacks, Tag 07LF] given hypothesis (1) of [Stacks, Tag 07JN].

**No tag attribute is placed.**  [Stacks, Tag 07JJ] is already carried, on its covering set, by
`...SmallSite.vanishing07JJ_abelianSheaf` and
`...SmallSite.isZero_overCohomology_abelianSheaf_of_isAffine` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/StandardCoverAcyclicity.lean`, for a locally
quasi-coherent module; what is proved here is that conclusion at one particular abelian sheaf, not
a further clause of the tag, and tagging it would register one result twice.  **No
`@[stacks 07LF]` is placed here either**: [Stacks, Tag 07LF] is proved, and carries its tag, at
`...SmallSite.vanishing07LF` of `SmallSite/LevelFormsCosimplicialIso.lean`; what this file
contributes is one of its inputs.  The survey below records how that proof was assembled.

### What this closes, and what it invalidates

The "What is and is not proved" note of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/FormsRestrictionQuasicoherent.lean` lists
four steps still owed for input (1) of [Stacks, Tag 07LF], says that "none of these four is proved
here", and says that that module "does not discharge the hypothesis `h` of
`...SmallSite.vanishing07JJ_tensorDifferentialFormsSheaf_of_isZero_cechHomology`, and therefore
does not make `...SmallSite.Vanishing07JJ` unconditional for the tensor sheaf".  All four steps
are now closed and `h` is discharged, so that last sentence is no longer the state of the library.
Two of the four were, moreover, **not** missing, contrary to what that note says:

1. The note says that restriction commuting with the objectwise tensor product is in the library
   by `rfl` for the mixed-universe `Stacks.tensorObj` and that "what is owed is the same statement
   for Mathlib's monoidal `PresheafOfModules.Monoidal.tensorObj` ... and the bridge between the two
   objectwise tensor products".  Both already existed.  Mathlib carries the monoidal structure of
   the restriction functor itself, as the instance of
   `Mathlib/Algebra/Category/ModuleCat/Presheaf/PushforwardZeroMonoidal.lean`, whose multiplication
   isomorphism has identity components; the equality of objects is
   `Stacks.MonoidalRestrictionTensor.restrictModules_tensorObj`, instantiated here as
   `restrictedModule_tensorObj`.  The bridge between the two objectwise tensor products is
   `Stacks.SheafOfModules.TensorEncodings.tensorObj_eq_tensorObj` and
   `...tensorObj_eq_tensor`, both `rfl`.
2. [Stacks, Tag 05NA] at the restricted spelling is used here in the form that the two factors
   actually have — one sheaf and one presheaf — namely
   `PresheafOfModules.tensorSheafifyMixedIso`, which is [Stacks, Tag 0GMW] with the first factor a
   sheaf.  The restricted spelling of the ring is fixed once, in `restrictedCommRing`.
3. The note calls the comparison between the tensor sheaf of [Stacks, Tag 05NA],
   `Stacks.SheafOfModules.TensorSheafification.tensorSheaf`, and the
   `PresheafOfModules.tensorSheafBifunctor` that [Stacks, Tag 03L6] is stated for, "likely the
   hardest of the four", and says "the library has no comparison".  **The library does have it**:
   `Stacks.TensorSheafWorld.tensorSheafBifunctor_obj_eq` of
   `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorSheafWorldBridge.lean` is exactly that
   comparison, by `rfl`, and `Stacks.SheafOfModules.TensorEncodings.tensorSheafBifunctor_eq`
   records the same for a third spelling.  In the event no transport is needed at all here: the
   route through [Stacks, Tag 0GMW] in step 2 lands directly in the
   `PresheafOfModules.tensorSheafBifunctor` world that [Stacks, Tag 03L6] speaks about.
4. The coefficient-universe passage `u → u + 1` for [Stacks, Tag 01X9] is
   `isZero_cechHomology_ulift` below, the only one of the four that needed work, and not much:
   `Stacks.CategoryTheory.CechComplex.isZero_homology_mapCoeff_iff` turns the Čech complex of
   `Z ⋙ AddCommGrpCat.uliftFunctor` into the universe lift of the Čech complex of `Z`, and
   `Stacks.Homology.RestrictScalars.mapHomologicalComplexHomologyIso` moves its homology inside the
   lift.  The local bijectivity of the lifted sheafification unit is
   `CategoryTheory.Presheaf.isLocallyInjective_whiskerRight_uliftFunctor` and its surjective
   sibling, as that note predicted.

The "What is and is not proved" note of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/SheafifySections.lean` says that for input (1)
of [Stacks, Tag 07LF] the exterior-power form of [Stacks, Tag 07KM] part (1) is owed — "the library
has clause (1) only for `Ω_{X/S}` itself" — that quasi-coherence of a tensor product on an affine
is owed, and that the passage between the `ModuleCat`-valued picture and the universe-lifted
`AddCommGrpCat.{u + 1}`-valued picture is owed; and that "only with those does [Stacks, Tag 01X9]
apply", which is the hypothesis of
`vanishing07JJ_tensorDifferentialFormsSheaf_of_isZero_cechHomology`.  All three are
available — the first as `...crysDifferentialForms_isLocallyQuasiCoherent`, the second as
[Stacks, Tag 03L6], the third as
`isZero_cechHomology_ulift` below — and that hypothesis is discharged.  The docstring of
`vanishing07JJ_tensorDifferentialFormsSheaf_of_isZero_cechHomology` itself says that the
quasi-coherence of the forms factor is what "the library does not have for `i ≠ 1`"; the
library does have it, as `...crysDifferentialForms_isLocallyQuasiCoherent`, and the clause
"and nothing here proves `h`" in the same docstring is true of that file but not of the
library.

### What still blocks [Stacks, Tag 07LF]

Input
(2) of [Stacks, Tag 07JN] for this coefficient sheaf is
`...SmallSite.hasSurjectiveWholeSpaceTransitions_tensorDifferentialFormsSheaf` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/TensorSheafGlobalSections.lean`, and the
cosimplicial divided power envelope of the source's proof is
`...SmallSite.wholeSpaceEnvelope` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/WholeSpaceEnvelope.lean`, a term of type
`Crystalline.CosimplicialEnvelope`.  With
`...SmallSite.vanishing07LF_of_levelCosimplicialSectionsIso` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LevelLimitAcyclicity.lean`, what the tag owes
is exactly the hypothesis `hiso` of that lemma: a cosimplicial `D(*)`-module `L_*` and an
isomorphism `M(•)_e ≅ L_* ⊗_{D(*)} Ω^i_{D(*)}` at each `p`-adic level `e`.  Its two equalities are
available — `...SmallSite.bijective_toSheafify_app_tensorDifferentialFormsPresheaf_of_isAffine` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/FormsRestrictionLocalizes.lean` and `Crystalline.tensorFormsLevelEquiv` of
`StacksFrontier/AlgebraicGeometry/Crystalline/ModuleDifferentials/QuotientForms.lean` — and so is the cosimplicial comparison of the two
`D(•)`, in `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/EnvelopeCosimplicialComparison.lean`.  Of the three things that used to
be owed here all three are now available, and `L_*` itself is built; what was left is the
isomorphism `ε` of `hiso` and nothing else, and that is now
`...SmallSite.levelCosimplicialSectionsFormsIso` of `SmallSite/LevelFormsCosimplicialIso.lean`.
**[Stacks, Tag 07LF] is proved there**, as `...SmallSite.vanishing07LF`, which carries the tag;
no tag attribute is placed in this file.  How `ε` was assembled is recorded, with citations, in
"What `ε` owes" below.

* **The sections of `Ω_{X/S}` as divided power differentials — available.**
  `Crystalline.GlobalCrystallineSituation.affineCrysDifferentialFormsIso` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/AffineObjectDifferentialForms.lean` identifies the
  sections of `Ω^i_{X/S}` at an affine object of the crystalline category with
  `Crystalline.dividedPowerDifferentialForms` of the divided powers of the thickening's ring,
  which is the shape `Crystalline.tensorFormsLevelEquiv` speaks in; it carries
  `...affineCrysDifferentialsIso` — [Stacks, Tag 07J0] — up the exterior powers, and
  `Crystalline.extPow_dpDifferentials_eq` there says the exterior powers of
  `Crystalline.dpDifferentials` are those forms, unconditionally and by `rfl`.  So the output of
  the first equality can be fed to the second.
* **`Ω_{D(n)}` in two incompatible shapes — reconciled at every finite level.**  The degree `n`
  of `...SmallSite.wholeSpaceEnvelopeDifferentials` is
  `Crystalline.completedTensorPowerDifferentials`, the `p`-adic completion of the differentials of
  the *uncompleted* envelope `E(n)` carrying a divided power derivation out of `D(n)`; while
  `Crystalline.tensorFormsLevelEquiv` at `B = D(n)` produces
  `Crystalline.dividedPowerDifferentialForms` of `D(n)`'s own divided powers, the universal
  object.  These two are not isomorphic, the universal one not being complete, but
  `Crystalline.completedDifferentialsLevelLinearEquiv` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/ModuleDifferentials/CompletionLevel.lean` identifies them **modulo `pᵏ`**, over the
  completion and with the quotients left uncompleted — which is what the source's level-`e`
  argument uses, and is more than the `p`-adically completed and merely additive comparison of
  `Crystalline.dividedPowerDifferentialsCompletionComparison`.
  `Crystalline.tensorPowerDifferentialsLevelLinearEquiv` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/EnvelopeDifferentialsLevel.lean` reads it at `E(n)`, and
  `Crystalline.completionDifferentialsModPow_tensorPowerEnvelope` there identifies its target with
  `Crystalline.completedTensorPowerDifferentials` modulo `pᵏ` by `rfl`.
* **The cosimplicial module `L_*` — available.**
  `...SmallSite.levelSectionsCosimplicialModule` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LevelSectionsCosimplicialModule.lean` is
  the cosimplicial `D(*)`-module of the sections `Γ((X, T(n)_e, δ(n)), F)` at a fixed `p`-adic
  level `e`: its `D(n)`-module structure is restriction of scalars along the projection
  `D(n) ⟶ D(n)/(p)^{N + e}` composed with the inverse of
  `...SmallSite.wholeSpaceEnvelopeRingLevelEquiv`, the semilinearity of its structure maps is
  `...SmallSite.wholeSpaceEnvelopeRingLevelEquiv_map`, and the assembly is a
  `Crystalline.SemilinearCosimplicialModule.{u, u}` read through
  `Crystalline.SemilinearCosimplicialModule.toCosimplicialModule` — which is available here
  because the carriers are the `Type u` sections of a `SheafOfModules.{u}` and the rings of
  `...SmallSite.wholeSpaceEnvelopeRing` are `CommRingCat.{u}`.  Its four `rfl` computation lemmas
  give the degreewise carrier and structure map before and after
  `Crystalline.cosimplicialModuleForget`.
* **The isomorphism `ε` — still owed, and the only thing owed.**  Nothing constructs the
  isomorphism `M(•)_e ≅ L_* ⊗_{D(*)} Ω^i_{D(*)}` of cosimplicial abelian groups that `hiso` asks
  for out of the four pieces above.  Its degreewise value is forced — the two equalities compose
  to `Γ(T(n)_e, F ⊗ Ω^i) ≅ Γ(T(n)_e, F) ⊗_{D(n)} ⋀^i Ω̂_{E(n)}`, through
  `Crystalline.tensorFormsCompletionLevelEquiv` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/ModuleDifferentials/CompletionLevelForms.lean` for the last step — and what is not written
  is that family *as a family*: each of its four steps is now natural in the cosimplicial
  direction (see "What `ε` owes" below), and what is missing is the composite and the
  `CategoryTheory.NatIso.ofComponents` assembling it in `AddCommGrpCat.{u + 1}` through the
  universe lift.  The template for that assembly is
  `Crystalline.generatorPowerSimplicialIso` of `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CechCohomologyGlue.lean`.

### What `ε` owes

The construction of `ε` breaks into the steps listed below, all of which are carried out.  `ε`
is constructed, as
`...SmallSite.levelCosimplicialSectionsFormsIso` of `SmallSite/LevelFormsCosimplicialIso.lean`,
out of the degreewise composite and the assembly described at the end of this section.

1. **The divided power compatibility at the level objects — CLOSED.**  To read
   `Crystalline.tensorFormsLevelEquiv` at `T(n)_e` one needs
   `Crystalline.GlobalCrystallineSituation.crysDividedPowers` on `Γ(T(n)_e, 𝒪)` to correspond,
   under `...SmallSite.wholeSpaceSystemLevelRingEquiv`, to
   `DividedPowers.quotientDividedPowers` on `D(n)/(p)^{N + e}`.  Both descriptions already held
   by `rfl` — `Crystalline.levelThickening_ring` on the affine side, the construction of
   `Crystalline.GlobalCrystallineSituation.wholeThickeningToAffine` on the global side — and
   nothing joined them, because
   `Crystalline.DividedPowerThickening.ringEquivOfIso` keeps only the underlying ring map of the
   counit isomorphism and discards its `isDPMorphism` fields.
   `...DividedPowerThickening.isDPMorphism_ringEquivOfIso` and its `_symm` recover the discarded
   half in both directions, and
   `...SmallSite.isDPMorphism_wholeSpaceSystemLevelRingEquiv` of
   `SmallSite/WholeSpaceSystemLevelRings.lean` is the compatibility at the level objects.
2. **Cosimplicial naturality of the two comparisons — CLOSED.**  Both
   `Crystalline.tensorFormsLevelEquiv` and `Crystalline.tensorFormsCompletionLevelEquiv` were
   stated for one fixed `B` / `B̂`, and `ε`'s naturality square needs them semilinear along
   `D(n) ⟶ D(m)` with `⋀^i` carried along;
   `...SmallSite.wholeSpaceEnvelopeRingLevelEquiv_map` supplies only the *ring-level*
   naturality.
   * For `tensorFormsLevelEquiv` this is now
     `Crystalline.tensorFormsLevelEquiv_symm_naturality` of
     `StacksFrontier/AlgebraicGeometry/Crystalline/ModuleDifferentials/QuotientForms.lean`, over
     `Crystalline.formsQuotientMap_naturality` in every degree.  The route is that the
     reductions are not new maps: `Crystalline.formsQuotientMap_eq` identifies the degree-`i`
     reduction with the functorial map
     `Crystalline.mapDifferentialFormsOfDPMorphism` of the quotient divided power morphism, so
     the square collapses to two applications of the composition law.
   * For `tensorFormsCompletionLevelEquiv` this is now
     `Crystalline.tensorFormsCompletionLevelEquivAt_naturality` of
     `StacksFrontier/AlgebraicGeometry/Crystalline/ModuleDifferentials/CompletionLevelFormsNaturality.lean`: an equation of additive maps,
     with the two verticals given by what they do to a tensor of a wedge, which is all a map
     between modules over two different rings can be given by.  Its two inputs are the
     extensionality principle `Crystalline.tensorExteriorPower_addMonoidHom_ext` and the
     *degree-one* square
     `Crystalline.completionDifferentialsModPowMap_comp_completedDifferentialsLevelEquivAt` of
     `StacksFrontier/AlgebraicGeometry/Crystalline/ModuleDifferentials/CompletionLevelReindex.lean`, which is in turn the two generator
     computations below read at a common level through the re-indexed
     `Crystalline.completedDifferentialsLevelEquivAt`.  The three things that were once listed
     here as missing are all gone, and two of the three entries were false absences.

     The first said that the semilinear transition maps `Ω_{B̂}/pᵏ ⟶ Ω_{B̂'}/pᵏ` and
     `Ω̂_B/pᵏ ⟶ Ω̂_{B'}/pᵏ` along `B ⟶ B'` "are not in the library at all, so the naturality
     square cannot be written down".  Every ingredient was in the library:
     `Crystalline.adicCompletionRingMap_isDPMorphism` of `Cosimplicial/Envelope.lean` says the
     completion of a divided power morphism is one, `Crystalline.mapDifferentialsOfDPMorphismₛₗ`
     makes the universal differentials functorial in it,
     `Crystalline.adicCompletionMapₛₗ` of `Cosimplicial/CompletedForms.lean` completes a
     semilinear map with `Crystalline.adicCompletionMapₛₗ_smul` for its semilinearity over the
     *completed* ring map, and `Crystalline.adicQuotientMap` descends any of these to the
     quotients.  The two maps are
     `Crystalline.completedDifferentialsModPowMap` and
     `Crystalline.completionDifferentialsModPowMap` of
     `StacksFrontier/AlgebraicGeometry/Crystalline/ModuleDifferentials/CompletionLevelTransition.lean`, and the two routes round the
     degree-one naturality square are computed there on the spanning classes by
     `Crystalline.completionDifferentialsModPowMap_completedDifferentialsLevelEquiv_mk_d` and
     `Crystalline.completedDifferentialsLevelEquiv_completedDifferentialsModPowMap_mk_d`: both
     are the class of the image of `d (f b)`.

     The second said that a naturality statement for
     `Crystalline.tensorExteriorPowerEquivOfBaseChange` across a square of ring maps is absent.
     It is absent, and it is not needed: such a square is an equation between two *additive*
     maps out of a tensor product of an exterior power, and
     `Crystalline.tensorExteriorPower_addMonoidHom_ext` of
     `StacksFrontier/AlgebraicGeometry/Crystalline/ModuleDifferentials/CompletionLevelFormsExt.lean` reduces it to the tensors of wedges,
     where `Crystalline.tensorExteriorPowerEquivOfBaseChange_tmul_ιMulti` and its `symm`
     companion compute both sides.  No linearity is asked of either map, which is what the
     semilinearity over two different rings requires.

     The third said that `Crystalline.completedDifferentialsLevelLinearEquiv` of
     `StacksFrontier/AlgebraicGeometry/Crystalline/ModuleDifferentials/CompletionLevel.lean` is built from a
     `Crystalline.DifferentialsCompletionComparison`, a **datum** with no field relating two
     different `B`'s, and that the derivation of naturality from
     `...fromOriginalAt_d`, `...fromCompletionAt_d` and `...fromCompletionAt_smul` "needs the
     spanning lemma, which is also unwritten".  The spanning lemma is
     `Crystalline.span_completedDifferentialsModPow_mk_d_of` of
     `StacksFrontier/AlgebraicGeometry/Crystalline/ModuleDifferentials/CompletionLevelSpan.lean` — the classes of `d (of b)` for `b` in
     the uncompleted `B` span `Ω_{B̂/A,γ̂} / pᵏ` over `B̂` — with the two extensionality
     corollaries `Crystalline.completedDifferentialsModPow_ext` and
     `...completedDifferentialsModPow_ext_addMonoidHom`, the second of which is the semilinear
     form the cosimplicial direction needs.  In degree `i` after tensoring the corresponding
     determination is `Crystalline.tensorFormsCompletionLevelEquiv_unique`.

     The re-indexing that the pair of generator computations once stopped short of is
     `Crystalline.completedDifferentialsLevelEquivAt` of
     `StacksFrontier/AlgebraicGeometry/Crystalline/ModuleDifferentials/CompletionLevelReindex.lean`: the level identification stated at a
     **bare** `k` carrying a proof `cmp.quotientSystem.cutoff + e = k`, so that two comparisons
     with two cutoffs are read at one level and the square is an equation of maps between types
     that are equal and not merely propositionally equal.
     `Crystalline.completedDifferentialsLevelLinearEquivAt` is its `B̂`-linear form and
     `Crystalline.tensorFormsCompletionLevelEquivAt` the degree-`i` one.

3. **The two remaining naturalities of the degreewise composite — CLOSED, the second a false
   absence.**  A later survey found that the composite forcing `ε`'s degreewise value needs two
   naturalities beyond the two comparisons above, and recorded both as absent.

   * **The sections of `Ω^i_{X/S}` at an affine object.**  The absence was real:
     `...GlobalCrystallineSituation.affineCrysDifferentialFormsIso` had no naturality and every
     out-of-file occurrence of it was a docstring mention.  It now does:
     `...GlobalCrystallineSituation.affineCrysDifferentialFormsIso_naturality` of
     `Crystalline/AffineObjectDifferentialFormsNaturality.lean`, an equation of maps along any
     `k : A ⟶ B` of `Crystalline.Thickening S` over one affine open `V` of the base.  Degree one
     is `...affineCrysDifferentialsIso_naturality` and
     `...affineCrysDifferentialsIso_inv_naturality`
     there, over the `dpDifferentials` functoriality `Crystalline.dpMap` — the analogue of
     `Crystalline.dpConstMap` that the transition map `Crystalline.crysDifferentialsMap` of
     `Ω^1_{X/S}` is itself built from — and the base-map compatibility
     `...GlobalCrystallineSituation.affineBaseAppLE_fac`.  The bridge from the *linear*
     `Stacks.exteriorPowerCongr` that the iso carries exterior powers up with to the
     *semilinear* `ExteriorAlgebra.powMapₛₗ` that the transition of `Ω^i_{X/S}` is, is
     `...exteriorPowerCongr_affineCrysDifferentialsIso_naturality` there.
   * **The inverse of the sheafification bijection.**  The absence was **false**.  It was
     recorded that
     `...SmallSite.bijective_toSheafify_app_tensorDifferentialFormsPresheaf_of_isAffine` of
     `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/FormsRestrictionLocalizes.lean` "is only a `Function.Bijective` with per-object
     hypotheses `h`/`hV`, so no uniform-in-`n` form exists".  Both halves are wrong.  The map
     is `.app` of `CategoryTheory.toSheafify`, a natural transformation, so its forward
     naturality is `CategoryTheory.NatTrans.naturality` and its inverse's is the standard
     consequence; and `V` is an open of the *base* `S.S.scheme`, not of the object, so `V = ⊤`,
     `hV = AlgebraicGeometry.isAffineOpen_top _` and `h = le_rfl` discharge both hypotheses
     uniformly under the standing `[IsAffine S.S.scheme]`.  The only genuinely per-object
     hypothesis is the affineness of the ambient scheme, and that holds at every `(n, e)` by
     `...SmallSite.isAffine_wholeSpaceSystem_target`, from
     `...SmallSite.isWholeSpaceSystem_wholeSpaceSystem` through
     `...SmallSite.isAffineObject_of_isOverWholeSpace`.  The uniform form is
     `...SmallSite.levelCosimplicialSectionsSheafifyIso` of
     `SmallSite/LevelSectionsSheafifyIso.lean`, over the functoriality of
     `...SmallSite.levelCosimplicialSections` in its presheaf argument,
     `...SmallSite.levelCosimplicialSectionsMap`, which was the one thing really missing.

### What is left of `ε`

Nothing in the list above.  What is left is the **assembly** — but the claim that the assembly
"is not a gap in the library" was wrong, and three gaps inside the first of its two bullets have
since been closed in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LevelRingDividedPowers.lean`.  The ring
identification `...SmallSite.wholeSpaceEnvelopeRingLevelEquiv` is the composite of
`...SmallSite.wholeSpaceSystemLevelRingEquiv`, whose divided power half
`...SmallSite.isDPMorphism_wholeSpaceSystemLevelRingEquiv` is cited below, with the quotient of
`...SmallSite.wholeSpaceSystemEnvelopeRingEquiv`, which had **no** divided power half at all;
and `Crystalline.differentialFormsEquivOfAlgEquiv` wants three things of a ring identification
that none of these gave.

* **The divided power half of the second factor.**
  `...SmallSite.wholeSpaceSystemEnvelopeRingEquiv` is `DividedPowerRing.ringEquivOfEq`, which
  keeps only the ring isomorphism attached to an equality of divided power rings, exactly as
  `Crystalline.DividedPowerThickening.ringEquivOfIso` keeps only the ring map of an isomorphism
  of thickenings.  `DividedPowerRing.isDPMorphism_ringEquivOfEq`, its `_symm` and
  `DividedPowerRing.ideal_map_ringEquivOfEq` recover it, and with the descent to the finite
  levels `Crystalline.isDPMorphism_quotientMap_pAdic` the composite is
  `...SmallSite.isDPMorphism_wholeSpaceEnvelopeRingLevelEquiv` and its `_symm`: the section ring
  of the level `(n, e)` is `D(n)/(p)^{N + e}` as a divided power ring **in the
  `...SmallSite.wholeSpaceEnvelopeRing` spelling**, which is the realisation
  [Stacks, Tag 07LA] is read in and not the one of [Stacks, Tag 07JN].
* **The ideal carried onto the ideal.**  `DividedPowers.IsDPMorphism` gives only
  `J.map f ≤ L`, and the hypothesis `hJ` of `Crystalline.differentialFormsEquivOfAlgEquiv` is
  the equality.  `Crystalline.ideal_map_of_isDPMorphism_symm` turns the two inclusions into it.
* **The base compatibility.**  The same two equivalences drop the compatibility with the maps
  from `Γ(S, ⊤)`, and `Crystalline.differentialFormsEquivOfAlgEquiv` asks for a `B ≃ₐ[A] C`.
  `Crystalline.DividedPowerThickening.fromBase_comp_ringEquivOfIso` and
  `Crystalline.completedEnvelopeThickeningRingEquiv_fromBase` are the two dropped fields, and
  `...SmallSite.wholeSpaceEnvelopeRingLevelEquiv_crysBaseAppLE` is their composite: the
  identification carries `...crysBaseAppLE` of the level object — which is
  `...affineBaseAppLE` at `V = ⊤` — to the reduction of `...SmallSite.wholeSpaceEnvelopeFromBase`
  modulo `(p)^{N + e}`.

A fourth thing the assembly needs is **not** a gap and is recorded here so it is not mistaken
for one: `Crystalline.tensorFormsCompletionLevelEquivAt` is read at a level `k` tied to the
cutoff of its own `Crystalline.DifferentialsCompletionComparison`, which is a `Classical.choose`
and is **not** comparable to `Crystalline.uniformLevel`.  No reindexing of the comparison is
needed: the equivalence's source and target do not depend on `k`, only its scalars and the
instance `[Module (B̂ ⧸ (p)^k) M]` do, and `M(n)_e` is a module over `D(n)/(p)^{k}` for **every**
`k ≥ N + e` by restriction along the surjection.  So `k := cmp.quotientSystem.cutoff + (N + e)`
with `hk := rfl` serves, and `...SmallSite.levelSectionsScalars` factors through every such
level.

What is still owed is therefore:

* the degreewise composite itself —
  `Γ(T(n)_e, F ⊗ Ω^i) ≅ ULift (L_n ⊗_{D(n)} ⋀^i Ω̂_{E(n)})` — which is now **built**, as
  `...SmallSite.levelTensorFormsEquiv` of `SmallSite/LevelSectionsFormsIso.lean`, by composing
  `...SmallSite.levelTensorFormsDPEquiv` with `...SmallSite.levelTensorFormsCrossingEquiv`;
* the three concrete inputs of the abstract naturality square
  `Crystalline.tensorFormsLevelComposite_naturality` at the level objects, which are **all
  three now supplied**: `hcomm` is
  `...SmallSite.wholeSpaceEnvelopeRingLevelAlgEquiv_naturality` and `hPhi` is
  `...SmallSite.levelFormsDPVertical_tmul`, both of
  `SmallSite/LevelFormsNaturalitySquares.lean`; `hPsi` is
  `...SmallSite.levelFormsPsi_tmul_ιMulti` of
  `SmallSite/LevelFormsCosimplicialVertical.lean`, together with
  `...SmallSite.levelEnvelopeDifferentialsMap_eq` which identifies the transition map of
  `Ω_{D(*)}` with the `Crystalline.completionDifferentialsMapₛₗ` the square is stated against,
  and `...SmallSite.levelEnvelopeReindex_isDPMorphism` which is its `hg`;
* and the `CategoryTheory.NatIso.ofComponents` assembling that family in
  `AddCommGrpCat.{u + 1}` through `AddCommGrpCat.uliftFunctor`.  The `CategoryTheory.opOp`
  reindexing and the universe lift that assembly has to cross are **no longer an obstruction**:
  `Crystalline.cosimplicialModuleForgetUliftIso` of `Cosimplicial/Acyclicity.lean` performs both
  with the cosimplicial module a variable, which is the only way the index substitution
  elaborates at `L_* ⊗ ⋀^i Ω_{D(*)}` — see the implementation notes of that file and of
  `SmallSite/LevelFormsCosimplicialVertical.lean`.

**The single-level obstruction that stood here is CLOSED.**
`Crystalline.tensorFormsLevelComposite_naturality` carries **one** finite level `k` for both of
its sides: `(e e' k : ℕ)` with `hk : cmp.quotientSystem.cutoff + e = k` on the unprimed side and
`hk' : cmp'.quotientSystem.cutoff + e' = k` on the primed one.  That is exactly right for two
*fixed* rings with two different cutoffs, and it is what
`Crystalline.completedDifferentialsLevelEquivAt` of `StacksFrontier/AlgebraicGeometry/Crystalline/ModuleDifferentials/CompletionLevelReindex.lean` was
introduced for.  It is not enough for a *family*.  The degreewise
`...SmallSite.levelTensorFormsCrossingEquiv` is read at `e := N + e` and
`k := cmp.quotientSystem.cutoff + (N + e)` with `hk := rfl` for
`cmp = ...SmallSite.wholeSpaceLevelComparison hp n.len`, whose cutoff is
`max N₀ (DividedPowers.nilpotencyExponent ...)` with `N₀` an `Exists.choose` inside
`Crystalline.dividedPowerDifferentialsCompletionComparison` — so it depends on the cosimplicial
degree and no `k` serves every degree at once.

What closes it is the **level-independence lemma**
`Crystalline.tensorFormsCompletionLevelEquivAt_level_independent` of
`StacksFrontier/AlgebraicGeometry/Crystalline/ModuleDifferentials/CompletionLevelIndependence.lean`: at any two levels of one and the same
comparison of [Stacks, Tag 07KK], `Crystalline.tensorFormsCompletionLevelEquivAt` — and hence
`Crystalline.tensorFormsLevelComposite`, by
`Crystalline.tensorFormsLevelComposite_level_independent` there — is the same additive map.  The
source and target mention no level; only the `[Module (B̂ ⧸ (p)^k) M]` instance and the `≃ₗ`
scalars do, so the statement is an equation of maps between the very same pair of types, with `M`
asked to carry the module structure at both levels.  The two levels are **not** assumed
comparable: the ordered form is `..._level_independent_of_le` and the unordered one follows from
it by `le_total`.

Its route goes through `Crystalline.completedDifferentialsLevelEquiv_transition`, the cross-level
compatibility of `Crystalline.completedDifferentialsLevelEquiv` of `StacksFrontier/AlgebraicGeometry/Crystalline/ModuleDifferentials/CompletionLevel.lean`, and
**that needs no cross-level property of the comparison.**  Both routes round its square are
`B̂`-linear, the classes of the differentials of elements of the uncompleted `B` span the source by
`Crystalline.span_completedDifferentialsModPow_mk_d_of`, and on such a class both compute to the
class of the image of `d b` by `Crystalline.completedDifferentialsLevelEquiv_d` at the respective
level — the transition maps being `Submodule.factor`s of the identity, which fix a class by
`rfl` — so `Crystalline.completedDifferentialsModPow_ext` closes it.  The two cross-level fields
`fromOriginalAt_transition` and `fromCompletionAt_transition` of
`Crystalline.DifferentialsCompletionComparison` of `StacksFrontier/AlgebraicGeometry/Crystalline/ModuleDifferentials/Completion.lean` are
the obvious route and are in the end **not used**: taking them would additionally need the
cross-level compatibility of the identification of [Stacks, Tag 05GG] with the transition maps,
which the library does not record.  Its consequence
`Crystalline.completedDifferentialsLevelEquivAt_mk_of_le` says a witness at a larger level is a
witness at a smaller one, so witnesses chosen at the larger level make
`Crystalline.tensorFormsCompletionLevelEquivAt_tmul_ιMulti_of_mk` compute **both** levels'
identifications on `m ⊗ ω₁ ∧ ⋯ ∧ ωᵢ` to the same value, and
`Crystalline.tensorExteriorPower_addMonoidHom_ext` of `StacksFrontier/AlgebraicGeometry/Crystalline/ModuleDifferentials/CompletionLevelFormsExt.lean` finishes.
The determination `Crystalline.tensorFormsCompletionLevelEquiv_unique` is stated at the level
`cutoff + e` and was never by itself enough.

The square in the shape the family consumes is
`Crystalline.tensorFormsLevelComposite_naturality_of_levels` of
`StacksFrontier/AlgebraicGeometry/Crystalline/ModuleDifferentials/LevelFormsCompositeTwoLevels.lean`: the same square with the two sides at
**two independent levels** `k` and `k'`, proved by reading both at a common level `K` and
transporting each horizontal back by level independence.  `K` is an argument together with the
two module structures and scalar towers reading the tensor products there — as a *number* it is
free (`max k k'` serves), but an instance at `K` cannot be produced from the ones at `k` and
`k'`, and the consumer has them: `...SmallSite.levelSectionsModuleAt` and
`...SmallSite.levelSectionsIsScalarTowerAt` give the sections over a level object a module
structure over **every** level past `N + e`, and at `K := max cutoff_n cutoff_m + (N + e)` the
registered instances `...SmallSite.levelSectionsModuleAtAdd` and
`...SmallSite.levelSectionsIsScalarTowerAtAdd` have exactly that shape.

### How `ε` was built

Three steps, all of them instantiation and assembly with no missing mathematics, carried out in
`SmallSite/LevelFormsCosimplicialIso.lean`:

1. **The cosimplicial naturality of `...SmallSite.levelTensorFormsCrossingEquiv`** — the
   instantiation of `Crystalline.tensorFormsLevelComposite_naturality_of_levels` at the level
   objects, with `g := ...SmallSite.levelEnvelopeReindex` and
   `hg := ...SmallSite.levelEnvelopeReindex_isDPMorphism`,
   `u := ...crysSectionsRestrictionAlgHom` at the transition of thickenings and `hu` its
   `compatible` field — which is the spelling `...SmallSite.levelDPFormsMap`, and hence `hPhi`,
   is written at — `phi := ...SmallSite.levelSectionsRestriction`,
   `hcomm := ...SmallSite.wholeSpaceEnvelopeRingLevelAlgEquiv_naturality`,
   `Phi := ...SmallSite.levelFormsDPVertical` with
   `hPhi := ...SmallSite.levelFormsDPVertical_tmul`,
   `Psi := ...SmallSite.levelFormsPsi` with `hPsi := ...SmallSite.levelFormsPsi_tmul_ιMulti`
   through `...SmallSite.levelEnvelopeDifferentialsMap_eq`, the two levels being
   `cutoff_n + (N + e)` and `cutoff_m + (N + e)` with `hk := rfl` and `hk' := rfl`, and
   `K := cutoff_n + (cutoff_m + (N + e))` with `hK := rfl` and `hK'` by `Nat.add_left_comm`,
   which needs neither `max` nor truncated subtraction.  The cost is the size of the
   application — the abstract square has four rings, eight ring instances and forty-odd further
   arguments — and it is three declarations rather than one, for the reason the implementation
   notes of that file record.
2. **The cosimplicial naturality of `...SmallSite.levelTensorFormsEquiv`**, which is step 1
   conjugated by `...SmallSite.levelTensorFormsDPEquiv`; the conjugation is exactly what
   `...SmallSite.levelFormsDPVertical` was defined to absorb, so this is `congrArg` and
   `symm_apply_apply`.
3. **The assembly.**  `Crystalline.cosimplicialModuleForgetUliftIso` of
   `Cosimplicial/Acyclicity.lean` takes the degreewise `comp n` and the naturality `hcomp` and
   produces the isomorphism onto
   `(cosimplicialModuleForget _).obj (L ⊗ ⋀^i Ω) ⋙ AddCommGrpCat.uliftFunctor` that the
   hypothesis `hiso` of `...SmallSite.vanishing07LF_of_levelCosimplicialSectionsIso` of
   `SmallSite/LevelLimitAcyclicity.lean` asks for, with
   `L := ...SmallSite.levelSectionsCosimplicialModule` and the
   `...SmallSite.levelCosimplicialSectionsSheafifyIso` of `SmallSite/LevelSectionsSheafifyIso.lean`
   composed in to pass from the presheaf to its sheafification.

**[Stacks, Tag 07LF] is proved**, as `...SmallSite.vanishing07LF` of
`SmallSite/LevelFormsCosimplicialIso.lean`, which is where the `@[stacks 07LF]` attribute is;
none is placed in this file.

## Implementation notes

Three identifications of presheaves of rings are paid for once each, in a definition, and never
inside a proof — the practice the implementation notes of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/ExteriorPowerComparisonSurjectivity.lean` and
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/FormsRestrictionQuasicoherent.lean` record for this area.

* `restrictedCommRing` fixes the restriction of the structure presheaf as
  `(restrictOpenFunctor A).op ⋙ structurePresheaf S`, *before* the forgetful functor to rings.
  The monoidal structure on presheaves of modules over it, and the whole `toRingCat` vocabulary of
  [Stacks, Tag 0GMW], are found by instance search only at that spelling: recovering the
  commutative-ring presheaf from `(restrictOpenFunctor A).op ⋙ (structurePresheaf S ⋙ forget₂ _ _)`
  asks the unifier to reassociate a composite of functors while solving for it.
* `restrictedCoefficientSheaf` is `...CohomologyRestriction.moduleRestrictionSheaf` retyped over
  `CategoryTheory.Sheaf.toRingCat _ (restrictedCommRingSheaf A)` rather than over
  `...Thickening.ringRestrictionSheaf A.obj`.  The two sheaves of rings are equal by `rfl`
  (`toRingCat_restrictedCommRingSheaf`), but they are different `DiscrTree` keys, and a
  quasi-coherence instance declared at one is invisible at the other — the failure recorded as
  cliff (ii) in `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/FormsRestrictionQuasicoherent.lean`.  This is **stuck elaboration, not a
  genuine obstruction**: naming the renaming once removes it.
* `isIso_toRingCatMap_id` is named, and proved by a `show` that unfolds to the identity, because
  `CategoryTheory.Sheaf.toRingCatMap _ (𝟙 _)` is the identity by `rfl` and not syntactically, so
  the local-bijectivity instances that [Stacks, Tag 0GMW] asks for are otherwise not found.

`tensorRestriction_eq` chains three `rfl`s with `Eq.trans` and `congrArg` rather than proving the
composite equality by a single `rfl`.  Each step on its own is a cheap definitional unfolding;
asked for all at once, inside the sheafification functor, `whnf` descends into the sheafification
and exhausts the heartbeat budget.  This is the hazard the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorSheafWorldBridge.lean` record for the
sheaf-level morphism identification, with the same remedy; no limit is raised anywhere.

The local injectivity and surjectivity of the Zariski sheafification unit are taken from
`CategoryTheory.GrothendieckTopology.W_toSheafify` rather than from Mathlib's global instances,
which is cliff (iii) of `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/SheafifySections.lean`: the global instances of
`StacksFrontier/AlgebraicGeometry/Divisors/Meromorphic/RegularIdealSheaves.lean` carry a universe
appearing nowhere in their statements and instance search reaches them first.

## References

* [Stacks Project, Tag 07JJ](https://stacks.math.columbia.edu/tag/07JJ)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07KM](https://stacks.math.columbia.edu/tag/07KM)
* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Tag 01X9](https://stacks.math.columbia.edu/tag/01X9)
* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open CategoryTheory.Sheaf Opposite
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}}

/-! ### The restriction of `𝒪_{X/S}` as a sheaf of commutative rings -/

/-- **The restriction of the structure presheaf of `Cris(X/S)` to the opens of the ambient scheme
of an object, as a presheaf of commutative rings**: over an open `W` of `T` it is the ring
`Γ(W, 𝒪_W)` of global sections of the ambient scheme of the restriction `A|_W`.

This is `...CohomologyRestriction.restriction` at the `CommRingCat`-valued structure presheaf.  It
is a definition rather than an abbreviation because fixing this spelling of the presheaf of
commutative rings — before the forgetful functor to rings — is what makes the monoidal structure
on presheaves of modules over it, and the vocabulary of [Stacks, Tag 0GMW], visible to instance
search; see the implementation notes. -/
def restrictedCommRing (A : CrystallineThickening S) :
    (A.obj.thickening.target.scheme.Opens)ᵒᵖ ⥤ CommRingCat.{u} :=
  (CrystallineThickening.restrictOpenFunctor A).op ⋙ structurePresheaf S

/-- The presheaf of rings underlying `restrictedCommRing` is the restriction of `𝒪_{X/S}` to the
opens of the ambient scheme of the underlying object of `CRIS(X/S)`. -/
theorem restrictedCommRing_comp_forget₂ (A : CrystallineThickening S) :
    restrictedCommRing A ⋙ forget₂ CommRingCat RingCat =
      (Thickening.ringRestrictionSheaf A.obj).obj := rfl

/-- **The restriction of `𝒪_{X/S}` to the opens of the ambient scheme of an object is a sheaf of
commutative rings.**  The forgetful functor to rings is fully faithful, hence reflects limits, so
this is the sheaf condition for the underlying presheaf of rings,
`...Thickening.ringRestrictionSheaf`. -/
theorem isSheaf_restrictedCommRing (A : CrystallineThickening S) :
    Presheaf.IsSheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (restrictedCommRing A) :=
  Presheaf.isSheaf_of_isSheaf_comp _ _ (forget₂ CommRingCat.{u} RingCat.{u})
    (Thickening.ringRestrictionSheaf A.obj).property

/-- **The restriction of `𝒪_{X/S}` to the ambient scheme of an object, as a sheaf of commutative
rings on that scheme.**  This is the ringed site over which both factors of the restriction of
`F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` are quasi-coherent. -/
def restrictedCommRingSheaf (A : CrystallineThickening S) :
    Sheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme) CommRingCat.{u} :=
  ⟨restrictedCommRing A, isSheaf_restrictedCommRing A⟩

/-- The sheaf of rings underlying `restrictedCommRingSheaf` is
`...Thickening.ringRestrictionSheaf`, the sheaf of rings over which
`...IsLocallyQuasiCoherent` states its conclusion. -/
theorem toRingCat_restrictedCommRingSheaf (A : CrystallineThickening S) :
    toRingCat (Opens.grothendieckTopology A.obj.thickening.target.scheme)
        (restrictedCommRingSheaf A) =
      Thickening.ringRestrictionSheaf A.obj := rfl

/-- The comparison morphism of presheaves of rings attached to the identity of
`restrictedCommRing` is the identity.  The restriction of `𝒪_{X/S}` is already a sheaf, so the
morphism to its associated sheaf which [Stacks, Tag 0GMW] takes as input is the identity. -/
theorem toRingCatMap_id_restrictedCommRingSheaf (A : CrystallineThickening S) :
    toRingCatMap (Opens.grothendieckTopology A.obj.thickening.target.scheme)
        (𝟙 (restrictedCommRingSheaf A).obj) =
      𝟙 (Thickening.ringRestrictionSheaf A.obj).obj := rfl

/-- The comparison morphism of presheaves of rings attached to the identity of
`restrictedCommRing` is an isomorphism, hence locally bijective; this is what makes the
sheafification of presheaves of modules of [Stacks, Tag 0GMW] available over the restricted
structure sheaf.  It is named, and proved by a `change`, because
`CategoryTheory.Sheaf.toRingCatMap _ (𝟙 _)` is the identity by `rfl` and not syntactically. -/
instance isIso_toRingCatMap_id_restrictedCommRingSheaf (A : CrystallineThickening S) :
    IsIso (toRingCatMap (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (𝟙 (restrictedCommRingSheaf A).obj)) := by
  change IsIso (𝟙 (Thickening.ringRestrictionSheaf A.obj).obj)
  infer_instance

/-! ### Restriction to `T` and the objectwise tensor product -/

/-- **The restriction to the ambient scheme of an object of a presheaf of `𝒪_{X/S}`-modules on
`Cris(X/S)`**, as a presheaf of modules over `restrictedCommRing`: its sections over an open `W`
of `T` are the sections of the given presheaf over the restriction `A|_W`. -/
def restrictedModule (A : CrystallineThickening S)
    (M : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.{u} (restrictedCommRing A ⋙ forget₂ CommRingCat RingCat) :=
  Stacks.MonoidalRestrictionTensor.restrictModules
    (CrystallineThickening.restrictOpenFunctor A) (structurePresheaf S) |>.obj M

/-- **Restriction to the ambient scheme of an object commutes with the objectwise tensor product
of presheaves of modules**, for the monoidal tensor product of
`PresheafOfModules (structurePresheaf S ⋙ forget₂ _ _)`, which is the one
`...SmallSite.tensorDifferentialForms` is built with.

This is `Stacks.MonoidalRestrictionTensor.restrictModules_tensorObj`; the mixed-universe form is
`Stacks.DenseSubsiteModules.presheafRestrict_tensorObj`, and the two objectwise tensor products
are the same construction by
`Stacks.SheafOfModules.TensorEncodings.tensorObj_eq_tensorObj`. -/
theorem restrictedModule_tensorObj (A : CrystallineThickening S)
    (M N : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) :
    restrictedModule A (M ⊗ N) = restrictedModule A M ⊗ restrictedModule A N :=
  Stacks.MonoidalRestrictionTensor.restrictModules_tensorObj _ _ M N

/-- The abelian presheaf underlying `restrictedModule A M` is the restriction of the abelian
presheaf of `M` along the restrictions of `A` to the opens of its ambient scheme. -/
theorem presheaf_restrictedModule (A : CrystallineThickening S)
    (M : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) :
    (restrictedModule A M).presheaf =
      (CrystallineThickening.restrictOpenFunctor A).op ⋙ M.presheaf := rfl

/-- **The restriction of `Ω^i_{X/S}` to `T` is
`...crysDifferentialFormsRestriction`**, the presheaf of modules over the restriction of
`𝒪_{X/S}` whose associated sheaf
`...isQuasicoherentOnSite_crysDifferentialFormsRestriction` proves quasi-coherent. -/
theorem restrictedModule_crysDifferentialForms (A : CrystallineThickening S) (i : ℕ) :
    restrictedModule A (crysDifferentialForms S i) =
      (crysDifferentialFormsRestriction S A.obj i :
        PresheafOfModules.{u} (restrictedCommRing A ⋙ forget₂ CommRingCat RingCat)) := rfl

/-- **The restriction of a sheaf of `𝒪_{X/S}`-modules to `T` is `F_T`**, the restriction
`...CohomologyRestriction.moduleRestrictionSheaf` whose quasi-coherence is hypothesis (1) of
[Stacks, Tag 07JN]. -/
theorem restrictedModule_val (A : CrystallineThickening S)
    (F : SheafOfModules.{u} (structureSheaf S)) :
    restrictedModule A
        (F.val : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) =
      ((CohomologyRestriction.moduleRestrictionSheaf F A).val :
        PresheafOfModules.{u} (restrictedCommRing A ⋙ forget₂ CommRingCat RingCat)) := rfl

/-- **The restriction `F_T` of a sheaf of `𝒪_{X/S}`-modules to the ambient scheme of an object**,
read over `CategoryTheory.Sheaf.toRingCat _ (restrictedCommRingSheaf A)`.

This is `...CohomologyRestriction.moduleRestrictionSheaf` and nothing else; the two sheaves of
rings are equal by `rfl`, by `toRingCat_restrictedCommRingSheaf`, but they are different keys for
instance search, so the renaming is paid for here once. -/
def restrictedCoefficientSheaf (A : CrystallineThickening S)
    (F : SheafOfModules.{u} (structureSheaf S)) :
    SheafOfModules.{u}
      (toRingCat (Opens.grothendieckTopology A.obj.thickening.target.scheme)
        (restrictedCommRingSheaf A)) :=
  CohomologyRestriction.moduleRestrictionSheaf F A

/-- `restrictedCoefficientSheaf`, read as a presheaf of modules over the restriction of
`𝒪_{X/S}` in the way [Stacks, Tag 0GMW] reads a sheaf of modules over an associated sheaf of
rings, is `restrictedModule` of the underlying presheaf of modules.  The comparison of rings being
the identity, this restriction of scalars changes nothing. -/
theorem restrictSheafFunctor_restrictedCoefficientSheaf (A : CrystallineThickening S)
    (F : SheafOfModules.{u} (structureSheaf S)) :
    (PresheafOfModules.restrictSheafFunctor
        (Opens.grothendieckTopology A.obj.thickening.target.scheme)
        (𝟙 (restrictedCommRingSheaf A).obj)).obj (restrictedCoefficientSheaf A F) =
      restrictedModule A
        (F.val : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) :=
  rfl

/-! ### The restriction of the coefficient sheaf of Stacks 07LF -/

/-- **The restriction to the ambient scheme of an object of the presheaf tensor product
`F ⊗_{𝒪_{X/S}} Ω^i_{X/S}`**, as a presheaf of modules over the restriction of `𝒪_{X/S}`: its
sections over an open `W` of `T` are `F(A|_W) ⊗_{Γ(W, 𝒪_W)} Ω^i_{X/S}(A|_W)`. -/
def tensorRestriction (A : CrystallineThickening S)
    (F : SheafOfModules.{u} (structureSheaf S)) (i : ℕ) :
    PresheafOfModules.{u} (restrictedCommRing A ⋙ forget₂ CommRingCat RingCat) :=
  restrictedModule A
    (tensorDifferentialForms
      (F.val : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i)

/-- **The restriction of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` to `T` is the objectwise tensor product of
`F_T` with the restriction of `Ω^i_{X/S}`**, in the shape [Stacks, Tag 0GMW] states its
comparison: the first factor read off a sheaf of modules, the second a bare presheaf.

The three steps are `restrictedModule_tensorObj`,
`restrictSheafFunctor_restrictedCoefficientSheaf` and
`Stacks.SheafOfModules.TensorEncodings.tensorObj_eq_tensor`, each a definitional unfolding; they
are chained rather than collapsed into one `rfl` for the reason in the implementation notes. -/
theorem tensorRestriction_eq (A : CrystallineThickening S)
    (F : SheafOfModules.{u} (structureSheaf S)) (i : ℕ) :
    tensorRestriction A F i =
      PresheafOfModules.tensorObj
        ((PresheafOfModules.restrictSheafFunctor
          (Opens.grothendieckTopology A.obj.thickening.target.scheme)
          (𝟙 (restrictedCommRingSheaf A).obj)).obj (restrictedCoefficientSheaf A F))
        (restrictedModule A (crysDifferentialForms S i)) :=
  (restrictedModule_tensorObj A _ _).trans
    ((congrArg (fun P ↦ P ⊗ restrictedModule A (crysDifferentialForms S i))
        (restrictSheafFunctor_restrictedCoefficientSheaf A F).symm).trans
      (Stacks.SheafOfModules.TensorEncodings.tensorObj_eq_tensor _ _).symm)

/-- **The associated sheaf, over the restriction of `𝒪_{X/S}` to the opens of `T`, of the
restriction of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}`.**  This is the candidate Zariski sheaf of
`...SmallSite.vanishing07JJ_tensorDifferentialFormsSheaf_of_isZero_cechHomology`, before the
coefficient universe is raised. -/
def tensorRestrictionSheaf (A : CrystallineThickening S)
    (F : SheafOfModules.{u} (structureSheaf S)) (i : ℕ) :
    SheafOfModules.{u} (Thickening.ringRestrictionSheaf A.obj) :=
  (PresheafOfModules.moduleSheafification
    (Opens.grothendieckTopology A.obj.thickening.target.scheme)
    (𝟙 (restrictedCommRingSheaf A).obj)).obj (tensorRestriction A F i)

/-- **The associated sheaf of the restriction of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` to `T` is
quasi-coherent**, for a locally quasi-coherent sheaf of `𝒪_{X/S}`-modules `F`, every `i : ℕ` and
every object of `Cris(X/S)`.

The two factors are quasi-coherent over one and the same sheaf of rings: `F_T` by hypothesis (1)
of [Stacks, Tag 07JN], which is `hF`; and the associated sheaf of the restriction of `Ω^i_{X/S}`
by `...isQuasicoherentOnSite_crysDifferentialFormsRestriction`, which is clause (1) of
[Stacks, Tag 07KM] for every exterior power read over the restriction of `𝒪_{X/S}`, and which
carries no hypothesis.  The conclusion is then
`Stacks.MonoidalRestrictionTensor.isQuasicoherentOnSite_moduleSheafification_tensorObj`, that is
[Stacks, Tag 03L6] through [Stacks, Tag 0GMW].

The only hypothesis carried is `hF`. -/
theorem isQuasicoherentOnSite_tensorRestrictionSheaf
    {F : SheafOfModules.{u} (structureSheaf S)} (hF : IsLocallyQuasiCoherent F)
    (A : CrystallineThickening S) (i : ℕ) :
    (tensorRestrictionSheaf A F i).IsQuasicoherentOnSite := by
  have : SheafOfModules.IsQuasicoherentOnSite (restrictedCoefficientSheaf A F) :=
    (hF A).choose_spec
  have : SheafOfModules.IsQuasicoherentOnSite
      ((PresheafOfModules.moduleSheafification
        (Opens.grothendieckTopology A.obj.thickening.target.scheme)
        (𝟙 (restrictedCommRingSheaf A).obj)).obj
          (restrictedModule A (crysDifferentialForms S i))) :=
    isQuasicoherentOnSite_crysDifferentialFormsRestriction S A.obj i
  show ((PresheafOfModules.moduleSheafification
    (Opens.grothendieckTopology A.obj.thickening.target.scheme)
    (𝟙 (restrictedCommRingSheaf A).obj)).obj (tensorRestriction A F i)).IsQuasicoherentOnSite
  rw [tensorRestriction_eq]
  exact Stacks.MonoidalRestrictionTensor.isQuasicoherentOnSite_moduleSheafification_tensorObj
    (Opens.grothendieckTopology A.obj.thickening.target.scheme)
    (𝟙 (restrictedCommRingSheaf A).obj) (restrictedCoefficientSheaf A F)
    (restrictedModule A (crysDifferentialForms S i))

/-! ### Čech vanishing on a standard open cover of an affine ambient scheme -/

/-- The abelian presheaf underlying `tensorRestrictionSheaf` is the Zariski sheafification of the
restriction to `T` of the abelian presheaf of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}`. -/
theorem presheaf_tensorRestrictionSheaf (A : CrystallineThickening S)
    (F : SheafOfModules.{u} (structureSheaf S)) (i : ℕ) :
    (tensorRestrictionSheaf A F i).val.presheaf =
      sheafify (Opens.grothendieckTopology A.obj.thickening.target.scheme)
        (tensorRestriction A F i).presheaf := rfl

/-- **[Stacks, Tag 01X9] for the restriction of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}`.**  For a locally
quasi-coherent `F` and an object of `Cris(X/S)` whose ambient divided power scheme `T` is affine,
the positive-degree Zariski Čech cohomology of `tensorRestrictionSheaf` on the basic opens of a
standard open cover of `T` vanishes.

The module is quasi-coherent by `isQuasicoherentOnSite_tensorRestrictionSheaf`; reading its
scalars in `𝒪_T` rather than in the restriction of `𝒪_{X/S}` along
`...Thickening.ringRestrictionSheafStructureIso` changes neither the module nor its Čech complex,
and `Stacks.Cohomology.Cech.isZero_cechCohomology_of_isStandardOpenCover` applies.

The only hypothesis carried is `hF`. -/
theorem isZero_cechHomology_tensorRestrictionSheaf
    {F : SheafOfModules.{u} (structureSheaf S)} (hF : IsLocallyQuasiCoherent F)
    (A : CrystallineThickening S) [IsAffine A.obj.thickening.target.scheme] (i : ℕ) {n : ℕ}
    (g : Fin n → Γ(A.obj.thickening.target.scheme, ⊤))
    (hg : PrimeSpectrum.IsStandardOpenCoverOfSpectrum g) (p : ℕ) (hp : 0 < p) :
    IsZero (((cechComplexFunctor fun j ↦ A.obj.thickening.target.scheme.basicOpen (g j)).obj
      (tensorRestrictionSheaf A F i).val.presheaf).homology p) := by
  have hqc : SheafOfModules.IsQuasicoherentOnSite
      ((SheafOfModules.restrictScalars
        (Thickening.ringRestrictionSheafStructureIso A.obj).inv).obj
          (tensorRestrictionSheaf A F i)) :=
    Stacks.SheafOfModules.isQuasicoherentOnSite_restrictScalars_of_isIso _ _
      (isQuasicoherentOnSite_tensorRestrictionSheaf hF A i)
  have := hqc.isQuasicoherent
  exact Stacks.Cohomology.Cech.isZero_cechCohomology_of_isStandardOpenCover
    A.obj.thickening.target.scheme
    ((SheafOfModules.restrictScalars
      (Thickening.ringRestrictionSheafStructureIso A.obj).inv).obj
        (tensorRestrictionSheaf A F i))
    ⊤ (isAffineOpen_top _) g hg p hp

/-- The restriction to `T` of `...SmallSite.tensorDifferentialFormsPresheaf`, the abelian presheaf
of the coefficient universe `u + 1` whose crystalline sheafification is
`...SmallSite.tensorDifferentialFormsSheaf`, is the universe lift of the abelian presheaf of
`tensorRestriction`. -/
theorem restrictOpen_tensorDifferentialFormsPresheaf (A : CrystallineThickening S)
    (F : SheafOfModules.{u} (structureSheaf S)) (i : ℕ) :
    (CrystallineThickening.restrictOpenFunctor A).op ⋙ tensorDifferentialFormsPresheaf F i =
      (tensorRestriction A F i).presheaf ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u} := rfl

/-- **[Stacks, Tag 01X9] for the restriction of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}`, at the coefficient
universe `u + 1`.**  This is the `u → u + 1` passage: the Čech complex of a universe-lifted
coefficient presheaf is the universe lift of the Čech complex, because the lift is additive and
preserves the products the complex is built from
(`Stacks.CategoryTheory.CechComplex.isZero_homology_mapCoeff_iff`), and the lift commutes with
homology because it preserves homology
(`Stacks.Homology.RestrictScalars.mapHomologicalComplexHomologyIso`); a universe lift of a zero
object is zero.

The only hypothesis carried is `hF`. -/
theorem isZero_cechHomology_ulift
    {F : SheafOfModules.{u} (structureSheaf S)} (hF : IsLocallyQuasiCoherent F)
    (A : CrystallineThickening S) [IsAffine A.obj.thickening.target.scheme] (i : ℕ) {n : ℕ}
    (g : Fin n → Γ(A.obj.thickening.target.scheme, ⊤))
    (hg : PrimeSpectrum.IsStandardOpenCoverOfSpectrum g) (p : ℕ) (hp : 0 < p) :
    IsZero (((cechComplexFunctor fun j ↦ A.obj.thickening.target.scheme.basicOpen (g j)).obj
      (sheafify (Opens.grothendieckTopology A.obj.thickening.target.scheme)
          (tensorRestriction A F i).presheaf ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u})).homology p) := by
  rw [Stacks.CategoryTheory.CechComplex.isZero_homology_mapCoeff_iff]
  exact (AddCommGrpCat.uliftFunctor.{u + 1, u}.map_isZero
      (isZero_cechHomology_tensorRestrictionSheaf hF A i g hg p hp)).of_iso
    (Stacks.Homology.RestrictScalars.mapHomologicalComplexHomologyIso
      AddCommGrpCat.uliftFunctor.{u + 1, u}
      ((cechComplexFunctor fun j ↦ A.obj.thickening.target.scheme.basicOpen (g j)).obj
        (tensorRestrictionSheaf A F i).val.presheaf) p)

/-! ### Stacks 07JJ for the coefficient sheaf of Stacks 07LF -/

/-- **The conclusion of [Stacks, Tag 07JJ] for the coefficient sheaf
`F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` of [Stacks, Tag 07LF].**  Let `F` be a sheaf of `𝒪_{X/S}`-modules on
the small crystalline site which is locally quasi-coherent — hypothesis (1) of
[Stacks, Tag 07JN] — and let `i : ℕ`.  Then for every object `(U, T, δ)` of `Cris(X/S)` whose
ambient divided power scheme `T` is affine and every `p > 0`,

`H^p(Cris(X/S)/(U, T, δ), F ⊗_{𝒪_{X/S}} Ω^i_{X/S}) = 0`.

This discharges the hypothesis `h` of
`...SmallSite.vanishing07JJ_tensorDifferentialFormsSheaf_of_isZero_cechHomology`.  The Zariski
sheaf it asks for over an affine `T` is `tensorRestrictionSheaf`, read at the coefficient universe
`u + 1`; the morphism from the restricted presheaf tensor product is the universe lift of its
Zariski sheafification unit, which is locally bijective because the unit is
(`CategoryTheory.GrothendieckTopology.W_toSheafify`) and because raising the universe of the
sections preserves local bijectivity; and its Čech vanishing is `isZero_cechHomology_ulift`.

`hF` is the only hypothesis carried: no affineness of `X` or `S`, no condition on `i`, nothing
about the crystal condition and nothing about surjectivity of comparison maps.  **No tag
attribute is placed**, [Stacks, Tag 07JJ] being already carried for a locally quasi-coherent
module; see the module documentation. -/
theorem vanishing07JJ_tensorDifferentialFormsSheaf
    {F : SheafOfModules.{u} (structureSheaf S)} (hF : IsLocallyQuasiCoherent F) (i : ℕ) :
    Vanishing07JJ S (tensorDifferentialFormsSheaf F i) := by
  refine vanishing07JJ_tensorDifferentialFormsSheaf_of_isZero_cechHomology F i fun A hA ↦ ?_
  have := hA
  have hW := (Opens.grothendieckTopology A.obj.thickening.target.scheme).W_toSheafify
    (tensorRestriction A F i).presheaf
  have := GrothendieckTopology.W.isLocallyInjective hW
  have := GrothendieckTopology.W.isLocallySurjective hW
  refine ⟨sheafify (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (tensorRestriction A F i).presheaf ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u},
    Functor.whiskerRight (toSheafify (Opens.grothendieckTopology
        A.obj.thickening.target.scheme) (tensorRestriction A F i).presheaf)
      AddCommGrpCat.uliftFunctor.{u + 1, u},
    Presheaf.isSheaf_comp_of_isSheaf _ _ AddCommGrpCat.uliftFunctor.{u + 1, u}
      (tensorRestrictionSheaf A F i).isSheaf,
    ?_, ?_, fun g hg p hp ↦ isZero_cechHomology_ulift hF A i g hg p hp⟩
  · exact Presheaf.isLocallyInjective_whiskerRight_uliftFunctor _ _
  · exact Presheaf.isLocallySurjective_whiskerRight_uliftFunctor _ _

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
