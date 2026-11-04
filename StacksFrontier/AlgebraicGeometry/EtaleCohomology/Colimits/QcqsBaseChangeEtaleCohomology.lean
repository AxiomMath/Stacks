module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineLimitEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.QcqsEtaleCohomologyColimit
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.GlobalSectionsAcyclicityOfColimitOfFiniteSites
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.BaseChangeAlgebraSystemCohomologySupplement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.BiggerSiteGlobalCohomologySupplement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.DenseSubsiteGlobalCohomologySupplement

/-!
# Stacks 03Q6 for a quasi-compact quasi-separated `X`, over the Cech descent

Stacks 03Q6 takes a ring `A`, a directed set `I`, a system `(B_i, φ_{ij})` of `A`-algebras with
`B = colim_i B_i`, and a **quasi-compact and quasi-separated** morphism `X ⟶ Spec A`. With
`Y_i = X ×_{Spec A} Spec B_i`, `Y = X ×_{Spec A} Spec B`, `G_i = (Y_i ⟶ X)^{-1} F` and
`G = (Y ⟶ X)^{-1} F` for an abelian sheaf `F` on `X_etale`, it asserts

`H^p_etale(Y, G) = colim_{i ∈ I} H^p_etale(Y_i, G_i)`.

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/BaseChangeAlgebraSystemCohomology.lean`
and its sequel `BaseChangeAlgebraSystemEtaleCohomology.lean` prove this for an **affine** `X`.
This file carries it out at the source's own generality on `X`, over one named hypothesis.

## What the affineness of `X` was buying, and what it was not

Only one thing. The site system of Stacks 0EYL for the diagram `Y_i` needs its transition
morphisms affine, and for an affine `X` every `Y_i` is affine so this is immediate. It is in fact
true with no affineness of `X` at all: the transition `Y_i ⟶ Y_j` lies over `X` and both
projections to `X` are base changes of the morphisms `Spec B_i ⟶ Spec A` of affine schemes, hence
affine, so the transition is affine by cancellation. That is
`Stacks.EtaleCohomology.BaseChangeAlgebraSystem.isAffineHom_baseChange_map'`, now proved in that
generality, and with it `bcSysGen`, `bcPrecoverageGen`, `bcToLimitSmallGen` and
`bcToLimitSmallGen_transition` are all available for an arbitrary `X` over an affine `T`.

What the affineness was buying is the *object the cohomology is taken over*. For an affine `X`
the level `Y_i` is an object of its own small affine etale site and is the terminal one
(`AlgebraicGeometry.SmallAffineEtale.finalIsTerminal`, which carries `[IsAffine S]`), so the
cohomology of the site is the cohomology over `Y_i`. For a merely quasi-compact and
quasi-separated `Y_i` there is no such object: the small affine etale site of `Y_i` has no
terminal object, and the passage from the cohomology over an affine chart to the cohomology of
the site is the Cech / Mayer-Vietoris descent along a finite affine cover. **That descent is the
one hypothesis this file carries, and it is carried explicitly.**

It is carried in the exact shape in which the affine case discharges it. There the two
identifications are
`Stacks.EtaleCohomology.AffineLimitCohomology.rightDerivedSectionsLevelTerminalIso` and
`...rightDerivedSectionsLimitTerminalIso`, each saying that the right derived functors of
sections over a *terminal* object of a site are the sheaf cohomology of that site — the
`Ext`-groups out of the constant sheaf on `ℤ`. The hypotheses `hdLevel` and `hdLimit` below say
exactly that for the chart `W`, with no terminality available to prove it.

## `hdLimit` and `hdLevel` are not the Cech descent, and are false off the affine case

That last sentence is where this file was wrong, and the correction is the content of
`qcqsHdLimit_of_isTerminal` and `subsingleton_globalSections_of_hdLimit_zero` below.

An isomorphism between the right derived functors of sections over an object `W` of a site and
the cohomology of the whole site is, on *every* site, exactly the statement that `W` is terminal,
and it has no descent content at all. Both halves of that are proved:

* for a terminal `W` the isomorphism holds in every degree with no affineness anywhere
  (`Stacks.Cohomology.GlobalSections.rightDerivedSectionsIsoFunctorH`, and at this system
  `qcqsHdLimit_of_isTerminal`), and `rightDerivedSectionsLimitTerminalIso` carries no affineness
  hypothesis;
* conversely, in degree zero the isomorphism forces every abelian sheaf with no section over `W`
  to have no global section whatsoever
  (`Stacks.Cohomology.GlobalSections.subsingleton_hom_constantSheaf_of_subsingleton_sections`, and
  at this system `subsingleton_globalSections_of_hdLimit_zero`).

For a non-affine quasi-compact quasi-separated `Y` the second clause fails outright: with `Y` a
projective line over a field, the image of the chart the affine open `Y \ {∞}`, and the sheaf the
direct image of the constant sheaf on `ℤ` along `∞`, that sheaf has no section over the chart and
has `ℤ` as its global sections. So `hdLimit` is not an unproved lemma awaiting the Cech descent:
it is **false** for every non-affine `Y`, in **every** degree including zero, and cannot be
discharged. The theorems below that take it as a hypothesis are therefore, for a non-affine `Y`,
vacuous rather than conditional.

Nothing above weakens what is unconditional here: the colimit statement
`etaleCohomologyColimit_baseChange_qcqs_isColimit`, the propagation of the source's hypothesis to
the system, and the covering input are all unaffected.

## What the real gap is, and what is already proved towards it

The cohomology group that Stacks 03Q6 is about is the cohomology of the *site* of `Y`, which is
`raisedAffineEtaleCohomologyFunctor B cY.pt hY p` — the `Ext`-groups out of the constant sheaf —
and that group is already identified with the library's etale cohomology of the scheme `Y` by the
affineness-free `raisedAffineEtaleCohomologyFunctorIsoEtaleCohomology`. What is missing is
not an identification of that group but a *colimit statement for it*: Stacks 09YP is available
only over an **object** of the colimit site
(`Stacks.WeakSites.ColimitSiteCohomology.isColimitCohomologyCocone`), and for a non-affine `Y` the
cohomology of the site is the cohomology over no object of it. The gap is therefore

> Stacks 09YP over the terminal **sheaf**: that the cohomology `H^p(C_Y, colim f_i^{-1}F_i)` of
> the colimit site is the filtered colimit of the cohomologies `H^p(C_{Y_j}, F_j)` of the level
> sites,

whose vertex is `(Sheaf.Γ _ Ab).rightDerived p` — equivalently `Sheaf.functorH _ p`, by
`Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH` — rather than the derived sections
over a chart. In degree zero that statement is **proved**:
`Stacks.WeakSites.ColimitGlobalSections.globalSections_colimit_pullback_of_colimit`, over a finite
one-hypercover of the terminal sheaf at a level, and its two hypotheses `hlev` and `hC` — that the
transition images of the chosen hypercover, and its image in the site of `Y`, are again
one-hypercovers — are **discharged**, by
`…AffineEtaleTopOneHypercover.exists_finite_isTopOneHypercover_level_transition`
for any quasi-compact quasi-separated level; the degree-zero statement assembled at this system,
with no hypothesis left about covers, is
`Stacks.EtaleCohomology.AffineEtaleTopOneHypercover.globalSections_colimit_of_level`. That
discharge is *not* the geometry that the preimage of an affine open under an affine morphism is
affine, and it needs no affineness of any transition beyond what the site system itself needs: the
transition images of the objects attached to the affine opens of the level are objects of the
affine etale sites downstairs by construction, so their schemes are affine for free and the
preimage opens are never asked to be. **Degree zero is complete, for abelian sheaves as well
as for sheaves of sets.** The passage from sheaves of sets to the right derived functors of
`CategoryTheory.Sheaf.Γ` on abelian sheaves is proved, as
`Stacks.EtaleCohomology.AffineEtaleTopOneHypercover.globalSections_colimit_of_level_ab` and, at
the derived vertex Stacks 09YP is stated at,
`…rightDerivedZero_globalSections_colimit_of_level_ab`. That passage is not formal:
the forgetful functor from abelian sheaves is a *right* adjoint, so it has no reason to preserve
`colim f_i^{-1}F_i`, and `IsColimitPresentation`'s universal property quantifies only over
abelian sheaves — so the step is not "push the presentation through the forgetful functor" but
rather to go through Stacks 09YN's element-level consequences, which are statements about
elements of the very same sets. Sheafification does not enter the argument at all.

What remains is **positive degrees only**: that the colimit of the pullbacks of a pointwise
injective system is acyclic for the global sections of the colimit site. The object-wise form
`Stacks.WeakSites.ColimitSiteCohomology.cohomology_isZero_of_pointwise_injective` is proved, and it
and `...systemColimitSheaf_cohomology_isZero_of_pointwise_injective` are `public theorem`s of
`StacksFrontier/CategoryTheory/Sites/InverseSystem/CohomologyOfColimitOfFiniteSites.lean`.

The passage from the object-wise form to the terminal sheaf is reduced to **one named library
predicate**, in
`…/Sites/InverseSystem/GlobalSectionsAcyclicityOfColimitOfFiniteSites.lean`:

* `Stacks.WeakSites.ColimitSiteCohomology.vanishesOnObjects_of_pointwise_injective_presentation`
  is the object-wise acyclicity in the spelling 07A1 uses — condition (1) of that criterion for
  the colimit sheaf, `Stacks.Cohomology.VanishesOnObjects`, with no hypothesis beyond the system
  data.
  It is the object-wise statement read through
  `Stacks.Cohomology.SiteSections.cohomologyIsoRightDerivedSections`.
* `Stacks.Cohomology.isZero_rightDerivedΓ_of_isTotallyAcyclic` is part (3) of Stacks 0731 for an
  **abelian** sheaf, which the library had only for sheaves of modules
  (`isTotallyAcyclic_rightAcyclic_globalSections`, stated as right acyclicity of
  `SiteModules.globalSectionsFunctor`). For an abelian sheaf no induction is needed: total
  acyclicity is `Ext^p(ℤ_K^♯, -) = 0` for *every* sheaf of sets `K`, so taking `K` terminal and
  reading through `freeAbelianSheafTerminalIsoConstantSheaf` and
  `globalSectionsRightDerivedIsoFunctorH` gives the vanishing of `R^pΓ` at once.
* `Stacks.WeakSites.ColimitSiteCohomology.isTotallyAcyclic_of_pointwise_injective` and
  `...isZero_rightDerivedΓ_of_pointwise_injective` are the two conclusions — total acyclicity of
  `𝒢`, and its Γ-acyclicity in positive degrees — over the single hypothesis `hcech`, which is
  `Stacks.Cohomology.CechComplexExactPos K.toGrothendieck 𝒢`, condition (2) of 07A1 for the colimit
  sheaf.

So **the gap in positive degrees is exactly `CechComplexExactPos` for `𝒢`**, and nothing else.

Two routes to it are available.

* Stacks 0731(3), `Stacks.Cohomology.isTotallyAcyclic_rightAcyclic_globalSections`, via the
  criterion of Stacks 07A1, `isTotallyAcyclic_of_conditions`. Its condition (2)
  `CechComplexExactPos` is **not** an unproved input: it is a `def`, and it is proved — for an
  injective abelian sheaf outright and with no further hypothesis by
  `Stacks.Cohomology.cechComplexExactPos_of_injective`, and for the inverse image of an injective
  sheaf of modules by `Stacks.Cohomology.DerivedLowerShriek.cechComplexExactPos_inverseImage`;
  `cechComplexExactPos_of_cechComplexExact` and `cechComplexExactPos_of_isTotallyAcyclic` derive
  it from the two stronger conditions. Nor is 07A1 blocked by missing fibre products: its Cech
  nerve is taken in `Sheaf J (Type _)`, which has all limits. What *is* true about products is
  narrower: the small affine etale site of a non-separated qcqs scheme has no products over the
  terminal sheaf, so the hypercovering spectral sequence of Stacks 09VY, which this development
  carries, does not apply to it.
* `Stacks.Cohomology.ColimitsOfCohomology.isZero_rightDerived_globalSections_colimit_of_isIso`
  concludes the statement above verbatim — `IsZero (((Sheaf.Γ J Ab).rightDerived (n+1)).obj
  (colimit G))` for a filtered diagram `G` of injective abelian sheaves — with no appeal to 07A1
  anywhere in its proof, and Stacks 0GN3
  (`Stacks.Cohomology.ColimitsOfCohomology.isIso_colimit_post_rightDerived_globalSections`) and
  Stacks 073E are both proved. Its hypothesis `hlocal` is **not** what blocks it: 0GN3 as
  formalized discharges `hlocal` from its
  covering-set hypotheses (1)–(5) through Stacks 07A0, and Stacks 0GN4
  (`...isIso_colimit_post_rightDerived_globalSections_of_finite_covers`) reduces those five to four
  conditions on a *set of objects* of the site. What blocks this route is **prior to any covering
  set**: every statement in that family concludes about `CategoryTheory.Limits.colimit G` for an
  honest filtered diagram `G : I ⥤ Sheaf J Ab`, and this development has no such diagram. The
  colimit `colim_i f_i⁻¹F_i` is pinned only by the universal property
  `Stacks.WeakSites.ColimitSiteCohomology.IsColimitPresentation`, realised by `systemColimitSheaf`
  as a pointwise left Kan extension of presheaves; the implementation notes of Stacks 09YN and
  0EXJ say why — the diagram `i ↦ f_i⁻¹F_i` is not available as a functor, its transition maps
  being data and equations, so there is no cocone on it whose `IsColimit` could be asserted. Nor is
  there a functor `Sheaf (D.J j) Ab ⥤ Sheaf K.toGrothendieck Ab` for the colimit-site morphism
  `f_j`, only the level-to-level `InverseSystemOfFiniteSites.abelianSheafPullback`. So the
  filtered-colimit route needs that diagram built first, and only then a covering set.

So the first route's obstruction is exactly `CechComplexExactPos` for `𝒢`, and the second route's
is the absent diagram.

### The obstruction to the colimit statement

Acyclicity is not by itself Stacks 09YP over the terminal sheaf; what 03Q6 needs is the *colimit*
statement, an `IsColimit` whose vertex is `((Sheaf.Γ _ Ab).rightDerived p).obj 𝒢`. Assembling one
is blocked **before** any homological algebra, at the construction of the diagram it would be a
colimit of.

The degree-zero statement
`Stacks.WeakSites.ColimitGlobalSections.abelianGlobalSections_colimit_pullback_of_colimit` is not
an `IsColimit` and has no diagram: its map `ρ` on global sections is *quantified over* and pinned
only by `hρ` through `CategoryTheory.Sheaf.ΓRes`, and its second clause gives agreement after
restriction to the hypercover members rather than equality. Two things are needed to turn it into
a universal property, and they are of quite different character.

* The separatedness upgrade is **proved**:
  `…ColimitGlobalSections.abGamma_eq_of_eq_on_topOneHypercover` (and the gluing half,
  `…existsUnique_abGamma_of_matching`) is the sheaf condition over the terminal sheaf for `Sheaf.Γ`
  of an abelian sheaf, which the library had only for sheaves of sets.
  With it, the second clause does give equality of global sections at a further level.
* The diagram itself is **missing**, and this is the obstruction. A diagram
  `(Over i₀)ᵒᵖ ⥤ Ab`, `A ↦ (Sheaf.Γ (D.J A.left) Ab).obj (F.obj A.left)`, needs a map
  `Γ_j(F_j) ⟶ Γ_k(F_k)` for a transition `a : k ⟶ j`. The transition datum is
  `transition D F a : F_j ⟶ (D.u a)_* F_k`, so `Sheaf.Γ` of it lands in `Γ_j((D.u a)_* F_k)`, and
  the missing step is the identification

  > `u.sheafPushforwardContinuous Ab J K ⋙ Sheaf.Γ J Ab ≅ Sheaf.Γ K Ab`
  > for a functor `u` with `u.IsMorphismOfSites J K`,

  i.e. that restriction along a morphism of sites does not change global sections. For sheaves of
  **sets** this is **proved**, in
  `StacksFrontier/CategoryTheory/Sites/ConstantSheaf/MorphismOfSitesGlobalSections.lean`:
  `Stacks.ConstantSheaf.gammaCompPushforwardIso` proves it for a continuous `u` whose inverse image
  on sheaves of sets is left exact, and
  `Stacks.ConstantSheaf.gammaCompPushforwardIsoOfMorphismOfSites` is the form a consumer has, with
  `CategoryTheory.Functor.IsMorphismOfSites` as the only hypothesis — which every transition of an
  `InverseSystemOfFiniteSites` carries. The two statements the library already had both assume
  something this system cannot supply: `Stacks.ConstantSheaf.gammaCompRestrictionIsoOfFinal`
  assumes `[u.Final]`, which the transitions are not, a quasi-compact étale scheme over a level
  having no reason to map to the base change of a single affine object upstairs; and
  `Stacks.Cohomology.BiggerSiteGlobal.gammaCompRestrictionIso` (with
  `Stacks.ConstantSheaf.pushforwardSectionsIso`) assumes a terminal object on both sites, the very
  thing a site of affine objects over a non-affine scheme lacks. The proof of the new statement is
  the formal one: `IsMorphismOfSites` carries
  `PreservesFiniteLimits (u.sheafPullback (Type _) J K)` as a field,
  `Stacks.ConstantSheaf.isTerminal_constantSheaf_obj` says the constant sheaf on a singleton is a
  final sheaf, `Stacks.ConstantSheaf.inverseImageTerminalIso` carries it across the left exact
  inverse image, and `CategoryTheory.Sheaf.ΓObjEquivHom` turns global sections into morphisms out
  of it.

  The **abelian form is proved too**, in the same file:
  `Stacks.ConstantSheaf.gammaCompPushforwardIsoAb` and
  `...gammaCompPushforwardIsoAbOfMorphismOfSites` give `u_* ⋙ Γ(A, -) ≅ Γ(B, -)` on abelian sheaves
  with `IsMorphismOfSites` as the only hypothesis. It does not follow formally from the set-valued
  one: `Sheaf.Γ` for abelian coefficients is corepresented by the constant sheaf on `ℤ` rather than
  by a final sheaf, so what is needed is that the *abelian* inverse image takes the constant sheaf
  to the constant sheaf — the abelian half of [Stacks, Tag 00XO] — and left exactness of the
  inverse image on sheaves of *sets* does not say that. The two routes, with what each still owes,
  are recorded in the implementation notes of the new file: either transport the set-valued
  isomorphism along the restriction maps, which needs the compatibility of
  `CategoryTheory.Sheaf.ΓObjEquivHom` with `CategoryTheory.Sheaf.ΓRes` — a statement Mathlib does
  not have — in order to recognise the transported bijection as the canonical limit comparison and
  then conclude in `Ab` because `forget Ab` creates that limit; or prove
  `u^{-1}(**Z**_A^♯) ≅ **Z**_B^♯` directly. The second is the route taken, as
  `Stacks.ConstantSheaf.pullbackConstantSheafIsoAb`: the constant sheaf on `ℤ` is the free abelian
  sheaf on the final sheaf
  (`Stacks.Cohomology.ColimitsOfCohomology.freeAbelianSheafTerminalIsoConstantSheaf`), the inverse
  image commutes with the free abelian sheaf functor by uniqueness of left adjoints
  (`pullbackFreeAbelianSheafIso`, from `CategoryTheory.Presheaf.freeAbelianSheafAdj` and
  `CategoryTheory.Functor.lanAdjunction`, their right adjoints agreeing because `u_*` is
  restriction along `u.op`), and the free abelian sheaf functor does not distinguish the left Kan
  extension of the final presheaf from the final presheaf
  (`CategoryTheory.Presheaf.isIso_freeAbelianSheaf_map_of_W`, the `W`-membership being
  `w_lanTerminalToTerminal`, read through `CategoryTheory.GrothendieckTopology.W_iff`). The
  derivation of the `Γ` comparison from it is `gammaCompPushforwardIsoAbOfConstantSheafIso`, which
  goes through `ModuleSheafCohomology.globalSectionsRepresentation` and
  `CategoryTheory.Adjunction.homAddEquiv` and so never touches `CategoryTheory.Sheaf.ΓRes` — the
  reason route 1's missing `ΓObjEquivHom`/`ΓRes` compatibility is not an obstruction to this one.
  The first route is not taken and that compatibility is still absent from Mathlib.

  So the `Γ`-indexed diagram `(Over i₀)ᵒᵖ ⥤ Ab`, `A ↦ Γ_{A.left}(F_{A.left})`, can now be written
  down: the transition datum `transition D F a : F_j ⟶ (u_a)_* F_k` composed with
  `gammaCompPushforwardIsoAbOfMorphismOfSites` at the transition's own `IsMorphismOfSites` is the
  map `Γ_j(F_j) ⟶ Γ_k(F_k)`. Building that diagram, its cocone at `Γ(𝒢)` with legs from the
  `IsColimitPresentation` legs `ι` read through the same isomorphism at `uC j`, and the degree-zero
  `IsColimit` — whose separatedness input is
  `Stacks.WeakSites.ColimitGlobalSections.abGamma_eq_of_eq_on_topOneHypercover` — is what remains
  on this side.

  The diagram is best built at a **fixed level**: `InverseSystemOfFiniteSites.comp` is an
  *equality* of functors and `…isMorphismOfSites` is a *field*, so taking
  `A ↦ Γ_i((f_{A.hom})_* F_{A.left})` puts every arrow on the single site `D.J i` and needs the
  `Γ`-restriction isomorphism exactly once, at the vertex — no composition compatibility for that
  isomorphism, which is worth avoiding since it would not be free (`Hom(ℤ_L^♯, ℤ_L^♯) ≅ Γ_L(ℤ_L^♯)`
  contains `ℤ`, so two natural isomorphisms `(u ⋙ v)^{-1}ℤ_J^♯ ≅ ℤ_L^♯` can differ and nothing
  formal forces agreement with `CategoryTheory.Functor.sheafPullbackComp`). The arrows and their
  two laws are available:
  `Stacks.WeakSites.ColimitSiteCohomology.systemPushforwardMap` with
  `…systemPushforwardMap_id` and `…systemPushforwardMap_comp`, the transition of a system of
  abelian sheaves in adjoint sheaf form together with its identity and composition laws read
  through `abelianSheafPushforwardIdIso` and `abelianSheafPushforwardCompIso`; all three are
  `public`, as the two acyclicity lemmas are.

  What the `map_id` of that diagram then needs, and what is not available, is the **coherence of
  `abelianSheafPushforwardIdIso` against `abelianSheafPushforwardCompIso`** — that
  `(f_{A.hom})_*` of the identity-transition, followed by the composition comparison at
  `(𝟙, A.hom)` and the `eqToHom` of `Over.w`, is the identity. The library's `sectionsDiagram`
  sidesteps it by evaluating at an object of the site, where the whole bookkeeping is `eqToHom` and
  `sectionsMapTo_congr` closes it; at the level of sheaves it is a genuine coherence statement
  about `CategoryTheory.Functor.sheafPushforwardContinuousComp'` and
  `…sheafPushforwardContinuousId`, and neither Mathlib nor this development has it.

For the same reason the engine of Stacks 09YP over an object cannot simply be reused: every
constructor and proof step of it — `canonicalCohomologyDiagram`, `canonicalCohomologyCocone`,
`isColimitCohomologyCoconeEquiv`, the whole `ColimitResolution` block, and the five generic
homological helpers `isIso_homologyMap_map_of_rightAcyclic`,
`isColimit_mapCocone_homologyFunctor`, `liftFromResolution`, `quasiIso_single₀_of_monoCokernel`,
`exactAt_succ_of_monoCokernel` — is `private` to
`StacksFrontier/CategoryTheory/Sites/InverseSystem/CohomologyOfColimitOfFiniteSites.lean`, so a `Γ` mirror in a downstream file would have to
re-derive it. Only the *statement* vocabulary (`CohomologyCocone`, `IsCohomologyMap`,
`cohomologyCongr`, `IsColimitPresentation`, `systemColimitSheaf`) is public, and `CohomologyCocone`
itself is tied to an object: its `objIso` field names
`sheafSections (D.J A.left) _ |>.obj (op ((D.u A.hom).obj X))`, so a `Γ` version is a new
structure, not an instance of that one.

### `CechComplexExactPos` is not a covering-set consequence

Deriving `CechComplexExactPos` for `𝒢` from the levels does not reduce to asking
`Hom(ℤ_{K'_n}^♯, -)` to commute with the colimit for the Čech terms of an arbitrary surjection of
sheaves of sets, that is, to quasi-compactness of those terms. The reason is visible in the proof
of `Stacks.Cohomology.isTotallyAcyclic_of_conditions`.

Condition (2) is applied **exactly once**, inside
`Stacks.Cohomology.subsingleton_ext_freeAbelianSheaf_succ`, to the single epi that
`Stacks.Cohomology.exists_epi_subsingleton_ext` hands it, and only as the extension input of
`ext_eq_zero_of_exact_tower` at the top index. The acyclicity of the Čech *terms* in the degrees
`1 ≤ q ≤ n` is already supplied there by the induction hypothesis `ih`, which is quantified over
*all* presheaves of sets and is applied to those terms directly; and the `i = 0` input comes from
condition (1) through the chosen `K'`. So condition (2) contributes nothing but the top degree
`n + 1` — the very degree the induction is trying to reach. It is an induction-breaking input of
the same strength as the conclusion, not quasi-compactness in disguise, and no weakening of it to
epis with quasi-compact source, or with source in `S`, or with `F`-acyclic source, turns it into a
covering-set consequence. Two further observations say the same: the Čech terms of an epi one did
not choose are fibre powers that nothing about `S` bounds, `S` being stable under *covering* a
product rather than under taking one; and there is no refinement step available, since the induced
map runs `Hom(ℤ_{K'_•}^♯, F) ⟶ Hom(ℤ_{K''_•}^♯, F)`, so exactness for a refinement does not give
it for the original.

What is missing is therefore the top-degree vanishing itself, and the covering set bears on it
only through condition (1): the sharpest statement is
`Stacks.Cohomology.subsingleton_ext_freeAbelianSheaf_of_mem_finiteCoproductSheafifiedYoneda`, that
a sheaf acyclic over every *object* is acyclic over every member of 0GN4's covering set, which
instantiated at `vanishesOnObjects_of_pointwise_injective_presentation` gives acyclicity of
`colim_i f_i⁻¹F_i` on all of `S` — condition (1) restated, not condition (2).

## What is proved from it, and what is not hypothesised

The colimit itself is **not** hypothesised. `IsColimit E.cocone` for an arbitrary chart `W` of a
level is `Stacks.EtaleCohomology.QcqsLimitCohomology.etaleCohomologyColimit_isColimit`, which is
Stacks 09YQ for arbitrary levels and needs only the transitions affine; instantiated at the
system of base changes it is `etaleCohomologyColimit_baseChange_qcqs_isColimit` below, which
carries no hypothesis beyond the source's own and is unconditional. What the carried descent is
used for is only the *identification of the groups*: that the vertex is the etale cohomology
group `H^p_etale(Y, 𝒢')` of the scheme `Y` and that the groups of the diagram are the etale
cohomology groups `H^p_etale(Y_j, F_j')` of the schemes `Y_j`. The second half of each of those
identifications is unconditional and proved —
`BaseChangeAlgebraSystem.raisedAffineEtaleCohomologyFunctorIsoEtaleCohomology` at the limit and
`AffineLimitCohomology.levelCohomologyFunctorIsoEtaleCohomology` at a level, neither of which
needs any affineness of its scheme, both being the cohomological form of Stacks 04HR.

## Main results

* `quasiCompact_baseChange_fst`, `quasiSeparated_baseChange_fst`, `compactSpace_baseChange_obj`:
  **the source's hypothesis propagates to the system.** If `X ⟶ T` is quasi-compact and
  quasi-separated then so is every projection `Y_i ⟶ Z_i`, and every level `Y_i` is then a
  quasi-compact scheme, `Z_i` being affine. This is what makes the covering input of the Cech
  step available at every level.
* `exists_finite_affine_cover_level`: every level of the system of base changes is covered by
  finitely many objects of its own small affine etale site — the covering input of the carried
  descent, at this system.
* `etaleCohomologyColimit_baseChange_qcqs_isColimit`: **Stacks 03Q6 at the source's generality on
  `X`, with the cohomology over a chart.** Unconditional.
* `qcqsCoconeVertexIsoEtaleCohomology` and `qcqsDiagramObjIsoEtaleCohomology`: the vertex and the
  groups of the diagram, identified with the etale cohomology of `Y` and of the `Y_j`, over the
  carried descent.
* `etaleCohomologyColimit_baseChange_qcqs_etale_isColimit`: **Stacks 03Q6 for a quasi-compact
  quasi-separated `X ⟶ Spec A`**, over the carried descent.
* `qcqsHdLimit_of_isTerminal` and `qcqsHdLevel_of_isTerminal`: **the carried descent, discharged
  for a terminal chart**, in every degree and with no affineness of anything.
* `etaleCohomologyColimit_baseChange_qcqs_etale_isColimit_of_isTerminal`: the main statement with
  the carried descent discharged from terminality of the chart, hence with no cohomological
  hypothesis.
* `subsingleton_globalSections_of_hdLimit_zero`: **what the carried descent asserts**, and why it
  is false off the affine case — a sheaf with no section over the chart would have no global
  section.
* `isZero_rightDerivedΓ_colimitSheaf_baseChange_qcqs`: **Stacks 03Q6 at a qcqs `X` carrying no
  terminality hypothesis at all** — the acyclicity half of the tag, that the right derived
  functors of `CategoryTheory.Sheaf.Γ` vanish on the colimit sheaf in positive degrees. Because
  `Sheaf.Γ` is sections over the terminal *sheaf*, no chart enters and neither `hdLimit` nor
  `hdLevel` appears, so unlike the statements above this one is not vacuous for a non-affine `Y`.
  Its single hypothesis is `Stacks.Cohomology.CechComplexExactPos`, which the registration string
  and the section below record as not a consequence of the covering set.

## Implementation notes

The limit cone `cY` of the system of base changes is a hypothesis rather than a construction, as
it is in `etaleCohomologyColimit_baseChange_isColimit` and in Stacks 09YQ. For an affine `X` the
canonical choice is `systemLimitCone T X Z`, whose apex is `(lim_i Spec B_i) ×_{Spec A} X` by
Stacks 01YW; its construction goes through `hasLimit_baseChange`, which uses that the levels are
affine, so at a qcqs `X` the limit is taken as given. It exists — a directed system of schemes
with affine transition morphisms over a qcqs base has a limit — but that is Stacks 01ZA and is
not what this file is about.

The system `F` of abelian sheaves on the levels, the sheaf `𝒢` presenting `colim_i f_i^{-1} F_i`,
its legs `ι`, its universal property `hcolim` and the cohomology cocone `E` are hypotheses for
the reasons given in `QcqsEtaleCohomologyColimit.lean`: they are given data in Stacks 09YP and in
the source, and `Stacks.EtaleCohomology.QcqsLimitCohomology.etaleCohomologyCocone` exhibits an
`E`, so no statement here is vacuous.

Nothing here closes the two further gaps the affine case owes: `F` is a given system of abelian
sheaves on the levels rather than the system of inverse images `(Y_i ⟶ X)^{-1} F` of a single
sheaf on `X`, and the transition maps of the cohomology diagram are not identified with the
transition maps of the etale cohomology groups. Both are discussed in
`BaseChangeAlgebraSystemInverseImages.lean` and `LevelBaseChangeComparison.lean`; neither is
affected by the generality of `X`.

## References

* [Stacks 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
* [Stacks 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks 09YP](https://stacks.math.columbia.edu/tag/09YP)
* [Stacks 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
* [Stacks 04HR](https://stacks.math.columbia.edu/tag/04HR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

universe u

namespace Stacks.EtaleCohomology.QcqsBaseChange

open AlgebraicGeometry CategoryTheory.Sites.InverseSystem
open Stacks.EtaleCohomology.AffineLimitCohomology
open Stacks.EtaleCohomology.BaseChangeAlgebraSystem
open Stacks.EtaleCohomology.QcqsLimitCohomology
open Stacks.WeakSites.ColimitSiteCohomology

attribute [local instance] isCocontinuous_smallAffineEtaleInclusion

/-! `EnoughInjectives` and additivity of global sections for abelian sheaves on a small site are
stated rather than registered in `Stacks.Cohomology.ColimitsOfCohomology`; every module of the
global-cohomology development installs them locally, and the acyclicity statement of Stacks 03Q6
instantiated below needs the second. The global instance set is unchanged. -/

attribute [local instance] Stacks.Cohomology.ColimitsOfCohomology.enoughInjectives_sheaf_ab
  Stacks.Cohomology.ColimitsOfCohomology.additive_globalSections_ab
  isDenseSubsite_smallAffineEtaleInclusion hasSheafify_smallAffineEtale hasSheafify_smallEtale
  locallySmall_smallAffineEtale locallySmall_smallEtale enoughInjectives_smallAffineEtale
  enoughInjectives_smallEtale hasExt_smallAffineEtale hasExt_smallEtale
  restrictToAffineEtale_isEquivalence CategoryTheory.AsSmall.isDenseSubsite_up
  hasSheafify_raisedAffineEtale locallySmall_raisedAffineEtale
  enoughInjectives_raisedAffineEtale hasExt_raisedAffineEtale

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (T : Scheme.{u}) (X : Over T) (Z : Iᵒᵖ ⥤ Over T)
  [IsAffine T] [∀ i, IsAffine (Z.obj i).left]

/-! ### The source's hypothesis on `X`, propagated to the system

The levels `Y_i = Z_i ×_T X` are quasi-compact and quasi-separated as soon as `X ⟶ T` is: the
projection `Y_i ⟶ Z_i` is the base change of `X ⟶ T`, and `Z_i` is affine. Quasi-compactness is
what the covering input of the Cech step asks for.
-/

omit [Nonempty I] [IsDirected I (· ≤ ·)] [IsAffine T] in
/-- **The projection `Y_i = Z_i ×_T X ⟶ Z_i` is quasi-compact** when `X ⟶ T` is, being its base
change. -/
theorem quasiCompact_baseChange_fst [QuasiCompact X.hom] (i : Iᵒᵖ) :
    QuasiCompact (Limits.pullback.fst (Z.obj i).hom X.hom) :=
  inferInstance

omit [Nonempty I] [IsDirected I (· ≤ ·)] [IsAffine T] in
/-- **The projection `Y_i = Z_i ×_T X ⟶ Z_i` is quasi-separated** when `X ⟶ T` is, being its base
change. -/
theorem quasiSeparated_baseChange_fst [QuasiSeparated X.hom] (i : Iᵒᵖ) :
    QuasiSeparated (Limits.pullback.fst (Z.obj i).hom X.hom) :=
  inferInstance

omit [Nonempty I] [IsDirected I (· ≤ ·)] [IsAffine T] in
/-- **Every level of the system of base changes is a quasi-compact scheme** when `X ⟶ T` is
quasi-compact: the projection `Y_i ⟶ Z_i` is quasi-compact and `Z_i` is affine, hence a
quasi-compact scheme. -/
instance compactSpace_baseChange_obj [QuasiCompact X.hom] (i : Iᵒᵖ) :
    CompactSpace ((baseChange T X Z).obj i) :=
  haveI : CompactSpace ((Z.obj i).left : Scheme.{u}) := inferInstance
  @QuasiCompact.compactSpace_of_compactSpace _ _ _ (quasiCompact_baseChange_fst T X Z i) _

/-- **The covering input of the carried descent, at this system.** Every level `Y_i` of the system
of base changes is covered by finitely many objects of its own small affine etale site: it is a
quasi-compact scheme by `compactSpace_baseChange_obj`, so
`Stacks.EtaleCohomology.QcqsLimitCohomology.exists_finite_jointlySurjective_smallAffineEtale`
applies to it. The descent of cohomology along such a cover is the hypothesis `hdLevel` of the
main statement and is not performed here. -/
theorem exists_finite_affine_cover_level [QuasiCompact X.hom]
    (B : AlgebraicGeometry.BigEtaleSite.{u})
    (hD : ∀ i, B.Contains ((baseChange T X Z).obj i)) (i : Iᵒᵖ) :
    ∃ (K : Type u) (_ : Finite K)
      (V : K → AlgebraicGeometry.SmallAffineEtale B ((baseChange T X Z).obj i) (hD i)),
      ∀ x : ((baseChange T X Z).obj i : Scheme.{u}), ∃ (k : K)
        (y : (AlgebraicGeometry.SmallAffineEtale.toScheme B
          ((baseChange T X Z).obj i) (hD i)).obj (V k)),
        (structMap B ((baseChange T X Z).obj i) (hD i) (V k)).base y = x :=
  exists_finite_jointlySurjective_smallAffineEtale B ((baseChange T X Z).obj i) (hD i)

/-! ### Stacks 03Q6 at the source's generality on `X`, over a chart

Nothing in this subsection is conditional. The site system of Stacks 0EYL for the diagram of base
changes exists for an arbitrary `X` over an affine `T`, the transitions being affine
(`isAffineHom_baseChange_map'`), and Stacks 09YQ at arbitrary levels then gives the colimit
statement over an arbitrary object of a level.
-/

variable (cY : Cone (baseChange T X Z)) (hcY : IsLimit cY)
  (B : AlgebraicGeometry.BigEtaleSite.{u})
  (hD : ∀ i, B.Contains ((baseChange T X Z).obj i)) (hY : B.Contains cY.pt)
  (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{u, u, u + 1, u + 1}
    (bcSysGen T X Z cY hcY B hD hY))
  (𝒢 : Sheaf (bcPrecoverageGen T X Z cY hcY B hD hY).toGrothendieck Ab.{u + 1})
  (ι : ∀ j, (F.obj j).obj ⟶ (bcToLimitSmallGen T X Z cY hcY B hD hY j).op ⋙ 𝒢.obj)

/-- **Stacks 03Q6 for an arbitrary `X` over an affine base, with the cohomology over a chart of a
level.** Let `T = Spec A` be affine, let `Z_i = Spec B_i` be a diagram of affine schemes over `T`
indexed by a nonempty directed `Iᵒᵖ`, and let `X` be **any** scheme over `T` — in particular the
source of a quasi-compact quasi-separated `X ⟶ Spec A`, which is the source's hypothesis. Form
the system `Y_i = Z_i ×_T X` and let `cY` be a limit cone of it, with apex `Y`. Let `F` be a
system of abelian sheaves on the levels of the site system of Stacks 0EYL, let `𝒢` with legs `ι`
present the colimit `colim_i f_i^{-1} F_i`, let `W` be an object of the level `i` and let `p` be a
degree. Then the canonical cohomology cocone over `W` is a colimit cocone.

This is `Stacks.EtaleCohomology.QcqsLimitCohomology.etaleCohomologyColimit_isColimit`
instantiated at the system of base changes. The instantiation is what the generalisation of
`isAffineHom_baseChange_map'` makes possible: that statement needs only the transition morphisms of
the diagram affine, and the affineness of `X` entered the registered affine case of Stacks 03Q6
nowhere else than in the identification of the object the cohomology is taken over.

The groups here are the right-derived `sheafSections` over `W` and its transition images, not the
etale cohomology of the schemes of the system; that identification is
`etaleCohomologyColimit_baseChange_qcqs_etale_isColimit`, and it is where the Cech descent is
carried. -/
def etaleCohomologyColimit_baseChange_qcqs_isColimit
    (hcolim : IsColimitPresentation.{u, u, u + 1, u + 1} (bcSysGen T X Z cY hcY B hD hY)
      (bcToLimitSmallGen T X Z cY hcY B hD hY) (bcToLimitSmallGen_transition T X Z cY hcY B hD hY)
      (bcPrecoverageGen T X Z cY hcY B hD hY) F 𝒢 ι)
    (i : (bcSysGen T X Z cY hcY B hD hY).I) (W : (bcSysGen T X Z cY hcY B hD hY).C i) (p : ℕ)
    (E : CohomologyCocone.{u, u, u + 1, u + 1} (bcSysGen T X Z cY hcY B hD hY)
      (bcToLimitSmallGen T X Z cY hcY B hD hY) (bcToLimitSmallGen_transition T X Z cY hcY B hD hY)
      (bcPrecoverageGen T X Z cY hcY B hD hY) F 𝒢 ι i W p) :
    IsColimit E.cocone :=
  etaleCohomologyColimit_isColimit.{u, u} (baseChange T X Z) cY B hD hY hcY F 𝒢 ι hcolim i W p E

/-! ### Stacks 03Q6 at a qcqs `X` with no terminality hypothesis

Everything else in this file that reaches etale cohomology carries `hdLimit` or `hdLevel`, and
those are terminality of the chart, hence false for a non-affine `Y`. The statement below carries
neither. It is the *acyclicity* half of the tag — the vanishing of the right derived functors of
`CategoryTheory.Sheaf.Γ` on the colimit sheaf in positive degrees — which is about the terminal
*sheaf* of the limit site and so needs no chart at all.
-/

/-- **Stacks 03Q6 at a quasi-compact quasi-separated `X`, with no terminality hypothesis.** Let
`T = Spec A` be affine, let `Z_i = Spec B_i` be a diagram of affine schemes over `T` indexed by a
nonempty directed `Iᵒᵖ`, and let `X` be any scheme over `T` — in particular the source of a
quasi-compact quasi-separated `X ⟶ Spec A`, which is the source's own hypothesis. Form the system
`Y_i = Z_i ×_T X` with limit `Y`, let `F` be a system of **injective** abelian sheaves on the
levels of the site system of Stacks 0EYL, and let `𝒢` with legs `ι` present the colimit
`colim_i f_i^{-1}F_i`. Then the right derived functors of `CategoryTheory.Sheaf.Γ` vanish on `𝒢`
in every positive degree.

This is `Stacks.WeakSites.ColimitSiteCohomology.isZero_rightDerivedΓ_of_pointwise_injective`
instantiated at `bcSysGen`; the four descent hypotheses of the general statement are discharged,
not assumed, by `toLimitSmall_obj_descends`, `toLimitSmall_hom_descends`,
`toLimitSmall_hom_eventually_eq` and `mem_limitSitePrecoverage_iff`.

`Sheaf.Γ` is sections over the terminal *sheaf*, which on a site with no terminal object is not
the derived sections over any object; that is exactly why no chart, and so no terminality, enters.
The one carried hypothesis is `hcech`, discussed in the registration string and in the module
documentation.

This is a partial form of [Stacks, Tag 03Q6]; the registered statement is
`Stacks.EtaleCohomology.ColimitBaseChange.isIso_colimitDesc_algebraCohomologyCocone`. -/
theorem isZero_rightDerivedΓ_colimitSheaf_baseChange_qcqs
    (hF : ∀ i, CategoryTheory.Injective (F.obj i))
    (hcolim : IsColimitPresentation.{u, u, u + 1, u + 1} (bcSysGen T X Z cY hcY B hD hY)
      (bcToLimitSmallGen T X Z cY hcY B hD hY) (bcToLimitSmallGen_transition T X Z cY hcY B hD hY)
      (bcPrecoverageGen T X Z cY hcY B hD hY) F 𝒢 ι)
    (hcech : Stacks.Cohomology.CechComplexExactPos
      (bcPrecoverageGen T X Z cY hcY B hD hY).toGrothendieck 𝒢)
    (p : ℕ) (hp : 0 < p) :
    IsZero ((((Sheaf.Γ (bcPrecoverageGen T X Z cY hcY B hD hY).toGrothendieck
      Ab.{u + 1}).rightDerived p)).obj 𝒢) :=
  isZero_rightDerivedΓ_of_pointwise_injective.{u, u, u + 1}
    (bcSysGen T X Z cY hcY B hD hY) (bcToLimitSmallGen T X Z cY hcY B hD hY)
    (bcToLimitSmallGen_transition T X Z cY hcY B hD hY)
    (toLimitSmall_obj_descends.{u, u} (baseChange T X Z) cY B hD hY hcY)
    (toLimitSmall_hom_descends.{u, u} (baseChange T X Z) cY B hD hY hcY)
    (toLimitSmall_hom_eventually_eq.{u, u} (baseChange T X Z) cY B hD hY hcY)
    (bcPrecoverageGen T X Z cY hcY B hD hY)
    (mem_limitSitePrecoverage_iff.{u, u} (baseChange T X Z) cY B hD hY hcY)
    F hF 𝒢 ι hcolim hcech p hp

/-! ### Terminality of the chart, carried, and why it is not the Cech descent

The two hypotheses below say that sections over the chart `W` compute the cohomology of the site.
They are not the Cech / Mayer-Vietoris descent along a finite affine cover, and the difference
is not a nuance: since
`raisedAffineEtaleCohomologyFunctor` is by definition `Sheaf.functorH`, the cohomology of the
whole site, each hypothesis asserts `R^p Γ_W(-) ≅ H^p(site, -)`, which on any site is exactly
terminality of `W` — sufficient by `rightDerivedSectionsIsoFunctorH`, and necessary already in
degree zero by `subsingleton_hom_constantSheaf_of_subsingleton_sections`.

So for a non-affine `Y` these hypotheses are *false*, not merely unproved, and anything carrying
them is vacuous there; `subsingleton_globalSections_of_hdLimit_zero` is the obstruction at this
system. Where the chart's image is terminal, equivalently `Y` affine, they are discharged in
every degree by `qcqsHdLimit_of_isTerminal` and `qcqsHdLevel_of_isTerminal`, which route through
the general `rightDerivedSectionsIsoFunctorH` rather than through the former affine-only
`rightDerivedSectionsLimitTerminalIso` and `rightDerivedSectionsLevelTerminalIso`.

The genuine remaining gap is recorded in the `@[stacks 03Q6]` string below: Stacks 09YP over the
terminal *sheaf* rather than over an object of the colimit site.
-/

section Descent

variable (i : (bcSysGen T X Z cY hcY B hD hY).I) (W : (bcSysGen T X Z cY hcY B hD hY).C i) (p : ℕ)

/-- **The vertex of the cohomology cocone is the etale cohomology group `H^p_etale(Y, 𝒢')`**,
given the carried descent at the limit. The hypothesis `hdLimit` identifies the right-derived
sections over the image of the chart `W` in the site of `Y` with the cohomology of that site, and
`raisedAffineEtaleCohomologyFunctorIsoEtaleCohomology` — the cohomological form of Stacks 04HR
composed with the universe raise, needing no affineness of `Y` — identifies that cohomology with
the library's etale cohomology of `Y`. -/
def qcqsCoconeVertexIsoEtaleCohomology
    (hdLimit : (((sheafSections (bcPrecoverageGen T X Z cY hcY B hD hY).toGrothendieck
          Ab.{u + 1}).obj
        (op ((bcToLimitSmallGen T X Z cY hcY B hD hY i).obj W))).rightDerived p) ≅
      raisedAffineEtaleCohomologyFunctor B cY.pt hY p) :
    ((((sheafSections (bcPrecoverageGen T X Z cY hcY B hD hY).toGrothendieck Ab.{u + 1}).obj
          (op ((bcToLimitSmallGen T X Z cY hcY B hD hY i).obj W))).rightDerived p).obj 𝒢) ≅
      (Stacks.EtaleCohomology.etaleCohomologyFunctor B ⟨cY.pt, hY⟩ p).obj
        ((raisedToSmallEtale B cY.pt hY).obj 𝒢) :=
  (hdLimit ≪≫ raisedAffineEtaleCohomologyFunctorIsoEtaleCohomology B cY.pt hY p).app 𝒢

/-- **Stacks 03Q6 for a quasi-compact and quasi-separated `X ⟶ Spec A`.** Let `A` be a ring
presented as an affine `T = Spec A`, let `(B_i)` be a system of `A`-algebras presented as a
diagram `Z` of affine schemes over `T` indexed by a nonempty directed `Iᵒᵖ`, and let `X ⟶ T` be
quasi-compact and quasi-separated. Form `Y_i = Z_i ×_T X`, let `cY` be a limit cone with apex
`Y`, and let `F`, `𝒢`, `ι`, `hcolim` be a system of abelian sheaves on the levels together with a
presentation of `colim_i f_i^{-1} F_i`. Then, for every degree `p`,

`H^p_etale(Y, 𝒢') = colim_i H^p(Y_i, F_i)`

is a filtered colimit: the canonical cohomology cocone, with its vertex transported onto the
etale cohomology group of the scheme `Y`, is a colimit cocone. The groups of the diagram are the
etale cohomology groups `H^p_etale(Y_j, F_j')` of the levels, by
`qcqsDiagramObjIsoEtaleCohomology`.

The colimit is unconditional: it is `etaleCohomologyColimit_baseChange_qcqs_isColimit`, Stacks
09YQ at arbitrary levels instantiated at this system. The two hypotheses `hdLimit` and `hdLevel`
are used only to name the groups, and they are the Cech descent; see the module documentation.

This is a partial form of [Stacks, Tag 03Q6]; the registered statement is
`Stacks.EtaleCohomology.ColimitBaseChange.isIso_colimitDesc_algebraCohomologyCocone`. -/
def etaleCohomologyColimit_baseChange_qcqs_etale_isColimit [QuasiCompact X.hom]
    [QuasiSeparated X.hom]
    (hcolim : IsColimitPresentation.{u, u, u + 1, u + 1} (bcSysGen T X Z cY hcY B hD hY)
      (bcToLimitSmallGen T X Z cY hcY B hD hY) (bcToLimitSmallGen_transition T X Z cY hcY B hD hY)
      (bcPrecoverageGen T X Z cY hcY B hD hY) F 𝒢 ι)
    (E : CohomologyCocone.{u, u, u + 1, u + 1} (bcSysGen T X Z cY hcY B hD hY)
      (bcToLimitSmallGen T X Z cY hcY B hD hY) (bcToLimitSmallGen_transition T X Z cY hcY B hD hY)
      (bcPrecoverageGen T X Z cY hcY B hD hY) F 𝒢 ι i W p)
    (hdLimit : (((sheafSections (bcPrecoverageGen T X Z cY hcY B hD hY).toGrothendieck
          Ab.{u + 1}).obj
        (op ((bcToLimitSmallGen T X Z cY hcY B hD hY i).obj W))).rightDerived p) ≅
      raisedAffineEtaleCohomologyFunctor B cY.pt hY p) :
    IsColimit (E.cocone.extend
      (qcqsCoconeVertexIsoEtaleCohomology T X Z cY hcY B hD hY 𝒢 i W p hdLimit).hom) :=
  IsColimit.ofIsoColimit
    (etaleCohomologyColimit_baseChange_qcqs_isColimit T X Z cY hcY B hD hY F 𝒢 ι hcolim i W p E)
    (Cocones.ext
      (qcqsCoconeVertexIsoEtaleCohomology T X Z cY hcY B hD hY 𝒢 i W p hdLimit) fun _ => rfl)


/-! ### What the carried descent asserts, and the one case in which it is discharged

The two hypotheses above are isomorphisms between the right derived functors of sections over a
*chart* and the cohomology of the *whole site*. On any site that is exactly the statement that the
chart is terminal, and nothing weaker:
`Stacks.Cohomology.GlobalSections.rightDerivedSectionsIsoFunctorH` proves it for a terminal chart,
with no affineness anywhere, and
`Stacks.Cohomology.GlobalSections.subsingleton_hom_constantSheaf_of_subsingleton_sections` extracts
from it, in degree zero, that every abelian sheaf with no section over the chart has no global
section at all. The two lemmas below are those two statements at this system.
-/

/-- **The carried descent at the limit, discharged for a terminal chart.** If the image of the
chart `W` in the site of `Y` is a terminal object of that site then `hdLimit` holds, in every
degree and with no affineness of `X`, of `Y` or of the levels: it is
`Stacks.EtaleCohomology.AffineLimitCohomology.rightDerivedSectionsLimitTerminalIso`, which this
development carries without an affineness hypothesis.

For an affine `X` the limit `Y` is affine and the image of the terminal object of a level is
terminal (`AffineLimitCohomology.toLimitLevelTerminal_isTerminal`), which is how the registered
affine case of Stacks 03Q6 discharges the hypothesis. For a quasi-compact quasi-separated `X` with
`Y` not affine the small affine etale site of `Y` has no terminal object, so this lemma does not
apply and `hdLimit` is not merely unproved — see
`subsingleton_globalSections_of_hdLimit_zero`. -/
def qcqsHdLimit_of_isTerminal
    (hW : IsTerminal ((bcToLimitSmallGen T X Z cY hcY B hD hY i).obj W)) :
    (((sheafSections (bcPrecoverageGen T X Z cY hcY B hD hY).toGrothendieck Ab.{u + 1}).obj
        (op ((bcToLimitSmallGen T X Z cY hcY B hD hY i).obj W))).rightDerived p) ≅
      raisedAffineEtaleCohomologyFunctor B cY.pt hY p :=
  rightDerivedSectionsLimitTerminalIso.{u, u} (baseChange T X Z) cY B hY _ hW p

/-- **The carried descent at a level, discharged for a terminal chart.** If the transition image of
the chart `W` at the level `A.left` is terminal there then `hdLevel` holds at `A`, in every degree
and with no affineness. This is
`Stacks.EtaleCohomology.AffineLimitCohomology.rightDerivedSectionsLevelTerminalIso`. -/
def qcqsHdLevel_of_isTerminal (A : Over i)
    (hW : IsTerminal (((bcSysGen T X Z cY hcY B hD hY).u A.hom).obj W)) :
    (((sheafSections ((bcSysGen T X Z cY hcY B hD hY).J A.left) Ab.{u + 1}).obj
        (op (((bcSysGen T X Z cY hcY B hD hY).u A.hom).obj W))).rightDerived p) ≅
      levelCohomologyFunctor (baseChange T X Z) cY B hD hY hcY A.left p :=
  rightDerivedSectionsLevelTerminalIso.{u, u} (baseChange T X Z) cY B hD hY hcY A.left _ hW p

/-- **Stacks 03Q6 for a quasi-compact quasi-separated `X ⟶ Spec A`, with the carried descent
discharged from terminality of the chart.** This is
`etaleCohomologyColimit_baseChange_qcqs_etale_isColimit` with its hypothesis `hdLimit` replaced by
the hypothesis that the image of the chart in the site of `Y` is terminal, which is what
`qcqsHdLimit_of_isTerminal` turns into `hdLimit`.

It carries no cohomological hypothesis. What it does not do is cover a non-affine `Y`: the small
affine etale site of such a `Y` has no terminal object, so the hypothesis is unsatisfiable there,
and by `subsingleton_globalSections_of_hdLimit_zero` so is `hdLimit` itself. The genuine
higher-degree descent for a qcqs `Y` is not this statement; see the module documentation.

This is a partial form of [Stacks, Tag 03Q6]; the registered statement is
`Stacks.EtaleCohomology.ColimitBaseChange.isIso_colimitDesc_algebraCohomologyCocone`. -/
def etaleCohomologyColimit_baseChange_qcqs_etale_isColimit_of_isTerminal [QuasiCompact X.hom]
    [QuasiSeparated X.hom]
    (hcolim : IsColimitPresentation.{u, u, u + 1, u + 1} (bcSysGen T X Z cY hcY B hD hY)
      (bcToLimitSmallGen T X Z cY hcY B hD hY) (bcToLimitSmallGen_transition T X Z cY hcY B hD hY)
      (bcPrecoverageGen T X Z cY hcY B hD hY) F 𝒢 ι)
    (E : CohomologyCocone.{u, u, u + 1, u + 1} (bcSysGen T X Z cY hcY B hD hY)
      (bcToLimitSmallGen T X Z cY hcY B hD hY) (bcToLimitSmallGen_transition T X Z cY hcY B hD hY)
      (bcPrecoverageGen T X Z cY hcY B hD hY) F 𝒢 ι i W p)
    (hW : IsTerminal ((bcToLimitSmallGen T X Z cY hcY B hD hY i).obj W)) :
    IsColimit (E.cocone.extend
      (qcqsCoconeVertexIsoEtaleCohomology T X Z cY hcY B hD hY 𝒢 i W p
        (qcqsHdLimit_of_isTerminal T X Z cY hcY B hD hY i W p hW)).hom) :=
  etaleCohomologyColimit_baseChange_qcqs_etale_isColimit T X Z cY hcY B hD hY F 𝒢 ι i W p hcolim E
    (qcqsHdLimit_of_isTerminal T X Z cY hcY B hD hY i W p hW)

/-- **What `hdLimit` asserts in degree zero: the chart detects global sections.** If `hdLimit`
holds in degree zero then every abelian sheaf on the site of `Y` whose sections over the image of
the chart `W` vanish has no nonzero morphism out of the constant sheaf on `ℤ`, that is, no nonzero
global section.

This is what makes `hdLimit` a statement about `W` being terminal rather than a descent statement.
It is true for an affine `Y`, where the image of a level's terminal object is terminal and the
assertion is the sheaf axiom for the maximal sieve. It is **false** for a non-affine
quasi-compact quasi-separated `Y`: take for `Y` a projective line over a field, for the image of
`W` the affine chart `Y \ {∞}`, and for the sheaf the direct image of the constant sheaf on `ℤ`
along the closed point `∞`. That sheaf has no section over any etale `Y`-scheme missing `∞`, in
particular none over the chart, and its global sections are `ℤ`. So the hypothesis `hdLimit`
cannot be discharged for a non-affine `Y` in any degree, and in particular it is not the
higher-degree Cech descent: it already fails in degree zero, where the Cech descent is a theorem
(`Stacks.WeakSites.ColimitGlobalSections.globalSections_colimit_pullback_of_colimit`).

The scheme-level counterexample is not formalised here; what is formalised is the implication,
which is what identifies the content of the hypothesis. -/
theorem subsingleton_globalSections_of_hdLimit_zero
    (hdLimit : (((sheafSections (bcPrecoverageGen T X Z cY hcY B hD hY).toGrothendieck
          Ab.{u + 1}).obj
        (op ((bcToLimitSmallGen T X Z cY hcY B hD hY i).obj W))).rightDerived 0) ≅
      raisedAffineEtaleCohomologyFunctor B cY.pt hY 0)
    (hzero : Subsingleton
      (𝒢.val.obj (op ((bcToLimitSmallGen T X Z cY hcY B hD hY i).obj W)))) :
    Subsingleton
      ((constantSheaf (bcPrecoverageGen T X Z cY hcY B hD hY).toGrothendieck
        Ab.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ 𝒢) :=
  Stacks.Cohomology.GlobalSections.subsingleton_hom_constantSheaf_of_subsingleton_sections
    (bcPrecoverageGen T X Z cY hcY B hD hY).toGrothendieck _ hdLimit 𝒢 hzero

/-- **Every group of the cohomology diagram of Stacks 03Q6 at a qcqs `X` is an etale cohomology
group of a level**, given the carried descent at that level. The value of the diagram at an arrow
`A : j ⟶ i` is `H^p_etale(Y_j, F_j')`, where `F_j'` is the abelian sheaf on the small etale site
of `Y_j` that `F_j` comes from.

The hypothesis `hdLevel` identifies the right-derived sections over the transition image of the
chart `W` with the cohomology of the level site, and
`levelCohomologyFunctorIsoEtaleCohomology` — the cohomological form of Stacks 04HR through the
small model of the level, needing no affineness of `Y_j` — identifies that with the etale
cohomology of `Y_j`. Only the groups are identified, object by object; the transition maps of the
diagram are not matched with the transition maps of the etale cohomology groups. -/
def qcqsDiagramObjIsoEtaleCohomology
    (E : CohomologyCocone.{u, u, u + 1, u + 1} (bcSysGen T X Z cY hcY B hD hY)
      (bcToLimitSmallGen T X Z cY hcY B hD hY) (bcToLimitSmallGen_transition T X Z cY hcY B hD hY)
      (bcPrecoverageGen T X Z cY hcY B hD hY) F 𝒢 ι i W p)
    (A : Over i)
    (hdLevel : (((sheafSections ((bcSysGen T X Z cY hcY B hD hY).J A.left) Ab.{u + 1}).obj
        (op (((bcSysGen T X Z cY hcY B hD hY).u A.hom).obj W))).rightDerived p) ≅
      levelCohomologyFunctor (baseChange T X Z) cY B hD hY hcY A.left p) :
    E.diagram.obj (op A) ≅
      (Stacks.EtaleCohomology.etaleCohomologyFunctor B
          ⟨levelScheme (baseChange T X Z) cY B hD hY hcY A.left,
            hD (levelIndex (baseChange T X Z) cY B hD hY hcY A.left)⟩ p).obj
        ((levelToSmallEtale (baseChange T X Z) cY B hD hY hcY A.left).obj (F.obj A.left)) :=
  E.objIso A ≪≫
    (hdLevel ≪≫ levelCohomologyFunctorIsoEtaleCohomology.{u, u} (baseChange T X Z) cY B hD hY hcY
      A.left p).app (F.obj A.left)

/-- **Every group of the cohomology diagram of Stacks 03Q6 at a qcqs `X` is an etale cohomology
group of a level, with the identification read on injective resolutions.** The same statement as
`qcqsDiagramObjIsoEtaleCohomology` and under the same hypotheses, built from
`levelCohomologyFunctorIsoEtaleCohomology'`.

The two differ in which comparison identifies the cohomology of the level with that of its small
model. The unprimed form uses
`Stacks.Cohomology.DenseSubsiteGlobal.sheafCohomologyIsoOfIsEquivalence`, whose engine is the
universality of δ-functors (Stacks 010T and 010U) and which therefore cannot be compared with any
resolution-level construction. This one uses
`Stacks.Cohomology.DenseSubsiteGlobal.sheafCohomologyIsoOfIsEquivalence'`, whose engine is Stacks
015Z on the globally chosen injective resolution and is identified with the Leray edge morphism by
`Stacks.Cohomology.ExtComparison.extFunctorObjIsoComp_inv_app_eq_edge_app`. Since the transition
maps of the diagram *are* Leray edge morphisms
(`Stacks.WeakSites.ColimitSiteCohomology.CohomologyCocone.diagram_map_eq_edge_app`), this is the
form in which the object-by-object identification can be matched with them; with the unprimed form
it cannot. -/
def qcqsDiagramObjIsoEtaleCohomology'
    (E : CohomologyCocone.{u, u, u + 1, u + 1} (bcSysGen T X Z cY hcY B hD hY)
      (bcToLimitSmallGen T X Z cY hcY B hD hY) (bcToLimitSmallGen_transition T X Z cY hcY B hD hY)
      (bcPrecoverageGen T X Z cY hcY B hD hY) F 𝒢 ι i W p)
    (A : Over i)
    (hdLevel : (((sheafSections ((bcSysGen T X Z cY hcY B hD hY).J A.left) Ab.{u + 1}).obj
        (op (((bcSysGen T X Z cY hcY B hD hY).u A.hom).obj W))).rightDerived p) ≅
      levelCohomologyFunctor (baseChange T X Z) cY B hD hY hcY A.left p) :
    E.diagram.obj (op A) ≅
      (Stacks.EtaleCohomology.etaleCohomologyFunctor B
          ⟨levelScheme (baseChange T X Z) cY B hD hY hcY A.left,
            hD (levelIndex (baseChange T X Z) cY B hD hY hcY A.left)⟩ p).obj
        ((levelToSmallEtale (baseChange T X Z) cY B hD hY hcY A.left).obj (F.obj A.left)) :=
  E.objIso A ≪≫
    (hdLevel ≪≫ levelCohomologyFunctorIsoEtaleCohomology'.{u, u} (baseChange T X Z) cY B hD hY hcY
      A.left p).app (F.obj A.left)

/-- **Every group of the cohomology diagram of Stacks 03Q6 at a qcqs `X` is an etale cohomology
group of a level, with no cohomological hypothesis.** The hypothesis `hdLevel` of
`qcqsDiagramObjIsoEtaleCohomology'` is replaced by terminality of the transition image of the
chart `W` at the level `A.left`, which is what `qcqsHdLevel_of_isTerminal` turns into `hdLevel`,
in every degree and with no affineness.

The identification is the resolution-pinned one of `qcqsDiagramObjIsoEtaleCohomology'`, so it is
the form that can be matched with the Leray edge morphisms that are the transition maps of the
diagram. Only the groups are identified, object by object; matching the maps is still open.

This is a partial form of [Stacks, Tag 03Q6]; the registered statement is
`Stacks.EtaleCohomology.ColimitBaseChange.isIso_colimitDesc_algebraCohomologyCocone`. -/
def qcqsDiagramObjIsoEtaleCohomology_of_isTerminal
    (E : CohomologyCocone.{u, u, u + 1, u + 1} (bcSysGen T X Z cY hcY B hD hY)
      (bcToLimitSmallGen T X Z cY hcY B hD hY) (bcToLimitSmallGen_transition T X Z cY hcY B hD hY)
      (bcPrecoverageGen T X Z cY hcY B hD hY) F 𝒢 ι i W p)
    (A : Over i)
    (hW : IsTerminal (((bcSysGen T X Z cY hcY B hD hY).u A.hom).obj W)) :
    E.diagram.obj (op A) ≅
      (Stacks.EtaleCohomology.etaleCohomologyFunctor B
          ⟨levelScheme (baseChange T X Z) cY B hD hY hcY A.left,
            hD (levelIndex (baseChange T X Z) cY B hD hY hcY A.left)⟩ p).obj
        ((levelToSmallEtale (baseChange T X Z) cY B hD hY hcY A.left).obj (F.obj A.left)) :=
  qcqsDiagramObjIsoEtaleCohomology' T X Z cY hcY B hD hY F 𝒢 ι i W p E A
    (qcqsHdLevel_of_isTerminal T X Z cY hcY B hD hY i W p A hW)

end Descent

end Stacks.EtaleCohomology.QcqsBaseChange

end
