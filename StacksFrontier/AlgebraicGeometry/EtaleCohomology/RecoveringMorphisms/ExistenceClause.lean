module

public import Mathlib.AlgebraicGeometry.Gluing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.RingedToposTwoIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SubterminalSheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SubterminalSheavesSupplement

/-!
# The existence clause of Stacks 04I7, and the one gap behind it

Stacks 04I7 says that for schemes `X` and `Y` a morphism of *locally* ringed topoi
`(g, g^♯) : (Sh(X_étale), 𝒪_X) ⟶ (Sh(Y_étale), 𝒪_Y)` is 2-isomorphic to
`(f_small, f_small^♯)` for a unique morphism of schemes `f : X ⟶ Y`.  The uniqueness clause is
proved unconditionally, as `AlgebraicGeometry.eq_of_twoIso_smallEtaleRingedToposHom` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.RingedToposTwoIso` — it is
Stacks 04LW and needs neither affineness nor local-ringedness.  The existence clause is proved,
by a different route from the one described in these notes, in the modules under
`StacksDraft.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.Existence`; the full
statement is registered there, on
`AlgebraicGeometry.existsUnique_schemeHom_twoIso_smallEtaleRingedToposHom`.  The partial
statements below are steps of the proof in the source and are not registered.

This module names that clause, `AlgebraicGeometry.Clause04I7`, and the corresponding clause of
Stacks 04I6, `AlgebraicGeometry.Clause04I6`, so that a consumer may take one as an explicit
hypothesis instead of restating it; it records the direction of the chain between them; and it
assembles the clause with the uniqueness into the tag's **full** `∃!` statement, so that
discharging the clause becomes the tag with no restatement in between.

## Main definitions

* `AlgebraicGeometry.Clause04I7` — the existence clause of Stacks 04I7, at the tag's own
  generality: arbitrary schemes of the big étale site.
* `AlgebraicGeometry.Clause04I6` — the existence clause of Stacks 04I6, the case of two affine
  schemes.

## Main results

* `AlgebraicGeometry.setStructureSheaf_eq_forgetRing_O` — the structure sheaf of *sets* of the
  small étale site, `AlgebraicGeometry.setStructureSheaf`, is the underlying sheaf of sets of
  the structure sheaf of the small étale ringed topos.  See the implementation note below: this
  identity is a definitional equality.
* `AlgebraicGeometry.existsUnique_open_of_isSubterminal_topos` — Stacks 04HV read off at the
  topos of `AlgebraicGeometry.smallEtaleRingedSite`, whose sections are of `Type u`.  This is
  what the target half of Stacks 04I7's gluing needs: see the implementation note below.
* `AlgebraicGeometry.existsUnique_open_inverseImage_openRepresentableSheaf` — the **target half
  of the Zariski gluing** of Stacks 04I7: for an open subscheme `V` of the target there is
  exactly one open subscheme of the source representing `g⁻¹h_V`.
* `AlgebraicGeometry.eq_top_of_iso_inverseImage_openRepresentableSheaf_top` — that step sends
  the whole of the target to the whole of the source.
* `AlgebraicGeometry.galoisConnection_inverseImageOpen_pushforwardOpen` — that step is a left
  adjoint between the lattices of open subschemes, its right adjoint being the same
  construction run on the direct image.
* `AlgebraicGeometry.iSup_eq_top_of_forall_iso_inverseImage_openRepresentableSheaf` — the
  **covering step** of that gluing: the opens produced from an open covering of the target cover
  the source.
* `AlgebraicGeometry.existsUnique_schemeHom_of_iSup_opens_eq_top` — morphisms of schemes glue
  over an open covering of the source, for an indexed family of opens covering it and
  compatibility stated on the overlaps.
* `AlgebraicGeometry.existsUnique_schemeHom_of_forall_iso_inverseImage_openRepresentableSheaf` —
  the **gluing step** of that gluing, on the morphisms of schemes: the chartwise morphisms over
  the opens produced by the target half glue to exactly one morphism of schemes, the covering
  hypothesis being discharged from the covering step.
* `AlgebraicGeometry.clause04I6_of_clause04I7` — Stacks 04I7's clause implies Stacks 04I6's.
* `AlgebraicGeometry.existsUnique_schemeHom_twoIso_of_clause04I7` — the full statement of
  Stacks 04I7, with its existence clause as a named hypothesis and its uniqueness clause
  discharged from Stacks 04LW.

## Implementation notes

### The structure-sheaf-of-sets bridge is a definitional identity

`AlgebraicGeometry.setStructureSheaf B S hS`, introduced in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.Faithful` as the sheaf at
which a 2-morphism of the small étale ringed topoi is evaluated, and at which
`AlgebraicGeometry.SolutionPresentation.coord` takes its values, is the *same term* as each of

* `(RingedSite.toRingedTopos (smallEtaleRingedSite B S hS)).forgetRing.obj _`, the spelling in
  which `AlgebraicGeometry.RingedToposHom.fSharpSet` — the structure map of an abstract
  morphism of ringed topoi on underlying sheaves of sets — names its source and target, and
* `Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS))`,
  the spelling obtained by forgetting commutativity first and the ring operations second.

All three are `(SmallEtale.toScheme B S hS).op ⋙ Scheme.Γ ⋙ forget CommRingCat` with a
proof-irrelevant sheaf condition, so `AlgebraicGeometry.setStructureSheaf_eq_forgetRing_O` is
`rfl` and the other two spellings are interchangeable with it by `rfl` as well.  No transport,
no comparison isomorphism and no bridging construction is needed to compose a
`AlgebraicGeometry.SolutionPresentation.coord`, or any other morphism into
`AlgebraicGeometry.setStructureSheaf`, with `AlgebraicGeometry.RingedToposHom.fSharpSet`.

`Stacks.SheafOfModules.Tensor.ringSheaf` is an `abbrev` for
`AlgebraicGeometry.SheafOfModules.underlyingRingSheafOfSite`, so the spelling that appears in a
goal is not the one written in the source; that is the only difficulty.

### What the existence clause rests on

Steps (3) and (4) of the proof of Stacks 04I6 — the comparison `g⁻¹h_V ⟶ h_{X ×_Y V}` and the
proof that it is an isomorphism — are the single open input *of*
`AlgebraicGeometry.Clause04I6`.  They are not the single open input of
`AlgebraicGeometry.Clause04I7`: the Zariski gluing that passes from the one to the other is a
second, and the paragraph after next says what of it is proved here.  What steps (3)
and (4) themselves need is what
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.AffineCase` describes in its
"What is missing for Stacks 04I6" section, and what the implementation notes of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.RingedToposTwoIso` repeat.
Of step (3) the coefficient compatibility is proved
(`AlgebraicGeometry.RingedToposHom.terminalObjHomEquiv_globalSectionsMap`), both rows of the
comparison square are available as solution presentations
(`AlgebraicGeometry.SolutionPresentation.existsUnique_hom` and
`AlgebraicGeometry.baseChangeSolutionPresentation`), and the stalk computation of step (4) is
proved (`AlgebraicGeometry.SolutionPresentation.bijective_stalkSolution` and
`AlgebraicGeometry.bijective_homOverMap_targetStalkRingMap`).

The transport of the *equations* is available too, in
general form, in `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposPullbackHomSolutions.lean`:
the solution condition on generalized elements of a sheaf of rings *is* the chartwise condition
(`CategoryTheory.Sheaf.isSolution_of_forall_sectionsEval_eval₂` with
`CategoryTheory.Sheaf.sectionsEvalRingHom_eval₂`), so it is an equation between
morphisms of sheaves — no hand-built polynomial evaluation is needed, `MvPolynomial.eval₂` into
`CategoryTheory.Sheaf.homCommRing` being that evaluation already — and it travels along an exact
inverse image followed by a structure map by
`Stacks.Sheaves.ToposPullback.isSolution_sections_postcomp_inverseImageRingHom`.  What is left of
step (3) is the étale instance of those statements; what is left of step (4) is the functoriality
of the resulting isomorphisms in `V` and the descent from affine étale charts to all of
`Y_étale`, for which nothing in this library builds an isomorphism of two colimit-preserving
functors out of a sheaf topos from an isomorphism given only on representables.  Nothing in that
list is this module's bridge.

Stacks 04I7's own argument on top of Stacks 04I6 is a Zariski gluing, over the source and then
over the target, and its inputs are available: Stacks 04I5
(`AlgebraicGeometry.smallEtaleRingedSiteHom_isLocallyRinged`), Stacks 04IJ
(`AlgebraicGeometry.Space.schemeSmallEtaleRingedToposHom_twoMorphism_eq_id`), Stacks 04HV
(`AlgebraicGeometry.existsUnique_open_of_isSubterminal`), the gluing of morphisms of sheaves
(`Stacks.SheafMapGluing.maps_of_sheaves_glue`, Stacks 04TQ, with
`Stacks.SheafMapGluing.iso_of_sheaves_glue` for the isomorphism form) and the constructor
`AlgebraicGeometry.RingedToposHom.TwoIso.ofInverseImageIso` and `.ofPushforwardIso`.

`.ofInverseImageIso` is in
`CategoryTheory/Sites/Modules/Localization/RingedToposRelocalizedMorphism.lean` and
`.ofPushforwardIso` in `Crystalline/BigSite/RingedStructureMorphism.lean`, both in namespace
`AlgebraicGeometry.RingedToposHom`.  The latter takes an isomorphism `f_* ≅ g_*` together with
the condition that its mate carries the inverse-image form of `f`'s structure map to `g`'s.

Note that `TwoIso` is *defined* by an isomorphism of the two direct images plus
the compatibility `commutes`, so the anonymous constructor is already close to the pushforward
form — what `.ofPushforwardIso` adds is the mate condition, and `.ofInverseImageIso` exists
because the inverse-image form has to be converted.

The *target half* of that gluing — the step which, from an open subscheme `V` of the target,
produces the open subscheme of the source representing `g⁻¹h_V` — is proved here, as
`AlgebraicGeometry.existsUnique_open_inverseImage_openRepresentableSheaf`; the *covering
step* — that the opens so produced from an open covering of the target cover the source — is
proved here too, as
`AlgebraicGeometry.iSup_eq_top_of_forall_iso_inverseImage_openRepresentableSheaf`; and so is the
*gluing step on the morphisms of schemes*,
`AlgebraicGeometry.existsUnique_schemeHom_of_forall_iso_inverseImage_openRepresentableSheaf`,
which takes the chartwise morphisms of schemes and no covering hypothesis — it calls the
covering step for that — and returns the unique morphism of schemes they glue to.  What the rest
of the assembly needs is the following.

1. The restriction of `g` to a morphism of ringed topoi between the small étale ringed topoi of
   `W` and of `V`.  **Available.**  Stacks 04IF's half is `AlgebraicGeometry.localizedOverOpen`;
   Stacks 04IE's half, as a morphism of ringed topoi and at the spelling of the represented sheaf
   that 04IF's half localizes at, is
   `AlgebraicGeometry.SmallEtale.openLocalizedRingedToposHom`; and the source of 04IF's half is
   identified with the localization at the open `AlgebraicGeometry.inverseImageOpen` of the
   source by `AlgebraicGeometry.inverseImageOpenLocalizedToposEquivalence`.
2. The existence clause of Stacks 04I6 applied to affine charts of those two.
3. The gluing of the *2-isomorphisms*.  The morphisms of schemes themselves glue; what remains
   is the 2-isomorphism, and it remains because its local pieces are the
   2-isomorphisms of the restricted morphisms, i.e. because it rests on (1) and (2).

That is why `AlgebraicGeometry.Clause04I7`, and not `AlgebraicGeometry.Clause04I6`, is the
hypothesis of the theorem below: Stacks 04I6's clause alone does not give Stacks 04I7's.

### The restriction of `g` to a pair of opens

Item (1) above is Stacks 04IF for the small étale ringed topoi, and it needs two
things, both available.

The first is Stacks 04IF itself at the universes of the small étale ringed topos, and it is
proved: `AlgebraicGeometry.localizedOverOpen` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/OpenLocalization.lean` is the
localization of a morphism of small étale ringed topoi at the sheaf represented by an open of
the target, with no hypothesis beyond the morphism and the open.  It rests on a universe
generalization.  `AlgebraicGeometry.RingedToposHom.localized` in
`StacksFrontier/CategoryTheory/Sites/Modules/Localization/RingedToposMorphismLocalization.lean` is
exactly the restriction wanted — the localization of an abstract morphism of ringed topoi at a
sheaf of the target, with its structure map — and it is needed beyond `RingedTopos.{u, u, u}`,
since `RingedSite.toRingedTopos (smallEtaleRingedSite B S hS)` is a `RingedTopos.{u, u + 1, u}`:
the objects of the small étale site are of `Type (u + 1)` and its morphisms and the sections of
its structure sheaf are of `Type u`.  The restriction to one universe is *not* forced by Stacks
0791: `CategoryTheory.Presheaf.IsSheaf.exists_sheafEquivalence_costructuredArrow_yoneda` in
`StacksFrontier/CategoryTheory/Sites/Topos/LocalizationOfTopoi.lean` is stated for `C : Type u` with
`Category.{v} C` and `F : Cᵒᵖ ⥤ Type v`, so the only constraint it imposes is that the sections
universe be the morphism universe, which holds here.  Nor is it forced by Stacks 04H1:
`MorphismOfTopoi.over` in
`StacksFrontier/CategoryTheory/Sites/SliceTopos/OverPushforward.lean` has the two topoi at wholly
independent universes.  What does force it is the *direct image* of the localization:
`AlgebraicGeometry.RingedTopos.localizationToposMorphism` takes
`(elementProjection X F).sheafPushforwardCocontinuous`, and with the site of elements of `Type
(u + 1)` and sheaves of `Type u` the instance
`∀ G, (elementProjection X F).op.HasPointwiseRightKanExtension G` is not available — the right
Kan extension is along a functor whose structured-arrow categories are `(u + 1)`-sized while the
limits are taken in `Type u`.

That obstruction is *not* mathematical, and the generalization is carried out:
essential `v`-smallness of the site makes the site of elements essentially `v`-small, because an
object of it is a pair `(U, s)` with `s` a section of `F` and the Yoneda lemma turns those
sections into a `v`-small family over a `v`-small model of the site, after which
`CategoryTheory.Limits.hasLimitsOfShape_of_essentiallySmall` supplies the limits and
`CategoryTheory.hasSheafComposeEssentiallySmallSite` the four `HasSheafCompose` instances that
`u = v` otherwise got for free from
`CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize`.  With `[EssentiallySmall.{v} X.C]`
assumed from `AlgebraicGeometry.RingedTopos.localizationToposMorphism` onwards, the whole tower
elaborates at `X Y : RingedTopos.{v, u, v}` with the localizations at
`RingedTopos.{v, max u v, v}`, and `g.localized G` type-checks for a `g` between two small étale
ringed topoi and any sheaf `G` on the target, the smallness hypothesis being discharged by the
instance `AlgebraicGeometry.SmallEtale.essentiallySmall`.

The *elaboration cost of that generalization downstream* falls on one module.  Making the object
universe a second parameter makes the localization's own object universe the level expression
`max u v`, so a consumer that applies these declarations at a single
universe has to solve `max ?u ?v =?= u` instead of matching a parameter, and `isDefEq` falls back
to unfolding `AlgebraicGeometry.RingedTopos.localizedRingedTopos`.  One module of
`StacksFrontier/CategoryTheory/Sites/Modules/Localization/` is large enough for that to exceed the
heartbeat limit:
`StacksFrontier/CategoryTheory/Sites/Modules/Localization/RepresentableRelocalization.lean`, whose
statements iterate the localization — they localize a localization — and already cost some 55,000
reducible unfoldings apiece.  Its repair is to pin the universes explicitly at the consumer,
`RingedTopos.localizedRingedTopos.{u, u} X.ringedTopos F` in place of
`X.ringedTopos.localizedRingedTopos F`, which leaves the unifier nothing to solve.  That is what the
file does, and its own universe note records it.  No heartbeat limit is raised anywhere in the
directory, and no option is changed there either.

The other modules of that directory —
`StacksFrontier/CategoryTheory/Sites/Modules/Localization/RingedToposRelocalizedMorphism.lean`,
`StructureSheafComparison.lean` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ArtinSchreierSequence/`, and
`StacksFrontier/CategoryTheory/Sites/Modules/Localization/RelocalizedMorphismComparison.lean` —
need no pinned universes, no bridging lemmas and no opacity attributes beyond the one
`attribute [local irreducible]` that
`StacksFrontier/CategoryTheory/Sites/Modules/Localization/RelocalizedMorphismComparison.lean`
carries on `RingedToposHom.inverseImageCompLocalizationIso`.  A blanket version of the opacity idea
does not work: `localizedRingedTopos` itself must stay transparent, because its consumers read
`(localizedRingedTopos X F).C` and `.J` throughout, and making it irreducible turns the one timeout
into type mismatches across three modules.

The second is the identification of the small étale topos of an open subscheme with that
localization, which is Stacks 04IE for the étale site, and it is proved on the **topoi**, as
`AlgebraicGeometry.SmallEtale.localizedToposEquivalence` and `.openLocalizedToposEquivalence` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/OpenLocalization.lean`.  Its
two site-level halves are
`AlgebraicGeometry.opensToBoundedEtale` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Comparison/ZariskiRestriction.lean` is the functor
`S.Opens ⥤ SmallEtale B S hS` sending `V` to `V` regarded as étale over `S`, and
`AlgebraicGeometry.SmallEtale.localizationEquivalence` in
`StacksFrontier/AlgebraicGeometry/Etale/SmallEtalePostcompose.lean`, with its topology comparison
`AlgebraicGeometry.SmallEtale.localizationEquivalence_topology`, is the equivalence between the
small étale site of an object of the small étale site and the slice of that site over it.  (A
parallel copy of that equivalence, `AlgebraicGeometry.smallEtaleEquivalenceOver` in
`StacksFrontier/AlgebraicGeometry/Topologies/Etale/SliceEquivalence/Equiv.lean`, is the same
construction; the one with the topology comparison beside it is the one used.)  What carries the
second half to sheaves is that the equivalence is a dense subsite inclusion for the two
topologies, so restriction along it is an equivalence of sheaf categories; the size condition of
that step is free here, because a structured-arrow category over an equivalence has an initial
object.

The composite does not need
`AlgebraicGeometry.RingedSite.representableLocalizationEquivalence` of
`StacksFrontier/CategoryTheory/Sites/Modules/Localization/RepresentableLocalization.lean`, which
carries the slice site `(X_ét)/U` to the site of elements of `h_U^#` on which
`AlgebraicGeometry.RingedTopos.localizedRingedTopos` is built and is stated for
`X : RingedSite.{u, u, u}`, whereas `AlgebraicGeometry.smallEtaleRingedSite` is a
`RingedSite.{u + 1, u, u}`.  That declaration is the *bundling* of two steps that are
separately universe-free — `CategoryTheory.OverShriek.sheafEquivalence` (Stacks 00Y1) in
`StacksFrontier/CategoryTheory/Sites/Localization/SheavesOverRepresentable.lean`, stated for
`C : Type u` with `Category.{v} C` and sheaves of `Type v`, so with its object universe free, and
`AlgebraicGeometry.RingedTopos.localizationEquivalence`, already at `RingedTopos.{v, u, v}` —
and composing those two directly gives the step at the universes of the small étale ringed topos.

The generalization of the bundled form is a different matter, and it is **blocked** in the
naive shape.  `representableLocalizationEquivalence` is stated over
`AlgebraicGeometry.RingedSite.ringedTopos`, which is stated at
`X : RingedSite.{u, v, max u v w}`: its sections universe is not a parameter but the expression
`max u v w`, so a small étale ringed site would need `max (u + 1) v w = u`, which has no
solution — the sections would have to be at `u + 1` or above while they are at `u`.  What forces
that expression is not the equivalence but the *ringed-site* localization underneath it:
`AlgebraicGeometry.RingedSite.overMorphismOfTopoi` in
`StacksFrontier/CategoryTheory/Sites/Localization/RingedSiteLocalization.lean` is stated with both
of its topoi at `Type (max u v w)`, because its direct image is a right Kan extension along
`(Over.forget U).op`, a limit indexed by structured arrows over `Over U` and so of size
`max u v`.  That is exactly the obstruction `[EssentiallySmall.{v} X.C]` removed for the
ringed-*topos* localization, and removing it here is the same generalization applied to the
ringed-site tower, starting at `overMorphismOfTopoi` and reaching `ringedTopos` and then
`StacksFrontier/CategoryTheory/Sites/Modules/Localization/RepresentableLocalization.lean`.  Nothing
above needs it.

The second of those two comparisons is proved.  Stacks 04IE as formed localizes at the
sheafification of `yoneda.obj U` for `U` an object of the small étale site, whereas Stacks 04IF's
half and `AlgebraicGeometry.inverseImageOpen` localize at the sheafification of
`AlgebraicGeometry.openRepresentable`, the restriction to the small étale site of the presheaf
the open represents in the big étale slice.  The two are identified by
`AlgebraicGeometry.SmallEtale.openRepresentableSheafIsoYoneda`, and
`AlgebraicGeometry.SmallEtale.openRepresentableLocalizedToposEquivalence` is 04IE at the second
spelling.  The construction is
`representablePresheafIso` and `openRepresentableIso` of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/OpenEqualityLocus.lean`, with the sections
universe free, stated over `AlgebraicGeometry.SmallEtale.toOver`.

The remaining part of input (1) is the first comparison, that of the two **structure sheaves**.
There are two routes.  Transport at the ring level along the
identification as formed in `OpenLocalization.lean` goes through Stacks 00Y1, whose functor is a
lower shriek, and so needs
`StacksFrontier/CategoryTheory/Sites/Modules/Localization/RepresentableLocalization.lean`'s
uniqueness-of-lift machinery at these universes, i.e. the ringed-site tower generalized from
`AlgebraicGeometry.RingedSite.overMorphismOfTopoi` (71 use sites in 12 modules) through
`AlgebraicGeometry.RingedSite.ringedTopos` (`.ringedTopos` read in 76 modules).  **That route is not
taken**: the generalization is feasible — the `[EssentiallySmall.{v} X.C]` it would carry *is*
discharged by instance search at a single universe, so it is backward compatible at
`RingedSite.{u, u, u}` — but it is a structural refactor of a whole subtree whose only gain is one
comparison that the other route buys inside one new construction.

The other route identifies the two topoi **by restriction along a functor of sites** instead,
which the small étale site allows and a general site does not: its topology is subcanonical
(`AlgebraicGeometry.SmallEtale.topology_subcanonical`), so a section of `h_U` over `T` is a
morphism `T ⟶ U` and the site of elements of `h_U` *is* the slice `(S_étale)/U`.  Its first half
is in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/SmallEtaleElementSite.lean`:
the functor of sites (`AlgebraicGeometry.SmallEtale.overToElementSite` and
`.toElementSite`), the comparison of the two topologies
(`.functorPushforward_mem_elementTopology_iff`, whence `.toElementSite_isDenseSubsite`), the
identification of the topoi as a restriction (`.elementSiteSheafEquivalence`), and — the payoff —
the comparison of the two structure sheaves as an **equality**
(`.sheafPushforward_localizedRingedTopos_O`), the cheap presheaf identity after all, because the
composite functor of sites down to `S_étale` is `AlgebraicGeometry.SmallEtale.postcompose`
(`.toElementSite_comp_elementProjection`).

The equality is put into inverse-image form through
`Stacks.Sheaves.ToposPullback.restrictionCommRingIso`, whose `UnivLE` side conditions pose
`u =?= max (u + 1) ?u` unless the universes are supplied positionally; with that the ringed
identification is proved:
`AlgebraicGeometry.SmallEtale.localizedRingedToposHom` is **Stacks 04IE for the small étale site
as a morphism of ringed topoi**, structure sheaves included, its structure map the adjunct of
`AlgebraicGeometry.SmallEtale.localizedStructureSheafIso` and so an isomorphism.  What the pins
are, and the three further things that had to be right — the second site's object universe
written `max (u + 1) u`, the localization pinned throughout, and the continuity instance passed
explicitly at the `(localizedRingedTopos _ _).J` spelling rather than left to instance search —
are recorded in that module's notes.

That identification is carried from the representable spelling `⟨yoneda.obj U, _⟩` of the sheaf
to the *sheafification* spelling — the one Stacks 04IF's half localizes at — by
`AlgebraicGeometry.RingedTopos.localizedRingedToposHomOfIso` in
`StacksFrontier/CategoryTheory/Sites/Modules/Localization/SliceEquivalence.lean`, which moves a
localization along an isomorphism of sheaves as a morphism of **ringed** topoi.  It is built like
the identification itself: `CategoryTheory.CostructuredArrow.mapIso` is a functor of sites over
the site of `X`, so the two localized structure sheaves are restrictions along equal composites
and their comparison is an equality.  The isomorphism transported along is
`AlgebraicGeometry.SmallEtale.openRepresentableSheafIso`, the sheafification counit at a sheaf
followed by `AlgebraicGeometry.SmallEtale.openRepresentableSheafIsoYoneda`, and the composite is
`AlgebraicGeometry.SmallEtale.openLocalizedRingedToposHom`.  With it input (1) is complete.

Two pieces of elaboration bookkeeping are needed and are recorded where they are used; both
have the same cause.  `Stacks.Sheaves.ToposPullback.restrictionCommRingIso` asks for its
continuity instance while its functor argument is still a metavariable, so the instance has to be
passed explicitly; and `AlgebraicGeometry.RingedToposHom.comp` elaborates its own nine universe
parameters before its arguments, so the three belonging to the source have to be pinned
positionally.  In both cases annotating the argument, `let`-binding it with its type written out,
and `by exact` all come too late.  Neither is about the mathematics, and neither
needed a bridge or a reducibility attribute.

### The covering step needs no epimorphism of sheaves

The covering step does not need that an open covering of a scheme makes `⨆_j h_{V_j} ⟶ *` an
epimorphism of sheaves on its small étale site, nor that local surjectivity of
`⨆_j h_{W_j} ⟶ *` forces `⨆_j W_j = ⊤`, and neither is proved here.  Coproducts of sheaves,
epimorphisms and local surjectivity do not enter the covering step at all.

What the step is, instead, is the statement that `V ↦ W` *preserves suprema*, and that is formal
once one observes that it is a **left adjoint**.  The operation `V ↦ W` of the target half has a
right adjoint `W ↦ V`, built by the same argument applied to `g_*` instead of `g⁻¹`
(`AlgebraicGeometry.existsUnique_open_pushforward_openRepresentableSheaf`): the two are
`AlgebraicGeometry.inverseImageOpen` and `AlgebraicGeometry.pushforwardOpen`, and they form a
Galois connection, `AlgebraicGeometry.galoisConnection_inverseImageOpen_pushforwardOpen`.  Its
whole content is the hom-set bijection of the adjunction `g⁻¹ ⊣ g_*` read through
`AlgebraicGeometry.nonempty_hom_openRepresentableSheaf_iff_le`, the identification of the
lattice `S.Opens` with the subobjects of the final sheaf: for opens `W`, `W'` of `S` there is a
morphism `h_W ⟶ h_{W'}` exactly when `W ≤ W'`.  A left adjoint between complete lattices
preserves arbitrary suprema (`GaloisConnection.l_iSup`), the lattices of opens of a scheme are
complete, and so `⨆_j W_j = ⨆_j inverseImageOpen (V_j) = inverseImageOpen (⨆_j V_j)`.  The one
geometric input is then the degenerate case `⨆_j V_j = ⊤` already proved as
`AlgebraicGeometry.eq_top_of_iso_inverseImage_openRepresentableSheaf_top`.

Two related facts are available — Mathlib's
`CategoryTheory.Sheaf.isLocallySurjective_iff_epi` is stated for `Sheaf J (Type w)` with `w`
free, so it is available at the sections universe `u` of the ringed topos, and a left adjoint
preserves epimorphisms — but on this route nothing uses them.

### Stacks 04HV is available at the sections universe of the ringed topos

A statement of Stacks 04HV only for sheaves of `Type (max (u + 1) v)` would not apply to the
target half of that gluing, the ringed topos of `AlgebraicGeometry.smallEtaleRingedSite` being
`Sheaf _ (Type u)` and `max (u + 1) v = u` having no solution.  But
`AlgebraicGeometry.existsUnique_open_of_isSubterminal` is stated for sheaves of
`Type (max u v)` with `v` free, which at `v := u` *is* `Sheaf _ (Type u)`, i.e. exactly
`(RingedSite.toRingedTopos (smallEtaleRingedSite B S hS)).Topos`; a subterminal object of the
ringed topos is handed to Stacks 04HV with no transport, no comparison equivalence and no
restatement.  What made the sections universe `u` available is sheafification there,
`AlgebraicGeometry.SmallEtale.hasSheafify_type`, which the site's essential smallness supplies
one universe below Mathlib's unconditional instance.

The chain is then four lines: `AlgebraicGeometry.isSubterminal_openRepresentableSheaf` says `h_V` is
subterminal, `CategoryTheory.IsSubterminal.map` carries that through the left-exact inverse image,
and
`AlgebraicGeometry.existsUnique_open_of_isSubterminal_topos` turns the result into the open.
Nothing about germs, nor about the structure sheaf, enters the target half at all.

## References

* [Stacks Project, Tag 04I7](https://stacks.math.columbia.edu/tag/04I7)
* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 04LW](https://stacks.math.columbia.edu/tag/04LW)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

/-! ### The structure sheaf of sets of the small étale ringed topos -/

/-- **The structure sheaf of sets of the small étale site is the one of its ringed topos.**
`AlgebraicGeometry.setStructureSheaf`, the sheaf of sets at which a 2-morphism of small étale
ringed topoi is evaluated, is the underlying sheaf of sets of the structure sheaf of
`AlgebraicGeometry.smallEtaleRingedSite`, which is the source and target of
`AlgebraicGeometry.RingedToposHom.fSharpSet`.

Both sides are `(SmallEtale.toScheme B S hS).op ⋙ Scheme.Γ ⋙ forget CommRingCat` with a
proof-irrelevant sheaf condition, so this is `rfl`; it is stated because the right-hand side
reaches a goal spelled through `AlgebraicGeometry.SheafOfModules.underlyingRingSheafOfSite`,
for which `Stacks.SheafOfModules.Tensor.ringSheaf` is an `abbrev`, and so does not look like
the left-hand side. -/
theorem setStructureSheaf_eq_forgetRing_O (S : Scheme.{u}) (hS : B.Contains S) :
    setStructureSheaf B S hS =
      (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS)).forgetRing.obj
        (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS)).O :=
  rfl

/-! ### Stacks 04HV at the topos of the small étale ringed site -/

/-- **Stacks 04HV for a subterminal object of the topos of the small étale ringed site.** A
subsheaf of the final object of `(Sh(S_étale), 𝒪_S)` is represented by exactly one open
subscheme of `S`.

This is `AlgebraicGeometry.existsUnique_open_of_isSubterminal` with its free sections universe
instantiated at the universe `u` of the sections of
`AlgebraicGeometry.smallEtaleRingedSite`, a `RingedSite.{u + 1, u, u}`.  Nothing is transported:
`CategoryTheory.IsSubterminal` is a condition in the sheaf category and the representability
conclusion is about the same sheaf, and the two sides are the same category, because
`AlgebraicGeometry.RingedTopos.Topos` of that ringed site *is*
`CategoryTheory.Sheaf (SmallEtale.topology B S hS) (Type u)`. -/
@[stacks 04HV "the case of a subterminal object of the topos of
  `AlgebraicGeometry.smallEtaleRingedSite`, whose sections are of `Type u`; this is
  `AlgebraicGeometry.existsUnique_open_of_isSubterminal`, which carries the tag in its own
  generality `Type (max u v)`, instantiated at `v := u` with no transport in between"]
theorem existsUnique_open_of_isSubterminal_topos (X : B.Scheme)
    (F : (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property)).Topos)
    (hF : IsSubterminal F) :
    ∃! W : X.obj.Opens,
      Nonempty (F ≅
        (presheafToSheaf (SmallEtale.topology B X.obj X.property) (Type u)).obj
          ((SmallEtale.inclusion B X.obj X.property ⋙
            Over.post (X := B.obj X.obj X.property) B.inclusion).op ⋙
            uliftYoneda.{u}.obj (Over.mk W.ι))) :=
  existsUnique_open_of_isSubterminal'.{u, u} B X.obj X.property F hF

/-! ### The target half of the Zariski gluing of Stacks 04I7 -/

/-- **The inverse image of the sheaf represented by an open of the target is a subsheaf of the
final sheaf of the source.** The inverse image of a morphism of topoi is left exact and
`AlgebraicGeometry.isSubterminal_openRepresentableSheaf` says the source of the inverse image
is subterminal. -/
theorem isSubterminal_inverseImage_openRepresentableSheaf (X Y : B.Scheme)
    (g : RingedToposHom (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
    (V : Y.obj.Opens) :
    IsSubterminal (g.toToposHom.inverseImage.obj
      ((presheafToSheaf (SmallEtale.topology B Y.obj Y.property) (Type u)).obj
        (openRepresentable'.{u, u} B Y.obj Y.property V))) :=
  let := g.toToposHom.preservesFiniteLimits
  (isSubterminal_openRepresentableSheaf.{u, u} B Y.obj Y.property V).map
    Limits.terminalIsTerminal _

/-- **The target half of the Zariski gluing of Stacks 04I7.** For an open subscheme `V` of the
target there is exactly one open subscheme `W` of the source with `g⁻¹h_V ≅ h_W`.

This is the step of the proof of Theorem 59.40.5 that produces the open subschemes of `X` over
which the morphism of locally ringed topoi is to be compared with a morphism of schemes: `h_V`
is a subsheaf of the final sheaf of `Sh(Y_étale)`, `g⁻¹` is exact, so `g⁻¹h_V` is a subsheaf of
the final sheaf of `Sh(X_étale)`, and Stacks 04HV turns that into a unique open of `X`.  Nothing
here needs `g` to be locally ringed, and nothing here needs the schemes to be affine. -/
theorem existsUnique_open_inverseImage_openRepresentableSheaf (X Y : B.Scheme)
    (g : RingedToposHom (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
    (V : Y.obj.Opens) :
    ∃! W : X.obj.Opens,
      Nonempty (g.toToposHom.inverseImage.obj
        ((presheafToSheaf (SmallEtale.topology B Y.obj Y.property) (Type u)).obj
          (openRepresentable'.{u, u} B Y.obj Y.property V)) ≅
        (presheafToSheaf (SmallEtale.topology B X.obj X.property) (Type u)).obj
          (openRepresentable'.{u, u} B X.obj X.property W)) :=
  existsUnique_open_of_isSubterminal_topos B X _
    (isSubterminal_inverseImage_openRepresentableSheaf B X Y g V)

/-- **The inverse image of the sheaf represented by the whole of the target is the final sheaf
of the source.** The sheaf represented by the whole of a scheme is the final sheaf of its small
étale topos (`AlgebraicGeometry.isTerminal_openRepresentableSheaf_top`) and the inverse image of
a morphism of topoi is left exact. -/
noncomputable def isTerminal_inverseImage_openRepresentableSheaf_top (X Y : B.Scheme)
    (g : RingedToposHom (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property))) :
    Limits.IsTerminal (g.toToposHom.inverseImage.obj
      ((presheafToSheaf (SmallEtale.topology B Y.obj Y.property) (Type u)).obj
        (openRepresentable'.{u, u} B Y.obj Y.property ⊤))) :=
  letI := g.toToposHom.preservesFiniteLimits
  (isTerminal_openRepresentableSheaf_top.{u, u} B Y.obj Y.property).isTerminalObj
    g.toToposHom.inverseImage

/-- **The target half of the gluing sends the whole of the target to the whole of the source.**
Both sides of the comparison are then final sheaves, so they are isomorphic, and the uniqueness
in `AlgebraicGeometry.existsUnique_open_inverseImage_openRepresentableSheaf` forces the open to
be `⊤`.  This is the degenerate case of the step of the proof of Theorem 59.40.5 that the opens
produced over an open covering of the target cover the source; the covering case itself is
`AlgebraicGeometry.iSup_eq_top_of_forall_iso_inverseImage_openRepresentableSheaf`, of which this
is also the one input that is not formal. -/
theorem eq_top_of_iso_inverseImage_openRepresentableSheaf_top (X Y : B.Scheme)
    (g : RingedToposHom (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
    (W : X.obj.Opens)
    (hW : Nonempty (g.toToposHom.inverseImage.obj
      ((presheafToSheaf (SmallEtale.topology B Y.obj Y.property) (Type u)).obj
        (openRepresentable'.{u, u} B Y.obj Y.property ⊤)) ≅
      (presheafToSheaf (SmallEtale.topology B X.obj X.property) (Type u)).obj
        (openRepresentable'.{u, u} B X.obj X.property W))) :
    W = ⊤ :=
  (existsUnique_open_inverseImage_openRepresentableSheaf B X Y g ⊤).unique hW
    ⟨(isTerminal_inverseImage_openRepresentableSheaf_top B X Y g).uniqueUpToIso
      (isTerminal_openRepresentableSheaf_top.{u, u} B X.obj X.property)⟩

/-! ### The covering step of the Zariski gluing of Stacks 04I7 -/

/-- **The direct image of the sheaf represented by an open of the source is a subsheaf of the
final sheaf of the target.** The direct image of a morphism of topoi is a right adjoint, so it
preserves all limits, and `AlgebraicGeometry.isSubterminal_openRepresentableSheaf` says the
source of the direct image is subterminal. -/
theorem isSubterminal_pushforward_openRepresentableSheaf (X Y : B.Scheme)
    (g : RingedToposHom (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
    (W : X.obj.Opens) :
    IsSubterminal (g.toToposHom.pushforward.obj
      ((presheafToSheaf (SmallEtale.topology B X.obj X.property) (Type u)).obj
        (openRepresentable'.{u, u} B X.obj X.property W))) :=
  let : Limits.PreservesLimitsOfSize g.toToposHom.pushforward :=
    g.toToposHom.adj.rightAdjoint_preservesLimits
  (isSubterminal_openRepresentableSheaf.{u, u} B X.obj X.property W).map
    Limits.terminalIsTerminal _

/-- **The direct-image counterpart of the target half of the Zariski gluing.** For an open
subscheme `W` of the source there is exactly one open subscheme `V` of the target with
`g_*h_W ≅ h_V`.

This is the same argument as
`AlgebraicGeometry.existsUnique_open_inverseImage_openRepresentableSheaf` run on the other side
of the adjunction: `h_W` is a subsheaf of the final sheaf of `Sh(X_étale)`, `g_*` preserves
limits, so `g_*h_W` is a subsheaf of the final sheaf of `Sh(Y_étale)`, and Stacks 04HV turns
that into a unique open of `Y`.  It is not a step of the proof of Theorem 59.40.5; it is the
right adjoint that makes the target half preserve unions of opens. -/
theorem existsUnique_open_pushforward_openRepresentableSheaf (X Y : B.Scheme)
    (g : RingedToposHom (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
    (W : X.obj.Opens) :
    ∃! V : Y.obj.Opens,
      Nonempty (g.toToposHom.pushforward.obj
        ((presheafToSheaf (SmallEtale.topology B X.obj X.property) (Type u)).obj
          (openRepresentable'.{u, u} B X.obj X.property W)) ≅
        (presheafToSheaf (SmallEtale.topology B Y.obj Y.property) (Type u)).obj
          (openRepresentable'.{u, u} B Y.obj Y.property V)) :=
  existsUnique_open_of_isSubterminal_topos B Y _
    (isSubterminal_pushforward_openRepresentableSheaf B X Y g W)

/-- The open subscheme of the source that the target half of the Zariski gluing produces from an
open subscheme of the target: the unique open representing `g⁻¹h_V`. -/
def inverseImageOpen (X Y : B.Scheme)
    (g : RingedToposHom (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
    (V : Y.obj.Opens) : X.obj.Opens :=
  (existsUnique_open_inverseImage_openRepresentableSheaf B X Y g V).choose

/-- The sheaf represented by `AlgebraicGeometry.inverseImageOpen` is the inverse image of the
sheaf represented by the given open of the target. -/
theorem nonempty_iso_inverseImageOpen (X Y : B.Scheme)
    (g : RingedToposHom (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
    (V : Y.obj.Opens) :
    Nonempty (g.toToposHom.inverseImage.obj
      ((presheafToSheaf (SmallEtale.topology B Y.obj Y.property) (Type u)).obj
        (openRepresentable'.{u, u} B Y.obj Y.property V)) ≅
      (presheafToSheaf (SmallEtale.topology B X.obj X.property) (Type u)).obj
        (openRepresentable'.{u, u} B X.obj X.property (inverseImageOpen B X Y g V))) :=
  (existsUnique_open_inverseImage_openRepresentableSheaf B X Y g V).choose_spec.1

/-- Any open of the source representing `g⁻¹h_V` is `AlgebraicGeometry.inverseImageOpen`. -/
theorem eq_inverseImageOpen (X Y : B.Scheme)
    (g : RingedToposHom (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
    (V : Y.obj.Opens) (W : X.obj.Opens)
    (hW : Nonempty (g.toToposHom.inverseImage.obj
      ((presheafToSheaf (SmallEtale.topology B Y.obj Y.property) (Type u)).obj
        (openRepresentable'.{u, u} B Y.obj Y.property V)) ≅
      (presheafToSheaf (SmallEtale.topology B X.obj X.property) (Type u)).obj
        (openRepresentable'.{u, u} B X.obj X.property W))) :
    W = inverseImageOpen B X Y g V :=
  (existsUnique_open_inverseImage_openRepresentableSheaf B X Y g V).choose_spec.2 W hW

/-- The open subscheme of the target representing `g_*h_W`, the right adjoint of
`AlgebraicGeometry.inverseImageOpen`. -/
def pushforwardOpen (X Y : B.Scheme)
    (g : RingedToposHom (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
    (W : X.obj.Opens) : Y.obj.Opens :=
  (existsUnique_open_pushforward_openRepresentableSheaf B X Y g W).choose

/-- The sheaf represented by `AlgebraicGeometry.pushforwardOpen` is the direct image of the
sheaf represented by the given open of the source. -/
theorem nonempty_iso_pushforwardOpen (X Y : B.Scheme)
    (g : RingedToposHom (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
    (W : X.obj.Opens) :
    Nonempty (g.toToposHom.pushforward.obj
      ((presheafToSheaf (SmallEtale.topology B X.obj X.property) (Type u)).obj
        (openRepresentable'.{u, u} B X.obj X.property W)) ≅
      (presheafToSheaf (SmallEtale.topology B Y.obj Y.property) (Type u)).obj
        (openRepresentable'.{u, u} B Y.obj Y.property (pushforwardOpen B X Y g W))) :=
  (existsUnique_open_pushforward_openRepresentableSheaf B X Y g W).choose_spec.1

/-- **The target half of the Zariski gluing of Stacks 04I7 is a left adjoint between the
lattices of opens.** `V ↦ inverseImageOpen V` and `W ↦ pushforwardOpen W` form a Galois
connection.

The content is the adjunction `g⁻¹ ⊣ g_*` read through
`AlgebraicGeometry.nonempty_hom_openRepresentableSheaf_iff_le`, which says that an inclusion of
opens is the same thing as a morphism between the sheaves they represent.  Nothing else enters:
the two sides of the Galois connection are the two sides of the hom-set bijection of the
adjunction, transported along the defining isomorphisms of the two operations. -/
theorem galoisConnection_inverseImageOpen_pushforwardOpen (X Y : B.Scheme)
    (g : RingedToposHom (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property))) :
    GaloisConnection (inverseImageOpen B X Y g) (pushforwardOpen B X Y g) := by
  intro V W
  obtain ⟨eV⟩ := nonempty_iso_inverseImageOpen B X Y g V
  obtain ⟨eW⟩ := nonempty_iso_pushforwardOpen B X Y g W
  rw [← nonempty_hom_openRepresentableSheaf_iff_le.{u, u} B X.obj X.property
      (inverseImageOpen B X Y g V) W,
    ← nonempty_hom_openRepresentableSheaf_iff_le.{u, u} B Y.obj Y.property V
      (pushforwardOpen B X Y g W)]
  exact ⟨fun ⟨φ⟩ => ⟨(g.toToposHom.adj.homEquiv _ _) (eV.hom ≫ φ) ≫ eW.hom⟩,
    fun ⟨ψ⟩ => ⟨eV.inv ≫ (g.toToposHom.adj.homEquiv _ _).symm (ψ ≫ eW.inv)⟩⟩

/-- The target half of the gluing sends the whole of the target to the whole of the source,
stated for `AlgebraicGeometry.inverseImageOpen`. -/
theorem inverseImageOpen_top (X Y : B.Scheme)
    (g : RingedToposHom (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property))) :
    inverseImageOpen B X Y g ⊤ = ⊤ :=
  eq_top_of_iso_inverseImage_openRepresentableSheaf_top B X Y g _
    (nonempty_iso_inverseImageOpen B X Y g ⊤)

/-- **The covering step of the Zariski gluing of Stacks 04I7: the opens produced from an open
covering of the target cover the source.**

Given an open covering `{V_j}` of the target and, for each `j`, an open `W_j` of the source with
`g⁻¹h_{V_j} ≅ h_{W_j}`, the `W_j` cover the source.  The index type is arbitrary.

The proof is that the operation `V ↦ W` of
`AlgebraicGeometry.existsUnique_open_inverseImage_openRepresentableSheaf` is a *left adjoint*
between the lattices of opens
(`AlgebraicGeometry.galoisConnection_inverseImageOpen_pushforwardOpen`,
whose content is the adjunction `g⁻¹ ⊣ g_*`), hence preserves arbitrary suprema, and that it
sends `⊤` to `⊤`, which is
`AlgebraicGeometry.eq_top_of_iso_inverseImage_openRepresentableSheaf_top`.  Neither the
epimorphism `⨆_j h_{V_j} ⟶ *` of sheaves nor the local surjectivity of `⨆_j h_{W_j} ⟶ *` is
needed: both are the formal content of the Galois connection, and the one geometric input is
the degenerate case `V = ⊤`. -/
theorem iSup_eq_top_of_forall_iso_inverseImage_openRepresentableSheaf (X Y : B.Scheme)
    (g : RingedToposHom (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
    {ι : Type*} (V : ι → Y.obj.Opens) (hV : ⨆ j, V j = ⊤) (W : ι → X.obj.Opens)
    (hW : ∀ j, Nonempty (g.toToposHom.inverseImage.obj
      ((presheafToSheaf (SmallEtale.topology B Y.obj Y.property) (Type u)).obj
        (openRepresentable'.{u, u} B Y.obj Y.property (V j))) ≅
      (presheafToSheaf (SmallEtale.topology B X.obj X.property) (Type u)).obj
        (openRepresentable'.{u, u} B X.obj X.property (W j)))) :
    ⨆ j, W j = ⊤ := by
  have hWj : ∀ j, W j = inverseImageOpen B X Y g (V j) := fun j =>
    eq_inverseImageOpen B X Y g (V j) (W j) (hW j)
  calc ⨆ j, W j = ⨆ j, inverseImageOpen B X Y g (V j) := by simp only [hWj]
    _ = inverseImageOpen B X Y g (⨆ j, V j) :=
        ((galoisConnection_inverseImageOpen_pushforwardOpen B X Y g).l_iSup).symm
    _ = inverseImageOpen B X Y g ⊤ := by rw [hV]
    _ = ⊤ := inverseImageOpen_top B X Y g

/-! ### The gluing step of the Zariski gluing of Stacks 04I7, on the morphisms of schemes -/

/-- **Morphisms of schemes glue over an open covering of the source.** Given opens `W j` of `X`
covering `X` and morphisms `f j : W j ⟶ Y` which agree on the overlaps `W j ⊓ W k`, there is
exactly one morphism `X ⟶ Y` restricting to each `f j`.

This is the engine of the last step of the proof of Theorem 59.40.5, and it is stated for
arbitrary schemes because nothing of that proof enters it.  Mathlib supplies the three halves
separately and for a bundled `AlgebraicGeometry.Scheme.OpenCover`
(`AlgebraicGeometry.Scheme.Cover.glueMorphisms`, `.ι_glueMorphisms` and `.hom_ext`); what is
added here is the passage from an indexed family of opens with `⨆ j, W j = ⊤` — which is the
form in which the covering step
`AlgebraicGeometry.iSup_eq_top_of_forall_iso_inverseImage_openRepresentableSheaf` produces its
covering — and from the compatibility stated on `W j ⊓ W k` rather than on the categorical
pullback of `(W j).ι` and `(W k).ι`, the two being identified by
`AlgebraicGeometry.isPullback_opens_inf`. -/
theorem existsUnique_schemeHom_of_iSup_opens_eq_top {X Y : Scheme.{u}} {ι : Type*}
    (W : ι → X.Opens) (hW : ⨆ j, W j = ⊤) (f : ∀ j, (W j).toScheme ⟶ Y)
    (hf : ∀ j k, X.homOfLE (inf_le_left : W j ⊓ W k ≤ W j) ≫ f j =
      X.homOfLE (inf_le_right : W j ⊓ W k ≤ W k) ≫ f k) :
    ∃! a : X ⟶ Y, ∀ j, (W j).ι ≫ a = f j := by
  have hf' : ∀ j k, Limits.pullback.fst ((W j).ι) ((W k).ι) ≫ f j =
      Limits.pullback.snd ((W j).ι) ((W k).ι) ≫ f k := fun j k => by
    rw [← cancel_epi (isPullback_opens_inf (W j) (W k)).isoPullback.hom, ← Category.assoc,
      CategoryTheory.IsPullback.isoPullback_hom_fst, ← Category.assoc,
      CategoryTheory.IsPullback.isoPullback_hom_snd]
    exact hf j k
  let c := X.openCoverOfIsOpenCover W hW
  refine ⟨c.glueMorphisms f hf', c.ι_glueMorphisms f hf', fun a ha => ?_⟩
  refine c.hom_ext a _ fun j => ?_
  rw [c.ι_glueMorphisms f hf' j]
  exact ha j

/-- **The gluing step of the Zariski gluing of Stacks 04I7.** Given an open covering `{V_j}` of
the target, the opens `W_j` of the source that the target half produces from it, and a morphism
of schemes `f_j : W_j ⟶ Y` for each `j` agreeing on the overlaps, there is exactly one morphism
of schemes `X ⟶ Y` restricting to each `f_j`.

The covering hypothesis on the `W_j` is not assumed: it is the covering step
`AlgebraicGeometry.iSup_eq_top_of_forall_iso_inverseImage_openRepresentableSheaf`, which the
proof calls on the hypothesis `hW` that each `W_j` represents `g⁻¹h_{V_j}`.  So the only input
this step still takes is the chartwise morphisms themselves, and those come from the existence
clause of Stacks 04I6 applied to affine charts of `W_j` and `V_j`, which requires the
restriction of `g` to those opens; see this module's implementation notes. -/
theorem existsUnique_schemeHom_of_forall_iso_inverseImage_openRepresentableSheaf
    (X Y : B.Scheme)
    (g : RingedToposHom (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
    {ι : Type*} (V : ι → Y.obj.Opens) (hV : ⨆ j, V j = ⊤) (W : ι → X.obj.Opens)
    (hW : ∀ j, Nonempty (g.toToposHom.inverseImage.obj
      ((presheafToSheaf (SmallEtale.topology B Y.obj Y.property) (Type u)).obj
        (openRepresentable'.{u, u} B Y.obj Y.property (V j))) ≅
      (presheafToSheaf (SmallEtale.topology B X.obj X.property) (Type u)).obj
        (openRepresentable'.{u, u} B X.obj X.property (W j))))
    (f : ∀ j, (W j).toScheme ⟶ Y.obj)
    (hf : ∀ j k, X.obj.homOfLE (inf_le_left : W j ⊓ W k ≤ W j) ≫ f j =
      X.obj.homOfLE (inf_le_right : W j ⊓ W k ≤ W k) ≫ f k) :
    ∃! a : X ⟶ Y, ∀ j, (W j).ι ≫ B.inclusion.map a = f j := by
  obtain ⟨a, ha, hu⟩ := existsUnique_schemeHom_of_iSup_opens_eq_top W
    (iSup_eq_top_of_forall_iso_inverseImage_openRepresentableSheaf B X Y g V hV W hW) f hf
  exact ⟨ObjectProperty.homMk a, ha, fun b hb => InducedCategory.hom_ext (hu b.hom hb)⟩

/-! ### The two existence clauses -/

/-- **The existence clause of Stacks 04I7.** Every morphism of locally ringed topoi between the
small étale ringed topoi of two schemes of `B` is 2-isomorphic to the one of a morphism of
schemes.

The uniqueness of that morphism of schemes is not part of the clause: it is proved
unconditionally as `AlgebraicGeometry.eq_of_twoIso_smallEtaleRingedToposHom`, and
`AlgebraicGeometry.existsUnique_schemeHom_twoIso_of_clause04I7` is the two together. -/
def Clause04I7 : Prop :=
  ∀ (X Y : B.Scheme)
    (g : RingedToposHom (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property))),
    g.IsLocallyRinged →
      ∃ f : X ⟶ Y, Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g
        (smallEtaleRingedToposHom B f))

/-- **The existence clause of Stacks 04I6**: `AlgebraicGeometry.Clause04I7` restricted to two
*affine* schemes, which is the generality at which the source states it. -/
def Clause04I6 : Prop :=
  ∀ (X Y : B.Scheme), IsAffine (B.inclusion.obj X) → IsAffine (B.inclusion.obj Y) →
    ∀ g : RingedToposHom
      (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)),
      g.IsLocallyRinged →
        ∃ f : X ⟶ Y, Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g
          (smallEtaleRingedToposHom B f))

/-- The existence clause of Stacks 04I7 implies that of Stacks 04I6: the latter is the former
with both schemes assumed affine.  The converse is the content of the proof of Theorem 59.40.5,
a Zariski gluing over the source and then over the target, and is not proved here. -/
theorem clause04I6_of_clause04I7 (h : Clause04I7 B) : Clause04I6 B :=
  fun X Y _ _ g hg => h X Y g hg

/-! ### Stacks 04I7 from its existence clause -/

/-- **Stacks 04I7, with its existence clause as a named hypothesis.** Given schemes `X` and `Y`
of a big étale site and a morphism of *locally* ringed topoi
`g : (Sh(X_étale), 𝒪_X) ⟶ (Sh(Y_étale), 𝒪_Y)`, there is exactly one morphism of schemes
`f : X ⟶ Y` for which `g` is 2-isomorphic to `(f_small, f_small^♯)`.

The uniqueness half is discharged, from Stacks 04LW
(`AlgebraicGeometry.eq_of_twoIso_smallEtaleRingedToposHom`); the existence half is the
hypothesis `hB`.  That hypothesis is proved as `AlgebraicGeometry.clause04I7` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.Existence.Assembly`, where
Stacks 04I7 is registered on
`AlgebraicGeometry.existsUnique_schemeHom_twoIso_smallEtaleRingedToposHom`. -/
theorem existsUnique_schemeHom_twoIso_of_clause04I7 (hB : Clause04I7 B) {X Y : B.Scheme}
    (g : RingedToposHom (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
    (hg : g.IsLocallyRinged) :
    ∃! f : X ⟶ Y, Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g
      (smallEtaleRingedToposHom B f)) := by
  obtain ⟨f, ⟨t⟩⟩ := hB X Y g hg
  refine ⟨f, ⟨t⟩, ?_⟩
  rintro f' ⟨t'⟩
  exact eq_of_twoIso_smallEtaleRingedToposHom B g f' f t' t

end AlgebraicGeometry

end
