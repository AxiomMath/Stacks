module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.AffineExistence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.ExistenceClause

/-!
# The existence clauses of Stacks 04I6 and 04I7, as named hypotheses

[Stacks Project, Tag 04I7] (Étale Cohomology, Theorem 59.40.5) says that for schemes `X` and
`Y` every morphism of *locally* ringed topoi
`(g, g^♯) : (Sh(X_étale), 𝒪_X) ⟶ (Sh(Y_étale), 𝒪_Y)` is 2-isomorphic to `(f_small, f_small^♯)`
for a unique morphism of schemes `f : X ⟶ Y`; [Stacks Project, Tag 04I6] (Lemma 59.40.4) is the
same assertion for `X` and `Y` **affine**.  The uniqueness half of both is proved and
unconditional — `AlgebraicGeometry.eq_of_twoIso_smallEtaleRingedToposHom` of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/RingedToposTwoIso.lean`,
which is [Stacks Project, Tag 04LW] — so what is open in each is exactly existence.

The two existence clauses, `AlgebraicGeometry.Clause04I6` and `AlgebraicGeometry.Clause04I7`,
together with `AlgebraicGeometry.clause04I6_of_clause04I7`, are defined in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.ExistenceClause`. This file
records further consequences of them.

**`Clause04I6` is a theorem, not a hypothesis**: `AlgebraicGeometry.clause04I6` proves it
from `AlgebraicGeometry.exists_schemeHom_twoIso_of_isLocallyRinged` of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/AffineExistence.lean`, which
is proved outright and is in fact more general — it assumes only the *target* affine, which is
`AlgebraicGeometry.clause04I6_affineTarget` below.  So no statement in the development need carry
`Clause04I6` as an argument, and Stacks 04I6 itself is registered outright, on
`AlgebraicGeometry.existsUnique_schemeHom_twoIso_of_isLocallyRinged`.

`Clause04I7` is not proved here: it is `AlgebraicGeometry.clause04I7` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.Existence.Assembly`, where
Stacks 04I7 is registered.  **Nothing here proves Stacks 04I7 or Stacks 04KL, and nothing here
carries a `@[stacks …]` attribute.**  A declaration that assumed one of these clauses and then
registered the tag it is the clause of would be a conditional registration; that is the thing
this file exists to make unnecessary, not to hide.

## Main results

* `AlgebraicGeometry.existsUnique_of_clause04I7` — the existence clause plus the uniqueness of
  Stacks 04LW is the **full** `∃!` statement of Stacks 04I7.  This is what makes the eventual
  discharge a one-liner: a proof of `Clause04I7` turns into the tag's own statement here, with
  no further work and no restatement.
* `AlgebraicGeometry.existsUnique_affine_of_clause04I6` — the same for Stacks 04I6.
* `AlgebraicGeometry.clause04I6` — **Stacks 04I6's existence clause, proved**, so the first link
  of the chain is closed.
* `AlgebraicGeometry.clause04I6_affineTarget` — the same at the generality of
  `AlgebraicGeometry.exists_schemeHom_twoIso_of_isLocallyRinged`, with only the target affine.
  This is the input the passage to Stacks 04I7 consumes, and it is why that passage needs no
  Zariski gluing over the *source*.

## The two links, and what each needs

This section records the route from Stacks 04I6 to Stacks 04I7 (link 1) and from Stacks 04I7 to
Stacks 04KL (link 2).  Neither link is proved in this file; link 1 is
`AlgebraicGeometry.clause04I7` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.Existence.Assembly`.

**The two links are not in series.**  As explained under link 2 below, the proof of Stacks 04KL
can be restructured so that every application of a recovery theorem is at an affine source *and*
an affine target, which is Stacks 04I6 and not Stacks 04I7.  So link 1 is not a prerequisite of
Stacks 04KL, and neither are the two inputs link 1 needs.  What Stacks 04KL needs instead is
listed there.

1. `Clause04I7 B` — the proof of Theorem 59.40.5 from Lemma 59.40.4.  The source calls the
   bookkeeping "a bit messy"; it is Zariski gluing twice over, and **the gluing over the source
   is already discharged**.  `AlgebraicGeometry.clause04I6_affineTarget` carries no hypothesis on
   `X`, so the source's affine-target case — cover `X` by affine opens, compose `(g, g^♯)` with
   the localization morphism of each inclusion ([Stacks Project, Tag 04I5],
   `StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/LocallyRinged.lean:128`)
   using composition of locally ringed morphisms ([Stacks Project, Tag 04IG],
   `AlgebraicGeometry.RingedToposHom.isLocallyRinged_comp`),
   apply Stacks 04I6, glue the resulting `fᵢ` by the uniqueness of Stacks 04LW, and glue the
   2-isomorphisms using the rigidity of [Stacks Project, Tag 04IJ]
   (`StacksFrontier/AlgebraicGeometry/Spaces/SchemeSmallEtaleTwoMorphismRigidity.lean:65`) — is not
   needed at all: it is subsumed, because the existence theorem already holds at an
   arbitrary `X`.  What remains is exactly the gluing over the *target*: for `V ⊆ Y` affine open,
   `h_V` is a subsheaf of the final sheaf on `Y_étale`, so `g⁻¹h_V` is a subsheaf of
   the final sheaf on `X_étale`, and [Stacks Project, Tag 04HV] represents it by an open
   `W ⊆ X` — that is `AlgebraicGeometry.existsUnique_open_of_isSubterminal` in
   `StacksFrontier/AlgebraicGeometry/EtaleCohomology/SubterminalSheaves.lean:748` —
   after which the localization square of [Stacks Project, Tag 04IH]
   (`StacksFrontier/AlgebraicGeometry/Recovery04IH/LocalizationMorphismsLocallyRinged.lean:137`,
   the topos localization morphism) produces `g' : W ⟶ V`, to which `clause04I6_affineTarget`
   applies directly with no affineness demanded of `W`, and the `f_V : W ⟶ V ⟶ Y` so obtained
   are glued over a cover of `X` by the uniqueness of Stacks 04LW.

   **What the target half needs.**  Four inputs; two are supplied below, and two are
   substantial, one of which has its own missing input named inside this development; the last
   gluing step, by contrast, is free.

   * *Supplied.* `IsSubterminal (g⁻¹ F)` from `IsSubterminal F` is
     `CategoryTheory.IsSubterminal.map_of_preservesFiniteLimits` of
     `StacksFrontier/AlgebraicGeometry/EtaleCohomology/SubterminalSheaves.lean`; the field
     `MorphismOfTopoi.preservesFiniteLimits` is what instantiates it.  Mathlib's `IsSubterminal`
     API says nothing about functors.
   * *Supplied.* The Zariski gluing of the `f_V` into a single `f : X ⟶ Y`, with its uniqueness,
     is Mathlib's `AlgebraicGeometry.Scheme.Cover.glueMorphisms`,
     `…Cover.ι_glueMorphisms` and `…Cover.hom_ext`, with the cover built by
     `AlgebraicGeometry.Scheme.openCoverOfIsOpenCover`.  An open of an object of the big étale
     site is again an object of it, `AlgebraicGeometry.BigEtaleSite.openObj` /
     `openObjι` of
     `StacksFrontier/AlgebraicGeometry/Topologies/Etale/SmallEtalePullbackFpqcAmalgamation.lean`, so
     no size argument has to be redone to form `V ⊆ Y` or `W ⊆ X`.
   * **Needed, and a universe restatement, not a theorem.**  Stacks 04HV is formalized only for sheaves
     of `Type (max (u + 1) v)` — that is the `F : smallEtaleTopos.{u, max (u + 1) v} B S hS` of
     `AlgebraicGeometry.existsUnique_open_of_isSubterminal` — whereas the small étale ringed topos
     of this chain is `Sheaf _ (Type u)`: `AlgebraicGeometry.smallEtaleRingedSite` is a
     `RingedSite.{u + 1, u, u}`, so its `toRingedTopos` has `O : Sheaf _ CommRingCat.{u}` and
     `RingedTopos.Topos` is `Sheaf _ (Type u)`.  Since `max (u + 1) v` is never `u`, the formalized
     04HV **cannot be applied to `g⁻¹h_V`**; attempting it reports `stuck at solving universe
     constraint max (u + 1) ?v =?= u`.  What is needed is 04HV for `Type u`-valued sheaves.  Note
     that the sheaf of an open is easier there, not harder: `AlgebraicGeometry.openRepresentable`
     carries a `uliftYoneda` only because its sections are raised, and at `Type u` the hom-sets of
     the site need no lifting at all.
   * **Available, at both levels.**  The localization of a given morphism of ringed *sites* is
     locally ringed — `AlgebraicGeometry.RingedSite.Hom.isLocallyRinged_localized` of
     `StacksFrontier/AlgebraicGeometry/Recovery04IH/LocalizedMorphismLocallyRinged.lean`, with the
     whole of Stacks 04IH (3) on `localized_isLocallyRinged_sites` in the same file.  The
     *topos-level* form is proved too, and unconditionally: the morphism this link wants is
     `AlgebraicGeometry.RingedToposHom.relocalized` of
     `StacksFrontier/CategoryTheory/Sites/Modules/Localization/RingedToposRelocalizedMorphism.lean`
     — it takes a map `s : F ⟶ g⁻¹G`, so `F := h_W`, `G := h_V` and `s` the comparison — and
     `AlgebraicGeometry.RingedToposHom.isLocallyRinged_relocalized` of
     `StacksFrontier/AlgebraicGeometry/Recovery04IH/LocalizedToposMorphismLocallyRinged.lean`
     proves `IsLocallyRinged` of exactly that one, from
     `.isLocallyRinged_localized` in the same file pasted with Stacks 04IG, together with the
     structure-map identity of 04IF's square,
     `AlgebraicGeometry.RingedToposHom.localized_fSharpInverseImage_forget` of
     `StacksFrontier/CategoryTheory/Sites/Modules/Localization/RingedToposMorphismLocalization.lean`.
     The other locally-ringed facts the development has are about the *canonical* localization and
     relocalization morphisms (`Recovery04IH/LocalizationMorphismsLocallyRinged.lean`) and about
     the localized *topos* as an object (`Recovery04IH/ToposLocalizationLocallyRinged.lean`).

     **The Beck–Chevalley input.**  `IsIso` of
     `CategoryTheory.SliceTopos.localizedInverseImageMate` is the input that
     `AlgebraicGeometry.RingedSite.Hom.localized` being a *locally ringed* morphism needs, through
     the identification of Stacks 03CF clause (b) with the mate.  That identification is
     `CategoryTheory.SliceTopos.overPullbackCompSheafPullbackOverPostIso_hom` of
     `StacksFrontier/CategoryTheory/Sites/SliceTopos/InverseImage.lean`, registered on
     Stacks 03CF, and the invertibility it yields for the mate that
     `localized_fSharpInverseImage_forget` actually uses is
     `CategoryTheory.SliceTopos.isIso_localizedInverseImageMate` (with its component form
     `isIso_localizedInverseImageMate_app`) of
     `StacksFrontier/AlgebraicGeometry/Recovery04IH/LocalizedMateInvertible.lean`.  The transport of
     the units square along that isomorphism — the units subsheaf of a restricted structure sheaf
     is the restriction of the units subsheaf on the nose and `j_U⁻¹` is a right adjoint, so it
     preserves the cartesian square — is
     `AlgebraicGeometry.RingedSite.Hom.isPullback_localizedUnitsSquare`.  So nothing is needed here
     at either level; what link 1 still needs is the universe restatement of Stacks 04HV above and
     the ringed-topos form of the identification below.

     A further input follows from this one: the identification of `Sh(W_étale)` with
     `Sh(X_étale)/h_W` is available at the level of sites and of sheaves of sets
     (`AlgebraicGeometry.smallEtaleEquivalenceOver` and `smallEtaleEquivalenceOver_topology` of
     `StacksFrontier/AlgebraicGeometry/Topologies/Etale/SliceEquivalence/`) but not as ringed topoi.
2. `Clause04I7 ⟹ Stacks 04KL` — the proof of Properties of Spaces, Theorem 66.28.4.  For `U` an
   object of `X_étale`, `V` of `Y_étale` and a section `s ∈ (g⁻¹h_V)(U)`, the relocalization of
   [Stacks Project, Tag 04J8] gives `(g_s, g_s^♯)`, to which `Clause04I7` applies; the resulting
   `f_s` are functorial by the uniqueness of Stacks 04LW; a chart `U` and a section `s` are produced
   from the surjectivity of `g⁻¹h_V ⟶ *`; and the two presentations are glued by
   `AlgebraicGeometry.Space.existsUnique_hom_of_atlas_square` in
   `StacksFrontier/AlgebraicGeometry/Spaces/AtlasMorphismDescent.lean`, which is [Stacks Project,
   Tag 0262] part (3).  This link additionally needs the bridge described below,
   and a relocalization at the universe of the small étale ringed topos of an algebraic space:
   `AlgebraicGeometry.Space.smallEtaleRingedTopos` is a `RingedTopos.{u, u + 1, u}`, whereas the
   relocalized morphism of Tag 04J8 in
   `StacksFrontier/CategoryTheory/Sites/Modules/Localization/RingedToposRelocalizedMorphism.lean`
   is stated for ringed topoi whose sections are in `Type u`; that mismatch is already recorded
   at `AlgebraicGeometry/Spaces/Topologies/SpacesEtaleChartRelocalizedComparison.lean:265`.

   **Which recovery applications link 2 makes, and at what target.**  The source's
   proof applies the recovery theorem for schemes exactly twice — once to the chart
   `s : h_U ⟶ g⁻¹h_V`, giving `f_s : U ⟶ V`, and once to `s × s : h_{R'} ⟶ g⁻¹h_R` with
   `R' = U ×_X U` and `R = V ×_Y V`, giving `f_{s × s} : R' ⟶ R`.  Of the two:

   * **The second application is not needed at all.**  It is used only to produce the invariance
     of `k := h_{f_s} ≫ h_{V ⟶ Y}` under the kernel pair of `U ⟶ X`, and that invariance is an
     equality of two morphisms `h_{R'} ⟶ Y` of algebraic spaces out of a *representable* one,
     which [Stacks Project, Tag 04M6] decides from a 2-isomorphism of the induced morphisms of
     small étale ringed topoi.  This is available, in the form the descent consumes:
     `AlgebraicGeometry.Space.existsUnique_hom_of_atlas_twoIso` and
     `AlgebraicGeometry.Space.exists_hom_of_chartHoms_twoIso` of
     `StacksFrontier/AlgebraicGeometry/Spaces/AtlasMorphismDescentTwoIso.lean`.  Dropping it is not
     optional bookkeeping: `R = V ×_Y V` is the one target in the proof that **cannot** be taken
     affine.  Even for `V` affine it is only étale over `V`; if it were affine then `Y` would be
     quasi-compact *and* quasi-separated, so demanding it would restrict the theorem to qcqs
     algebraic spaces.  The development carries the witness, its algebraicity conditional on the
     two effective-descent hypotheses this library's Stacks 0265 carries
     (`AlgebraicGeometry.IntegerShift.isAlgebraicSpace_shiftQuotient`): for `Y` the quotient of
     `Spec K[y, x_n : n ∈ ℤ]` by the integer shift
     (`AlgebraicGeometry.IntegerShift.shiftQuotient`) the chart
     `AlgebraicGeometry.IntegerShift.shiftChart` is affine
     (`AlgebraicGeometry.IntegerShift.isAffine_shiftChart`) while its kernel pair is
     `AlgebraicGeometry.IntegerShift.shiftRelationObj`
     (`AlgebraicGeometry.Space.quotientMap_isPullback` of
     `StacksFrontier/AlgebraicGeometry/Spaces/PresentationFromQuotient.lean`), which is the
     `Multiplicative ℤ`-indexed coproduct `∐ fun _ ↦ shiftChart` of
     `AlgebraicGeometry.Space.actionRelationScheme` and so is not even quasi-compact.
   * **The first application need not be taken at an arbitrary target either, but not for the
     reason a chart of `Y` suggests.**  A chart `V ⟶ Y` of an algebraic space is affine only
     when `Y` is quasi-compact: [Stacks Project, Tag 03FX]
     (`AlgebraicGeometry.IsAlgebraicSpace.exists_etale_surjective_coproduct_affine_cover`)
     delivers a *disjoint union* of affines, and a disjoint union of infinitely many nonempty
     affines is not affine.  What does make the target affine is restructuring the gluing:
     `AlgebraicGeometry.Space.exists_hom_of_chartHoms_twoIso` asks for a morphism `h_T ⟶ Y` for
     each **affine** étale chart `T` of `X`, and such a morphism is produced from an *affine*
     chart `V_i` of `Y` together with a section `h_T ⟶ g⁻¹h_{V_i}`.  Both schemes are then
     affine, so what is applied is [Stacks Project, Tag 04I6] — **closed**, and registered on
     `AlgebraicGeometry.existsUnique_schemeHom_twoIso_of_isLocallyRinged` — and not Stacks 04I7
     at all.  So link 1 is **not needed for 04KL** in this route, and neither are the two inputs
     link 1 needs: 04HV at `Type u`, and the Zariski gluing over the target.

   **What the affine-target route needs.**  The inputs are listed below; none of them is
   Stacks 04I7:

   * *The source-side refinement* — **available.**  A single affine chart `T` of `X` need not admit a
     section into a single `g⁻¹h_{V_i}`; only a cover of `T` does, since surjectivity of
     `∐ᵢ g⁻¹h_{V_i} ⟶ *` is local.  `exists_hom_of_chartHoms_twoIso` wants the family on *every*
     affine chart, and the variant for a family given only on a cofinal set of affine charts is
     `AlgebraicGeometry.Space.exists_hom_of_chartHoms_twoIso_of_cofinal` of
     `StacksFrontier/AlgebraicGeometry/Spaces/CofinalChartGluing.lean`, with the cofinality condition
     `AlgebraicGeometry.Space.IsCofinalChartFamily` stated for affine charts — which is what the
     caller proves — and raised to arbitrary charts by `IsCofinalChartFamily.exists_cover`.  As
     expected, it is a statement about the fppf sheaf `Y` and the étale topology alone: no recovery
     theorem, no universe question, no ringed topoi.
   * *The relocalization, and that it is locally ringed.*  Turning `s : h_T ⟶ g⁻¹h_{V_i}` into a
     morphism of ringed topoi `Sh(T_étale) ⟶ Sh(V_{i,étale})`, and knowing it locally ringed, is
     the same input as link 1's fourth bullet above, now over an algebraic space: Tag 04J8's
     `AlgebraicGeometry.RingedToposHom.relocalized` at the universe of
     `AlgebraicGeometry.Space.smallEtaleRingedTopos`, plus `IsLocallyRinged` of it, plus the
     identification of the localized ringed topos with the small étale ringed topos of the chart.
     As explained there, the Beck–Chevalley comparison involved is invertible.

     **The universe obstruction.**  It is *not* that the
     localization forces the sections of the structure sheaf into the universe of the site's
     objects.  What `AlgebraicGeometry.RingedTopos.elementSite` forces is that the sections and
     the *morphisms* share a universe — `CostructuredArrow yoneda F.obj` only typechecks when
     `F` is valued in the universe `yoneda` lands in — and that holds here:
     `Space.smallEtaleRingedTopos` is a `RingedTopos.{u, u + 1, u}`, morphisms and sections both
     at `u`.  The *object* universe is genuinely free, and the localization preserves the shape:
     by the comma-category arithmetic the site of elements has objects in `Type (max u₁ v₁)` and
     morphisms in `Type v₁`, so `localizedRingedTopos` would be typed
     `RingedTopos.{v, max u v, v}` and at `{u, u + 1, u}` that is `{u, u + 1, u}` again.
     If the four `variable` lines of
     `CategoryTheory/Sites/Modules/Localization/ToposLocalization.lean` are rewritten accordingly,
     two things break, in this order.

     1. `Functor.sheafPushforwardCocontinuous` reports
        `failed to synthesize ∀ F, (elementProjection X F).op.HasPointwiseRightKanExtension F` —
        the right Kan extension computing the *direct* image is indexed by comma categories whose
        objects lie in `Type (max u v)`, so it does not exist in `Type v` for formal reasons.
        **This one is solved by a two-line proof**: the
        site of elements is essentially small at `v` whenever the site is, because by the Yoneda
        lemma it is the category of elements of `F`, and Mathlib's
        `CategoryTheory.Elements.essentiallySmall` covers that —
        `(essentiallySmall_congr.{v} (CategoryOfElements.costructuredArrowYonedaEquivalence
        F.obj)).1 inferInstance`, after which
        `CategoryTheory.Limits.hasLimitsOfShape_of_essentiallySmall` gives
        `HasLimitsOfShape (StructuredArrow W (elementProjection X F).op) (Type v)` and the Kan
        extension exists.  Note that Mathlib's `CostructuredArrow.essentiallySmall` does *not*
        apply: it asks for `LocallySmall.{v}` of the presheaf category, whose hom types are in
        `Type (max u v)`.  `[EssentiallySmall.{v} X.C]` is free at `u = v` by
        `essentiallySmallSelf`, so adding it as a hypothesis costs nothing downstream, and it
        holds for the small étale site by `Space.SmallEtale.instEssentiallySmall`.
     2. `localizationInverseImageCommRingIso` and `localizationMorphism` then report
        `stuck at solving universe constraint v =?= max (max u v) ?w` against
        `UnivLE.{max (max u v) ?w, max (max u v) ?w}`.  Adding the four `HasSheafCompose` side
        conditions of `restrictionCommRingIso` as hypotheses does **not** remove it, so it is not
        those.  The free metavariable `?w` is the signature this file's own notes elsewhere
        record for a stuck report that outlives a successful search — the declarations *are*
        produced, and only the report remains — but it is still an error.  What the shape says
        is that a `Type v`-valued sheaf theory on a site with objects
        in `Type (max u v)` needs the bespoke smallness plumbing that
        `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleToposRingUniverse.lean` writes out for the
        small étale site — local smallness, sheafification, the Kan extensions, and left exactness
        of the inverse image — and that the element site needs its own copy.  Unlike the
        spaces-étale site the element site **is** essentially small at `v`, so that copy is
        available in principle; it is not in the library.

        Past that file the chain of files to generalize is
        `StacksFrontier/CategoryTheory/Sites/Modules/Localization/RingedToposMorphismLocalization.lean` (04IF, 7 declarations),
        `Recovery04IH/ToposRelocalization.lean` (04J4, 9 — and this one routes through
        `Stacks.Sheaves.LocallyRingedTopos.RingedTopos.{u}`, a structure with a single universe
        variable that cannot be generalized, so its continuity and cocontinuity inputs have to be
        re-derived), `Recovery04IH/LocalizedToposStructureMap.lean` (26),
        `StacksFrontier/CategoryTheory/Sites/Modules/Localization/RingedToposRelocalizedMorphism.lean` (04J8, 11),
        `Recovery04IH/LocalizedToposMorphismLocallyRinged.lean` (2),
        `Recovery04IH/ToposLocalizationLocallyRinged.lean` (1) and
        `StacksFrontier/CategoryTheory/Sites/Modules/Localization/SliceEquivalence.lean` (4), plus the `RingedSite.Hom` comparison layer
        (`StacksFrontier/CategoryTheory/Sites/Modules/Localization/RelocalizedMorphismComparison.lean`, 44, and its neighbours), whose
        morphism structure `AlgebraicGeometry.RingedSite.Hom` is itself declared at
        `RingedSite.{u, u, w}` and would have to migrate to the already-general
        `RingedSite.HomGeneral`.  The slice-topos presentation is not a way round it:
        `CategoryTheory/Sites/SliceTopos/` is stated for `SmallCategory` sites throughout.
   * *The bridge below*: **available, in all four of its parts** (see the second bullet of the next
     section).
   * *A chart and a section, from the surjectivity of `∐ᵢ g⁻¹h_{V_i} ⟶ *`.*  **Available**, in
     `StacksFrontier/AlgebraicGeometry/Spaces/CofinalChartFamilySurjective.lean`, which supplies the
     passage from the small étale topology to the big fppf one; the site-generic half is
     general.  The statement is
     `AlgebraicGeometry.Space.isCofinalChartFamily_of_isLocallySurjective_sigmaDesc`: for a
     family `G i` of sheaves on the small étale site of `F` whose induced morphism out of the
     coproduct onto the final sheaf is a surjection of sheaves, the charts over which some `G i`
     has a section — `AlgebraicGeometry.Space.HasSomeChartSection` — form a cofinal family in
     the sense of `AlgebraicGeometry.Space.IsCofinalChartFamily`.  Two inputs, both already
     present: `CategoryTheory.Sheaf.exists_sieve_of_isLocallySurjective_sigmaDesc` of
     `StacksFrontier/CategoryTheory/Sites/JointlyLocallySurjective.lean`, which turns the
     surjectivity into a covering sieve each of whose arrows has a section of some member over
     its source — so the `Presheaf.IsLocallySurjective` step is *not* specific to the big fppf
     topology — and `Space.SmallEtale.exists_finite_affine_etale_ofArrows_le` of
     `Spaces/SmallEtaleAffineRefinement.lean`, which refines that sieve to a finite family of
     charts with affine underlying scheme whose underlying morphisms of schemes form an étale,
     hence fppf, covering family; `BigFppfOver.sieve_generate_ofArrows_mem_topology` then makes
     it a covering sieve of the big fppf site, which is the topology the cofinality condition
     speaks about.  Nothing is vacuous: the one-member family consisting of the final sheaf
     selects every affine étale chart (`isCofinalChartFamily_hasSomeChartSection_terminal`).

     **The surjectivity itself is proved too**, so nothing further is needed: for a morphism of
     topoi `g : Sh(X_étale) ⟶ Sh(Y_étale)` and étale charts `V i` of `Y` covering the final
     object of the small étale site of `Y`,
     `AlgebraicGeometry.Space.isLocallySurjective_sigmaDesc_inverseImage_smallEtaleChartSheaf`
     of `StacksFrontier/AlgebraicGeometry/Spaces/CofinalChartFamilyInverseImage.lean` proves
     `∐ᵢ g⁻¹h_{V i} ⟶ *` to be a surjection of sheaves, and the two gluing statements with the
     cofinality hypothesis fully discharged are
     `AlgebraicGeometry.Space.exists_hom_of_chartHoms_twoIso_of_coversTop` and
     `AlgebraicGeometry.Space.inducesSmallEtaleRingedToposHom_of_coversTop` in the same file.
     The engine is general and is not about coproducts at all:
     `Stacks.Topos.jointlyLocallyInhabited_inverseImage` of
     `StacksFrontier/CategoryTheory/Sites/Topos/JointlyLocallyInhabited.lean` transports "every
     object is covered by objects carrying a section of some member of the family" along a
     morphism of topoi, by moving the subsheaf of the terminal sheaf cut out by that condition
     across the adjunction.  `Stacks.Topos.isLocallySurjective_sigmaDesc_iff_of_isTerminal`
     identifies that condition with the surjectivity whenever the coproduct exists.

     **Which of the two forms a consumer should use.**  `HasCoproduct` for
     `Type u`-valued sheaves constrains the index universe:
     `HasColimitsOfShape (Discrete I) (Type u)` holds for `I : Type u` and fails for
     `I : Type (u + 1)`.  So the cover produced by
     `AlgebraicGeometry.Space.SmallEtale.coversTop_affineCharts`, being indexed by the affine
     étale charts themselves, has no coproduct of inverse images, and a consumer at that
     generality must take
     `AlgebraicGeometry.Space.isCofinalChartFamily_inverseImage_smallEtaleChartSheaf`, which
     reaches the cofinality with no colimit anywhere.  A `Type u`-indexed cover always exists
     (`AlgebraicGeometry.Space.SmallEtale.exists_coversTop_punit`, from the scheme atlas), so
     the coproduct form is usable as well.
   * *The descent of the 2-isomorphisms — step 6 of the source's proof.*  **Available**:
     `AlgebraicGeometry.Space.inducesSmallEtaleRingedToposHom_of_cofinal` of
     `StacksFrontier/AlgebraicGeometry/Spaces/CofinalChartTwoIsoGluing.lean` glues chartwise
     2-isomorphisms over a cofinal family of charts into the single 2-isomorphism
     `(g, g^♯) ≅ (l_small, l^♯)` that `Space.InducesSmallEtaleRingedToposHom` — and hence
     `Space.IsRecoveredFromSmallEtale` — demands, whereas
     `Space.exists_hom_of_chartHoms_twoIso_of_cofinal` produces only the morphism
     `l : X ⟶ Y`.  Both gluing statements are also recorded with their
     cofinality hypothesis discharged by the surjectivity, as
     `Space.exists_hom_of_chartHoms_twoIso_of_isLocallySurjective_sigmaDesc` and
     `Space.inducesSmallEtaleRingedToposHom_of_isLocallySurjective_sigmaDesc`.

The last link, from Stacks 04KL to the form its consumers use, is proved:
`AlgebraicGeometry.Space.isRecoveredFromSmallEtale_of_baseSpace` in
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/MorphismFromStructureMap.lean` reduces
`AlgebraicGeometry.Space.IsRecoveredFromSmallEtale`, which is quantified over an arbitrary base,
to the clause over the base alone.

## The `BigEtaleSite`/`BigFppfSite` bridge: what it would have to say

The clauses here are stated over a `AlgebraicGeometry.BigEtaleSite`, because that is the site
over which the scheme-level recovery results of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/` are stated.  Their
consumer, Stacks 04KL, lives over a `AlgebraicGeometry.BigFppfSite`: an algebraic space is a
sheaf on `AlgebraicGeometry.BigFppfOver B S hS`, and the objects of the small étale site
`AlgebraicGeometry.Space.SmallEtale B S hS X` of an algebraic space are objects of that fppf
site which are étale over `X`.  So the `f_s : U ⟶ V` that link 2 reads off a chart of `X` and a
chart of `Y` is a morphism of schemes of the *fppf* site, while `Clause04I7` speaks about
morphisms of schemes of an *étale* site.

**The site half of that bridge is already built**, and it is most of the first of the three
bullets below:

* **Supplied.** The identification of the two sites, *with their topologies and with their
  structure sheaves*, is `AlgebraicGeometry.Space.representedSmallEtaleEquivalence` of
  `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleRepresentableEquivalence.lean`, an equivalence
  `Space.SmallEtale B S hS (yoneda.obj U) ≌ SmallEtale (associatedBigEtaleSite B) …` for `U` an
  object of the big fppf site over `S`, together with
  `AlgebraicGeometry.Space.representedSmallEtaleEquivalence_topology` in the same file (the
  induced topology is the small étale one, so both directions are continuous) and
  `AlgebraicGeometry.Space.representedStructureMap` of
  `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModuleComparison.lean`, which compares the two
  structure sheaves and is **the identity** (`hom := 𝟙 _`): both sides send a chart to the global
  regular functions on the same scheme.  `AlgebraicGeometry.associatedBigEtaleSite` of
  `StacksFrontier/AlgebraicGeometry/Topologies/ChangeOfSites/FppfToEtaleSquares.lean` is the big
  étale site to read the schemes in, and it keeps the fppf site's own `cutoff`, so a chart of the
  fppf site is an object of it with no size argument to redo.  The restatement at `CommRingCat`
  is available too: `representedStructureMap` is `RingCat`-valued, through
  `AlgebraicGeometry.Space.ringStructureSheaf`, whereas
  `AlgebraicGeometry.smallEtaleRingedSite` carries the `CommRingCat`-valued
  `AlgebraicGeometry.SmallEtale.commRingStructureSheaf`, and the comparison at `CommRingCat` is
  `AlgebraicGeometry.Space.representedCommRingStructureMap` of
  `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedCommRingStructureComparison.lean` — the
  identity presheaf map again, an isomorphism in both directions
  (`representedCommRingStructureIso`, `representedCommRingStructureInverseIso`), and equal to
  `representedStructureMap` after forgetting commutativity
  (`sheafCompose_representedCommRingStructureMap`).  So this bullet is fully supplied.
* **All four are available.**  The transport in question is of
  `AlgebraicGeometry.RingedToposHom`, `AlgebraicGeometry.RingedToposHom.IsLocallyRinged`,
  `AlgebraicGeometry.RingedToposHom.TwoIso` and `AlgebraicGeometry.smallEtaleRingedToposHom`
  along that identification — i.e. that the morphism of small étale ringed topoi of a morphism of
  schemes does not depend on which big site the schemes are read in.

  **The first two**, in
  `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedSmallEtaleRingedToposEquivalence.lean`.
  `AlgebraicGeometry.Space.representedSmallEtaleRingedToposHom` is the identification as a
  morphism of ringed topoi from `Space.smallEtaleRingedTopos B S hS (yoneda.obj U)` to
  `RingedSite.toRingedTopos (smallEtaleRingedSite (associatedBigEtaleSite B) _ _)`,
  `…RingedToposInverse` is the same identification read from the scheme side,
  `isLocallyRinged_representedSmallEtaleRingedToposHom` and `…Inverse` say both are locally
  ringed, and `Space.schemeOfRepresentedRingedToposHom` with
  `isLocallyRinged_schemeOfRepresentedRingedToposHom` conjugate a morphism of the small étale
  ringed topoi of two representable algebraic spaces into one of the small étale ringed topoi of
  the two schemes, preserving the locally ringed condition.  That is what feeds
  `AlgebraicGeometry.clause04I6` / `clause04I6_affineTarget`.

  **The other two**, in
  `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedSmallEtaleRingedToposTransport.lean`:
  `AlgebraicGeometry.RingedToposHom.TwoIso` and
  `AlgebraicGeometry.smallEtaleRingedToposHom`.  The first is
  `AlgebraicGeometry.Space.twoIsoSchemeOfRepresentedRingedToposHom`, two whiskerings of the
  2-isomorphism calculus and nothing else.  The second is the naturality square — that
  `representedSmallEtaleRingedToposHom` is natural in the chart, i.e.
  `ε_V ∘ Space.smallEtaleRingedToposHom (representedSpaceMap g)` is 2-isomorphic to
  `smallEtaleRingedToposHom (associatedBigEtaleSite B) g.left ∘ ε_U` — and it is
  `AlgebraicGeometry.Space.representedSmallEtaleRingedToposNaturality`.  The inputs it is
  assembled from:

  * the site-level square is `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso` of
    `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleRepresentableBaseChange.lean` — chart base
    change along the represented morphism, followed by the identification for the source, is the
    identification for the target followed by base change of schemes;
  * on the scheme side the direct image of `smallEtaleRingedToposHom` **is** restriction along
    `smallEtaleBaseChange`, by `rfl` (`smallEtaleRingedToposHom_pushforward` of
    `RecoveringMorphisms/RingedToposTwoIso.lean`);
  * on the space side the direct image of `Space.smallEtaleRingedToposHom` is restriction along
    `smallBaseChange` whenever the morphism is relatively representable, which a represented one
    is (`Space.smallEtaleRingedToposHom_representable` and the `CommRingCat` form
    `…_representableRing` of `Spaces/SmallEtaleRingedToposHom.lean`, with
    `Space.relativelyRepresentable_yoneda_map`);
  * the two identifications' direct images are restrictions **only up to
    `Adjunction.rightAdjointUniq`, and that caveat is the whole difficulty**: they are built
    with `(representedSmallEtaleRestriction …).asEquivalence.inverse`, and
    `CategoryTheory.Functor.IsEquivalence` is a `Prop` class, so
    `CategoryTheory.Functor.inv` is assembled from `CategoryTheory.Functor.objPreimage`, a
    `Classical.choice`.  The identification's direct image therefore has **no description on
    sections**, and the structure-map compatibility cannot be checked there.  What is a
    restriction on the nose is the identification's *inverse* image, and the comparison of
    structure sheaves is the identity there (`representedCommRingStructureIso`).

  So the square is stated and proved on **inverse** images, through
  `AlgebraicGeometry.RingedToposHom.TwoIso.ofInverseImageIso` of
  `CategoryTheory/Sites/Modules/Localization/RingedToposRelocalizedMorphism.lean`, packaged as
  `AlgebraicGeometry.RingedToposHom.TwoIso.ofCommonRightAdjoint`: the two inverse images are
  left adjoints of one and the same *concrete* functor — restriction along the inverse
  equivalence for `U` followed by base change of schemes — and their structure maps are the
  adjunct of one and the same morphism, pullback of regular functions along the cartesian
  projection.  Neither adjunction used is the canonical one, and the choice-built direct images
  never appear.  The only geometric input is
  `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeComponent_inv_comp_snd`: the
  comparison of the two fibre products is a morphism over their projections to the chart.

  **The conjugated form and its converse are available too**, in
  `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedSmallEtaleRingedToposConjugate.lean`:
  `AlgebraicGeometry.Space.twoIsoSchemeOfSmallEtaleRingedToposHom` is the 2-isomorphism between
  `Space.schemeOfRepresentedRingedToposHom B S hS U V (Space.smallEtaleRingedToposHom …)` and
  `smallEtaleRingedToposHom (associatedBigEtaleSite B) g.left`, and
  `…reflectTwoIsoSchemeOfRepresentedRingedToposHom` and `…reflectTwoIsoSmallEtaleRingedToposHom`
  reflect a 2-isomorphism of conjugates back to one of the originals — the direction the proof
  of Stacks 04KL consumes, since it applies the recovery theorem to the conjugate and needs the
  2-isomorphism back on the spaces side.

  **Neither needs new geometry, and neither needs a second
  `AlgebraicGeometry.RingedToposHom.TwoIso.ofCommonRightAdjoint`** (for instance through the right
  adjoint `R_U ⋙ (chart base change)^s ⋙ R_V'`).  Both are the
  2-category calculus applied to the naturality square above: `TwoIso.associator`,
  `whiskerLeft`, `whiskerRight` and the two unitors
  (`AlgebraicGeometry.RingedToposHom.TwoIso.compId` and `.idComp` of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposTwoIsoUnitor.lean`, which are the
  only new generic ingredient), together with the statement that
  the identification is an **equivalence** in the 2-category:
  `AlgebraicGeometry.Space.representedSmallEtaleRingedToposCompInverse` and `…InverseComp` say
  its two composites with the identification read from the other side are 2-isomorphic to
  `AlgebraicGeometry.RingedToposHom.id`.  Those two are `TwoIso.ofInverseImageIso` on the unit
  respectively the counit of `AlgebraicGeometry.Space.representedSmallEtaleSheafCongr`, both of
  which are the identity at the structure sheaf by `rfl` — the counit of the equivalence of
  *sites* being the identity (`Space.representedSmallEtaleEquivalence_counit_app`).  So the
  choice-built direct images stay out of these statements for the same reason as before, but no
  common right adjoint has to be exhibited.

  The general machinery the instantiation is assembled from:

  * `AlgebraicGeometry.RingedToposHom.isLocallyRinged_iff_of_ringedToposEquivalence` of
    `StacksFrontier/CategoryTheory/Sites/Modules/LocallyRingedTopoi/InverseImage.lean`, registered on
    Stacks 04H7 (2): for a `RingedToposHom` whose inverse image is an equivalence and whose
    structure map is an isomorphism, `IsLocallyRinged` of the two ends agree.  So the
    `IsLocallyRinged` half of the transport is a general theorem, not a new proof.
  * `AlgebraicGeometry.RingedToposHom.inverse` and its `fSharp`/`toToposHom` computations
    (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposEquivalence.lean`), which build the
    morphism of ringed topoi in the other direction.
  * `AlgebraicGeometry.RingedToposHom.TwoIso.ofInverseImageIso`
    (`StacksFrontier/CategoryTheory/Sites/Modules/Localization/RingedToposRelocalizedMorphism.lean`),
    which makes a `TwoIso` out of an isomorphism of inverse images compatible with the structure
    maps — the shape the comparison here arrives in.
  * A change-of-big-site equivalence *of ringed topoi* already exists in another instance:
    `AlgebraicGeometry.fppf_affineToBigRingedToposEquivalence` and its four siblings
    (`StacksFrontier/AlgebraicGeometry/Topologies/BigSites/AffineRingedToposEquivalence.lean`,
    Stacks 0GZU), for the affine-to-big comparison.  The pattern is the same, but **the
    declaration itself cannot be instantiated here.**
    `AlgebraicGeometry.affineToBigRingedToposHom` takes the structure sheaf's sections in a
    universe dominating both sites' *object* universes — its topos is
    `Sheaf _ (Type max u₁ v₁ u₂ v₂ w)` — while both sites here have objects in `Type (u + 1)` and
    sections in `Type u`, so the hypothesis reads `max (u + 1) w = u`.  What replaces that size
    hypothesis is that the functor of sites is an **equivalence**: restriction along it is then an
    equivalence of sheaf categories for any category of values and with no size condition, which
    is `CategoryTheory.Equivalence.sheafCongr`, and its `inverse` is
    `CategoryTheory.Functor.sheafPushforwardContinuous` on the nose — so the structure map can
    still be the adjunct of `Stacks.Sheaves.ToposPullback.restrictionCommRingIso`, exactly as in
    the affine-to-big construction.  `Equivalence.sheafCongr` wants
    `e.inverse.IsDenseSubsite K J`, which follows from
    `Space.representedSmallEtaleEquivalence_topology` through
    `Space.inducedTopology_symm_of_equivalence` and Mathlib's unconditional
    `e.functor.IsDenseSubsite J (e.inverse.inducedTopology J)`.

  The instantiation is not free: the two sides' structure sheaves are compared by
  `representedCommRingStructureIso` rather than being definitionally equal, so the hypothesis
  `IsIso f.fSharp` of 04H7 (2) has to be produced from that comparison.  Note also that 04H7 (2)
  is about `AlgebraicGeometry.RingedTopos.IsLocallyRinged`, the condition on a ringed topos, and
  what the bridge has to transport is `AlgebraicGeometry.RingedToposHom.IsLocallyRinged`, the
  cartesian-units-square condition of Stacks 04HA on a *morphism*; those are different predicates
  and no declaration transports the second along an equivalence either.

  The route that reduces the morphism-level transport to one new fact: write the conjugate of
  `(g, g^♯)` as the composite of the equivalence's ringed-topos morphism, `(g, g^♯)`, and the
  equivalence's inverse, and use Stacks 04IG —
  `AlgebraicGeometry.RingedToposHom.isLocallyRinged_comp`, stated at three
  independent pairs of site and section universes — so that the only new input is that a
  morphism of ringed topoi whose structure map is an isomorphism is itself locally ringed in the
  sense of 04HA.

  **That one fact is available.**  It is
  `AlgebraicGeometry.RingedToposHom.isLocallyRinged_of_isIso_fSharpInverseImage` of
  `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleRingedToposIsoLocallyRinged.lean`, proved
  at two independent pairs of site universes and one common section universe.
  Its inputs are in the same file: `AlgebraicGeometry.RingedTopos.unitsMapOf_id`,
  `unitsMapOf_comp`, `isIso_unitsMapOf` and `isPullback_unitsSquare_of_isIso`.

  **Use that one, not the corollary, and do not build the backward direction as a formal
  inverse.**  The corollary
  `AlgebraicGeometry.RingedToposHom.isLocallyRinged_of_isEquivalence_of_isIso_fSharp` asks for
  `IsIso f.fSharp`, the structure map in *direct-image* form, and the identification here supplies
  only `IsIso f.fSharpInverseImage`; nothing in the tree converts the second into the first (the
  known implication runs the other way, `isIso_fSharpInverseImage`).  For the same reason
  `AlgebraicGeometry.RingedToposHom.inverse` is unusable, since it too requires `IsIso f.fSharp`.
  The backward direction is therefore built directly, out of
  `Space.representedSmallEtaleEquivalence.inverse` and
  `Space.representedCommRingStructureInverseIso`, so that both directions have an invertible
  inverse-image structure map and `isLocallyRinged_of_isIso_fSharpInverseImage` applies to each.
  That is what `Spaces/RepresentedSmallEtaleRingedToposEquivalence.lean` does.

  That fact does **not**
  have to be proved from `AlgebraicGeometry.RingedTopos.ReflectsUnitsObj` and
  `isPullback_unitsSquare_of_family`: a conservative family of points is the route for a structure
  map that is *not* invertible.  Here the map of units subsheaves is functorial, hence invertible
  when the structure map is, and a commutative square whose two horizontal arrows are isomorphisms
  is cartesian.  The same argument, for the canonical morphism, whose structure map is the
  identity, is `AlgebraicGeometry.inverseImageRingedToposHom_isLocallyRinged`, registered on
  Stacks 04KR.

  One practical note on elaboration.  The statement of the square these
  proofs go through mentions
  `RingedTopos.unitsιOf ((inverseImageCommRingFunctor f.toToposHom).obj Y.O)`, and writing that
  spelling out in a *type ascription* in a module downstream of
  `StacksFrontier/CategoryTheory/Sites/Modules/LocallyRingedSites/ToposHomUnitsSquare.lean` exhausts
  the 200,000-heartbeat budget in `isDefEq`, with `RingedTopos.ofStructureSheaf` unfolded over five
  million times; inside that file the same expression is cheap.  Let the type be inferred from
  `f.fSharpInverseImage`, as `isPullback_unitsSquare_of_isIso` does, instead of ascribing it.
* **Not an issue.** Nothing about universes: the two sides already agree.
  `smallEtaleRingedSite` is a `RingedSite.{u + 1, u, u}` (`SmallEtaleRingedSite.lean:127`), so
  `AlgebraicGeometry.RingedSite.toRingedTopos` of it is a `RingedTopos.{u, u + 1, u}`, which is
  the universe shape of `AlgebraicGeometry.Space.smallEtaleRingedTopos`.  This is
  why the bridge is a question about vocabulary and not about raising a universe.

An alternative to the transport is to restate `Clause04I7` over a
`BigFppfSite` directly and prove link 1 there; the scheme-level development of
`RecoveringMorphisms/` would then have to be reread at that site, which is the larger job of the
two.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 04I7](https://stacks.math.columbia.edu/tag/04I7)
* [Stacks Project, Tag 04LW](https://stacks.math.columbia.edu/tag/04LW), the uniqueness, which
  is what makes the clauses here existence-only.
* [Stacks Project, Tag 04HV](https://stacks.math.columbia.edu/tag/04HV)
* [Stacks Project, Tag 04IJ](https://stacks.math.columbia.edu/tag/04IJ)
* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {B : BigEtaleSite.{u}}

/-- **The existence clause of Stacks 04I7 gives the theorem's full statement.**  Granted
`AlgebraicGeometry.Clause04I7`, there is a *unique* morphism of schemes `f : X ⟶ Y` whose
morphism of small étale ringed topoi is 2-isomorphic to a given locally ringed `(g, g^♯)`.

The uniqueness is added for free by [Stacks Project, Tag 04LW]
(`AlgebraicGeometry.eq_of_twoIso_smallEtaleRingedToposHom`), which assumes
neither affineness nor locality.  So a proof of `Clause04I7` is a proof of Stacks 04I7, with no
restatement in between. -/
theorem existsUnique_of_clause04I7 (h : Clause04I7 B) (X Y : B.Scheme)
    (g : RingedToposHom
      (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
    (hg : g.IsLocallyRinged) :
    ∃! f : X ⟶ Y, Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g
      (smallEtaleRingedToposHom B f)) := by
  exact existsUnique_of_exists_of_unique (h X Y g hg) fun a b ha hb =>
    eq_of_twoIso_smallEtaleRingedToposHom B g a b ha.some hb.some

/-- **The existence clause of Stacks 04I6 gives that lemma's full statement**, by the same
uniqueness as `AlgebraicGeometry.existsUnique_of_clause04I7`. -/
theorem existsUnique_affine_of_clause04I6 (h : Clause04I6 B) (X Y : B.Scheme)
    (hX : IsAffine X.obj) (hY : IsAffine Y.obj)
    (g : RingedToposHom
      (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
    (hg : g.IsLocallyRinged) :
    ∃! f : X ⟶ Y, Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g
      (smallEtaleRingedToposHom B f)) := by
  exact existsUnique_of_exists_of_unique (h X Y hX hY g hg) fun a b ha hb =>
    eq_of_twoIso_smallEtaleRingedToposHom B g a b ha.some hb.some

/-- **Stacks 04I6's existence clause holds.**  It is
`AlgebraicGeometry.exists_schemeHom_twoIso_of_isLocallyRinged`, which is proved outright, so no
statement needs to carry `AlgebraicGeometry.Clause04I6` as a hypothesis.

That theorem is strictly more general than the clause: it asks only that the *target* `Y`
be affine.  That is recorded separately as
`AlgebraicGeometry.clause04I6_affineTarget`, which is the input the remaining link of the chain
actually consumes — see the module documentation. -/
theorem clause04I6 (B : BigEtaleSite.{u}) : Clause04I6 B := by
  intro X Y _ hY g hg
  have : IsAffine Y.obj := hY
  exact exists_schemeHom_twoIso_of_isLocallyRinged B g hg

/-- **Stacks 04I6's existence clause with only the target assumed affine.**  This is the
generality in which `AlgebraicGeometry.exists_schemeHom_twoIso_of_isLocallyRinged` is proved, and
it is what the passage from Stacks 04I6 to Stacks 04I7 has left to do: the affineness of the
*source* is already gone, so the Zariski gluing described in the module documentation is needed
only over the target.

Compare `AlgebraicGeometry.clause04I6`, which is this with the redundant hypothesis on `X` put
back so as to match the tag's own statement. -/
theorem clause04I6_affineTarget (B : BigEtaleSite.{u}) (X Y : B.Scheme) (hY : IsAffine Y.obj)
    (g : RingedToposHom
      (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
    (hg : g.IsLocallyRinged) :
    ∃ f : X ⟶ Y, Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g
      (smallEtaleRingedToposHom B f)) := by
  have : IsAffine Y.obj := hY
  exact exists_schemeHom_twoIso_of_isLocallyRinged B g hg

end AlgebraicGeometry

end
