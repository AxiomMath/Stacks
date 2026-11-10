module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.ClassifiesDescent.Descent
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.ClassifiesDescent.SectionChain
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.ClassifiesDescent.ExistsClassifies
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.ClassifiesDescent.Uniqueness

/-!
# The classifying isomorphism of an invertible quotient descends from an open cover

Let `E` be a sheaf of modules on a scheme `X` and let `p : E ⟶ M` and `q : E ⟶ N` be two
morphisms out of it with `p` an epimorphism. **If the inverse images of `M` and `N` along the
members of an open cover of `X` are isomorphic by isomorphisms carrying the inverse image of `p`
to the inverse image of `q`, then `M` and `N` are isomorphic by an isomorphism carrying `p` to
`q`.**

The hypothesis is *not* asked for on pairwise intersections. An isomorphism `α` with
`p ≫ α = q` is unique, because `p` is an epimorphism and epimorphisms cancel on the right; the
inverse image of an epimorphism along a morphism of schemes is again an epimorphism, the inverse
image functor being a left adjoint, so the same cancellation holds over every open and the local
isomorphisms agree on every open contained in two members of the cover whether one asks them to
or not.

## Why this file exists

On the route from the universal property of absolute `Proj` to [Stacks, Tag 0B3V]'s bijection
between the sections of `π : 𝐏(ℰ) ⟶ X` and the invertible quotients of `ℰ`, step 4 is the
descent of the local
classifying data to `X`. The *morphism* half of that descent is proved —
`Stacks.RelativeProj.globalSection` glues the local sections of
`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/GlobalSection.lean` — and what remains is the
descent of the **classifying isomorphism**: a glued section is a section, and nothing above said
that the quotient it pulls back is the given one.

This file performs that descent, and the point is that it costs nothing beyond the epimorphism
cancellation: the quotient maps make the comparison isomorphism unique, so a family of local
comparisons is automatically a descent datum. In particular no quasi-coherence, no affineness of
the members of the cover and no invertibility of `M` or `N` is used.

## Main results

* `Stacks.Divisors.exists_iso_of_pullback_cover`: **the descent**, for two morphisms out of a
  sheaf of modules with the first an epimorphism.
* `Stacks.Divisors.InvertibleQuotient.isEquivalent_of_pullback_cover`: the same read on two
  invertible quotients of `ℰ`, concluding that they are equivalent — the relation
  [Stacks, Tag 0B3V]'s bijection is taken modulo.
* `Stacks.RelativeProj.TautologicalDatum.classifies_of_pullback_cover`: the same read as the
  classifying relation of a tautological datum, so that `Classifies` for a section of `π` is a
  local question on the base.
* `Stacks.RelativeProj.TautologicalDatum.exists_classifies_of_pullback_cover`: the field
  `Stacks.RelativeProj.TautologicalDatum.IsUniversal.exists_classifies` reduced to the local
  classifying data, the section being produced by
  `Stacks.RelativeProj.globalSection`. **This is the shape the remaining work on Tag 0B3V's
  bijection is owed in** — see `Not done here`.
* `Stacks.RelativeProj.globalSectionPullbackTwistIsoOnCover` and
  `…RelativeProj.exists_globalSectionPullbackTwistIsoOnCover`: **the object half of that local
  datum, over every member of `Stacks.RelativeProj.trivCover`, with no input from the consumer.**
  The inverse image along the member of the module the glued section pulls back from
  `𝒪_{𝐏(ℰ)}(1)` is identified with the
  `Stacks.AlgebraicGeometry.MorphismsIntoProj.pullbackTwist` on which
  `Stacks.AlgebraicGeometry.ProjTwistPinnedChart.bijective_smul_pullbackDegreeSection` and the
  pinning match `Stacks.RelativeProj.resT_pullbackDegreeSection_localChartMap` live. What this
  does *not* give is that the comparison carries the pulled-back tautological map to `q`.
* `Stacks.RelativeProj.TautologicalDatum.pullbackQuotientMap_val_app`: **the pulled-back
  tautological map on sections**, past its three
  `AlgebraicGeometry.Scheme.Modules.pullback` comparisons. At `m : Γ(ℰ, W)` the value is the
  pullback along `σ` of the value of the datum's universal surjection at the pullback of `m`
  along `π`, and the collapse `σ ⁻¹ᵁ (π ⁻¹ᵁ W) = W` — which is *not* definitional — is
  `Stacks.RelativeProj.preimage_preimage_of_comp_eq_id`.
* `Stacks.RelativeProj.tautologicalDatumUniv_val_app` and
  `…RelativeProj.pullbackQuotientMap_tautologicalDatum_val_app`: the same for the repository's
  own tautological datum, past all **six** comparisons, ending at
  `Stacks.ProjectiveBundleSplitting.tautologicalMap` — so the `bundlePresentationIso` transport
  between the two bundle substrates is discharged on sections.
* `Stacks.RelativeProj.pullbackSection_pullbackId_inv`,
  `…RelativeProj.pullbackSection_pullbackCongrComp_inv_map` and
  `…RelativeProj.pullbackSection_sectionComparisons_map`: the three statements above with every
  trace of the projective bundle removed — an arbitrary morphism of schemes, an arbitrary section
  of it, and an arbitrary morphism out of the inverse image. The specialisations are instances of
  these with nothing to re-associate.
* `Stacks.RelativeProj.pullbackSection_compCongr_map`,
  `…RelativeProj.pullbackComp_inv_pullbackSection`,
  `…RelativeProj.pullbackSection_top_eq_resT` and
  `…RelativeProj.pullbackDegreeSection_eq_pullbackSection`: **the generic collapses the object
  comparison is built out of, in the `hom` direction.** The composite
  `pullbackComp`-then-`pullbackCongr` of a factorisation `c ≫ σ = τ` occurs twice in
  `globalSectionPullbackTwistIsoOnCover` — once at `(V.ι, globalSection q, localSection)` and
  once inside `Stacks.RelativeProj.localSectionTwistIso` at
  `(localSection, bundlePresentationIso.inv, localChartMap ≫ chart)` — and
  `pullbackSection_compCongr_map` is that pair at opaque morphisms;
  `pullbackComp_inv_pullbackSection` is the splitting of a single pullback along a composite,
  which is what reaches `Stacks.ProjectiveBundle.chartTwistIso` under two pullbacks; and the last
  two are the dictionary between
  `AlgebraicGeometry.Scheme.Modules.pullbackSection` over an open and the
  `Stacks.ProjectiveFromSections.resT`-of-a-global-section spelling that the pinning match and
  `Stacks.AlgebraicGeometry.ProjTwistPinnedChart.pinnedFrameIso_inv_smul_resT` use.
* `Stacks.RelativeProj.exists_classifies_tautologicalDatum`: **the first field of
  `Stacks.RelativeProj.TautologicalDatum.IsUniversal` for the repository's own tautological
  datum, discharged** — every invertible quotient of `ℰ` is classified by a section of
  `π : 𝐏(ℰ) ⟶ X`, namely `Stacks.RelativeProj.globalSection` of the quotient map.
  `…RelativeProj.exists_classifies_globalSection` is the same for one quotient map, and
  `…RelativeProj.exists_classifyingIso_onCover` is the local classifying datum over a member of
  `Stacks.RelativeProj.trivCover` with nothing left for the consumer.
* `Stacks.RelativeProj.pullbackQuotientMap_comp_pinnedFrameIso_inv`: **the compatibility** — the
  object comparison over a member of the cover carries the inverse image of the pulled-back
  tautological map to the inverse image of `q`. This is
  `Stacks.Chow.GenuineChern.pullback_hom_ext_of_isAffineOpen` at `V.ι` applied to
  `…RelativeProj.pullbackQuotientMap_comp_pinnedFrameIso_inv_unitSection` and
  `…RelativeProj.pullback_map_comp_pullbackIsoUnitOfOverIsoUnit_hom_unitSection`, which land on
  one and the same trivialised quotient — and it is why the members of `trivCover` must be
  affine.
* `Stacks.RelativeProj.globalSectionPullbackTwistIsoOnCover_hom_pullbackSection` and the chain
  behind it (`…RelativeProj.chartFactorisationTwistIso_hom_pullbackSection`,
  `…RelativeProj.chartFactorisationPullbackTwistIso_hom_pullbackSection`,
  `…RelativeProj.restrictChartFactorisationPullbackTwistIso_hom_pullbackSection`,
  `…RelativeProj.pullback_map_pullbackQuotientMap_unitSection`,
  `…RelativeProj.pinnedFrameIso_inv_resT_pullbackDegreeSection`): **the object comparison
  evaluated on the section the pulled-back tautological map produces**, landing on the section
  the pinning match `Stacks.RelativeProj.resT_pullbackDegreeSection_localChartMap` is stated on,
  and then the pinned frame inverted on it. **The whole chain is stated at an arbitrary chart
  factorisation and at an arbitrary section `σ` of `π`**; the glued section is the instance of it
  at `Stacks.RelativeProj.localChartMap`.
* `Stacks.RelativeProj.sectionChartMap` and `…RelativeProj.sectionChartMap_comp_chart`: **the
  chart factorisation of an arbitrary section of `π` over an affine open**, which is the `h`
  the injectivity clause of [Stacks, Tag 0B3V] feeds the chain, produced from
  `Stacks.AlgebraicGeometry.RelativeProj.chartHomEquivOver` and nothing else.
* `Stacks.RelativeProj.classifyingTrivialisationOfSection` and
  `…RelativeProj.classifyingTrivialisationOfSection_hom_pullbackSection`: **the degree-one
  dictionary at an arbitrary classified section.** Given a section `σ` of `π`, a witness `α` that
  `σ` classifies `q : ℰ ↠ ℒ`, and a trivialisation `e` of `ℒ` over an affine open `V`, the
  twisting sheaf of `Γ(V, Sym ℰ)` pulled back along `sectionChartMap` is trivialised in such a
  way that the pulled-back degree-one section of `x : Γ(ℰ, V)` is `e (q x)`. **No standard-open
  hypothesis, no frame and no choice of `m₀` occurs**, which is what makes it the input of the
  standard-open hypothesis rather than a consequence of it.
* `Stacks.RelativeProj.preimage_basicOpen_sectionChartMap_eq_top`: **clause (a) of
  [Stacks, Tag 0B3V] at an arbitrary section of `π`** — the chart factorisation `sectionChartMap`
  of an arbitrary section lands wholly inside the standard open of the degree-one element of a
  section of `ℰ` whose trivialised quotient is the unit. This is item 3 of the degree-one route
  to `…IsUniversal.eq_of_classifies`, and the only remaining input of that route is the pure
  algebra of item 4 — see `Not done here`. For the *glued* section the same statement is
  `Stacks.RelativeProj.preimage_basicOpen_localDegreeOne_eq_top` and costs nothing; for an
  arbitrary one the standard open has to be reached through the section, which is what the next
  three results do.
* `Stacks.RelativeProj.classifyingTrivialisationOfSection_hom_pullbackSection_top`: item 2
  transported from `V.ι ⁻¹ᵁ V` to `⊤`. `AlgebraicGeometry.Scheme.Opens.ι_preimage_self` is an
  equality of opens and **not** a definitional one, so this is a genuine restriction map, carried
  across the trivialisation by `Stacks.Chow.GenuineChern.app_resTop` and performed on the source
  by `Stacks.AlgebraicGeometry.ProjChartCocycleMatch.resTop_pullbackSectionHom`.
* `Stacks.RelativeProj.nonvanishingOpen_eq_top_of_isoUnit` and
  `…RelativeProj.nonvanishingOpen_pullbackSection_eq_top`: **the nonvanishing open of a section
  that an isomorphism carries to a unit is everything**, the second with the inverse image along
  an *equal* morphism interposed, both at opaque data.
  `…RelativeProj.nonvanishingLocus_unit_eq_basicOpen` is the `Γ(M, ⊤)` spelling of
  `Stacks.SheafOfModules.nonvanishingLocus_unit_eq_basicOpen` that they are read through, and
  `…RelativeProj.pullbackCongrApp_trans_hom` the morphism-level `rfl` the second is split on.
* `Stacks.RelativeProj.pullbackSection_fourComparisons_map`,
  `…RelativeProj.pullbackSection_compCongrTrans_map`,
  `…RelativeProj.comp_val_app_apply_eq` and `…RelativeProj.resTop_preimageSelfTopRingHom`: the
  generic steps that chain is assembled from, at opaque morphisms.
* `Stacks.RelativeProj.pullbackIsoUnitOfOverIsoUnit_hom_pullback_map_unitSection`: **the
  trivialisation of the inverse image of `ℒ` carries the inverse image of `q` to
  `Stacks.RelativeProj.trivializedQuotientHom`.** This is the `ℒ`-side half of the local
  classifying datum, and it is the statement that puts both sides of the compatibility into one
  vocabulary: the object comparison on the `ℒ` side is
  `Stacks.AlgebraicGeometry.ProjInvertibleLocus.pullbackIsoUnitOfOverIsoUnit`, the bridge from
  the restricted-site packaging `(-).over V` that every trivialisation in this repository is
  produced in to `AlgebraicGeometry.Scheme.Modules.pullback V.ι`, and the morphism it lands on is
  the `κ` that `Stacks.RelativeProj.resT_pullbackDegreeSection_localChartMap` is stated in terms
  of. Nothing is assumed of `V` beyond the trivialisation; invertibility of `ℒ` is not used.

## Implementation notes

**The gluing is `Stacks.AlgebraicGeometry.ModuleHomGlue.glueIsoOfCover`**, which asks exactly for
a family of isomorphisms of the inverse images agreeing after restriction to the opens contained
in two members, and nothing else; `…ModuleHomGlue.pullbackRestrictLocal_pullback_map` and
`…ModuleHomGlue.pullbackRestrictLocal_comp` are what carry the equation `p ≫ α = q` down to a
smaller open, and `CategoryTheory.cancel_epi` is what turns two solutions of it into one.

**The choice of local isomorphisms is made inside the proof.** The hypothesis is an existence
statement, so the conclusion does not depend on which local comparisons are taken — they are
unique anyway, for the same reason their agreement is automatic.

**The section-level comparisons are cancelled forwards and at opaque schemes.** Mathlib states
`pullbackSection_congr`, `pullbackSection_comp` and `pullbackSection_naturality` with the `hom`
of each comparison, whereas `pullbackQuotientMap` composes the `inv`s; each is therefore turned
around rather than inverted by injectivity. They are also proved with the morphisms of schemes as
*variables*: `Stacks.RelativeProj.projectiveBundle` and
`…RelativeProj.projectiveBundleToBase` are reducible abbreviations of the `Situation` presentation,
so leaving them in the statement lets `isDefEq` unfold the whole chart layer and the 200000
heartbeats are gone. The specialisations below are then `exact`s with no re-association, because
`pullbackQuotientMap` and `tautologicalDatumUniv` are *literally* in the shape of the generic
statements.

**Not deduplicated with `Stacks.ProjectiveBundleConormal.pullbackSection_collapse`.** That
declaration is the three-comparison collapse on sections for `(bundle ℰ).toBase`, the projection
of the `SheafGradedAlgebra` presentation, and its proof uses nothing of that morphism;
`pullbackSection_sectionComparisons_map` below is the same content at an arbitrary morphism and
with the trailing `(pullback σ).map t` included, which is what makes the specialisations
`exact`s. The clean merge is to restate `pullbackSection_collapse` as an instance of the general
one; that touches `StacksFrontier/AlgebraicGeometry/ProjectiveBundleConormal/` and its two consumers
and is not done here.

**Two modules under `Chow/GenuineChern/` are imported.**
`…GenuineChern.PullbackExt` carries `pullback_hom_ext_of_isAffineOpen`, the extensionality
principle the compatibility is going to be checked by, and `…GenuineChern.TwistPullback` carries
`restrictFunctorIsoPullback_inv_unitSection`, which evaluates the comparison of the two
restriction functors on a pulled-back section. Neither is restated here: there are already two
copies of the latter in the repository (`…GenuineChern.TwistPullback` and
`…GenuineChern.SubbundleZeroScheme`), and a third would be a duplicate. Both add few modules to this
file's import closure, whereas
`…GenuineChern.SubbundleZeroScheme`, which holds the same lemma, would add over two thousand and
is not used.

**The chain of sections is spelled out in small declarations on purpose, and the reason is the
heartbeat budget.** The comparisons this file composes live under
`Stacks.RelativeProj.projectiveBundle`, `…RelativeProj.projectiveBundleToBase` and
`…RelativeProj.tautologicalDatumTwist`, all reducible abbreviations of the bundle's
presentations, and `isDefEq` unfolds the chart layer through them. Three habits make
the difference between a few seconds and exhausting the 200000 heartbeats:

* **unfold a definition at the level of morphisms, never of sections.**
  `chartFactorisationTwistIso_hom`, `chartFactorisationPullbackTwistIso_hom`,
  `restrictChartFactorisationTwistIso_hom`,
  `restrictChartFactorisationPullbackTwistIso_hom` and
  `globalSectionPullbackTwistIsoOnCover_hom` are `rfl` and free; the *same* identities read on a
  section do not elaborate at all, because `isDefEq` then whnfs both sides as elements of a
  `ModuleCat` carrier and unfolds the pullback construction itself. The crossing to sections is
  `Stacks.AlgebraicGeometry.ChartCocycleRigidity.app_val_congr`, which adds **no** module to the
  import closure.
* **let the goal drive the unification.** A substitution written as a `congrArg` over an
  explicitly spelled-out composite is matched against the goal by `isDefEq` on two closed terms;
  stated as `comp_val_app_apply_eq`, with the two morphisms as variables, the same step is a
  metavariable assignment. The three concrete chain lemmas were each over budget in the first
  form and instant in the second.
* **one definitional crossing per declaration.** `chartFactorisationTwistIso_hom` and
  `chartFactorisationPullbackTwistIso_hom` are separate `rfl`s because the two together exceed one
  budget; `chartFactorisationPullbackTwistIso_hom_val_app` stops at the composite rather than at
  the nested application for the same reason, the consumer's `Eq.trans` crossing that step for
  free. `globalSectionPullbackTwistIsoOnCover_hom` exists for exactly this reason too:
  specialising `restrictChartFactorisationPullbackTwistIso_hom_pullbackSection` to the glued
  section *and* crossing the definition of `globalSectionPullbackTwistIsoOnCover` in one
  declaration exceeds the budget, and separately each is instant.

No heartbeat limit is raised anywhere below, and none needs to be.

**One more module is imported.**
`…ProjectiveBundleConormal.PullbackTautologicalSection` carries
`pullbackSection_preimage_self` — pulling a section back to the whole preimage of its open is the
adjunction unit — which is what matches the output of
`pullbackQuotientMap_tautologicalDatum_val_app` with the input of
`Stacks.ProjectiveBundleConormal.projectiveBundle_chartTwistIso_hom_pullbackSection`. Restating the
lemma here instead would be a duplicate. `…ChartCocycleRigidity.DegreeSection` is imported for
`app_val_congr`.

**Five more modules are imported for item 3.**
`…Constructions.MorphismToProjUniversal` carries `preimage_basicOpen_eq_nonvanishingOpen` — the
preimage of a standard open under a morphism through `U_d` is the nonvanishing open of the
pulled-back degree-`d` section — and, through `…Constructions.ProjChartCocycleMatch`,
`resTop_pullbackSectionHom`; `…Constructions.ProjDegreeOneRepresents` carries
`degreeOpen_one_eq_top` and `factorThroughDegreeOpenOne`; `…SymGenDegreeOne.Basic` carries
`Stacks.SymGraded.adjoin_grading_one_eq_top`; and `…AmpleBridge.Basic` together with
`…Ample.StructureSheaf` carry the two halves of `nonvanishingLocus_unit_eq_basicOpen`.

**Two more modules are imported for items 4 and B.**
`…RelativeProjBridge.DegreeOneProductsGlue` carries the degree-one extensionality of ring maps out
of the chart ring, and `…TwistPullbackRatio.ChartHom` carries
`pullbackSection_degreeSection_eq_smul` and `pullbackSection_res`.

**No `@[stacks 0B3V]` attribute is attached in this file.** The tag is registered once, on
`Stacks.RelativeProj.projectiveBundle_sections_classification` in
`StacksFrontier/AlgebraicGeometry/ProjectiveBundleConormal/SectionsClause.lean`, stated on
`Stacks.RelativeProj.projectiveBundle`; its bijection clause is `projectiveBundleSectionsEquiv`,
the unconditional bijection between the sections of `π : 𝐏(ℰ) ⟶ X` and the invertible quotients
of `ℰ` up to isomorphism. It is unconditional because `isUniversal_tautologicalDatum` below is an
instance: both fields of `Stacks.RelativeProj.TautologicalDatum.IsUniversal` are proved at the
bundle's own tautological datum — `exists_classifies_tautologicalDatum` and
`eq_of_classifies_tautologicalDatum`. No attribute is attached to either field, to any of the
four items of the route, or to anything carrying `[IsUniversal]` as a hypothesis.

## The second field

**`Stacks.RelativeProj.TautologicalDatum.IsUniversal.eq_of_classifies` is
`eq_of_classifies_tautologicalDatum` below**, and it is *not* a consequence of the first half of
this file: everything in that half is about the glued section
`Stacks.RelativeProj.globalSection q`, which is built from the quotient, whereas
`eq_of_classifies` quantifies over sections nothing is known about. It needs the whole of the
degree-one route recorded below.

The route to Tag 0B3V's bijection treats it as
its step 7. The mechanism is
`Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.eq_of_chartHomEquiv_eq` (two morphisms into the
chart at `r` inducing the same `Away`-homomorphism are equal) together with
`Stacks.AlgebraicGeometry.RelativeProj.comp_chart_injective` (two morphisms into the relative
`Proj` over the same morphism to an affine open agree as soon as their chart components do).
**What is needed is their input**: for an *arbitrary* section `σ` of `π` and a trivialisation of
the quotient `σ` pulls back over a member `V` of a cover, that `σ` restricted to `V` induces the
dehomogenisation `Stacks.RelativeProj.localDehomogenize` of that quotient — equivalently that
`V.ι ≫ σ = Stacks.RelativeProj.localSection V …`. For the glued section that holds by
construction (`Stacks.RelativeProj.ι_comp_globalSection_eq_localSection`); for an arbitrary one
nothing above says anything about it.

**That input does not require a
`Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections` of `Γ(V, Sym ℰ)` attached to the
quotient — step 3 of the route record — and the sheaf-level part of that object is available
in any case.**

* The *sheaf-level* half of step 3 is proved. `Stacks.RelativeProj.quotientGradedMap` of
  `StacksFrontier/AlgebraicGeometry/ProjectiveBundle/QuotientGradedMap.lean` is the graded map
  `ψ : Sym(ℰ) ⟶ ⨁_{n ∈ ℤ} ℒ^{⊗ n}` attached to an arbitrary `q : ℰ ⟶ ℒ` into an invertible
  module, with the degree-one normalisation
  `…RelativeProj.symmetricAlgebraGen_comp_quotientGradedMap` and the uniqueness
  `…RelativeProj.quotientGradedMap_unique`, and with no hypothesis at all;
  `Symⁿ ℒ ≅ ℒ^{⊗ n}` for an invertible `ℒ` is formalized as
  `Stacks.SheafOfModules.symmetricPowerIsoTensorPowerOfIsInvertible`. What step 3 still needs is
  only the *section-level* reading of `ψ` over an affine open as a `VeroneseSections`. Nothing
  in the repository consumes `quotientGradedMap`.
* The input above needs no `VeroneseSections` at all, because the mechanism it feeds compares
  `Away`-homomorphisms and the dictionary from pulled-back **degree-one** sections to the value
  of `…ProjF1DegreeOneChart.chartHomEquiv` is proved at an *arbitrary* morphism:
  `Stacks.TwistPullbackRatio.pullbackSection_degreeSection_eq_smul` of
  `StacksFrontier/AlgebraicGeometry/TwistPullbackRatio/ChartHom.lean` says that for `g` into
  `Proj 𝒮` with `g ⁻¹ᵁ D₊(t) = ⊤` and `p`, `t` of degree one the pullback of the degree-one
  section of `p` is `chartHomEquiv ⟨g, hg⟩ (p/t)` times the pullback of that of `t`. The
  pinning of `StacksFrontier/AlgebraicGeometry/ProjTwistPinnedChart/Basic.lean` —
  `…ProjTwistPinnedChart.bijective_smul_pullbackDegreeSection` and
  `…ProjTwistPinnedChart.pinnedFrameIso` — is stated at that same arbitrary `g`, not only at
  `fromOfIsUnit`. So no tensor power, no `Symⁿ` and no [Stacks, Tag 01NA] occurs on this route,
  and the graded upgrade of
  `Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.thetaNat` that the degree-`n` clauses
  of [Stacks, Tag 01NA]'s `Classifies` would need — recorded as blocked where it lives — is not
  reached.

The degree-one route needs four statements and no object, **all four proved here**, and the
order matters: 3 comes *before* the `chartHomEquiv`-valued form of 2, because `chartHomEquiv` is
only defined on morphisms that land in the standard open.

1. **The twist comparison at an arbitrary chart factorisation.**
   `Stacks.RelativeProj.chartFactorisationTwistIso` and
   `…RelativeProj.chartFactorisationPullbackTwistIso` of
   `StacksFrontier/AlgebraicGeometry/ProjectiveBundle/LocalChartPinning.lean` are the comparison at
   an arbitrary pair `(g, h)` with `g ≫ bundlePresentationIso.inv = h ≫ chart V hV`, with
   `…RelativeProj.localSectionTwistIso` and `…RelativeProj.localSectionPullbackTwistIso` their
   instances at `Stacks.RelativeProj.localChartMap`; the whole section-level chain above is
   stated there, and `…RelativeProj.restrictChartFactorisationTwistIso` and
   `…RelativeProj.restrictChartFactorisationPullbackTwistIso` add the restriction `V.ι ≫ σ = τ`
   in front. The `h` of `V.ι ≫ σ` is `Stacks.RelativeProj.sectionChartMap`, whose factorisation
   is `…RelativeProj.sectionChartMap_comp_chart`, built from
   `Stacks.AlgebraicGeometry.RelativeProj.chartHomEquivOver` of
   `StacksFrontier/AlgebraicGeometry/RelativeProj/MappingInSheafGraded.lean`.
2. **The degree-one value, in its `hg`-free form.**
   `Stacks.RelativeProj.classifyingTrivialisationOfSection_hom_pullbackSection` says that for an
   arbitrary section `σ` of `π` classifying `q : ℰ ↠ ℒ` by `α`, and a trivialisation `e` of `ℒ`
   over an affine open `V`, the explicit trivialisation
   `…RelativeProj.classifyingTrivialisationOfSection` of the twisting sheaf of `Γ(V, Sym ℰ)`
   pulled back along `sectionChartMap` carries the pulled-back degree-one section of `x` to
   `e (q x)`, over the open `V.ι ⁻¹ᵁ V`. Degree one only: `α` is never raised to a tensor power.
   **The `chartHomEquiv`-valued form** — `chartHomEquiv … h (localDegreeOne m / localDegreeOne
   m₀) = e (q m)` — is `chartHomEquiv_sectionChartMap_localDegreeOne` below: this together with
   item 3 and `Stacks.TwistPullbackRatio.pullbackSection_degreeSection_eq_smul`, whose scalar is
   identified with the value above by `eq_of_smul_frame_app`. No pinning isomorphism and no
   injectivity of multiplication by a frame is needed: the frame enters only through the value `1`
   that item 2 gives it, so
   `Stacks.AlgebraicGeometry.ProjTwistPinnedChart.bijective_smul_pullbackDegreeSection` does not
   occur.
3. **Clause (a) for `σ`.**
   `Stacks.RelativeProj.preimage_basicOpen_sectionChartMap_eq_top` is
   `sectionChartMap V σ hσ hV ⁻¹ᵁ D₊((localDegreeOne V m₀).1) = ⊤` for an `m₀` with
   `e (q m₀) = 1` — which exists over an affine open by
   `Stacks.RelativeProj.exists_app_trivializedQuotientHom_eq_one` and
   `…RelativeProj.surjective_app_of_isAffineOpen_of_epi`. By item 2 the pulled-back degree-one
   section of such an `m₀` is carried by an *isomorphism* of `𝒪_V`-modules to `1`, hence vanishes
   nowhere; the standard open is then reached by
   `Stacks.AlgebraicGeometry.MorphismToProjUniversal.preimage_basicOpen_eq_nonvanishingOpen`,
   which is stated for a morphism *through* `U_1` and is therefore fed
   `Stacks.AlgebraicGeometry.ProjDegreeOneRepresents.factorThroughDegreeOpenOne` at
   `…ProjDegreeOneRepresents.degreeOpen_one_eq_top`, whose generation hypothesis is `U_1 = Proj`
   at `Stacks.SymGraded.adjoin_grading_one_eq_top`.

   Three statements are used in between. That the nonvanishing open of a section is carried
   along an isomorphism of modules is `Stacks.Ample.nonvanishingLocus_congr`. The other two are
   the transport of item 2 from `V.ι ⁻¹ᵁ V` to `⊤`
   (`classifyingTrivialisationOfSection_hom_pullbackSection_top`) and the `Γ(M, ⊤)` spelling
   `nonvanishingLocus_unit_eq_basicOpen` of the nonvanishing locus of a
   section of the structure sheaf, the library's identification with the basic open being stated
   over a restriction-compatible family instead, which is not the spelling
   `Stacks.NonvanishingOpen.nonvanishingOpen` is built on. The identification of
   `Stacks.AlgebraicGeometry.MorphismsIntoProj.pullbackDegreeSection` at
   `factorThroughDegreeOpenOne` with the `pullbackSection`-of-`chartDegreeOneSection` spelling
   item 2 produces is `…RelativeProj.pullbackDegreeSection_eq_pullbackSection` and
   `…RelativeProj.chartDegreeOneSection_eq_degreeSection_localDegreeOne`; the
   transport between the two sections is absorbed into
   `nonvanishingOpen_pullbackSection_eq_top`'s `haa` argument, and is performed there because
   the module is a variable there — read at the bundle's twist, the same `congrArg` exhausts the
   recursion budget.
4. **`Away`-extensionality in degree one.** For `t ∈ 𝒜 1` and
   `Algebra.adjoin (𝒜 0) (𝒜 1 : Set A) = ⊤`, two ring homomorphisms out of
   `HomogeneousLocalization.Away 𝒜 t` that agree on the image of `𝒜 0` and on the ratios `m/t`,
   `m ∈ 𝒜 1`, are equal. Mathlib's `HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top` is
   exactly that generation statement for a **finite** generating family, which `Γ(V, ℰ)` is not,
   so the infinite-family version is needed;
   `Stacks.ProjGlobalSectionsAppTop.away_ringHom_ext` is the all-degrees extensionality it
   refines. This is the only one of the four that is pure algebra.

   **Its generation half is available, at one spelling.**
   `SheafGradedAlgebra.mem_prodClosure_of_adjoin_eq_top` (in the namespace
   `Stacks.AlgebraicGeometry.RelativeProjBridge`) of
   `StacksFrontier/AlgebraicGeometry/RelativeProjBridge/DegreeOneProducts.lean` says that a
   homogeneous section of degree `d` is a sum of products of `d` degree-one sections with a
   degree-zero coefficient, from exactly the `Algebra.adjoin` hypothesis above and with **no
   finiteness** — which is the infinite-family generation statement, and it is what remains to be
   transported along `HomogeneousLocalization.Away.mk` (`Away.mk` is additive in the numerator at
   a fixed denominator exponent, and `(a · m₁ ⋯ m_d)/t^d = (a/1) · (m₁/t) ⋯ (m_d/t)`). It is
   stated for `A : SheafGradedAlgebra S` over an open of the base rather than for an abstract
   `𝒜 : ℕ → σ` with `[GradedRing 𝒜]`, and **item 4 is stated at that same section-ring
   spelling**, as
   `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.away_ringHom_ext_degree_one`:
   it is the spelling the consumer `Γ(V, Sym ℰ)` actually meets, and generalising the generation
   half in place is not merely a question of taste — the transparency note of
   `StacksFrontier.AlgebraicGeometry.RelativeProjBridge.SectionRing` records the synthesis of
   `SetLike.GradedMul` over a section ring as prohibitive, so an abstract version instantiated
   here would not elaborate.

   **No hypothesis in degree zero is needed**: a degree-zero coefficient
   contributes `a / 1`, which is the degree-one ratio `(a · t) / t`
   (`Stacks.ProjGlobalSectionsAppTop.away_mk_zero_eq_mk_one`), so the degree-one ratios alone
   generate the chart ring and the extensionality is tested on them alone.

With item 4 and the `chartHomEquiv`-valued form of item 2, `eq_of_chartHomEquiv_eq` gives
`sectionChartMap V σ hσ hV = sectionChartMap V σ' hσ' hV`, hence `V.ι ≫ σ = V.ι ≫ σ'` over every
trivialising affine open (`ι_comp_eq_of_classifies`), and a morphism out of `X` is determined on
an open cover (`eq_of_classifies_tautologicalDatum`).
`Stacks.AlgebraicGeometry.RelativeProj.comp_chart_injective` **is not used and cannot be**: it goes
from the composites with the chart
to the chart morphisms, and the route needs the converse, which is `congrArg` and
`CategoryTheory.cancel_mono`.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01NA](https://stacks.math.columbia.edu/tag/01NA)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
-/
