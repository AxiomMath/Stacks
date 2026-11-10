module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationAssociatedModule
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSchemeTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentFromCoherence
import StacksCore.Tactic.StacksAttribute

/-!
# The sheaf of differentials of a morphism locally of finite presentation

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`.  Stacks 05ZF asserts that
`Ω_{X/Y}` is an `𝒪_X`-module of finite presentation when `f` is locally of finite presentation.

**The tag is proved here, unconditionally and under the source's own hypothesis**, by the
source's own route, as
`Space.isFinitePresentationOnSite_sheafOfDifferentials_of_isLocallyOfFinitePresentation`:
the source reduces to the scheme case, Morphisms, Lemma 01V3 — which this repository proves, as
`AlgebraicGeometry.Scheme.Hom.isFinitePresentation_relativeDifferentials` — by the étale
localization of Stacks 04CU.  Both halves of that route are available.  The identification
`Ω_{X/Y}|_{U_étale} = Ω_{U/V}` on a square of étale charts is
`AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso`, and the final sentence of
Stacks 04CU — the identification of `Ω_{U/V}` for a morphism of *schemes* of the site with the
small-étale module associated to the Zariski sheaf of relative differentials, Stacks 04CS — is
`AlgebraicGeometry.Space.sheafOfDifferentialsSchemeComparison`.  The two further steps the
reduction needs are proved in this development:
`AlgebraicGeometry.Space.isFinitePresentationOnSite_representedAssociatedModule`, the
finite-presentation analogue of Stacks 03DV (2), and
`AlgebraicGeometry.Space.isFinitePresentationOnSite_iff_exists_etale_surjective`, the
finite-presentation analogue of Stacks 03M0, conditions (1) and (2).

A second, sectionwise route to the same conclusion is also kept here, and it is the
finite-presentation refinement of the proof given for Stacks 05ZE in
`StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsFiniteType`.  There the presentation is
read off the construction of `Ω_{X/Y}` as the sheafification of the presheaf of sectionwise Kähler
differentials of `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X`:

* the *generators* are the universal differentials `d_{X/Y}(yᵢ)` of a finite family of sections
  generating `𝒪_X(V)` as an `(f⁻¹𝒪_Y)(V)`-algebra.  That they generate `Ω_{X/Y}` on the slice at
  `V` is `AlgebraicGeometry.Space.generates_universalDerivation_of_adjoin` below, which is the
  content of Stacks 05ZE repackaged in the sectionwise form `PresheafOfModules.Generates`;
* the *relations* among them are carried, as the last clause of
  `AlgebraicGeometry.Space.HasFinitePresentationChartData`;
* generators and relations together give a finite global presentation on the slice at `V` by
  `SheafOfModules.hasFiniteGlobalPresentation_over_of_generates`, and those presentations on a
  covering of every object are Stacks 03DL(7),
  `SheafOfModules.IsFinitePresentationOnSite`.

## Algebra, Lemma 00UU: carried by one group of statements, proved for the other

Stacks 05ZE carries `AlgebraicGeometry.Space.HasUnramifiedChartTransitions` — that the transition
maps `𝒪_X(V) ⟶ 𝒪_X(W)` of the small étale site have vanishing module of differentials, which is
"an étale ring map is unramified", Algebra, Lemma 00UU, for the ring map of sections of an arrow
of the small étale site.  **That hypothesis is false as stated** (see the implementation notes for
a chart of `P¹` on which it fails), so carrying it makes the conclusion vacuous for every space
with a non-affine étale chart.  The first group of sectionwise statements below carries it, as
`hunram`; the second group, whose names end in `_of_isAffine` or `_of_chartData`, does not.

What Algebra, Lemma 00UU does give is the vanishing at an arrow between charts with *affine*
underlying scheme, `AlgebraicGeometry.Space.subsingleton_kaehlerDifferential_chartRing`, and that
is all the second group ever needs: every covering sieve it uses is replaced by the sieve generated
by its affine members (`AlgebraicGeometry.Space.SmallEtale.ofArrows_affineMember_mem_topology`),
and the generation statement, once established at an affine member, holds on everything over that
member because restriction is semilinear and so carries a linear combination of restricted
generators to another one.

## The sectionwise route's chart data

`AlgebraicGeometry.Space.HasFinitePresentationChartData` is the sheaf-theoretic content of "`f`
is locally of finite presentation": on a covering of every object of the small étale site of `X`
there are finitely many sections generating `𝒪_X(V)` as an `(f⁻¹𝒪_Y)(V)`-algebra together with
finitely many relations among their universal differentials which generate all such relations
étale-locally.  Its generation clause is exactly the clause of
`AlgebraicGeometry.Space.HasFiniteTypeChartAlgebras` that Stacks 05ZE goes through, and its
relations clause is the *finite* form of the relations half of the base-change comparison of
Descent, Proposition 03DX(2).  Both halves of that proposition are proved in this development
and unconditionally — the equivalence is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts` and the
commutative-algebra core of its relations half is
`AlgebraicGeometry.Space.ker_eq_span_image_mapRange_of_flat` — but
`AlgebraicGeometry.Space.epi_kernelLift_chartRelations`, the form in which the relations half is
used there, indexes the generating family by *all* relations, which is exactly the distinction
between quasi-coherence and finite presentation; so it does not by itself supply the finitely
many `rⱼ` this clause asks for.

Nothing below depends on that: the tag is proved by the source's route instead, and this chart
datum is an input to the sectionwise route only.

The tag is registered twice, as it is on the base: the two `@[stacks 05ZF]` suffixes sit on
`AlgebraicGeometry.Space.isFinitePresentationOnSite_sheafOfDifferentials_of_chartData`, the
sectionwise route from the chart datum, and on
`isFinitePresentationOnSite_sheafOfDifferentials_of_isLocallyOfFinitePresentation_unconditional`,
the source's statement with nothing assumed.

## Main definitions

* `AlgebraicGeometry.Space.HasFinitePresentationChartData` is the chart datum of the sectionwise
  route.

## Main results

* `AlgebraicGeometry.Space.hasUnramifiedChartTransitions_of_forall_isAffine`: the hypothesis
  `HasUnramifiedChartTransitions` holds for a space all of whose étale charts are affine.  Nothing
  below uses it; it is kept because it says exactly how far Algebra, Lemma 00UU goes.
* `AlgebraicGeometry.Space.SmallEtale.ofArrows_affineMember_mem_topology`: **every covering sieve
  of the small étale site is generated by its members with affine underlying scheme.**  This is
  what lets an argument available only at affine charts run on a covering.
* `AlgebraicGeometry.Space.universalDerivation_mem_span_restrict_of_subsingleton`: the pointwise
  form of the trapping lemma of Stacks 05ZE, taking the vanishing of the differentials of *one*
  transition map rather than of all of them.
* `AlgebraicGeometry.Space.span_universalDerivation_le_of_isAffine`: over an affine chart above
  an affine chart carrying algebra generators, every universal differential is in the span of the
  differentials of the restricted generators.
* `AlgebraicGeometry.Space.generates_universalDerivation_of_adjoin`,
  `AlgebraicGeometry.Space.hasFiniteGlobalPresentation_sheafOfDifferentials_over`,
  `AlgebraicGeometry.Space.isFinitePresentationOnSite_sheafOfDifferentials` and
  `Space.isFinitePresentationOnSite_sheafOfDifferentials_of_isLocallyOfFinitePresentation`:
  the sectionwise route carrying `HasUnramifiedChartTransitions` as `hunram`, as it is carried on
  the base — the generators half, the presentation on one chart, the conclusion of Stacks 05ZF
  from the chart datum, and that conclusion at the source's hypothesis.
* `AlgebraicGeometry.Space.generates_universalDerivation_of_adjoin_of_isAffine`: the universal
  differentials of a family of algebra generators of `𝒪_X(V)` over `(f⁻¹𝒪_Y)(V)`, for an
  *affine* `V`, generate `Ω_{X/Y}` sectionwise over `V`, with no unramifiedness hypothesis.
* `AlgebraicGeometry.Space.hasFiniteGlobalPresentation_sheafOfDifferentials_over_of_isAffine`:
  **the presentation on one affine chart** — those generators together with a locally generating
  family of relations exhibit a finite global presentation of `Ω_{X/Y}` on the slice at `V`, in
  the sense of Stacks 03DE(7).
* `AlgebraicGeometry.Space.isFinitePresentationOnSite_sheafOfDifferentials_of_chartData`: the
  conclusion of Stacks 05ZF from the chart datum of the sectionwise route alone.
* `isFinitePresentationOnSite_sheafOfDifferentials_of_isLocallyOfFinitePresentation_unconditional`:
  **Stacks 05ZF**, under exactly the source's hypothesis and with nothing else assumed — if `f`
  is locally of finite presentation then `Ω_{X/Y}` is an `𝒪_X`-module of finite presentation.
* `Space.isQuasicoherentOnSite_sheafOfDifferentials_of_finitePresentationChartData`
  and
  `AlgebraicGeometry.Space.isFiniteTypeOnSite_sheafOfDifferentials_of_finitePresentationChartData`:
  the two consequences the source draws from 05ZF, quasi-coherence of `Ω_{X/Y}` (the statement of
  Stacks 04CV) and its finite type (Stacks 05ZE), from the chart datum alone; the same two
  carrying `hunram` are `..._of_chartData`.

Every declaration below lives in the `AlgebraicGeometry.Space` namespace.

## Implementation notes

**Why `HasUnramifiedChartTransitions` is false, and so had to be removed rather than proved.**
The objects of
`AlgebraicGeometry.Space.SmallEtale` are étale charts with *arbitrary* underlying scheme —
`AlgebraicGeometry.Space.IsEtaleChart` asks for representability and étaleness, never for
affineness — and the structure sheaf is global regular functions,
`AlgebraicGeometry.Space.structurePresheaf` being by definition
`(toOver ⋙ toScheme).op ⋙ Scheme.Γ`.  So `HasUnramifiedChartTransitions` asserts
`Ω[Γ(W)⁄Γ(V)] = 0` for *every* arrow `W ⟶ V` of the site.  Take `X = P¹_k` over `S = Spec k`,
`V` the identity chart of `P¹` and `W` the open immersion `A¹ ↪ P¹`, both étale charts and the
arrow between them the open immersion: then `Γ(V) = k` and `Γ(W) = k[t]`, and `Ω[k[t]⁄k]` is
free of rank one.  The failure is affineness of the *larger* chart.  Affineness of the smaller
chart is separately necessary for the related base-change statements, as the module notes of
`StacksFrontier.AlgebraicGeometry.Spaces.ChartSections` record.

**How the hypothesis was dropped.**  Every covering sieve the proof uses is refined to the sieve
generated by its members with affine underlying scheme, by
`AlgebraicGeometry.Space.SmallEtale.ofArrows_affineMember_mem_topology`, which is
`AlgebraicGeometry.Space.SmallEtale.exists_affine_etale_ofArrows` at each member together with
`CategoryTheory.GrothendieckTopology.transitive`; and the chart carrying the algebra generators is
asked to be affine, which costs nothing because the covering supplied by
`AlgebraicGeometry.Space.HasFinitePresentationChartData` is refined the same way before its data
is read off.  The two charts of every transition map the proof differentiates are then affine, so
`AlgebraicGeometry.Space.subsingleton_kaehlerDifferential_chartRing` applies.

The one thing this needs beyond the Stacks 05ZE argument is that the conclusion survives
precomposition: the sieve generated by a family of affine charts has members that are not affine,
and at such a member the generation statement is obtained by restricting the one at the affine
chart it factors through — restriction being semilinear, a linear combination of restricted
generators restricts to a linear combination of restricted generators.  That step is the `key`
computation inside
`AlgebraicGeometry.Space.generates_universalDerivation_of_adjoin`; it is written out there rather
than as a standalone lemma because the module instance on `Ω_{X/Y}(W)` over `𝒪_X(W)` is the one
the surrounding `PresheafOfModules.Generates` goal fixes, and a standalone statement of the same
equation re-searches for it and finds a different, merely definitionally equal, path.

**The source's route, which is the one the tag is proved by.**  Stacks 05ZF is deduced in the
source from the scheme case by the étale localization of Stacks 04CU, and all four steps that
route needs are available.  The scheme case 01V3 is
`AlgebraicGeometry.Scheme.Hom.isFinitePresentation_relativeDifferentials`.  The two clauses of
Stacks 04CU proper are
`AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso`.  The *final sentence* of
Stacks 04CU read through Stacks 04CS — the identification of the spaces-level `Ω` of a morphism
of schemes of the site with the small-étale module associated to its Zariski sheaf of relative
differentials — is `AlgebraicGeometry.Space.sheafOfDifferentialsSchemeComparison`, proved in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeTransport.lean`; an earlier
revision of this paragraph called it a missing hypothesis of Stacks 04CV, which is also no longer
true — `AlgebraicGeometry.Space.isQuasicoherentOnSite_sheafOfDifferentials` carries nothing.  The
two remaining steps are the finite-presentation analogues of the two local statements the
quasi-coherent route uses, and they are proved for this purpose:
`AlgebraicGeometry.Space.isFinitePresentationOnSite_representedAssociatedModule` in
`StacksFrontier/AlgebraicGeometry/Spaces/FinitePresentationAssociatedModule.lean` and
`AlgebraicGeometry.Space.isFinitePresentationOnSite_iff_exists_etale_surjective` in
`StacksFrontier/AlgebraicGeometry/Spaces/FinitePresentationEtaleMorphism.lean`, the latter resting
on `SheafOfModules.isFinitePresentationOnSite_of_coversTop_hasFiniteGlobalPresentation`, which is
the locality of `SheafOfModules.IsFinitePresentationOnSite` on a covering family — Stacks 03DN for
clause (7).

`PresheafOfModules.Generates` is the sectionwise form of generation by finitely many sections
over an object, and it is what
`SheafOfModules.hasFiniteGlobalPresentation_over_of_generates` consumes, so the generators half
is proved in that form here rather than reused from
`AlgebraicGeometry.Space.hasFiniteGlobalGenerators_sheafOfDifferentials_over_of_isAffine`, which
has already discarded the sectionwise data in favour of
`SheafOfModules.HasFiniteGlobalGenerators`.  The
three ingredients are the same: local surjectivity of the unit of sheafification
(`AlgebraicGeometry.Space.exists_sieve_mem_span_universalDerivation`), the trapping of the
universal differentials of the sections over `W` by those of the restrictions from `V`
(`AlgebraicGeometry.Space.universalDerivation_mem_span_restrict`), and the `Algebra.adjoin`
induction (`AlgebraicGeometry.Space.universalDerivation_restrict_mem_span_of_adjoin`).

The relations clause of `AlgebraicGeometry.Space.HasFinitePresentationChartData` is stated in
exactly the shape `SheafOfModules.hasFiniteGlobalPresentation_over_of_generates` asks for, with
the restriction maps written as `AlgebraicGeometry.Space.chartRestrict`; this is the shape in
which the base-change comparison of Descent, Proposition 03DX(2) supplies it, the relations over a
member of a covering being combinations of the restrictions of the relations over the chart.

Quasi-coherence and finite type are read off the conclusion through the instances
`SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite` and
`SheafOfModules.isFiniteTypeOnSite_of_isFinitePresentationOnSite`.  No 04CV attribute is claimed
on them: Stacks 04CV is already proved unconditionally, as
`AlgebraicGeometry.Space.isQuasicoherentOnSite_sheafOfDifferentials`, and these two draw the
source's consequences of 05ZF from the chart data of the sectionwise route instead.

## References

* [Stacks Project, Tag 05ZF](https://stacks.math.columbia.edu/tag/05ZF)
* [Stacks Project, Tag 05ZE](https://stacks.math.columbia.edu/tag/05ZE), the finite type
  statement this refines.
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT), the sheaf of
  differentials of a morphism of algebraic spaces and its universal derivation.
* [Stacks Project, Tag 01V3](https://stacks.math.columbia.edu/tag/01V3), the scheme case, which
  the source reduces to.
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU), the étale localization
  the source's reduction uses.
* [Stacks Project, Tag 04CV](https://stacks.math.columbia.edu/tag/04CV), quasi-coherence of
  `Ω_{X/Y}`.
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP), locally of finite
  presentation for morphisms of algebraic spaces.
* [Stacks Project, Tag 00UU](https://stacks.math.columbia.edu/tag/00UU), unramified ring maps.
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL), part (7), modules of
  finite presentation on a site, and [Tag 03DE](https://stacks.math.columbia.edu/tag/03DE),
  part (7), a finite global presentation.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-! ### Refining a covering sieve to its affine members -/

/-- **The affine members of a sieve of the small étale site**: an object with affine underlying
scheme, together with an arrow of the sieve out of it. -/
abbrev SmallEtale.AffineMember {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : SmallEtale B S hS F} (T : Sieve U) :=
  Σ V : SmallEtale B S hS F, {g : V ⟶ U // T.arrows g ∧
    IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V)}

/-- **Every covering sieve of the small étale site is generated by its affine members.**  The
affine opens of the scheme underlying a member of the sieve are again étale charts, they are
affine, and they cover that member
(`AlgebraicGeometry.Space.SmallEtale.exists_affine_etale_ofArrows`); a sieve is closed under
precomposition, so each of them is itself a member of the sieve.  So the family of *all* affine
members covers each member, and the sieve it generates is covering by transitivity.

This is what lets an argument which only works at a chart with affine underlying scheme be run on
a covering: it replaces an arbitrary covering by one whose generating family is affine, at the
cost of nothing, since the generated sieve is contained in the original.  It is the tool the
implementation notes of this file used to call for. -/
theorem SmallEtale.ofArrows_affineMember_mem_topology
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : SmallEtale B S hS F} (T : Sieve U)
    (hT : T ∈ SmallEtale.topology B S hS F U) :
    Sieve.ofArrows (fun i : SmallEtale.AffineMember B S hS T => i.1)
        (fun i => i.2.1) ∈ SmallEtale.topology B S hS F U := by
  refine (SmallEtale.topology B S hS F).transitive hT _ fun V h hh => ?_
  obtain ⟨I, Z, a, haff, hcov, -⟩ := SmallEtale.exists_affine_etale_ofArrows B S hS F V
  refine (SmallEtale.topology B S hS F).superset_covering ?_ hcov
  rintro W w ⟨A, q, b, ⟨j⟩, rfl⟩
  exact (Sieve.mem_ofArrows_iff _ _ _).2
    ⟨⟨Z j, a j ≫ h, T.downward_closed hh (a j), haff j⟩, q, Category.assoc _ _ _⟩

/-! ### Algebra, Lemma 00UU for the transition maps between affine charts -/

/-- **Restriction of regular functions along a morphism of affine étale charts is an étale ring
map.**  The underlying morphism of schemes is étale by the cancellation lemma
`AlgebraicGeometry.Space.etale_of_comp_etale_chart`, and for affine source and target an étale
morphism of schemes is an étale map on global sections.

Both affineness hypotheses are genuinely needed: `AlgebraicGeometry.HasRingHomProperty.appTop`
asks for them, and `AlgebraicGeometry.Etale.etale_appLE` only ever speaks about affine opens.
This is the étale analogue of `AlgebraicGeometry.Space.smooth_chartRestrict`. -/
theorem etale_chartRestrict {U V : SmallEtale B S hS X.1} (f : V ⟶ U)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj V)) :
    (chartRestrict (hF := X.2) f).Etale := by
  have _ := hU
  have _ := hV
  have _ : AlgebraicGeometry.Etale
      ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).map f) :=
    etale_of_comp_etale_chart B S hS V.property U.property (CostructuredArrow.w f.hom)
  exact HasRingHomProperty.appTop (P := @AlgebraicGeometry.Etale)
    ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).map f) inferInstance

/-- **Algebra, Lemma 00UU for the small étale site, at affine charts.**  For a morphism
`f : V ⟶ U` of étale charts of `X` whose two underlying schemes are affine, the module of
differentials of the restriction ring map `𝒪_X(U) ⟶ 𝒪_X(V)` vanishes.

An étale ring map is formally unramified, and a formally unramified algebra has vanishing module
of Kähler differentials (`Algebra.FormallyUnramified.subsingleton_kaehlerDifferential`).

This is the content that `AlgebraicGeometry.Space.HasUnramifiedChartTransitions` asks for —
*restricted to affine charts*.  It does **not** discharge that hypothesis, which quantifies over
all arrows of the small étale site; see the implementation notes for why the unrestricted
statement is false. -/
theorem subsingleton_kaehlerDifferential_chartRing {U V : SmallEtale B S hS X.1} (f : V ⟶ U)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj V)) :
    letI := chartAlgebra (hF := X.2) f
    Subsingleton (KaehlerDifferential (chartRing B S hS X.1 X.2 U)
      (chartRing B S hS X.1 X.2 V)) :=
  (etale_chartRestrict B S hS f hU hV).formallyUnramified.subsingleton_kaehlerDifferential

/-- **`HasUnramifiedChartTransitions` holds whenever every étale chart of `X` is affine.**  On
affine charts the transition maps are étale ring maps, hence formally unramified, by
`AlgebraicGeometry.Space.subsingleton_kaehlerDifferential_chartRing`.

This is the exact extent to which Algebra, Lemma 00UU discharges
`AlgebraicGeometry.Space.HasUnramifiedChartTransitions`, and the affineness side condition
cannot be dropped: see the implementation notes for a chart of `P¹` on which the unrestricted
statement fails.  Nothing below needs this: the statements of this file quantify over no
transition map that is not an arrow between affine charts. -/
theorem hasUnramifiedChartTransitions_of_forall_isAffine
    (haff : ∀ U : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    HasUnramifiedChartTransitions B S hS X := by
  intro V W g
  exact subsingleton_kaehlerDifferential_chartRing B S hS g (haff V) (haff W)

/-! ### The chart datum of the sectionwise route -/

/-- **Étale-local finite presentation data for `𝒪_X` over `f⁻¹𝒪_Y`.**  On a covering sieve of
every object of the small étale site of `X` there are finitely many sections `y₁, …, yₙ`
generating `𝒪_X(V)` as an `(f⁻¹𝒪_Y)(V)`-algebra, together with finitely many vectors
`r₁, …, r_k` of coefficients which are relations among the universal differentials
`d_{X/Y}(yᵢ)` and which generate, étale-locally, every relation among their restrictions.

This is the sheaf-theoretic content of "`f` is locally of finite presentation".  Its first
clause is the one `AlgebraicGeometry.Space.HasFiniteTypeChartAlgebras` records for Stacks 05ZE;
its third clause is the *finite* form of the relations half of the base-change comparison of
Descent, Proposition 03DX(2).  That proposition itself is proved in this development, as
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`, with the
commutative-algebra core of its relations half
`AlgebraicGeometry.Space.ker_eq_span_image_mapRange_of_flat`; what the third clause adds to it is
the finiteness of the generating family of relations.

This datum is an input to the sectionwise route only.  Stacks 05ZF itself is proved without it,
by the source's route, in
`Space.isFinitePresentationOnSite_sheafOfDifferentials_of_isLocallyOfFinitePresentation`. -/
def HasFinitePresentationChartData (f : X ⟶ Y) : Prop :=
  ∀ U : SmallEtale B S hS X.1, ∃ T : Sieve U, T ∈ (SmallEtale.topology B S hS X.1) U ∧
    ∀ ⦃V : SmallEtale B S hS X.1⦄ (g : V ⟶ U), T.arrows g →
      ∃ (n k : ℕ) (y : Fin n → chartRing B S hS X.1 X.2 V)
        (r : Fin k → Fin n → chartRing B S hS X.1 X.2 V),
        (letI := sharpAlgebra B S hS f V
          ∀ z : chartRing B S hS X.1 X.2 V,
            z ∈ Algebra.adjoin (inverseImageStructureRing B S hS f V) (Set.range y)) ∧
        (∀ j : Fin k, ∑ i, r j i • (universalDerivation B S hS f).d (y i) = 0) ∧
        (∀ (W : SmallEtale B S hS X.1) (h : W ⟶ V)
          (τ : Fin n → chartRing B S hS X.1 X.2 W),
          (∑ i, τ i • (universalDerivation B S hS f).d
              (chartRestrict (hF := X.2) h (y i)) = 0) →
          ∃ T' : Sieve W, T' ∈ (SmallEtale.topology B S hS X.1) W ∧
            ∀ ⦃Wo : SmallEtale B S hS X.1⦄ (p : Wo ⟶ W), T'.arrows p →
              ∃ c : Fin k → chartRing B S hS X.1 X.2 Wo, ∀ i,
                ∑ j, c j * chartRestrict (hF := X.2) (p ≫ h) (r j i) =
                  chartRestrict (hF := X.2) p (τ i))

/-! ### The generators half, sectionwise -/

/-- **With unramified transitions, the universal differentials of a family of algebra generators
generate `Ω_{X/Y}` sectionwise over `V`.**

This is the content of Stacks 05ZE in the form `PresheafOfModules.Generates`: every section of
`Ω_{X/Y}` over an object lying over `V` is, on a covering sieve, an `𝒪_X`-combination of the
restrictions of the `d_{X/Y}(yᵢ)`.

A section is locally an `𝒪_X`-combination of universal differentials because the unit of
sheafification is locally surjective
(`AlgebraicGeometry.Space.exists_sieve_mem_span_universalDerivation`); each universal
differential is trapped by the restrictions from `V`
(`AlgebraicGeometry.Space.universalDerivation_mem_span_restrict`); and those are in the span of
the `d_{X/Y}(yᵢ|_·)` by the `Algebra.adjoin` induction
(`AlgebraicGeometry.Space.universalDerivation_restrict_mem_span_of_adjoin`). -/
theorem generates_universalDerivation_of_adjoin (f : X ⟶ Y)
    (hunram : HasUnramifiedChartTransitions B S hS X)
    {V : SmallEtale B S hS X.1} {n : ℕ}
    (y : Fin n → chartRing B S hS X.1 X.2 V)
    (hy : letI := sharpAlgebra B S hS f V
      ∀ z : chartRing B S hS X.1 X.2 V,
        z ∈ Algebra.adjoin (inverseImageStructureRing B S hS f V) (Set.range y)) :
    PresheafOfModules.Generates (smallEtaleRingedSite B S hS X.1 X.2).J
      (sheafOfDifferentials B S hS f).val
      (fun i => (universalDerivation B S hS f).d (y i)) := by
  intro V' g t
  obtain ⟨T, hT, hTspec⟩ := exists_sieve_mem_span_universalDerivation B S hS f V' t
  refine ⟨T, hT, fun W h hh => ?_⟩
  have hle : (Submodule.span (chartRing B S hS X.1 X.2 W)
        (Set.range fun c : chartRing B S hS X.1 X.2 W =>
          (universalDerivation B S hS f).d c) :
        Submodule (chartRing B S hS X.1 X.2 W)
          ((sheafOfDifferentials B S hS f).val.obj (op W))) ≤
      Submodule.span (chartRing B S hS X.1 X.2 W)
        (Set.range fun i : Fin n => (universalDerivation B S hS f).d
          (chartRestrict (hF := X.2) (h ≫ g) (y i))) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨c, rfl⟩
    exact universalDerivation_mem_span_restrict B S hS f hunram (h ≫ g) _
      (fun z => universalDerivation_restrict_mem_span_of_adjoin B S hS f (h ≫ g) y z (hy z)) c
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hle (hTspec h hh))
  refine ⟨a, Eq.trans (Finset.sum_congr rfl fun i _ => ?_) ha⟩
  exact congrArg (fun w : (sheafOfDifferentials B S hS f).val.obj (op W) => a i • w)
    (((universalDerivation B S hS f).d_map (h ≫ g).op (y i)).symm)

/-! ### The presentation on one chart -/

/-- A finite global presentation of `Ω_{X/Y}` on the slice at `V` from generators `d(yᵢ)` that
generate sectionwise and relations `r` that generate all relations étale-locally. -/
private theorem hasFiniteGlobalPresentation_over_of_generates_d (f : X ⟶ Y)
    (V : (smallEtaleRingedSite B S hS X.1 X.2).C) {n k : ℕ}
    (y : Fin n → chartRing B S hS X.1 X.2 V)
    (r : Fin k → Fin n → chartRing B S hS X.1 X.2 V)
    (hr : ∀ j : Fin k, ∑ i, r j i • (universalDerivation B S hS f).d (y i) = 0)
    (hgen : PresheafOfModules.Generates (smallEtaleRingedSite B S hS X.1 X.2).J
      (sheafOfDifferentials B S hS f).val
      (fun i => (universalDerivation B S hS f).d (y i)))
    (hrel : ∀ (W : SmallEtale B S hS X.1) (h : W ⟶ V)
      (τ : Fin n → chartRing B S hS X.1 X.2 W),
      (∑ i, τ i • (universalDerivation B S hS f).d
          (chartRestrict (hF := X.2) h (y i)) = 0) →
      ∃ T' : Sieve W, T' ∈ (SmallEtale.topology B S hS X.1) W ∧
        ∀ ⦃Wo : SmallEtale B S hS X.1⦄ (p : Wo ⟶ W), T'.arrows p →
          ∃ c : Fin k → chartRing B S hS X.1 X.2 Wo, ∀ i,
            ∑ j, c j * chartRestrict (hF := X.2) (p ≫ h) (r j i) =
              chartRestrict (hF := X.2) p (τ i)) :
    ((sheafOfDifferentials B S hS f).over V).HasFiniteGlobalPresentation :=
  SheafOfModules.hasFiniteGlobalPresentation_over_of_generates
    (sheafOfDifferentials B S hS f) V
    (fun i => (universalDerivation B S hS f).d (y i)) r hr hgen
    (fun W h τ hτ => hrel W h τ
      (Eq.trans (Finset.sum_congr rfl fun i _ =>
        congrArg (fun w : (sheafOfDifferentials B S hS f).val.obj (op W) => τ i • w)
          ((universalDerivation B S hS f).d_map h.op (y i))) hτ))

/-- **A finite global presentation of `Ω_{X/Y}` on the slice at a chart.**  If `𝒪_X(V)` is
generated as an `(f⁻¹𝒪_Y)(V)`-algebra by `y₁, …, yₙ`, the transition maps of the small étale
site are unramified, and `r₁, …, r_k` are relations among the `d_{X/Y}(yᵢ)` which generate all
relations étale-locally, then `Ω_{X/Y}` has a finite global presentation on the slice at `V` in
the sense of Stacks 03DE(7).

The generators are `AlgebraicGeometry.Space.generates_universalDerivation_of_adjoin` and the
assembly is `SheafOfModules.hasFiniteGlobalPresentation_over_of_generates`. -/
theorem hasFiniteGlobalPresentation_sheafOfDifferentials_over (f : X ⟶ Y)
    (hunram : HasUnramifiedChartTransitions B S hS X)
    (V : (smallEtaleRingedSite B S hS X.1 X.2).C) {n k : ℕ}
    (y : Fin n → chartRing B S hS X.1 X.2 V)
    (r : Fin k → Fin n → chartRing B S hS X.1 X.2 V)
    (hy : letI := sharpAlgebra B S hS f V
      ∀ z : chartRing B S hS X.1 X.2 V,
        z ∈ Algebra.adjoin (inverseImageStructureRing B S hS f V) (Set.range y))
    (hr : ∀ j : Fin k, ∑ i, r j i • (universalDerivation B S hS f).d (y i) = 0)
    (hrel : ∀ (W : SmallEtale B S hS X.1) (h : W ⟶ V)
      (τ : Fin n → chartRing B S hS X.1 X.2 W),
      (∑ i, τ i • (universalDerivation B S hS f).d
          (chartRestrict (hF := X.2) h (y i)) = 0) →
      ∃ T' : Sieve W, T' ∈ (SmallEtale.topology B S hS X.1) W ∧
        ∀ ⦃Wo : SmallEtale B S hS X.1⦄ (p : Wo ⟶ W), T'.arrows p →
          ∃ c : Fin k → chartRing B S hS X.1 X.2 Wo, ∀ i,
            ∑ j, c j * chartRestrict (hF := X.2) (p ≫ h) (r j i) =
              chartRestrict (hF := X.2) p (τ i)) :
    ((sheafOfDifferentials B S hS f).over V).HasFiniteGlobalPresentation :=
  hasFiniteGlobalPresentation_over_of_generates_d B S hS f V y r hr
    (generates_universalDerivation_of_adjoin B S hS f hunram y hy) hrel

/-! ### Stacks 05ZF -/

/-- **Stacks 05ZF**, with the two carried hypotheses in place of "`f` is locally of finite
presentation".  If `𝒪_X` is étale-locally generated as an `f⁻¹𝒪_Y`-algebra by finitely many
sections whose universal differentials have étale-locally finitely generated relations, and the
transition maps of the small étale site of `X` are unramified, then `Ω_{X/Y}` is an
`𝒪_X`-module of finite presentation.

The covering of each object is the one `hfp` supplies, presented as the family of all its
arrows indexed by their sources, and on each member the finite presentation is
`AlgebraicGeometry.Space.hasFiniteGlobalPresentation_sheafOfDifferentials_over`. -/
@[stacks 05ZF "finite presentation of Ω_{X/Y}. ASSUMED, not proved: the relations half of
  Descent, Proposition 03DX(2), as the last clause of `hfp` — that the relations among the
  universal differentials of a finite generating family are étale-locally finitely generated.
  Also assumed: the bridge from 03XP(1) to étale-local finite generation of 𝒪_X over f⁻¹𝒪_Y
  (first clause of `hfp`), and unramifiedness of the transition maps of the small étale site
  (`hunram`, 00UU), which `hasUnramifiedChartTransitions_of_forall_isAffine` discharges when
  every étale chart is affine. PROVED here: the generators half and the assembly into 03DL(7)"]
theorem isFinitePresentationOnSite_sheafOfDifferentials (f : X ⟶ Y)
    (hunram : HasUnramifiedChartTransitions B S hS X)
    (hfp : HasFinitePresentationChartData B S hS f) :
    (sheafOfDifferentials B S hS f).IsFinitePresentationOnSite := by
  refine ⟨fun U => ?_⟩
  obtain ⟨T, hT, hTspec⟩ := hfp U
  refine ⟨Σ V : (smallEtaleRingedSite B S hS X.1 X.2).C, {g : V ⟶ U // T.arrows g},
    fun i => i.1, fun i => i.2.1, ?_, fun i => ?_⟩
  · refine (smallEtaleRingedSite B S hS X.1 X.2).J.superset_covering (fun Z g hg => ?_) hT
    exact (Sieve.mem_ofArrows_iff _ _ _).2 ⟨⟨Z, g, hg⟩, 𝟙 Z, (Category.id_comp g).symm⟩
  · obtain ⟨n, k, y, r, hy, hr, hrel⟩ := hTspec i.2.1 i.2.2
    exact hasFiniteGlobalPresentation_sheafOfDifferentials_over B S hS f hunram i.1 y r hy hr
      hrel

/-- **Stacks 05ZF.**  If `f : X ⟶ Y` is a morphism of algebraic spaces over `S` which is
locally of finite presentation, then `Ω_{X/Y}` is an `𝒪_X`-module of finite presentation.

The two inputs not proved in this development are carried universally quantified: the bridge
from `AlgebraicGeometry.Space.IsLocallyOfFinitePresentation` (Stacks 03XP(1), defined through
étale scheme charts) to the étale-local finite presentation data of
`AlgebraicGeometry.Space.HasFinitePresentationChartData`, and the unramifiedness of the
transition maps of a small étale site, which is Algebra, Lemma 00UU for the ring map of
sections of an arrow of that site. -/
@[stacks 05ZF "the source's statement. ASSUMED, not proved: the relations half of Descent,
  Proposition 03DX(2), inside `hfp`; the bridge from 03XP(1) to étale-local finite presentation
  data for 𝒪_X over f⁻¹𝒪_Y, also inside `hfp`; and unramifiedness of the transition maps of a
  small étale site (`hunram`, 00UU), discharged by
  `hasUnramifiedChartTransitions_of_forall_isAffine` when every étale chart is affine. Both
  inputs are quantified over all algebraic spaces over `S`"]
theorem isFinitePresentationOnSite_sheafOfDifferentials_of_isLocallyOfFinitePresentation
    (hunram : ∀ X' : AlgebraicSpaces B S hS, HasUnramifiedChartTransitions B S hS X')
    (hfp : ∀ (X' Y' : AlgebraicSpaces B S hS) (g : X' ⟶ Y'),
      IsLocallyOfFinitePresentation B S hS g.hom → HasFinitePresentationChartData B S hS g)
    (f : X ⟶ Y) (hf : IsLocallyOfFinitePresentation B S hS f.hom) :
    (sheafOfDifferentials B S hS f).IsFinitePresentationOnSite :=
  isFinitePresentationOnSite_sheafOfDifferentials B S hS f (hunram X) (hfp X Y f hf)

/-! ### The two consequences the source draws -/

/-- **Quasi-coherence of `Ω_{X/Y}` under the hypotheses of Stacks 05ZF.**  A module of finite
presentation on a site is quasi-coherent, so the conclusion of Stacks 05ZF gives the statement
of Stacks 04CV for a morphism carrying the finite presentation data.

This is weaker than Stacks 04CV, whose statement in the source is unconditional; no 04CV
attribute is claimed. -/
theorem isQuasicoherentOnSite_sheafOfDifferentials_of_chartData (f : X ⟶ Y)
    (hunram : HasUnramifiedChartTransitions B S hS X)
    (hfp : HasFinitePresentationChartData B S hS f) :
    (sheafOfDifferentials B S hS f).IsQuasicoherentOnSite :=
  letI := isFinitePresentationOnSite_sheafOfDifferentials B S hS f hunram hfp
  inferInstance

/-- **Finite type of `Ω_{X/Y}` under the hypotheses of Stacks 05ZF.**  A module of finite
presentation on a site is of finite type, so the conclusion of Stacks 05ZF gives that of
Stacks 05ZE for a morphism carrying the finite presentation data, without the separate
generation hypothesis of
`AlgebraicGeometry.Space.isFiniteTypeOnSite_sheafOfDifferentials`. -/
theorem isFiniteTypeOnSite_sheafOfDifferentials_of_chartData (f : X ⟶ Y)
    (hunram : HasUnramifiedChartTransitions B S hS X)
    (hfp : HasFinitePresentationChartData B S hS f) :
    (sheafOfDifferentials B S hS f).IsFiniteTypeOnSite :=
  letI := isFinitePresentationOnSite_sheafOfDifferentials B S hS f hunram hfp
  inferInstance

/-! ### The generators half with Algebra, Lemma 00UU proved rather than assumed -/

/-- **The span of all universal differentials over an affine chart is the span of the
differentials of the generators restricted there.**  This is
`AlgebraicGeometry.Space.universalDerivation_mem_span_restrict_of_subsingleton` at the arrow
`p ≫ g`, whose vanishing differentials are Algebra, Lemma 00UU for an arrow between affine
charts, together with the `Algebra.adjoin` induction. -/
theorem span_universalDerivation_le_of_isAffine (f : X ⟶ Y)
    {V : SmallEtale B S hS X.1} {n : ℕ}
    (hV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj V))
    (y : Fin n → chartRing B S hS X.1 X.2 V)
    (hy : letI := sharpAlgebra B S hS f V
      ∀ z : chartRing B S hS X.1 X.2 V,
        z ∈ Algebra.adjoin (inverseImageStructureRing B S hS f V) (Set.range y))
    {V' A : SmallEtale B S hS X.1} (g : V' ⟶ V) (p : A ⟶ V')
    (hA : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj A)) :
    (Submodule.span (chartRing B S hS X.1 X.2 A)
        (Set.range fun c : chartRing B S hS X.1 X.2 A =>
          (universalDerivation B S hS f).d c) :
        Submodule (chartRing B S hS X.1 X.2 A)
          ((sheafOfDifferentials B S hS f).val.obj (op A))) ≤
      Submodule.span (chartRing B S hS X.1 X.2 A)
        (Set.range fun i : Fin n => (universalDerivation B S hS f).d
          (chartRestrict (hF := X.2) (p ≫ g) (y i))) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨c, rfl⟩
  exact universalDerivation_mem_span_restrict_of_subsingleton B S hS f (p ≫ g)
    (subsingleton_kaehlerDifferential_chartRing B S hS (p ≫ g) hV hA) _
    (fun z => universalDerivation_restrict_mem_span_of_adjoin B S hS f (p ≫ g) y z (hy z)) c

/-- **The universal differentials of a family of algebra generators of an affine chart generate
`Ω_{X/Y}` sectionwise over it.**

This is the content of Stacks 05ZE in the form `PresheafOfModules.Generates`: every section of
`Ω_{X/Y}` over an object lying over `V` is, on a covering sieve, an `𝒪_X`-combination of the
restrictions of the `d_{X/Y}(yᵢ)`.

A section is locally an `𝒪_X`-combination of universal differentials because the unit of
sheafification is locally surjective
(`AlgebraicGeometry.Space.exists_sieve_mem_span_universalDerivation`); on an *affine* member of
that covering each universal differential is trapped by the restrictions from `V`
(`AlgebraicGeometry.Space.exists_fun_sum_smul_eq_of_isAffine`); and the covering may be taken to
be generated by its affine members
(`AlgebraicGeometry.Space.SmallEtale.ofArrows_affineMember_mem_topology`), the conclusion
propagating from a member to anything over it because restriction carries a linear combination of
restrictions to a linear combination of restrictions. -/
theorem generates_universalDerivation_of_adjoin_of_isAffine (f : X ⟶ Y)
    {V : SmallEtale B S hS X.1} {n : ℕ}
    (hV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj V))
    (y : Fin n → chartRing B S hS X.1 X.2 V)
    (hy : letI := sharpAlgebra B S hS f V
      ∀ z : chartRing B S hS X.1 X.2 V,
        z ∈ Algebra.adjoin (inverseImageStructureRing B S hS f V) (Set.range y)) :
    PresheafOfModules.Generates (smallEtaleRingedSite B S hS X.1 X.2).J
      (sheafOfDifferentials B S hS f).val
      (fun i => (universalDerivation B S hS f).d (y i)) := by
  intro V' g t
  obtain ⟨T, hT, hTspec⟩ := exists_sieve_mem_span_universalDerivation B S hS f V' t
  refine ⟨Sieve.ofArrows (fun i : SmallEtale.AffineMember B S hS T => i.1) (fun i => i.2.1),
    SmallEtale.ofArrows_affineMember_mem_topology B S hS T hT, fun W h hh => ?_⟩
  obtain ⟨A, q, p, ⟨i⟩, rfl⟩ := hh
  -- the coefficients over the affine member `i`, where Algebra, Lemma 00UU is available
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
    (span_universalDerivation_le_of_isAffine B S hS f hV y hy g i.2.1 i.2.2.2
      (hTspec i.2.1 i.2.2.1))
  -- restrict them along `q`; restriction is semilinear, so the combination restricts too
  refine ⟨fun j => chartRestrict (hF := X.2) q (c j), ?_⟩
  have key : ∀ j : Fin n,
      chartRestrict (hF := X.2) q (c j) •
          (sheafOfDifferentials B S hS f).val.restrictₛₗ ((q ≫ i.2.1) ≫ g).op
            ((universalDerivation B S hS f).d (y j)) =
        (sheafOfDifferentials B S hS f).val.restrictₛₗ q.op
          (c j • (universalDerivation B S hS f).d
            (chartRestrict (hF := X.2) (i.2.1 ≫ g) (y j))) := by
    intro j
    refine Eq.trans ?_
      (map_smulₛₗ ((sheafOfDifferentials B S hS f).val.restrictₛₗ q.op) (c j) _).symm
    refine congrArg
      (fun w : (sheafOfDifferentials B S hS f).val.obj (op W) =>
        chartRestrict (hF := X.2) q (c j) • w) ?_
    refine Eq.trans ((sheafOfDifferentials B S hS f).val.congr_map_apply
      (show ((q ≫ i.2.1) ≫ g).op = (i.2.1 ≫ g).op ≫ q.op from
        congrArg Quiver.Hom.op (Category.assoc q i.2.1 g)) _) ?_
    exact Eq.trans
      ((sheafOfDifferentials B S hS f).val.map_comp_apply (i.2.1 ≫ g).op q.op _)
      (congrArg
        (fun w : (sheafOfDifferentials B S hS f).val.obj (op i.1) =>
          (sheafOfDifferentials B S hS f).val.restrictₛₗ q.op w)
        ((universalDerivation B S hS f).d_map (i.2.1 ≫ g).op (y j)).symm)
  refine Eq.trans (Finset.sum_congr rfl fun j _ => key j) ?_
  refine Eq.trans (map_sum ((sheafOfDifferentials B S hS f).val.restrictₛₗ q.op) _ _).symm ?_
  exact Eq.trans
    (congrArg (fun w : (sheafOfDifferentials B S hS f).val.obj (op i.1) =>
      (sheafOfDifferentials B S hS f).val.restrictₛₗ q.op w) hc)
    ((sheafOfDifferentials B S hS f).val.map_comp_apply i.2.1.op q.op t).symm

/-! ### The presentation on one affine chart -/

/-- **A finite global presentation of `Ω_{X/Y}` on the slice at a chart.**  If `𝒪_X(V)` is
generated as an `(f⁻¹𝒪_Y)(V)`-algebra by `y₁, …, yₙ`, the transition maps of the small étale
site are unramified, and `r₁, …, r_k` are relations among the `d_{X/Y}(yᵢ)` which generate all
relations étale-locally, then `Ω_{X/Y}` has a finite global presentation on the slice at `V` in
the sense of Stacks 03DE(7).

The generators are `AlgebraicGeometry.Space.generates_universalDerivation_of_adjoin` and the
assembly is `SheafOfModules.hasFiniteGlobalPresentation_over_of_generates`. -/
theorem hasFiniteGlobalPresentation_sheafOfDifferentials_over_of_isAffine (f : X ⟶ Y)
    (V : (smallEtaleRingedSite B S hS X.1 X.2).C)
    (hV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj V))
    {n k : ℕ}
    (y : Fin n → chartRing B S hS X.1 X.2 V)
    (r : Fin k → Fin n → chartRing B S hS X.1 X.2 V)
    (hy : letI := sharpAlgebra B S hS f V
      ∀ z : chartRing B S hS X.1 X.2 V,
        z ∈ Algebra.adjoin (inverseImageStructureRing B S hS f V) (Set.range y))
    (hr : ∀ j : Fin k, ∑ i, r j i • (universalDerivation B S hS f).d (y i) = 0)
    (hrel : ∀ (W : SmallEtale B S hS X.1) (h : W ⟶ V)
      (τ : Fin n → chartRing B S hS X.1 X.2 W),
      (∑ i, τ i • (universalDerivation B S hS f).d
          (chartRestrict (hF := X.2) h (y i)) = 0) →
      ∃ T' : Sieve W, T' ∈ (SmallEtale.topology B S hS X.1) W ∧
        ∀ ⦃Wo : SmallEtale B S hS X.1⦄ (p : Wo ⟶ W), T'.arrows p →
          ∃ c : Fin k → chartRing B S hS X.1 X.2 Wo, ∀ i,
            ∑ j, c j * chartRestrict (hF := X.2) (p ≫ h) (r j i) =
              chartRestrict (hF := X.2) p (τ i)) :
    ((sheafOfDifferentials B S hS f).over V).HasFiniteGlobalPresentation :=
  hasFiniteGlobalPresentation_over_of_generates_d B S hS f V y r hr
    (generates_universalDerivation_of_adjoin_of_isAffine B S hS f hV y hy) hrel

/-! ### Stacks 05ZF, with Algebra, Lemma 00UU proved rather than assumed -/

/-- **Finite presentation of `Ω_{X/Y}` from étale-local presentation data for `𝒪_X` over
`f⁻¹𝒪_Y`.**  If `𝒪_X` is étale-locally generated as an `f⁻¹𝒪_Y`-algebra by finitely many sections
whose universal differentials have étale-locally finitely generated relations, then `Ω_{X/Y}` is
an `𝒪_X`-module of finite presentation.

The covering of each object is the one `hfp` supplies, refined to its members with affine
underlying scheme
(`AlgebraicGeometry.Space.SmallEtale.ofArrows_affineMember_mem_topology`), and on each such
member the finite presentation is
`AlgebraicGeometry.Space.hasFiniteGlobalPresentation_sheafOfDifferentials_over`.  Refining to
affine members is what makes Algebra, Lemma 00UU applicable: the only transition maps the proof
differentiates are arrows between affine charts.

The tag itself is
`Space.isFinitePresentationOnSite_sheafOfDifferentials_of_isLocallyOfFinitePresentation`
below, which takes the source's hypothesis on `f`; this is the sectionwise route to the same
conclusion, kept because it reads the presentation off the construction of `Ω_{X/Y}` as a
sheafification rather than off the scheme case. -/
@[stacks 05ZF "finite presentation of Ω_{X/Y} from étale-local finite presentation data for 𝒪_X
  over f⁻¹𝒪_Y; unramifiedness of the transition maps of the small étale site (00UU) is proved,
  not assumed.  The source's own hypothesis is taken in
  `isFinitePresentationOnSite_sheafOfDifferentials_of_isLocallyOfFinitePresentation_unconditional`"]
theorem isFinitePresentationOnSite_sheafOfDifferentials_of_chartData (f : X ⟶ Y)
    (hfp : HasFinitePresentationChartData B S hS f) :
    (sheafOfDifferentials B S hS f).IsFinitePresentationOnSite := by
  refine ⟨fun U => ?_⟩
  obtain ⟨T, hT, hTspec⟩ := hfp U
  refine ⟨SmallEtale.AffineMember B S hS T, fun i => i.1, fun i => i.2.1,
    SmallEtale.ofArrows_affineMember_mem_topology B S hS T hT, fun i => ?_⟩
  obtain ⟨n, k, y, r, hy, hr, hrel⟩ := hTspec i.2.1 i.2.2.1
  exact hasFiniteGlobalPresentation_sheafOfDifferentials_over_of_isAffine B S hS f i.1 i.2.2.2 y
    r hy hr hrel

/-- **Stacks 05ZF.**  If `f : X ⟶ Y` is a morphism of algebraic spaces over `S` which is locally
of finite presentation, then `Ω_{X/Y}` is an `𝒪_X`-module of finite presentation.

The proof is the source's, and it is the finite-presentation refinement of the proof of
Stacks 04CV in `StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsQuasicoherent`.  An
atlas `q : V ⟶ Y` of the target lifts, by Stacks 02X1, to a surjective étale chart `p : U ⟶ X`
of the source together with a morphism `α : U ⟶ V` of schemes of the site making the square
commute.  Being locally of finite presentation is a condition on exactly such squares, so `α` is
a morphism of schemes locally of finite presentation and its Zariski sheaf of relative
differentials is of finite presentation by Morphisms, Lemma 01V3.  The identification of
Stacks 04CU reads the pullback of `Ω_{X/Y}` along `p` as the sheaf of differentials of `α`, which
the final sentence of Stacks 04CU — Stacks 04CS, in the form
`AlgebraicGeometry.Space.sheafOfDifferentialsSchemeComparison` — identifies with the small-étale
module associated to that Zariski sheaf; the associated module of a module of finite presentation
is of finite presentation by
`AlgebraicGeometry.Space.isFinitePresentationOnSite_representedAssociatedModule`.  Finally
finite presentation descends from a surjective étale chart by
`AlgebraicGeometry.Space.isFinitePresentationOnSite_iff_exists_etale_surjective`, the pullback of
modules and étale restriction being matched by Equation 03LW. -/
@[stacks 05ZF "finite presentation of Ω_{X/Y} for a morphism of algebraic spaces locally of
  finite presentation", sga "3 III 0.14" "more general", sga "7 VI 5.1" "partial"]
theorem
  isFinitePresentationOnSite_sheafOfDifferentials_of_isLocallyOfFinitePresentation_unconditional
    (f : X ⟶ Y) (hf : IsLocallyOfFinitePresentation B S hS f.hom) :
    (sheafOfDifferentials B S hS f).IsFinitePresentationOnSite := by
  obtain ⟨V, q, hqS, hqE⟩ := Y.property.exists_atlas
  obtain ⟨U, p, α, hdiag, hpS, hpE⟩ :=
    exists_surjective_etale_presentation_lift B S hS X.property Y.property f.hom V q hqS hqE
  set a : schemeSpace U ⟶ X := ObjectProperty.homMk p
  set bb : schemeSpace V ⟶ Y := ObjectProperty.homMk q
  set ψ : schemeSpace U ⟶ schemeSpace V := schemeSpaceMap α
  have haE : IsEtale B S hS a.hom := isEtale_of_presheaf_etale B S hS hpE
  have hbE : IsEtale B S hS bb.hom := isEtale_of_presheaf_etale B S hS hqE
  have haS : IsSurjective B S hS a.hom := isSurjective_of_presheafSurjective B S hS p hpS
  have hcomm : a ≫ f = ψ ≫ bb := by
    apply ObjectProperty.hom_ext
    exact hdiag
  have iso1 := sheafOfDifferentialsEtaleLocalizationIso B S hS f a ψ bb haE hbE hcomm
  obtain ⟨echart⟩ := sheafOfDifferentialsSchemeComparison B S hS U V α
  let hα : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map α) :=
    hf U V p q α hpE hqE hdiag.symm
  have hfp : (sheafOfDifferentials B S hS ψ).IsFinitePresentationOnSite :=
    SheafOfModules.IsFinitePresentationOnSite.of_iso echart.symm
      (isFinitePresentationOnSite_representedAssociatedModule B S hS U _ _
        (Scheme.Hom.isFinitePresentation_relativeDifferentials _))
  refine (isFinitePresentationOnSite_iff_exists_etale_surjective B S hS
    (sheafOfDifferentials B S hS f)).2 ⟨schemeSpace U, a, haE, haS, ?_⟩
  exact SheafOfModules.IsFinitePresentationOnSite.of_iso
    ((modulePullbackIsoEtaleModulePullback B S hS a haE).app (sheafOfDifferentials B S hS f))
    (SheafOfModules.IsFinitePresentationOnSite.of_iso iso1.symm hfp)

/-! ### The two consequences the source draws, from the chart datum alone -/

/-- **Quasi-coherence of `Ω_{X/Y}` from the chart datum of the sectionwise route.**  A module of
finite presentation on a site is quasi-coherent, so the conclusion of Stacks 05ZF gives the
statement of Stacks 04CV for a morphism with finite presentation data.

No 04CV attribute is claimed: Stacks 04CV is proved unconditionally as
`AlgebraicGeometry.Space.isQuasicoherentOnSite_sheafOfDifferentials`, and this records only what
the sectionwise route yields on its own. -/
theorem isQuasicoherentOnSite_sheafOfDifferentials_of_finitePresentationChartData (f : X ⟶ Y)
    (hfp : HasFinitePresentationChartData B S hS f) :
    (sheafOfDifferentials B S hS f).IsQuasicoherentOnSite :=
  letI := isFinitePresentationOnSite_sheafOfDifferentials_of_chartData B S hS f hfp
  inferInstance

/-- **Finite type of `Ω_{X/Y}` from the chart datum of the sectionwise route.**  A module of
finite presentation on a site is of finite type, so the conclusion of Stacks 05ZF gives that of
Stacks 05ZE for a morphism with finite presentation data, without the separate generation
hypothesis of `AlgebraicGeometry.Space.isFiniteTypeOnSite_sheafOfDifferentials`. -/
theorem isFiniteTypeOnSite_sheafOfDifferentials_of_finitePresentationChartData (f : X ⟶ Y)
    (hfp : HasFinitePresentationChartData B S hS f) :
    (sheafOfDifferentials B S hS f).IsFiniteTypeOnSite :=
  letI := isFinitePresentationOnSite_sheafOfDifferentials_of_chartData B S hS f hfp
  inferInstance

end AlgebraicGeometry.Space

end
