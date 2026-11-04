module

public import Mathlib.Algebra.MvPolynomial.Cardinal
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.SmoothFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Smooth.LiftTorsor
public import StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmooth
import StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmoothTag
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Smoothness and formal smoothness for morphisms of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, that is a morphism of
presheaves on the big fppf site of `S`.

## Main definitions

No new definitions are introduced. Smoothness of `f` is
`AlgebraicGeometry.Space.IsSmooth` of `StacksFrontier.AlgebraicGeometry.Spaces.Smooth`: every
commuting square of étale scheme charts of `f` has smooth underlying scheme morphism. The
same condition for `AlgebraicGeometry.LocallyOfFinitePresentation` is
`AlgebraicGeometry.Space.IsLocallyOfFinitePresentation` of
`StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation`.

## Main results

* `AlgebraicGeometry.Space.isSmoothAt_of_isOpenSubspace` is the introduction rule for
  smoothness at a point: a smooth open subspace witnesses it at each of its points, and
  `AlgebraicGeometry.Space.IsSmoothAt.exists_mem_range_pointsMap` restates the definition with
  the point condition as a membership in the image of the open subspace on points.
* `AlgebraicGeometry.Space.isSmooth_of_isLocallyOfFinitePresentation_of_formallySmooth`: a
  morphism of algebraic spaces which is locally of finite presentation and formally smooth is
  smooth. This is the implication towards smoothness of [Stacks Project, Tag 04AM].
* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_and_formallySmooth_of_isSmooth`: a
  smooth *representable* morphism of algebraic spaces is locally of finite presentation and
  formally smooth. This is the implication from smoothness of [Stacks Project, Tag 04AM], under
  the extra hypothesis that the morphism is representable.
* `AlgebraicGeometry.Space.exists_lift_of_formallySmooth`: if `f` is formally smooth then,
  in any commuting square of étale charts `a` of `X` and `b` of `Y` over `h : U ⟶ V`, every
  lifting problem for `h` along a square-zero closed immersion of affine objects of the site
  has a solution. This is [Stacks Project, Tag 061H], and
  `AlgebraicGeometry.Space.exists_lift_scheme_of_formallySmooth` is the same statement with
  the thickening presented by a first-order thickening of affine *schemes* which the site
  contains, rather than by a morphism of the site.
* `Stacks.Smooth.smooth_of_exists_lift_of_size_lt`: a morphism of schemes of size below a
  cardinal `κ` which is locally of finite presentation and has the lifting property against
  first-order thickenings of affine schemes of size below `κ` is smooth. This is the form of
  the hard direction of [Stacks Project, Tag 02H6] that a lifting property quantified over a
  site can supply, and it rests on
  `Stacks.Smooth.formallySmooth_of_exists_section_of_mk_lt`, that formal smoothness of an
  algebra is detected by square-zero extensions of bounded cardinality, and on
  `Stacks.Smooth.exists_appLE_section_of_exists_lift`, which turns a solution of a lifting
  problem into a section of a square-zero extension of the sections over an affine chart.

## Implementation notes

The equivalence of [Stacks Project, Tag 04AM] — `f` is smooth if and only if it is locally of
finite presentation and formally smooth — is **not** fully proved here. The implication towards
smoothness is proved for every `f`; the implication from smoothness is proved only for a
*representable* `f`, and formal smoothness of a smooth morphism which is not representable is
missing.

The implication towards smoothness is proved. Stacks proves it by descending smoothness from a
chart, but here nothing has to be descended: smoothness of `f` *is* a property of its étale
charts, `AlgebraicGeometry.Space.IsSmooth` being the every-chart condition of Tag 03MJ. So the
proof has two steps. First, Tag 061H: a lifting problem for a chart `h : U ⟶ V` is pushed into
`X` along the chart, solved there by formal smoothness of `f`, and pulled back to `U` because
the chart is étale, so that the solution extends over the thickening, uniquely enough to be
compatible with the chart of `Y`. Second, the scheme case Tag 02H6. The second step is *not*
`Stacks.Smooth.smooth_of_formallySmoothScheme`, because
`AlgebraicGeometry.Space.FormallySmooth` quantifies over affine objects of the site — schemes
of size below `AlgebraicGeometry.BigFppfSite.cutoff` — whereas
`Stacks.Smooth.FormallySmoothScheme` and `Stacks.Smooth.FormallySmooth` quantify over all
affine schemes, equivalently over all rings, in the ambient universe; and for any big fppf
site there are affine schemes it does not contain. The replacement is
`Stacks.Smooth.smooth_of_exists_lift_of_size_lt`, which needs the lifting property only for
thickenings the site contains. Its proof uses `Algebra.FormallySmooth.of_split`: a surjection
`P →ₐ[R] A` from a formally smooth `R`-algebra with kernel `J` makes `A` formally smooth over
`R` as soon as `P ⧸ J ^ 2 →ₐ[R] A` has a section, so a *single* thickening suffices, and
taking `P` to be the polynomial algebra on `A` over `R` its cardinality is at most
`max ℵ₀ (max #A #R)` by `MvPolynomial.cardinalMk_le_max`. With `R = Γ(S, V₀)` and
`A = Γ(X, W)` for affine opens of the chart, those are at most the sizes of the two schemes by
`AlgebraicGeometry.Scheme.mk_sections_le_size`, so the spectrum of `P ⧸ J ^ 2` has size below
the cutoff by `AlgebraicGeometry.Scheme.size_of_isAffine` and the site contains it.

The implication from smoothness needs no torsor argument when `f` is representable. Its easy
half, that a smooth morphism is locally of finite presentation, is
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_isSmooth` of
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties`, since smoothness of a
scheme morphism implies local finite presentation. For its other half, smoothness of a
representable `f` is smoothness of each of its base changes to an object of the site, by
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_relative`, which is Tag 03MJ for a
representable morphism; so the base change of `f` along a section of the target over the
thickening is a smooth morphism of *schemes*, the scheme case Tag 02H6
`Stacks.Smooth.formallySmoothScheme_of_smooth` extends the section of that base change over
the thickening, and the extension is a morphism of the site because the site's inclusion into
schemes is fully faithful.

Representability is exactly what step (II) of the proof of Tag 04AM dispenses with, and it is
step (II) alone that is unavailable. For a general `f` the sheaf of solutions of a lifting
problem on the étale site of the thickening `T'` is a pseudo-torsor under
`Hom(a^*Ω_{X/Y}, 𝒞_{T/T'})`, étale-local solutions exist, and triviality of the torsor is the
vanishing of `H¹` of that sheaf on the small étale site of the affine scheme `T`.

Step (I), the étale-local solutions, is proved unconditionally:
`AlgebraicGeometry.Space.exists_etale_affine_local_lift` is part (4) of Tag 04CY, resting on
the topological invariance of the étale site, Tag 039R. The objects of step (II) are all
present too: the sheaf of solutions is `AlgebraicGeometry.Space.liftsSubfunctor` and the
acting sheaf `Hom(a^*Ω_{X/Y}, 𝒞_{T/T'})` is `AlgebraicGeometry.Space.liftActionSheaf`, both
Tag 061D; the sheaf of relative differentials of a morphism of algebraic spaces is
`AlgebraicGeometry.Space.sheafOfDifferentials`, Tag 04CT; the conormal module is
`AlgebraicGeometry.Space.conormalModule`, Tag 04CN; torsors on a site and the bijection of
Tag 03AJ between their isomorphism classes and `H¹` are `PseudoTorsor` and
`Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1`; and the comparison of étale with Zariski
cohomology of a quasi-coherent sheaf is
`AlgebraicGeometry.smallEtaleQuasiCoherentGlobalCohomologyIso`, Tag 03DW, whose Zariski half
on an affine is `Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen`, Tag 01XB.

The one thing that would join them is the *action* of
`AlgebraicGeometry.Space.liftActionSheaf` on `AlgebraicGeometry.Space.liftsSubfunctor`, which
is what makes the sheaf of solutions a pseudo-torsor at all. Translating a lift `a'` by
`θ : a^*Ω_{Y/B} ⟶ 𝒞_{X/X'}` means forming the structure map `(a')^♯ + d_{Y/B} ∘ θ` and reading
the result back as a morphism. **That action is built over an étale scheme chart**, in
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheafAction`; what is still owed is
said after the list of its ingredients below.

**That does not have to go through Tag 04D0, and so does not have to go through Tag 04KL.** It
does not need to read a homomorphism of structure sheaves back as a morphism of algebraic
*spaces*, the existence half of Tag 04KL over a base
(`AlgebraicGeometry.Space.IsRecoveredFromSmallEtale`, proved by
`AlgebraicGeometry.Space.isRecoveredFromSmallEtale_holds`, so Tag 04D0 assumes nothing either).
The sheaf of solutions is a sheaf on the small étale site, so the action only has
to be defined on the sections over an étale *scheme* chart, where reading a ring map back as a
morphism is `Spec` and not Tag 04KL. The four ingredients are:

* the translation itself, in a chart: `Stacks.Smooth.addDerivationHom` and
  `Stacks.Smooth.exists_lift_of_derivation`, with the difference of two lifts as
  `Stacks.Smooth.liftDiffDerivation`
  (`StacksFrontier.AlgebraicGeometry.Smooth.LiftTorsor`), for the solutions of a lifting problem
  whose image lies in an affine open of a scheme;
* the comparison of two chart presentations of one section, which is what makes the chart-level
  difference well defined: `AlgebraicGeometry.Space.exists_chart_hom_of_restrict_app_eq`
  (`StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartLiftTransport`), Tag 04AL, with no
  hypothesis beyond étaleness and representability of the chart;
* the abstract principal homogeneity the result would satisfy, on an arbitrary site:
  `Deformation.ToposThickening.LiftDiagram.translate_existsUnique`, Tag 08UG;
* the comparison `Ω_{U/V} ≅ a^*Ω_{Y/B}|_U` over a commuting square of étale charts, which
  identifies a chart derivation with a section of
  `AlgebraicGeometry.Space.liftActionSheaf` — Tag 04CU with Tag 04CS, both proved outright here
  as `AlgebraicGeometry.Space.sheafOfDifferentialsEtaleChartComparison` and
  `AlgebraicGeometry.Space.sheafOfDifferentialsSchemeSiteComparison`.

**The assembly is written down.**
`AlgebraicGeometry.Space.ChartLiftPresentation.translateActionSection` of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheafAction` is the action `θ · a'` on
the sections of `AlgebraicGeometry.Space.liftsSubfunctor` over an étale scheme chart, against a
chart presentation of the lifting problem — an affine étale chart `U'` of `X'`, the square-zero
closed immersion `U = X ×_{X'} U' ⟶ U'` it carries, an affine chart square `W ⟶ V` over
`q : Y ⟶ B`, and a factorization of the lift through `W`.  The translate is again a lift,
`0` acts trivially, sums act as composites, and the action is free and transitive on the lifts
the chart presents — the transitivity is where Tag 04AL enters, and the freeness is where
étaleness of the chart of `Y` does.  A presentation exists for every lift that factors through
an affine chart square, `AlgebraicGeometry.Space.exists_chartLiftPresentation`.  The acting
group there is not an auxiliary one: by
`Stacks.Smooth.existsUnique_linearMap_comp_pullbackD_of_module`
(`AlgebraicGeometry.Space.ChartLiftPresentation.derivOfActionSection_bijective`) it is exactly
the `Γ(U, ⊤)`-linear maps `Γ(a^*Ω_{W/V}, ⊤) ⟶ 𝒞_{U/U'}`, which are the sections of the acting
sheaf at the chart in their *Zariski* form.  **The comparison of those Zariski sections with the
sections of the small étale internal hom `AlgebraicGeometry.Space.liftActionSheaf` itself is now
complete** — `AlgebraicGeometry.Space.ChartLiftPresentation.actionSectionEquiv`
(`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftActionSheafActionSection`) — so what
remains before this is an action of sheaves is the glueing of the chartwise actions alone, a lift
over an arbitrary chart factoring through an affine chart of `Y` only locally.

**The two geometric halves and the two passages of that comparison are all proved.**  Reading a section of
`AlgebraicGeometry.Space.smallEtaleInternalHom` on a chart is
`AlgebraicGeometry.Space.liftActionSheafChartEval`, and with
`AlgebraicGeometry.Space.firstOrderConormalModuleIso` for the conormal side the *target* is
identified by `AlgebraicGeometry.Space.liftActionSheafChartKerEval`.  For the *source*:

* Tags 04CU and 04CS compose, in exactly the spelling a chart presentation produces, to
  `AlgebraicGeometry.Space.chartCompositeDifferentialsAssociatedIso`
  (`StacksFrontier.AlgebraicGeometry.Spaces.ChartSquareDifferentialsAssociated`): for a morphism
  `c` of represented algebraic spaces factoring as a morphism of the site into the chart `W` of
  `Y` followed by that chart, `c^*Ω_{Y/B}` is the module `Mᵃ` of Tag 03DU (4) of the Zariski
  `a^*Ω_{W/V}`;
* the passage from an isomorphism of associated modules to a bijection of **morphisms** carries
  nothing: the small étale half of Tag 0GN7 is unconditional over an arbitrary scheme,
  `AlgebraicGeometry.SmallEtale.fullyFaithfulAssociatedModuleQcoh'`, Tag 070S part (2) for the
  small étale site being proved as
  `AlgebraicGeometry.SmallEtale.sectionsComparisonSheafifiesToIso`; its hom-set form on a
  represented algebraic space is
  `AlgebraicGeometry.Space.bijective_representedAssociatedModule_map`
  (`StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModuleFullyFaithful`), which asks
  quasi-coherence of the target only.

The passage does not need Tag 0GN7 on the slice at an *affine* chart, and the fpqc sheaf
condition of Tag 03DT that such a route would carry is available anyway: Tag 03DT is
`AlgebraicGeometry.quasiCoherentPresheaf_isSheaf_fpqc'`; its instance on the slice is
`AlgebraicGeometry.Space.SmallEtale.isSheaf_sliceAssociatedPresheaf_of_isQuasicoherent`, with the
hypothesis-free slice full faithfulness
`AlgebraicGeometry.Space.SmallEtale.bijective_associatedModuleMap_slice_unconditional`; and no
slice and no affineness are needed anyway.

* the Zariski side is available too: morphisms of quasi-coherent modules on an affine scheme *are*
  the `Γ(U, ⊤)`-linear maps of their global sections, which is
  `Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_app_top` with
  `Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_top_eq`, packaged as
  `Stacks.AlgebraicGeometry.ModuleLimits.bijective_appTopₗ`.  Composed with the previous item
  this is `AlgebraicGeometry.Space.representedAssociatedModuleHomEquivLinearMap`, whose
  right-hand side is character-for-character the shape of `ActionSection`.

**So exactly one link of the source comparison is still owed**, and it is bookkeeping: the
sections of `AlgebraicGeometry.Space.liftActionSheaf` at a chart are morphisms of the
restrictions to the *slice* at that chart, whereas the isomorphism above is about the inverse
image to the small étale site of the chart space.  Matching them is the slice form of Tag 04M0,
restated for the projections of the small étale ringed site as
`AlgebraicGeometry.Space.smallEtaleRingedSitePostcompOverEquivalence`
(`StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeChartComparison`), together with
Equation 03LW, `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`, which identifies
the inverse image along an étale chart with restriction of sections.

Simple transitivity of the action *at the chart* needs none of Tag 05ZM: the two lifts being
compared there have structure maps into one and the same ring `Γ(U', ⊤)`, which is what
`Stacks.Smooth.liftDiffDerivation` subtracts.  For the difference of two lifts read on sheaves,
however, the structure-sheaf half of Tag 05ZM does enter: the difference of *two* lifts
compares structure maps whose targets are the two different direct images `(a')_*𝒪_{X'}` and
`(b')_*𝒪_{X'}`, and identifying those is that half of Tag 05ZM. **It is proved**, as
`AlgebraicGeometry.Space.structureRingSheafDirectImageIsoOfRestrictEq`
(`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSheafEquivalence`), beside the
equivalence of spaces-étale sheaf topoi
`AlgebraicGeometry.Space.spacesEtaleSheafEquiv_of_isThickening`. So the two structure maps of two lifts are parallel
homomorphisms of sheaves of rings — `AlgebraicGeometry.Space.structureSharpOfRestrictEq` and
the structure map of the second lift — and their difference can be formed.

**That the two agree after `i^♯` is proved**, as
`AlgebraicGeometry.Space.structureSharpOfRestrictEq_comp_pushforward_structureSharp`
(`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSharpRestrictEq`): the two parallel
homomorphisms become equal after the direct image along `b'` of
`i^♯ : 𝒪_{X'} ⟶ i_*𝒪_X`, both sides being the structure map of `i ≫ a' = i ≫ b'` read through
the composition isomorphism of Tag 03G2 part (3). That is the first of the two items which the
"Partial coverage" section of
`StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceDerivation` lists.

**The second item of that list — the descent of the derivation along `𝒪_{Y'} ⟶ 𝒪_Y` — does not
arise in step (II) of Tag 04AM at all**, and neither does hypothesis (2) of Tag 0618. The sheaf
of lifts `AlgebraicGeometry.Space.liftsSubfunctor` is the one of Tag 061D in the case where the
target is *not* deformed: a lift is a morphism `U' ⟶ Y` into `Y` itself, so the target
thickening is `Y ⊆ Y`, the map `𝒪_{Y'} ⟶ 𝒪_Y` along which the derivation would have to descend
is the identity, and hypothesis (2) — the equality of the two maps
`a^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` — holds because `𝒞_{Y/Y}` vanishes, which is
`AlgebraicGeometry.Space.isZero_conormalModule_top` and
`AlgebraicGeometry.Space.eq_zero_of_isZero_conormalModule_top`, the remark of Tag 061D that the
map `A` is always zero. The bookkeeping that puts the two structure maps in the shape
`AlgebraicGeometry.Space.liftDifference` consumes — two homomorphisms *into* `𝒪_{X'}`, that is
the inverse-image form `(b')^{-1}𝒪_{Y'} ⟶ 𝒪_{X'}` of the two structure maps — **is written
down**, in
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSharpRestrictEqInverseImage`. The
comparison of the two inverse images is
`AlgebraicGeometry.Space.commRingInverseImageIsoOfRestrictEq`, the mate of the Tag 05ZM
comparison of the two direct images along
`Stacks.Sheaves.ToposPushforward.commRingImageAdjunction`; the transported equality is
`AlgebraicGeometry.Space.inverseImageStructureSharpOfRestrictEq_comp_structureSharp`, which is
the hypothesis `hfg`; and the difference of the two structure maps of two lifts is
`AlgebraicGeometry.Space.liftPairDifference`. The comparison itself is never computed — it only
has to carry one named morphism to another, which is a statement about transposes,
`CategoryTheory.Adjunction.eq_leftAdjointUniq_hom_app_comp`.

What then separates that difference from a section of
`AlgebraicGeometry.Space.liftActionSheaf` is the bundling of its four equations as a
`PresheafOfModules.Derivation'`, the transposition
`Stacks.Sheaves.RingedToposModules.inverseImageDerivationEquiv` of a derivation of an inverse
image into a derivation with values in a direct image, and then Equation (0619),
`AlgebraicGeometry.Space.derivationDirectImageEquiv`. Until those are written down the simply
transitive action of Tag 061C, `AlgebraicGeometry.Space.LiftDerivationAction`, lives over an
abstract sheaf of abelian groups rather than over
`AlgebraicGeometry.Space.liftActionSheaf`.

The *vanishing* half of step (II) — `H¹(T_étale, Hom(a^*Ω_{X/Y}, 𝒞_{T/T'})) = 0`, Tag 061J —
owes **one** thing; two further inputs one might expect are not needed at all.

Quasi-coherence of the acting sheaf is **unconditional for a smooth `q`**:
`AlgebraicGeometry.Space.isQuasicoherentOnSite_liftActionSheaf_of_isSmooth`
(`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheafQuasicoherentSmooth`) carries no
hypothesis.  It is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_liftActionSheaf_of_isFiniteLocallyFreeOnSite`
(from Tag 0GNC, with Tags 04CV, 03GA and 04CN all unconditional here) with its finite local
freeness discharged by Tag 0CK5,
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_sheafOfDifferentials_of_isSmooth`, together
with Tag 03DO for the clause Tag 03DL (2) along an arbitrary morphism of algebraic spaces —
which is proved, as
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_modulePullback`, beside the sibling clause
03DL (7), `AlgebraicGeometry.Space.isFinitePresentationOnSite_modulePullback`.

Nor does essential surjectivity of `(-)ᵃ` on the small étale site trace to the effectivity of
descent, Tag 023T.  That would be a **homonym**:
`AlgebraicGeometry.BigFppfOver.QuasicoherentIsEssImageAssociatedModule` is a predicate on the
*big fppf* site and is indeed open, but the predicate this argument needs is
`AlgebraicGeometry.SmallEtale.QuasicoherentIsEssImageAssociatedModule`, and that one is a
**theorem** — `AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule`
(`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit`), proved
unconditionally for an arbitrary scheme and registered against Tag 03DX clause (2).  The
counit route it uses goes through Tag 0GN7 at the Zariski site, not through Tag 023T.

So what Tag 061J still owes is exactly the hypothesis `h03DW` of
`AlgebraicGeometry.SmallEtale.subsingleton_sheafH_one_sheafHom_of_isLocallyProjective`
(`StacksFrontier.AlgebraicGeometry.EtaleCohomology.InternalHomAffineVanishing`): the vanishing of
the first cohomology of `𝓗om_𝒪(𝒪, 𝓖)` on the small étale site of an affine, that is Tag 03DW
with Tag 01XB, at the module universe of the internal hom.  The vanishing is proved for the
*associated* module of a quasi-coherent module on an affine scheme
(`AlgebraicGeometry.isZero_sheafCohomology_succ_smallEtaleAffine`, with Tag 03DW's small étale
half as `AlgebraicGeometry.smallEtaleQuasiCoherentGlobalCohomologyIso`), and what is missing is
its transport to that spelling.

Two things about that hypothesis, both recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.InternalHomAffineVanishing`.  First, the two
registered statements there ask the *target* `𝓖` to be quasi-coherent on the site, which is
Tag 061J's own hypothesis: for an arbitrary `𝓖` on the small étale site of an affine the first
cohomology of `𝓗om_𝒪(𝒪, 𝓖)` is not zero, so without that hypothesis `h03DW`
would be false rather than merely undischarged.  Second, of the three
spellings separating `h03DW` from the proved vanishing, the site one is closed — by
`Stacks.EtaleCohomology.ConstantTransport.subsingleton_H_boundedSmallEtale_of_smallEtale_sheaf`,
which transports the vanishing of `CategoryTheory.Sheaf.H` across a dense subsite for an
arbitrary abelian sheaf — while the module-universe one is **not** a transport along an
equivalence: `CategoryTheory.Sheaf.H` is an `Ext`-group *in the category*
`Sheaf J AddCommGrpCat.{t}`, and the universe-lifting functor on abelian groups is fully
faithful but not essentially surjective, so a discharge owes a comparison of `Sheaf.H` at the
two coefficient universes on top of the unit-source internal-hom isomorphism modelled by
`AlgebraicGeometry.Space.smallEtaleUnitCoevalIso`.

Step (II) is therefore isolated, for a general `f`, as the single proposition
`AlgebraicGeometry.Space.FormallySmoothEtaleDescent` of
`StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtInfinitesimalLifting`: descent of formal
smoothness along a surjective étale chart, from which
`AlgebraicGeometry.Space.formallySmooth_of_isSmooth` gives formal smoothness of every smooth
morphism of algebraic spaces.

The scheme-level analogue of the torsor argument, on the other hand, is carried out
in `StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmoothTag`;
`StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmooth` proves formal smoothness of a
smooth morphism of schemes only for an affine morphism,
`Stacks.Smooth.formallySmoothScheme_of_isAffineHom`, and for a formally unramified one,
`Stacks.Smooth.formallySmoothScheme_of_formallyUnramified`.

## References

* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
* [Stacks Project, Tag 039R](https://stacks.math.columbia.edu/tag/039R)
* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 03ZC](https://stacks.math.columbia.edu/tag/03ZC)
* [Stacks Project, Tag 049S](https://stacks.math.columbia.edu/tag/049S)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT)
* [Stacks Project, Tag 04CY](https://stacks.math.columbia.edu/tag/04CY)
* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
* [Stacks Project, Tag 061H](https://stacks.math.columbia.edu/tag/061H)
* [Stacks Project, Tag 061J](https://stacks.math.columbia.edu/tag/061J)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public section

open CategoryTheory Opposite Cardinal

universe u

namespace Stacks.Smooth

open _root_.AlgebraicGeometry

/-! ### Formal smoothness from one thickening of bounded size

An algebra is formally smooth as soon as *one* square-zero thickening of it admits a section,
namely the one cut out by the square of the kernel of a polynomial presentation. Since that
thickening has cardinality bounded by the data, formal smoothness is detected by thickenings
of bounded size. -/

/-- **Formal smoothness is detected by square-zero extensions of bounded cardinality.** If
every surjection `π : Q →ₐ[R] A` with square-zero kernel and `#Q < κ` admits a section, and
`#R`, `#A` and `ℵ₀` are below `κ`, then `A` is formally smooth over `R`.

Only one such `Q` is used, the quotient of the polynomial algebra `R[A]` by the square of the
kernel of the canonical presentation `R[A] ⟶ A`; a section of it is formal smoothness by
`Algebra.FormallySmooth.of_split`. Its cardinality is bounded by
`MvPolynomial.cardinalMk_le_max`. -/
theorem formallySmooth_of_exists_section_of_mk_lt {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] {κ : Cardinal.{u}} (hκ : ℵ₀ < κ) (hR : #R < κ) (hA : #A < κ)
    (H : ∀ (Q : Type u) [CommRing Q] [Algebra R Q] (π : Q →ₐ[R] A), Function.Surjective π →
      RingHom.ker π.toRingHom ^ 2 = ⊥ → #Q < κ →
        ∃ s : A →ₐ[R] Q, π.comp s = AlgHom.id R A) :
    Algebra.FormallySmooth R A := by
  set p : MvPolynomial A R →ₐ[R] A := MvPolynomial.aeval id with hp
  have hpsurj : Function.Surjective p := fun x => ⟨MvPolynomial.X x, by simp [hp]⟩
  have hqsurj : Function.Surjective p.kerSquareLift :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ hpsurj
  have hqsq : RingHom.ker p.kerSquareLift.toRingHom ^ 2 = ⊥ := by
    rw [AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square]
  have hcard : #(MvPolynomial A R ⧸ RingHom.ker p.toRingHom ^ 2) < κ := by
    refine lt_of_le_of_lt (Cardinal.mk_le_of_surjective Ideal.Quotient.mk_surjective) ?_
    refine lt_of_le_of_lt MvPolynomial.cardinalMk_le_max ?_
    simp only [sup_lt_iff]
    exact ⟨⟨hR, hA⟩, hκ⟩
  obtain ⟨s, hs⟩ := H _ p.kerSquareLift hqsurj hqsq hcard
  exact Algebra.FormallySmooth.of_split p s hs

/-! ### The lifting property over a bounded family of thickenings -/

/-- **A section of a square-zero extension of the sections over an affine chart, from the
lifting property.** Let `f : X ⟶ S` be a morphism of schemes, `V₀` an affine open of `S` and
`W` an affine open of `X` with `W ≤ f ⁻¹ᵁ V₀`. Let `θ : Q ⟶ Γ(X, W)` be a surjection with
square-zero kernel and `ψ : Γ(S, V₀) ⟶ Q` a factorization of `f.appLE V₀ W e` through it. If
the lifting problem for `f` along the thickening `Spec θ` is solvable, then `θ` has a section
compatible with `ψ`.

This is the geometric half of the infinitesimal criterion in the shape the ring-level
criterion consumes: the solution `τ` of the lifting problem maps into `W`, because the
thickening is surjective on points, and its sections over `W` are the required section of
`θ`. -/
theorem exists_appLE_section_of_exists_lift {X S : Scheme.{u}} (f : X ⟶ S) {V₀ : S.Opens}
    {W : X.Opens} (hV₀ : IsAffineOpen V₀) (hW : IsAffineOpen W) (e : W ≤ f ⁻¹ᵁ V₀)
    {Q : CommRingCat.{u}} (θ : Q ⟶ Γ(X, W)) (hθ : Function.Surjective θ.hom)
    (hθ2 : RingHom.ker θ.hom ^ 2 = ⊥) (ψ : Γ(S, V₀) ⟶ Q) (hψ : ψ ≫ θ = f.appLE V₀ W e)
    (H : ∀ (g : Spec Γ(X, W) ⟶ X) (k : Spec Q ⟶ S), g ≫ f = Spec.map θ ≫ k →
      ∃ τ : Spec Q ⟶ X, Spec.map θ ≫ τ = g ∧ τ ≫ f = k) :
    ∃ s : Γ(X, W) ⟶ Q, s ≫ θ = 𝟙 _ ∧ f.appLE V₀ W e ≫ s = ψ := by
  obtain ⟨g, hg, hgapp⟩ := exists_hom_appLE (X := X) (T' := Spec Γ(X, W)) hW
    (Scheme.ΓSpecIso Γ(X, W)).inv
  obtain ⟨k, hk, hkapp⟩ := exists_hom_appLE (X := S) (T' := Spec Q) hV₀
    (ψ ≫ (Scheme.ΓSpecIso Q).inv)
  have hsurjbase : Function.Surjective (Spec.map θ).base := specMap_base_surjective hθ hθ2
  have hgfV : (⊤ : (Spec Γ(X, W)).Opens) ≤ (g ≫ f) ⁻¹ᵁ V₀ := fun x _ => e (hg (Set.mem_univ x))
  have hikV : (⊤ : (Spec Γ(X, W)).Opens) ≤ (Spec.map θ ≫ k) ⁻¹ᵁ V₀ :=
    fun x _ => hk (Set.mem_univ ((Spec.map θ).base x))
  have hcomm : g ≫ f = Spec.map θ ≫ k := by
    refine hom_ext_of_appLE hV₀ hgfV hikV ?_
    rw [← Scheme.Hom.appLE_comp_appLE g f V₀ W ⊤ e hg, hgapp,
      ← Scheme.Hom.appLE_comp_appLE (Spec.map θ) k V₀ ⊤ ⊤ hk le_top, appLE_top_top, hkapp,
      Category.assoc, ← Scheme.ΓSpecIso_inv_naturality θ, ← Category.assoc, hψ]
  obtain ⟨τ, hτg, hτk⟩ := H g k hcomm
  have hτW : (⊤ : (Spec Q).Opens) ≤ τ ⁻¹ᵁ W := by
    intro x _
    obtain ⟨y, rfl⟩ := hsurjbase x
    show τ.base ((Spec.map θ).base y) ∈ W
    rw [← Scheme.Hom.comp_apply, hτg]
    exact hg (Set.mem_univ y)
  refine ⟨τ.appLE W ⊤ hτW ≫ (Scheme.ΓSpecIso Q).hom, ?_, ?_⟩
  · have h1 : τ.appLE W ⊤ hτW ≫ (Spec.map θ).appTop = (Scheme.ΓSpecIso Γ(X, W)).inv := by
      rw [appLE_appTop_of_lift hτg hτW hg, hgapp]
    rw [Category.assoc, ← Scheme.ΓSpecIso_naturality θ, ← Category.assoc, h1, Iso.inv_hom_id]
  · rw [← Category.assoc, appLE_comp_appLE_of_lift f hτk e hτW hk, hkapp, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]

/-- **The infinitesimal lifting criterion for smoothness, over thickenings of bounded size.**
A morphism of schemes of size below `κ` which is locally of finite presentation and has the
lifting property against first-order thickenings of affine schemes of size below `κ` is
smooth.

This is the form of the hard direction of [Stacks Project, Tag 02H6] that a lifting property
quantified over a *site* can supply: `Stacks.Smooth.smooth_of_formallySmoothScheme` needs the
lifting property for all affine schemes, which no big site provides. The reduction to bounded
size is `Stacks.Smooth.formallySmooth_of_exists_section_of_mk_lt`, which needs only the one
thickening of a polynomial presentation of the sections over an affine chart; that thickening
is the spectrum of a ring of cardinality at most `max ℵ₀ (max #Γ(S, V₀) #Γ(X, W))`, and both
of those are at most the size of the respective scheme by
`AlgebraicGeometry.Scheme.mk_sections_le_size`. -/
@[ega "0 19.0.1" "Implication, partial",
  ega "IV 17.3.1" "sufficiency direction",
  sga "1 III 5.5" "sufficiency"]
theorem smooth_of_exists_lift_of_size_lt {κ : Cardinal.{u}} (hκ : ℵ₀ < κ) {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFinitePresentation f] (hX : X.size < κ) (hS : S.size < κ)
    (H : ∀ (T T' : Scheme.{u}), IsAffine T → IsAffine T' → T.size < κ → T'.size < κ →
      ∀ i : T ⟶ T', Thickenings.IsFirstOrderThickening i →
      ∀ (g : T ⟶ X) (k : T' ⟶ S), g ≫ f = i ≫ k →
        ∃ τ : T' ⟶ X, i ≫ τ = g ∧ τ ≫ f = k) :
    AlgebraicGeometry.Smooth f := by
  have hspec : ∀ Rr : CommRingCat.{u}, #Rr < κ → (Spec Rr).size < κ := by
    intro Rr hRr
    rw [Scheme.size_of_isAffine]
    exact max_lt hκ (lt_of_le_of_lt (le_of_eq (Cardinal.mk_congr
      (Scheme.ΓSpecIso Rr).commRingCatIsoToRingEquiv.toEquiv)) hRr)
  rw [HasRingHomProperty.iff_appLE (P := @AlgebraicGeometry.Smooth) (Q := @RingHom.Smooth)]
  intro V₀ W e
  let instAlg : Algebra Γ(S, V₀.1) Γ(X, W.1) := (f.appLE V₀.1 W.1 e).hom.toAlgebra
  refine ⟨?_, HasRingHomProperty.appLE (@LocallyOfFinitePresentation) f inferInstance V₀ W e⟩
  refine formallySmooth_of_exists_section_of_mk_lt hκ
    (lt_of_le_of_lt (S.mk_sections_le_size V₀) hS)
    (lt_of_le_of_lt (X.mk_sections_le_size W) hX) ?_
  intro Q _ _ π hπ hπ2 hQ
  obtain ⟨s, hs₁, hs₂⟩ := exists_appLE_section_of_exists_lift f V₀.2 W.2 e
    (Q := CommRingCat.of Q) (CommRingCat.ofHom π.toRingHom) hπ hπ2
    (CommRingCat.ofHom (algebraMap Γ(S, V₀.1) Q))
    (CommRingCat.hom_ext (RingHom.ext fun r => π.commutes r))
    (fun g k hgk => H _ _ inferInstance inferInstance
      (hspec _ (lt_of_le_of_lt (X.mk_sections_le_size W) hX)) (hspec _ hQ) _
      (isFirstOrderThickening_specMap _ hπ hπ2) g k hgk)
  refine ⟨{ s.hom with commutes' := fun r => ?_ }, AlgHom.ext fun x => ?_⟩
  · have h2 := congr($(hs₂).hom r)
    simp only [CommRingCat.hom_ofHom] at h2
    exact h2
  · have h1 := congr($(hs₁).hom x)
    simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom, CommRingCat.hom_id,
      RingHom.id_apply] at h1
    exact h1

end Stacks.Smooth

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Formal smoothness -/

variable {B S hS}

/-- A section `ρ` of the scheme underlying `p : P ⟶ T'` which restricts to `σ₀` along `i` is the
image of a section of `p` in the site, because the inclusion of the site into schemes is fully
faithful. -/
private theorem exists_section_of_map_section {P T T' : BigFppfOver B S hS} (p : P ⟶ T')
    (i : T ⟶ T') (σ₀ : T ⟶ P) (ρ : (BigFppfOver.toScheme B S hS).obj T' ⟶
      (BigFppfOver.toScheme B S hS).obj P)
    (hρ₁ : ρ ≫ (BigFppfOver.toScheme B S hS).map p = 𝟙 _)
    (hρ₂ : (BigFppfOver.toScheme B S hS).map i ≫ ρ = (BigFppfOver.toScheme B S hS).map σ₀) :
    ∃ σ : T' ⟶ P, σ ≫ p = 𝟙 T' ∧ i ≫ σ = σ₀ := by
  have hρleft : B.inclusion.preimage ρ ≫ p.left = 𝟙 _ :=
    B.inclusion.map_injective (by
      rw [B.inclusion.map_comp, B.inclusion.map_preimage, B.inclusion.map_id]
      exact hρ₁)
  set σ : T' ⟶ P :=
    Over.homMk (B.inclusion.preimage ρ) (by
      rw [← Over.w p, ← Category.assoc, hρleft]
      simp)
  have hmapσ : (BigFppfOver.toScheme B S hS).map σ = ρ := B.inclusion.map_preimage ρ
  refine ⟨σ, (BigFppfOver.toScheme B S hS).map_injective ?_,
    (BigFppfOver.toScheme B S hS).map_injective ?_⟩
  · rw [(BigFppfOver.toScheme B S hS).map_comp, hmapσ, hρ₁,
      (BigFppfOver.toScheme B S hS).map_id]
  · rw [(BigFppfOver.toScheme B S hS).map_comp, hmapσ, hρ₂]

/-- **Stacks 061H.** Let `f : X ⟶ Y` be a formally smooth morphism of algebraic spaces over
`S` and let `a : U ⟶ X`, `b : V ⟶ Y` be étale scheme charts fitting in a commuting square over
`h : U ⟶ V`. Then every lifting problem for `h` along a square-zero closed immersion
`i : T ⟶ T'` of affine objects of the site has a solution.

The solution is produced in three steps. The lifting problem is pushed into `X` along the
chart, where formal smoothness of `f` solves it; the solution is pulled back to the chart,
which is legitimate because `a` is representable and étale, so the pullback of `a` along it is
an étale morphism of the site admitting a section over `T`, which extends over `T'` by
`Stacks.Smooth.formallySmoothScheme_of_etale`; and the resulting morphism `T' ⟶ U` is
compatible with the chart of `Y` because two morphisms `T' ⟶ V` which agree over `Y` and
restrict to the same morphism on `T` define two sections of the étale pullback of `b`, which
agree by `Stacks.Smooth.lift_unique`. -/
theorem exists_lift_of_formallySmooth {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hf : FormallySmooth f) {U V : BigFppfOver B S hS} {a : yoneda.obj U ⟶ X}
    {b : yoneda.obj V ⟶ Y} {h : U ⟶ V}
    (ha : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hsq : yoneda.map h ≫ b = a ≫ f) {T T' : BigFppfOver B S hS}
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    {i : T ⟶ T'} (hi : IsSquareZeroClosedImmersion B S hS i)
    {g : T ⟶ U} {k : T' ⟶ V} (hcomm : g ≫ h = i ≫ k) :
    ∃ τ : T' ⟶ U, i ≫ τ = g ∧ τ ≫ h = k := by
  have hthick : Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map i) := ⟨hi.1, hi.2⟩
  -- The lifting problem pushed into `X` and `Y`.
  have hsqx : (yoneda.map g ≫ a) ≫ f = yoneda.map i ≫ yoneda.map k ≫ b := by
    rw [Category.assoc, ← hsq, ← Functor.map_comp_assoc, hcomm, Functor.map_comp,
      Category.assoc]
  obtain ⟨z, hz₁, hz₂⟩ := hf T T' hT hT' i hi (yonedaEquiv (yoneda.map g ≫ a))
    (yonedaEquiv (yoneda.map k ≫ b))
    (calc f.app (op T) (yonedaEquiv (yoneda.map g ≫ a))
        = yonedaEquiv ((yoneda.map g ≫ a) ≫ f) := (yonedaEquiv_comp _ _).symm
      _ = yonedaEquiv (yoneda.map i ≫ yoneda.map k ≫ b) := congrArg _ hsqx
      _ = Y.map i.op (yonedaEquiv (yoneda.map k ≫ b)) := (yonedaEquiv_naturality _ _).symm)
  -- Its solution, as a morphism out of the representable presheaf of `T'`.
  set w : yoneda.obj T' ⟶ X := yonedaEquiv.symm z with hw
  have hw₁ : yoneda.map i ≫ w = yoneda.map g ≫ a := by
    rw [hw, yonedaEquiv_symm_naturality_left, hz₁, Equiv.symm_apply_apply]
  have hw₂ : w ≫ f = yoneda.map k ≫ b := by
    rw [hw, yonedaEquiv_symm_naturality_right, hz₂, Equiv.symm_apply_apply]
  -- Pull the chart `a` back along it; the pullback is étale over `T'`.
  have hetale : AlgebraicGeometry.Etale
      ((BigFppfOver.toScheme B S hS).map (ha.rep.snd w)) := ha.property_snd w
  set σ₀ : T ⟶ ha.rep.pullback w := ha.rep.lift' g i hw₁.symm with hσ₀
  obtain ⟨ρ, hρ₁, hρ₂⟩ := Stacks.Smooth.formallySmoothScheme_of_etale
    ((BigFppfOver.toScheme B S hS).map (ha.rep.snd w)) hT hT'
    ((BigFppfOver.toScheme B S hS).map i) hthick
    ((BigFppfOver.toScheme B S hS).map σ₀) (𝟙 _)
    (by rw [← Functor.map_comp, hσ₀, Functor.relativelyRepresentable.lift'_snd,
      Category.comp_id])
  -- The section of that étale morphism is a morphism of the site.
  obtain ⟨σ, hσsnd, hσi⟩ := exists_section_of_map_section (ha.rep.snd w) i σ₀ ρ hρ₁ hρ₂
  -- The solution of the original lifting problem.
  refine ⟨σ ≫ ha.rep.fst' w, ?_, ?_⟩
  · rw [← Category.assoc, hσi, hσ₀, Functor.relativelyRepresentable.lift'_fst]
  · -- Compatibility with the chart of `Y`, by uniqueness of sections of an étale morphism.
    have hτa : yoneda.map (σ ≫ ha.rep.fst' w) ≫ a = w := by
      rw [yoneda.map_comp, Category.assoc, (ha.rep.isPullback' w).w, ← Functor.map_comp_assoc,
        hσsnd]
      simp
    have hτb : yoneda.map ((σ ≫ ha.rep.fst' w) ≫ h) ≫ b
        = yoneda.map (𝟙 T') ≫ yoneda.map k ≫ b := by
      rw [yoneda.map_comp, Category.assoc, hsq, ← Category.assoc, hτa, hw₂]
      simp
    have hetaleb : AlgebraicGeometry.Etale
        ((BigFppfOver.toScheme B S hS).map (hb.rep.snd (yoneda.map k ≫ b))) :=
      hb.property_snd _
    set ω₁ : T' ⟶ hb.rep.pullback (yoneda.map k ≫ b) :=
      hb.rep.lift' ((σ ≫ ha.rep.fst' w) ≫ h) (𝟙 T') hτb with hω₁
    set ω₂ : T' ⟶ hb.rep.pullback (yoneda.map k ≫ b) :=
      hb.rep.lift' k (𝟙 T') (by simp) with hω₂
    have hiω : i ≫ ω₁ = i ≫ ω₂ := by
      refine Functor.relativelyRepresentable.hom_ext' hb.rep ?_ ?_
      · rw [Category.assoc, Category.assoc, hω₁, hω₂,
          Functor.relativelyRepresentable.lift'_fst,
          Functor.relativelyRepresentable.lift'_fst, ← Category.assoc, ← Category.assoc,
          hσi, hσ₀, Functor.relativelyRepresentable.lift'_fst, hcomm]
      · rw [Category.assoc, Category.assoc, hω₁, hω₂,
          Functor.relativelyRepresentable.lift'_snd,
          Functor.relativelyRepresentable.lift'_snd]
    have hω : ω₁ = ω₂ := by
      refine (BigFppfOver.toScheme B S hS).map_injective ?_
      refine Stacks.Smooth.lift_unique
        ((BigFppfOver.toScheme B S hS).map (hb.rep.snd (yoneda.map k ≫ b))) hthick
        (h := 𝟙 _) (a := (BigFppfOver.toScheme B S hS).map (i ≫ ω₁)) ?_ ?_ ?_ ?_
      · rw [← (BigFppfOver.toScheme B S hS).map_comp, hω₁,
          Functor.relativelyRepresentable.lift'_snd, (BigFppfOver.toScheme B S hS).map_id]
      · rw [← (BigFppfOver.toScheme B S hS).map_comp, hω₂,
          Functor.relativelyRepresentable.lift'_snd, (BigFppfOver.toScheme B S hS).map_id]
      · rw [← (BigFppfOver.toScheme B S hS).map_comp]
      · rw [← (BigFppfOver.toScheme B S hS).map_comp, hiω]
    calc (σ ≫ ha.rep.fst' w) ≫ h
        = ω₁ ≫ hb.rep.fst' (yoneda.map k ≫ b) := by
          rw [hω₁, Functor.relativelyRepresentable.lift'_fst]
      _ = k := by rw [hω, hω₂, Functor.relativelyRepresentable.lift'_fst]

/-- **Stacks 061H, in the vocabulary of schemes.** The lifting property of
`AlgebraicGeometry.Space.exists_lift_of_formallySmooth` for the scheme morphism underlying a
chart `h : U ⟶ V`, with the thickening presented as a first-order thickening `i : T ⟶ T'` of
affine schemes which the site contains, and with arbitrary morphisms `g`, `k` of schemes.

No compatibility of `g` and `k` with the structure morphisms to `S` is assumed: the thickening
is made a thickening *over* `S` by giving `T'` the structure morphism through `k` and `T` the
structure morphism through `g`, which are compatible precisely because the lifting square
commutes.

This is the statement that the implication `locally of finite presentation and formally
smooth → smooth` consumes. It is weaker than `Stacks.Smooth.FormallySmoothScheme` for the
chart morphism exactly in requiring `B.Contains T` and `B.Contains T'`. -/
theorem exists_lift_scheme_of_formallySmooth {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hf : FormallySmooth f) {U V : BigFppfOver B S hS} {a : yoneda.obj U ⟶ X}
    {b : yoneda.obj V ⟶ Y} {h : U ⟶ V}
    (ha : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hsq : yoneda.map h ≫ b = a ≫ f) {T T' : Scheme.{u}} (hT : IsAffine T) (hT' : IsAffine T')
    (hTB : B.Contains T) (hT'B : B.Contains T') {i : T ⟶ T'}
    (hi : Stacks.Thickenings.IsFirstOrderThickening i)
    {g : T ⟶ (BigFppfOver.toScheme B S hS).obj U}
    {k : T' ⟶ (BigFppfOver.toScheme B S hS).obj V}
    (hcomm : g ≫ (BigFppfOver.toScheme B S hS).map h = i ≫ k) :
    ∃ τ : T' ⟶ (BigFppfOver.toScheme B S hS).obj U,
      i ≫ τ = g ∧ τ ≫ (BigFppfOver.toScheme B S hS).map h = k := by
  -- Present the thickening and the lifting problem in the site over `S`.
  set g' : B.obj hTB ⟶ U.left := B.inclusion.preimage g with hg'
  set k' : B.obj hT'B ⟶ V.left := B.inclusion.preimage k with hk'
  set i' : B.obj hTB ⟶ B.obj hT'B := B.inclusion.preimage i with hi'
  have hik : i' ≫ k' = g' ≫ h.left := B.inclusion.map_injective (by
    rw [B.inclusion.map_comp, B.inclusion.map_comp, hg', hk', hi', B.inclusion.map_preimage,
      B.inclusion.map_preimage, B.inclusion.map_preimage]
    exact hcomm.symm)
  set Tₛ : BigFppfOver B S hS := Over.mk (g' ≫ U.hom)
  set T'ₛ : BigFppfOver B S hS := Over.mk (k' ≫ V.hom)
  set gₛ : Tₛ ⟶ U := Over.homMk g' rfl
  set kₛ : T'ₛ ⟶ V := Over.homMk k' rfl
  set iₛ : Tₛ ⟶ T'ₛ := Over.homMk i'
    (show i' ≫ k' ≫ V.hom = g' ≫ U.hom by
      rw [← Category.assoc, hik, Category.assoc, Over.w h])
  have hmapg : (BigFppfOver.toScheme B S hS).map gₛ = g :=
    B.inclusion.map_preimage (X := B.obj hTB) (Y := U.left) g
  have hmapk : (BigFppfOver.toScheme B S hS).map kₛ = k :=
    B.inclusion.map_preimage (X := B.obj hT'B) (Y := V.left) k
  have hmapi : (BigFppfOver.toScheme B S hS).map iₛ = i :=
    B.inclusion.map_preimage (X := B.obj hTB) (Y := B.obj hT'B) i
  have hiₛsq : IsSquareZeroClosedImmersion B S hS iₛ := ⟨hmapi ▸ hi.1, hmapi ▸ hi.2⟩
  have hcommₛ : gₛ ≫ h = iₛ ≫ kₛ := (BigFppfOver.forget B S hS).map_injective (by
    rw [(BigFppfOver.forget B S hS).map_comp, (BigFppfOver.forget B S hS).map_comp]
    exact hik.symm)
  obtain ⟨τ, hτ₁, hτ₂⟩ := exists_lift_of_formallySmooth hf ha hb hsq
    (T := Tₛ) (T' := T'ₛ) hT hT' hiₛsq hcommₛ
  refine ⟨(BigFppfOver.toScheme B S hS).map τ, ?_, ?_⟩
  · rw [← hmapi, ← (BigFppfOver.toScheme B S hS).map_comp, hτ₁, hmapg]
  · rw [← (BigFppfOver.toScheme B S hS).map_comp, hτ₂, hmapk]

/-- **Stacks 04AM, the implication towards smoothness.** A morphism of algebraic spaces over
`S` which is locally of finite presentation and formally smooth is smooth.

Smoothness of `f` is a property of its étale charts, so there is nothing to descend: a chart
`h : U ⟶ V` is locally of finite presentation by hypothesis, and
`AlgebraicGeometry.Space.exists_lift_scheme_of_formallySmooth` solves every lifting problem for
it along a first-order thickening of affine schemes *contained in the site*. That is exactly
the hypothesis of `Stacks.Smooth.smooth_of_exists_lift_of_size_lt`, which upgrades it to
smoothness: the only thickening the criterion needs is the spectrum of a polynomial
presentation of the sections over an affine chart, and the site contains it. -/
@[stacks 04AM "condition (2) implies condition (1)"]
theorem isSmooth_of_isLocallyOfFinitePresentation_of_formallySmooth
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hlfp : IsLocallyOfFinitePresentation B S hS f) (hf : FormallySmooth f) :
    IsSmooth B S hS f := by
  intro U V a b h ha hb hsq
  have hLFP : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map h) :=
    hlfp U V a b h ha hb hsq
  exact Stacks.Smooth.smooth_of_exists_lift_of_size_lt B.aleph0_lt_cutoff _
    U.left.property V.left.property
    fun T T' hT hT' hTB hT'B i hi g k hcomm =>
      exists_lift_scheme_of_formallySmooth hf ha hb hsq hT hT' hTB hT'B hi hcomm

/-- **Stacks 04AM, the implication from smoothness, for a representable morphism.** A smooth
representable morphism of algebraic spaces over `S` is locally of finite presentation and
formally smooth.

Local finite presentation is Tag 04AJ. For formal smoothness, smoothness of a representable
morphism is smoothness of each of its base changes to an object of the site by Tag 03MJ, so the
base change of `f` along a section `y` of the target over the thickened test object is a smooth
morphism of schemes; the scheme case Tag 02H6 extends the section of that base change cut out
by the given section of `X` over the test object, and the extension is a morphism of the site
because the inclusion of the site into schemes is fully faithful. -/
@[stacks 04AM "condition (1) implies condition (2), for a representable morphism"]
theorem isLocallyOfFinitePresentation_and_formallySmooth_of_isSmooth
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hrep : yoneda.relativelyRepresentable f) (hf : IsSmooth B S hS f) :
    IsLocallyOfFinitePresentation B S hS f ∧ FormallySmooth f := by
  refine ⟨isLocallyOfFinitePresentation_of_isSmooth B S hS hf, ?_⟩
  have : MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.Smooth.{u} : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  have hrel : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Smooth.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f :=
    (holdsOnEveryEtaleChart_iff_relative B S hS
      (@AlgebraicGeometry.Smooth.{u} : MorphismProperty Scheme.{u})
      AlgebraicGeometry.Smooth.isEtaleLocalOnSourceAndTarget hX hY f hrep).mp hf
  intro T T' hT hT' i hi x y hxy
  -- The base change of `f` along `y`, a smooth morphism of schemes over `T'`.
  set y' : yoneda.obj T' ⟶ Y := yonedaEquiv.symm y with hy'
  have hsm : AlgebraicGeometry.Smooth
      ((BigFppfOver.toScheme B S hS).map (hrel.rep.snd y')) := hrel.property_snd y'
  have hthick : Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map i) := ⟨hi.1, hi.2⟩
  -- The section of that base change over `T` cut out by `x`.
  have hw : yonedaEquiv.symm x ≫ f = yoneda.map i ≫ y' := by
    rw [hy', yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_left, hxy]
  set σ₀ : T ⟶ hrel.rep.pullback y' := hrel.rep.lift (yonedaEquiv.symm x) i hw
  have hσ₀snd : σ₀ ≫ hrel.rep.snd y' = i := hrel.rep.lift_snd (yonedaEquiv.symm x) i hw
  have hσ₀fst : yoneda.map σ₀ ≫ hrel.rep.fst y' = yonedaEquiv.symm x :=
    hrel.rep.lift_fst (yonedaEquiv.symm x) i hw
  -- Its extension over `T'`, by the scheme case.
  obtain ⟨ρ, hρ₁, hρ₂⟩ := Stacks.Smooth.formallySmoothScheme_of_smooth
    ((BigFppfOver.toScheme B S hS).map (hrel.rep.snd y')) hT hT'
    ((BigFppfOver.toScheme B S hS).map i) hthick
    ((BigFppfOver.toScheme B S hS).map σ₀) (𝟙 _)
    (by rw [← Functor.map_comp, hσ₀snd, Category.comp_id])
  -- The extension is a morphism of the site.
  obtain ⟨σ, hσsnd, hσi⟩ := exists_section_of_map_section (hrel.rep.snd y') i σ₀ ρ hρ₁ hρ₂
  -- The solution of the lifting problem it carries.
  refine ⟨yonedaEquiv (yoneda.map σ ≫ hrel.rep.fst y'), ?_, ?_⟩
  · rw [yonedaEquiv_naturality, ← Functor.map_comp_assoc, hσi, hσ₀fst,
      Equiv.apply_symm_apply]
  · rw [← yonedaEquiv_comp, Category.assoc, (hrel.rep.isPullback y').w,
      ← Functor.map_comp_assoc, hσsnd, CategoryTheory.Functor.map_id, Category.id_comp, hy',
      Equiv.apply_symm_apply]

/-! ### Smoothness at a point -/

section Chart

variable (B S hS) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A smooth open subspace of the source witnesses smoothness at each of its points. -/
theorem isSmoothAt_of_isOpenSubspace {f : X ⟶ Y} (U : Subfunctor X)
    (hU : IsOpenSubspace B S hS U) (hf : IsSmooth B S hS (U.ι ≫ f))
    (x' : points B S hS U.toFunctor) :
    IsSmoothAt B S hS f (pointsMap B S hS U.toFunctor U.ι x') :=
  ⟨U, hU, x', rfl, hf⟩

/-- Smoothness at a point, with the point condition read as a membership in the image of the
open subspace on points. -/
theorem IsSmoothAt.exists_mem_range_pointsMap {f : X ⟶ Y} {x : points B S hS X}
    (h : IsSmoothAt B S hS f x) :
    ∃ U : Subfunctor X, IsOpenSubspace B S hS U ∧ IsSmooth B S hS (U.ι ≫ f) ∧
      x ∈ Set.range (pointsMap B S hS U.toFunctor U.ι) := by
  obtain ⟨U, hU, x', hx', hf⟩ := h
  exact ⟨U, hU, hf, x', hx'⟩

end Chart

end AlgebraicGeometry.Space

end
