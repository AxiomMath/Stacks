module

public import StacksFrontier.AlgebraicGeometry.Smooth.LiftTorsor
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartLiftTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsAffineHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheaf

/-!
# The action of chart derivations on the sheaf of lifts

Let `B`, `X'` and `Y` be algebraic spaces over a scheme `S`, let `X ⊆ X'` be a subspace and let
`a : X ⟶ Y` be a morphism over `B`.  The lifts of `a` over the étale scheme charts of `X'` form
the sheaf `AlgebraicGeometry.Space.liftsSubfunctor` of [Stacks Project, Tag 061D], and the
`𝒪_X`-module `SheafHom_{𝒪_X}(a^*Ω_{Y/B}, 𝒞_{X/X'})` that the source makes act on it is
`AlgebraicGeometry.Space.liftActionSheaf`.  This file constructs that action **on the sections
over an étale scheme chart**, which is where it lives: a section of the sheaf of lifts over a
chart is a morphism out of a *scheme*, so the translated structure map `(a')^♯ + d_{Y/B} ∘ θ`
is read back as a morphism by `Spec` and not by [Stacks Project, Tag 04KL].

The datum the action is defined against is a *chart presentation* of the lifting problem,
`AlgebraicGeometry.Space.ChartLiftPresentation`: an affine étale chart `U'` of `X'`, the
square-zero closed immersion `U = X ×_{X'} U' ⟶ U'` it carries, a commuting square of affine
charts `W ⟶ V` of `q : Y ⟶ B`, and a factorization of the given lift through `W`.  The base
morphism `U' ⟶ V` of the lifting problem is not part of the datum: the lift lies over `B`, so
the composite of its factorization with the chart morphism is the only candidate, and
`AlgebraicGeometry.Space.ChartLiftPresentation.baseSq` is then a theorem.  Over such a
presentation the translation is the one of
`StacksFrontier.AlgebraicGeometry.Smooth.LiftTorsor`, carried out in the chart and read back as a
morphism of the big fppf site.

## Main definitions

* `AlgebraicGeometry.Space.ChartLiftPresentation`: the chart presentation of a lifting problem
  at an étale scheme chart of `X'`.
* `AlgebraicGeometry.Space.ChartLiftPresentation.Deriv`: the derivations acting on the lifts
  presented by the chart — the `Γ(V, ⊤)`-derivations of `Γ(W, ⊤)` with values in the conormal
  module `𝒞_{U/U'}` of the chart thickening, in exactly the module structures that
  `Stacks.Smooth.existsUnique_linearMap_comp_pullbackD_of_module` identifies with the
  `Γ(U, ⊤)`-linear maps `Γ(a^*Ω_{W/V}, ⊤) ⟶ 𝒞_{U/U'}`, that is with the sections of the acting
  sheaf at the chart.
* `AlgebraicGeometry.Space.ChartLiftPresentation.translateHom`: the translated structure map
  `(a')^♯ + d ∘ δ` on global sections of the target chart.
* `AlgebraicGeometry.Space.ChartLiftPresentation.translateScheme` and
  `AlgebraicGeometry.Space.ChartLiftPresentation.translate`: the translate itself, as a
  morphism of schemes and as a morphism of the big fppf site.
* `AlgebraicGeometry.Space.ChartLiftPresentation.translateSection`: the translate as a section
  of `AlgebraicGeometry.Space.liftsSubfunctor` over the chart, which is the action itself.
* `AlgebraicGeometry.Space.ChartLiftPresentation.ActionSection`: the sections at the chart of
  the acting sheaf `SheafHom_{𝒪_X}(a^*Ω_{Y/B}, 𝒞_{X/X'})` in their Zariski form — the
  `Γ(U, ⊤)`-linear maps `Γ(a^*Ω_{W/V}, ⊤) ⟶ 𝒞_{U/U'}` — with
  `AlgebraicGeometry.Space.ChartLiftPresentation.derivOfActionSection` the derivation `θ ∘ d`
  attached to such a section, Equation [Stacks Project, Tag 0619] at the chart, and
  `AlgebraicGeometry.Space.ChartLiftPresentation.translateActionSection` the action of such a
  section on the sheaf of lifts.

## Main results

* `AlgebraicGeometry.Space.ChartLiftPresentation.isChartLift_translate`: **the translate of a
  lift is again a lift**, so the action lands in the sheaf of lifts.  It lies over `B` because
  it lies over the base chart, and it agrees with `a` on `X ×_{X'} U'` because every test
  object landing in `X` factors through the closed subscheme of the chart, where the translate
  agrees with the original lift.
* `AlgebraicGeometry.Space.ChartLiftPresentation.liftDiffDerivation_translate`: **the
  characterising equation**.  The difference of the translate from the presented lift, in the
  sense of `Stacks.Smooth.liftDiffDerivation`, is the derivation that was used to translate.
* `AlgebraicGeometry.Space.ChartLiftPresentation.translateScheme_zero` and
  `AlgebraicGeometry.Space.ChartLiftPresentation.translateHom_add`: the action laws, that the
  zero derivation fixes the presented lift and that translating by a sum is translating the
  translate.
* `AlgebraicGeometry.Space.ChartLiftPresentation.liftDiffDerivation_translate_translate`: the
  difference of two translates is the difference of the two derivations.
* `AlgebraicGeometry.Space.ChartLiftPresentation.translateSection_injective`: **the action is
  free on the sheaf of lifts**, granted that the chart of `Y` is étale — two derivations whose
  translates have the same image in `Y` are equal.  This is where the chart of `Y` has to be
  étale: the two translates agree on the closed subscheme of the chart, so formal étaleness,
  [Stacks Project, Tag 04AL], identifies them already in the chart.
* `AlgebraicGeometry.Space.ChartLiftPresentation.translateScheme_injective`: **the action is
  free**.
* `AlgebraicGeometry.Space.ChartLiftPresentation.exists_translateScheme_eq`: **the action is
  transitive on the solutions presented by the chart** — every morphism of schemes solving the
  lifting problem at the chart is a translate of the presented lift.  Together with freeness
  this is the simple transitivity of the action at a chart; it is proved here without the
  structure-sheaf half of [Stacks Project, Tag 05ZM], because in a chart the two lifts being
  compared have structure maps into one and the same ring `Γ(U', ⊤)`.
* `AlgebraicGeometry.Space.ChartLiftPresentation.exists_translateSection_eq`: **transitivity on
  the sheaf of lifts**, granted that both charts are étale — every section of
  `AlgebraicGeometry.Space.liftsSubfunctor` over the chart which comes from a morphism into the
  chart of `Y` is a translate.  Two repairs are needed before the chart-level statement
  applies, and the two charts being étale supplies both: [Stacks Project, Tag 04AL],
  `AlgebraicGeometry.Space.exists_chart_hom_of_restrict_app_eq`, rechooses the morphism so that
  it restricts to the closed subscheme as the presented lift does, and formal étaleness of the
  chart of `B` puts the rechosen morphism over the base morphism of the presentation.  With
  `translateSection_injective` this is the **simple transitivity of the action on the sections
  over an étale scheme chart**, among the lifts presented by the chart.
* `AlgebraicGeometry.Space.ChartLiftPresentation.derivOfActionSection_bijective`: **the acting
  group at the chart is exactly the sections of the acting sheaf there** — `θ ↦ θ ∘ d` is a
  bijection from those linear maps onto the derivations.  This is
  `Stacks.Smooth.existsUnique_linearMap_comp_pullbackD_of_module` at the presentation, and it
  is what makes `translateActionSection` an action of the acting sheaf's sections rather than of
  an auxiliary group;
  `AlgebraicGeometry.Space.ChartLiftPresentation.translateActionSection_injective` and
  `AlgebraicGeometry.Space.ChartLiftPresentation.exists_translateActionSection_eq` are freeness
  and transitivity for it.
* `AlgebraicGeometry.Space.exists_chartLiftPresentation`: **a presentation exists**, so none of
  the statements above is empty.  Over an affine étale chart of a first-order thickening, every
  morphism into an affine chart of `Y` sitting in a commuting square over an affine chart of `B`
  whose image in `Y` is a lift of `a` is presented by one; the square-zero chart datum is
  supplied by `AlgebraicGeometry.Space.exists_squareZeroChart_of_isFirstOrderThickening` and the
  base morphism is forced.

## Implementation notes

The target chart is required to be affine and nothing else: no étaleness of `w : W ⟶ Y` or of
`v : V ⟶ B` is used, so the statements below hold for any commuting square of affine charts
through which the lift factors.  Étaleness is what the comparison with `liftActionSheaf` needs
(see below), not what the action needs.

Reading the translated structure map back as a morphism of schemes is
`Stacks.Smooth.homEquivOfIsAffine`, the unit-counit computation for `Γ ⊣ Spec`; recognising
that morphism as a morphism of the *site* is `AlgebraicGeometry.BigFppfOver.homOfCompEq`,
applied to the factorization through the base chart, since a morphism which lies over `V` lies
over `S`.

The square `U = X ×_{X'} U'` is asked to be cartesian as a square of presheaves,
`AlgebraicGeometry.Space.ChartLiftPresentation.isPullback`.  That is what turns the chart-level
agreement `i ≫ (θ · a') = i ≫ a'` into the pointwise clause of
`AlgebraicGeometry.Space.IsChartLift`: a test object of the site mapping into `U'` and landing
in `X` factors through `U`, uniquely, and there the two morphisms agree.  Such a square exists
through every point and over every affine étale chart of a first-order thickening, by
`AlgebraicGeometry.Space.exists_squareZeroChart_of_isFirstOrderThickening`.

## What this does not do

The acting object here is `AlgebraicGeometry.Space.ChartLiftPresentation.ActionSection`, the
sections at the chart of the acting sheaf in their **Zariski** form: the `Γ(U, ⊤)`-linear maps
`Γ(a^*Ω_{W/V}, ⊤) ⟶ 𝒞_{U/U'}`.  What is still owed is the comparison of those with the sections
of the small-étale internal hom `AlgebraicGeometry.Space.liftActionSheaf` itself.  Its two
geometric halves are proved in this tree, [Stacks Project, Tag 04CU] as
`AlgebraicGeometry.Space.sheafOfDifferentialsEtaleChartComparison` and
[Stacks Project, Tag 04CS] as
`AlgebraicGeometry.Space.sheafOfDifferentialsSchemeSiteComparison`.

Two further pieces of that comparison are now available and are **not** what is missing.

* The reading of a section of `AlgebraicGeometry.Space.smallEtaleInternalHom` on a chart is
  `AlgebraicGeometry.Space.smallEtaleInternalHomChartEval`
  (`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHomChartSections`), at the acting
  sheaf `AlgebraicGeometry.Space.liftActionSheafChartEval`; it is additive and `Γ(U, ⊤)`-linear
  in the section.
* The identification of the sections of the conormal module of the chart thickening with
  `RingHom.ker i^♯` is `AlgebraicGeometry.Space.conormalChartKerEquiv`
  (`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalChartSections`), for **any**
  presentation of the chart thickening by a cartesian square, which is what the presentations
  below carry — `AlgebraicGeometry.Space.definingIdealAt_eq_ker_of_isPullback` is the clause
  about `AlgebraicGeometry.Space.ChartLiftPresentation.conormal` itself.
  `AlgebraicGeometry.Space.liftActionSheafChartKerEval`
  (`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftActionSheafChartSections`) composes the
  two: a section of the acting sheaf over the base-changed chart, applied to a section of
  `a^*Ω_{Y/B}` there, lands in `RingHom.ker i^♯`, which is this file's `conormal`.

**What is genuinely missing is the source comparison.**  `ActionSection` takes the Zariski
`Γ(a^*Ω_{W/V}, ⊤)` of the chart square as its source and the acting sheaf takes the sections of
the small-étale `a^*Ω_{Y/B}` over the chart; both geometric comparisons above are isomorphisms of
*sheaves*.  Their composite, in the spelling a presentation below produces, **is now written
down**: `AlgebraicGeometry.Space.chartCompositeDifferentialsAssociatedIso`
(`StacksFrontier.AlgebraicGeometry.Spaces.ChartSquareDifferentialsAssociated`) exhibits
`c^*Ω_{Y/B}`, for a morphism `c` of represented algebraic spaces factoring through the chart of
`Y`, as the associated module of the Zariski `a^*Ω_{W/V}`.

Turning an isomorphism of associated modules into a bijection of *morphisms* carries **nothing**
either.  It is not the slice at an affine chart and it is not the fpqc sheaf condition of
[Stacks Project, Tag 03DT]: Tag 03DT is
proved and registered as `AlgebraicGeometry.quasiCoherentPresheaf_isSheaf_fpqc'` with its slice
instance `AlgebraicGeometry.Space.SmallEtale.isSheaf_sliceAssociatedPresheaf_of_isQuasicoherent`,
and no slice is needed at all — the small étale half of [Stacks Project, Tag 0GN7] holds over an
arbitrary scheme with no hypothesis,
`AlgebraicGeometry.SmallEtale.fullyFaithfulAssociatedModuleQcoh'`, whose hom-set form on a
represented algebraic space is
`AlgebraicGeometry.Space.bijective_representedAssociatedModule_map`
(`StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModuleFullyFaithful`).

The Zariski side is available too: morphisms of quasi-coherent modules on an affine scheme *are*
the `Γ(U, ⊤)`-linear maps of their global sections,
`Stacks.AlgebraicGeometry.ModuleLimits.bijective_appTopₗ`, and composed with the previous
statement that gives
`AlgebraicGeometry.Space.representedAssociatedModuleHomEquivLinearMap` — the morphisms
`Mᵃ ⟶ Nᵃ` on the small étale site of a represented algebraic space with affine underlying scheme
are exactly `ActionSection`'s shape.

**The source comparison is now complete, and so is the whole identification.**  The sections of
`AlgebraicGeometry.Space.liftActionSheaf` at a chart are morphisms of the *restrictions to the
slice* at that chart, while the isomorphisms above are about the inverse image to the small étale
site of the chart space; the two are matched by [Stacks Project, Tag 04M0] in the form
`AlgebraicGeometry.Space.chartSmallEtaleRestrictionHomEquiv` together with Equation
[Stacks Project, Tag 03LW] in the form
`AlgebraicGeometry.Space.chartModuleRestrictionIsoChartSmallEtaleRestriction`, packaged as
`AlgebraicGeometry.Space.smallEtaleInternalHomChartPullbackHomEquiv`.  The finished
identification is
`AlgebraicGeometry.Space.ChartLiftPresentation.actionSectionEquiv`
(`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftActionSheafActionSection`): granted that
the two charts of `q` are étale — which is what [Stacks Project, Tag 04CU] needs and what none of
the statements below needs — a section of the acting sheaf over the étale chart of `X` presented
by a `AlgebraicGeometry.Space.ChartLiftPresentation` is exactly an
`AlgebraicGeometry.Space.ChartLiftPresentation.ActionSection`.

`AlgebraicGeometry.Space.smallEtaleRingedSitePostcompOverEquivalence` is **not** what matches the
two descriptions.  That is the *slice-to-slice* comparison for an étale morphism of algebraic
spaces; what is needed is the slice at a chart against the small étale site of the chart *space*,
which is `AlgebraicGeometry.Space.SmallEtale.chartLocalizationEquivalence`.

The action's **compatibility with restriction** is
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ChartLiftRestriction`: a presentation restricts
along a morphism `V' ⟶ U'` of étale charts of `X'`
(`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction`, which exists over every affine
étale chart of a first-order thickening), the acting derivations and the acting sections restrict
with it, and the translate of a restriction is the restriction of the translate
(`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.map_translateSection` and
`…map_translateActionSection`).  The identification of the acting group with the acting sheaf's
sections is additive but is **not** yet known to be natural in the chart; that is stated as
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.IsActionSectionRestrictionNatural`.

No `@[stacks 04AM]` attribute is carried: the general direction of that tag needs the whole
torsor argument, which is isolated as
`AlgebraicGeometry.Space.FormallySmoothEtaleDescent` of
`StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtInfinitesimalLifting`.  What is built here is one
input to it.

## References

* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 04AL](https://stacks.math.columbia.edu/tag/04AL)
* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
variable {B X' Y : AlgebraicSpaces C S hS}


/-- A morphism of schemes factoring a morphism of the site through another one is a morphism of
the site: its compatibility with the structure morphisms to `S` is inherited. -/
theorem comp_inclusion_map_hom_of_comp {T W V : BigFppfOver C S hS}
    (v : (BigFppfOver.toScheme C S hS).obj T ⟶ (BigFppfOver.toScheme C S hS).obj W) (k : W ⟶ V)
    (g : T ⟶ V)
    (h : v ≫ (BigFppfOver.toScheme C S hS).map k = (BigFppfOver.toScheme C S hS).map g) :
    v ≫ C.inclusion.map W.hom = C.inclusion.map T.hom := by
  have hW : C.inclusion.map W.hom = C.inclusion.map k.left ≫ C.inclusion.map V.hom := by
    rw [← Functor.map_comp]
    exact congrArg _ (Over.w k).symm
  have hT : C.inclusion.map T.hom = C.inclusion.map g.left ≫ C.inclusion.map V.hom := by
    rw [← Functor.map_comp]
    exact congrArg _ (Over.w g).symm
  rw [hW, hT, ← Category.assoc]
  exact congrArg (· ≫ C.inclusion.map V.hom) h


/-- A section of a presheaf represented by an object of the site, read at a test object, is the
composite of the corresponding morphism of presheaves with the chart. -/
theorem app_eq_yonedaEquiv_comp {Z : BigFppfOver C S hS}
    {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (α : yoneda.obj Z ⟶ F)
    {W₀ : BigFppfOver C S hS} (k : W₀ ⟶ Z) :
    α.app (op W₀) k = yonedaEquiv (yoneda.map k ≫ α) := by
  rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]

/-- **A chart presentation of a lifting problem.**  The data of an affine étale scheme chart
`U'` of `X'` over which a lift of `a` is presented by a morphism into an affine chart `W` of
`Y`: the square-zero closed immersion `U = X ×_{X'} U' ⟶ U'` cut out by `X`, a commuting square
of affine charts `W ⟶ V` of `q : Y ⟶ B`, and a factorization `U' ⟶ W` of the lift through the
chart of `Y`.  The base morphism `U' ⟶ V` is the composite of that factorization with the chart
morphism, `AlgebraicGeometry.Space.ChartLiftPresentation.baseHom`, and not a field.

No étaleness of the charts `W ⟶ Y` and `V ⟶ B` is required: only affineness of the three
schemes `U'`, `W` and `V` and the commutativity of the squares are used. -/
structure ChartLiftPresentation (p : X' ⟶ B) (q : Y ⟶ B) {X : Subfunctor X'.1}
    (a : X.toFunctor ⟶ Y.1) (U' : SmallEtale C S hS X'.1) where
  /-- sub -/
  sub : BigFppfOver C S hS
  /-- incl -/
  incl : sub ⟶ (SmallEtale.toOver C S hS X'.1).obj U'
  /-- subChart -/
  subChart : yoneda.obj sub ⟶ X.toFunctor
  /-- isPullback -/
  isPullback : IsPullback (yoneda.map incl) subChart U'.1.hom X.ι
  /-- squareZero -/
  squareZero : IsSquareZeroClosedImmersion C S hS incl
  /-- ambient affine -/
  isAffineAmbient :
    IsAffine ((BigFppfOver.toScheme C S hS).obj ((SmallEtale.toOver C S hS X'.1).obj U'))
  /-- target chart object -/
  tgt : BigFppfOver C S hS
  /-- target affine -/
  isAffineTgt : IsAffine ((BigFppfOver.toScheme C S hS).obj tgt)
  /-- base chart object -/
  bse : BigFppfOver C S hS
  /-- base affine -/
  isAffineBse : IsAffine ((BigFppfOver.toScheme C S hS).obj bse)
  /-- target chart -/
  tgtChart : yoneda.obj tgt ⟶ Y.1
  /-- base chart -/
  bseChart : yoneda.obj bse ⟶ B.1
  /-- chart morphism -/
  chartHom : tgt ⟶ bse
  /-- the chart square over `q` -/
  chartSq : yoneda.map chartHom ≫ bseChart = tgtChart ≫ q.hom
  /-- the presentation of the lift -/
  liftHom : (SmallEtale.toOver C S hS X'.1).obj U' ⟶ tgt
  /-- the presented morphism is a lift -/
  isLift : IsChartLift C S hS p q a U' (yoneda.map liftHom ≫ tgtChart)


namespace ChartLiftPresentation

variable {C S hS} {p : X' ⟶ B} {q : Y ⟶ B} {X : Subfunctor X'.1} {a : X.toFunctor ⟶ Y.1}
  {U' : SmallEtale C S hS X'.1} (P : ChartLiftPresentation C S hS p q a U')

/-- The ambient scheme of the chart. -/
abbrev ambientScheme (_P : ChartLiftPresentation C S hS p q a U') : Scheme.{u} :=
  (BigFppfOver.toScheme C S hS).obj ((SmallEtale.toOver C S hS X'.1).obj U')

/-- The closed subscheme of the chart. -/
abbrev subScheme : Scheme.{u} := (BigFppfOver.toScheme C S hS).obj P.sub

/-- The target chart as a scheme. -/
abbrev tgtScheme : Scheme.{u} := (BigFppfOver.toScheme C S hS).obj P.tgt

/-- The base chart as a scheme. -/
abbrev bseScheme : Scheme.{u} := (BigFppfOver.toScheme C S hS).obj P.bse

/-- The thickening of schemes underlying the chart. -/
abbrev inclScheme : P.subScheme ⟶ P.ambientScheme := (BigFppfOver.toScheme C S hS).map P.incl

/-- The chart morphism as a morphism of schemes. -/
abbrev chartHomScheme : P.tgtScheme ⟶ P.bseScheme := (BigFppfOver.toScheme C S hS).map P.chartHom

/-- The base morphism of the lifting problem: the presented lift followed by the chart
morphism.  It is not extra data — the lift lies over `B`, so its composite with the chart
morphism is the only morphism into the base chart the presentation could use. -/
def baseHom : (SmallEtale.toOver C S hS X'.1).obj U' ⟶ P.bse := P.liftHom ≫ P.chartHom

/-- The presented lift lies over the base morphism, by construction. -/
theorem liftSq : P.liftHom ≫ P.chartHom = P.baseHom := rfl

/-- The base morphism presents the structure morphism of the chart over `B`. -/
theorem baseSq : yoneda.map P.baseHom ≫ P.bseChart = U'.1.hom ≫ p.hom := by
  rw [baseHom, Functor.map_comp, Category.assoc, P.chartSq, ← Category.assoc]
  exact P.isLift.1

/-- The base morphism of the lifting problem, as a morphism of schemes. -/
abbrev baseHomScheme : P.ambientScheme ⟶ P.bseScheme := (BigFppfOver.toScheme C S hS).map P.baseHom

/-- The presented lift, as a morphism of schemes. -/
abbrev liftHomScheme : P.ambientScheme ⟶ P.tgtScheme := (BigFppfOver.toScheme C S hS).map P.liftHom

/-- The reduction of the presented lift to the closed subscheme. -/
abbrev redHomScheme : P.subScheme ⟶ P.tgtScheme :=
  (BigFppfOver.toScheme C S hS).map (P.incl ≫ P.liftHom)

/-- The conormal module of the chart thickening: the kernel of its map of global sections. -/
abbrev conormal : Type u := RingHom.ker P.inclScheme.appTop.hom

/-- The thickening of schemes underlying the chart is a first-order thickening. -/
theorem isFirstOrderThickening : Stacks.Thickenings.IsFirstOrderThickening P.inclScheme :=
  P.squareZero

/-- The reduction of the lift followed by the chart morphism equals the thickening followed by
the base morphism. -/
theorem redHomScheme_comp : P.redHomScheme ≫ P.chartHomScheme = P.inclScheme ≫ P.baseHomScheme := by
  rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, P.liftSq]

/-- The lift followed by the chart morphism is the base morphism, as morphisms of schemes. -/
theorem liftHomScheme_comp : P.liftHomScheme ≫ P.chartHomScheme = P.baseHomScheme := by
  rw [← Functor.map_comp, P.liftSq]

/-- The thickening followed by the lift is the reduction of the lift. -/
theorem incl_comp_liftHomScheme : P.inclScheme ≫ P.liftHomScheme = P.redHomScheme :=
  (Functor.map_comp _ _ _).symm


/-- The whole target chart lies over the whole base chart. -/
theorem tgt_le_preimage : (⊤ : P.tgtScheme.Opens) ≤ P.chartHomScheme ⁻¹ᵁ (⊤ : P.bseScheme.Opens) :=
  le_top

/-- The reduction of the lift maps the subscheme into the target chart. -/
theorem sub_le_preimage : (⊤ : P.subScheme.Opens) ≤ P.redHomScheme ⁻¹ᵁ (⊤ : P.tgtScheme.Opens) :=
  le_top

/-- The base morphism maps the ambient scheme into the base chart. -/
theorem ambient_le_preimage_bse :
    (⊤ : P.ambientScheme.Opens) ≤ P.baseHomScheme ⁻¹ᵁ (⊤ : P.bseScheme.Opens) :=
  le_top

/-- The presented lift maps the ambient scheme into the target chart. -/
theorem ambient_le_preimage_tgt :
    (⊤ : P.ambientScheme.Opens) ≤ P.liftHomScheme ⁻¹ᵁ (⊤ : P.tgtScheme.Opens) :=
  le_top

/-- The derivations acting on the lifts presented by the chart: the `Γ(V, ⊤)`-derivations of
`Γ(W, ⊤)` with values in the conormal module of the chart thickening. -/
abbrev Deriv (P : ChartLiftPresentation C S hS p q a U') : Type u :=
  letI := P.isAffineAmbient
  letI := Stacks.Smooth.algebraAppLE P.chartHomScheme P.tgt_le_preimage
  letI := Stacks.Smooth.thickeningKerModule P.isFirstOrderThickening
  letI := Stacks.Smooth.moduleOfAppLE P.redHomScheme P.sub_le_preimage P.conormal
  letI := Stacks.Smooth.moduleOfAppLEBase P.chartHomScheme P.redHomScheme P.tgt_le_preimage
    P.sub_le_preimage P.conormal
  letI := Stacks.Smooth.isScalarTowerOfAppLEBase P.chartHomScheme P.redHomScheme
    P.tgt_le_preimage P.sub_le_preimage P.conormal
  Derivation Γ(P.bseScheme, (⊤ : P.bseScheme.Opens)) Γ(P.tgtScheme, (⊤ : P.tgtScheme.Opens))
    P.conormal

/-- The translated structure map `(a')^♯ + d ∘ θ` on global sections of the target chart. -/
noncomputable def translateHom (δ : P.Deriv) :
    Γ(P.tgtScheme, (⊤ : P.tgtScheme.Opens)) ⟶ Γ(P.ambientScheme, (⊤ : P.ambientScheme.Opens)) :=
  letI := P.isAffineAmbient
  Stacks.Smooth.addDerivationHom P.chartHomScheme P.isFirstOrderThickening P.tgt_le_preimage
    P.sub_le_preimage δ P.incl_comp_liftHomScheme P.ambient_le_preimage_tgt

/-- The translate of the presented lift, as a morphism of schemes: the morphism whose structure
map is `(a')^♯ + d ∘ θ`, read back through `Spec`. -/
noncomputable def translateScheme (δ : P.Deriv) : P.ambientScheme ⟶ P.tgtScheme :=
  letI := P.isAffineTgt
  Stacks.Smooth.homEquivOfIsAffine.symm (P.translateHom δ)

/-- The structure map of the translate is the translated structure map. -/
theorem translateScheme_appTop (δ : P.Deriv) :
    (P.translateScheme δ).appTop = P.translateHom δ :=
  let := P.isAffineTgt
  Stacks.Smooth.homEquivOfIsAffine.apply_symm_apply (P.translateHom δ)


/-- The ambient scheme of the chart is affine. -/
private instance instIsAffineAmbient : IsAffine P.ambientScheme := P.isAffineAmbient

/-- The target chart is affine. -/
private instance instIsAffineTgt : IsAffine P.tgtScheme := P.isAffineTgt

/-- The base chart is affine. -/
private instance instIsAffineBse : IsAffine P.bseScheme := P.isAffineBse

/-- The algebra structure of the target chart over the base chart. -/
private noncomputable instance instAlgebraBseTgt :
    Algebra Γ(P.bseScheme, (⊤ : P.bseScheme.Opens)) Γ(P.tgtScheme, (⊤ : P.tgtScheme.Opens)) :=
  Stacks.Smooth.algebraAppLE P.chartHomScheme P.tgt_le_preimage

/-- The conormal module of the chart as a module over the sections of the closed subscheme. -/
private noncomputable instance instModuleSubConormal :
    Module Γ(P.subScheme, (⊤ : P.subScheme.Opens)) P.conormal :=
  Stacks.Smooth.thickeningKerModule P.isFirstOrderThickening

/-- The conormal module of the chart as a module over the sections of the target chart. -/
private noncomputable instance instModuleTgtConormal :
    Module Γ(P.tgtScheme, (⊤ : P.tgtScheme.Opens)) P.conormal :=
  Stacks.Smooth.moduleOfAppLE P.redHomScheme P.sub_le_preimage P.conormal

/-- The conormal module of the chart as a module over the sections of the base chart. -/
private noncomputable instance instModuleBseConormal :
    Module Γ(P.bseScheme, (⊤ : P.bseScheme.Opens)) P.conormal :=
  Stacks.Smooth.moduleOfAppLEBase P.chartHomScheme P.redHomScheme P.tgt_le_preimage
    P.sub_le_preimage P.conormal

private noncomputable instance instIsScalarTowerConormal :
    IsScalarTower Γ(P.bseScheme, (⊤ : P.bseScheme.Opens)) Γ(P.tgtScheme, (⊤ : P.tgtScheme.Opens))
      P.conormal :=
  Stacks.Smooth.isScalarTowerOfAppLEBase P.chartHomScheme P.redHomScheme
    P.tgt_le_preimage P.sub_le_preimage P.conormal


/-- The translated structure map commutes with the structure maps out of the base chart: a
derivation kills the image of the base. -/
theorem chartHom_appLE_comp_translateHom (δ : P.Deriv) :
    P.chartHomScheme.appLE (⊤ : P.bseScheme.Opens) ⊤ P.tgt_le_preimage ≫ P.translateHom δ
      = P.baseHomScheme.appLE (⊤ : P.bseScheme.Opens) ⊤ P.ambient_le_preimage_bse := by
  refine CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_)
  rw [CommRingCat.hom_comp, RingHom.comp_apply]
  show (P.translateHom δ).hom
      ((P.chartHomScheme.appLE (⊤ : P.bseScheme.Opens) ⊤ P.tgt_le_preimage).hom r) = _
  rw [translateHom, Stacks.Smooth.addDerivationHom_apply]
  have hd : δ ((P.chartHomScheme.appLE (⊤ : P.bseScheme.Opens) ⊤ P.tgt_le_preimage).hom r) = 0 := by
    rw [← RingHom.algebraMap_toAlgebra
      (P.chartHomScheme.appLE (⊤ : P.bseScheme.Opens) ⊤ P.tgt_le_preimage).hom]
    exact δ.map_algebraMap r
  rw [hd, Submodule.coe_zero, add_zero, ← CommRingCat.comp_apply,
    Stacks.Smooth.appLE_comp_appLE_of_lift P.chartHomScheme P.liftHomScheme_comp
      P.tgt_le_preimage P.ambient_le_preimage_tgt P.ambient_le_preimage_bse]

/-- The translated structure map reduces to the structure map of the reduction: the derivation
takes values in the defining ideal of the chart thickening. -/
theorem translateHom_comp_incl_appTop (δ : P.Deriv) :
    P.translateHom δ ≫ P.inclScheme.appTop
      = P.redHomScheme.appLE (⊤ : P.tgtScheme.Opens) ⊤ P.sub_le_preimage := by
  refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
  rw [CommRingCat.hom_comp, RingHom.comp_apply]
  show P.inclScheme.appTop.hom ((P.translateHom δ).hom x) = _
  rw [translateHom, Stacks.Smooth.addDerivationHom_apply, map_add,
    RingHom.mem_ker.mp (δ x).2, add_zero, ← CommRingCat.comp_apply,
    Stacks.Smooth.appLE_appTop_of_lift P.incl_comp_liftHomScheme P.ambient_le_preimage_tgt
      P.sub_le_preimage]


/-- The translate maps the ambient scheme into the target chart. -/
theorem ambient_le_preimage_translate (δ : P.Deriv) :
    (⊤ : P.ambientScheme.Opens) ≤ P.translateScheme δ ⁻¹ᵁ (⊤ : P.tgtScheme.Opens) := by
  simp

/-- The sections of the translate over the target chart are the translated structure map. -/
theorem translateScheme_appLE (δ : P.Deriv) :
    (P.translateScheme δ).appLE (⊤ : P.tgtScheme.Opens) ⊤ (P.ambient_le_preimage_translate δ)
      = P.translateHom δ :=
  (Stacks.Smooth.appLE_top_top (P.translateScheme δ)).trans (P.translateScheme_appTop δ)

/-- **The translate of the presented lift is again a solution of the lifting problem**, at the
level of the chart: it is a morphism over the base chart restricting to the same reduction. -/
theorem translateScheme_spec (δ : P.Deriv) :
    P.translateScheme δ ≫ P.chartHomScheme = P.baseHomScheme ∧
      P.inclScheme ≫ P.translateScheme δ = P.redHomScheme := by
  obtain ⟨b, hb, hbf, hba, hbφ⟩ := Stacks.Smooth.exists_lift_of_algHom P.chartHomScheme
    (isAffineOpen_top _) (isAffineOpen_top _) P.tgt_le_preimage P.sub_le_preimage
    P.ambient_le_preimage_bse (P.translateHom δ)
    (P.chartHom_appLE_comp_translateHom δ) (P.translateHom_comp_incl_appTop δ)
  have heq : P.translateScheme δ = b :=
    Stacks.Smooth.hom_ext_of_appLE (isAffineOpen_top _) (P.ambient_le_preimage_translate δ) hb
      ((P.translateScheme_appLE δ).trans hbφ.symm)
  rw [heq]
  exact ⟨hbf, hba⟩

/-- **The translate is again a morphism over the base chart.** -/
theorem translateScheme_comp_chartHom (δ : P.Deriv) :
    P.translateScheme δ ≫ P.chartHomScheme = P.baseHomScheme :=
  (P.translateScheme_spec δ).1

/-- **The translate is again a lift of the reduction.** -/
theorem incl_comp_translateScheme (δ : P.Deriv) :
    P.inclScheme ≫ P.translateScheme δ = P.redHomScheme :=
  (P.translateScheme_spec δ).2


/-- **The translate of the presented lift, as a morphism of the big fppf site.**  The structure
map `(a')^♯ + d ∘ δ` is read back as a morphism of schemes by `Spec` — the target chart is
affine — and that morphism lies over the base chart, hence over `S`. -/
noncomputable def translate (δ : P.Deriv) :
    (SmallEtale.toOver C S hS X'.1).obj U' ⟶ P.tgt :=
  BigFppfOver.homOfCompEq C S hS (P.translateScheme δ)
    (comp_inclusion_map_hom_of_comp C S hS (P.translateScheme δ) P.chartHom P.baseHom
      (P.translateScheme_comp_chartHom δ))

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.ChartLiftPresentation.translate`
is `AlgebraicGeometry.Space.ChartLiftPresentation.translateScheme`. -/
@[simp]
theorem toScheme_map_translate (δ : P.Deriv) :
    (BigFppfOver.toScheme C S hS).map (P.translate δ) = P.translateScheme δ :=
  BigFppfOver.toScheme_map_homOfCompEq C S hS _ _

/-- The translate lies over the base chart, as a morphism of the site. -/
theorem translate_comp_chartHom (δ : P.Deriv) : P.translate δ ≫ P.chartHom = P.baseHom :=
  (BigFppfOver.toScheme C S hS).map_injective (by
    rw [Functor.map_comp, P.toScheme_map_translate, P.translateScheme_comp_chartHom])

/-- The translate restricts to the closed subscheme as the presented lift does. -/
theorem incl_comp_translate (δ : P.Deriv) : P.incl ≫ P.translate δ = P.incl ≫ P.liftHom :=
  (BigFppfOver.toScheme C S hS).map_injective (by
    rw [Functor.map_comp, Functor.map_comp, P.toScheme_map_translate,
      P.incl_comp_translateScheme, redHomScheme, Functor.map_comp])


/-- **The translate of a lift is again a lift.**  This is the assertion that the action lands in
`AlgebraicGeometry.Space.liftsSubfunctor`: the translated morphism lies over `B`, because it
lies over the base chart, and it agrees with `a` on `X ×_{X'} U'`, because it agrees with the
original lift after restriction to the closed subscheme of the chart and every test object
landing in `X` factors through that subscheme. -/
theorem isChartLift_translate (δ : P.Deriv) :
    IsChartLift C S hS p q a U' (yoneda.map (P.translate δ) ≫ P.tgtChart) := by
  refine ⟨?_, fun W₀ k t hkt => ?_⟩
  · rw [Category.assoc, ← P.chartSq, ← Category.assoc, ← Functor.map_comp,
      P.translate_comp_chartHom, P.baseSq]
  · have hl := P.isPullback.lift_fst (yoneda.map k) t hkt
    set l := P.isPullback.lift (yoneda.map k) t hkt with hldef
    have key : l ≫ yoneda.map P.incl ≫ yoneda.map (P.translate δ) ≫ P.tgtChart
        = l ≫ yoneda.map P.incl ≫ yoneda.map P.liftHom ≫ P.tgtChart := by
      rw [← Category.assoc (yoneda.map P.incl), ← Functor.map_comp, P.incl_comp_translate,
        Functor.map_comp, Category.assoc]
    rw [← hl, Category.assoc, key, ← Category.assoc, hl]
    exact P.isLift.2 W₀ k t hkt


/-- **The characterising equation of the action.**  The difference of the translate from the
presented lift, as a derivation with values in the conormal module of the chart thickening, is
the derivation that was used to translate. -/
theorem liftDiffDerivation_translate (δ : P.Deriv) :
    letI := P.isAffineAmbient
    letI := Stacks.Smooth.algebraAppLE P.chartHomScheme P.tgt_le_preimage
    letI := Stacks.Smooth.thickeningKerModule P.isFirstOrderThickening
    letI := Stacks.Smooth.moduleOfAppLE P.redHomScheme P.sub_le_preimage P.conormal
    letI := Stacks.Smooth.moduleOfAppLEBase P.chartHomScheme P.redHomScheme P.tgt_le_preimage
      P.sub_le_preimage P.conormal
    letI := Stacks.Smooth.isScalarTowerOfAppLEBase P.chartHomScheme P.redHomScheme
      P.tgt_le_preimage P.sub_le_preimage P.conormal
    Stacks.Smooth.liftDiffDerivation P.chartHomScheme P.isFirstOrderThickening P.tgt_le_preimage
        P.sub_le_preimage P.ambient_le_preimage_bse P.redHomScheme_comp
        (P.translateScheme_comp_chartHom δ) P.liftHomScheme_comp
        (P.incl_comp_translateScheme δ) P.incl_comp_liftHomScheme
        (P.ambient_le_preimage_translate δ) P.ambient_le_preimage_tgt
      = δ := by
  refine Derivation.ext fun x => Subtype.ext ?_
  rw [Stacks.Smooth.liftDiffDerivation_apply, P.translateScheme_appLE, translateHom,
    Stacks.Smooth.addDerivationHom_apply]
  ring

/-- **The zero derivation acts trivially.** -/
theorem translateScheme_zero : P.translateScheme 0 = P.liftHomScheme := by
  have hhom : P.translateHom 0 = P.liftHomScheme.appTop := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    show (P.translateHom 0).hom x = _
    rw [translateHom, Stacks.Smooth.addDerivationHom_apply]
    change (P.liftHomScheme.appLE (⊤ : P.tgtScheme.Opens) ⊤ P.ambient_le_preimage_tgt).hom x
      + ((0 : P.conormal) : Γ(P.ambientScheme, (⊤ : P.ambientScheme.Opens))) = _
    rw [ZeroMemClass.coe_zero, add_zero, Stacks.Smooth.appLE_top_top]
  rw [translateScheme, hhom]
  exact Stacks.Smooth.homEquivOfIsAffine.symm_apply_eq.mpr rfl

/-- The zero derivation acts trivially, as a morphism of the site. -/
theorem translate_zero : P.translate 0 = P.liftHom :=
  (BigFppfOver.toScheme C S hS).map_injective (by
    rw [P.toScheme_map_translate, P.translateScheme_zero])

/-- **The action is free.**  Two derivations with the same translate are equal. -/
theorem translateScheme_injective : Function.Injective P.translateScheme := by
  intro δ₁ δ₂ h
  refine Derivation.ext fun x => Subtype.ext ?_
  have h1 : P.translateHom δ₁ = P.translateHom δ₂ := by
    rw [← P.translateScheme_appTop, ← P.translateScheme_appTop, h]
  have h2 := congr($(h1).hom x)
  rw [translateHom, translateHom, Stacks.Smooth.addDerivationHom_apply,
    Stacks.Smooth.addDerivationHom_apply] at h2
  exact add_left_cancel h2

/-- **The action is transitive on the solutions presented by the chart.**  Every morphism of
schemes which solves the lifting problem at the chart is the translate of the presented lift by
a derivation. -/
theorem exists_translateScheme_eq (b : P.ambientScheme ⟶ P.tgtScheme)
    (hbf : b ≫ P.chartHomScheme = P.baseHomScheme)
    (hba : P.inclScheme ≫ b = P.redHomScheme)
    (hb : (⊤ : P.ambientScheme.Opens) ≤ b ⁻¹ᵁ (⊤ : P.tgtScheme.Opens)) :
    ∃ δ : P.Deriv, P.translateScheme δ = b := by
  refine ⟨Stacks.Smooth.liftDiffDerivation P.chartHomScheme P.isFirstOrderThickening
    P.tgt_le_preimage P.sub_le_preimage P.ambient_le_preimage_bse P.redHomScheme_comp
    hbf P.liftHomScheme_comp hba P.incl_comp_liftHomScheme hb P.ambient_le_preimage_tgt, ?_⟩
  refine Stacks.Smooth.hom_ext_of_appLE (isAffineOpen_top _)
    (P.ambient_le_preimage_translate _) hb ?_
  rw [P.translateScheme_appLE, translateHom]
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  rw [Stacks.Smooth.addDerivationHom_apply, Stacks.Smooth.liftDiffDerivation_apply]
  ring


/-- The closed subscheme of the chart is affine: it is the source of a closed immersion into an
affine scheme. -/
theorem isAffineSub : IsAffine P.subScheme :=
  have : _root_.AlgebraicGeometry.IsClosedImmersion P.inclScheme := P.squareZero.1
  isAffine_of_isAffineHom P.inclScheme

/-- The closed subscheme of the chart is affine. -/
private instance instIsAffineSub : IsAffine P.subScheme := P.isAffineSub

/-- The presented lift, as a section of `Y` over the chart. -/
noncomputable def liftValue : Y.1.obj (op ((SmallEtale.toOver C S hS X'.1).obj U')) :=
  yonedaEquiv (yoneda.map P.liftHom ≫ P.tgtChart)

/-- The translate of the presented lift, as a section of `Y` over the chart. -/
noncomputable def translateValue (δ : P.Deriv) :
    Y.1.obj (op ((SmallEtale.toOver C S hS X'.1).obj U')) :=
  yonedaEquiv (yoneda.map (P.translate δ) ≫ P.tgtChart)

/-- The presented lift, as a section of the sheaf of lifts over the chart. -/
noncomputable def liftSection : (liftsSubfunctor C S hS p q a).toFunctor.obj (op U') :=
  ⟨P.liftValue, by
    change IsChartLift C S hS p q a U' (yonedaEquiv.symm P.liftValue)
    rw [liftValue, Equiv.symm_apply_apply]
    exact P.isLift⟩

/-- **The action of the chart derivations on the sheaf of lifts.**  The translate of the
presented lift by a derivation, as a section of `AlgebraicGeometry.Space.liftsSubfunctor` over
the chart. -/
noncomputable def translateSection (δ : P.Deriv) :
    (liftsSubfunctor C S hS p q a).toFunctor.obj (op U') :=
  ⟨P.translateValue δ, by
    change IsChartLift C S hS p q a U' (yonedaEquiv.symm (P.translateValue δ))
    rw [translateValue, Equiv.symm_apply_apply]
    exact P.isChartLift_translate δ⟩

/-- The zero derivation fixes the presented lift, as a section of the sheaf of lifts. -/
theorem translateSection_zero : P.translateSection 0 = P.liftSection := by
  refine Subtype.ext ?_
  change P.translateValue 0 = P.liftValue
  rw [translateValue, liftValue, P.translate_zero]

/-- **The action is free on the sheaf of lifts**, granted that the chart of `Y` is étale.  Two
derivations whose translates have the same image in `Y` are equal: the two translates restrict
to the same morphism on the closed subscheme of the chart, so formal étaleness of the chart —
[Stacks Project, Tag 04AL] — identifies them already in the chart, and the action of the
derivations in the chart is free. -/
theorem translateSection_injective
    (hw : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart) :
    Function.Injective P.translateSection := by
  intro δ₁ δ₂ h
  have himg : P.translateValue δ₁ = P.translateValue δ₂ := congrArg Subtype.val h
  have hxy : P.tgtChart.app (op P.sub) (P.incl ≫ P.liftHom)
      = Y.1.map P.incl.op (P.translateValue δ₁) := by
    rw [app_eq_yonedaEquiv_comp C S hS P.tgtChart (P.incl ≫ P.liftHom), translateValue,
      yonedaEquiv_naturality, ← Category.assoc, ← Functor.map_comp, P.incl_comp_translate]
  obtain ⟨z, -, huniq⟩ := formallyEtale_of_etale C S hS P.tgtChart hw P.sub
    ((SmallEtale.toOver C S hS X'.1).obj U') P.isAffineSub P.isAffineAmbient P.incl P.squareZero
    (P.incl ≫ P.liftHom) (P.translateValue δ₁) hxy
  have e₁ := huniq (P.translate δ₁)
    ⟨P.incl_comp_translate δ₁, app_eq_yonedaEquiv_comp C S hS P.tgtChart (P.translate δ₁)⟩
  have e₂ := huniq (P.translate δ₂)
    ⟨P.incl_comp_translate δ₂,
      (app_eq_yonedaEquiv_comp C S hS P.tgtChart (P.translate δ₂)).trans himg.symm⟩
  refine P.translateScheme_injective ?_
  rw [← P.toScheme_map_translate, ← P.toScheme_map_translate, e₁, e₂]


/-- **The action law.**  Translating by a sum is translating the translate: on global sections
of the target chart, the structure map of the translate by `δ₁ + δ₂` is that of the translate
by `δ₁` with `δ₂` added. -/
theorem translateHom_add (δ₁ δ₂ : P.Deriv)
    (x : Γ(P.tgtScheme, (⊤ : P.tgtScheme.Opens))) :
    letI := P.isAffineAmbient
    letI := Stacks.Smooth.algebraAppLE P.chartHomScheme P.tgt_le_preimage
    letI := Stacks.Smooth.thickeningKerModule P.isFirstOrderThickening
    letI := Stacks.Smooth.moduleOfAppLE P.redHomScheme P.sub_le_preimage P.conormal
    letI := Stacks.Smooth.moduleOfAppLEBase P.chartHomScheme P.redHomScheme P.tgt_le_preimage
      P.sub_le_preimage P.conormal
    letI := Stacks.Smooth.isScalarTowerOfAppLEBase P.chartHomScheme P.redHomScheme
      P.tgt_le_preimage P.sub_le_preimage P.conormal
    (P.translateHom (δ₁ + δ₂)).hom x
      = (P.translateHom δ₁).hom x
        + ((δ₂ x : P.conormal) : Γ(P.ambientScheme, (⊤ : P.ambientScheme.Opens))) := by
  simp only [translateHom, Stacks.Smooth.addDerivationHom_apply, Derivation.add_apply,
    AddMemClass.coe_add]
  ring

/-- **The difference of two translates is the difference of the derivations.**  Together with
`AlgebraicGeometry.Space.ChartLiftPresentation.liftDiffDerivation_translate` this is the
cocycle identity for the difference of lifts in the chart. -/
theorem liftDiffDerivation_translate_translate (δ₁ δ₂ : P.Deriv) :
    letI := P.isAffineAmbient
    letI := Stacks.Smooth.algebraAppLE P.chartHomScheme P.tgt_le_preimage
    letI := Stacks.Smooth.thickeningKerModule P.isFirstOrderThickening
    letI := Stacks.Smooth.moduleOfAppLE P.redHomScheme P.sub_le_preimage P.conormal
    letI := Stacks.Smooth.moduleOfAppLEBase P.chartHomScheme P.redHomScheme P.tgt_le_preimage
      P.sub_le_preimage P.conormal
    letI := Stacks.Smooth.isScalarTowerOfAppLEBase P.chartHomScheme P.redHomScheme
      P.tgt_le_preimage P.sub_le_preimage P.conormal
    Stacks.Smooth.liftDiffDerivation P.chartHomScheme P.isFirstOrderThickening P.tgt_le_preimage
        P.sub_le_preimage P.ambient_le_preimage_bse P.redHomScheme_comp
        (P.translateScheme_comp_chartHom δ₁) (P.translateScheme_comp_chartHom δ₂)
        (P.incl_comp_translateScheme δ₁) (P.incl_comp_translateScheme δ₂)
        (P.ambient_le_preimage_translate δ₁) (P.ambient_le_preimage_translate δ₂)
      = δ₁ - δ₂ := by
  refine Derivation.ext fun x => Subtype.ext ?_
  rw [Stacks.Smooth.liftDiffDerivation_apply, P.translateScheme_appLE, P.translateScheme_appLE]
  simp only [translateHom, Stacks.Smooth.addDerivationHom_apply, Derivation.sub_apply,
    AddSubgroupClass.coe_sub]
  ring


/-- The translate, as a section of `Y` over the chart, is the image of the translating
morphism. -/
theorem translateValue_eq (δ : P.Deriv) :
    P.translateValue δ = P.tgtChart.app (op ((SmallEtale.toOver C S hS X'.1).obj U'))
      (P.translate δ) :=
  (app_eq_yonedaEquiv_comp C S hS P.tgtChart (P.translate δ)).symm

/-- The closed subscheme of the chart lies in `X`: the square of the presentation commutes. -/
theorem incl_comp_chart : yoneda.map P.incl ≫ U'.1.hom = P.subChart ≫ X.ι :=
  P.isPullback.w

/-- **Transitivity of the action on the sheaf of lifts**, granted that both charts are étale.
Every section of `AlgebraicGeometry.Space.liftsSubfunctor` over the chart which comes from a
morphism into the chart of `Y` is a translate of the presented lift.

Two things have to be repaired before the chart-level transitivity
`AlgebraicGeometry.Space.ChartLiftPresentation.exists_translateScheme_eq` applies, and both
are repaired by the two charts being étale.  The given morphism into the chart of `Y` need not
restrict to the closed subscheme as the presented lift does — only their images in `Y` agree
there — and [Stacks Project, Tag 04AL],
`AlgebraicGeometry.Space.exists_chart_hom_of_restrict_app_eq`, rechooses it so that it does.
The rechosen morphism need not lie over the base morphism of the presentation either — only
over `B` — and formal étaleness of the chart of `B` identifies the two, since they agree on the
closed subscheme and have the same image in `B`.

The factorization `hb` is **not a restriction on the statement**: granted the same étaleness of
the chart of `Y`, every section of `AlgebraicGeometry.Space.liftsSubfunctor` over the chart admits
one, by `AlgebraicGeometry.Space.ChartLiftPresentation.exists_hom_tgtChart_app_eq` of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ChartLiftFactorization`, whence the
hypothesis-free form
`AlgebraicGeometry.Space.ChartLiftPresentation.exists_translateSection_eq_of_isEtale`. -/
theorem exists_translateSection_eq
    (hw : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart)
    (hv : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.bseChart)
    (β : (liftsSubfunctor C S hS p q a).toFunctor.obj (op U'))
    (b : (SmallEtale.toOver C S hS X'.1).obj U' ⟶ P.tgt)
    (hb : β.1 = P.tgtChart.app (op ((SmallEtale.toOver C S hS X'.1).obj U')) b) :
    ∃ δ : P.Deriv, P.translateSection δ = β := by
  have hβ : IsChartLift C S hS p q a U' (yonedaEquiv.symm β.1) := β.2
  have hsymm : (yonedaEquiv.symm β.1 :
      yoneda.obj ((SmallEtale.toOver C S hS X'.1).obj U') ⟶ Y.1)
      = yoneda.map b ≫ P.tgtChart := by
    rw [hb, app_eq_yonedaEquiv_comp C S hS P.tgtChart b, Equiv.symm_apply_apply]
  -- the two presentations have the same image in `Y` on the closed subscheme of the chart
  have hsub : P.tgtChart.app (op P.sub) (P.incl ≫ b)
      = P.tgtChart.app (op P.sub) (P.incl ≫ P.liftHom) := by
    have h₁ := hβ.2 P.sub P.incl P.subChart P.incl_comp_chart
    have h₂ := P.isLift.2 P.sub P.incl P.subChart P.incl_comp_chart
    rw [hsymm] at h₁
    rw [app_eq_yonedaEquiv_comp C S hS P.tgtChart (P.incl ≫ b),
      app_eq_yonedaEquiv_comp C S hS P.tgtChart (P.incl ≫ P.liftHom), Functor.map_comp,
      Functor.map_comp, Category.assoc, Category.assoc, h₁, h₂]
  -- Stacks 04AL rechooses the presentation so that it restricts as the presented lift does
  obtain ⟨c', hc'incl, hc'img⟩ := exists_chart_hom_of_restrict_app_eq C S hS P.tgtChart hw
    P.isAffineSub P.isAffineAmbient P.squareZero b P.liftHom hsub
  have hc'comp : yoneda.map c' ≫ P.tgtChart = yoneda.map b ≫ P.tgtChart := by
    refine yonedaEquiv.injective ?_
    rw [← app_eq_yonedaEquiv_comp C S hS P.tgtChart c',
      ← app_eq_yonedaEquiv_comp C S hS P.tgtChart b]
    exact hc'img
  -- formal étaleness of the chart of `B` puts the rechosen presentation over the base morphism
  have hbase : c' ≫ P.chartHom = P.baseHom := by
    have hxy : P.bseChart.app (op P.sub) (P.incl ≫ P.baseHom)
        = B.1.map P.incl.op (yonedaEquiv (U'.1.hom ≫ p.hom)) := by
      rw [app_eq_yonedaEquiv_comp C S hS P.bseChart (P.incl ≫ P.baseHom), yonedaEquiv_naturality,
        Functor.map_comp, Category.assoc, P.baseSq]
    obtain ⟨z, -, huniq⟩ := formallyEtale_of_etale C S hS P.bseChart hv P.sub
      ((SmallEtale.toOver C S hS X'.1).obj U') P.isAffineSub P.isAffineAmbient P.incl
      P.squareZero (P.incl ≫ P.baseHom) (yonedaEquiv (U'.1.hom ≫ p.hom)) hxy
    have e₁ : c' ≫ P.chartHom = z := by
      refine huniq (c' ≫ P.chartHom) ⟨?_, ?_⟩
      · change P.incl ≫ c' ≫ P.chartHom = P.incl ≫ P.baseHom
        rw [← Category.assoc, hc'incl, Category.assoc, P.liftSq]
      · rw [app_eq_yonedaEquiv_comp C S hS P.bseChart (c' ≫ P.chartHom), Functor.map_comp,
          Category.assoc, P.chartSq, ← Category.assoc, hc'comp, ← hsymm]
        exact congrArg yonedaEquiv hβ.1
    have e₂ : P.baseHom = z := by
      refine huniq P.baseHom ⟨rfl, ?_⟩
      rw [app_eq_yonedaEquiv_comp C S hS P.bseChart P.baseHom, P.baseSq]
    rw [e₁, e₂]
  -- the chart-level transitivity now applies
  obtain ⟨δ, hδ⟩ := P.exists_translateScheme_eq ((BigFppfOver.toScheme C S hS).map c')
    (by rw [← Functor.map_comp, hbase])
    (by rw [← Functor.map_comp, hc'incl, redHomScheme, Functor.map_comp]) le_top
  refine ⟨δ, Subtype.ext ?_⟩
  have hct : P.translate δ = c' :=
    (BigFppfOver.toScheme C S hS).map_injective (by rw [P.toScheme_map_translate, hδ])
  change P.translateValue δ = β.1
  rw [translateValue, hct, hc'comp, ← hsymm, Equiv.apply_symm_apply]


/-! ### The acting group at the chart, as the sections of the acting sheaf -/

/-- The Zariski pullback `a^*Ω_{W/V}` of the sheaf of differentials of the chart square along
the reduction of the lift. -/
noncomputable abbrev chartCotangent : P.subScheme.Modules :=
  Stacks.Smooth.pullbackCotangentSheaf P.chartHomScheme P.redHomScheme

/-- The sections at the chart of the acting sheaf `SheafHom_{𝒪_X}(a^*Ω_{Y/B}, 𝒞_{X/X'})`, in
their Zariski form: the `Γ(U, ⊤)`-linear maps `Γ(a^*Ω_{W/V}, ⊤) ⟶ 𝒞_{U/U'}`. -/
abbrev ActionSection (P : ChartLiftPresentation C S hS p q a U') : Type u :=
  letI := P.isAffineAmbient
  letI := Stacks.Smooth.thickeningKerModule P.isFirstOrderThickening
  Γ(P.chartCotangent, (⊤ : P.subScheme.Opens)) →ₗ[Γ(P.subScheme, (⊤ : P.subScheme.Opens))]
    P.conormal

/-- **The derivation attached to a section of the acting sheaf at the chart**: the section
composed with the pullback of the universal differential, which is Equation
[Stacks Project, Tag 0619] read at the chart. -/
noncomputable def derivOfActionSection (θ : P.ActionSection) : P.Deriv :=
  letI := P.isAffineAmbient
  letI := Stacks.Smooth.algebraAppLE P.chartHomScheme P.tgt_le_preimage
  letI := Stacks.Smooth.algebraAppLE P.redHomScheme P.sub_le_preimage
  letI := Stacks.Smooth.thickeningKerModule P.isFirstOrderThickening
  letI := Stacks.Smooth.moduleOfAppLE P.redHomScheme P.sub_le_preimage P.conormal
  letI := Stacks.Smooth.moduleOfAppLEBase P.chartHomScheme P.redHomScheme P.tgt_le_preimage
    P.sub_le_preimage P.conormal
  letI := Stacks.Smooth.isScalarTowerOfAppLE P.redHomScheme P.sub_le_preimage P.conormal
  letI := Stacks.Smooth.isScalarTowerOfAppLEBase P.chartHomScheme P.redHomScheme
    P.tgt_le_preimage P.sub_le_preimage P.conormal
  letI := Stacks.Smooth.moduleAppLE P.redHomScheme P.chartCotangent P.sub_le_preimage
  letI := Stacks.Smooth.moduleAppLEBase P.chartHomScheme P.redHomScheme P.chartCotangent
    P.tgt_le_preimage P.sub_le_preimage
  letI := Stacks.Smooth.isScalarTowerAppLE P.redHomScheme P.chartCotangent P.sub_le_preimage
  letI := Stacks.Smooth.isScalarTowerAppLEBase P.chartHomScheme P.redHomScheme P.chartCotangent
    P.tgt_le_preimage P.sub_le_preimage
  (θ.restrictScalars Γ(P.tgtScheme, (⊤ : P.tgtScheme.Opens))).compDer
    (Stacks.Smooth.pullbackCotangentDerivation P.chartHomScheme P.redHomScheme ⊤
      P.tgt_le_preimage P.sub_le_preimage)

/-- The value of `AlgebraicGeometry.Space.ChartLiftPresentation.derivOfActionSection`. -/
theorem derivOfActionSection_apply (θ : P.ActionSection)
    (x : Γ(P.tgtScheme, (⊤ : P.tgtScheme.Opens))) :
  letI := P.isAffineAmbient
  letI := Stacks.Smooth.algebraAppLE P.chartHomScheme P.tgt_le_preimage
  letI := Stacks.Smooth.algebraAppLE P.redHomScheme P.sub_le_preimage
  letI := Stacks.Smooth.thickeningKerModule P.isFirstOrderThickening
  letI := Stacks.Smooth.moduleOfAppLE P.redHomScheme P.sub_le_preimage P.conormal
  letI := Stacks.Smooth.moduleOfAppLEBase P.chartHomScheme P.redHomScheme P.tgt_le_preimage
    P.sub_le_preimage P.conormal
  letI := Stacks.Smooth.isScalarTowerOfAppLE P.redHomScheme P.sub_le_preimage P.conormal
  letI := Stacks.Smooth.isScalarTowerOfAppLEBase P.chartHomScheme P.redHomScheme
    P.tgt_le_preimage P.sub_le_preimage P.conormal
  letI := Stacks.Smooth.moduleAppLE P.redHomScheme P.chartCotangent P.sub_le_preimage
  letI := Stacks.Smooth.moduleAppLEBase P.chartHomScheme P.redHomScheme P.chartCotangent
    P.tgt_le_preimage P.sub_le_preimage
  letI := Stacks.Smooth.isScalarTowerAppLE P.redHomScheme P.chartCotangent P.sub_le_preimage
  letI := Stacks.Smooth.isScalarTowerAppLEBase P.chartHomScheme P.redHomScheme P.chartCotangent
    P.tgt_le_preimage P.sub_le_preimage
  P.derivOfActionSection θ x
    = θ (Stacks.Smooth.pullbackD P.chartHomScheme P.redHomScheme ⊤ P.sub_le_preimage x) :=
  rfl


/-- **The acting group at the chart is exactly the sections of the acting sheaf there.**  The
map `θ ↦ θ ∘ d` from the `Γ(U, ⊤)`-linear maps `Γ(a^*Ω_{W/V}, ⊤) ⟶ 𝒞_{U/U'}` to the
`Γ(V, ⊤)`-derivations of `Γ(W, ⊤)` with values in `𝒞_{U/U'}` is a bijection.  This is
`Stacks.Smooth.existsUnique_linearMap_comp_pullbackD_of_module`, the chart-independent
description of the acting group, read at the presentation. -/
theorem derivOfActionSection_bijective : Function.Bijective P.derivOfActionSection := by
  refine ⟨fun θ₁ θ₂ h => ?_, fun δ => ?_⟩
  · obtain ⟨θ, -, huniq⟩ := Stacks.Smooth.existsUnique_linearMap_comp_pullbackD_of_module
      P.chartHomScheme P.redHomScheme P.conormal (isAffineOpen_top _) (isAffineOpen_top _)
      P.tgt_le_preimage P.sub_le_preimage (P.derivOfActionSection θ₁)
    refine (huniq θ₁ fun x => (P.derivOfActionSection_apply θ₁ x).symm).trans
      (huniq θ₂ fun x => ?_).symm
    rw [h, P.derivOfActionSection_apply θ₂ x]
  · obtain ⟨θ, hθ, -⟩ := Stacks.Smooth.existsUnique_linearMap_comp_pullbackD_of_module
      P.chartHomScheme P.redHomScheme P.conormal (isAffineOpen_top _) (isAffineOpen_top _)
      P.tgt_le_preimage P.sub_le_preimage δ
    exact ⟨θ, Derivation.ext fun x => (P.derivOfActionSection_apply θ x).trans (hθ x)⟩

/-- **The action of the sections of the acting sheaf at the chart on the sheaf of lifts.**  The
translate of the presented lift by a section `θ` of `SheafHom_{𝒪_X}(a^*Ω_{Y/B}, 𝒞_{X/X'})` at
the chart, as a section of `AlgebraicGeometry.Space.liftsSubfunctor`.  This is the source's
`θ · a'`, read over an étale scheme chart. -/
noncomputable def translateActionSection (θ : P.ActionSection) :
    (liftsSubfunctor C S hS p q a).toFunctor.obj (op U') :=
  P.translateSection (P.derivOfActionSection θ)

/-- **The action of the sections of the acting sheaf is free on the sheaf of lifts**, granted
that the chart of `Y` is étale. -/
theorem translateActionSection_injective
    (hw : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart) :
    Function.Injective P.translateActionSection :=
  (P.translateSection_injective hw).comp P.derivOfActionSection_bijective.1

/-- **The action of the sections of the acting sheaf is transitive on the lifts presented by the
chart**, granted that both charts are étale. -/
theorem exists_translateActionSection_eq
    (hw : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart)
    (hv : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.bseChart)
    (β : (liftsSubfunctor C S hS p q a).toFunctor.obj (op U'))
    (b : (SmallEtale.toOver C S hS X'.1).obj U' ⟶ P.tgt)
    (hb : β.1 = P.tgtChart.app (op ((SmallEtale.toOver C S hS X'.1).obj U')) b) :
    ∃ θ : P.ActionSection, P.translateActionSection θ = β := by
  obtain ⟨δ, hδ⟩ := P.exists_translateSection_eq hw hv β b hb
  obtain ⟨θ, hθ⟩ := P.derivOfActionSection_bijective.2 δ
  exact ⟨θ, by rw [translateActionSection, hθ, hδ]⟩

end ChartLiftPresentation


/-! ### Existence of a chart presentation -/

/-- **A chart presentation exists for every lift that factors through an affine chart square of
`q`.**  Over an affine étale chart `U'` of a first-order thickening `X ⊂ X'`, a morphism into an
affine chart `W` of `Y` sitting in a commuting square over an affine chart `V` of `B`, whose
image in `Y` is a lift of `a`, is presented by a `ChartLiftPresentation`.

So the square-zero chart datum of the presentation is never an obstruction: the cartesian square
`X ×_{X'} U' ⟶ U'` is supplied by
`AlgebraicGeometry.Space.exists_squareZeroChart_of_isFirstOrderThickening`, and neither is the
base morphism, which is forced.  What a presentation genuinely asks for beyond the lift is the
affine chart square of `q` through which the lift factors, and that is supplied — on a covering
family of affine étale charts, which is the best that can be asked for — by
`AlgebraicGeometry.Space.exists_affine_chartSquare_hom_ofArrows` of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ChartLiftFactorization`, whence
`AlgebraicGeometry.Space.exists_chartLiftPresentation_liftSection_ofArrows` for a given section of
`AlgebraicGeometry.Space.liftsSubfunctor`. -/
theorem exists_chartLiftPresentation (p : X' ⟶ B) (q : Y ⟶ B) {X : Subfunctor X'.1}
    (a : X.toFunctor ⟶ Y.1) (hX : IsFirstOrderThickening C S hS X' X)
    (U' : SmallEtale C S hS X'.1)
    (hU' : IsAffine
      ((BigFppfOver.toScheme C S hS).obj ((SmallEtale.toOver C S hS X'.1).obj U')))
    {W V : BigFppfOver C S hS}
    (hW : IsAffine ((BigFppfOver.toScheme C S hS).obj W))
    (hV : IsAffine ((BigFppfOver.toScheme C S hS).obj V))
    (w : yoneda.obj W ⟶ Y.1) (v : yoneda.obj V ⟶ B.1) (ψ : W ⟶ V)
    (hsq : yoneda.map ψ ≫ v = w ≫ q.hom)
    (c : (SmallEtale.toOver C S hS X'.1).obj U' ⟶ W)
    (hc : IsChartLift C S hS p q a U' (yoneda.map c ≫ w)) :
    ∃ P : ChartLiftPresentation C S hS p q a U',
      P.liftValue = yonedaEquiv (yoneda.map c ≫ w) := by
  obtain ⟨T₀, i₀, u₀, hpb, -, -, hsz⟩ :=
    exists_squareZeroChart_of_isFirstOrderThickening C S hS hX
      ((SmallEtale.toOver C S hS X'.1).obj U') U'.1.hom
      ((isEtale_iff_presheaf_of_yoneda C S hS U'.1.hom).2 U'.property) hU'
  exact
    ⟨{ sub := T₀
       incl := i₀
       subChart := u₀
       isPullback := hpb
       squareZero := hsz
       isAffineAmbient := hU'
       tgt := W
       isAffineTgt := hW
       bse := V
       isAffineBse := hV
       tgtChart := w
       bseChart := v
       chartHom := ψ
       chartSq := hsq
       liftHom := c
       isLift := hc }, rfl⟩

end AlgebraicGeometry.Space

end
