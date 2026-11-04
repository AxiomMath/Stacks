module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartLimitEqualizerPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence

/-!
# The equalizer presentation of Stacks 07SI with its own coefficients

`AlgebraicGeometry.Space.LimitSituation.chartEqualizerPresentation` and
`.chartLimitEqualizerPresentation` present the groups `Γ(Xᵢ, ℱᵢ)` and `Γ(X, ℱ)` of Stacks 07SI as
equalizers **of rings of regular functions** `Γ(Uᵢ, ⊤)` on the charts.  That shape is only
available when the coefficients `ℱ₀` are the structure sheaf of the chosen stage: for a general
module the group of sections of `ℱᵢ` over the chart `Uᵢ` is not a ring of functions, so the
equalizer has to be taken in `ℱᵢ(Uᵢ)` instead.

This file supplies the presentations in that shape, for an **arbitrary** module `ℱ₀`:

`Γ(Xᵢ, ℱᵢ) ≃ {y : ℱᵢ(Uᵢ) // t^*y = s^*y}` and `Γ(X, ℱ) ≃ {y : ℱ(U) // t^*y = s^*y}`,

over the chart system of an affine surjective étale chart of the chosen stage and its relation
system, and over their limits.  Both are Stacks 03M8 for the module in question, which the
library already has for every module as
`AlgebraicGeometry.Space.moduleSectionsEquivEqualizer`; what is added here is the reading of the
chart system's charts and of the limit chart as the étale chart and relation chart that
statement asks for, which `AlgebraicGeometry.Space.LimitSituation.stagesEtaleChart` and
`.limitEtaleChart` already provide.

So no identification of `ℱᵢ` with anything is involved, and in particular **no unit
isomorphism**: the structure-sheaf presentations go through
`AlgebraicGeometry.Space.LimitSituation.stageModuleUnitIso` and `.limitModuleUnitIso` in order to
read the sections over a chart as functions on it, and that is exactly the step that has no
components in the library; the presentations below do not take it.

## Main definitions

* `AlgebraicGeometry.Space.LimitSituation.stageModuleSectionsEquivChartEqualizer`: the stagewise
  equalizer presentation of Stacks 07SG over a chart system, for an arbitrary module.
* `AlgebraicGeometry.Space.LimitSituation.limitModuleSectionsEquivChartEqualizer`: the same at
  the limit of a chart system, for an arbitrary module.
* `AlgebraicGeometry.Space.LimitSituation.chartModuleEqualizerPresentation` and
  `.chartLimitModuleEqualizerPresentation`: the two specialisations at the chart system and the
  limit bridge of a limit situation, which are the shapes a consumer of Stacks 07SI at general
  coefficients takes.

## Main results

* `AlgebraicGeometry.Space.LimitSituation.stageModuleSectionsEquivChartEqualizer_apply_val`,
  `.limitModuleSectionsEquivChartEqualizer_apply_val`,
  `.chartModuleEqualizerPresentation_apply_val` and
  `.chartLimitModuleEqualizerPresentation_apply_val`: **each presentation is evaluation at the
  chart.**  A global section of `ℱᵢ` — a compatible family of sections over the étale charts of
  `Xᵢ` — is carried to its own member at the chart of the stage, with no transport in between.

## Implementation notes

*Why these are not transports of the structure-sheaf presentations.*  The groups are different:
the structure-sheaf presentations land in `Γ(Uᵢ, 𝒪)` and these land in `ℱᵢ(Uᵢ)`, and the two
agree only when `ℱ₀ = 𝒪_{X₀}`.  Each of the four declarations below is therefore
`AlgebraicGeometry.Space.moduleSectionsEquivEqualizer`, respectively its value lemma
`AlgebraicGeometry.Space.moduleSectionsEquivEqualizer_apply_val`, at the module and the chart
data in hand — no transport is composed on either side, which is why the value is evaluation at
the chart on the nose.

*The sheaf of sets is named rather than spelled out.*  The sections of a module over a chart are
the sections of its underlying sheaf of sets, and that sheaf is
`AlgebraicGeometry.Space.moduleSetSheaf`; the statements use that abbreviation, in the form
`AlgebraicGeometry.Space.moduleSectionsEquivEqualizer` states it, so that no coercion between
the module and its sheaf of sets has to be unfolded.

*Genericity in the chart system and the limit bridge.*  As in
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/ChartLimitEqualizerPresentation.lean`, the two
general statements take the chart system and its limit bridge as arguments and the two
specialisations instantiate them at the limit situation's own, for the reason recorded in that
file's implementation notes.

### Not proved here

**Stacks 07SI is not proved here and no `@[stacks]` attribute appears in this file.**  What these
presentations discharge are the hypotheses `e` and `eT` of a consumer of Stacks 07SI at general
coefficients; the two naturality hypotheses `he` and `heT` of
`AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_equalizerPresentation` are not
addressed here, and neither are its two colimit hypotheses `hU` and `hR`, which for a general
module are the part of Stacks 01Z0 the library does not have.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Tag 07SG](https://stacks.math.columbia.edu/tag/07SG)
* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space.LimitSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (A : LimitSituation B S hS hZ X)

/-! ### The stagewise presentation, for an arbitrary module -/

section Generic

variable {U₀ R₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ A.system.obj (op A.base)}
  {g₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R₀) ⟶ A.system.obj (op A.base)}
  {τ υ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R₀) ⟶
    yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀)}
  (C : AffineChartSystem B S hS (op A.base) A.system U₀ f₀)
  (LC : AffineChartSystem.LimitBridge C)
  (E : AffineChartSystem B S hS (op A.base) A.system R₀ g₀)
  (LE : AffineChartSystem.LimitBridge E)
  (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀))
  (hg₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk g₀))
  (F₀ : Modules.{u, u} B S hS (A.stage A.base).obj (A.stage A.base).property)

/-- **The stagewise equalizer presentation of Stacks 07SG over a chart system, for an arbitrary
module.**  Let `Xᵢ` be a stage of a limit situation and let `Uᵢ` and `Rᵢ` be the values at that
stage of the chart system of an affine étale chart `U₀ ⟶ X₀` surjective on points and of the
chart system of its relation.  Then, for **any** module `ℱ₀` on the chosen stage, the group
`Γ(Xᵢ, ℱᵢ)` of Stacks 07SI is in bijection with the sections of `ℱᵢ` over `Uᵢ` equalized by the
two maps the relation induces:

`Γ(Xᵢ, ℱᵢ) ≃ {y : ℱᵢ(Uᵢ) // t^*y = s^*y}`.

This is `AlgebraicGeometry.Space.moduleSectionsEquivEqualizer` — Stacks 03M8 for the sheaf of
sets underlying a module, which holds for every module — at the module `ℱᵢ`, the étale chart
`AlgebraicGeometry.Space.LimitSituation.stagesEtaleChart` and the relation square
`AlgebraicGeometry.Space.LimitSituation.isPullback_comparisonFunctor_stagesEtaleChartMap`.

Unlike `AlgebraicGeometry.Space.LimitSituation.stageSectionsEquivChartEqualizer`, which is this
statement at structure-sheaf coefficients composed with the identification of `ℱᵢ` with the
structure sheaf of the stage, nothing is composed here. -/
noncomputable def stageModuleSectionsEquivChartEqualizer (hsurj : IsSurjective B S hS f₀)
    (hτ : τ ≫ f₀ = g₀) (hυ : υ ≫ f₀ = g₀) (hpb : IsPullback τ υ f₀ f₀) (i : A.Stages) :
    A.stageSections F₀ i ≃
      {y : (moduleSetSheaf B S hS (A.stage i.1) (A.stageModule F₀ i)).obj.obj
            (op (A.stagesEtaleChart C hf₀ i)) //
        (moduleSetSheaf B S hS (A.stage i.1) (A.stageModule F₀ i)).obj.map
            (A.stagesEtaleChartMap C hf₀ E hg₀ hτ i).op y
          = (moduleSetSheaf B S hS (A.stage i.1) (A.stageModule F₀ i)).obj.map
            (A.stagesEtaleChartMap C hf₀ E hg₀ hυ i).op y} :=
  moduleSectionsEquivEqualizer B S hS (A.stageModule F₀ i)
    (A.isSurjective_stagesEtaleChart C hf₀ hsurj i)
    (A.isPullback_comparisonFunctor_stagesEtaleChartMap C hf₀ E hg₀ hτ hυ hpb i)

/-- **The stagewise presentation is evaluation at the chart.**  A global section of `ℱᵢ` — a
compatible family of sections over the étale charts of the stage — is carried by
`AlgebraicGeometry.Space.LimitSituation.stageModuleSectionsEquivChartEqualizer` to its own member
at the chart `Uᵢ`, with no transport in between.

This is `AlgebraicGeometry.Space.moduleSectionsEquivEqualizer_apply_val` at the module `ℱᵢ`. -/
theorem stageModuleSectionsEquivChartEqualizer_apply_val (hsurj : IsSurjective B S hS f₀)
    (hτ : τ ≫ f₀ = g₀) (hυ : υ ≫ f₀ = g₀) (hpb : IsPullback τ υ f₀ f₀) (i : A.Stages)
    (σ : A.stageSections F₀ i) :
    (A.stageModuleSectionsEquivChartEqualizer C E hf₀ hg₀ F₀ hsurj hτ hυ hpb i σ).1
      = σ.val (op (A.stagesEtaleChart C hf₀ i)) :=
  moduleSectionsEquivEqualizer_apply_val B S hS (A.stageModule F₀ i) _ _ σ

/-! ### The presentation at the limit, for an arbitrary module -/

/-- **The equalizer presentation of Stacks 07SG at the limit of a chart system, for an arbitrary
module.**  Let `U = lim Uᵢ` be the limit of the chart system of an affine étale chart of the
chosen stage surjective on points and `R = lim Rᵢ` the limit of the chart system of its
relation.  Then, for **any** module `ℱ₀` on the chosen stage, the group `Γ(X, ℱ)` of Stacks 07SI
is in bijection with the sections of `ℱ` over `U` equalized by the two maps the relation
induces:

`Γ(X, ℱ) ≃ {y : ℱ(U) // t^*y = s^*y}`.

This is `AlgebraicGeometry.Space.moduleSectionsEquivEqualizer` at the module `ℱ`, the étale chart
`AlgebraicGeometry.Space.LimitSituation.limitEtaleChart` — which is an étale chart of the limit,
surjective on points, by `.isEtaleChart_limitChartToSpace` and `.isSurjective_limitEtaleChart` —
and the relation square
`AlgebraicGeometry.Space.LimitSituation.isPullback_comparisonFunctor_limitEtaleChartMap`.

As for the stagewise statement, nothing is composed: in particular
`AlgebraicGeometry.Space.LimitSituation.limitModuleUnitIso`, which the structure-sheaf
presentation `.limitSectionsEquivEqualizer` goes through, does not appear. -/
noncomputable def limitModuleSectionsEquivChartEqualizer (hX : IsAlgebraicSpace B S hS X)
    (hsurj : IsSurjective B S hS f₀) (hτ : τ ≫ f₀ = g₀) (hυ : υ ≫ f₀ = g₀)
    (hpb : IsPullback τ υ f₀ f₀) :
    A.limitSections F₀ hX ≃
      {y : (moduleSetSheaf B S hS (A.limitSpace hX) (A.limitModule F₀ hX)).obj.obj
            (op (A.limitEtaleChart C LC hf₀)) //
        (moduleSetSheaf B S hS (A.limitSpace hX) (A.limitModule F₀ hX)).obj.map
            (A.limitEtaleChartMap C LC E LE hf₀ hg₀ hτ).op y
          = (moduleSetSheaf B S hS (A.limitSpace hX) (A.limitModule F₀ hX)).obj.map
            (A.limitEtaleChartMap C LC E LE hf₀ hg₀ hυ).op y} :=
  moduleSectionsEquivEqualizer B S hS (A.limitModule F₀ hX)
    (A.isSurjective_limitEtaleChart C LC hf₀ hsurj)
    (A.isPullback_comparisonFunctor_limitEtaleChartMap C LC E LE hf₀ hg₀ hX hτ hυ hpb)

/-- **The presentation at the limit is evaluation at the limit chart.**  A global section of `ℱ`
is carried by `AlgebraicGeometry.Space.LimitSituation.limitModuleSectionsEquivChartEqualizer` to
its own member at the chart `U = lim Uᵢ`.

This is `AlgebraicGeometry.Space.moduleSectionsEquivEqualizer_apply_val` at the module `ℱ`. -/
theorem limitModuleSectionsEquivChartEqualizer_apply_val (hX : IsAlgebraicSpace B S hS X)
    (hsurj : IsSurjective B S hS f₀) (hτ : τ ≫ f₀ = g₀) (hυ : υ ≫ f₀ = g₀)
    (hpb : IsPullback τ υ f₀ f₀) (σ : A.limitSections F₀ hX) :
    (A.limitModuleSectionsEquivChartEqualizer C LC E LE hf₀ hg₀ F₀ hX hsurj hτ hυ hpb σ).1
      = σ.val (op (A.limitEtaleChart C LC hf₀)) :=
  moduleSectionsEquivEqualizer_apply_val B S hS (A.limitModule F₀ hX) _ _ σ

end Generic

/-! ### The two presentations at the chart system of a limit situation -/

section Consumer

variable {U₀ R₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ A.system.obj (op A.base)}
  {t : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R₀) ⟶
    yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀)}
  {s : (BigAffineFppf.inclusion B S hS).obj R₀ ⟶ (BigAffineFppf.inclusion B S hS).obj U₀}
  (F₀ : Modules.{u, u} B S hS (A.stage A.base).obj (A.stage A.base).property)
  (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀))

/-- **The stagewise equalizer presentation of Stacks 07SG at the chart system of a limit
situation, for an arbitrary module.**  This is
`AlgebraicGeometry.Space.LimitSituation.stageModuleSectionsEquivChartEqualizer` at the chart
system of `U₀ ⟶ X₀` and the chart system of its relation, which are what
`AlgebraicGeometry.Space.LimitSituation.chartStagesDiagram` is built from.

It is the hypothesis `e` of
`AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_equalizerPresentation` at the
equalizer system `CU i = ℱᵢ(Uᵢ)`, for **every** module `ℱ₀` — where the structure-sheaf
presentation `AlgebraicGeometry.Space.LimitSituation.chartEqualizerPresentation` is the
hypothesis `e` only for `ℱ₀ = 𝒪_{X₀}`. -/
noncomputable def chartModuleEqualizerPresentation (hsurj : IsSurjective B S hS f₀)
    (hpb : IsPullback t (yoneda.map s) f₀ f₀) (i : A.Stages) :
    A.stageSections F₀ i ≃
      {y : (moduleSetSheaf B S hS (A.stage i.1) (A.stageModule F₀ i)).obj.obj
            (op (A.stagesEtaleChart (A.chartSystem U₀ f₀) hf₀ i)) //
        (moduleSetSheaf B S hS (A.stage i.1) (A.stageModule F₀ i)).obj.map
            (A.stagesEtaleChartMap (A.chartSystem U₀ f₀) hf₀ (A.chartSystem R₀ (t ≫ f₀))
              (isEtaleChart_comp_of_isPullback hf₀ hpb) rfl i).op y
          = (moduleSetSheaf B S hS (A.stage i.1) (A.stageModule F₀ i)).obj.map
            (A.stagesEtaleChartMap (A.chartSystem U₀ f₀) hf₀ (A.chartSystem R₀ (t ≫ f₀))
              (isEtaleChart_comp_of_isPullback hf₀ hpb) hpb.w.symm i).op y} :=
  A.stageModuleSectionsEquivChartEqualizer (A.chartSystem U₀ f₀) (A.chartSystem R₀ (t ≫ f₀))
    hf₀ (isEtaleChart_comp_of_isPullback hf₀ hpb) F₀ hsurj rfl hpb.w.symm hpb i

/-- **The stagewise presentation at the chart system is evaluation at the chart.** -/
theorem chartModuleEqualizerPresentation_apply_val (hsurj : IsSurjective B S hS f₀)
    (hpb : IsPullback t (yoneda.map s) f₀ f₀) (i : A.Stages) (σ : A.stageSections F₀ i) :
    (A.chartModuleEqualizerPresentation F₀ hf₀ hsurj hpb i σ).1
      = σ.val (op (A.stagesEtaleChart (A.chartSystem U₀ f₀) hf₀ i)) :=
  A.stageModuleSectionsEquivChartEqualizer_apply_val _ _ hf₀ _ F₀ hsurj rfl hpb.w.symm hpb i σ

/-- **The equalizer presentation of Stacks 07SG at the limit of the chart system of a limit
situation, for an arbitrary module.**  This is
`AlgebraicGeometry.Space.LimitSituation.limitModuleSectionsEquivChartEqualizer` at the chart
system of `U₀ ⟶ X₀` with its limit bridge and the chart system of its relation with its own,
which are what `AlgebraicGeometry.Space.LimitSituation.chartStagesCone` is built from.

It is the hypothesis `eT` of
`AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_equalizerPresentation` at the
equalizer system `CU i = ℱᵢ(Uᵢ)`, for **every** module `ℱ₀`. -/
noncomputable def chartLimitModuleEqualizerPresentation (hX : IsAlgebraicSpace B S hS X)
    (hI : #A.I < B.cutoff.ord.cof) (hsurj : IsSurjective B S hS f₀)
    (hpb : IsPullback t (yoneda.map s) f₀ f₀) :
    A.limitSections F₀ hX ≃
      {y : (moduleSetSheaf B S hS (A.limitSpace hX) (A.limitModule F₀ hX)).obj.obj
            (op (A.limitEtaleChart (A.chartSystem U₀ f₀)
              (A.chartLimitBridge U₀ f₀ hI) hf₀)) //
        (moduleSetSheaf B S hS (A.limitSpace hX) (A.limitModule F₀ hX)).obj.map
            (A.limitEtaleChartMap (A.chartSystem U₀ f₀) (A.chartLimitBridge U₀ f₀ hI)
              (A.chartSystem R₀ (t ≫ f₀)) (A.chartLimitBridge R₀ (t ≫ f₀) hI) hf₀
              (isEtaleChart_comp_of_isPullback hf₀ hpb) rfl).op y
          = (moduleSetSheaf B S hS (A.limitSpace hX) (A.limitModule F₀ hX)).obj.map
            (A.limitEtaleChartMap (A.chartSystem U₀ f₀) (A.chartLimitBridge U₀ f₀ hI)
              (A.chartSystem R₀ (t ≫ f₀)) (A.chartLimitBridge R₀ (t ≫ f₀) hI) hf₀
              (isEtaleChart_comp_of_isPullback hf₀ hpb) hpb.w.symm).op y} :=
  A.limitModuleSectionsEquivChartEqualizer (A.chartSystem U₀ f₀) (A.chartLimitBridge U₀ f₀ hI)
    (A.chartSystem R₀ (t ≫ f₀)) (A.chartLimitBridge R₀ (t ≫ f₀) hI) hf₀
    (isEtaleChart_comp_of_isPullback hf₀ hpb) F₀ hX hsurj rfl hpb.w.symm hpb

/-- **The presentation at the limit of the chart system is evaluation at the limit chart.** -/
theorem chartLimitModuleEqualizerPresentation_apply_val (hX : IsAlgebraicSpace B S hS X)
    (hI : #A.I < B.cutoff.ord.cof) (hsurj : IsSurjective B S hS f₀)
    (hpb : IsPullback t (yoneda.map s) f₀ f₀) (σ : A.limitSections F₀ hX) :
    (A.chartLimitModuleEqualizerPresentation F₀ hf₀ hX hI hsurj hpb σ).1
      = σ.val (op (A.limitEtaleChart (A.chartSystem U₀ f₀)
          (A.chartLimitBridge U₀ f₀ hI) hf₀)) :=
  A.limitModuleSectionsEquivChartEqualizer_apply_val _ _ _ _ hf₀ _ F₀ hX hsurj rfl
    hpb.w.symm hpb σ

end Consumer

end AlgebraicGeometry.Space.LimitSituation

end
