module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartModuleEqualizerPresentation

/-!
# Stacks 07SI at arbitrary coefficients, reduced to the naturality of evaluation

`AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_equalizerPresentation` reduces
Stacks 07SI to four compatibilities and two equalizer presentations `e`, `eT` of the groups
`Γ(Xᵢ, ℱᵢ)` and `Γ(X, ℱ)`.  This file discharges `e` and `eT` for an **arbitrary** module `ℱ₀`,
using the presentations of
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/ChartModuleEqualizerPresentation.lean`, and records
what the two naturality hypotheses `he` and `heT` become once that is done.

They become statements about **evaluation**: since each presentation is evaluation at the chart,
`he` says that the transition map `Γ(Xᵢ, ℱᵢ) → Γ(Xⱼ, ℱⱼ)` of Stacks 07SI, followed by evaluation
at the chart `Uⱼ`, is evaluation at `Uᵢ` followed by a map `ℱᵢ(Uᵢ) → ℱⱼ(Uⱼ)` of sections over the
charts, and `heT` says the same for the maps to the limit.  No equivalence and no identification
of modules occurs in either statement.

That is the point of the reshape.  The structure-sheaf consumer
`AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_naturality_of_unit` states `he` and
`heT` through `AlgebraicGeometry.Space.LimitSituation.chartEqualizerPresentation`, whose value
(`.stageSectionsEquivEqualizer_apply_val`) carries the component at the chart of
`AlgebraicGeometry.Space.LimitSituation.stageModuleUnitIso` — and the components of that
isomorphism are not described anywhere in the library, it being built by
`CategoryTheory.Functor.CorepresentableBy.uniqueUpToIso`.  Here no such component appears.

## Main definitions

* `AlgebraicGeometry.Space.LimitSituation.chartStageSections` and `.chartLimitSections`: the
  sections of `ℱᵢ` over the chart `Uᵢ` of the chart system, and of `ℱ` over its limit — the
  carriers of the equalizer presentations.
* `AlgebraicGeometry.Space.LimitSituation.relationStageSections` and `.relationLimitSections`:
  the same over the relation chart system and its limit.
* `AlgebraicGeometry.Space.LimitSituation.chartStageRelationRestriction` and
  `.chartLimitRelationRestriction`: restriction along one of the two maps the relation induces,
  at a stage and at the limit — the parallel pair the equalizers are taken over.

## Main results

* `AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_evaluationNaturality`: **Stacks
  07SI for an arbitrary module `ℱ₀`, with both equalizer presentations discharged**, so that what
  remains is the naturality of evaluation (`he`, `heT`) together with the two colimit assertions
  (`hU`, `hR`) for the systems of sections over the charts.

## Implementation notes

*Why the colimit assertions stay hypotheses.*  For the structure sheaf they are discharged by
`AlgebraicGeometry.isStagesColimit_appTop_of_isAffine_of_isLimit_of_directed`, the affine case of
Stacks 01Z0: the systems are the rings of global functions on an inverse system of affine
schemes.  For a general module the systems are instead the groups `ℱᵢ(Uᵢ)` and `ℱᵢ(Rᵢ)`.  The
corresponding part of Stacks 01Z0 — a quasi-coherent module over a merely quasi-compact and
quasi-separated system — *is* proved, as
`AlgebraicGeometry.isStagesColimit_stagePullbackSection_of_isQuasicoherent`, and in this
elementwise shape; but
its groups are the global sections of a module on the chart as a *scheme*.  The identification
of those with `ℱᵢ(Uᵢ)`, a group of sections on the small étale site of `Xᵢ`, is the declaration
`AlgebraicGeometry.Space.chartRestrictionSheafTopEquiv`, but its naturality in the stage is not:
that needs the action on sections of
`AlgebraicGeometry.Space.restrictToChartBaseChangeIso`, which is undescribed.  The three
factors of that composite are not obstructions: neither of the
two adjunction maps among them is inverted on the route the composite takes, and the third
has its adjunct square
(`AlgebraicGeometry.Space.unit_comp_representedModulePullbackIso_hom`).  What blocks instead is
that the adjunct of the composite is formally free, so a description must prove it equal to an
independently given morphism of sheaves of modules
`restrictToChart G V ⟶ g_*(restrictToChart (a^*G) W)`.

**That morphism exists and most of the adjunct is taken; one factor is left.**  The morphism is
`AlgebraicGeometry.Space.restrictToChartPushforwardHom`, described on sections by
`AlgebraicGeometry.Space.chartRestrictionPushforwardHom_val_app`, so a note that the library has
none of it is wrong.  The adjunct of the composite is reduced by
`AlgebraicGeometry.Space.homEquiv_restrictToChartBaseChangeIso_hom` and then by
`AlgebraicGeometry.Space.homEquiv_restrictToChartBaseChangeIso_hom_peeled` in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeRestrictionBaseChangeAdjunct.lean`, which
discharges the represented base-change isomorphism's adjunct as well; what is left is the direct
image of `AlgebraicGeometry.Space.restrictToChartBaseChangeEtaleTail`, whose action on the chart
component of the unit of Stacks 03D7 is the one remaining obstruction.  **One of that tail's
factors now has a reading on sections**, so the claim that none of them does is no longer true:
in the namespace `AlgebraicGeometry.Space`, the lemma
`chartModuleRestrictionIsoChartSmallEtaleRestriction_hom_val_app_modulePullbackUnitSection` in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleRestrictionChartSection.lean` gives the value of
`AlgebraicGeometry.Space.chartModuleRestrictionIsoChartSmallEtaleRestriction` on a chart section.
What the tail still lacks is the value of the factor that carries the passage from the represented
morphism to `a`, and the obstruction there is not a missing lemma: the three reductions it is
assembled from each compile on their own, and only their composition exceeds the budget.  The
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionBaseChangeAdjunct.lean` measure it.  So
`hU` and `hR` stay hypotheses, but for one reason and not three.  See the implementation notes of
`AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_equalizerPresentation_of_isAffine`,
the third "Missing" bullet of the module documentation of `SectionsColimitDescent.lean`, and the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionBaseChange.lean`, which name them.
The assertions are therefore carried, exactly as that declaration's `hU` and `hR` are.

*Why the maps between the systems stay hypotheses.*  A map `ℱᵢ(Uᵢ) → ℱⱼ(Uⱼ)` of sections over
the charts is the chartwise inverse image, which the library has as
`AlgebraicGeometry.Space.modulePullbackUnitSection` — the chart component of the unit of the
Stacks 03LU adjunction.  Taking that as `transU` is what would make `he` a statement about one
identity; see the "Not proved here" section.  The declaration below leaves the maps as
parameters so that it does not commit to that choice, which is the same shape
`AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_equalizerPresentation` uses.

### Not proved here

**Stacks 07SI is not proved here and no `@[stacks]` attribute appears in this file.**  With
`transU` taken to be the chartwise inverse image, `he` unfolds — by
`PresheafOfModules.sectionsMap_coe`, `AlgebraicGeometry.Space.modulePushforwardCounitApp_map` and
the naturality of the unit of the Stacks 03LU adjunction in the module — to the single identity

`(modulePullbackUnitIso B S hS f).inv.val.app (op U) 1 = modulePullbackUnitSection B S hS f _ d 1`

for the transition morphism `f`, that is: the canonical identification `𝒪_{Xⱼ} ≅ f^*𝒪_{Xᵢ}`
carries the unit function to the chartwise inverse image of the unit function.  That identity is
not available.  `AlgebraicGeometry.Space.modulePullbackUnitIso` is
`Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso`, which is
`CategoryTheory.Functor.CorepresentableBy.uniqueUpToIso`, so the only description of it is the
corepresentability bijection; and unwinding that bijection reaches
`CategoryTheory.MorphismOfTopoi.pushforwardTerminalHomEquiv`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposTerminalSections.lean:154`), for which the
library has naturality in the sheaf but no description of a value on sections.  So the identity
cannot presently be reduced to
`AlgebraicGeometry.Space.modulePushforwardCounitApp`, which is what the chartwise inverse image
is built from.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Tag 07SG](https://stacks.math.columbia.edu/tag/07SG)
* [Stacks Project, Tag 01Z0](https://stacks.math.columbia.edu/tag/01Z0)
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
  {U₀ R₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ A.system.obj (op A.base)}
  {t : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R₀) ⟶
    yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀)}
  {s : (BigAffineFppf.inclusion B S hS).obj R₀ ⟶ (BigAffineFppf.inclusion B S hS).obj U₀}
  (F₀ : Modules.{u, u} B S hS (A.stage A.base).obj (A.stage A.base).property)
  (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀))

/-! ### The systems of sections over the charts -/

/-- **The group `ℱᵢ(Uᵢ)` of the equalizer presentation of Stacks 07SG**: the sections of the
module `ℱᵢ` of Stacks 07SI over the chart of the stage carried by the chart system of an étale
chart of the chosen stage. -/
noncomputable abbrev chartStageSections (i : A.Stages) : Type u :=
  (moduleSetSheaf B S hS (A.stage i.1) (A.stageModule F₀ i)).obj.obj
    (op (A.stagesEtaleChart (A.chartSystem U₀ f₀) hf₀ i))

/-- **The group `ℱ(U)` of the equalizer presentation of Stacks 07SG at the limit**: the sections
of the module `ℱ` of Stacks 07SI over the limit `U = lim Uᵢ` of the chart system. -/
noncomputable abbrev chartLimitSections (hX : IsAlgebraicSpace B S hS X)
    (hI : #A.I < B.cutoff.ord.cof) : Type u :=
  (moduleSetSheaf B S hS (A.limitSpace hX) (A.limitModule F₀ hX)).obj.obj
    (op (A.limitEtaleChart (A.chartSystem U₀ f₀) (A.chartLimitBridge U₀ f₀ hI) hf₀))

/-- **The group `ℱᵢ(Rᵢ)` of the equalizer presentation of Stacks 07SG**: the sections of `ℱᵢ`
over the chart of the stage carried by the chart system of the relation. -/
noncomputable abbrev relationStageSections (hpb : IsPullback t (yoneda.map s) f₀ f₀)
    (i : A.Stages) : Type u :=
  (moduleSetSheaf B S hS (A.stage i.1) (A.stageModule F₀ i)).obj.obj
    (op (A.stagesEtaleChart (A.chartSystem R₀ (t ≫ f₀))
      (isEtaleChart_comp_of_isPullback hf₀ hpb) i))

/-- **The group `ℱ(R)` of the equalizer presentation of Stacks 07SG at the limit**: the sections
of `ℱ` over the limit `R = lim Rᵢ` of the chart system of the relation. -/
noncomputable abbrev relationLimitSections (hpb : IsPullback t (yoneda.map s) f₀ f₀)
    (hX : IsAlgebraicSpace B S hS X) (hI : #A.I < B.cutoff.ord.cof) : Type u :=
  (moduleSetSheaf B S hS (A.limitSpace hX) (A.limitModule F₀ hX)).obj.obj
    (op (A.limitEtaleChart (A.chartSystem R₀ (t ≫ f₀))
      (A.chartLimitBridge R₀ (t ≫ f₀) hI) (isEtaleChart_comp_of_isPullback hf₀ hpb)))

/-- **One of the two maps `ℱᵢ(Uᵢ) → ℱᵢ(Rᵢ)` the relation induces**: restriction of sections of
`ℱᵢ` along the map of charts `Rᵢ ⟶ Uᵢ` induced by one of the two projections of the relation.
The two projections of the relation `R₀ = U₀ ×_{X₀} U₀` give the two values `hτ = rfl` and
`hτ = hpb.w.symm` of the argument. -/
noncomputable def chartStageRelationRestriction
    (hpb : IsPullback t (yoneda.map s) f₀ f₀) {τ : _}
    (hτ : τ ≫ f₀ = t ≫ f₀) (i : A.Stages) :
    A.chartStageSections F₀ hf₀ i → A.relationStageSections F₀ hf₀ hpb i := fun y =>
  (moduleSetSheaf B S hS (A.stage i.1) (A.stageModule F₀ i)).obj.map
    (A.stagesEtaleChartMap (A.chartSystem U₀ f₀) hf₀ (A.chartSystem R₀ (t ≫ f₀))
      (isEtaleChart_comp_of_isPullback hf₀ hpb) hτ i).op y

/-- **One of the two maps `ℱ(U) → ℱ(R)` the relation induces at the limit**: restriction of
sections of `ℱ` along the map of limit charts induced by one of the two projections of the
relation. -/
noncomputable def chartLimitRelationRestriction
    (hpb : IsPullback t (yoneda.map s) f₀ f₀) (hX : IsAlgebraicSpace B S hS X)
    (hI : #A.I < B.cutoff.ord.cof) {τ : _} (hτ : τ ≫ f₀ = t ≫ f₀) :
    A.chartLimitSections F₀ hf₀ hX hI → A.relationLimitSections F₀ hf₀ hpb hX hI := fun y =>
  (moduleSetSheaf B S hS (A.limitSpace hX) (A.limitModule F₀ hX)).obj.map
    (A.limitEtaleChartMap (A.chartSystem U₀ f₀) (A.chartLimitBridge U₀ f₀ hI)
      (A.chartSystem R₀ (t ≫ f₀)) (A.chartLimitBridge R₀ (t ≫ f₀) hI) hf₀
      (isEtaleChart_comp_of_isPullback hf₀ hpb) hτ).op y

/-! ### Stacks 07SI at arbitrary coefficients, with `e` and `eT` discharged -/

/-- **Stacks 07SI for an arbitrary module, reduced to the naturality of evaluation at the
charts.**  Let `U₀ ⟶ X₀` be an affine scheme-valued point of the chosen stage of a limit
situation which is an étale chart surjective on points, and let `t` and `yoneda s` be the two
projections of its relation `R₀ = U₀ ×_{X₀} U₀`, which at a separated stage is again affine by
`AlgebraicGeometry.Space.LimitSituation.exists_affine_relationChart_of_isAbsolutelySeparated`.
Let `ℱ₀` be **any** module on the chosen stage.

Suppose given maps `transU`, `ιU` between the groups `ℱᵢ(Uᵢ)` and `ℱ(U)` of sections over the
chart system and its limit, and `transR`, `ιR` between the groups over the relation system,
compatible with the two restrictions the relation induces (`hpt`, `hqt`, `hpi`, `hqi`), and
suppose each of the two systems is a filtered colimit (`hU`, `hR`).  If moreover evaluation at
the charts carries the transition maps `Γ(Xᵢ, ℱᵢ) → Γ(Xⱼ, ℱⱼ)` and the maps `Γ(Xᵢ, ℱᵢ) → Γ(X, ℱ)`
of Stacks 07SI to `transU` and `ιU` (`he`, `heT`), then `Γ(X, ℱ)` is the filtered colimit of the
`Γ(Xᵢ, ℱᵢ)`.

This is `AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_equalizerPresentation` with
its two equalizer presentations supplied by
`AlgebraicGeometry.Space.LimitSituation.chartModuleEqualizerPresentation` and
`.chartLimitModuleEqualizerPresentation`, and with `he` and `heT` restated through their value
lemmas, which say that each presentation is evaluation at the chart.  So the two naturality
hypotheses below mention no equivalence and no identification of modules — which is what
separates this from the structure-sheaf consumer
`AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_naturality_of_unit`; see the
"Not proved here" section of this file's module documentation for what is still missing. -/
theorem isSectionsColimit_of_evaluationNaturality
    (hX : IsAlgebraicSpace B S hS X) (hI : #A.I < B.cutoff.ord.cof)
    (hsurj : IsSurjective B S hS f₀) (hpb : IsPullback t (yoneda.map s) f₀ f₀)
    (transU : ∀ i j : A.Stages, i ≤ j →
      A.chartStageSections F₀ hf₀ i → A.chartStageSections F₀ hf₀ j)
    (ιU : ∀ i : A.Stages,
      A.chartStageSections F₀ hf₀ i → A.chartLimitSections F₀ hf₀ hX hI)
    (transR : ∀ i j : A.Stages, i ≤ j →
      A.relationStageSections F₀ hf₀ hpb i → A.relationStageSections F₀ hf₀ hpb j)
    (ιR : ∀ i : A.Stages,
      A.relationStageSections F₀ hf₀ hpb i → A.relationLimitSections F₀ hf₀ hpb hX hI)
    (hpt : ∀ (i j : A.Stages) (h : i ≤ j) (y : A.chartStageSections F₀ hf₀ i),
      A.chartStageRelationRestriction F₀ hf₀ hpb rfl j (transU i j h y)
        = transR i j h (A.chartStageRelationRestriction F₀ hf₀ hpb rfl i y))
    (hqt : ∀ (i j : A.Stages) (h : i ≤ j) (y : A.chartStageSections F₀ hf₀ i),
      A.chartStageRelationRestriction F₀ hf₀ hpb hpb.w.symm j (transU i j h y)
        = transR i j h (A.chartStageRelationRestriction F₀ hf₀ hpb hpb.w.symm i y))
    (hpi : ∀ (i : A.Stages) (y : A.chartStageSections F₀ hf₀ i),
      A.chartLimitRelationRestriction F₀ hf₀ hpb hX hI rfl (ιU i y)
        = ιR i (A.chartStageRelationRestriction F₀ hf₀ hpb rfl i y))
    (hqi : ∀ (i : A.Stages) (y : A.chartStageSections F₀ hf₀ i),
      A.chartLimitRelationRestriction F₀ hf₀ hpb hX hI hpb.w.symm (ιU i y)
        = ιR i (A.chartStageRelationRestriction F₀ hf₀ hpb hpb.w.symm i y))
    (he : ∀ (i j : A.Stages) (h : i ≤ j) (σ : A.stageSections F₀ i),
      (A.stageTransition F₀ i j h σ).val
          (op (A.stagesEtaleChart (A.chartSystem U₀ f₀) hf₀ j))
        = transU i j h (σ.val (op (A.stagesEtaleChart (A.chartSystem U₀ f₀) hf₀ i))))
    (heT : ∀ (i : A.Stages) (σ : A.stageSections F₀ i),
      (A.stageProjection F₀ hX i σ).val
          (op (A.limitEtaleChart (A.chartSystem U₀ f₀) (A.chartLimitBridge U₀ f₀ hI) hf₀))
        = ιU i (σ.val (op (A.stagesEtaleChart (A.chartSystem U₀ f₀) hf₀ i))))
    (hU : Stacks.IsStagesColimit transU ιU) (hR : Stacks.IsStagesColimit transR ιR) :
    A.IsSectionsColimit F₀ hX :=
  A.isSectionsColimit_of_equalizerPresentation F₀ hX hpt hqt hpi hqi
    (A.chartModuleEqualizerPresentation F₀ hf₀ hsurj hpb)
    (A.chartLimitModuleEqualizerPresentation F₀ hf₀ hX hI hsurj hpb)
    (fun i j h σ =>
      ((A.chartModuleEqualizerPresentation_apply_val F₀ hf₀ hsurj hpb j
            (A.stageTransition F₀ i j h σ)).trans (he i j h σ)).trans
        (congrArg (transU i j h)
          (A.chartModuleEqualizerPresentation_apply_val F₀ hf₀ hsurj hpb i σ).symm))
    (fun i σ =>
      ((A.chartLimitModuleEqualizerPresentation_apply_val F₀ hf₀ hX hI hsurj hpb
            (A.stageProjection F₀ hX i σ)).trans (heT i σ)).trans
        (congrArg (ιU i)
          (A.chartModuleEqualizerPresentation_apply_val F₀ hf₀ hsurj hpb i σ).symm))
    hU hR

end AlgebraicGeometry.Space.LimitSituation

end
