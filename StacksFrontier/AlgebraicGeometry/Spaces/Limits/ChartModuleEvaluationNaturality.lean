module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartModuleSectionsColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionChartValue

/-!
# The chart diagrams of a chart system, and the maps of sections they carry

`AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_evaluationNaturality` reduces
Stacks 07SI, at arbitrary coefficients, to two naturality hypotheses `he` and `heT`: that
evaluation at the chart of a stage carries the transition map `Γ(Xᵢ, ℱᵢ) → Γ(Xⱼ, ℱⱼ)` and the
map `Γ(Xᵢ, ℱᵢ) → Γ(X, ℱ)` of Stacks 07SI to maps `ℱᵢ(Uᵢ) → ℱⱼ(Uⱼ)` and `ℱᵢ(Uᵢ) → ℱ(U)` of
sections over the charts.

This file supplies the geometry those statements need: the commutative diagrams of étale scheme
charts over the transition morphisms and over the limit projection, and the maps of sections over
the charts they carry.  The maps are built, not assumed: by
`AlgebraicGeometry.Space.modulePullbackSections_val` the value over a chart of an inverse image
of a global section is the chart section of the value below, and the maps of Stacks 07SI are such
inverse images followed by a comparison of iterated inverse images, so the maps `transU` and `ιU`
that `he` and `heT` speak of are determined — they are
`AlgebraicGeometry.Space.chartPullbackSectionMap` at these diagrams.

## Main definitions

* `AlgebraicGeometry.Space.LimitSituation.stagesChartDiagram`: the commutative diagram of étale
  scheme charts relating the chart of a later stage to the chart of an earlier one over the
  transition morphism — the chart system's own transition map of charts.
* `AlgebraicGeometry.Space.LimitSituation.limitChartDiagram`: the same from the limit chart to
  the chart of a stage, over the limit projection — the limit bridge's own cone projection.
* `AlgebraicGeometry.Space.LimitSituation.chartStageTransition` and `.chartLimitInclusion`:
  **the maps `ℱᵢ(Uᵢ) → ℱⱼ(Uⱼ)` and `ℱᵢ(Uᵢ) → ℱ(U)` of sections over the charts**, that is the
  data `transU` and `ιU` of
  `AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_evaluationNaturality`, for an
  arbitrary module on the chosen stage.

## Main results

The content of each definition is the commutativity of a square of charts over a morphism of
algebraic spaces.  Across two stages that is
`AlgebraicGeometry.Space.AffineChartSystem.stageMap_naturality`; from the limit it is
`AlgebraicGeometry.Space.AffineChartSystem.LimitBridge.toLimit_comp_limitπ` after
`AlgebraicGeometry.Space.LimitSituation.limitIso_hom_comp_π` has rewritten the limit projection
of the situation as the projection of the categorical limit.  Both diagrams are reindexed along
`AlgebraicGeometry.Space.LimitSituation.stagesOverEquivalence`, the chart system being indexed by
the slice over the chosen stage and the stages by the opposite upper set.

## Implementation notes

### Not proved here

**Stacks 07SI is not proved here and no `@[stacks]` attribute appears in this file.**  Two
separate things are still missing, and they are of different kinds.

*The two naturality statements `he` and `heT` are proved, in
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/ChartModuleEvaluationValue.lean`.*  They are the
composite of `AlgebraicGeometry.Space.LimitSituation.stageTransition_eq` (resp.
`stageProjection_eq`) with `AlgebraicGeometry.Space.sectionsMap_modulePullbackSections_val`.
Written with `.val` applied to a section of
`AlgebraicGeometry.Space.LimitSituation.stageModule`, that composite is rejected by the kernel
with a deterministic timeout, in every shape tried.  The cause is not the delta of
`AlgebraicGeometry.Space.LimitSituation.stageTransition`, as was recorded here before: the
elaborated `.val` carries the auxiliary proof `stageModule._proof_2` in the implicit arguments of
`Subtype.val` where the generic lemma carries `(A.stage j).property`, and it is checking those two
spellings against each other, with the transition map and the chart both concrete, that exhausts
the budget.  Stated through `AlgebraicGeometry.Space.moduleSectionValue`, which fixes those
implicit arguments to the generic ones, the same composite is checked at once; that file also
records the consumer with `he` and `heT` discharged,
`AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_chartColimits`.

*The two colimit assertions `hU` and `hR`.*  Even with `he` and `heT` discharged,
`AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_evaluationNaturality` carries them:
that `ℱ(U)` is the filtered colimit of the `ℱᵢ(Uᵢ)` and `ℱ(R)` of the `ℱᵢ(Rᵢ)`.  Those are the
part of Stacks 01Z0 for a *module* rather than for the structure sheaf, and the library now
proves that part: `AlgebraicGeometry.isStagesColimit_stagePullbackSection_of_isQuasicoherent` in
`StacksFrontier/AlgebraicGeometry/ModuleLimits/SectionsColimitQuasiCoherent.lean` is the colimit
assertion for a quasi-coherent module over a merely quasi-compact and quasi-separated inverse
system of schemes, in this very elementwise shape.  It is still not a producer for `hU` or `hR`,
because its groups are the global sections of a module on `Uᵢ` *as a scheme*, whereas `ℱᵢ(Uᵢ)`
is a group of sections on the small étale site of `Xᵢ`.  The identification of the two is now a
declaration — `AlgebraicGeometry.Space.chartRestrictionSheafTopEquiv`, a `LinearEquiv` over the
global functions on the chart's scheme — but its **naturality in the stage** is not: that would
have to be read off `AlgebraicGeometry.Space.restrictToChartBaseChangeIso`, whose action on
sections is undescribed.  Of the seventeen named isomorphisms that composite expands into, the
one that might look like the obstruction —
`AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso`, the associated-module functor
of Stacks 03DU commuting with Zariski pullback — has both an adjunct square and a reading on
sections, `AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso_hom_val_app_unit`.
Three of the other sixteen might look like obstructions of the same kind; they are
not, and the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionBaseChange.lean` record why — no
adjunction map among them is inverted on the route the composite takes, and the one comparison of
left adjoints has its adjunct square.

**What blocks is one named compatibility, and it is one the library already owes
elsewhere.**  The morphism the adjunct is to be compared with exists —
`AlgebraicGeometry.Space.restrictToChartPushforwardHom` — and
`AlgebraicGeometry.Space.homEquiv_restrictToChartBaseChangeIso_hom` in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionBaseChangeAdjunct.lean` reduces the adjunct
to the adjunct of the *represented* base-change isomorphism, which is formal, together with the
direct image of `AlgebraicGeometry.Space.restrictToChartBaseChangeEtaleTail`.  **The represented
half is now taken**, by
`AlgebraicGeometry.Space.homEquiv_restrictToChartSchemeBaseChangeIso_inv` in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeRestrictionBaseChangeAdjunct.lean`, which also
substitutes it into the reduction as
`AlgebraicGeometry.Space.homEquiv_restrictToChartBaseChangeIso_hom_peeled`; so the adjunct is now
short of one factor and not two.  The obstruction is
the action of that tail on the chart component of the unit of Stacks 03D7: the tail's one factor
with content is `AlgebraicGeometry.Space.chartModuleRestrictionBaseChangeIso`, two instances of
the composition comparison `AlgebraicGeometry.Space.modulePullbackCompIso` of Stacks 03LU, and
what is wanted is the value of that comparison on the chart component.  That is the compatibility
of the comparisons of Stacks 03LU and 03LW with the chart component of the unit of Stacks 03D7,
already recorded as missing in three places by the "What is not proved" section of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartBaseChangeEtaleSquareComparison.lean`.  See also the
third "Missing" bullet of the module documentation of `SectionsColimitDescent.lean`.  So `he` and
`heT`, now closed, do not alone reach the tag.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 01Z0](https://stacks.math.columbia.edu/tag/01Z0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space.LimitSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (A : LimitSituation B S hS hZ X)
  {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ A.system.obj (op A.base)}
  (C : AffineChartSystem B S hS (op A.base) A.system U₀ f₀)
  (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀))

/-! ### The chart diagrams of a chart system -/

/-- **The commutative diagram of étale scheme charts relating two stages of a chart system**: the
chart of the later stage above the chart of the earlier one, over the transition morphism of the
limit situation.

The morphism of schemes is the chart system's own transition map of charts, read through the
reindexing `AlgebraicGeometry.Space.LimitSituation.stagesOverEquivalence`, and the diagram
commutes by `AlgebraicGeometry.Space.AffineChartSystem.stageMap_naturality`. -/
noncomputable def stagesChartDiagram {i j : A.Stages} (h : i ≤ j) :
    ChartDiagram B S hS (A.stage j.1).obj (A.stage i.1).obj (A.transition h).hom where
  U := A.stagesEtaleChart C hf₀ j
  V := A.stagesEtaleChart C hf₀ i
  g := C.siteDiagram.map ((stagesOverEquivalence A).functor.map (homOfLE h).op)
  comm := (C.stageMap_naturality ((stagesOverEquivalence A).functor.map (homOfLE h).op)).symm

/-- **The commutative diagram of étale scheme charts relating the limit of a chart system to one
of its stages**: the limit chart above the chart of the stage, over the limit projection.

The morphism of schemes is the projection of the limit bridge's cone, and the diagram commutes
by `AlgebraicGeometry.Space.AffineChartSystem.LimitBridge.toLimit_comp_limitπ` once
`AlgebraicGeometry.Space.LimitSituation.limitIso_hom_comp_π` has rewritten the limit projection
of the situation as the projection of the categorical limit. -/
noncomputable def limitChartDiagram (LC : AffineChartSystem.LimitBridge C)
    (hX : IsAlgebraicSpace B S hS X) (i : A.Stages) :
    ChartDiagram B S hS (A.limitSpace hX).obj (A.stage i.1).obj
      (A.projection hX i.1).hom where
  U := A.limitEtaleChart C LC hf₀
  V := A.stagesEtaleChart C hf₀ i
  g := LC.cone.π.app ((stagesOverEquivalence A).functor.obj (op i))
  comm := by
    have h1 : A.limitChartToSpace C LC ≫ A.π.app (op i.1)
        = LC.toLimit ≫ limit.π A.system (op i.1) := by
      rw [limitChartToSpace, Category.assoc, A.limitIso_hom_comp_π]
    exact h1.trans
      (LC.toLimit_comp_limitπ ((stagesOverEquivalence A).functor.obj (op i)))

/-! ### The maps of sections over the charts -/

variable (F₀ : Modules.{u, u} B S hS (A.stage A.base).obj (A.stage A.base).property)

/-- **The map `ℱᵢ(Uᵢ) → ℱⱼ(Uⱼ)` of sections over the charts of Stacks 07SI**: the chart section
of the inverse image along the transition morphism, followed by the comparison
`AlgebraicGeometry.Space.LimitSituation.stageTransitionComparison` of iterated inverse images.

This is the data `transU` of
`AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_evaluationNaturality`, and it is
not a choice: by `AlgebraicGeometry.Space.sectionsMap_modulePullbackSections_val` the value over
the chart of the later stage of the transition map applied to a global section is this map
applied to the value of that section over the chart of the earlier stage, which is what the
hypothesis `he` of that declaration asserts. -/
noncomputable def chartStageTransition {i j : A.Stages} (h : i ≤ j) :
    (A.stageModule F₀ i).val.obj (op (A.stagesEtaleChart C hf₀ i)) →
      (A.stageModule F₀ j).val.obj (op (A.stagesEtaleChart C hf₀ j)) :=
  chartPullbackSectionMap B S hS (A.transition h) (A.stageModule F₀ i) (A.stageModule F₀ j)
    (A.stageTransitionComparison F₀ i j h) (A.stagesChartDiagram C hf₀ h)

/-- **The map `ℱᵢ(Uᵢ) → ℱ(U)` of sections over the charts of Stacks 07SI**: the chart section of
the inverse image along the limit projection, followed by the comparison
`AlgebraicGeometry.Space.LimitSituation.stageProjectionComparison`.

This is the data `ιU` of
`AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_evaluationNaturality`, forced by
its hypothesis `heT` in the same way. -/
noncomputable def chartLimitInclusion (LC : AffineChartSystem.LimitBridge C)
    (hX : IsAlgebraicSpace B S hS X) (i : A.Stages) :
    (A.stageModule F₀ i).val.obj (op (A.stagesEtaleChart C hf₀ i)) →
      (A.limitModule F₀ hX).val.obj (op (A.limitEtaleChart C LC hf₀)) :=
  chartPullbackSectionMap B S hS (A.projection hX i.1) (A.stageModule F₀ i)
    (A.limitModule F₀ hX) (A.stageProjectionComparison F₀ hX i)
    (A.limitChartDiagram C hf₀ LC hX i)

end AlgebraicGeometry.Space.LimitSituation

end
