module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.ModuleIsoFlatness
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Limits.RelativeApproximation.FlatDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.RelativeDimensionDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonoCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFormallySmooth
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties

namespace AlgebraicGeometry.Space.MorphismDescentSituation.C1573
end AlgebraicGeometry.Space.MorphismDescentSituation.C1573

/-!
# DescendingMorphismProperties under the site convention

The declarations below accompany
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties`: they state its results
under the chapter's standing convention of Section 70.2 (tag 07SD) on the size of the site, in the
form the absolute Noetherian approximation of Stacks 07SU consumes.

## Main results

* `MorphismDescentSituation.C1573.exists_isFlatOver_mapAt_of_siteContainsBaseChangeLimits`:
  if the pullback of a quasi-coherent module of finite presentation is flat over the limit, then
  its pullback to some stage is flat.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe w v u

namespace CategoryTheory

variable {A : Type*} [Category* A]

variable [HasPullbacks A]

end CategoryTheory

namespace AlgebraicGeometry

/-! ### Flatness of a pulled back module over the second factor of a fibre product -/

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

/-! ### Chart squares of a base change -/

section BaseChangeSquares

variable {A : Type*} [Category* A] [HasPullbacks A]

end BaseChangeSquares

/-! ### Relative étaleness and surjectivity of charts -/

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

/-! ### Transferring a chart-local property to the morphism of charts -/

section Transfer

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

end Transfer

/-! ### Transferring surjectivity to the morphism of charts -/

section SurjectiveTransfer

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

end SurjectiveTransfer

/-! ### The descent results for the situation of Stacks 084W

The results above, stated for `AlgebraicGeometry.Space.MorphismDescentSituation`, which imposes
no condition on the size of the index. What the proofs need is that the limits of the affine
charts of the system are formed inside the site, which is the chapter's convention of Section
70.2 (tag 07SD), the explicit hypothesis
`hconv : AlgebraicGeometry.Space.SiteContainsBaseChangeLimits B S hS D.base`. Each result is
also stated under `hb : AlgebraicGeometry.Space.IsSiteSmall B S hS D.base`, which implies the
convention by `AlgebraicGeometry.Space.IsSiteSmall.siteContainsBaseChangeLimits`. -/

section SituationChartData

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]

/-- A square of affine étale charts for a morphism descent system: an affine étale surjective
chart `V₀ ⟶ Y₀` of the target at the distinguished stage, an affine étale surjective chart
`U₀ ⟶ X₀ ×_{Y₀} V₀` of the fibre product, and the morphism `U₀ ⟶ V₀` of affine objects of the
site that the square induces. -/
private structure BridgedSituationChartSquare (D : MorphismDescentSituation B S hS hZ I) where
  /-- The affine charts of the distinguished stage have their limits inside the site, as data
  (`AlgebraicGeometry.Space.AffineChartSystem.LimitBridge`): this is what the chapter's
  convention of Section 70.2 (tag 07SD) grants there, and what bounded base changes at that
  stage provide as well. -/
  bridges : ∀ (U₀ : BigAffineFppf B S hS)
    (f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.base.obj (op D.initial))
    (C : AffineChartSystem B S hS (op D.initial) D.base U₀ f₀), Nonempty C.LimitBridge
  /-- The affine object of the site charting the target. -/
  targetObj : BigAffineFppf B S hS
  /-- The affine object of the site charting the fibre product of the morphism with the chart
  of the target. -/
  sourceObj : BigAffineFppf B S hS
  /-- The chart `V₀ ⟶ Y₀` of the target. -/
  targetChart : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj targetObj) ⟶ D.target₀
  /-- The chart `U₀ ⟶ X₀ ×_{Y₀} V₀` of the fibre product. -/
  cover : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj sourceObj) ⟶
    pullback D.map₀ targetChart
  /-- The morphism `U₀ ⟶ V₀` of affine objects of the site. -/
  chartMap : (BigAffineFppf.inclusion B S hS).obj sourceObj ⟶
    (BigAffineFppf.inclusion B S hS).obj targetObj
  /-- The chart of the target is étale. -/
  targetChart_etale : relEtale B S hS targetChart
  /-- The chart of the target is surjective. -/
  targetChart_surjective : relSurjective B S hS targetChart
  /-- The chart of the fibre product is étale. -/
  cover_etale : relEtale B S hS cover
  /-- The chart of the fibre product is surjective. -/
  cover_surjective : relSurjective B S hS cover
  /-- The morphism of affine objects is the second projection of the chart of the fibre
  product. -/
  yoneda_map_chartMap : yoneda.map chartMap = cover ≫ pullback.snd D.map₀ targetChart

/-- **Stacks 07SL, 07SN and 0CN2**, the choice of charts the three proofs begin with. A
quasi-compact quasi-separated morphism descent system admits a square of affine étale
charts. -/
private theorem nonempty_bridgedSituationChartSquare (D : MorphismDescentSituation B S hS hZ I)
    (hL : ∀ (U₀ : BigAffineFppf B S hS)
      (f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.base.obj (op D.initial))
      (C : AffineChartSystem B S hS (op D.initial) D.base U₀ f₀), Nonempty C.LimitBridge) :
    Nonempty (BridgedSituationChartSquare D) := by
  obtain ⟨U, chart, hU, hchartS, hchartE⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS D.target₀
      D.target₀_isAlgebraicSpace).mp D.target₀_quasiCompact
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  have hfibSpace : IsAlgebraicSpace B S hS (pullback D.map₀ chart) :=
    isAlgebraicSpace_pullback B S hS D.map₀ chart D.source₀_isAlgebraicSpace
      (isAlgebraicSpace_yoneda B S hS U) D.target₀_isAlgebraicSpace
  have hfib : IsQuasiCompactSpace B S hS (pullback D.map₀ chart) :=
    isQuasiCompactSpace_pullback B S hS hZ D.map₀ chart D.source₀_isAlgebraicSpace
      D.target₀_isAlgebraicSpace D.source₀_quasiCompact
      (isQuasiCompactSpace_yoneda_obj B S hS inferInstance) D.target₀_quasiSeparated
  obtain ⟨V, cover, hV, hcoverS, hcoverE⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS _ hfibSpace).mp hfib
  exact ⟨{ bridges := hL
           targetObj := ⟨U, hU⟩
           sourceObj := ⟨V, hV⟩
           targetChart := chart
           cover := cover
           chartMap := yoneda.preimage (cover ≫ pullback.snd D.map₀ chart)
           targetChart_etale := (isEtale_iff_presheaf_of_yoneda B S hS chart).mp hchartE
           targetChart_surjective := hchartS
           cover_etale := (isEtale_iff_presheaf_of_yoneda B S hS cover).mp hcoverE
           cover_surjective := hcoverS
           yoneda_map_chartMap := yoneda.map_preimage _ }⟩

/-- The chapter's convention of Section 70.2 (tag 07SD) puts the limits of the affine charts of
the distinguished stage inside the site
(`AlgebraicGeometry.Space.AffineChartSystem.limitBridgeOfLimitInSite`). -/
private theorem limitBridges_of_siteContainsBaseChangeLimits
    (D : MorphismDescentSituation B S hS hZ I) (hconv : SiteContainsBaseChangeLimits B S hS D.base)
    (U₀ : BigAffineFppf B S hS)
    (f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.base.obj (op D.initial))
    (C : AffineChartSystem B S hS (op D.initial) D.base U₀ f₀) : Nonempty C.LimitBridge :=
  have : Nonempty I := ⟨D.initial⟩
  ⟨C.limitBridgeOfLimitInSite (C.limitInSite_of_siteContainsBaseChangeLimits hconv)⟩

/-- Bounded base changes at the distinguished stage put the limits of its affine charts inside
the site (`AlgebraicGeometry.Space.AffineChartSystem.limitBridgeOfBounded`, Stacks 07SF). -/
private theorem limitBridges_of_hasBoundedBaseChanges
    (D : MorphismDescentSituation B S hS hZ I)
    (hb : HasBoundedBaseChanges B S hS (op D.initial) D.base)
    (U₀ : BigAffineFppf B S hS)
    (f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.base.obj (op D.initial))
    (C : AffineChartSystem B S hS (op D.initial) D.base U₀ f₀) : Nonempty C.LimitBridge :=
  have : Nonempty I := ⟨D.initial⟩
  ⟨AffineChartSystem.limitBridgeOfBounded (C := C)
    (AffineChartSystem.diagramBoundedBelow (C := C) hb)⟩

namespace BridgedSituationChartSquare

/-- The chart `U₀ ⟶ X₀` of the source. -/
private noncomputable def sourceChart {D : MorphismDescentSituation B S hS hZ I}
    (C : BridgedSituationChartSquare D) :
    yoneda.obj ((BigAffineFppf.inclusion B S hS).obj C.sourceObj) ⟶ D.source₀ :=
  C.cover ≫ pullback.fst D.map₀ C.targetChart

private theorem sourceChart_etale {D : MorphismDescentSituation B S hS hZ I} (C :
    BridgedSituationChartSquare D) :
    relEtale B S hS C.sourceChart := by
  have := isMultiplicative_presheaf_etale B S hS
  exact MorphismProperty.comp_mem _ _ _ C.cover_etale
    (MorphismProperty.of_isPullback (IsPullback.of_hasPullback D.map₀ C.targetChart).flip
      C.targetChart_etale)

private theorem sourceChart_surjective {D : MorphismDescentSituation B S hS hZ I}
    (C : BridgedSituationChartSquare D) : relSurjective B S hS C.sourceChart := by
  have := isMultiplicative_presheaf_surjective B S hS
  exact MorphismProperty.comp_mem _ _ _ C.cover_surjective
    (MorphismProperty.of_isPullback (IsPullback.of_hasPullback D.map₀ C.targetChart).flip
      C.targetChart_surjective)

private theorem comm {D : MorphismDescentSituation B S hS hZ I}
    (C : BridgedSituationChartSquare D) :
    yoneda.map C.chartMap ≫ C.targetChart = C.sourceChart ≫ D.map₀ := by
  rw [C.yoneda_map_chartMap]
  simp only [sourceChart, Category.assoc, pullback.condition]

/-- The chart of the distinguished stage `B₀` obtained from the chart of the target. -/
private noncomputable def baseChart {D : MorphismDescentSituation B S hS hZ I} (C :
    BridgedSituationChartSquare D) :
    yoneda.obj ((BigAffineFppf.inclusion B S hS).obj C.targetObj) ⟶ D.base.obj (op D.initial) :=
  C.targetChart ≫ D.targetToBase

/-- The system of affine charts of the stages, obtained by base changing the chart of the
distinguished stage along the transition morphisms. -/
private noncomputable def system {D : MorphismDescentSituation B S hS hZ I} (C :
    BridgedSituationChartSquare D) :
    AffineChartSystem B S hS (op D.initial) D.base C.targetObj C.baseChart :=
  affineChartSystem B S hS (op D.initial) D.base C.targetObj C.baseChart
    (fun {_ _} g ↦ D.transition_affine g)

/-- The limit of the system of affine charts of the stages. -/
private noncomputable def bridge {D : MorphismDescentSituation B S hS hZ I} (C :
    BridgedSituationChartSquare D) :
    AffineChartSystem.LimitBridge C.system :=
  (C.bridges _ _ C.system).some

/-- The diagram of affine schemes charting the stages at or beyond the distinguished one. -/
private noncomputable abbrev diagram {D : MorphismDescentSituation B S hS hZ I}
    (C : BridgedSituationChartSquare D) : Over (op D.initial) ⥤ Scheme.{u} :=
  C.system.schemeDiagram

/-- The limit cone of the diagram of affine schemes charting the stages. -/
private noncomputable abbrev cone {D : MorphismDescentSituation B S hS hZ I} (C :
    BridgedSituationChartSquare D) :
    Cone C.diagram :=
  (BigFppfOver.toScheme B S hS).mapCone C.bridge.cone

/-- The cone of charts of the stages is a limit cone. -/
private noncomputable def isLimit_cone {D : MorphismDescentSituation B S hS hZ I}
    (C : BridgedSituationChartSquare D) : IsLimit C.cone := C.bridge.schemeIsLimit

private theorem isAffine_diagram_obj {D : MorphismDescentSituation B S hS hZ I} (C :
    BridgedSituationChartSquare D)
    (j : Over (op D.initial)) : IsAffine (C.diagram.obj j) :=
  C.system.isAffine_obj j

private theorem isAffineHom_diagram_map {D : MorphismDescentSituation B S hS hZ I}
    (C : BridgedSituationChartSquare D) {j k : Over (op D.initial)} (g : j ⟶ k) :
    _root_.AlgebraicGeometry.IsAffineHom (C.diagram.map g) :=
  C.system.isAffineHom_map g

/-- The chart of a stage, as a morphism of the site. -/
private noncomputable def stageChart {D : MorphismDescentSituation B S hS hZ I} (C :
    BridgedSituationChartSquare D)
    (j : Over (op D.initial)) :
    C.system.siteDiagram.obj j ⟶ (BigAffineFppf.inclusion B S hS).obj C.targetObj :=
  yoneda.preimage (C.system.baseMap j)

private theorem yoneda_map_stageChart {D : MorphismDescentSituation B S hS hZ I} (C :
    BridgedSituationChartSquare D)
    (j : Over (op D.initial)) : yoneda.map (C.stageChart j) = C.system.baseMap j :=
  yoneda.map_preimage _

private theorem isPullback_stageChart {D : MorphismDescentSituation B S hS hZ I} (C :
    BridgedSituationChartSquare D)
    (j : Over (op D.initial)) :
    IsPullback (C.system.stageMap j) (yoneda.map (C.stageChart j)) (D.base.map j.hom)
      C.baseChart := by
  rw [C.yoneda_map_stageChart]
  exact C.system.isPullback j

private theorem siteDiagram_map_comp_stageChart {D : MorphismDescentSituation B S hS hZ I}
    (C : BridgedSituationChartSquare D) {j k : Over (op D.initial)} (g : j ⟶ k) :
    C.system.siteDiagram.map g ≫ C.stageChart k = C.stageChart j := by
  have hnat : yoneda.map (C.system.siteDiagram.map g) ≫ C.system.iso.hom.app k =
      C.system.iso.hom.app j ≫ (stageBaseChangeDiagram B S hS (op D.initial) D.base
        C.targetObj C.baseChart).map g := C.system.iso.hom.naturality g
  have hw : (stageBaseChangeDiagram B S hS (op D.initial) D.base C.targetObj C.baseChart).map g ≫
      stageBaseChangeSnd B S hS (op D.initial) D.base C.targetObj C.baseChart k =
      stageBaseChangeSnd B S hS (op D.initial) D.base C.targetObj C.baseChart j :=
    Over.w ((Over.post (X := op D.initial) D.base ⋙ Over.pullback C.baseChart).map g)
  apply yoneda.map_injective
  rw [yoneda.map_comp, C.yoneda_map_stageChart, C.yoneda_map_stageChart]
  simp only [AffineChartSystem.baseMap]
  rw [← Category.assoc, hnat, Category.assoc, hw]

/-- The chart of the limit, as a morphism of the site. -/
private noncomputable def limitChart {D : MorphismDescentSituation B S hS hZ I}
    (C : BridgedSituationChartSquare D) :
    C.bridge.cone.pt ⟶ (BigAffineFppf.inclusion B S hS).obj C.targetObj :=
  yoneda.preimage C.bridge.toBase

private theorem yoneda_map_limitChart {D : MorphismDescentSituation B S hS hZ I}
    (C : BridgedSituationChartSquare D) : yoneda.map C.limitChart = C.bridge.toBase :=
  yoneda.map_preimage _

private theorem isPullback_limitChart {D : MorphismDescentSituation B S hS hZ I}
    (C : BridgedSituationChartSquare D) :
    IsPullback C.bridge.toLimit (yoneda.map C.limitChart) (limit.π D.base (op D.initial))
      C.baseChart := by
  rw [C.yoneda_map_limitChart]
  exact C.bridge.isPullback

private theorem cone_π_comp_stageChart {D : MorphismDescentSituation B S hS hZ I}
    (C : BridgedSituationChartSquare D) (j : Over (op D.initial)) :
    C.bridge.cone.π.app j ≫ C.stageChart j = C.limitChart := by
  apply yoneda.map_injective
  rw [yoneda.map_comp, C.yoneda_map_stageChart, C.yoneda_map_limitChart]
  exact C.bridge.baseMap_comp j

/-- The chart of a stage is the pullback of the chart of the distinguished stage along the
transition morphism of the system. -/
private theorem isPullback_stageChart_baseAtToInitial
    {D : MorphismDescentSituation B S hS hZ I} (C : BridgedSituationChartSquare D)
    (j : Over (op D.initial)) :
    IsPullback (C.system.stageMap j) (yoneda.map (C.stageChart j))
      (D.baseAtToInitial j.left.unop (leOfHom j.hom.unop)) C.baseChart := by
  have h := C.isPullback_stageChart j
  rwa [show D.baseAtToInitial j.left.unop (leOfHom j.hom.unop) = D.base.map j.hom from
    congrArg D.base.map (Subsingleton.elim _ _)]

/-- The projection of the limit cone to a stage is compatible with the charts of the base. -/
private theorem cone_π_comp_map_stageChart {D : MorphismDescentSituation B S hS hZ I}
    (C : BridgedSituationChartSquare D) (j : Over (op D.initial)) :
    C.cone.π.app j ≫ (BigFppfOver.toScheme B S hS).map (C.stageChart j) =
      (BigFppfOver.toScheme B S hS).map C.limitChart := by
  show (BigFppfOver.toScheme B S hS).map (C.bridge.cone.π.app j) ≫ _ = _
  rw [← Functor.map_comp, C.cone_π_comp_stageChart j]

/-- The transition morphisms of the diagram of charts are compatible with the charts of the
base. -/
private theorem diagram_map_comp_map_stageChart {D : MorphismDescentSituation B S hS hZ I}
    (C : BridgedSituationChartSquare D) {j k : Over (op D.initial)} (g : j ⟶ k) :
    C.diagram.map g ≫ (BigFppfOver.toScheme B S hS).map (C.stageChart k) =
      (BigFppfOver.toScheme B S hS).map (C.stageChart j) := by
  show (BigFppfOver.toScheme B S hS).map (C.system.siteDiagram.map g) ≫ _ = _
  rw [← Functor.map_comp, C.siteDiagram_map_comp_stageChart g]

end BridgedSituationChartSquare

/-! ### Descending a property of the morphism along the limit -/

/-- The shared argument behind Stacks 07SL, 07SN and 0CN2. Suppose a property `Q` of morphisms
of algebraic spaces over `S` can be read off, for each base change of the given morphism along
a transition morphism, from the property `P` of the morphism of schemes obtained by base
changing the chart morphism `U₀ ⟶ V₀` of a square of affine étale charts, and suppose `P`
descends from a limit of affine schemes to a finite stage under a finiteness hypothesis `R`
stable under base change. If the chart morphism of `f₀` has `R` and the base change of `f₀` to
the limit has `Q`, then its base change to some stage has `Q`. -/
private theorem exists_prop_mapAt_of_prop_mapLimit_bridgedSituation
    {D : MorphismDescentSituation B S hS hZ I} (C : BridgedSituationChartSquare D)
    (Q : ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, (F ⟶ G) → Prop)
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (R : MorphismProperty Scheme.{u}) [R.IsStableUnderBaseChange]
    (hR : R ((BigFppfOver.toScheme B S hS).map C.chartMap))
    (htransfer : ∀ (B' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (t : B' ⟶ D.base.obj (op D.initial)) (W : BigFppfOver B S hS) (p : yoneda.obj W ⟶ B')
      (q : W ⟶ (BigAffineFppf.inclusion B S hS).obj C.targetObj),
      IsPullback p (yoneda.map q) t C.baseChart →
      ∀ f' : pullback t D.sourceToBase ⟶ pullback t D.targetToBase,
        f' ≫ pullback.fst t D.targetToBase = pullback.fst t D.sourceToBase →
        f' ≫ pullback.snd t D.targetToBase = pullback.snd t D.sourceToBase ≫ D.map₀ →
        IsAlgebraicSpace B S hS (pullback t D.sourceToBase) →
        IsAlgebraicSpace B S hS (pullback t D.targetToBase) →
        (Q f' ↔ P ((BigFppfOver.toScheme B S hS).map (pullback.snd C.chartMap q))))
    (hdescend : ∀ (j₀ : Over (op D.initial)) (X₀ Y₀ : Over (C.diagram.obj j₀)) (f₀ : X₀ ⟶ Y₀),
      CompactSpace X₀.left → QuasiSeparatedSpace X₀.left → CompactSpace Y₀.left →
      QuasiSeparatedSpace Y₀.left → R f₀.left →
      P ((Over.pullback (C.cone.π.app j₀)).map f₀).left →
      ∃ (j : Over (op D.initial)) (g : j ⟶ j₀),
        P ((Over.pullback (C.diagram.map g)).map f₀).left)
    (hlimit : Q D.mapLimit) :
    ∃ (i : I) (hi : D.initial ≤ i), Q (D.mapAt i hi) := by
  let j₀ : Over (op D.initial) := Over.mk (𝟙 (op D.initial))
  let fbase := pullback.snd ((BigFppfOver.toScheme B S hS).map C.chartMap)
    ((BigFppfOver.toScheme B S hS).map (C.stageChart j₀))
  let X₀ : Over (C.diagram.obj j₀) := Over.mk fbase
  let Y₀ : Over (C.diagram.obj j₀) := Over.mk (𝟙 (C.diagram.obj j₀))
  have hj₀aff : IsAffine ((BigFppfOver.toScheme B S hS).obj (C.system.siteDiagram.obj j₀)) :=
    C.isAffine_diagram_obj j₀
  have htgt : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj C.targetObj)) := C.targetObj.property
  have hsrc : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj C.sourceObj)) := C.sourceObj.property
  have hstageAff : _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B S hS).map (C.stageChart j₀)) := isAffineHom_of_isAffine _
  have hfstAff : _root_.AlgebraicGeometry.IsAffineHom
      (pullback.fst ((BigFppfOver.toScheme B S hS).map C.chartMap)
        ((BigFppfOver.toScheme B S hS).map (C.stageChart j₀))) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip hstageAff
  have hX₀aff : IsAffine X₀.left := isAffine_of_isAffineHom
    (pullback.fst ((BigFppfOver.toScheme B S hS).map C.chartMap)
      ((BigFppfOver.toScheme B S hS).map (C.stageChart j₀)))
  have hY₀aff : IsAffine Y₀.left := hj₀aff
  have hX₀c : CompactSpace X₀.left := Scheme.compactSpace_of_isAffine _
  have hY₀c : CompactSpace Y₀.left := Scheme.compactSpace_of_isAffine _
  have hX₀qs : QuasiSeparatedSpace X₀.left := inferInstance
  have hY₀qs : QuasiSeparatedSpace Y₀.left := inferInstance
  have hf₀R : R (Over.homMk fbase : X₀ ⟶ Y₀).left :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback
      ((BigFppfOver.toScheme B S hS).map C.chartMap)
      ((BigFppfOver.toScheme B S hS).map (C.stageChart j₀))) hR
  have hover : P ((Over.pullback (C.cone.π.app j₀)).map (Over.homMk fbase : X₀ ⟶ Y₀)).left := by
    refine (prop_overPullback_map_left_iff_pullback_snd P fbase (C.cone.π.app j₀)).mpr ?_
    refine (prop_iteratedPullback_snd_iff (BigFppfOver.toScheme B S hS) P C.chartMap
      (C.stageChart j₀) C.limitChart (C.cone.π.app j₀) (C.cone_π_comp_map_stageChart j₀)).mpr ?_
    exact (htransfer (limit D.base) (limit.π D.base (op D.initial)) C.bridge.cone.pt
      C.bridge.toLimit C.limitChart C.isPullback_limitChart D.mapLimit D.mapLimit_fst
      D.mapLimit_snd D.sourceLimit_isAlgebraicSpace D.targetLimit_isAlgebraicSpace).mp hlimit
  obtain ⟨j, g, hstage⟩ := hdescend j₀ X₀ Y₀ (Over.homMk fbase) hX₀c hX₀qs hY₀c hY₀qs hf₀R hover
  refine ⟨j.left.unop, leOfHom j.hom.unop, ?_⟩
  refine (htransfer _ _ _ (C.system.stageMap j) (C.stageChart j)
    (C.isPullback_stageChart_baseAtToInitial j) (D.mapAt _ _) (D.mapAt_fst _ _) (D.mapAt_snd _ _)
    (D.sourceAt_isAlgebraicSpace _ _) (D.targetAt_isAlgebraicSpace _ _)).mpr ?_
  exact (prop_iteratedPullback_snd_iff (BigFppfOver.toScheme B S hS) P C.chartMap
    (C.stageChart j₀) (C.stageChart j) (C.diagram.map g)
    (C.diagram_map_comp_map_stageChart g)).mp
    ((prop_overPullback_map_left_iff_pullback_snd P fbase (C.diagram.map g)).mp hstage)

/-! ### Reading flatness of a pulled back module on the chart square -/

/-- The chart `U₀ ⟶ X₀` of the source of a square of affine étale charts, as an object of the
small étale site of `X₀`. -/
private noncomputable def BridgedSituationChartSquare.sourceSmallEtale
    {D : MorphismDescentSituation B S hS hZ I} (C : BridgedSituationChartSquare D) :
    SmallEtale B S hS D.source₀ :=
  ⟨CostructuredArrow.mk C.sourceChart, C.sourceChart_etale⟩

/-- Let `t : B' ⟶ B₀` be a base change of the distinguished stage represented over the chart
`V₀` of the target by a morphism `q : W ⟶ V₀` of the site, and let `f'` be the base change of
`f₀` along `t`. A quasi-coherent `𝒪_{X₀}`-module `F₀` pulled back to `B' ×_{B₀} X₀` is flat over
`B' ×_{B₀} Y₀` exactly when the pullback of `F₀|_{U₀}` to `U₀ ×_{V₀} W` is flat over `W`. The
chart of `B' ×_{B₀} X₀` obtained by base change from `U₀ ⟶ X₀` is surjective, so the one chart
square suffices, by Stacks 05VU. -/
private theorem isFlatOver_modulePullback_baseChange_iff_situation
    {D : MorphismDescentSituation B S hS hZ I}
    (C : BridgedSituationChartSquare D)
    (F₀ : Modules.{u, u} B S hS D.source₀ D.source₀_isAlgebraicSpace)
    [F₀.IsQuasicoherentOnSite] (B' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (t : B' ⟶ D.base.obj (op D.initial)) (W : BigFppfOver B S hS) (p : yoneda.obj W ⟶ B')
    (q : W ⟶ (BigAffineFppf.inclusion B S hS).obj C.targetObj)
    (hp : IsPullback p (yoneda.map q) t C.baseChart)
    (f' : pullback t D.sourceToBase ⟶ pullback t D.targetToBase)
    (hf₁ : f' ≫ pullback.fst t D.targetToBase = pullback.fst t D.sourceToBase)
    (hf₂ : f' ≫ pullback.snd t D.targetToBase = pullback.snd t D.sourceToBase ≫ D.map₀)
    (hX : IsAlgebraicSpace B S hS (pullback t D.sourceToBase))
    (hY : IsAlgebraicSpace B S hS (pullback t D.targetToBase)) :
    IsFlatOver B S hS hX f' ((modulePullback B S hS
      (ObjectProperty.homMk (pullback.snd t D.sourceToBase) :
        (⟨pullback t D.sourceToBase, hX⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨D.source₀, D.source₀_isAlgebraicSpace⟩)).obj F₀) ↔
      _root_.AlgebraicGeometry.IsFlatOver
        ((BigFppfOver.toScheme B S hS).map (pullback.snd C.chartMap q)).toLRSHom.toShHom
        ((Scheme.Modules.pullback
          ((BigFppfOver.toScheme B S hS).map (pullback.fst C.chartMap q))).obj
          (restrictToChart B S hS D.source₀_isAlgebraicSpace F₀ C.sourceSmallEtale)) := by
  obtain ⟨a', b', sa, sb, comm⟩ := exists_chart_square_baseChange D.sourceToBase D.targetToBase
    D.map₀ D.map₀_over t C.sourceChart C.targetChart (yoneda.map C.chartMap) C.comm p
    (yoneda.map q) hp ((IsPullback.of_hasPullback C.chartMap q).map yoneda) f' hf₁ hf₂
  let π : (⟨pullback t D.sourceToBase, hX⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨D.source₀, D.source₀_isAlgebraicSpace⟩ :=
    ObjectProperty.homMk (pullback.snd t D.sourceToBase)
  let U : SmallEtale B S hS (pullback t D.sourceToBase) :=
    ⟨CostructuredArrow.mk a', MorphismProperty.of_isPullback sa C.sourceChart_etale⟩
  let V : SmallEtale B S hS (pullback t D.targetToBase) :=
    ⟨CostructuredArrow.mk b', MorphismProperty.of_isPullback sb C.targetChart_etale⟩
  let d : ChartDiagram B S hS (pullback t D.sourceToBase) (pullback t D.targetToBase) f' :=
    { U := U, V := V, g := pullback.snd C.chartMap q, comm := comm.symm }
  have qc : ((modulePullback B S hS π).obj F₀).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS π F₀ inferInstance
  have hd : IsFlatOverOnChartDiagram B S hS hX ((modulePullback B S hS π).obj F₀) d ↔
      _root_.AlgebraicGeometry.IsFlatOver
        ((BigFppfOver.toScheme B S hS).map (pullback.snd C.chartMap q)).toLRSHom.toShHom
        ((Scheme.Modules.pullback
          ((BigFppfOver.toScheme B S hS).map (pullback.fst C.chartMap q))).obj
          (restrictToChart B S hS D.source₀_isAlgebraicSpace F₀ C.sourceSmallEtale)) :=
    (_root_.AlgebraicGeometry.isFlatOver_iff_of_iso _
      (restrictToChartBaseChangeIso B S hS π F₀ inferInstance C.sourceSmallEtale U
        (pullback.fst C.chartMap q) sa.w)).symm
  refine ⟨fun h ↦ hd.mp (h d), fun h ↦ ?_⟩
  have hs : Function.Surjective (pointsMap B S hS (yoneda.obj d.U.obj.left) d.U.obj.hom) :=
    (surjective_iff_surjective_pointsMap B S hS _ hX _ a').mp
      (MorphismProperty.of_isPullback sa C.sourceChart_surjective)
  exact (isFlatOver_iff_forall_isFlatOverAtGeometricPoint B S hS
    (Xs := ⟨pullback t D.sourceToBase, hX⟩) (Ys := ⟨pullback t D.targetToBase, hY⟩)
    (ObjectProperty.homMk f') ((modulePullback B S hS π).obj F₀)).mpr fun xbar ↦
      isFlatOver_of_isFlatOverOnChartDiagram_of_surjective B S hS
        (Xs := ⟨pullback t D.sourceToBase, hX⟩) (Ys := ⟨pullback t D.targetToBase, hY⟩)
        (ObjectProperty.homMk f') ((modulePullback B S hS π).obj F₀) d hs (hd.mpr h) xbar

namespace MorphismDescentSituation

open _root_.AlgebraicGeometry.Space.MorphismDescentSituation.C1573
/-- The descent of étaleness for a situation whose affine charts at the distinguished stage
have their limits inside the site. -/
private theorem exists_isEtale_mapAt_of_limitBridges (D : MorphismDescentSituation B S hS hZ I)
    (hL : ∀ (U₀ : BigAffineFppf B S hS)
      (f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.base.obj (op D.initial))
      (C : AffineChartSystem B S hS (op D.initial) D.base U₀ f₀), Nonempty C.LimitBridge)
    (etale : IsEtale B S hS D.mapLimit) (fp : IsLocallyOfFinitePresentation B S hS D.map₀) :
    ∃ (i : I) (le : D.initial ≤ i), IsEtale B S hS (D.mapAt i le) := by
  obtain ⟨C⟩ := nonempty_bridgedSituationChartSquare D hL
  have : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hchartFp : LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map C.chartMap) :=
    fp _ _ C.sourceChart C.targetChart C.chartMap C.sourceChart_etale C.targetChart_etale C.comm
  refine exists_prop_mapAt_of_prop_mapLimit_bridgedSituation C (fun {_ _} f ↦ IsEtale B S hS f)
    (@AlgebraicGeometry.Etale.{u}) (@LocallyOfFinitePresentation) hchartFp ?_ ?_ etale
  · intro B' t W p q hp f' hf₁ hf₂ hX hY
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · exact prop_chartMap_of_holdsOnEveryEtaleChart _ D.sourceToBase D.targetToBase D.map₀
        D.map₀_over t C.sourceChart C.targetChart C.chartMap C.comm C.sourceChart_etale
        C.targetChart_etale p q hp f' hf₁ hf₂
        ((isEtale_iff_holdsOnEveryEtaleChart B S hS hX hY f').mp h)
    · obtain ⟨U', V', a', b', α, ha', hb', hs', hab', hP'⟩ :=
        holdsOnSurjectiveEtaleChart_of_prop_chartMap _ D.sourceToBase D.targetToBase D.map₀
          D.map₀_over t C.sourceChart C.targetChart C.chartMap C.comm C.sourceChart_etale
          C.targetChart_etale C.sourceChart_surjective p q hp f' hf₁ hf₂ h
      exact (isEtale_iff_exists_etale_chart_square B S hS hX hY f').mpr
        ⟨U', V', a', b', α, hab'.symm, hs', ha', hb', hP'⟩
  · intro j₀ X₀ Y₀ f₀ _ _ _ _ _ _
    have : Nonempty I := ⟨D.initial⟩
    have : IsDirectedOrder I := inferInstance
    have : IsFiltered I := inferInstance
    have : IsCofiltered Iᵒᵖ := inferInstance
    have : IsCofiltered (Over (op D.initial)) := inferInstance
    have : ∀ {j k : Over (op D.initial)} (g : j ⟶ k),
        _root_.AlgebraicGeometry.IsAffineHom (C.diagram.map g) :=
      fun g ↦ C.isAffineHom_diagram_map g
    have := C.isAffine_diagram_obj j₀
    have : CompactSpace (C.diagram.obj j₀) := Scheme.compactSpace_of_isAffine _
    have : QuasiSeparatedSpace (C.diagram.obj j₀) := inferInstance
    obtain ⟨jj, hjj⟩ :=
      exists_etale_pullback_of_isLimit C.diagram C.cone C.isLimit_cone j₀ X₀ Y₀ f₀
    exact ⟨jj.left, jj.hom, hjj⟩

/-- The descent of surjectivity for a situation whose affine charts at the distinguished stage
have their limits inside the site. -/
private theorem exists_isSurjective_mapAt_of_limitBridges
    (D : MorphismDescentSituation B S hS hZ I)
    (hL : ∀ (U₀ : BigAffineFppf B S hS)
      (f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.base.obj (op D.initial))
      (C : AffineChartSystem B S hS (op D.initial) D.base U₀ f₀), Nonempty C.LimitBridge)
    (surjective : IsSurjective B S hS D.mapLimit)
    (fp : IsLocallyOfFinitePresentation B S hS D.map₀) :
    ∃ (i : I) (le : D.initial ≤ i), IsSurjective B S hS (D.mapAt i le) := by
  obtain ⟨C⟩ := nonempty_bridgedSituationChartSquare D hL
  have hfibSpace : IsAlgebraicSpace B S hS (pullback D.map₀ C.targetChart) :=
    isAlgebraicSpace_pullback B S hS D.map₀ C.targetChart D.source₀_isAlgebraicSpace
      (isAlgebraicSpace_yoneda B S hS _) D.target₀_isAlgebraicSpace
  have hcover : IsSurjective B S hS C.cover :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS _ hfibSpace _ C.cover).mp
      C.cover_surjective
  have hchart : IsSurjective B S hS C.targetChart :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS _ D.target₀_isAlgebraicSpace _
      C.targetChart).mp C.targetChart_surjective
  have hchartFp : LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map C.chartMap) :=
    fp _ _ C.sourceChart C.targetChart C.chartMap C.sourceChart_etale C.targetChart_etale C.comm
  refine exists_prop_mapAt_of_prop_mapLimit_bridgedSituation C (fun {_ _} f ↦ IsSurjective B S hS f)
    (@Surjective.{u}) (@LocallyOfFinitePresentation) hchartFp ?_ ?_ surjective
  · intro B' t W p q hp f' hf₁ hf₂ hX hY
    rw [surjective_map_pullback_snd_iff, C.yoneda_map_chartMap]
    exact (isSurjective_chart_iff D.source₀_isAlgebraicSpace D.target₀_isAlgebraicSpace hX hY
      (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _)
      (isAlgebraicSpace_yoneda B S hS W) C.cover
      (isPullback_of_proj_eq D.sourceToBase D.targetToBase D.map₀ D.map₀_over t f' hf₁ hf₂)
      (isPullback_chart_baseChange C.targetChart D.targetToBase t p (yoneda.map q) hp)
      hcover hchart).symm
  · intro j₀ X₀ Y₀ f₀ _ _ _ _ _ _
    have : Nonempty I := ⟨D.initial⟩
    have : IsDirectedOrder I := inferInstance
    have : IsFiltered I := inferInstance
    have : IsCofiltered Iᵒᵖ := inferInstance
    have : IsCofiltered (Over (op D.initial)) := inferInstance
    have : ∀ {j k : Over (op D.initial)} (g : j ⟶ k),
        _root_.AlgebraicGeometry.IsAffineHom (C.diagram.map g) :=
      fun g ↦ C.isAffineHom_diagram_map g
    have := C.isAffine_diagram_obj j₀
    have : CompactSpace (C.diagram.obj j₀) := Scheme.compactSpace_of_isAffine _
    have : QuasiSeparatedSpace (C.diagram.obj j₀) := inferInstance
    exact exists_surjective_baseChange_of_surjective_limitBaseChange C.diagram C.cone
      C.isLimit_cone j₀ X₀ Y₀ f₀

/-- **Stacks 08K0**, flatness of a module. In the situation of Stacks 084W, let `F₀` be a
quasi-coherent `𝒪_{X₀}`-module, with pullbacks `F_i` to `X_i` and `F` to `X`. If `F` is flat over
`Y`, `F₀` is of finite presentation and `f₀` is locally of finite presentation, then `F_i` is
flat over `Y_i` for some stage `i ≥ 0`.

This is the statement under the chapter's convention of Section 70.2 (tag 07SD), which asks
nothing of the index. The proof is that of
`AlgebraicGeometry.Space.MorphismDescentSystem.exists_isFlatOver_mapAt`: flatness of `F` is read
on a square of affine étale charts, descended to a stage of the system of charts by Stacks 05LY,
and read back on the charts of that stage. -/
theorem C1573.exists_isFlatOver_mapAt_of_siteContainsBaseChangeLimits
    (D : MorphismDescentSituation B S hS hZ I) (hconv : SiteContainsBaseChangeLimits B S hS D.base)
    (F₀ : Modules.{u, u} B S hS D.source₀ D.source₀_isAlgebraicSpace)
    [F₀.IsQuasicoherentOnSite] [F₀.IsFinitePresentationOnSite]
    (flat : IsFlatOver B S hS D.sourceLimit_isAlgebraicSpace D.mapLimit
      ((modulePullback B S hS (ObjectProperty.homMk
        (pullback.snd (limit.π D.base (op D.initial)) D.sourceToBase) :
          (⟨D.sourceLimit, D.sourceLimit_isAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨D.source₀, D.source₀_isAlgebraicSpace⟩)).obj F₀))
    (fp : IsLocallyOfFinitePresentation B S hS D.map₀) :
    ∃ (i : I) (le : D.initial ≤ i), IsFlatOver B S hS (D.sourceAt_isAlgebraicSpace i le)
      (D.mapAt i le) ((modulePullback B S hS (ObjectProperty.homMk
        (pullback.snd (D.baseAtToInitial i le) D.sourceToBase) :
          (⟨D.sourceAt i le, D.sourceAt_isAlgebraicSpace i le⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨D.source₀, D.source₀_isAlgebraicSpace⟩)).obj F₀) := by
  obtain ⟨C⟩ := nonempty_bridgedSituationChartSquare D
    (limitBridges_of_siteContainsBaseChangeLimits D hconv)
  let H := BigFppfOver.toScheme B S hS
  let M : (H.obj ((BigAffineFppf.inclusion B S hS).obj C.sourceObj)).Modules :=
    restrictToChart B S hS D.source₀_isAlgebraicSpace F₀ C.sourceSmallEtale
  have : M.IsQuasicoherent :=
    isQuasicoherent_restrictToChart B S hS ⟨D.source₀, D.source₀_isAlgebraicSpace⟩ F₀
      inferInstance C.sourceSmallEtale
  have : M.IsFinitePresentation :=
    isFinitePresentation_restrictToChart B S hS ⟨D.source₀, D.source₀_isAlgebraicSpace⟩ F₀
      inferInstance inferInstance C.sourceSmallEtale
  have hchartFp : LocallyOfFinitePresentation (H.map C.chartMap) :=
    fp _ _ C.sourceChart C.targetChart C.chartMap C.sourceChart_etale
      C.targetChart_etale C.comm
  let j₀ : Over (op D.initial) := Over.mk (𝟙 (op D.initial))
  let st₀ := H.map (C.stageChart j₀)
  let g := pullback.snd (H.map C.chartMap) st₀
  let N := (Scheme.Modules.pullback (pullback.fst (H.map C.chartMap) st₀)).obj M
  have key : ∀ {W : BigFppfOver B S hS} (s : H.obj W ⟶ C.diagram.obj j₀)
      (q : W ⟶ (BigAffineFppf.inclusion B S hS).obj C.targetObj), s ≫ st₀ = H.map q →
      (_root_.AlgebraicGeometry.IsFlatOver (pullback.snd g s).toLRSHom.toShHom
          ((Scheme.Modules.pullback (pullback.fst g s)).obj N) ↔
        _root_.AlgebraicGeometry.IsFlatOver (H.map (pullback.snd C.chartMap q)).toLRSHom.toShHom
          ((Scheme.Modules.pullback (H.map (pullback.fst C.chartMap q))).obj M)) := by
    intro W s q hs
    have h₁ := (IsPullback.of_hasPullback g s).paste_horiz
      (IsPullback.of_hasPullback (H.map C.chartMap) st₀)
    rw [hs] at h₁
    exact (_root_.AlgebraicGeometry.isFlatOver_iff_of_iso _
      ((schemeModulePullbackCompIso (pullback.fst g s) (pullback.fst (H.map C.chartMap) st₀)).app
        M)).trans (isFlatOver_modulePullback_iff_of_isPullback h₁
          ((IsPullback.of_hasPullback C.chartMap q).map H) M)
  have hlimit := (key (C.cone.π.app j₀) C.limitChart (C.cone_π_comp_map_stageChart j₀)).mpr
    ((isFlatOver_modulePullback_baseChange_iff_situation C F₀ (limit D.base)
      (limit.π D.base (op D.initial)) C.bridge.cone.pt C.bridge.toLimit C.limitChart
      C.isPullback_limitChart D.mapLimit D.mapLimit_fst D.mapLimit_snd
      D.sourceLimit_isAlgebraicSpace D.targetLimit_isAlgebraicSpace).mp flat)
  have : Nonempty I := ⟨D.initial⟩
  have : IsCofiltered (Over (op D.initial)) := inferInstance
  have : ∀ {j k : Over (op D.initial)} (e : j ⟶ k),
      _root_.AlgebraicGeometry.IsAffineHom (C.diagram.map e) :=
    fun e ↦ C.isAffineHom_diagram_map e
  have : ∀ j, CompactSpace (C.diagram.obj j) :=
    fun j ↦ have := C.isAffine_diagram_obj j; Scheme.compactSpace_of_isAffine _
  have : ∀ j, QuasiSeparatedSpace (C.diagram.obj j) :=
    fun j ↦ have := C.isAffine_diagram_obj j; inferInstance
  have : IsAffine (H.obj ((BigAffineFppf.inclusion B S hS).obj C.sourceObj)) :=
    C.sourceObj.property
  have : IsAffine (H.obj ((BigAffineFppf.inclusion B S hS).obj C.targetObj)) :=
    C.targetObj.property
  have : IsAffine (H.obj (C.system.siteDiagram.obj j₀)) := C.isAffine_diagram_obj j₀
  have : _root_.AlgebraicGeometry.IsAffineHom st₀ := isAffineHom_of_isAffine _
  have : _root_.AlgebraicGeometry.IsAffineHom (pullback.fst (H.map C.chartMap) st₀) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip ‹_›
  have : IsAffine (pullback (H.map C.chartMap) st₀) :=
    isAffine_of_isAffineHom (pullback.fst (H.map C.chartMap) st₀)
  have : CompactSpace ↥(pullback (H.map C.chartMap) st₀) := Scheme.compactSpace_of_isAffine _
  have : LocallyOfFinitePresentation g :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (H.map C.chartMap) st₀) hchartFp
  have : N.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ M
  have : SheafOfModules.IsFinitePresentation (R := structureSheafRing
      (H.obj ((BigAffineFppf.inclusion B S hS).obj C.sourceObj)).toRingedSpace) M := ‹_›
  have : N.IsFinitePresentation :=
    Stacks.SheafOfModules.modulePullback_isFinitePresentation
      (pullback.fst (H.map C.chartMap) st₀).toLRSHom.toShHom M
  obtain ⟨j, e, hj⟩ := exists_isFlatOver_modulePullback_pullback_snd C.diagram C.cone
    C.isLimit_cone j₀ g N hlimit
  exact ⟨j.left.unop, leOfHom j.hom.unop,
    (isFlatOver_modulePullback_baseChange_iff_situation C F₀ _ _ _ (C.system.stageMap j)
      (C.stageChart j) (C.isPullback_stageChart_baseAtToInitial j) (D.mapAt _ _)
      (D.mapAt_fst _ _) (D.mapAt_snd _ _) (D.sourceAt_isAlgebraicSpace _ _)
      (D.targetAt_isAlgebraicSpace _ _)).mpr
      ((key (C.diagram.map e) (C.stageChart j) (C.diagram_map_comp_map_stageChart e)).mp hj)⟩

/-- The descent of universal injectivity for a situation whose affine charts at the
distinguished stage have their limits inside the site. -/
private theorem exists_universallyInjective_mapAt_of_limitBridges
    (D : MorphismDescentSituation B S hS hZ I)
    (hL : ∀ (U₀ : BigAffineFppf B S hS)
      (f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.base.obj (op D.initial))
      (C : AffineChartSystem B S hS (op D.initial) D.base U₀ f₀), Nonempty C.LimitBridge)
    (injective : UniversallyInjective B S hS D.mapLimit)
    (ft : IsLocallyOfFiniteType B S hS D.map₀) :
    ∃ (i : I) (le : D.initial ≤ i), UniversallyInjective B S hS (D.mapAt i le) := by
  let Δ : MorphismDescentSituation B S hS hZ I :=
    { D with
      target₀ := pullback D.map₀ D.map₀
      targetToBase := pullback.fst D.map₀ D.map₀ ≫ D.sourceToBase
      map₀ := pullback.diagonal D.map₀
      map₀_over := by rw [pullback.diagonal_fst_assoc]
      target₀_isAlgebraicSpace :=
        isAlgebraicSpace_pullback B S hS D.map₀ D.map₀ D.source₀_isAlgebraicSpace
          D.source₀_isAlgebraicSpace D.target₀_isAlgebraicSpace
      target₀_quasiCompact :=
        isQuasiCompactSpace_pullback B S hS hZ D.map₀ D.map₀ D.source₀_isAlgebraicSpace
          D.target₀_isAlgebraicSpace D.source₀_quasiCompact D.source₀_quasiCompact
          D.target₀_quasiSeparated
      target₀_quasiSeparated :=
        isAbsolutelyQuasiSeparated_pullback B S hS hZ D.map₀ D.map₀
          D.source₀_isAlgebraicSpace D.source₀_isAlgebraicSpace D.target₀_isAlgebraicSpace
          D.source₀_quasiSeparated D.source₀_quasiSeparated }
  have hdiag₀ : IsLocallyOfFinitePresentation B S hS Δ.map₀ :=
    isLocallyOfFinitePresentation_pullbackDiagonal B S hS D.map₀ D.source₀_isAlgebraicSpace
      D.target₀_isAlgebraicSpace ft
  have hdiagLim : IsSurjective B S hS Δ.mapLimit :=
    (isSurjective_baseChange_diagonal_iff B S hS D.sourceToBase D.targetToBase
      (limit.π D.base (op D.initial)) D.map₀ D.map₀_over D.mapLimit D.mapLimit_fst
      D.mapLimit_snd).mpr
      (isSurjective_diagonal_of_universallyInjective B S hS D.sourceLimit_isAlgebraicSpace
        D.mapLimit injective)
  obtain ⟨i, hi, hsurj⟩ := exists_isSurjective_mapAt_of_limitBridges Δ hL hdiagLim hdiag₀
  refine ⟨i, hi, universallyInjective_of_isSurjective_diagonal B S hS (D.mapAt i hi) ?_⟩
  exact (isSurjective_baseChange_diagonal_iff B S hS D.sourceToBase D.targetToBase
    (D.baseAtToInitial i hi) D.map₀ D.map₀_over (D.mapAt i hi) (D.mapAt_fst i hi)
    (D.mapAt_snd i hi)).mp hsurj

/-! ### The covariant indexing of Stacks 07SK

Stacks 084W, and every statement above, indexes the system by a directed preorder `I` and carries
it as the *contravariant* diagram `base : Iᵒᵖ ⥤ …`, reading a stage beyond the distinguished one
as an inequality `0 ≤ i`. The library's Stacks 07SK —
`AlgebraicGeometry.Space.exists_model_of_finitePresentation` and its fullness and faithfulness
companions — instead consumes a *cofiltered category* together with a *covariant* diagram out of
it, and states its conclusions over a morphism `j ⟶ i` of that category.

These are two readings of one and the same system: `base` is already a covariant functor on the
category `Iᵒᵖ`, which is cofiltered because a directed preorder is filtered. The declarations
below record that, and restate Stacks 0CN2 over a morphism of `Iᵒᵖ` rather than over an
inequality in `I`, so that it composes with Stacks 07SK without either result being reindexed.
-/

end MorphismDescentSituation

end SituationChartData

/-! ### The affine chart square of a morphism descent system -/

section ChartData

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]

namespace ChartSquare

end ChartSquare

/-! ### Descending a property of the morphism along the limit -/

/-! ### Reading flatness of a pulled back module on the chart square -/

namespace MorphismDescentSystem

/-! ### The covariant indexing of Stacks 07SK

Stacks 084W, and every statement above, indexes the system by a directed preorder `I` and carries
it as the *contravariant* diagram `base : Iᵒᵖ ⥤ …`, reading a stage beyond the distinguished one
as an inequality `0 ≤ i`. The library's Stacks 07SK —
`AlgebraicGeometry.Space.exists_model_of_finitePresentation` and its fullness and faithfulness
companions — instead consumes a *cofiltered category* together with a *covariant* diagram out of
it, and states its conclusions over a morphism `j ⟶ i` of that category.

These are two readings of one and the same system: `base` is already a covariant functor on the
category `Iᵒᵖ`, which is cofiltered because a directed preorder is filtered. The declarations
below record that, and restate Stacks 0CN2 over a morphism of `Iᵒᵖ` rather than over an
inequality in `I`, so that it composes with Stacks 07SK without either result being reindexed.
-/

end MorphismDescentSystem

end ChartData


end AlgebraicGeometry.Space

end
