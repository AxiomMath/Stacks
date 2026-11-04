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
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystemSizeBound
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismsSupplement
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
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties

/-!
# Supplement to `DescendingMorphismProperties`

The results of this module extend those of
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties`.
They use imports, universe variables or `open` declarations that the base module does not
have, and are kept in a module of their own so that its header is unchanged.

## Main results

* `baseChangedChart`
* `isPullback_baseChangedChart`
* `baseChangedChart_comp_fst`
* `ChartSquareOfChartsBounded`
* `nonempty_chartSquare_of_chartsBounded`
* `sourceChart`
* `sourceChart_etale`
* `sourceChart_surjective`
* `comm`
* `baseChart`
* `system`
* `bridge`
* `diagram`
* `cone`
* `isLimit_cone`
* `isAffine_diagram_obj`
* `isAffineHom_diagram_map`
* `stageChart`
* `yoneda_map_stageChart`
* `isPullback_stageChart`
* `siteDiagram_map_comp_stageChart`
* `limitChart`
* `yoneda_map_limitChart`
* `isPullback_limitChart`
* `cone_π_comp_stageChart`
* `sourceSmallEtale`
* `exists_prop_mapAt_of_prop_mapLimit_of_chartsBounded`
* `isFlatOver_modulePullback_baseChange_iff_of_chartsBounded`
* `exists_isEtale_mapAt`
* `exists_isSurjective_mapAt`
* `exists_isSmooth_mapAt`
* `exists_isFlat_mapAt`
* `exists_isFlatOver_mapAt`
* `exists_universallyInjective_mapAt`
* `exists_hasRelativeDimensionLE_mapAt`
* `isCofiltered_op`
* `base_map_eq_baseAtToInitial`
* `exists_isSmooth_mapAt_op`
-/

/-! ### The generalizations made by this development

The declarations below restate, under weaker hypotheses or at more general universes, declarations
of this file whose statements are kept as they are above. Each carries the name of the declaration
it generalizes with the suffix `_of_chartsBounded` (or `OfChartsBounded` for a definition). -/

universe w v u

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

namespace AlgebraicGeometry.Space

/-! ### Chart squares of a base change -/

/-! ### Relative étaleness and surjectivity of charts -/

/-! ### The base change of a chart of an algebraic space over a representable base -/

section ChartOverRepresentableBase

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Ti Tj Vs : BigFppfOver B S hS}

/-- **The base change along `h_m` of a chart `a : h_V ⟶ Z` of an algebraic space over the
representable base `h_{T_i}`**, for a morphism `m : T_j ⟶ T_i` of the site and a `qa` with
`yoneda.map qa = a ≫ z`. Its source is the representable `h_{V ×_{T_i} T_j}`, the fibre product
being formed in the site. -/
noncomputable def baseChangedChart (z : Z ⟶ yoneda.obj Ti) (a : yoneda.obj Vs ⟶ Z)
    (qa : Vs ⟶ Ti) (hqa : yoneda.map qa = a ≫ z) (m : Tj ⟶ Ti) :
    yoneda.obj (pullback qa m) ⟶ pullback (yoneda.map m) z :=
  pullback.lift (yoneda.map (pullback.snd qa m)) (yoneda.map (pullback.fst qa m) ≫ a) (by
    rw [Category.assoc, ← hqa, ← yoneda.map_comp, ← yoneda.map_comp, pullback.condition])

/-- The base changed chart is a base change of the chart. -/
theorem isPullback_baseChangedChart (z : Z ⟶ yoneda.obj Ti) (a : yoneda.obj Vs ⟶ Z)
    (qa : Vs ⟶ Ti) (hqa : yoneda.map qa = a ≫ z) (m : Tj ⟶ Ti) :
    IsPullback (yoneda.map (pullback.fst qa m)) (baseChangedChart z a qa hqa m) a
      (pullback.snd (yoneda.map m) z) := by
  have h : IsPullback (yoneda.map (pullback.snd qa m)) (yoneda.map (pullback.fst qa m))
      (yoneda.map m) (a ≫ z) := by
    rw [← hqa]
    exact ((IsPullback.of_hasPullback qa m).flip).map yoneda
  exact isPullback_chart_baseChange a z (yoneda.map m) _ _ h

/-- The base changed chart lies over the base change of the structure morphism. -/
theorem baseChangedChart_comp_fst (z : Z ⟶ yoneda.obj Ti) (a : yoneda.obj Vs ⟶ Z)
    (qa : Vs ⟶ Ti) (hqa : yoneda.map qa = a ≫ z) (m : Tj ⟶ Ti) :
    baseChangedChart z a qa hqa m ≫ pullback.fst (yoneda.map m) z =
      yoneda.map (pullback.snd qa m) :=
  pullback.lift_fst _ _ _

end ChartOverRepresentableBase

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

/-! ### Transferring a chart-local property to the morphism of charts -/

/-! ### Transferring surjectivity to the morphism of charts -/

/-! ### The affine chart square of a morphism descent system -/

section ChartData

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]

/-- A square of affine étale charts for a morphism descent system: an affine étale surjective
chart `V₀ ⟶ Y₀` of the target at the distinguished stage, an affine étale surjective chart
`U₀ ⟶ X₀ ×_{Y₀} V₀` of the fibre product, and the morphism `U₀ ⟶ V₀` of affine objects of the
site that the square induces. -/
private structure ChartSquareOfChartsBounded
    (D : MorphismDescentSystemOfChartsBounded B S hS hZ I) where
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
private theorem nonempty_chartSquare_of_chartsBounded
    (D : MorphismDescentSystemOfChartsBounded B S hS hZ I) :
    Nonempty (ChartSquareOfChartsBounded D) := by
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
  exact ⟨{ targetObj := ⟨U, hU⟩
           sourceObj := ⟨V, hV⟩
           targetChart := chart
           cover := cover
           chartMap := yoneda.preimage (cover ≫ pullback.snd D.map₀ chart)
           targetChart_etale := (isEtale_iff_presheaf_of_yoneda B S hS chart).mp hchartE
           targetChart_surjective := hchartS
           cover_etale := (isEtale_iff_presheaf_of_yoneda B S hS cover).mp hcoverE
           cover_surjective := hcoverS
           yoneda_map_chartMap := yoneda.map_preimage _ }⟩

namespace ChartSquareOfChartsBounded

/-- The chart `U₀ ⟶ X₀` of the source. -/
private noncomputable def sourceChart {D : MorphismDescentSystemOfChartsBounded B S hS hZ I}
    (C : ChartSquareOfChartsBounded D) :
    yoneda.obj ((BigAffineFppf.inclusion B S hS).obj C.sourceObj) ⟶ D.source₀ :=
  C.cover ≫ pullback.fst D.map₀ C.targetChart

private theorem sourceChart_etale {D : MorphismDescentSystemOfChartsBounded B S hS hZ I}
    (C : ChartSquareOfChartsBounded D) :
    relEtale B S hS C.sourceChart := by
  have := isMultiplicative_presheaf_etale B S hS
  exact MorphismProperty.comp_mem _ _ _ C.cover_etale
    (MorphismProperty.of_isPullback (IsPullback.of_hasPullback D.map₀ C.targetChart).flip
      C.targetChart_etale)

private theorem sourceChart_surjective {D : MorphismDescentSystemOfChartsBounded B S hS hZ I}
    (C : ChartSquareOfChartsBounded D) : relSurjective B S hS C.sourceChart := by
  have := isMultiplicative_presheaf_surjective B S hS
  exact MorphismProperty.comp_mem _ _ _ C.cover_surjective
    (MorphismProperty.of_isPullback (IsPullback.of_hasPullback D.map₀ C.targetChart).flip
      C.targetChart_surjective)

private theorem comm {D : MorphismDescentSystemOfChartsBounded B S hS hZ I}
    (C : ChartSquareOfChartsBounded D) :
    yoneda.map C.chartMap ≫ C.targetChart = C.sourceChart ≫ D.map₀ := by
  rw [C.yoneda_map_chartMap]
  simp only [sourceChart, Category.assoc, pullback.condition]

/-- The chart of the distinguished stage `B₀` obtained from the chart of the target. -/
private noncomputable def baseChart {D : MorphismDescentSystemOfChartsBounded B S hS hZ I}
    (C : ChartSquareOfChartsBounded D) :
    yoneda.obj ((BigAffineFppf.inclusion B S hS).obj C.targetObj) ⟶ D.base.obj (op D.initial) :=
  C.targetChart ≫ D.targetToBase

/-- The system of affine charts of the stages, obtained by base changing the chart of the
distinguished stage along the transition morphisms. -/
private noncomputable def system {D : MorphismDescentSystemOfChartsBounded B S hS hZ I}
    (C : ChartSquareOfChartsBounded D) :
    AffineChartSystem B S hS (op D.initial) D.base C.targetObj C.baseChart :=
  affineChartSystem B S hS (op D.initial) D.base C.targetObj C.baseChart
    (fun {_ _} g ↦ D.transition_affine g)

/-- The limit of the system of affine charts of the stages. -/
private noncomputable def bridge {D : MorphismDescentSystemOfChartsBounded B S hS hZ I}
    (C : ChartSquareOfChartsBounded D) :
    AffineChartSystem.LimitBridge C.system := by
  haveI : Nonempty I := ⟨D.initial⟩
  haveI : IsDirectedOrder I := inferInstance
  haveI : IsFiltered I := inferInstance
  haveI : IsCofiltered Iᵒᵖ := inferInstance
  exact AffineChartSystem.limitBridgeOfSizeBound C.system (D.chartsBounded.sizeBound C.system)

/-- The diagram of affine schemes charting the stages at or beyond the distinguished one. -/
private noncomputable abbrev diagram {D : MorphismDescentSystemOfChartsBounded B S hS hZ I}
    (C : ChartSquareOfChartsBounded D) : Over (op D.initial) ⥤ Scheme.{u} :=
  C.system.schemeDiagram

/-- The limit cone of the diagram of affine schemes charting the stages. -/
private noncomputable abbrev cone {D : MorphismDescentSystemOfChartsBounded B S hS hZ I}
    (C : ChartSquareOfChartsBounded D) :
    Cone C.diagram :=
  (BigFppfOver.toScheme B S hS).mapCone C.bridge.cone

/-- The cone of charts of the stages is a limit cone. -/
private noncomputable def isLimit_cone {D : MorphismDescentSystemOfChartsBounded B S hS hZ I}
    (C : ChartSquareOfChartsBounded D) : IsLimit C.cone := C.bridge.schemeIsLimit

private theorem isAffine_diagram_obj {D : MorphismDescentSystemOfChartsBounded B S hS hZ I}
    (C : ChartSquareOfChartsBounded D)
    (j : Over (op D.initial)) : IsAffine (C.diagram.obj j) :=
  C.system.isAffine_obj j

private theorem isAffineHom_diagram_map {D : MorphismDescentSystemOfChartsBounded B S hS hZ I}
    (C : ChartSquareOfChartsBounded D) {j k : Over (op D.initial)} (g : j ⟶ k) :
    _root_.AlgebraicGeometry.IsAffineHom (C.diagram.map g) :=
  C.system.isAffineHom_map g

/-- The chart of a stage, as a morphism of the site. -/
private noncomputable def stageChart {D : MorphismDescentSystemOfChartsBounded B S hS hZ I}
    (C : ChartSquareOfChartsBounded D)
    (j : Over (op D.initial)) :
    C.system.siteDiagram.obj j ⟶ (BigAffineFppf.inclusion B S hS).obj C.targetObj :=
  yoneda.preimage (C.system.baseMap j)

private theorem yoneda_map_stageChart {D : MorphismDescentSystemOfChartsBounded B S hS hZ I}
    (C : ChartSquareOfChartsBounded D)
    (j : Over (op D.initial)) : yoneda.map (C.stageChart j) = C.system.baseMap j :=
  yoneda.map_preimage _

private theorem isPullback_stageChart {D : MorphismDescentSystemOfChartsBounded B S hS hZ I}
    (C : ChartSquareOfChartsBounded D)
    (j : Over (op D.initial)) :
    IsPullback (C.system.stageMap j) (yoneda.map (C.stageChart j)) (D.base.map j.hom)
      C.baseChart := by
  rw [C.yoneda_map_stageChart]
  exact C.system.isPullback j

private theorem siteDiagram_map_comp_stageChart
    {D : MorphismDescentSystemOfChartsBounded B S hS hZ I}
    (C : ChartSquareOfChartsBounded D) {j k : Over (op D.initial)} (g : j ⟶ k) :
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
private noncomputable def limitChart {D : MorphismDescentSystemOfChartsBounded B S hS hZ I}
    (C : ChartSquareOfChartsBounded D) :
    C.bridge.cone.pt ⟶ (BigAffineFppf.inclusion B S hS).obj C.targetObj :=
  yoneda.preimage C.bridge.toBase

private theorem yoneda_map_limitChart {D : MorphismDescentSystemOfChartsBounded B S hS hZ I}
    (C : ChartSquareOfChartsBounded D) : yoneda.map C.limitChart = C.bridge.toBase :=
  yoneda.map_preimage _

private theorem isPullback_limitChart {D : MorphismDescentSystemOfChartsBounded B S hS hZ I}
    (C : ChartSquareOfChartsBounded D) :
    IsPullback C.bridge.toLimit (yoneda.map C.limitChart) (limit.π D.base (op D.initial))
      C.baseChart := by
  rw [C.yoneda_map_limitChart]
  exact C.bridge.isPullback

private theorem cone_π_comp_stageChart {D : MorphismDescentSystemOfChartsBounded B S hS hZ I}
    (C : ChartSquareOfChartsBounded D) (j : Over (op D.initial)) :
    C.bridge.cone.π.app j ≫ C.stageChart j = C.limitChart := by
  apply yoneda.map_injective
  rw [yoneda.map_comp, C.yoneda_map_stageChart, C.yoneda_map_limitChart]
  exact C.bridge.baseMap_comp j

/-- The chart `U₀ ⟶ X₀` of the source, as an object of the small étale site of `X₀`. -/
private noncomputable def sourceSmallEtale {D : MorphismDescentSystemOfChartsBounded B S hS hZ I}
    (C : ChartSquareOfChartsBounded D) : SmallEtale B S hS D.source₀ :=
  ⟨CostructuredArrow.mk C.sourceChart, C.sourceChart_etale⟩

/-- The chart morphism `U₀ ⟶ V₀` of a chart square is locally of finite presentation when the
morphism of the descent system is. -/
private theorem locallyOfFinitePresentation_chartMap
    {D : MorphismDescentSystemOfChartsBounded B S hS hZ I}
    (C : ChartSquareOfChartsBounded D) (fp : IsLocallyOfFinitePresentation B S hS D.map₀) :
    LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map C.chartMap) :=
  fp _ _ C.sourceChart C.targetChart C.chartMap C.sourceChart_etale C.targetChart_etale C.comm

/-- The pullback of the stage chart `U_j ⟶ V₀` along the chart morphism has an affine projection
to the source chart. -/
private theorem isAffineHom_pullback_fst_stageChart
    {D : MorphismDescentSystemOfChartsBounded B S hS hZ I}
    (C : ChartSquareOfChartsBounded D) (j : Over (op D.initial)) :
    _root_.AlgebraicGeometry.IsAffineHom (pullback.fst
      ((BigFppfOver.toScheme B S hS).map C.chartMap)
      ((BigFppfOver.toScheme B S hS).map (C.stageChart j))) := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (C.system.siteDiagram.obj j)) :=
    C.isAffine_diagram_obj j
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj C.targetObj)) := C.targetObj.property
  have : _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B S hS).map (C.stageChart j)) := isAffineHom_of_isAffine _
  exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip ‹_›

/-- The pullback of the stage chart `U_j ⟶ V₀` along the chart morphism is affine. -/
private theorem isAffine_pullback_chartMap_stageChart
    {D : MorphismDescentSystemOfChartsBounded B S hS hZ I}
    (C : ChartSquareOfChartsBounded D) (j : Over (op D.initial)) :
    IsAffine (pullback ((BigFppfOver.toScheme B S hS).map C.chartMap)
      ((BigFppfOver.toScheme B S hS).map (C.stageChart j))) :=
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj C.sourceObj)) := C.sourceObj.property
  have := C.isAffineHom_pullback_fst_stageChart j
  isAffine_of_isAffineHom (pullback.fst _ _)

/-- The projection of the limit cone is compatible with the chart of the limit and the stage
chart, as morphisms of schemes. -/
private theorem cone_π_comp_map_stageChart
    {D : MorphismDescentSystemOfChartsBounded B S hS hZ I}
    (C : ChartSquareOfChartsBounded D) (j : Over (op D.initial)) :
    C.cone.π.app j ≫ (BigFppfOver.toScheme B S hS).map (C.stageChart j) =
      (BigFppfOver.toScheme B S hS).map C.limitChart := by
  change (BigFppfOver.toScheme B S hS).map (C.bridge.cone.π.app j) ≫ _ = _
  rw [← Functor.map_comp, C.cone_π_comp_stageChart j]

/-- The transition morphisms of the diagram of schemes are compatible with the stage charts. -/
private theorem diagram_map_comp_map_stageChart
    {D : MorphismDescentSystemOfChartsBounded B S hS hZ I}
    (C : ChartSquareOfChartsBounded D) {j k : Over (op D.initial)} (g : j ⟶ k) :
    C.diagram.map g ≫ (BigFppfOver.toScheme B S hS).map (C.stageChart k) =
      (BigFppfOver.toScheme B S hS).map (C.stageChart j) := by
  change (BigFppfOver.toScheme B S hS).map (C.system.siteDiagram.map g) ≫ _ = _
  rw [← Functor.map_comp, C.siteDiagram_map_comp_stageChart g]

/-- The stage chart of `j` is a base change of the chart of the target along the transition
morphism to the distinguished stage. -/
private theorem isPullback_stageChart_baseAtToInitial
    {D : MorphismDescentSystemOfChartsBounded B S hS hZ I}
    (C : ChartSquareOfChartsBounded D) (j : Over (op D.initial)) :
    IsPullback (C.system.stageMap j) (yoneda.map (C.stageChart j))
      (D.baseAtToInitial j.left.unop (leOfHom j.hom.unop)) C.baseChart := by
  have h := C.isPullback_stageChart j
  rwa [show D.baseAtToInitial j.left.unop (leOfHom j.hom.unop) = D.base.map j.hom from
    congrArg D.base.map (Subsingleton.elim _ _)]

/-- The instances on the diagram of affine schemes needed to descend a property of a morphism
from the limit to a finite stage. -/
private theorem with_diagram_instances
    {D : MorphismDescentSystemOfChartsBounded B S hS hZ I}
    (C : ChartSquareOfChartsBounded D) {α : Prop}
    (k : IsCofiltered (Over (op D.initial)) →
      (∀ {j k : Over (op D.initial)} (g : j ⟶ k),
        _root_.AlgebraicGeometry.IsAffineHom (C.diagram.map g)) →
      (∀ j, CompactSpace (C.diagram.obj j)) → (∀ j, QuasiSeparatedSpace (C.diagram.obj j)) → α) :
    α :=
  have : Nonempty I := ⟨D.initial⟩
  have := C.isAffine_diagram_obj
  k inferInstance (fun g ↦ C.isAffineHom_diagram_map g)
    (fun _ ↦ Scheme.compactSpace_of_isAffine _) fun _ ↦ inferInstance

/-- A property read off from the chart morphism, for the base change of a chart square along a
chart `q`, holds on every étale chart as soon as it holds for the chart morphism. -/
private theorem chartMap_prop_of_holdsOnEveryEtaleChart
    {D : MorphismDescentSystemOfChartsBounded B S hS hZ I}
    (C : ChartSquareOfChartsBounded D) (P : MorphismProperty Scheme.{u})
    {B' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (t : B' ⟶ D.base.obj (op D.initial))
    {W : BigFppfOver B S hS} (p : yoneda.obj W ⟶ B')
    (q : W ⟶ (BigAffineFppf.inclusion B S hS).obj C.targetObj)
    (hp : IsPullback p (yoneda.map q) t C.baseChart)
    (f' : pullback t D.sourceToBase ⟶ pullback t D.targetToBase)
    (hf₁ : f' ≫ pullback.fst t D.targetToBase = pullback.fst t D.sourceToBase)
    (hf₂ : f' ≫ pullback.snd t D.targetToBase = pullback.snd t D.sourceToBase ≫ D.map₀)
    (h : HoldsOnEveryEtaleChart B S hS P f') :
    P ((BigFppfOver.toScheme B S hS).map (pullback.snd C.chartMap q)) :=
  prop_chartMap_of_holdsOnEveryEtaleChart P D.sourceToBase D.targetToBase D.map₀
    D.map₀_over t C.sourceChart C.targetChart C.chartMap C.comm C.sourceChart_etale
    C.targetChart_etale p q hp f' hf₁ hf₂ h

/-- Conversely, a property of the chart morphism, for the base change along a chart `q`, gives
the property on a surjective family of étale charts. -/
private theorem holdsOnSurjectiveEtaleChart_of_chartMap_prop
    {D : MorphismDescentSystemOfChartsBounded B S hS hZ I}
    (C : ChartSquareOfChartsBounded D) (P : MorphismProperty Scheme.{u})
    {B' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (t : B' ⟶ D.base.obj (op D.initial))
    {W : BigFppfOver B S hS} (p : yoneda.obj W ⟶ B')
    (q : W ⟶ (BigAffineFppf.inclusion B S hS).obj C.targetObj)
    (hp : IsPullback p (yoneda.map q) t C.baseChart)
    (f' : pullback t D.sourceToBase ⟶ pullback t D.targetToBase)
    (hf₁ : f' ≫ pullback.fst t D.targetToBase = pullback.fst t D.sourceToBase)
    (hf₂ : f' ≫ pullback.snd t D.targetToBase = pullback.snd t D.sourceToBase ≫ D.map₀)
    (h : P ((BigFppfOver.toScheme B S hS).map (pullback.snd C.chartMap q))) :
    HoldsOnSurjectiveEtaleChart B S hS P f' :=
  holdsOnSurjectiveEtaleChart_of_prop_chartMap P D.sourceToBase D.targetToBase D.map₀
    D.map₀_over t C.sourceChart C.targetChart C.chartMap C.comm C.sourceChart_etale
    C.targetChart_etale C.sourceChart_surjective p q hp f' hf₁ hf₂ h

/-- For a property `P` local in the étale topology on source and target, `P` of the base change
of the chart morphism along `q` is equivalent to `P` holding on every étale chart of the base
change `f'` of the morphism. -/
private theorem holdsOnEveryEtaleChart_iff_chartMap_prop
    {D : MorphismDescentSystemOfChartsBounded B S hS hZ I}
    (C : ChartSquareOfChartsBounded D) (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P)
    (B' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (t : B' ⟶ D.base.obj (op D.initial))
    (W : BigFppfOver B S hS) (p : yoneda.obj W ⟶ B')
    (q : W ⟶ (BigAffineFppf.inclusion B S hS).obj C.targetObj)
    (hp : IsPullback p (yoneda.map q) t C.baseChart)
    (f' : pullback t D.sourceToBase ⟶ pullback t D.targetToBase)
    (hf₁ : f' ≫ pullback.fst t D.targetToBase = pullback.fst t D.sourceToBase)
    (hf₂ : f' ≫ pullback.snd t D.targetToBase = pullback.snd t D.sourceToBase ≫ D.map₀)
    (hX : IsAlgebraicSpace B S hS (pullback t D.sourceToBase))
    (hY : IsAlgebraicSpace B S hS (pullback t D.targetToBase)) :
    HoldsOnEveryEtaleChart B S hS P f' ↔
      P ((BigFppfOver.toScheme B S hS).map (pullback.snd C.chartMap q)) :=
  ⟨C.chartMap_prop_of_holdsOnEveryEtaleChart P t p q hp f' hf₁ hf₂, fun h ↦
    (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P hP hX hY f').mpr
      (C.holdsOnSurjectiveEtaleChart_of_chartMap_prop P t p q hp f' hf₁ hf₂ h)⟩

end ChartSquareOfChartsBounded

/-! ### Descending a property of the morphism along the limit -/

/-- The shared argument behind Stacks 07SL, 07SN and 0CN2. Suppose a property `Q` of morphisms
of algebraic spaces over `S` can be read off, for each base change of the given morphism along
a transition morphism, from the property `P` of the morphism of schemes obtained by base
changing the chart morphism `U₀ ⟶ V₀` of a square of affine étale charts, and suppose `P`
descends from a limit of affine schemes to a finite stage under a finiteness hypothesis `R`
stable under base change. If the chart morphism of `f₀` has `R` and the base change of `f₀` to
the limit has `Q`, then its base change to some stage has `Q`. -/
private theorem exists_prop_mapAt_of_prop_mapLimit_of_chartsBounded
    {D : MorphismDescentSystemOfChartsBounded B S hS hZ I}
    (C : ChartSquareOfChartsBounded D)
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
  have hX₀aff : IsAffine X₀.left := C.isAffine_pullback_chartMap_stageChart j₀
  have hY₀aff : IsAffine Y₀.left := C.isAffine_diagram_obj j₀
  have hX₀c : CompactSpace X₀.left := Scheme.compactSpace_of_isAffine _
  have hY₀c : CompactSpace Y₀.left := Scheme.compactSpace_of_isAffine _
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
  obtain ⟨j, g, hstage⟩ := hdescend j₀ X₀ Y₀ (Over.homMk fbase) hX₀c inferInstance hY₀c
    inferInstance hf₀R hover
  refine ⟨j.left.unop, leOfHom j.hom.unop, ?_⟩
  refine (htransfer _ _ _ (C.system.stageMap j) (C.stageChart j)
    (C.isPullback_stageChart_baseAtToInitial j) (D.mapAt _ _) (D.mapAt_fst _ _)
    (D.mapAt_snd _ _) (D.sourceAt_isAlgebraicSpace _ _)
    (D.targetAt_isAlgebraicSpace _ _)).mpr ?_
  exact (prop_iteratedPullback_snd_iff (BigFppfOver.toScheme B S hS) P C.chartMap
    (C.stageChart j₀) (C.stageChart j) (C.diagram.map g)
    (C.diagram_map_comp_map_stageChart g)).mp
    ((prop_overPullback_map_left_iff_pullback_snd P fbase (C.diagram.map g)).mp hstage)

/-! ### Reading flatness of a pulled back module on the chart square -/

/-- Let `t : B' ⟶ B₀` be a base change of the distinguished stage represented over the chart
`V₀` of the target by a morphism `q : W ⟶ V₀` of the site, and let `f'` be the base change of
`f₀` along `t`. A quasi-coherent `𝒪_{X₀}`-module `F₀` pulled back to `B' ×_{B₀} X₀` is flat over
`B' ×_{B₀} Y₀` exactly when the pullback of `F₀|_{U₀}` to `U₀ ×_{V₀} W` is flat over `W`. The
chart of `B' ×_{B₀} X₀` obtained by base change from `U₀ ⟶ X₀` is surjective, so the one chart
square suffices, by Stacks 05VU. -/
private theorem isFlatOver_modulePullback_baseChange_iff_of_chartsBounded
    {D : MorphismDescentSystemOfChartsBounded B S hS hZ I}
    (C : ChartSquareOfChartsBounded D)
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

namespace MorphismDescentSystemOfChartsBounded

/-- **Stacks 07SL.** In the situation of Stacks 084W, if the base change `f` of `f₀` to the
limit `B` is étale and `f₀` is locally of finite presentation, then the base change `f_i` of
`f₀` to some stage `B_i` is étale. -/
theorem exists_isEtale_mapAt (D : MorphismDescentSystemOfChartsBounded B S hS hZ I)
    (etale : IsEtale B S hS D.mapLimit) (fp : IsLocallyOfFinitePresentation B S hS D.map₀) :
    ∃ (i : I) (le : D.initial ≤ i), IsEtale B S hS (D.mapAt i le) := by
  obtain ⟨C⟩ := nonempty_chartSquare_of_chartsBounded D
  have : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine exists_prop_mapAt_of_prop_mapLimit_of_chartsBounded C (fun {_ _} f ↦ IsEtale B S hS f)
    (@AlgebraicGeometry.Etale.{u}) (@LocallyOfFinitePresentation)
    (C.locallyOfFinitePresentation_chartMap fp) ?_ ?_ etale
  · intro B' t W p q hp f' hf₁ hf₂ hX hY
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · exact C.chartMap_prop_of_holdsOnEveryEtaleChart _ t p q hp f' hf₁ hf₂
        ((isEtale_iff_holdsOnEveryEtaleChart B S hS hX hY f').mp h)
    · obtain ⟨U', V', a', b', α, ha', hb', hs', hab', hP'⟩ :=
        C.holdsOnSurjectiveEtaleChart_of_chartMap_prop _ t p q hp f' hf₁ hf₂ h
      exact (isEtale_iff_exists_etale_chart_square B S hS hX hY f').mpr
        ⟨U', V', a', b', α, hab'.symm, hs', ha', hb', hP'⟩
  · intro j₀ X₀ Y₀ f₀ h₁ h₂ h₃ h₄ h₅ h₆
    refine C.with_diagram_instances fun _ _ _ _ ↦ ?_
    obtain ⟨jj, hjj⟩ :=
      exists_etale_pullback_of_isLimit C.diagram C.cone C.isLimit_cone j₀ X₀ Y₀ f₀
    exact ⟨jj.left, jj.hom, hjj⟩

/-- **Stacks 07SN.** In the situation of Stacks 084W, if the base change `f` of `f₀` to the
limit `B` is surjective and `f₀` is locally of finite presentation, then the base change `f_i`
of `f₀` to some stage `B_i` is surjective. -/
theorem exists_isSurjective_mapAt
    (D : MorphismDescentSystemOfChartsBounded B S hS hZ I)
    (surjective : IsSurjective B S hS D.mapLimit)
    (fp : IsLocallyOfFinitePresentation B S hS D.map₀) :
    ∃ (i : I) (le : D.initial ≤ i), IsSurjective B S hS (D.mapAt i le) := by
  obtain ⟨C⟩ := nonempty_chartSquare_of_chartsBounded D
  have hfibSpace : IsAlgebraicSpace B S hS (pullback D.map₀ C.targetChart) :=
    isAlgebraicSpace_pullback B S hS D.map₀ C.targetChart D.source₀_isAlgebraicSpace
      (isAlgebraicSpace_yoneda B S hS _) D.target₀_isAlgebraicSpace
  have hcover : IsSurjective B S hS C.cover :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS _ hfibSpace _ C.cover).mp
      C.cover_surjective
  have hchart : IsSurjective B S hS C.targetChart :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS _ D.target₀_isAlgebraicSpace _
      C.targetChart).mp C.targetChart_surjective
  refine exists_prop_mapAt_of_prop_mapLimit_of_chartsBounded C (fun {_ _} f ↦ IsSurjective B S hS f)
    (@Surjective.{u}) (@LocallyOfFinitePresentation)
    (C.locallyOfFinitePresentation_chartMap fp) ?_ ?_ surjective
  · intro B' t W p q hp f' hf₁ hf₂ hX hY
    rw [surjective_map_pullback_snd_iff, C.yoneda_map_chartMap]
    exact (isSurjective_chart_iff D.source₀_isAlgebraicSpace D.target₀_isAlgebraicSpace hX hY
      (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _)
      (isAlgebraicSpace_yoneda B S hS W) C.cover
      (isPullback_of_proj_eq D.sourceToBase D.targetToBase D.map₀ D.map₀_over t f' hf₁ hf₂)
      (isPullback_chart_baseChange C.targetChart D.targetToBase t p (yoneda.map q) hp)
      hcover hchart).symm
  · intro j₀ X₀ Y₀ f₀ h₁ h₂ h₃ h₄ h₅ h₆
    refine C.with_diagram_instances fun _ _ _ _ ↦ ?_
    exact exists_surjective_baseChange_of_surjective_limitBaseChange C.diagram C.cone
      C.isLimit_cone j₀ X₀ Y₀ f₀

/-- **Stacks 0CN2.** In the situation of Stacks 084W, if the base change `f` of `f₀` to the
limit `B` is smooth and `f₀` is locally of finite presentation, then the base change `f_i` of
`f₀` to some stage `B_i` is smooth. -/
theorem exists_isSmooth_mapAt (D : MorphismDescentSystemOfChartsBounded B S hS hZ I)
    (smooth : IsSmooth B S hS D.mapLimit) (fp : IsLocallyOfFinitePresentation B S hS D.map₀) :
    ∃ (i : I) (le : D.initial ≤ i), IsSmooth B S hS (D.mapAt i le) := by
  obtain ⟨C⟩ := nonempty_chartSquare_of_chartsBounded D
  have : MorphismProperty.RespectsIso (@Smooth.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine exists_prop_mapAt_of_prop_mapLimit_of_chartsBounded C (fun {_ _} f ↦ IsSmooth B S hS f)
    (@Smooth.{u}) (@LocallyOfFinitePresentation)
    (C.locallyOfFinitePresentation_chartMap fp) ?_ ?_ smooth
  · exact C.holdsOnEveryEtaleChart_iff_chartMap_prop (@Smooth.{u})
      Smooth.isEtaleLocalOnSourceAndTarget
  · intro j₀ X₀ Y₀ f₀ h₁ h₂ h₃ h₄ h₅ h₆
    refine C.with_diagram_instances fun _ _ _ _ ↦ ?_
    exact exists_smooth_baseChange_of_smooth_limitBaseChange C.diagram C.cone j₀ X₀ Y₀ f₀
      C.isLimit_cone

/-- **Stacks 08K0**, flatness of the morphism. In the situation of Stacks 084W, if `f₀` is locally
of finite presentation and its base change `f : X ⟶ Y` to the limit is flat, then its base change
`f_i : X_i ⟶ Y_i` to some stage `i ≥ 0` is flat. -/
theorem exists_isFlat_mapAt
    (D : MorphismDescentSystemOfChartsBounded B S hS hZ I) (flat : IsFlat B S hS D.mapLimit)
    (fp : IsLocallyOfFinitePresentation B S hS D.map₀) :
    ∃ (i : I) (le : D.initial ≤ i), IsFlat B S hS (D.mapAt i le) := by
  obtain ⟨C⟩ := nonempty_chartSquare_of_chartsBounded D
  have : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine exists_prop_mapAt_of_prop_mapLimit_of_chartsBounded C (fun {_ _} f ↦ IsFlat B S hS f)
    (@_root_.AlgebraicGeometry.Flat.{u}) (@LocallyOfFinitePresentation)
    (C.locallyOfFinitePresentation_chartMap fp) ?_ ?_ flat
  · exact C.holdsOnEveryEtaleChart_iff_chartMap_prop (@_root_.AlgebraicGeometry.Flat.{u})
      _root_.AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget
  · intro j₀ X₀ Y₀ f₀ h₁ h₂ h₃ h₄ h₅ h₆
    refine C.with_diagram_instances fun _ _ _ _ ↦ ?_
    exact exists_flat_baseChange_of_limitBaseChange C.diagram C.cone j₀ X₀ Y₀ f₀ C.isLimit_cone

/-- **Stacks 08K0**, flatness of a module. In the situation of Stacks 084W, let `F₀` be a
quasi-coherent `𝒪_{X₀}`-module, with pullbacks `F_i` to `X_i` and `F` to `X`. If `F` is flat over
`Y`, `F₀` is of finite presentation and `f₀` is locally of finite presentation, then `F_i` is flat
over `Y_i` for some stage `i ≥ 0`. -/
theorem exists_isFlatOver_mapAt (D : MorphismDescentSystemOfChartsBounded B S hS hZ I)
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
  obtain ⟨C⟩ := nonempty_chartSquare_of_chartsBounded D
  let H := BigFppfOver.toScheme B S hS
  let M : (H.obj ((BigAffineFppf.inclusion B S hS).obj C.sourceObj)).Modules :=
    restrictToChart B S hS D.source₀_isAlgebraicSpace F₀ C.sourceSmallEtale
  have : M.IsQuasicoherent :=
    isQuasicoherent_restrictToChart B S hS ⟨D.source₀, D.source₀_isAlgebraicSpace⟩ F₀
      inferInstance C.sourceSmallEtale
  have : M.IsFinitePresentation :=
    isFinitePresentation_restrictToChart B S hS ⟨D.source₀, D.source₀_isAlgebraicSpace⟩ F₀
      inferInstance inferInstance C.sourceSmallEtale
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
    ((isFlatOver_modulePullback_baseChange_iff_of_chartsBounded C F₀ (limit D.base)
      (limit.π D.base (op D.initial)) C.bridge.cone.pt C.bridge.toLimit C.limitChart
      C.isPullback_limitChart D.mapLimit D.mapLimit_fst D.mapLimit_snd
      D.sourceLimit_isAlgebraicSpace D.targetLimit_isAlgebraicSpace).mp flat)
  refine C.with_diagram_instances fun _ _ _ _ ↦ ?_
  have := C.isAffineHom_pullback_fst_stageChart j₀
  have := C.isAffine_pullback_chartMap_stageChart j₀
  have : CompactSpace ↥(pullback (H.map C.chartMap) st₀) := Scheme.compactSpace_of_isAffine _
  have : LocallyOfFinitePresentation g :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (H.map C.chartMap) st₀)
      (C.locallyOfFinitePresentation_chartMap fp)
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
    (isFlatOver_modulePullback_baseChange_iff_of_chartsBounded C F₀ _ _ _ (C.system.stageMap j)
      (C.stageChart j) (C.isPullback_stageChart_baseAtToInitial j) (D.mapAt _ _)
      (D.mapAt_fst _ _) (D.mapAt_snd _ _) (D.sourceAt_isAlgebraicSpace _ _)
      (D.targetAt_isAlgebraicSpace _ _)).mpr
      ((key (C.diagram.map e) (C.stageChart j) (C.diagram_map_comp_map_stageChart e)).mp hj)⟩

/-- **Stacks 084X.** In the situation of Stacks 084W, if the base change `f` of `f₀` to the
limit `B` is universally injective and `f₀` is locally of finite type, then the base change
`f_i` of `f₀` to some stage `B_i` is universally injective. -/
theorem exists_universallyInjective_mapAt
    (D : MorphismDescentSystemOfChartsBounded B S hS hZ I)
    (injective : UniversallyInjective B S hS D.mapLimit)
    (ft : IsLocallyOfFiniteType B S hS D.map₀) :
    ∃ (i : I) (le : D.initial ≤ i), UniversallyInjective B S hS (D.mapAt i le) := by
  let Δ : MorphismDescentSystemOfChartsBounded B S hS hZ I :=
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
  obtain ⟨i, hi, hsurj⟩ := exists_isSurjective_mapAt Δ hdiagLim hdiag₀
  refine ⟨i, hi, universallyInjective_of_isSurjective_diagonal B S hS (D.mapAt i hi) ?_⟩
  exact (isSurjective_baseChange_diagonal_iff B S hS D.sourceToBase D.targetToBase
    (D.baseAtToInitial i hi) D.map₀ D.map₀_over (D.mapAt i hi) (D.mapAt_fst i hi)
    (D.mapAt_snd i hi)).mp hsurj

/-- **Stacks 0D4K.** In the situation of Stacks 084W, if the base change `f` of `f₀` to the
limit `B` has relative dimension at most `d` and `f₀` is locally of finite type, then the base
change `f_i` of `f₀` to some stage `B_i` has relative dimension at most `d`. -/
theorem exists_hasRelativeDimensionLE_mapAt (D : MorphismDescentSystemOfChartsBounded B S hS hZ I)
    (d : ℕ)
    (dimension : HasRelativeDimensionLE d B S hS D.mapLimit)
    (ft : IsLocallyOfFiniteType B S hS D.map₀) :
    ∃ (i : I) (le : D.initial ≤ i), HasRelativeDimensionLE d B S hS (D.mapAt i le) := by
  obtain ⟨C⟩ := nonempty_chartSquare_of_chartsBounded D
  have hchartFt : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map C.chartMap) :=
    ft _ _ C.sourceChart C.targetChart C.chartMap C.sourceChart_etale C.targetChart_etale C.comm
  refine exists_prop_mapAt_of_prop_mapLimit_of_chartsBounded C
    (fun {_ _} f ↦ HasRelativeDimensionLE d B S hS f) (fiberDimensionLE d) (@LocallyOfFiniteType)
    hchartFt ?_ ?_ dimension
  · intro B' t W p q hp f' hf₁ hf₂ hX hY
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · exact C.chartMap_prop_of_holdsOnEveryEtaleChart _ t p q hp f' hf₁ hf₂
        (fiberDimensionLE_chartMap_of_hasRelativeDimensionLE B S hS f' d h)
    · exact hasRelativeDimensionLE_of_holdsOnSurjectiveEtaleChart B S hS hX f' d
        (C.holdsOnSurjectiveEtaleChart_of_chartMap_prop _ t p q hp f' hf₁ hf₂ h)
  · intro j₀ X₀ Y₀ f₀ h₁ h₂ h₃ h₄ h₅ h₆
    refine C.with_diagram_instances fun _ _ _ _ ↦ ?_
    exact exists_fiberDimensionLE_baseChange_of_limitBaseChange C.diagram C.isLimit_cone j₀
      X₀ Y₀ f₀ d h₆

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

/-- The index category of a morphism descent system, read covariantly, is cofiltered. This is the
indexing the library's Stacks 07SK consumes: a directed preorder is filtered, so its opposite is
cofiltered, and the distinguished stage makes the index nonempty. -/
theorem isCofiltered_op (D : MorphismDescentSystemOfChartsBounded B S hS hZ I) : IsCofiltered Iᵒᵖ :=
  have : Nonempty I := ⟨D.initial⟩
  inferInstance

/-- A morphism of the index category `Iᵒᵖ` into the distinguished stage induces exactly the
transition morphism of the inequality it encodes. The morphisms of a preorder read as a category
are unique, so there is nothing to choose. -/
theorem base_map_eq_baseAtToInitial (D : MorphismDescentSystemOfChartsBounded B S hS hZ I) {j : Iᵒᵖ}
    (g : j ⟶ op D.initial) :
    D.base.map g = D.baseAtToInitial j.unop (leOfHom g.unop) :=
  congrArg D.base.map (congrArg Quiver.Hom.op (homOfLE_leOfHom g.unop)).symm

/-- **Stacks 0CN2 in the covariant indexing of Stacks 07SK.** In the situation of Stacks 084W, if
the base change `f` of `f₀` to the limit `B` is smooth and `f₀` is locally of finite presentation,
then there is a morphism `j ⟶ 0` of the cofiltered index category `Iᵒᵖ` along which the base
change of `f₀` is smooth.

This is `AlgebraicGeometry.Space.MorphismDescentSystemOfChartsBounded.exists_isSmooth_mapAt` with
its conclusion read over a morphism of `Iᵒᵖ` instead of an inequality of `I`; the transition
morphism is the same one, by
`AlgebraicGeometry.Space.MorphismDescentSystemOfChartsBounded.base_map_eq_baseAtToInitial`. It is
the shape in which the conclusions of Stacks 07SK are stated, so the two can be used together. -/
theorem exists_isSmooth_mapAt_op (D : MorphismDescentSystemOfChartsBounded B S hS hZ I)
    (smooth : IsSmooth B S hS D.mapLimit) (fp : IsLocallyOfFinitePresentation B S hS D.map₀) :
    ∃ (j : Iᵒᵖ) (g : j ⟶ op D.initial),
      IsSmooth B S hS (D.mapAt j.unop (leOfHom g.unop)) := by
  obtain ⟨i, hi, h⟩ := exists_isSmooth_mapAt D smooth fp
  exact ⟨op i, (homOfLE hi).op, h⟩

end MorphismDescentSystemOfChartsBounded

end ChartData

end AlgebraicGeometry.Space

end
