module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuadrupleGeometricPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartQuadrupleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPointEtaleLift
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkCohomologyMapEtaleTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange

/-!
# Conditions (2) and (3) of Stacks 0DKG

For a cartesian square of algebraic spaces, `K ∈ D_QCoh(𝒪_X)`, `K' ∈ D_QCoh(𝒪_{X'})` and
`φ : L(g')^*K ⟶ K'`, condition (2) of Stacks 0DKG asks the chart condition of Stacks 0DJ8 on every
étale diagram of schemes `U ⟶ V ⟵ V'` over `X ⟶ Y ⟵ Y'` with `U' = V' ×_V U`, for the objects of
`D_QCoh` of the schemes corresponding to `La^*K` and `L(a')^*K'` (Stacks 071Q, 08GH); condition (3)
asks it on one such diagram with `U' ⟶ X'` surjective. On an affine étale quadruple the
condition on the whole chart is condition (1) at the geometric points coming from `U'`, and every
geometric point of `X'` comes from the affine quadruple of a chart of a surjective diagram.

## Main definitions

* `AlgebraicGeometry.Space.DiagramChartwiseBaseChange`: the chart condition on one diagram.
* `AlgebraicGeometry.Space.EtaleDiagramChartwiseBaseChange`: condition (2) of Stacks 0DKG.
* `AlgebraicGeometry.Space.SurjectiveDiagramChartwiseBaseChange`: condition (3) of Stacks 0DKG.

## Main results

* `AlgebraicGeometry.Space.surjectiveDiagramChartwiseBaseChange_of_etaleDiagramChartwiseBaseChange`:
  (2) implies (3).
* `isIso_affineQuadrupleChart_comparison_iff_forall_isIso_geometricStalkBaseChangeCohomologyMap`:
  the whole chart of an affine étale quadruple against condition (1).
* `AlgebraicGeometry.Space.exists_baseChangeChart_geometricPoint_lift`: geometric points of `X'`
  lift to the affine quadruples of the charts of a surjective diagram.
-/

/- Instances that come into scope here only through the base versions of imported modules,
and that would change the elaboration below (universe joins, the small model of `D(R)`). -/
-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

attribute [-instance] SheafOfModules.hasBinBiprod

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section ChartPoints

attribute [local instance] BaseChangeChart.isOpenImmersion_incU BaseChangeChart.isOpenImmersion_incV
  BaseChangeChart.isOpenImmersion_incV'

variable {U V U' V' : BigFppfOver B S hS} {f₀ : U ⟶ V} {g₀ : V' ⟶ V} {f₀' : U' ⟶ V'}
  {g₀' : U' ⟶ U}

/-- The open `U'` of a chart lies in the image of the fibre product of its affine quadruple. -/
theorem incU'_apply_mem_range_chartQuadrupleι'
    (ch : BaseChangeChart ((BigFppfOver.toScheme B S hS).map f₀)
      ((BigFppfOver.toScheme B S hS).map g₀) ((BigFppfOver.toScheme B S hS).map f₀')
      ((BigFppfOver.toScheme B S hS).map g₀'))
    (hpb : IsPullback g₀' f₀' f₀ g₀) (y : Spec ch.A') :
    ch.incU' y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (chartQuadrupleι' ch hpb)) := by
  have e : (chartQuadrupleWhole ch).incU' ≫
      (BigFppfOver.toScheme B S hS).map (chartQuadrupleι' ch hpb) = ch.incU' :=
    eq_of_heq (congr_arg_heq BaseChangeChart.incU' (chartQuadrupleWhole_mapSquare ch hpb))
  rw [← e]
  exact ⟨(chartQuadrupleWhole ch).incU' y, (Scheme.Hom.comp_apply _ _ y).symm⟩

/-- **A geometric point of `X'` lifts to the affine quadruple of a chart.** For an étale diagram
of schemes over a cartesian square of algebraic spaces with `a' : U' ⟶ X'` surjective, every
geometric point of `X'` is the image of a geometric point of the fibre product of the affine
quadruple of some chart of the square of schemes. -/
theorem exists_baseChangeChart_geometricPoint_lift {X Y X' Y' : AlgebraicSpaces B S hS}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (a : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ X)
    (b : (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶ Y)
    (c : (⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩ : AlgebraicSpaces B S hS) ⟶ Y')
    (a' : (⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ : AlgebraicSpaces B S hS) ⟶ X')
    (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom) (hc : IsEtale B S hS c.hom)
    (hpb : IsPullback g₀' f₀' f₀ g₀)
    (hfa : representedSpaceMap B S hS f₀ ≫ b = a ≫ f)
    (hgb : representedSpaceMap B S hS g₀ ≫ b = c ≫ g)
    (hfc : representedSpaceMap B S hS f₀' ≫ c = a' ≫ f')
    (ha' : representedSpaceMap B S hS g₀' ≫ a = a' ≫ g')
    (hs : IsSurjective B S hS a'.hom) (x' : GeometricPoint B S hS X'.1) :
    ∃ (ch : BaseChangeChart ((BigFppfOver.toScheme B S hS).map f₀)
        ((BigFppfOver.toScheme B S hS).map g₀) ((BigFppfOver.toScheme B S hS).map f₀')
        ((BigFppfOver.toScheme B S hS).map g₀'))
      (x : GeometricPoint B S hS (yoneda.obj (pullback (chartQuadrupleF ch) (chartQuadrupleG ch)))),
      geometricPointMap (representedSpaceMap B S hS (chartQuadrupleι' ch hpb) ≫ a').hom x = x' := by
  have := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  obtain ⟨u, hu⟩ := hs x'.image
  obtain ⟨ch, y, hy⟩ := exists_baseChangeChart_covering (hpb.map (BigFppfOver.toScheme B S hS))
    (pointsToScheme B S hS U' u)
  obtain ⟨w, hw⟩ := mem_range_pointsMap_yoneda_map B S hS (chartQuadrupleι' ch hpb) u
    (hy ▸ incU'_apply_mem_range_chartQuadrupleι' ch hpb y)
  have he : IsEtale B S hS (representedSpaceMap B S hS (chartQuadrupleι' ch hpb) ≫ a').hom :=
    isEtale_of_isPullback_of_etaleQuadruple B S hS sq
      (isEtale_representedSpaceMap_chartSiteObjectι_comp ch.incU a ha)
      (isEtale_representedSpaceMap_chartSiteObjectι_comp ch.incV b hb)
      (isEtale_representedSpaceMap_chartSiteObjectι_comp ch.incV' c hc)
      (isPullback_representedSpaceMap B S hS
        (IsPullback.of_hasPullback (chartQuadrupleF ch) (chartQuadrupleG ch)))
      (chartQuadruple_hfa ch f a b hfa) (chartQuadruple_hgb ch g b c hgb)
      (chartQuadruple_hfc ch hpb f' c a' hfc) (chartQuadruple_ha' ch g' hpb a a' ha')
  obtain ⟨x, -, hx⟩ := exists_geometricPoint_lift_of_isEtale B S hS
    (isAlgebraicSpace_yoneda B S hS _) X'.2 _ he x' w
    ((pointsMap_comp_apply B S hS _ _ w).trans ((congrArg _ hw).trans hu))
  exact ⟨ch, x, Subtype.ext hx⟩

end ChartPoints

section Conditions

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
  (g' : X' ⟶ X)

/-- **The chart condition of Stacks 0DJ8 on one étale diagram.** For schemes `U`, `U'` of the
site with `a : U ⟶ X`, `a' : U' ⟶ X'` over `g₀' : U' ⟶ U`, and `K`, `K'`, `φ` as in Stacks 0DKG,
the comparison of Stacks 0DJ8 (2) is invertible on every chart of the square of schemes
`U' ⟶ V'`, `U' ⟶ U`, `U ⟶ V`, `V' ⟶ V`, for the objects of `D_QCoh` of the schemes corresponding
to `La^*K`, `L(a')^*K'` under Stacks 071Q and the morphism corresponding to the one induced by
`φ` under Stacks 08GH. -/
structure DiagramChartwiseBaseChange
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hK : QcohDerived B S hS X K)
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (hK' : QcohDerived B S hS X' K')
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K')
    {U V V' U' : BigFppfOver B S hS}
    (a : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ X)
    (a' : (⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ : AlgebraicSpaces B S hS) ⟶ X')
    (f₀ : U ⟶ V) (g₀ : V' ⟶ V) (f₀' : U' ⟶ V') (g₀' : U' ⟶ U)
    (ha' : representedSpaceMap B S hS g₀' ≫ a = a' ≫ g') : Prop where
  /-- The comparison of Stacks 0DJ8 (2) is invertible on every chart. -/
  isIso : ∀ ch : BaseChangeChart ((BigFppfOver.toScheme B S hS).map f₀)
      ((BigFppfOver.toScheme B S hS).map g₀) ((BigFppfOver.toScheme B S hS).map f₀')
      ((BigFppfOver.toScheme B S hS).map g₀'),
    IsIso (ch.comparison
      ((representedDualityQuasicoherentDerivedEquivalence B S hS U).inverse.obj
        ⟨(smallEtaleDerivedModulePullback B S hS a).obj K,
          derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a K hK⟩).obj
      ((representedDualityQuasicoherentDerivedEquivalence B S hS U').inverse.obj
        ⟨(smallEtaleDerivedModulePullback B S hS a').obj K',
          derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a' K' hK'⟩).obj
      (representedQuasicoherentTransport g₀'
        ⟨(smallEtaleDerivedModulePullback B S hS a).obj K,
          derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a K hK⟩
        ⟨(smallEtaleDerivedModulePullback B S hS a').obj K',
          derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a' K' hK'⟩
        (ObjectProperty.homMk
          ((smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS g₀')
              a).hom.app K ≫
            (smallEtaleDerivedModulePullbackCongr B S hS ha').hom.app K ≫
            (smallEtaleDerivedModulePullbackCompIso B S hS a' g').inv.app K ≫
            (smallEtaleDerivedModulePullback B S hS a').map φ))).hom)

/-- **Condition (2) of Stacks 0DKG.** For every commutative diagram of schemes `U ⟶ V ⟵ V'`
étale over `X ⟶ Y ⟵ Y'` (through `a`, `b`, `c`) and `U' = V' ×_V U` with its induced morphism
`a' : U' ⟶ X'`, the equivalent conditions of Stacks 0DJ8 hold for `La^*K` and `L(a')^*K'`, in the
form of the chart condition `DiagramChartwiseBaseChange`. -/
structure EtaleDiagramChartwiseBaseChange
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hK : QcohDerived B S hS X K)
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (hK' : QcohDerived B S hS X' K')
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K') : Prop where
  /-- The chart condition holds on every étale diagram. -/
  holds : ∀ (U V V' U' : BigFppfOver B S hS)
      (a : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ X)
      (b : (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶ Y)
      (c : (⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩ : AlgebraicSpaces B S hS) ⟶ Y')
      (a' : (⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ : AlgebraicSpaces B S hS) ⟶ X')
      (f₀ : U ⟶ V) (g₀ : V' ⟶ V) (f₀' : U' ⟶ V') (g₀' : U' ⟶ U),
      IsEtale B S hS a.hom → IsEtale B S hS b.hom → IsEtale B S hS c.hom →
      IsPullback g₀' f₀' f₀ g₀ →
      representedSpaceMap B S hS f₀ ≫ b = a ≫ f →
      representedSpaceMap B S hS g₀ ≫ b = c ≫ g →
      representedSpaceMap B S hS f₀' ≫ c = a' ≫ f' →
      ∀ ha' : representedSpaceMap B S hS g₀' ≫ a = a' ≫ g',
      DiagramChartwiseBaseChange g' K hK K' hK' φ a a' f₀ g₀ f₀' g₀' ha'

/-- **Condition (3) of Stacks 0DKG.** There is a commutative diagram as in condition (2) with
`a' : U' ⟶ X'` surjective on which the chart condition `DiagramChartwiseBaseChange` holds. -/
structure SurjectiveDiagramChartwiseBaseChange
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hK : QcohDerived B S hS X K)
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (hK' : QcohDerived B S hS X' K')
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K') : Prop where
  /-- A surjective étale diagram on which the chart condition holds. -/
  exists_diagram : ∃ (U V V' U' : BigFppfOver B S hS)
      (a : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ X)
      (b : (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶ Y)
      (c : (⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩ : AlgebraicSpaces B S hS) ⟶ Y')
      (a' : (⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ : AlgebraicSpaces B S hS) ⟶ X')
      (f₀ : U ⟶ V) (g₀ : V' ⟶ V) (f₀' : U' ⟶ V') (g₀' : U' ⟶ U),
      IsEtale B S hS a.hom ∧ IsEtale B S hS b.hom ∧ IsEtale B S hS c.hom ∧
      IsPullback g₀' f₀' f₀ g₀ ∧
      representedSpaceMap B S hS f₀ ≫ b = a ≫ f ∧
      representedSpaceMap B S hS g₀ ≫ b = c ≫ g ∧
      representedSpaceMap B S hS f₀' ≫ c = a' ≫ f' ∧
      ∃ ha' : representedSpaceMap B S hS g₀' ≫ a = a' ≫ g',
        IsSurjective B S hS a'.hom ∧
          DiagramChartwiseBaseChange g' K hK K' hK' φ a a' f₀ g₀ f₀' g₀' ha'

variable {f g f' g'}

/-- **Condition (2) of Stacks 0DKG implies condition (3).** -/
theorem surjectiveDiagramChartwiseBaseChange_of_etaleDiagramChartwiseBaseChange
    (sq : IsPullback g' f' f g)
    {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    {hK : QcohDerived B S hS X K}
    {K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X'))}
    {hK' : QcohDerived B S hS X' K'}
    {φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K'}
    (h : EtaleDiagramChartwiseBaseChange f g f' g' K hK K' hK' φ) :
    SurjectiveDiagramChartwiseBaseChange f g f' g' K hK K' hK' φ := by
  obtain ⟨U, V, V', U', a, b, c, a', f₀, g₀, f₀', g₀', ha, hb, hc, hpb, hfa, hgb, hfc, ha', hs⟩ :=
    exists_etaleDiagram_isSurjective sq
  exact ⟨⟨U, V, V', U', a, b, c, a', f₀, g₀, f₀', g₀', ha, hb, hc, hpb, hfa, hgb, hfc, ha', hs,
    h.holds U V V' U' a b c a' f₀ g₀ f₀' g₀' ha hb hc hpb hfa hgb hfc ha'⟩⟩

/-- **Condition (2) of Stacks 0DJ8 on the whole chart of an affine étale quadruple** is condition
(1) of Stacks 0DKG at the geometric points of `X'` coming from `U'`: for a cartesian square of
algebraic spaces and an affine étale quadruple over it, the comparison of Stacks 0DJ8 (2) on the
whole chart of the quadruple, for the transports of `La^*K`, `L(a')^*K'` and `φ`, is invertible
exactly when the map of Equation 0DKF is invertible at every `a'(x̄)` in every degree. -/
theorem isIso_affineQuadrupleChart_comparison_iff_forall_isIso_geometricStalkBaseChangeCohomologyMap
    (sq : IsPullback g' f' f g)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hK : QcohDerived B S hS X K)
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (hK' : QcohDerived B S hS X' K')
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K')
    {U V V' U' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
    (a : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ X)
    (b : (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶ Y)
    (c : (⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩ : AlgebraicSpaces B S hS) ⟶ Y')
    (a' : (⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ : AlgebraicSpaces B S hS) ⟶ X')
    (f₀ : U ⟶ V) (g₀ : V' ⟶ V) (f₀' : U' ⟶ V') (g₀' : U' ⟶ U) (w₀ : g₀' ≫ f₀ = f₀' ≫ g₀)
    (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom) (hc : IsEtale B S hS c.hom)
    (hpb : IsPullback g₀' f₀' f₀ g₀)
    (hfa : representedSpaceMap B S hS f₀ ≫ b = a ≫ f)
    (hgb : representedSpaceMap B S hS g₀ ≫ b = c ≫ g)
    (hfc : representedSpaceMap B S hS f₀' ≫ c = a' ≫ f')
    (ha' : representedSpaceMap B S hS g₀' ≫ a = a' ≫ g') :
    IsIso ((affineQuadrupleChart f₀ g₀ f₀' g₀' hpb).comparison
      ((representedDualityQuasicoherentDerivedEquivalence B S hS U).inverse.obj
        ⟨(smallEtaleDerivedModulePullback B S hS a).obj K,
          derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a K hK⟩).obj
      ((representedDualityQuasicoherentDerivedEquivalence B S hS U').inverse.obj
        ⟨(smallEtaleDerivedModulePullback B S hS a').obj K',
          derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a' K' hK'⟩).obj
      (representedQuasicoherentTransport g₀'
        ⟨(smallEtaleDerivedModulePullback B S hS a).obj K,
          derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a K hK⟩
        ⟨(smallEtaleDerivedModulePullback B S hS a').obj K',
          derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a' K' hK'⟩
        (ObjectProperty.homMk
          ((smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS g₀')
              a).hom.app K ≫
            (smallEtaleDerivedModulePullbackCongr B S hS ha').hom.app K ≫
            (smallEtaleDerivedModulePullbackCompIso B S hS a' g').inv.app K ≫
            (smallEtaleDerivedModulePullback B S hS a').map φ))).hom) ↔
      ∀ (x : GeometricPoint B S hS (yoneda.obj U')) (n : ℤ),
        IsIso (canonicalGeometricStalkBaseChangeCohomologyMap B S hS f g f' g' sq.w
          (geometricPointMap a'.hom x) K K' φ n) := by
  have hKa := derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a K hK
  have hKa' := derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ a' K' hK'
  exact (isIso_affineQuadrupleChart_comparison_iff f₀ g₀ f₀' g₀' w₀ hpb _ hKa _ hKa' _).trans
    ((forall_isIso_geometricStalkBaseChangeCohomologyMap_iff_isIso_representedAffineSectionsBaseChangeComp
      B S hS f₀ g₀ f₀' g₀' w₀ hpb _ hKa _ hKa' _).symm.trans
      (forall_congr' fun x => forall_congr' fun n =>
        (isIso_geometricStalkBaseChangeCohomologyMap_iff_affineQuadruple sq K K' φ U V V' U' a b c
          a' f₀ g₀ f₀' g₀' w₀ ha hb hc hpb hfa hgb hfc ha' x n).symm))

end Conditions

end AlgebraicGeometry.Space

end
