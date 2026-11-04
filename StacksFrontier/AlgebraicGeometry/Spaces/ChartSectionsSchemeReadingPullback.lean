module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsSchemeReading
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiPullbackSection

/-!
# The chart sections of the reading and pullback of sections

`AlgebraicGeometry.Space.chartSectionsReadingEquiv` identifies the sections of a module over an
étale chart with the global sections of its reading on the scheme of the chart.  This file proves
that the identification is compatible with pullback: along a chart diagram over `f : X ⟶ Y`, the
chart section of `f^*N` attached to a section of `N` is, read on the scheme of the chart of `X`,
the comparison of readings `AlgebraicGeometry.Space.schemeReadingPullbackIso` applied to the
pullback, along the morphism of chart schemes, of the reading of that section.

## Main results

* `AlgebraicGeometry.Space.chartReadingSection_comp`: the chart section of the reading along a
  composite point is the comparison of readings applied to the pulled-back chart section, for any
  represented points.
* `AlgebraicGeometry.Space.chartSectionsReadingEquiv_modulePullbackChartSection`: the same at a
  chart diagram, for `θ`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section ChartDiagramMoves

attribute [-instance] CategoryTheory.catToReflQuiver

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- A chart diagram restricted along a morphism of charts of the source. -/
def ChartDiagram.precompU (d : ChartDiagram B S hS X.1 Y.1 f.hom) {U' : SmallEtale B S hS X.1}
    (i : U' ⟶ d.U) : ChartDiagram B S hS X.1 Y.1 f.hom where
  U := U'
  V := d.V
  g := (SmallEtale.toOver B S hS X.1).map i ≫ d.g
  comm := by
    rw [CategoryTheory.Functor.map_comp, Category.assoc, ← d.comm, ← Category.assoc]
    exact congrArg (· ≫ f.hom) (CostructuredArrow.w i.hom).symm

/-- The chart section at a restricted chart diagram is the restriction of the chart section. -/
theorem modulePullbackChartSection_precompU (M : Modules.{u, u} B S hS Y.1 Y.2)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) {U' : SmallEtale B S hS X.1} (i : U' ⟶ d.U)
    (s : M.val.obj (op d.V)) :
    modulePullbackChartSection B S hS f M (d.precompU f i) s =
      ((modulePullback B S hS f).obj M).val.map i.op (modulePullbackChartSection B S hS f M d s) :=
  (congrArg (modulePullbackChartSection B S hS f M (d.precompU f i))
      (chartReading_presheaf_map_id_apply M.val _ s).symm).trans
    (modulePullbackChartSection_naturality B S hS f M d (d.precompU f i) i (𝟙 _)
      ((Category.comp_id _).symm.trans
        (congrArg (_ ≫ ·) ((SmallEtale.toOver B S hS Y.1).map_id _).symm)) s)

/-- Chart sections at chart diagrams with equal vertical morphisms agree. -/
theorem modulePullbackChartSection_mk_congr_vertical (M : Modules.{u, u} B S hS Y.1 Y.2)
    {U : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1}
    {g₁ g₂ : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V}
    (h₁ : U.1.hom ≫ f.hom = yoneda.map g₁ ≫ V.1.hom)
    (h₂ : U.1.hom ≫ f.hom = yoneda.map g₂ ≫ V.1.hom) (e : g₁ = g₂) (s : M.val.obj (op V)) :
    modulePullbackChartSection B S hS f M ⟨U, V, g₁, h₁⟩ s =
      modulePullbackChartSection B S hS f M ⟨U, V, g₂, h₂⟩ s := by
  subst e
  rfl

variable {Z : AlgebraicSpaces B S hS} (g : Y ⟶ Z)

/-- **The comparison of iterated inverse images carries a chart section of a chart section to
the chart section of the composite.** -/
theorem modulePullbackCompIso_hom_modulePullbackChartSection
    {U : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1} {W : SmallEtale B S hS Z.1}
    (a : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (b : (SmallEtale.toOver B S hS Y.1).obj V ⟶ (SmallEtale.toOver B S hS Z.1).obj W)
    (ha : U.1.hom ≫ f.hom = yoneda.map a ≫ V.1.hom)
    (hb : V.1.hom ≫ g.hom = yoneda.map b ≫ W.1.hom)
    (M : Modules.{u, u} B S hS Z.1 Z.2) (s : M.val.obj (op W)) :
    ((modulePullbackCompIso B S hS f g).hom.app M).val.app (op U)
        (modulePullbackChartSection B S hS f ((modulePullback B S hS g).obj M) ⟨U, V, a, ha⟩
          (modulePullbackChartSection B S hS g M ⟨V, W, b, hb⟩ s)) =
      modulePullbackChartSection B S hS (f ≫ g) M (ChartDiagram.comp B S hS f g a b ha hb) s := by
  refine Eq.trans ?_ ((modulePullbackCompIso_hom_val_app_modulePullbackUnitSection B S hS f g a b
    ha hb M s).trans (modulePullbackUnitSection_eq_modulePullbackChartSection B S hS (f ≫ g) M
      (ChartDiagram.comp B S hS f g a b ha hb) s))
  refine congrArg (fun z => ((modulePullbackCompIso B S hS f g).hom.app M).val.app (op U) z) ?_
  exact (congrArg (modulePullbackChartSection B S hS f ((modulePullback B S hS g).obj M)
      ⟨U, V, a, ha⟩) (modulePullbackUnitSection_eq_modulePullbackChartSection B S hS g M
        ⟨V, W, b, hb⟩ s).symm).trans
    (modulePullbackUnitSection_eq_modulePullbackChartSection B S hS f
      ((modulePullback B S hS g).obj M) ⟨U, V, a, ha⟩ _).symm

end ChartDiagramMoves

section Pullback

attribute [-instance] CategoryTheory.catToReflQuiver

variable {Y : AlgebraicSpaces B S hS}

/-- The vertical morphism of the restricted base-changed diagram, followed by the top chart of `T`,
is the top chart of `T'` followed by `g`. -/
theorem representedTopBaseChangeChartHom_comp_eq {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (K : topRepChart T' ⟶ (smallBaseChange B S hS (representedSpaceMap B S hS g)
      (relativelyRepresentable_yoneda_map B S hS g)).obj (topRepChart T)) :
    (SmallEtale.toOver B S hS (yoneda.obj T')).map K ≫
        (relativelyRepresentable_yoneda_map B S hS g).snd (topRepChart T).1.hom ≫
          readingTopChartMap T =
      readingTopChartMap T' ≫ g := by
  apply yoneda.map_injective
  have h1 := (relativelyRepresentable_yoneda_map B S hS g).w (topRepChart T).1.hom
  have h2 := CostructuredArrow.w K.hom
  refine (yoneda.map_comp _ _).trans ?_
  refine (congrArg (yoneda.map ((SmallEtale.toOver B S hS (yoneda.obj T')).map K) ≫ ·)
    ((yoneda.map_comp _ _).trans (congrArg (_ ≫ ·) (yoneda.map_preimage _)))).trans ?_
  refine (congrArg (yoneda.map ((SmallEtale.toOver B S hS (yoneda.obj T')).map K) ≫ ·)
    h1.symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ yoneda.map g) h2).trans ?_
  exact (congrArg (· ≫ yoneda.map g) (yoneda.map_preimage _).symm).trans (yoneda.map_comp _ _).symm

/-- The comparison of readings, on global sections: the comparison of Stacks 03LU at the top
chart after the comparison `r^*(F|_{T_Zar}) ≅ (φ^*F)|_{T'_Zar}`. -/
theorem schemeReadingPullbackIso_hom_app_top (N : Modules.{u, u} B S hS Y.1 Y.2)
    (hN : N.IsQuasicoherentOnSite) {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (ψ : representedAlgebraicSpace B S hS T ⟶ Y)
    (z : Γ((Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)).obj
        (schemeReading N ψ), ⊤)) :
    (schemeReadingPullbackIso N hN g (ψ := ψ) rfl).hom.app ⊤ z =
      (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS g) ψ
          (representedSpaceMap B S hS g ≫ ψ) rfl N).inv.val.app (op (topRepChart T'))
        ((representedZariskiModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g)
          ((modulePullback B S hS ψ).obj N)
          (isQuasicoherentOnSite_modulePullback_schemeReading N hN ψ)).hom.app ⊤ z) := by
  rw [schemeReadingPullbackIso_eq, Iso.trans_hom, Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply]
  exact readingTopSectionsAddEquiv_map T' _ _

/-- **The chart section of the reading along a composite point is the comparison of readings
applied to the pulled-back chart section.** -/
theorem chartReadingSection_comp (N : Modules.{u, u} B S hS Y.1 Y.2)
    (hN : N.IsQuasicoherentOnSite) (V : SmallEtale B S hS Y.1) {T' T : BigFppfOver B S hS}
    (g : T' ⟶ T) (v : T ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    {ψ : representedAlgebraicSpace B S hS T ⟶ Y} (hψ : ψ.hom = yoneda.map v ≫ V.1.hom)
    {ψ' : representedAlgebraicSpace B S hS T' ⟶ Y} (w : representedSpaceMap B S hS g ≫ ψ = ψ')
    (hψ' : ψ'.hom = yoneda.map (g ≫ v) ≫ V.1.hom) (x : N.val.obj (op V)) :
    chartReadingSection N V (g ≫ v) hψ' x =
      (schemeReadingPullbackIso N hN g w).hom.app ⊤
        (pullbackSectionHom
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)
          (schemeReading N ψ) ⊤ ⊤ le_top (chartReadingSection N V v hψ x)) := by
  subst w
  refine Eq.trans ?_ (schemeReadingPullbackIso_hom_app_top N hN g ψ _).symm
  refine Eq.trans ?_ (congrArg ((QuasiCoherentDescent.pullbackComparison B S hS
      (representedSpaceMap B S hS g) ψ (representedSpaceMap B S hS g ≫ ψ) rfl N).inv.val.app
        (op (topRepChart T')))
    ((modulePullbackChartSection_precompU (representedSpaceMap B S hS g)
      ((modulePullback B S hS ψ).obj N)
      (chartDiagramOfSmallBaseChange (representedSpaceMap B S hS g)
        (relativelyRepresentable_yoneda_map B S hS g) (topRepChart T))
      (representedTopBaseChangeChartHom g (relativelyRepresentable_yoneda_map B S hS g))
      (chartReadingSection N V v hψ x)).trans
    (representedZariskiModulePullbackIso_hom_pullbackSection_eq_restrict g
      (relativelyRepresentable_yoneda_map B S hS g) ((modulePullback B S hS ψ).obj N)
      (isQuasicoherentOnSite_modulePullback_schemeReading N hN ψ)
      (chartReadingSection N V v hψ x)).symm))
  refine Eq.trans ?_ (modulePullbackCompIso_hom_modulePullbackChartSection
    (representedSpaceMap B S hS g) ψ _ (readingTopChartMap T ≫ v) _
    (readingChartDiagram_comm V v hψ) N x).symm
  exact modulePullbackChartSection_mk_congr_vertical (representedSpaceMap B S hS g ≫ ψ) N _ _
    ((congrArg (· ≫ v) (representedTopBaseChangeChartHom_comp_eq g
      (representedTopBaseChangeChartHom g
        (relativelyRepresentable_yoneda_map B S hS g))).symm).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans
        (Category.assoc _ _ _).symm))) x

/-- The identification of the reading of an inverse image with the reading along the composite,
on global sections. -/
theorem schemeReadingModulePullbackIso_hom_app_top {X : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (N : Modules.{u, u} B S hS Y.1 Y.2) {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ X)
    (z : Γ(schemeReading ((modulePullback B S hS f).obj N) ψ, ⊤)) :
    (schemeReadingModulePullbackIso f N ψ).hom.app ⊤ z =
      (QuasiCoherentDescent.pullbackComparison B S hS ψ f (ψ ≫ f) rfl N).inv.val.app
        (op (readingTopChart T)) z :=
  readingTopSectionsAddEquiv_map T _ _

/-- The inverse of an isomorphism of modules on a scheme undoes it on sections. -/
theorem scheme_modules_iso_inv_hom_app {Z : Scheme.{u}} {M M' : Z.Modules} (e : M ≅ M')
    (U : Z.Opens) (z : Γ(M, U)) : e.inv.app U (e.hom.app U z) = z :=
  congrArg (fun m : M ⟶ M => m.app U z) e.hom_inv_id

/-- The comparison of iterated inverse images on the chart section of the reading. -/
theorem pullbackComparison_inv_chartReadingSection {X : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (N : Modules.{u, u} B S hS Y.1 Y.2) (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    {T : BigFppfOver B S hS} (v : T ⟶ (SmallEtale.toOver B S hS X.1).obj d.U)
    {ψ : representedAlgebraicSpace B S hS T ⟶ X} (hψ : ψ.hom = yoneda.map v ≫ d.U.1.hom)
    (x : N.val.obj (op d.V)) :
    (QuasiCoherentDescent.pullbackComparison B S hS ψ f (ψ ≫ f) rfl N).inv.val.app
        (op (readingTopChart T))
        (chartReadingSection ((modulePullback B S hS f).obj N) d.U v hψ
          (modulePullbackChartSection B S hS f N d x)) =
      modulePullbackChartSection B S hS (ψ ≫ f) N
        (ChartDiagram.comp B S hS ψ f (readingTopChartMap T ≫ v) d.g
          (readingChartDiagram_comm d.U v hψ) d.comm) x :=
  modulePullbackCompIso_hom_modulePullbackChartSection ψ f _ d.g
    (readingChartDiagram_comm d.U v hψ) d.comm N x

/-- θ on a chart section of an inverse image, read along the composite. -/
theorem schemeReadingModulePullbackIso_hom_chartSectionsReadingEquiv {X : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (N : Modules.{u, u} B S hS Y.1 Y.2) (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (x : N.val.obj (op d.V)) :
    (schemeReadingModulePullbackIso f N (chartToSpace B S hS X d.U)).hom.app ⊤
        (chartSectionsReadingEquiv ((modulePullback B S hS f).obj N) d.U
          (modulePullbackChartSection B S hS f N d x)) =
      modulePullbackChartSection B S hS (chartToSpace B S hS X d.U ≫ f) N
        (ChartDiagram.comp B S hS (chartToSpace B S hS X d.U) f
          (readingTopChartMap (chartFppfObject B S hS X d.U) ≫ 𝟙 _) d.g
          (readingChartDiagram_comm d.U (𝟙 _) (chartToSpace_hom_eq d.U)) d.comm) x := by
  rw [chartSectionsReadingEquiv_apply]
  exact (schemeReadingModulePullbackIso_hom_app_top f N (chartToSpace B S hS X d.U) _).trans
    (pullbackComparison_inv_chartReadingSection f N d (𝟙 _) (chartToSpace_hom_eq d.U) x)

/-- **θ carries the chart section of an inverse image to the comparison of readings applied to the
pulled-back θ.**  For a chart diagram `d` over `f : X ⟶ Y`, with `g = d.g`, the section of
`f^*N` over `d.U` attached to `x ∈ N(d.V)`, read on the scheme of `d.U`, is the comparison
`g^* N_{d.V} ≅ N_{d.U}` of readings applied to the pullback along `g` of the reading of `x`, read
back through the identification of the reading of `f^*N` with the reading of `N` along the
composite. -/
theorem chartSectionsReadingEquiv_modulePullbackChartSection {X : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (N : Modules.{u, u} B S hS Y.1 Y.2) (hN : N.IsQuasicoherentOnSite)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (w : representedSpaceMap B S hS d.g ≫ chartToSpace B S hS Y d.V =
      chartToSpace B S hS X d.U ≫ f)
    (x : N.val.obj (op d.V)) :
    chartSectionsReadingEquiv ((modulePullback B S hS f).obj N) d.U
        (modulePullbackChartSection B S hS f N d x) =
      (schemeReadingModulePullbackIso f N (chartToSpace B S hS X d.U)).inv.app ⊤
        ((schemeReadingPullbackIso N hN d.g w).hom.app ⊤
          (pullbackSectionHom
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) d.g.left)
            (schemeReading N (chartToSpace B S hS Y d.V)) ⊤ ⊤ le_top
            (chartSectionsReadingEquiv N d.V x))) := by
  have hψ' : (chartToSpace B S hS X d.U ≫ f).hom = yoneda.map (d.g ≫ 𝟙 _) ≫ d.V.1.hom := by
    rw [Category.comp_id]
    exact d.comm
  rw [chartSectionsReadingEquiv_apply N d.V x,
    ← chartReadingSection_comp N hN d.V d.g (𝟙 _) (chartToSpace_hom_eq d.V) w hψ' x]
  refine (scheme_modules_iso_inv_hom_app
    (schemeReadingModulePullbackIso f N (chartToSpace B S hS X d.U)) ⊤ _).symm.trans ?_
  refine congrArg (fun z => (schemeReadingModulePullbackIso f N
    (chartToSpace B S hS X d.U)).inv.app ⊤ z) ?_
  refine (schemeReadingModulePullbackIso_hom_chartSectionsReadingEquiv f N d x).trans ?_
  exact modulePullbackChartSection_mk_congr_vertical (chartToSpace B S hS X d.U ≫ f) N _ _
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
      ((Category.id_comp _).trans (Category.comp_id _).symm))) x

end Pullback

end AlgebraicGeometry.Space

end
