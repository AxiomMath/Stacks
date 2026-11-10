module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModulePullbackSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeComp

/-!
# Étale locality of the base change map of Stacks 0DKH on both bases

The composite `Lg^*Rf_*K ⟶ Rf'_*L(g')^*K ⟶ Rf'_*K'` of Stacks 0DKH
(`AlgebraicGeometry.Space.smallEtaleDerivedBaseChangeComp`) is invertible as soon as it is
invertible for every square of affine étale charts: for an affine étale chart `W` of `Y'`, an
affine étale chart `V` of `Y` and a morphism `q : W ⟶ V` over `g`, the square formed by
`X'_W = W ×_{Y'} X'` and `X_V = V ×_Y X` over `q`, with `K` restricted to `X_V`, `K'` restricted
to `X'_W` and the restriction of `φ`.  This is the first step of the proof of Stacks 0DKH ("we may
assume `g : Y' → Y` is a morphism of affine schemes").

## Main definitions

* `AlgebraicGeometry.Space.chartBaseChangeSquareMap`: the morphism `X'_W ⟶ X_V`.

## Main results

* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedBaseChangeComp_congr`: transport of the
  composite along equalities of the two horizontal morphisms.
* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedBaseChangeComp_of_coversTop`: étale locality on
  `Y'` for any covering family of étale charts, and
  `AlgebraicGeometry.Space.isIso_smallEtaleDerivedBaseChangeComp_of_coversTop'` the same with the
  horizontal morphisms of each chart square given up to equality.
* `AlgebraicGeometry.Space.isPullback_chartBaseChangeSquareMap`:
  the square of charts is cartesian when the
  original square is.
* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedBaseChangeComp_of_affineCharts`: the reduction
  to squares of affine charts, through its chart step
  `AlgebraicGeometry.Space.isIso_smallEtaleDerivedBaseChangeComp_chart_of_affineCharts`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Congr

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (f' : X' ⟶ Y')

/-- **Transport of the composite along equalities of the horizontal morphisms.** -/
theorem isIso_smallEtaleDerivedBaseChangeComp_congr {g₁ g₂ : Y' ⟶ Y} {t₁ t₂ : X' ⟶ X}
    (hg : g₁ = g₂) (ht : t₁ = t₂) (w₁ : t₁ ≫ f = f' ≫ g₁) (w₂ : t₂ ≫ f = f' ≫ g₂)
    (K : _) (K' : _) (φ : (smallEtaleDerivedModulePullback B S hS t₂).obj K ⟶ K')
    (h : IsIso (smallEtaleDerivedBaseChangeComp B S hS f g₁ f' t₁ w₁ K K'
      ((smallEtaleDerivedModulePullbackCongr B S hS ht).hom.app K ≫ φ))) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS f g₂ f' t₂ w₂ K K' φ) := by
  subst hg ht
  simpa [smallEtaleDerivedModulePullbackCongr] using h

end Congr

section Cover

/-- The base change map along an étale chart `V` of the base is invertible. -/
private theorem isIso_smallEtaleDerivedModuleBaseChangeMap_chart {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) (K : _) :
    IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f (chartToSpace B S hS Y V)
      (chartBaseChangeProjection B S hS f V) (chartBaseChangeInclusion B S hS f V)
      (isPullback_chartBaseChangeInclusion B S hS f V).w K) :=
  isIso_smallEtaleDerivedBaseChangeMap_of_isEtale B S hS f (chartToSpace B S hS Y V)
    (chartBaseChangeProjection B S hS f V) (chartBaseChangeInclusion B S hS f V)
    (isPullback_chartBaseChangeInclusion B S hS f V) (isEtale_chartToSpace B S hS Y V)
    (relativelyRepresentable_chartToSpace B S hS Y V) K

variable {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
  {g' : X' ⟶ X}

/-- **The invertibility of the composite is étale local on `Y'`**, for any covering family of
étale charts of `Y'`. -/
theorem isIso_smallEtaleDerivedBaseChangeComp_of_coversTop (w : g' ≫ f = f' ≫ g)
    (K : _) (K' : _)
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K')
    {ι : Type*} {V : ι → SmallEtale B S hS Y'.1}
    (hV : (SmallEtale.topology B S hS Y'.1).CoversTop V)
    (h : ∀ i, IsIso (smallEtaleDerivedBaseChangeComp B S hS f (chartToSpace B S hS Y' (V i) ≫ g)
        (chartBaseChangeProjection B S hS f' (V i))
        (chartBaseChangeInclusion B S hS f' (V i) ≫ g')
        (comp_rectangle_smallEtaleDerivedBaseChange B S hS f f' _ g' _ g _ w
          (isPullback_chartBaseChangeInclusion B S hS f' (V i)).w) K
        ((smallEtaleDerivedModulePullback B S hS (chartBaseChangeInclusion B S hS f' (V i))).obj
          K')
        ((smallEtaleDerivedModulePullbackCompIso B S hS
            (chartBaseChangeInclusion B S hS f' (V i)) g').inv.app K ≫
          (smallEtaleDerivedModulePullback B S hS (chartBaseChangeInclusion B S hS f' (V i))).map
            φ))) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS f g f' g' w K K' φ) := by
  refine isIso_of_isIso_smallEtaleDerivedModulePullback_chartToSpace B S hS hV _ fun i => ?_
  have sq := isPullback_chartBaseChangeInclusion B S hS f' (V i)
  have hBC := isIso_smallEtaleDerivedModuleBaseChangeMap_chart B S hS f' (V i) K'
  have hE := smallEtaleDerivedBaseChangeComp_horizontal B S hS f f'
    (chartBaseChangeProjection B S hS f' (V i)) g' (chartBaseChangeInclusion B S hS f' (V i)) g
    (chartToSpace B S hS Y' (V i)) w sq.w K K' φ
  exact Stacks.CategoryTheory.BaseChangeComp.isIso_map_of_isIso_comp _ _ _ _
    (Iso.isIso_inv ((smallEtaleDerivedModulePullbackCompIso B S hS
      (chartToSpace B S hS Y' (V i)) g).app _)) hBC hE (h i)

/-- `isIso_smallEtaleDerivedBaseChangeComp_of_coversTop` with the horizontal morphisms of each
chart square given up to equality. -/
theorem isIso_smallEtaleDerivedBaseChangeComp_of_coversTop' (w : g' ≫ f = f' ≫ g)
    (K : _) (K' : _)
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K')
    {ι : Type*} {V : ι → SmallEtale B S hS Y'.1}
    (hV : (SmallEtale.topology B S hS Y'.1).CoversTop V)
    (h : ∀ i, ∃ (b : chartSpace B S hS Y' (V i) ⟶ Y) (_ : b = chartToSpace B S hS Y' (V i) ≫ g)
      (t : chartBaseChangeSpace B S hS f' (V i) ⟶ X)
      (ht : t = chartBaseChangeInclusion B S hS f' (V i) ≫ g')
      (w' : t ≫ f = chartBaseChangeProjection B S hS f' (V i) ≫ b),
      IsIso (smallEtaleDerivedBaseChangeComp B S hS f b
        (chartBaseChangeProjection B S hS f' (V i)) t w' K
        ((smallEtaleDerivedModulePullback B S hS (chartBaseChangeInclusion B S hS f' (V i))).obj
          K')
        ((smallEtaleDerivedModulePullbackCongr B S hS ht).hom.app K ≫
          (smallEtaleDerivedModulePullbackCompIso B S hS
            (chartBaseChangeInclusion B S hS f' (V i)) g').inv.app K ≫
          (smallEtaleDerivedModulePullback B S hS (chartBaseChangeInclusion B S hS f' (V i))).map
            φ))) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS f g f' g' w K K' φ) := by
  refine isIso_smallEtaleDerivedBaseChangeComp_of_coversTop B S hS w K K' φ hV fun i => ?_
  obtain ⟨b, hb, t, ht, w', hI⟩ := h i
  exact isIso_smallEtaleDerivedBaseChangeComp_congr B S hS _ _ hb ht w' _ K _ _ hI

end Cover

section Charts

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
  (g' : X' ⟶ X)

/-- The morphism `X'_W = W ×_{Y'} X' ⟶ X_V = V ×_Y X` attached to étale charts `W` of `Y'` and
`V` of `Y` and a morphism `q : W ⟶ V` over `g`. -/
def chartBaseChangeSquareMap (w : g' ≫ f = f' ≫ g) (W : SmallEtale B S hS Y'.1)
    (V : SmallEtale B S hS Y.1) (q : W.1.left ⟶ V.1.left)
    (hq : yoneda.map q ≫ V.1.hom = W.1.hom ≫ g.hom) :
    chartBaseChangeSpace B S hS f' W ⟶ chartBaseChangeSpace B S hS f V :=
  (isPullback_chartBaseChangeInclusion B S hS f V).lift
    (chartBaseChangeInclusion B S hS f' W ≫ g')
    (chartBaseChangeProjection B S hS f' W ≫ chartSpaceMapOver B S hS q) (by
      have h₁ := (chartSpaceMapOver_comp_chartToSpace B S hS g q hq).symm
      have h₂ := (isPullback_chartBaseChangeInclusion B S hS f' W).w
      simp only [Category.assoc, w, reassoc_of% h₂]
      exact (Category.assoc (obj := AlgebraicSpaces B S hS) _ _ _).trans
        ((congrArg (fun k => chartBaseChangeProjection B S hS f' W ≫ k) h₁).trans
          (Category.assoc (obj := AlgebraicSpaces B S hS) _ _ _).symm))

theorem chartBaseChangeSquareMap_inclusion (w : g' ≫ f = f' ≫ g) (W : SmallEtale B S hS Y'.1)
    (V : SmallEtale B S hS Y.1) (q : W.1.left ⟶ V.1.left)
    (hq : yoneda.map q ≫ V.1.hom = W.1.hom ≫ g.hom) :
    chartBaseChangeSquareMap B S hS f g f' g' w W V q hq ≫ chartBaseChangeInclusion B S hS f V =
      chartBaseChangeInclusion B S hS f' W ≫ g' :=
  (isPullback_chartBaseChangeInclusion B S hS f V).lift_fst _ _ _

theorem chartBaseChangeSquareMap_projection (w : g' ≫ f = f' ≫ g) (W : SmallEtale B S hS Y'.1)
    (V : SmallEtale B S hS Y.1) (q : W.1.left ⟶ V.1.left)
    (hq : yoneda.map q ≫ V.1.hom = W.1.hom ≫ g.hom) :
    chartBaseChangeSquareMap B S hS f g f' g' w W V q hq ≫ chartBaseChangeProjection B S hS f V =
      chartBaseChangeProjection B S hS f' W ≫ chartSpaceMapOver B S hS q :=
  (isPullback_chartBaseChangeInclusion B S hS f V).lift_snd _ _ _

/-- **The square of charts is cartesian** when the original square is: `X'_W = W ×_V X_V`. -/
theorem isPullback_chartBaseChangeSquareMap (sq : IsPullback g' f' f g) (W : SmallEtale B S hS Y'.1)
    (V : SmallEtale B S hS Y.1) (q : W.1.left ⟶ V.1.left)
    (hq : yoneda.map q ≫ V.1.hom = W.1.hom ≫ g.hom) :
    IsPullback (chartBaseChangeSquareMap B S hS f g f' g' sq.w W V q hq)
      (chartBaseChangeProjection B S hS f' W) (chartBaseChangeProjection B S hS f V)
      (chartSpaceMapOver B S hS q) := by
  have hV := isPullback_chartBaseChangeInclusion B S hS f V
  have hW := isPullback_chartBaseChangeInclusion B S hS f' W
  -- the outer rectangle `X'_W ⟶ X ⟶ Y` over `W ⟶ Y` is cartesian
  have hout : IsPullback (chartBaseChangeInclusion B S hS f' W ≫ g')
      (chartBaseChangeProjection B S hS f' W) f
      (chartToSpace B S hS Y' W ≫ g) := hW.paste_horiz sq
  have hout' : IsPullback (chartBaseChangeSquareMap B S hS f g f' g' sq.w W V q hq ≫
        chartBaseChangeInclusion B S hS f V)
      (chartBaseChangeProjection B S hS f' W) f
      (chartSpaceMapOver B S hS q ≫ chartToSpace B S hS Y V) := by
    rw [chartBaseChangeSquareMap_inclusion]
    convert hout using 1
    exact chartSpaceMapOver_comp_chartToSpace B S hS g q hq
  exact IsPullback.of_right hout'
    (chartBaseChangeSquareMap_projection B S hS f g f' g' sq.w W V q hq) hV

/-- The chart step of `isIso_smallEtaleDerivedBaseChangeComp_of_affineCharts`, at one chart of
`Y'` carrying an affine chart diagram over `g`. -/
theorem isIso_smallEtaleDerivedBaseChangeComp_chart_of_affineCharts (sq : IsPullback g' f' f g)
    (K : _) (K' : _)
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K')
    (h : ∀ (W : SmallEtale B S hS Y'.1) (V : SmallEtale B S hS Y.1) (q : W.1.left ⟶ V.1.left)
      (hq : yoneda.map q ≫ V.1.hom = W.1.hom ≫ g.hom),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W.1.left) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left) →
      IsIso (smallEtaleDerivedBaseChangeComp B S hS (chartBaseChangeProjection B S hS f V)
        (chartSpaceMapOver B S hS q) (chartBaseChangeProjection B S hS f' W)
        (chartBaseChangeSquareMap B S hS f g f' g' sq.w W V q hq)
        (isPullback_chartBaseChangeSquareMap B S hS f g f' g' sq W V q hq).w
        ((smallEtaleDerivedModulePullback B S hS (chartBaseChangeInclusion B S hS f V)).obj K)
        ((smallEtaleDerivedModulePullback B S hS (chartBaseChangeInclusion B S hS f' W)).obj K')
        ((smallEtaleDerivedModulePullbackCompIso B S hS
            (chartBaseChangeSquareMap B S hS f g f' g' sq.w W V q hq)
            (chartBaseChangeInclusion B S hS f V)).hom.app K ≫
          (smallEtaleDerivedModulePullbackCongr B S hS
            (chartBaseChangeSquareMap_inclusion B S hS f g f' g' sq.w W V q hq)).hom.app K ≫
          (smallEtaleDerivedModulePullbackCompIso B S hS
            (chartBaseChangeInclusion B S hS f' W) g').inv.app K ≫
          (smallEtaleDerivedModulePullback B S hS (chartBaseChangeInclusion B S hS f' W)).map
            φ)))
    (W : SmallEtale B S hS Y'.1) (hW : HasAffineChartDiagram B S hS g W) :
    ∃ (b : chartSpace B S hS Y' W ⟶ Y) (_ : b = chartToSpace B S hS Y' W ≫ g)
      (t : chartBaseChangeSpace B S hS f' W ⟶ X)
      (ht : t = chartBaseChangeInclusion B S hS f' W ≫ g')
      (w' : t ≫ f = chartBaseChangeProjection B S hS f' W ≫ b),
      IsIso (smallEtaleDerivedBaseChangeComp B S hS f b
        (chartBaseChangeProjection B S hS f' W) t w' K
        ((smallEtaleDerivedModulePullback B S hS (chartBaseChangeInclusion B S hS f' W)).obj K')
        ((smallEtaleDerivedModulePullbackCongr B S hS ht).hom.app K ≫
          (smallEtaleDerivedModulePullbackCompIso B S hS
            (chartBaseChangeInclusion B S hS f' W) g').inv.app K ≫
          (smallEtaleDerivedModulePullback B S hS (chartBaseChangeInclusion B S hS f' W)).map
            φ)) := by
  obtain ⟨hWaff, V, q, hq, hVaff⟩ := hW
  have sqV := isPullback_chartBaseChangeInclusion B S hS f V
  have hBC := isIso_smallEtaleDerivedModuleBaseChangeMap_chart B S hS f V K
  have hrect := isIso_smallEtaleDerivedBaseChangeComp_rectangle B S hS
    (Y'' := chartSpace B S hS Y' W) f
    (chartBaseChangeProjection B S hS f V) (chartBaseChangeProjection B S hS f' W)
    (chartBaseChangeInclusion B S hS f V) (chartBaseChangeSquareMap B S hS f g f' g' sq.w W V q hq)
    (chartToSpace B S hS Y V)
    (chartSpaceMapOver B S hS q) sqV.w
    (isPullback_chartBaseChangeSquareMap B S hS f g f' g' sq W V q hq).w K hBC
    ((smallEtaleDerivedModulePullback B S hS (chartBaseChangeInclusion B S hS f' W)).obj K')
    ((smallEtaleDerivedModulePullbackCongr B S hS
        (chartBaseChangeSquareMap_inclusion B S hS f g f' g' sq.w W V q hq)).hom.app K ≫
      (smallEtaleDerivedModulePullbackCompIso B S hS
        (chartBaseChangeInclusion B S hS f' W) g').inv.app K ≫
      (smallEtaleDerivedModulePullback B S hS (chartBaseChangeInclusion B S hS f' W)).map φ)
    (h W V q hq hWaff hVaff)
  exact ⟨_, chartSpaceMapOver_comp_chartToSpace B S hS g q hq, _,
    chartBaseChangeSquareMap_inclusion B S hS f g f' g' sq.w W V q hq, _, hrect⟩


/-- **Reduction of Stacks 0DKH to squares of affine étale charts.**  For a cartesian square, the
composite `Lg^*Rf_*K ⟶ Rf'_*K'` attached to `φ : L(g')^*K ⟶ K'` is invertible as soon as, for
every affine étale chart `W` of `Y'`, affine étale chart `V` of `Y` and `q : W ⟶ V` over `g`, the
composite for the square of charts `X'_W ⟶ X_V` over `q` is invertible at the restriction
`L(ι_V)^*K` of `K`, the restriction `L(ι_W)^*K'` of `K'` and the restriction of `φ`. -/
theorem isIso_smallEtaleDerivedBaseChangeComp_of_affineCharts (sq : IsPullback g' f' f g)
    (K : _) (K' : _)
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K')
    (h : ∀ (W : SmallEtale B S hS Y'.1) (V : SmallEtale B S hS Y.1) (q : W.1.left ⟶ V.1.left)
      (hq : yoneda.map q ≫ V.1.hom = W.1.hom ≫ g.hom),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W.1.left) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left) →
      IsIso (smallEtaleDerivedBaseChangeComp B S hS (chartBaseChangeProjection B S hS f V)
        (chartSpaceMapOver B S hS q) (chartBaseChangeProjection B S hS f' W)
        (chartBaseChangeSquareMap B S hS f g f' g' sq.w W V q hq)
        (isPullback_chartBaseChangeSquareMap B S hS f g f' g' sq W V q hq).w
        ((smallEtaleDerivedModulePullback B S hS (chartBaseChangeInclusion B S hS f V)).obj K)
        ((smallEtaleDerivedModulePullback B S hS (chartBaseChangeInclusion B S hS f' W)).obj K')
        ((smallEtaleDerivedModulePullbackCompIso B S hS
            (chartBaseChangeSquareMap B S hS f g f' g' sq.w W V q hq)
            (chartBaseChangeInclusion B S hS f V)).hom.app K ≫
          (smallEtaleDerivedModulePullbackCongr B S hS
            (chartBaseChangeSquareMap_inclusion B S hS f g f' g' sq.w W V q hq)).hom.app K ≫
          (smallEtaleDerivedModulePullbackCompIso B S hS
            (chartBaseChangeInclusion B S hS f' W) g').inv.app K ≫
          (smallEtaleDerivedModulePullback B S hS (chartBaseChangeInclusion B S hS f' W)).map
            φ))) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS f g f' g' sq.w K K' φ) := by
  exact isIso_smallEtaleDerivedBaseChangeComp_of_coversTop' B S hS sq.w K K' φ
    (V := affineChartDiagramCharts B S hS g)
    (coversTop_affineChartDiagramCharts B S hS g) fun i =>
    isIso_smallEtaleDerivedBaseChangeComp_chart_of_affineCharts B S hS f g f' g' sq K K' φ h
      (affineChartDiagramCharts B S hS g i) i.2
end Charts

end AlgebraicGeometry.Space

end
