module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOverBaseChangeAlgebraIso
public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapCompDischarge
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPushforwardAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffinePushforwardExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangeAffineChartReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangeChartIdentification

/-!
# The base change map of a cartesian square along an affine morphism is an isomorphism

Let

```
X' --i--> X
|f'       |f
Y' --g--> Y
```

be a **cartesian** square of algebraic spaces over a scheme `S` contained in a big fppf site
`B`, with `f` and `f'` affine, and let `K` be a quasi-coherent `𝒪_X`-module. Then the base change
map `g^*f_*K ⟶ f'_*(i^*K)` is an isomorphism: the base-change clause of Stacks 07U8, Stacks 02KG
for an affine morphism of algebraic spaces.

## Main definitions

* `AlgebraicGeometry.Space.modulePushforwardCounitLinear`: the chart component of a direct image
  as a linear map over the regular functions on the lower chart.

## Main results

* `AlgebraicGeometry.Space.appTop_hom_map_comp`: pullback of regular functions along a composite.
* `AlgebraicGeometry.Space.chartDiagramRestrict_chartSquare_comm`: the square of rings of
  regular functions of the chart square commutes.
* `AlgebraicGeometry.Space.bijective_moduleBaseChangeMap_val_app_of_affineChartDiagram`: **the
  base change map of a cartesian square whose two vertical morphisms are affine is bijective on
  the sections over the chart of `Y'` of every diagram of affine étale scheme charts over `g`**,
  at a quasi-coherent module.
* `AlgebraicGeometry.Space.nonempty_iso_modulePushforward_modulePullback_of_isAffineHom`:
  **the base-change isomorphism `f'_*(i^*K) ≅ g^*(f_*K)` of the base-change clause of Stacks
  07U8**, for a cartesian square whose two vertical morphisms are affine and a quasi-coherent
  `K`.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Sections

variable {X Y : AlgebraicSpaces B S hS}

/-- The chart component of a direct image, as a linear map over the ring of regular functions on
the chart of the target. -/
def modulePushforwardCounitLinear (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    letI := chartDiagramSectionModule B S hS f d F
    ((modulePushforward B S hS f).obj F).val.obj (op d.V) →ₗ[chartRing B S hS Y.1 Y.2 d.V]
      F.val.obj (op d.U) :=
  letI := chartDiagramSectionModule B S hS f d F
  { toFun := modulePushforwardCounitApp B S hS f F d
    map_add' := modulePushforwardCounitApp_add B S hS f F d
    map_smul' := modulePushforwardCounitApp_smul B S hS f F d }

/-- Pullback of regular functions along a composite of morphisms of the site. -/
theorem appTop_hom_map_comp {U V W : BigFppfOver B S hS} (a : U ⟶ V) (b : V ⟶ W) :
    ((BigFppfOver.toScheme B S hS).map (a ≫ b)).appTop.hom =
      (((BigFppfOver.toScheme B S hS).map a).appTop.hom).comp
        (((BigFppfOver.toScheme B S hS).map b).appTop.hom) := by
  rw [CategoryTheory.Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]

end Sections

variable {X X' Y Y' : AlgebraicSpaces B S hS} (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y)

/-- **The square of chart rings of the chart square commutes.** -/
theorem chartDiagramRestrict_chartSquare_comm
    (hf : yoneda.relativelyRepresentable f.hom) (hf' : yoneda.relativelyRepresentable f'.hom)
    (d : ChartDiagram B S hS Y'.1 Y.1 g.hom) (comm : i ≫ f = f' ≫ g) :
    (chartDiagramRestrict B S hS i
          (chartDiagramOfSquare B S hS i f' f g hf hf' d comm)).comp
        (chartDiagramRestrict B S hS f (smallBaseChangeDiagram f hf d.V)) =
      (chartDiagramRestrict B S hS f'
          (smallBaseChangeDiagram f' hf' d.U)).comp
        (chartDiagramRestrict B S hS g d) :=
  ((appTop_hom_map_comp B S hS (baseChangeChartSquareMap B S hS i f' f g hf hf' d comm)
        (hf.snd d.V.1.hom)).symm.trans
      (congrArg (fun k ↦ ((BigFppfOver.toScheme B S hS).map k).appTop.hom)
        (baseChangeChartSquareMap_snd B S hS i f' f g hf hf' d comm))).trans
    (appTop_hom_map_comp B S hS (hf'.snd d.U.1.hom) d.g)

/-- **The base change map of a cartesian square with an affine `f` is bijective on the sections
over the chart of `Y'` of a diagram of affine étale scheme charts over `g`.** -/
theorem bijective_moduleBaseChangeMap_val_app_of_affineChartDiagram
    (hf : yoneda.relativelyRepresentable f.hom) (hf' : yoneda.relativelyRepresentable f'.hom)
    (sq : IsPullback i f' f g) (haff : IsAffineHom B S hS f.hom)
    (haff' : IsAffineHom B S hS f'.hom) (K : Modules.{u, u} B S hS X.1 X.2)
    (hK : K.IsQuasicoherentOnSite) (d : ChartDiagram B S hS Y'.1 Y.1 g.hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS Y'.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    Function.Bijective ((((moduleBaseChangeMap f g f' i sq.w).app K).val.app (op d.U))) := by
  have hV0 : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj
      (chartDiagramOfSquare B S hS i f' f g hf hf' d sq.w).V) :=
    isAffine_smallBaseChange_obj B S hS f hf haff d.V hV
  have hW : IsAffine ((SmallEtale.toOver B S hS X'.1 ⋙ BigFppfOver.toScheme B S hS).obj
      (chartDiagramOfSquare B S hS i f' f g hf hf' d sq.w).U) :=
    isAffine_smallBaseChange_obj B S hS f' hf' haff' d.U hU
  let algRS : Algebra (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS Y'.1 Y'.2 d.U) :=
    chartDiagramAlgebra B S hS g d
  let algRA : Algebra (chartRing B S hS Y.1 Y.2 d.V)
      (chartRing B S hS X.1 X.2 (chartDiagramOfSquare B S hS i f' f g hf hf' d sq.w).V) :=
    chartDiagramAlgebra B S hS f (smallBaseChangeDiagram f hf d.V)
  let algAB : Algebra
      (chartRing B S hS X.1 X.2 (chartDiagramOfSquare B S hS i f' f g hf hf' d sq.w).V)
      (chartRing B S hS X'.1 X'.2 (chartDiagramOfSquare B S hS i f' f g hf hf' d sq.w).U) :=
    chartDiagramAlgebra B S hS i (chartDiagramOfSquare B S hS i f' f g hf hf' d sq.w)
  let algSB : Algebra (chartRing B S hS Y'.1 Y'.2 d.U)
      (chartRing B S hS X'.1 X'.2 (chartDiagramOfSquare B S hS i f' f g hf hf' d sq.w).U) :=
    chartDiagramAlgebra B S hS f' (smallBaseChangeDiagram f' hf' d.U)
  let algRB : Algebra (chartRing B S hS Y.1 Y.2 d.V)
      (chartRing B S hS X'.1 X'.2 (chartDiagramOfSquare B S hS i f' f g hf hf' d sq.w).U) :=
    ((algebraMap (chartRing B S hS Y'.1 Y'.2 d.U)
      (chartRing B S hS X'.1 X'.2 (chartDiagramOfSquare B S hS i f' f g hf hf' d sq.w).U)).comp
      (algebraMap (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS Y'.1 Y'.2 d.U))).toAlgebra
  have towerS : IsScalarTower (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS Y'.1 Y'.2 d.U)
      (chartRing B S hS X'.1 X'.2 (chartDiagramOfSquare B S hS i f' f g hf hf' d sq.w).U) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have towerA : IsScalarTower (chartRing B S hS Y.1 Y.2 d.V)
      (chartRing B S hS X.1 X.2 (chartDiagramOfSquare B S hS i f' f g hf hf' d sq.w).V)
      (chartRing B S hS X'.1 X'.2 (chartDiagramOfSquare B S hS i f' f g hf hf' d sq.w).U) :=
    IsScalarTower.of_algebraMap_eq'
      (chartDiagramRestrict_chartSquare_comm B S hS i f' f g hf hf' d sq.w).symm
  have pushout : Algebra.IsPushout (chartRing B S hS Y.1 Y.2 d.V)
      (chartRing B S hS Y'.1 Y'.2 d.U)
      (chartRing B S hS X.1 X.2 (chartDiagramOfSquare B S hS i f' f g hf hf' d sq.w).V)
      (chartRing B S hS X'.1 X'.2 (chartDiagramOfSquare B S hS i f' f g hf hf' d sq.w).U) :=
    (CommRingCat.isPushout_iff_isPushout.1
      (isPushout_appTop_chartSquare_of_isAffineHom B S hS i f' f g hf hf' d sq haff hU hV)).symm
  let modRM : Module (chartRing B S hS Y.1 Y.2 d.V)
      (K.val.obj (op (chartDiagramOfSquare B S hS i f' f g hf hf' d sq.w).V)) :=
    chartDiagramSectionModule B S hS f (smallBaseChangeDiagram f hf d.V) K
  have towerM : IsScalarTower (chartRing B S hS Y.1 Y.2 d.V)
      (chartRing B S hS X.1 X.2 (chartDiagramOfSquare B S hS i f' f g hf hf' d sq.w).V)
      (K.val.obj (op (chartDiagramOfSquare B S hS i f' f g hf hf' d sq.w).V)) :=
    chartDiagramSection_isScalarTower B S hS f (smallBaseChangeDiagram f hf d.V) K
  have hPhi : Function.Bijective
      (modulePullbackChartBaseChange B S hS g ((modulePushforward B S hS f).obj K) d) :=
    bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS g
      ((modulePushforward B S hS f).obj K)
      (isQuasicoherentOnSite_modulePushforward_isAffineHom B S hS f haff K hK) d hU hV
  have hPsi : Function.Bijective
      (modulePushforwardCounitApp B S hS f' ((modulePullback B S hS i).obj K)
        (smallBaseChangeDiagram f' hf' d.U)) :=
    bijective_modulePushforwardCounitApp_smallBaseChangeDiagram f'
      hf' ((modulePullback B S hS i).obj K) d.U
  have hTheta : Function.Bijective (modulePullbackChartBaseChange B S hS i K
      (chartDiagramOfSquare B S hS i f' f g hf hf' d sq.w)) :=
    bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS i K hK
      (chartDiagramOfSquare B S hS i f' f g hf hf' d sq.w) hW hV0
  let eC : ((((modulePushforward B S hS f).obj K)).val.obj (op d.V))
      ≃ₗ[(chartRing B S hS Y.1 Y.2 d.V)]
      (K.val.obj (op (chartDiagramOfSquare B S hS i f' f g hf hf' d sq.w).V)) :=
    LinearEquiv.ofBijective
      (modulePushforwardCounitLinear B S hS f K (smallBaseChangeDiagram f hf d.V))
      (bijective_modulePushforwardCounitApp_smallBaseChangeDiagram f hf K d.V)
  let eP := Algebra.IsPushout.cancelBaseChange (chartRing B S hS Y.1 Y.2 d.V)
    (chartRing B S hS Y'.1 Y'.2 d.U)
    (chartRing B S hS X.1 X.2 (chartDiagramOfSquare B S hS i f' f g hf hf' d sq.w).V)
    (chartRing B S hS X'.1 X'.2 (chartDiagramOfSquare B S hS i f' f g hf hf' d sq.w).U)
    (K.val.obj (op (chartDiagramOfSquare B S hS i f' f g hf hf' d sq.w).V))
  let eT := TensorProduct.congr
    (LinearEquiv.refl (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS Y'.1 Y'.2 d.U)) eC
  have key : ∀ z, modulePushforwardCounitApp B S hS f' ((modulePullback B S hS i).obj K)
        (smallBaseChangeDiagram f' hf' d.U)
        ((((moduleBaseChangeMap f g f' i sq.w).app K).val.app (op d.U))
          (modulePullbackChartBaseChange B S hS g ((modulePushforward B S hS f).obj K) d z)) =
      modulePullbackChartBaseChange B S hS i K
        (chartDiagramOfSquare B S hS i f' f g hf hf' d sq.w) (eP.symm (eT z)) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a s =>
      have e1 : modulePullbackChartBaseChange B S hS g ((modulePushforward B S hS f).obj K) d
            (TensorProduct.tmul (chartRing B S hS Y.1 Y.2 d.V) a s) =
          a • modulePullbackChartSection B S hS g ((modulePushforward B S hS f).obj K) d s :=
        modulePullbackChartBaseChange_tmul B S hS g ((modulePushforward B S hS f).obj K) d a s
      have e2 : (((moduleBaseChangeMap f g f' i sq.w).app K).val.app (op d.U))
            (a • modulePullbackChartSection B S hS g ((modulePushforward B S hS f).obj K) d s) =
          a • (((moduleBaseChangeMap f g f' i sq.w).app K).val.app (op d.U))
            (modulePullbackChartSection B S hS g ((modulePushforward B S hS f).obj K) d s) :=
        map_smul _ a _
      have e3 : modulePushforwardCounitApp B S hS f' ((modulePullback B S hS i).obj K)
            (smallBaseChangeDiagram f' hf' d.U)
            (a • (((moduleBaseChangeMap f g f' i sq.w).app K).val.app (op d.U))
              (modulePullbackChartSection B S hS g ((modulePushforward B S hS f).obj K) d s)) =
          chartDiagramPullback B S hS f' (smallBaseChangeDiagram f' hf' d.U) a •
            modulePushforwardCounitApp B S hS f' ((modulePullback B S hS i).obj K)
              (smallBaseChangeDiagram f' hf' d.U)
              ((((moduleBaseChangeMap f g f' i sq.w).app K).val.app (op d.U))
                (modulePullbackChartSection B S hS g ((modulePushforward B S hS f).obj K) d s)) :=
        modulePushforwardCounitApp_smul B S hS f' ((modulePullback B S hS i).obj K)
          (smallBaseChangeDiagram f' hf' d.U) a _
      have e4 : modulePushforwardCounitApp B S hS f' ((modulePullback B S hS i).obj K)
            (smallBaseChangeDiagram f' hf' d.U)
            ((((moduleBaseChangeMap f g f' i sq.w).app K).val.app (op d.U))
              (modulePullbackChartSection B S hS g ((modulePushforward B S hS f).obj K) d s)) =
          modulePullbackChartSection B S hS i K (chartDiagramOfSquare B S hS i f' f g hf hf' d sq.w)
            (modulePushforwardCounitApp B S hS f K (smallBaseChangeDiagram f hf d.V) s) := by
        rw [← modulePullbackUnitSection_eq_modulePullbackChartSection B S hS g
          ((modulePushforward B S hS f).obj K) d s]
        exact (counitApp_val_app_moduleBaseChangeMap_modulePullbackUnitSection B S hS i f' f g K
            hf hf' d sq.w s).trans
          (modulePullbackUnitSection_eq_modulePullbackChartSection B S hS i K
            (chartDiagramOfSquare B S hS i f' f g hf hf' d sq.w) _)
      have e5 : modulePullbackChartBaseChange B S hS i K
            (chartDiagramOfSquare B S hS i f' f g hf hf' d sq.w)
            (TensorProduct.tmul
              (chartRing B S hS X.1 X.2 (chartDiagramOfSquare B S hS i f' f g hf hf' d sq.w).V)
              (algebraMap (chartRing B S hS Y'.1 Y'.2 d.U)
                (chartRing B S hS X'.1 X'.2
                  (chartDiagramOfSquare B S hS i f' f g hf hf' d sq.w).U) a) (eC s)) =
          algebraMap (chartRing B S hS Y'.1 Y'.2 d.U)
              (chartRing B S hS X'.1 X'.2
                (chartDiagramOfSquare B S hS i f' f g hf hf' d sq.w).U) a •
            modulePullbackChartSection B S hS i K
              (chartDiagramOfSquare B S hS i f' f g hf hf' d sq.w) (eC s) :=
        modulePullbackChartBaseChange_tmul B S hS i K
          (chartDiagramOfSquare B S hS i f' f g hf hf' d sq.w) _ _
      rw [TensorProduct.congr_tmul, Algebra.IsPushout.cancelBaseChange_symm_tmul, e1, e2, e3, e4]
      exact e5.symm
    | add x y hx hy =>
      simp only [map_add]
      exact (modulePushforwardCounitApp_add B S hS f' ((modulePullback B S hS i).obj K)
        (smallBaseChangeDiagram f' hf' d.U) _ _).trans (congrArg₂ (· + ·) hx hy)
  have hG : Function.Bijective (fun z ↦ modulePushforwardCounitApp B S hS f'
      ((modulePullback B S hS i).obj K) (smallBaseChangeDiagram f' hf' d.U)
      ((((moduleBaseChangeMap f g f' i sq.w).app K).val.app (op d.U))
        (modulePullbackChartBaseChange B S hS g ((modulePushforward B S hS f).obj K) d z))) := by
    rw [funext key]
    exact hTheta.comp (eP.symm.bijective.comp eT.bijective)
  exact (Function.Bijective.of_comp_iff _ hPhi).1 ((hPsi.of_comp_iff' _).1 hG)

/-- **The base-change isomorphism of the base-change clause of Stacks 07U8, Stacks 02KG for an
affine morphism of algebraic spaces.** For a cartesian square of algebraic spaces whose two
vertical morphisms are affine and a quasi-coherent `𝒪_X`-module `K`, the direct image along `f'`
of the inverse image of `K` along `i` is the inverse image along `g` of the direct image of `K`
along `f`. -/
theorem nonempty_iso_modulePushforward_modulePullback_of_isAffineHom
    (sq : IsPullback i f' f g) (haff : IsAffineHom B S hS f.hom)
    (haff' : IsAffineHom B S hS f'.hom) (K : Modules.{u, u} B S hS X.1 X.2)
    (hK : K.IsQuasicoherentOnSite) :
    Nonempty ((modulePushforward B S hS f').obj ((modulePullback B S hS i).obj K) ≅
      (modulePullback B S hS g).obj ((modulePushforward B S hS f).obj K)) :=
  nonempty_iso_modulePushforward_modulePullback_of_bijective_affineChartDiagram B S hS f g f' i
    sq.w K fun d hU hV ↦
      bijective_moduleBaseChangeMap_val_app_of_affineChartDiagram B S hS i f' f g
        (relativelyRepresentable_hom_of_isAffineHom B S hS f haff)
        (relativelyRepresentable_hom_of_isAffineHom B S hS f' haff') sq haff haff' K hK d hU hV

end AlgebraicGeometry.Space

end
