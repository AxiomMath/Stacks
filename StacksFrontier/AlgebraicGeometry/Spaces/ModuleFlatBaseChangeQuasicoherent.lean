module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramIsoDetection
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapCompDischarge
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangeMapChartFormula
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFlatBaseChangeCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFlatBaseChangeEqualizer
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeTheoreticSupportFlatPullback
public import StacksFrontier.RingTheory.Flat.EqualizerBaseChange

/-!
# Flat base change for the direct image of a quasi-coherent module, in degree zero

Let

```
X' --g'--> X
|f'         |f
v           v
Y' --g-->  Y
```

be a cartesian square of algebraic spaces over a scheme `S` of a big fppf site `B`, with `g`
flat and `f` quasi-compact and quasi-separated.  For every quasi-coherent `𝒪_X`-module `F` the
base change map `g^*f_*F ⟶ f'_*(g')^*F` of `AlgebraicGeometry.Space.moduleBaseChangeMap` is an
isomorphism.  This is the degree-zero clause of Stacks 073K, part (1).

## Main results

* `AlgebraicGeometry.Space.isIso_moduleBaseChangeMap_app_of_isFlat`: the statement above.
* `AlgebraicGeometry.Space.flatBaseChangeZero`: the same, in the shape
  `AlgebraicGeometry.Space.FlatBaseChangeZero`.

## Proof

Invertibility is checked on the sections over the source charts `U'` of the affine chart
diagrams `U' ⟶ V` over `g` (`AlgebraicGeometry.Space.isIso_of_bijective_affineChartDiagram`).
There `(g^*f_*F)(U') = 𝒪(U') ⊗_{𝒪(V)} (f_*F)(V)`, `f_*F` being quasi-coherent by Stacks 03M9.
The space `V ×_Y X` is quasi-compact and quasi-separated over the affine `V`, so it has an
affine étale chart `W` with relation covered by an affine chart `R'`; the sections of `f_*F`
over `V` are then the equalizer of `F(W) ⇉ F(R')`
(`AlgebraicGeometry.Space.exists_modulePushforwardCounitApp_eq`).  Base changing `W` and `R'`
along `U' ⟶ V` gives affine charts of `X'` whose rings are `𝒪(U') ⊗_{𝒪(V)} 𝒪(W)` and
`𝒪(U') ⊗_{𝒪(V)} 𝒪(R')`, over which the sections of `(g')^*F` are the base changes of `F(W)`
and `F(R')`.  The chart formula of the base change map
(`AlgebraicGeometry.Space.modulePushforwardCounitApp_moduleBaseChangeMap_unitSection`) and
flatness of `𝒪(V) ⟶ 𝒪(U')` finish the computation
(`LinearMap.bijective_liftBaseChange_of_equalizer`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Main

variable {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
  {g' : X' ⟶ X}


/-- Pulling back regular functions along two morphisms in turn only depends on their composite. -/
private theorem chartDiagramPullback_comp_apply_of_eq {U V W : BigFppfOver B S hS} (φ : U ⟶ V)
    (ψ : V ⟶ W) (χ : U ⟶ W) (h : φ ≫ ψ = χ)
    (r : (Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj W)))) :
    ((forget₂ CommRingCat.{u} RingCat.{u}).map
          (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map φ).op))
        (((forget₂ CommRingCat.{u} RingCat.{u}).map
          (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map ψ).op)) r) =
      ((forget₂ CommRingCat.{u} RingCat.{u}).map
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map χ).op)) r :=
  (chartDiagramPullback_comp_apply B S hS φ ψ r).trans (congrArg (fun m =>
    ((forget₂ CommRingCat.{u} RingCat.{u}).map
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map m).op)) r) h)

/-- The ring maps of the cube `W ×_V U'` commute. -/
theorem chartDiagramRestrict_chartBaseChangeAlong (sq : IsPullback g' f' f g)
    (d : ChartDiagram B S hS Y'.1 Y.1 g.hom) {W : SmallEtale B S hS X.1}
    (b : (SmallEtale.toOver B S hS X.1).obj W ⟶ (SmallEtale.toOver B S hS Y.1).obj d.V)
    (hb : W.1.hom ≫ f.hom = yoneda.map b ≫ d.V.1.hom) (x : chartRing B S hS Y.1 Y.2 d.V) :
    chartDiagramRestrict B S hS g'
        ⟨chartBaseChangeAlong sq d.g d.comm b hb, W, pullback.fst b d.g,
          chartBaseChangeAlong_fst sq d.g d.comm b hb⟩
        (chartDiagramRestrict B S hS f ⟨W, d.V, b, hb⟩ x) =
      chartDiagramRestrict B S hS f' (chartBaseChangeAlongDiagram sq d.g d.comm b hb)
        (chartDiagramRestrict B S hS g d x) :=
  (chartDiagramPullback_comp_apply_of_eq _ _ _ pullback.condition x).trans
    (chartDiagramPullback_comp_apply B S hS (pullback.snd b d.g) d.g x).symm

/-- **The comparison of the sections of `(g')^*F` over `W ×_V U'` with the base change of the
sections of `F` over `W` along `𝒪(V) ⟶ 𝒪(U')`** is bijective for affine charts and
quasi-coherent `F`. -/
theorem exists_bijective_liftBaseChange_unitSection (sq : IsPullback g' f' f g)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (d : ChartDiagram B S hS Y'.1 Y.1 g.hom)
    (hU : IsAffine (chartScheme d.U)) (hV : IsAffine (chartScheme d.V)) {W : SmallEtale B S hS X.1}
    (b : (SmallEtale.toOver B S hS X.1).obj W ⟶ (SmallEtale.toOver B S hS Y.1).obj d.V)
    (hb : W.1.hom ≫ f.hom = yoneda.map b ≫ d.V.1.hom) (hW : IsAffine (chartScheme W)) :
    letI := chartDiagramAlgebra B S hS g d
    letI : Module (chartRing B S hS Y.1 Y.2 d.V) (F.val.obj (op W)) :=
      Module.compHom _ (chartDiagramRestrict B S hS f ⟨W, d.V, b, hb⟩)
    letI : Module (chartRing B S hS Y'.1 Y'.2 d.U)
        (((modulePullback B S hS g').obj F).val.obj
          (op (chartBaseChangeAlong sq d.g d.comm b hb))) :=
      Module.compHom _ (chartDiagramRestrict B S hS f'
        (chartBaseChangeAlongDiagram sq d.g d.comm b hb))
    ∃ θ : TensorProduct (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS Y'.1 Y'.2 d.U)
        (F.val.obj (op W)) →ₗ[chartRing B S hS Y'.1 Y'.2 d.U]
        ((modulePullback B S hS g').obj F).val.obj
          (op (chartBaseChangeAlong sq d.g d.comm b hb)),
      Function.Bijective θ ∧ ∀ (r : chartRing B S hS Y'.1 Y'.2 d.U) (p : F.val.obj (op W)),
        θ (TensorProduct.tmul _ r p) = r • modulePullbackUnitSection B S hS g' F
          ⟨chartBaseChangeAlong sq d.g d.comm b hb, W, pullback.fst b d.g,
            chartBaseChangeAlong_fst sq d.g d.comm b hb⟩ p := by
  let iRS := chartDiagramAlgebra B S hS g d
  let mRM : Module (chartRing B S hS Y.1 Y.2 d.V) (F.val.obj (op W)) :=
    Module.compHom _ (chartDiagramRestrict B S hS f ⟨W, d.V, b, hb⟩)
  let mSM' : Module (chartRing B S hS Y'.1 Y'.2 d.U)
      (((modulePullback B S hS g').obj F).val.obj
        (op (chartBaseChangeAlong sq d.g d.comm b hb))) :=
    Module.compHom _ (chartDiagramRestrict B S hS f'
      (chartBaseChangeAlongDiagram sq d.g d.comm b hb))
  let κ : ChartDiagram B S hS X'.1 X.1 g'.hom :=
    ⟨chartBaseChangeAlong sq d.g d.comm b hb, W, pullback.fst b d.g,
      chartBaseChangeAlong_fst sq d.g d.comm b hb⟩
  let e : ChartDiagram B S hS X.1 Y.1 f.hom := ⟨W, d.V, b, hb⟩
  let e' := chartBaseChangeAlongDiagram sq d.g d.comm b hb
  have hT : IsAffine (chartScheme κ.U) := isAffine_chartBaseChangeAlong sq d.g d.comm b hb hW hU hV
  let iRA : Algebra (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS X.1 X.2 W) :=
    chartDiagramAlgebra B S hS f e
  let iAB : Algebra (chartRing B S hS X.1 X.2 W) (chartRing B S hS X'.1 X'.2 κ.U) :=
    chartDiagramAlgebra B S hS g' κ
  let iSB : Algebra (chartRing B S hS Y'.1 Y'.2 d.U) (chartRing B S hS X'.1 X'.2 κ.U) :=
    chartDiagramAlgebra B S hS f' e'
  let iRB : Algebra (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS X'.1 X'.2 κ.U) :=
    ((algebraMap (chartRing B S hS X.1 X.2 W) (chartRing B S hS X'.1 X'.2 κ.U)).comp
      (algebraMap (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS X.1 X.2 W))).toAlgebra
  have : IsScalarTower (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS X.1 X.2 W)
      (chartRing B S hS X'.1 X'.2 κ.U) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS Y'.1 Y'.2 d.U)
      (chartRing B S hS X'.1 X'.2 κ.U) :=
    IsScalarTower.of_algebraMap_eq (fun x => chartDiagramRestrict_chartBaseChangeAlong sq d b hb x)
  have : Algebra.IsPushout (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS Y'.1 Y'.2 d.U)
      (chartRing B S hS X.1 X.2 W) (chartRing B S hS X'.1 X'.2 κ.U) := by
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj W)) :=
      hW
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS Y'.1).obj d.U)) := hU
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS Y.1).obj d.V)) := hV
    have hpo := isPushout_appTop_of_isPullback (isPullback_chartScheme_chartBaseChangeAlong d.g b)
    exact Algebra.IsPushout.symm (CommRingCat.isPushout_iff_isPushout.1 hpo)
  let mAM' : Module (chartRing B S hS X.1 X.2 W)
      (((modulePullback B S hS g').obj F).val.obj (op κ.U)) :=
    modulePullbackChartSectionModule B S hS g' F κ
  have : IsScalarTower (chartRing B S hS X.1 X.2 W) (chartRing B S hS X'.1 X'.2 κ.U)
      (((modulePullback B S hS g').obj F).val.obj (op κ.U)) :=
    modulePullbackChart_isScalarTower B S hS g' F κ
  have : IsScalarTower (chartRing B S hS Y'.1 Y'.2 d.U) (chartRing B S hS X'.1 X'.2 κ.U)
      (((modulePullback B S hS g').obj F).val.obj (op κ.U)) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let mRM' : Module (chartRing B S hS Y.1 Y.2 d.V)
      (((modulePullback B S hS g').obj F).val.obj (op κ.U)) :=
    Module.compHom _ (algebraMap (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS X'.1 X'.2 κ.U))
  have : IsScalarTower (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS X.1 X.2 W)
      (((modulePullback B S hS g').obj F).val.obj (op κ.U)) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have : IsScalarTower (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS Y'.1 Y'.2 d.U)
      (((modulePullback B S hS g').obj F).val.obj (op κ.U)) :=
    IsScalarTower.of_algebraMap_smul (fun x m => by
      change (chartDiagramRestrict B S hS f' e' (chartDiagramRestrict B S hS g d x)) • m =
        (chartDiagramRestrict B S hS g' κ (chartDiagramRestrict B S hS f e x)) • m
      rw [chartDiagramRestrict_chartBaseChangeAlong sq d b hb x])
  have : IsScalarTower (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS X.1 X.2 W)
      (F.val.obj (op W)) := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have hu := bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS g' F hF κ
    hT hW
  refine ⟨((modulePullbackChartSectionLinear B S hS g' F κ).restrictScalars
      (chartRing B S hS Y.1 Y.2 d.V)).liftBaseChange (chartRing B S hS Y'.1 Y'.2 d.U),
    LinearMap.bijective_liftBaseChange_restrictScalars_of_isPushout _ hu, fun r p => ?_⟩
  rw [LinearMap.liftBaseChange_tmul]
  exact congrArg (r • ·)
    (modulePullbackUnitSection_eq_modulePullbackChartSection B S hS g' F κ p).symm

/-- The unit sections of `(g')^* ⊣ g'_*` are compatible with restriction of both charts. -/
theorem modulePullbackUnitSection_naturality (g' : X' ⟶ X) (F : Modules.{u, u} B S hS X.1 X.2)
    (κ κR : ChartDiagram B S hS X'.1 X.1 g'.hom) (m : κR.U ⟶ κ.U) (j : κR.V ⟶ κ.V)
    (hm : (SmallEtale.toOver B S hS X'.1).map m ≫ κ.g = κR.g ≫ (SmallEtale.toOver B S hS X.1).map j)
    (p : F.val.obj (op κ.V)) :
    modulePullbackUnitSection B S hS g' F κR (F.val.map j.op p) =
      ((modulePullback B S hS g').obj F).val.map m.op (modulePullbackUnitSection B S hS g' F κ p) :=
  (modulePushforwardHomFMap_unit_app g' F κR (F.val.map j.op p)).symm.trans
    (((modulePushforwardHomFMap B S hS g' ((modulePullback B S hS g').obj F) F
      ((modulePullbackAdjunction B S hS g').unit.app F)).naturality κ κR m j hm p).trans
      (congrArg (fun y => ((modulePullback B S hS g').obj F).val.map m.op y)
        (modulePushforwardHomFMap_unit_app g' F κ p)))

/-- The chart formula of the base change map at the base-changed chart `W ×_V U'`. -/
theorem modulePushforwardCounitApp_moduleBaseChangeMap_chartSection (sq : IsPullback g' f' f g)
    (F : Modules.{u, u} B S hS X.1 X.2) (d : ChartDiagram B S hS Y'.1 Y.1 g.hom)
    {W : SmallEtale B S hS X.1}
    (b : (SmallEtale.toOver B S hS X.1).obj W ⟶ (SmallEtale.toOver B S hS Y.1).obj d.V)
    (hb : W.1.hom ≫ f.hom = yoneda.map b ≫ d.V.1.hom)
    (n : ((modulePushforward B S hS f).obj F).val.obj (op d.V)) :
    modulePushforwardCounitApp B S hS f' ((modulePullback B S hS g').obj F)
        (chartBaseChangeAlongDiagram sq d.g d.comm b hb)
        ((((moduleBaseChangeMap f g f' g' sq.w).app F).val.app (op d.U)).hom
          (modulePullbackChartSection B S hS g ((modulePushforward B S hS f).obj F) d n)) =
      modulePullbackUnitSection B S hS g' F
        ⟨chartBaseChangeAlong sq d.g d.comm b hb, W, pullback.fst b d.g,
          chartBaseChangeAlong_fst sq d.g d.comm b hb⟩
        (modulePushforwardCounitApp B S hS f F ⟨W, d.V, b, hb⟩ n) := by
  refine (congrArg (fun y => modulePushforwardCounitApp B S hS f'
    ((modulePullback B S hS g').obj F) (chartBaseChangeAlongDiagram sq d.g d.comm b hb)
      ((((moduleBaseChangeMap f g f' g' sq.w).app F).val.app (op d.U)).hom y))
    (modulePullbackUnitSection_eq_modulePullbackChartSection B S hS g
      ((modulePushforward B S hS f).obj F) d n).symm).trans ?_
  exact modulePushforwardCounitApp_moduleBaseChangeMap_unitSection sq.w F
    (T := chartBaseChangeAlong sq d.g d.comm b hb) (W := W) (U' := d.U) (V := d.V)
    (pullback.fst b d.g) b (pullback.snd b d.g) d.g (chartBaseChangeAlong_fst sq d.g d.comm b hb)
    hb (chartBaseChangeAlong_snd sq d.g d.comm b hb) d.comm pullback.condition n

/-- **Flat base change on the sections over an affine chart diagram.** -/
theorem bijective_moduleBaseChangeMap_app_val_app (sq : IsPullback g' f' f g)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hg : IsFlat B S hS g.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (d : ChartDiagram B S hS Y'.1 Y.1 g.hom)
    (hU : IsAffine (chartScheme d.U)) (hV : IsAffine (chartScheme d.V)) :
    Function.Bijective (((moduleBaseChangeMap f g f' g' sq.w).app F).val.app (op d.U)).hom := by
  obtain ⟨W, b, hb, R, R', t, s, k, hWa, hR'a, hsurj, hpb, hk⟩ :=
    exists_affine_presentation_chartBaseChange f hfqc hfqs d.V hV
  -- the data over `d.V`
  let e : ChartDiagram B S hS X.1 Y.1 f.hom := ⟨W, d.V, b, hb⟩
  let bR : (SmallEtale.toOver B S hS X.1).obj R' ⟶ (SmallEtale.toOver B S hS Y.1).obj d.V :=
    (SmallEtale.toOver B S hS X.1).map (k ≫ t) ≫ b
  have hbR : R'.1.hom ≫ f.hom = yoneda.map bR ≫ d.V.1.hom := chart_comp_comm f (k ≫ t) b hb
  have hts : (SmallEtale.toOver B S hS X.1).map (k ≫ s) ≫ b = bR := by
    have h := chartMap_comp_eq_of_isPullback f e hpb
    simp only [bR, Functor.map_comp, Category.assoc]
    exact congrArg (_ ≫ ·) h.symm
  let eR : ChartDiagram B S hS X.1 Y.1 f.hom := ⟨R', d.V, bR, hbR⟩
  -- the charts of `X'`
  let T := chartBaseChangeAlong sq d.g d.comm b hb
  let TR := chartBaseChangeAlong sq d.g d.comm bR hbR
  let e' := chartBaseChangeAlongDiagram sq d.g d.comm b hb
  let e'R := chartBaseChangeAlongDiagram sq d.g d.comm bR hbR
  let mt : TR ⟶ T := chartBaseChangeAlongMap sq d.g d.comm bR hbR b hb (k ≫ t) rfl
  let ms : TR ⟶ T := chartBaseChangeAlongMap sq d.g d.comm bR hbR b hb (k ≫ s) hts
  -- the modules
  let N := (modulePushforward B S hS f).obj F
  let F' := (modulePullback B S hS g').obj F
  let M := (modulePushforward B S hS f').obj F'
  have hN : N.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS f hfqc hfqs F hF
  -- the rings and the module structures
  let iAA' := chartDiagramAlgebra B S hS g d
  have : Module.Flat (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS Y'.1 Y'.2 d.U) :=
    moduleFlat_chartDiagram_of_isFlat B S hS hg d hU hV
  let mP : Module (chartRing B S hS Y.1 Y.2 d.V) (F.val.obj (op W)) :=
    Module.compHom _ (chartDiagramRestrict B S hS f e)
  let mQ : Module (chartRing B S hS Y.1 Y.2 d.V) (F.val.obj (op R')) :=
    Module.compHom _ (chartDiagramRestrict B S hS f eR)
  let mP' : Module (chartRing B S hS Y'.1 Y'.2 d.U) (F'.val.obj (op T)) :=
    Module.compHom _ (chartDiagramRestrict B S hS f' e')
  let mQ' : Module (chartRing B S hS Y'.1 Y'.2 d.U) (F'.val.obj (op TR)) :=
    Module.compHom _ (chartDiagramRestrict B S hS f' e'R)
  let mM : Module (chartRing B S hS Y.1 Y.2 d.V) (M.val.obj (op d.U)) :=
    Module.compHom _ (algebraMap (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS Y'.1 Y'.2 d.U))
  have : IsScalarTower (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS Y'.1 Y'.2 d.U)
      (M.val.obj (op d.U)) := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  obtain ⟨θP, hθP, hθPt⟩ := exists_bijective_liftBaseChange_unitSection sq F hF d hU hV b hb hWa
  obtain ⟨θQ, hθQ, hθQt⟩ :=
    exists_bijective_liftBaseChange_unitSection sq F hF d hU hV bR hbR hR'a
  -- the linear maps
  let iL : N.val.obj (op d.V) →ₗ[chartRing B S hS Y.1 Y.2 d.V] F.val.obj (op W) :=
    { toFun := modulePushforwardCounitApp B S hS f F e
      map_add' := modulePushforwardCounitApp_add B S hS f F e
      map_smul' := modulePushforwardCounitApp_smul B S hS f F e }
  let iL' : M.val.obj (op d.U) →ₗ[chartRing B S hS Y'.1 Y'.2 d.U] F'.val.obj (op T) :=
    { toFun := modulePushforwardCounitApp B S hS f' F' e'
      map_add' := modulePushforwardCounitApp_add B S hS f' F' e'
      map_smul' := modulePushforwardCounitApp_smul B S hS f' F' e' }
  let L : ∀ u : R' ⟶ W, (SmallEtale.toOver B S hS X.1).map u ≫ b = bR →
      F.val.obj (op W) →ₗ[chartRing B S hS Y.1 Y.2 d.V] F.val.obj (op R') := fun u hu =>
    { toFun := F.val.map u.op
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x => (F.val.map_smul u.op (chartDiagramRestrict B S hS f e r) x).trans
        (congrArg (· • F.val.map u.op x) (chartDiagramPullback_comp_apply_of_eq _ _ _ hu r)) }
  let mm : ∀ u : R' ⟶ W, (SmallEtale.toOver B S hS X.1).map u ≫ b = bR → (TR ⟶ T) :=
    fun u hu => chartBaseChangeAlongMap sq d.g d.comm bR hbR b hb u hu
  let L' : ∀ (u : R' ⟶ W) (hu : (SmallEtale.toOver B S hS X.1).map u ≫ b = bR),
      F'.val.obj (op T) →ₗ[chartRing B S hS Y'.1 Y'.2 d.U] F'.val.obj (op TR) := fun u hu =>
    { toFun := F'.val.map (mm u hu).op
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x => (F'.val.map_smul (mm u hu).op (chartDiagramRestrict B S hS f' e' r)
        x).trans (congrArg (· • F'.val.map (mm u hu).op x) (chartDiagramPullback_comp_apply_of_eq
          _ _ _ (chartBaseChangeAlongMap_snd sq d.g d.comm bR hbR b hb u hu) r)) }
  let aL := L (k ≫ t) rfl
  let bL := L (k ≫ s) hts
  let β : ((modulePullback B S hS g).obj N).val.obj (op d.U) ⟶ M.val.obj (op d.U) :=
    ((moduleBaseChangeMap f g f' g' sq.w).app F).val.app (op d.U)
  let μ : N.val.obj (op d.V) →ₗ[chartRing B S hS Y.1 Y.2 d.V] M.val.obj (op d.U) :=
    { toFun := fun n => β.hom (modulePullbackChartSection B S hS g N d n)
      map_add' := fun x y => by
        rw [modulePullbackChartSection_add, map_add]
      map_smul' := fun r x => by
        rw [modulePullbackChartSection_smul, map_smul]
        rfl }
  have hi : Function.Injective iL := injective_modulePushforwardCounitApp f F e hsurj
  have hnat : ∀ u hu x, L u hu (iL x) =
      modulePushforwardCounitApp B S hS f F eR (N.val.map (𝟙 d.V).op x) := fun u hu x =>
    (modulePushforwardCounitApp_naturality B S hS f F e eR u (𝟙 d.V) (by
      rw [CategoryTheory.Functor.map_id, Category.comp_id]; exact hu) x).symm
  have hab : aL ∘ₗ iL = bL ∘ₗ iL := LinearMap.ext fun x =>
    (hnat _ rfl x).trans (hnat _ hts x).symm
  have heq : ∀ p, aL p = bL p → ∃ n, iL n = p := fun p hp =>
    exists_modulePushforwardCounitApp_eq f F e hsurj t s hpb k hk p
      ((F.val.map_comp_apply t.op k.op p).symm.trans (hp.trans (F.val.map_comp_apply s.op k.op p)))
  have hi' : Function.Injective iL' := injective_modulePushforwardCounitApp f' F' e'
    (isSurjective_chartLift_chartBaseChangeAlongDiagram sq d.g d.comm b hb hsurj)
  have hnat' : ∀ u hu x, L' u hu (iL' x) =
      modulePushforwardCounitApp B S hS f' F' e'R (M.val.map (𝟙 d.U).op x) := fun u hu x =>
    (modulePushforwardCounitApp_naturality B S hS f' F' e' e'R (mm u hu) (𝟙 d.U) (by
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
      exact chartBaseChangeAlongMap_snd sq d.g d.comm bR hbR b hb u hu) x).symm
  have hab' : (L' _ rfl) ∘ₗ iL' = (L' _ hts) ∘ₗ iL' := LinearMap.ext fun x =>
    (hnat' _ rfl x).trans (hnat' _ hts x).symm
  let κ : ChartDiagram B S hS X'.1 X.1 g'.hom :=
    ⟨T, W, pullback.fst b d.g, chartBaseChangeAlong_fst sq d.g d.comm b hb⟩
  let κR : ChartDiagram B S hS X'.1 X.1 g'.hom :=
    ⟨TR, R', pullback.fst bR d.g, chartBaseChangeAlong_fst sq d.g d.comm bR hbR⟩
  have hL : ∀ u hu z,
      L' u hu (θP z) = θQ ((L u hu).baseChange (chartRing B S hS Y'.1 Y'.2 d.U) z) :=
    fun u hu => LinearMap.map_liftBaseChange_eq_of_tmul θP θQ
      (modulePullbackUnitSection B S hS g' F κ) (modulePullbackUnitSection B S hS g' F κR) hθPt hθQt
      (L u hu) (L' u hu) (fun p => modulePullbackUnitSection_naturality g' F κ κR (mm u hu) u
        (chartBaseChangeAlongMap_fst sq d.g d.comm bR hbR b hb u hu) p)
  have hμ : ∀ n, iL' (μ n) = θP (1 ⊗ₜ iL n) := fun n =>
    (modulePushforwardCounitApp_moduleBaseChangeMap_chartSection sq F d b hb n).trans
      ((one_smul _ _).symm.trans (hθPt 1 (iL n)).symm)
  have hbij := LinearMap.bijective_liftBaseChange_of_equalizer
    (A' := chartRing B S hS Y'.1 Y'.2 d.U)
    iL aL bL hi hab heq iL' (L' _ rfl) (L' _ hts) hi' hab' θP θQ hθP hθQ.1 (hL _ rfl) (hL _ hts) μ
    hμ
  have hcmp :=
    bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS g N hN d hU hV
  have h1 : ∀ n, modulePullbackChartBaseChange B S hS g N d (1 ⊗ₜ n) =
      modulePullbackChartSection B S hS g N d n := fun n =>
    (modulePullbackChartBaseChange_tmul B S hS g N d 1 n).trans (one_smul _ _)
  exact LinearMap.bijective_of_comp_liftBaseChange (A' := chartRing B S hS Y'.1 Y'.2 d.U)
    (modulePullbackChartBaseChange B S hS g N d) β.hom μ (fun n => congrArg β.hom (h1 n)) hcmp hbij

/-- **Flat base change for the direct image of a quasi-coherent module, in degree zero**
(Stacks 073K, part (1), degree zero).  For a cartesian square of algebraic spaces whose bottom
morphism `g` is flat and whose right morphism `f` is quasi-compact and quasi-separated, the base
change map `g^*f_*F ⟶ f'_*(g')^*F` is an isomorphism at every quasi-coherent `𝒪_X`-module
`F`. -/
theorem isIso_moduleBaseChangeMap_app_of_isFlat (sq : IsPullback g' f' f g)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hg : IsFlat B S hS g.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) :
    IsIso ((moduleBaseChangeMap f g f' g' sq.w).app F) :=
  isIso_of_bijective_affineChartDiagram B S hS g _ fun d hU hV =>
    bijective_moduleBaseChangeMap_app_val_app sq hfqc hfqs hg F hF d hU hV

end Main

section Pointwise

variable (B S hS)

/-- **The degree-zero clause of Stacks 073K, part (1), for the cartesian squares over a fixed
morphism `f`**:  for `f` quasi-compact and quasi-separated and for every cartesian square

```
X' --g'--> X
|f'        |f
Y' --g-->  Y
```

whose base `g` is flat, the base change map
`AlgebraicGeometry.Space.moduleBaseChangeMap` of the square is an isomorphism at every
quasi-coherent `𝒪_X`-module.  It holds for every morphism, by
`AlgebraicGeometry.Space.flatBaseChangeZero`.

The map in question is pinned down by
`AlgebraicGeometry.Space.moduleBaseChangeMap_adjoint_split`:  it is the inverse image along the
top of the square of the counit of `f^* ⊣ f_*`, transported across the comparison of the two
composite inverse images, which is the description the source gives it by. -/
def FlatBaseChangeZero {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) : Prop :=
  IsQuasiCompact B S hS f.hom → IsQuasiSeparated B S hS f.hom →
    ∀ {X' Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
      (comm : g' ≫ f = f' ≫ g), IsPullback g' f' f g → IsFlat B S hS g.hom →
        ∀ (F : Modules.{u, u} B S hS X.1 X.2), F.IsQuasicoherentOnSite →
          IsIso ((moduleBaseChangeMap f g f' g' comm).app F)

/-- **Flat base change in degree zero holds for every morphism of algebraic spaces**, in the
shape `AlgebraicGeometry.Space.FlatBaseChangeZero`. -/
theorem flatBaseChangeZero {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    FlatBaseChangeZero B S hS f := by
  intro hfqc hfqs X' Y' g f' g' comm sq hg F hF
  have h := isIso_moduleBaseChangeMap_app_of_isFlat sq hfqc hfqs hg F hF
  have e : sq.w = comm := Subsingleton.elim _ _
  rw [e] at h
  exact h

end Pointwise

end AlgebraicGeometry.Space

end
