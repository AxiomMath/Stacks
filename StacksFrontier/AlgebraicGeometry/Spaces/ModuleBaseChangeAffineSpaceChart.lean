module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureMap
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapCompDischarge
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicFunctionsPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicRepresentableComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangeMapChartFormula
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.QcqsOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineBijective

/-!
# Affine base change of modules

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a cartesian square of algebraic spaces with `Y` and `Y'` affine.  The base change map
`f^*g_*M ⟶ g'_*(f')^*M` of modules is an isomorphism for every quasi-coherent `𝒪_{Y'}`-module
`M`: on an affine étale chart `Z` of `X` both sides are `𝒪(Z) ⊗_{𝒪(Y)} M(Y')`.

## Main results

* `AlgebraicGeometry.Space.isIso_moduleBaseChangeMap_app_of_isAffineSpace`: **affine base change
  of modules.**
* `AlgebraicGeometry.Space.bijective_moduleBaseChangeMap_app_of_chartSquare`: the base change
  map on the sections over a chart, for a square of affine charts whose rings form a pushout.

* `AlgebraicGeometry.Space.bijective_modulePushforwardCounitApp_baseChangeChartDiagram`: the
  sections of a direct image along a representable morphism over a chart are the sections over
  the base-changed chart.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Counit

variable {X Y : AlgebraicSpaces B S hS}

/-- **The sections of a direct image along a representable morphism over a chart `V` are the
sections over the base-changed chart `X ×_Y V`**: the canonical map of sections at the chart
diagram of the base change is bijective. -/
theorem bijective_modulePushforwardCounitApp_baseChangeChartDiagram (f : X ⟶ Y)
    (hr : yoneda.relativelyRepresentable f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS Y.1) :
    Function.Bijective (modulePushforwardCounitApp B S hS f F
      (baseChangeChartDiagram B S hS f hr V)) := by
  have hd : baseChangeChartDiagram B S hS f hr V =
      chartDiagramOfIndex B S hS f V (chartBaseChangeArrow B S hS f hr V) :=
    ChartDiagram.ext B S hS _ _ rfl rfl
      (heq_of_eq (chartBaseChangeMap_chartBaseChangeArrow B S hS f hr V).symm)
  rw [hd]
  let j := indexOfChartDiagram B S hS f
    (chartDiagramOfIndex B S hS f V (chartBaseChangeArrow B S hS f hr V))
  have hπ : IsIso ((ranChartCone B S hS X (moduleSetSheaf B S hS X F).obj
      (chartBaseChange B S hS f V)).π.app j) :=
    (ranChartIsLimit B S hS X _ _).isIso_π_app_of_isInitial _
      ((chartBaseChangeArrowIsInitial B S hS f hr V).ofIso
        (eqToIso (indexOfChartDiagram_chartDiagramOfIndex B S hS f V _).symm))
  have hi : IsIso (((smallEtaleDirectImageRanIso B S hS f).hom.app
      (moduleSetSheaf B S hS X F)).hom.app (op V)) := inferInstance
  have e : modulePushforwardCounitApp B S hS f F
      (chartDiagramOfIndex B S hS f V (chartBaseChangeArrow B S hS f hr V)) =
      ((ranChartCone B S hS X (moduleSetSheaf B S hS X F).obj
        (chartBaseChange B S hS f V)).π.app j) ∘
      (((smallEtaleDirectImageRanIso B S hS f).hom.app
        (moduleSetSheaf B S hS X F)).hom.app (op V)) :=
    funext fun x => moduleChartProjection_app B S hS f V j _ x
  rw [e]
  exact ((isIso_iff_bijective _).1 hπ).comp ((isIso_iff_bijective _).1 hi)

end Counit

section CounitEquiv

variable {X Y : AlgebraicSpaces B S hS}

/-- The canonical map of sections into a direct image at a chart diagram, as an additive
equivalence when it is bijective. -/
def modulePushforwardCounitAddEquiv (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (h : Function.Bijective (modulePushforwardCounitApp B S hS f F d)) :
    ((modulePushforward B S hS f).obj F).val.obj (op d.V) ≃+ F.val.obj (op d.U) :=
  AddEquiv.ofBijective (AddMonoidHom.mk' (modulePushforwardCounitApp B S hS f F d)
    (modulePushforwardCounitApp_add B S hS f F d)) h

/-- `AlgebraicGeometry.Space.modulePushforwardCounitAddEquiv` is the canonical map of sections. -/
theorem modulePushforwardCounitAddEquiv_apply (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (h : Function.Bijective (modulePushforwardCounitApp B S hS f F d))
    (x : ((modulePushforward B S hS f).obj F).val.obj (op d.V)) :
    modulePushforwardCounitAddEquiv f F d h x = modulePushforwardCounitApp B S hS f F d x :=
  rfl

/-- The canonical map of sections into a direct image is semilinear over the algebra structure
of a chart diagram. -/
theorem modulePushforwardCounitAddEquiv_smul (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (h : Function.Bijective (modulePushforwardCounitApp B S hS f F d))
    (r : chartRing B S hS Y.1 Y.2 d.V)
    (x : ((modulePushforward B S hS f).obj F).val.obj (op d.V)) :
    letI := chartDiagramAlgebra B S hS f d
    modulePushforwardCounitAddEquiv f F d h (r • x) =
      algebraMap (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS X.1 X.2 d.U) r •
        modulePushforwardCounitAddEquiv f F d h x :=
  modulePushforwardCounitApp_smul B S hS f F d r x

end CounitEquiv

/-- A map agreeing pointwise with a bijection is bijective. -/
theorem _root_.Function.Bijective.of_eq_apply {α β : Type*} {F G : α → β}
    (hF : Function.Bijective F) (h : ∀ w, G w = F w) : Function.Bijective G :=
  (funext h : G = F) ▸ hF

/-- The ring map of a chart diagram is the map of global functions of its vertical morphism. -/
theorem ofHom_chartDiagramRestrict_mk {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {U : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1}
    (c : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (hc : U.1.hom ≫ f.hom = yoneda.map c ≫ V.1.hom) :
    CommRingCat.ofHom (chartDiagramRestrict B S hS f ⟨U, V, c, hc⟩) =
      ((BigFppfOver.toScheme B S hS).map c).appTop :=
  rfl

section Square

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
  (g' : X' ⟶ X)

/-- The base change map `f^*g_*M ⟶ g'_*(f')^*M` on chart sections: the chart component of the
image of the chart section of `s` is the chart section of the chart component of `s`. -/
theorem modulePushforwardCounitApp_moduleBaseChangeMap_chartSection_of_comm
    (comm : f' ≫ g = g' ≫ f)
    (M : Modules.{u, u} B S hS Y'.1 Y'.2)
    {Z : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1} {U : SmallEtale B S hS Y'.1}
    {U' : SmallEtale B S hS X'.1}
    (b : (SmallEtale.toOver B S hS X.1).obj Z ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (hb : Z.1.hom ≫ f.hom = yoneda.map b ≫ V.1.hom)
    (c : (SmallEtale.toOver B S hS Y'.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (hc : U.1.hom ≫ g.hom = yoneda.map c ≫ V.1.hom)
    (a : (SmallEtale.toOver B S hS X'.1).obj U' ⟶ (SmallEtale.toOver B S hS X.1).obj Z)
    (ha : U'.1.hom ≫ g'.hom = yoneda.map a ≫ Z.1.hom)
    (t : (SmallEtale.toOver B S hS X'.1).obj U' ⟶ (SmallEtale.toOver B S hS Y'.1).obj U)
    (ht : U'.1.hom ≫ f'.hom = yoneda.map t ≫ U.1.hom) (hat : t ≫ c = a ≫ b)
    (s : ((modulePushforward B S hS g).obj M).val.obj (op V)) :
    modulePushforwardCounitApp B S hS g' ((modulePullback B S hS f').obj M) ⟨U', Z, a, ha⟩
        (((moduleBaseChangeMap g f g' f' comm).app M).val.app (op Z)
          (modulePullbackChartSection B S hS f ((modulePushforward B S hS g).obj M)
            ⟨Z, V, b, hb⟩ s)) =
      modulePullbackChartSection B S hS f' M ⟨U', U, t, ht⟩
        (modulePushforwardCounitApp B S hS g M ⟨U, V, c, hc⟩ s) := by
  rw [← modulePullbackUnitSection_eq_modulePullbackChartSection,
    ← modulePullbackUnitSection_eq_modulePullbackChartSection]
  exact modulePushforwardCounitApp_moduleBaseChangeMap_unitSection comm M t c a b ht hc ha hb hat s

/-- **The base change map `f^*g_*M ⟶ g'_*(f')^*M` on the sections over a chart `Z` of `X`.**
Let `Z ⟶ V` be a chart diagram over `f`, `U ⟶ V` one over `g` and `U' ⟶ Z`, `U' ⟶ U` ones over
`g'` and `f'` with `U' ⟶ Z ⟶ V = U' ⟶ U ⟶ V`, all four charts affine.  If the two canonical maps
of sections into the direct images at `U ⟶ V` and `U' ⟶ Z` are bijective, the rings of the four
charts form a pushout square, and `M` and `g_*M` are quasi-coherent, then the base change map is
bijective on the sections over `Z`: both sides are `𝒪(Z) ⊗_{𝒪(V)} M(U)`. -/
theorem bijective_moduleBaseChangeMap_app_of_chartSquare (comm : f' ≫ g = g' ≫ f)
    (M : Modules.{u, u} B S hS Y'.1 Y'.2) (hM : M.IsQuasicoherentOnSite)
    (hgM : ((modulePushforward B S hS g).obj M).IsQuasicoherentOnSite)
    {Z : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1} {U : SmallEtale B S hS Y'.1}
    {U' : SmallEtale B S hS X'.1}
    (b : (SmallEtale.toOver B S hS X.1).obj Z ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (hb : Z.1.hom ≫ f.hom = yoneda.map b ≫ V.1.hom)
    (c : (SmallEtale.toOver B S hS Y'.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (hc : U.1.hom ≫ g.hom = yoneda.map c ≫ V.1.hom)
    (a : (SmallEtale.toOver B S hS X'.1).obj U' ⟶ (SmallEtale.toOver B S hS X.1).obj Z)
    (ha : U'.1.hom ≫ g'.hom = yoneda.map a ≫ Z.1.hom)
    (t : (SmallEtale.toOver B S hS X'.1).obj U' ⟶ (SmallEtale.toOver B S hS Y'.1).obj U)
    (ht : U'.1.hom ≫ f'.hom = yoneda.map t ≫ U.1.hom) (hat : t ≫ c = a ≫ b)
    (hZ : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj Z))
    (hV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj V))
    (hU : IsAffine ((SmallEtale.toOver B S hS Y'.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hU' : IsAffine ((SmallEtale.toOver B S hS X'.1 ⋙ BigFppfOver.toScheme B S hS).obj U'))
    (hcU : Function.Bijective (modulePushforwardCounitApp B S hS g M ⟨U, V, c, hc⟩))
    (haU : Function.Bijective (modulePushforwardCounitApp B S hS g'
      ((modulePullback B S hS f').obj M) ⟨U', Z, a, ha⟩))
    (hpo : IsPushout (CommRingCat.ofHom (chartDiagramRestrict B S hS g ⟨U, V, c, hc⟩))
      (CommRingCat.ofHom (chartDiagramRestrict B S hS f ⟨Z, V, b, hb⟩))
      (CommRingCat.ofHom (chartDiagramRestrict B S hS f' ⟨U', U, t, ht⟩))
      (CommRingCat.ofHom (chartDiagramRestrict B S hS g' ⟨U', Z, a, ha⟩))) :
    Function.Bijective (((moduleBaseChangeMap g f g' f' comm).app M).val.app (op Z)).hom := by
  let iVZ : Algebra (chartRing B S hS Y.1 Y.2 V) (chartRing B S hS X.1 X.2 Z) :=
    chartDiagramAlgebra B S hS f ⟨Z, V, b, hb⟩
  let iVU : Algebra (chartRing B S hS Y.1 Y.2 V) (chartRing B S hS Y'.1 Y'.2 U) :=
    chartDiagramAlgebra B S hS g ⟨U, V, c, hc⟩
  let iUU' : Algebra (chartRing B S hS Y'.1 Y'.2 U) (chartRing B S hS X'.1 X'.2 U') :=
    chartDiagramAlgebra B S hS f' ⟨U', U, t, ht⟩
  let iZU' : Algebra (chartRing B S hS X.1 X.2 Z) (chartRing B S hS X'.1 X'.2 U') :=
    chartDiagramAlgebra B S hS g' ⟨U', Z, a, ha⟩
  let iVU' : Algebra (chartRing B S hS Y.1 Y.2 V) (chartRing B S hS X'.1 X'.2 U') :=
    ((chartDiagramRestrict B S hS g' ⟨U', Z, a, ha⟩).comp
      (chartDiagramRestrict B S hS f ⟨Z, V, b, hb⟩)).toAlgebra
  have hsq : ∀ r, chartDiagramRestrict B S hS f' ⟨U', U, t, ht⟩
      (chartDiagramRestrict B S hS g ⟨U, V, c, hc⟩ r) =
      chartDiagramRestrict B S hS g' ⟨U', Z, a, ha⟩
        (chartDiagramRestrict B S hS f ⟨Z, V, b, hb⟩ r) :=
    fun r => congrArg (fun φ => φ.hom r) hpo.w
  have : IsScalarTower (chartRing B S hS Y.1 Y.2 V) (chartRing B S hS Y'.1 Y'.2 U)
      (chartRing B S hS X'.1 X'.2 U') := IsScalarTower.of_algebraMap_eq fun r => (hsq r).symm
  have : IsScalarTower (chartRing B S hS Y.1 Y.2 V) (chartRing B S hS X.1 X.2 Z)
      (chartRing B S hS X'.1 X'.2 U') := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsPushout (chartRing B S hS Y.1 Y.2 V) (chartRing B S hS X.1 X.2 Z)
      (chartRing B S hS Y'.1 Y'.2 U) (chartRing B S hS X'.1 X'.2 U') :=
    (CommRingCat.isPushout_iff_isPushout.1 hpo).symm
  let := modulePullbackChartSectionModule B S hS f' M ⟨U', U, t, ht⟩
  have := modulePullbackChart_isScalarTower B S hS f' M ⟨U', U, t, ht⟩
  let iR₂ : Module (chartRing B S hS Y.1 Y.2 V)
      (((modulePushforward B S hS g').obj ((modulePullback B S hS f').obj M)).val.obj (op Z)) :=
    Module.compHom _ (chartDiagramRestrict B S hS f ⟨Z, V, b, hb⟩)
  have iT₂ : IsScalarTower (chartRing B S hS Y.1 Y.2 V) (chartRing B S hS X.1 X.2 Z)
      (((modulePushforward B S hS g').obj ((modulePullback B S hS f').obj M)).val.obj (op Z)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let φ : ((modulePushforward B S hS g).obj M).val.obj (op V) →ₗ[chartRing B S hS Y.1 Y.2 V]
      ((modulePushforward B S hS g').obj ((modulePullback B S hS f').obj M)).val.obj (op Z) :=
    { toFun := fun x => ((moduleBaseChangeMap g f g' f' comm).app M).val.app (op Z)
        (modulePullbackChartSection B S hS f ((modulePushforward B S hS g).obj M)
          ⟨Z, V, b, hb⟩ x)
      map_add' := fun x y => by
        rw [modulePullbackChartSection_add, map_add]
      map_smul' := fun r x => by
        rw [modulePullbackChartSection_smul, map_smul]
        rfl }
  have hL := Algebra.IsPushout.bijective_liftBaseChange_of_addEquiv
    (R := chartRing B S hS Y.1 Y.2 V) (Sr := chartRing B S hS X.1 X.2 Z)
    (A := chartRing B S hS Y'.1 Y'.2 U) (Bb := chartRing B S hS X'.1 X'.2 U')
    (iR₂ := iR₂) (iT₂ := iT₂)
    (modulePullbackChartSectionLinear B S hS f' M ⟨U', U, t, ht⟩)
    (bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS f' M hM
      ⟨U', U, t, ht⟩ hU' hU) φ
    (modulePushforwardCounitAddEquiv g M ⟨U, V, c, hc⟩ hcU)
    (modulePushforwardCounitAddEquiv g' ((modulePullback B S hS f').obj M) ⟨U', Z, a, ha⟩ haU)
    (modulePushforwardCounitAddEquiv_smul g M ⟨U, V, c, hc⟩ hcU)
    (modulePushforwardCounitAddEquiv_smul g' ((modulePullback B S hS f').obj M) ⟨U', Z, a, ha⟩
      haU)
    (modulePushforwardCounitApp_moduleBaseChangeMap_chartSection_of_comm f g f' g' comm M
      b hb c hc a ha t ht hat)
  refine (Function.Bijective.of_comp_iff _
    (bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS f
      ((modulePushforward B S hS g).obj M) hgM ⟨Z, V, b, hb⟩ hZ hV)).1
    (hL.of_eq_apply fun w => ?_)
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul z x =>
    rw [Function.comp_apply, LinearMap.liftBaseChange_tmul, modulePullbackChartBaseChange_tmul,
      map_smul]
    rfl
  | add w₁ w₂ h₁ h₂ =>
    rw [map_add, ← h₁, ← h₂]
    simp only [Function.comp_apply, map_add]

/-- **Affine base change of modules.**  For a cartesian square of algebraic spaces with `Y` and
`Y'` affine, the base change map `f^*g_*M ⟶ g'_*(f')^*M` is an isomorphism at every
quasi-coherent `𝒪_{Y'}`-module `M`.  On an affine étale chart `Z` of `X` both sides are
`𝒪(Z) ⊗_{𝒪(Y)} M(Y')`. -/
theorem isIso_moduleBaseChangeMap_app_of_isAffineSpace (sq : IsPullback g' f' f g)
    (hY : IsAffineSpace B S hS Y.1) (hY' : IsAffineSpace B S hS Y'.1)
    (M : Modules.{u, u} B S hS Y'.1 Y'.2) (hM : M.IsQuasicoherentOnSite) :
    IsIso ((moduleBaseChangeMap g f g' f' sq.w.symm).app M) := by
  have sqh := AlgebraicSpaces.isPullback_hom B S hS sq
  have hg : IsAffineHom B S hS g.hom := isAffineHom_of_isAffineSpace B S hS g.hom hY' hY
  have hg' : IsAffineHom B S hS g'.hom := isAffineHom_of_isPullback sqh.flip hg
  have hrg := relativelyRepresentable_of_isAffineHom B S hS g hg
  have hrg' := relativelyRepresentable_of_isAffineHom B S hS g' hg'
  obtain ⟨T, hT, ⟨e⟩⟩ := hY
  let V : SmallEtale B S hS Y.1 :=
    ⟨CostructuredArrow.mk e.inv, isEtaleChart_of_isIso B S hS T e.inv⟩
  have hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)) :=
    hT
  refine SmallEtale.isIso_of_bijective_app_of_isAffineChart B S hS X.1 X.2 _ fun Z hZ => ?_
  let b : (SmallEtale.toOver B S hS X.1).obj Z ⟶ (SmallEtale.toOver B S hS Y.1).obj V :=
    yoneda.preimage (Z.1.hom ≫ f.hom ≫ e.hom)
  have hb : Z.1.hom ≫ f.hom = yoneda.map b ≫ V.1.hom := by
    show _ = yoneda.map (yoneda.preimage _) ≫ e.inv
    rw [Functor.map_preimage, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let U := (smallBaseChange B S hS g hrg).obj V
  let U' := (smallBaseChange B S hS g' hrg').obj Z
  have hU : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y'.1).obj U)) :=
    isAffine_smallBaseChange_obj B S hS g hrg hg V hV
  have hU' : IsAffine ((SmallEtale.toOver B S hS X'.1 ⋙ BigFppfOver.toScheme B S hS).obj U') :=
    isAffine_smallBaseChange_obj B S hS g' hrg' hg' Z hZ
  let a : (SmallEtale.toOver B S hS X'.1).obj U' ⟶ (SmallEtale.toOver B S hS X.1).obj Z :=
    hrg'.snd Z.1.hom
  have ha : U'.1.hom ≫ g'.hom = yoneda.map a ≫ Z.1.hom := hrg'.w Z.1.hom
  let c : (SmallEtale.toOver B S hS Y'.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V :=
    hrg.snd V.1.hom
  have hc : U.1.hom ≫ g.hom = yoneda.map c ≫ V.1.hom := hrg.w V.1.hom
  have hcond : (U'.1.hom ≫ f'.hom) ≫ g.hom = yoneda.map (a ≫ b) ≫ V.1.hom := by
    rw [Category.assoc, ← sqh.w, ← Category.assoc, ha, Category.assoc, hb, Functor.map_comp,
      Category.assoc]
  let t : (SmallEtale.toOver B S hS X'.1).obj U' ⟶ (SmallEtale.toOver B S hS Y'.1).obj U :=
    hrg.lift (U'.1.hom ≫ f'.hom) (a ≫ b) hcond
  have ht : U'.1.hom ≫ f'.hom = yoneda.map t ≫ U.1.hom := (hrg.lift_fst _ _ _).symm
  have hat : t ≫ c = a ≫ b := hrg.lift_snd _ _ _
  have hpb : IsPullback (yoneda.map t) (yoneda.map a) (yoneda.map c) (yoneda.map b) := by
    have hbig : IsPullback (U'.1.hom ≫ f'.hom) (yoneda.map a) g.hom (Z.1.hom ≫ f.hom) :=
      (hrg'.isPullback Z.1.hom).paste_horiz sqh.flip
    rw [ht, hb] at hbig
    exact IsPullback.of_right hbig
      (by rw [← Functor.map_comp, ← Functor.map_comp, hat]) (hrg.isPullback V.1.hom)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj Z)) :=
    hZ
  have hpo := isPushout_appTop_of_isPullback
    ((IsPullback.of_map_of_faithful yoneda hpb).map (BigFppfOver.toScheme B S hS))
  rw [← ofHom_chartDiagramRestrict_mk g c hc, ← ofHom_chartDiagramRestrict_mk f b hb,
    ← ofHom_chartDiagramRestrict_mk f' t ht, ← ofHom_chartDiagramRestrict_mk g' a ha] at hpo
  exact bijective_moduleBaseChangeMap_app_of_chartSquare f g f' g' sq.w.symm M hM
    (isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional B S hS g hg M hM)
    b hb c hc a ha t ht hat hZ hV hU hU'
    (bijective_modulePushforwardCounitApp_baseChangeChartDiagram g hrg M V)
    (bijective_modulePushforwardCounitApp_baseChangeChartDiagram g' hrg' _ Z) hpo

end Square

end AlgebraicGeometry.Space

end
