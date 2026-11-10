module

public import StacksFrontier.AlgebraicGeometry.Spaces.RetractionReductionExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackCompIsoChartSection

/-!
# Transfer of the direct image along a morphism of retractions

Let `r₁ : X₁ ⟶ X₀` and `r₂ : X₂ ⟶ X₀` be representable morphisms of algebraic spaces and
`h : X₂ ⟶ X₁` a morphism with `h ≫ r₁ = r₂`. For an `𝒪_{X₁}`-module `ℱ₁`, an `𝒪_{X₂}`-module
`ℱ₂` and a morphism `θ : h^*ℱ₁ ⟶ ℱ₂`, the chart components of the unit of `h^* ⊣ h_*` at the
diagrams `U ×_{X₀} X₂ ⟶ U ×_{X₀} X₁` followed by `θ` make up a morphism of `𝒪_{X₀}`-modules

`r₁_*ℱ₁ ⟶ r₂_*ℱ₂`,

the *transfer* along `(h, θ)`. For sections `i₁ = i₂ ≫ h` of `r₁` and `r₂`, the transfer is
compatible with the reductions along `i₁` and `i₂`, and with multiplication by global functions.

## Main definitions

* `AlgebraicGeometry.Space.transferChartDiagram`: the diagram `U ×_{X₀} X₂ ⟶ U ×_{X₀} X₁` of
  étale charts over `h`.
* `AlgebraicGeometry.Space.transferMap`: the transfer `r₁_*ℱ₁ ⟶ r₂_*ℱ₂`.

## Main results

* `AlgebraicGeometry.Space.transferMap_naturality`: it is natural in `(ℱ₁, ℱ₂, θ)`.
* `AlgebraicGeometry.Space.transferMap_comp_reductionMap`: it is compatible with the
  reductions, read through the comparison of Stacks 03LU for `i₂ ≫ h = i₁`.
* `AlgebraicGeometry.Space.transferMap_comp_globalSmul`: it carries multiplication by a global
  function to multiplication by its pullback.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Transfer

variable {X₀ X₁ X₂ : AlgebraicSpaces B S hS}
  (r₁ : X₁ ⟶ X₀) (hrep₁ : yoneda.relativelyRepresentable r₁.hom)
  (r₂ : X₂ ⟶ X₀) (hrep₂ : yoneda.relativelyRepresentable r₂.hom)
  (h : X₂ ⟶ X₁) (hr : h ≫ r₁ = r₂)

/-- The morphism `U ×_{X₀} X₂ ⟶ U ×_{X₀} X₁` of the site attached to `h`. -/
def transferChartMap (U : SmallEtale B S hS X₀.1) :
    hrep₂.pullback U.1.hom ⟶ hrep₁.pullback U.1.hom :=
  hrep₁.lift (hrep₂.fst U.1.hom ≫ h.hom) (hrep₂.snd U.1.hom) (by
    rw [Category.assoc, show h.hom ≫ r₁.hom = r₂.hom from congrArg (fun f => f.hom) hr,
      hrep₂.w])

/-- The transfer chart map followed by the first projection of `U ×_{X₀} X₁` is the first
projection of `U ×_{X₀} X₂` followed by `h`. -/
theorem transferChartMap_fst (U : SmallEtale B S hS X₀.1) :
    yoneda.map (transferChartMap B S hS r₁ hrep₁ r₂ hrep₂ h hr U) ≫ hrep₁.fst U.1.hom =
      hrep₂.fst U.1.hom ≫ h.hom :=
  hrep₁.lift_fst _ _ _

/-- The transfer chart map followed by the projection of `U ×_{X₀} X₁` to `U` is the projection
of `U ×_{X₀} X₂` to `U`. -/
theorem transferChartMap_snd (U : SmallEtale B S hS X₀.1) :
    transferChartMap B S hS r₁ hrep₁ r₂ hrep₂ h hr U ≫ hrep₁.snd U.1.hom =
      hrep₂.snd U.1.hom :=
  hrep₁.lift_snd _ _ _

/-- **The diagram of étale charts `U ×_{X₀} X₂ ⟶ U ×_{X₀} X₁` over `h`.** -/
def transferChartDiagram (U : SmallEtale B S hS X₀.1) : ChartDiagram B S hS X₂.1 X₁.1 h.hom where
  U := (smallBaseChange B S hS r₂ hrep₂).obj U
  V := (smallBaseChange B S hS r₁ hrep₁).obj U
  g := transferChartMap B S hS r₁ hrep₁ r₂ hrep₂ h hr U
  comm := (transferChartMap_fst B S hS r₁ hrep₁ r₂ hrep₂ h hr U).symm

/-- The transfer chart maps commute with étale restriction of the chart of `X₀`. -/
theorem transferChartMap_naturality {U₁ U₂ : SmallEtale B S hS X₀.1} (k : U₁ ⟶ U₂) :
    (SmallEtale.toOver B S hS X₂.1).map ((smallBaseChange B S hS r₂ hrep₂).map k) ≫
        transferChartMap B S hS r₁ hrep₁ r₂ hrep₂ h hr U₂ =
      transferChartMap B S hS r₁ hrep₁ r₂ hrep₂ h hr U₁ ≫
        (SmallEtale.toOver B S hS X₁.1).map ((smallBaseChange B S hS r₁ hrep₁).map k) := by
  let L₁ : hrep₁.pullback U₁.1.hom ⟶ hrep₁.pullback U₂.1.hom :=
    hrep₁.lift (hrep₁.fst U₁.1.hom) (hrep₁.snd U₁.1.hom ≫ k.hom.left)
      (representablePullback_lift_cond B S hS r₁ hrep₁ k)
  let L₂ : hrep₂.pullback U₁.1.hom ⟶ hrep₂.pullback U₂.1.hom :=
    hrep₂.lift (hrep₂.fst U₁.1.hom) (hrep₂.snd U₁.1.hom ≫ k.hom.left)
      (representablePullback_lift_cond B S hS r₂ hrep₂ k)
  change (L₂ ≫ transferChartMap B S hS r₁ hrep₁ r₂ hrep₂ h hr U₂ :
      hrep₂.pullback U₁.1.hom ⟶ hrep₁.pullback U₂.1.hom) =
    transferChartMap B S hS r₁ hrep₁ r₂ hrep₂ h hr U₁ ≫ L₁
  apply hrep₁.hom_ext
  · rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
      transferChartMap_fst, hrep₁.lift_fst, ← Category.assoc, hrep₂.lift_fst,
      transferChartMap_fst]
  · rw [Category.assoc, Category.assoc, transferChartMap_snd, hrep₁.lift_snd,
      hrep₂.lift_snd, ← Category.assoc, transferChartMap_snd]

/-- Pulling back the structure map of small-chart base change along `r₁` by the transfer chart
map is the structure map along `r₂`. -/
theorem chartDiagramRestrict_transferChartDiagram_smallBaseChangeSharp
    (U : SmallEtale B S hS X₀.1) (a : chartRing B S hS X₀.1 X₀.2 U) :
    chartDiagramRestrict B S hS h (transferChartDiagram B S hS r₁ hrep₁ r₂ hrep₂ h hr U)
        ((smallBaseChangeSharp B S hS r₁ hrep₁).hom.app (op U) a) =
      (smallBaseChangeSharp B S hS r₂ hrep₂).hom.app (op U) a := by
  have h' : Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (hrep₁.snd U.1.hom)).op ≫
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (transferChartMap B S hS r₁ hrep₁ r₂ hrep₂ h hr U)).op =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (hrep₂.snd U.1.hom)).op := by
    rw [← Scheme.Γ.map_comp, ← op_comp, ← Functor.map_comp, transferChartMap_snd]
  exact congrArg (fun f => f.hom a) h'

variable {F₁ : Modules.{u, u} B S hS X₁.1 X₁.2} {F₂ : Modules.{u, u} B S hS X₂.1 X₂.2}

/-- The transfer `r₁_*ℱ₁ ⟶ r₂_*(h^*ℱ₁)` along `h`: over a chart `U` of `X₀` it is the chart
component of the unit of `h^* ⊣ h_*` at `U ×_{X₀} X₂ ⟶ U ×_{X₀} X₁`. -/
def transferUnit (F₁ : Modules.{u, u} B S hS X₁.1 X₁.2) :
    (retractionPushforward B S hS r₁ hrep₁).obj F₁ ⟶
      (retractionPushforward B S hS r₂ hrep₂).obj ((modulePullback B S hS h).obj F₁) where
  val := PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := (modulePullbackChartFMap B S hS h F₁).app
            (transferChartDiagram B S hS r₁ hrep₁ r₂ hrep₂ h hr U.unop)
          map_zero' := by
            have e := (modulePullbackChartFMap B S hS h F₁).map_add
              (transferChartDiagram B S hS r₁ hrep₁ r₂ hrep₂ h hr U.unop) 0 0
            rw [add_zero] at e
            exact left_eq_add.mp e
          map_add' := (modulePullbackChartFMap B S hS h F₁).map_add
            (transferChartDiagram B S hS r₁ hrep₁ r₂ hrep₂ h hr U.unop) }
      naturality := fun {U₁ U₂} k => by
        ext s
        exact (modulePullbackChartFMap B S hS h F₁).naturality
          (transferChartDiagram B S hS r₁ hrep₁ r₂ hrep₂ h hr U₁.unop)
          (transferChartDiagram B S hS r₁ hrep₁ r₂ hrep₂ h hr U₂.unop)
          ((smallBaseChange B S hS r₂ hrep₂).map k.unop)
          ((smallBaseChange B S hS r₁ hrep₁).map k.unop)
          (transferChartMap_naturality B S hS r₁ hrep₁ r₂ hrep₂ h hr k.unop) s }
    (fun U a s => by
      refine ((modulePullbackChartFMap B S hS h F₁).map_smul
        (transferChartDiagram B S hS r₁ hrep₁ r₂ hrep₂ h hr U.unop)
        ((smallBaseChangeSharp B S hS r₁ hrep₁).hom.app U a) s).trans ?_
      congr 1
      exact chartDiagramRestrict_transferChartDiagram_smallBaseChangeSharp B S hS r₁ hrep₁ r₂
        hrep₂ h hr U.unop a)

/-- Over a chart `U` of `X₀`, the transfer `r₁_*ℱ₁ ⟶ r₂_*(h^*ℱ₁)` sends a section to its chart
section along `U ×_{X₀} X₂ ⟶ U ×_{X₀} X₁`. -/
theorem transferUnit_app (F₁ : Modules.{u, u} B S hS X₁.1 X₁.2) (U : SmallEtale B S hS X₀.1)
    (s : F₁.val.obj (op ((smallBaseChange B S hS r₁ hrep₁).obj U))) :
    (transferUnit B S hS r₁ hrep₁ r₂ hrep₂ h hr F₁).val.app (op U) s =
      modulePullbackChartSection B S hS h F₁
        (transferChartDiagram B S hS r₁ hrep₁ r₂ hrep₂ h hr U) s := by
  change (modulePullbackChartFMap B S hS h F₁).app
    (transferChartDiagram B S hS r₁ hrep₁ r₂ hrep₂ h hr U) s = _
  exact modulePullbackChartFMap_app B S hS h F₁
    (transferChartDiagram B S hS r₁ hrep₁ r₂ hrep₂ h hr U) s

/-- **The transfer `r₁_*ℱ₁ ⟶ r₂_*ℱ₂` along `(h, θ)`**: the transfer to `r₂_*(h^*ℱ₁)` followed
by the direct image of `θ`. -/
def transferMap (θ : (modulePullback B S hS h).obj F₁ ⟶ F₂) :
    (retractionPushforward B S hS r₁ hrep₁).obj F₁ ⟶
      (retractionPushforward B S hS r₂ hrep₂).obj F₂ :=
  transferUnit B S hS r₁ hrep₁ r₂ hrep₂ h hr F₁ ≫ (retractionPushforward B S hS r₂ hrep₂).map θ

/-- Over a chart `U` of `X₀`, the transfer `r₁_*ℱ₁ ⟶ r₂_*ℱ₂` sends a section to the image under
`θ` of its chart section along `U ×_{X₀} X₂ ⟶ U ×_{X₀} X₁`. -/
theorem transferMap_app (θ : (modulePullback B S hS h).obj F₁ ⟶ F₂) (U : SmallEtale B S hS X₀.1)
    (s : F₁.val.obj (op ((smallBaseChange B S hS r₁ hrep₁).obj U))) :
    (transferMap B S hS r₁ hrep₁ r₂ hrep₂ h hr θ).val.app (op U) s =
      θ.val.app (op ((smallBaseChange B S hS r₂ hrep₂).obj U))
        (modulePullbackChartSection B S hS h F₁
          (transferChartDiagram B S hS r₁ hrep₁ r₂ hrep₂ h hr U) s) :=
  congrArg (θ.val.app (op ((smallBaseChange B S hS r₂ hrep₂).obj U)))
    (transferUnit_app B S hS r₁ hrep₁ r₂ hrep₂ h hr F₁ U s)

/-- Morphisms of modules on the small étale site of `X₀` agree if they agree on all sections. -/
private theorem modules_hom_ext {X₀ : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS X₀.1 X₀.2} {f g : M ⟶ N}
    (h : ∀ (U : (SmallEtale B S hS X₀.1)ᵒᵖ) (s : M.val.obj U),
      f.val.app U s = g.val.app U s) : f = g :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun s => h U s))

/-- **The transfer is natural** in the two modules and the morphism `θ`. -/
theorem transferMap_naturality {F₁' : Modules.{u, u} B S hS X₁.1 X₁.2}
    {F₂' : Modules.{u, u} B S hS X₂.1 X₂.2} (a₁ : F₁ ⟶ F₁') (a₂ : F₂ ⟶ F₂')
    (θ : (modulePullback B S hS h).obj F₁ ⟶ F₂) (θ' : (modulePullback B S hS h).obj F₁' ⟶ F₂')
    (hθ : (modulePullback B S hS h).map a₁ ≫ θ' = θ ≫ a₂) :
    (retractionPushforward B S hS r₁ hrep₁).map a₁ ≫
        transferMap B S hS r₁ hrep₁ r₂ hrep₂ h hr θ' =
      transferMap B S hS r₁ hrep₁ r₂ hrep₂ h hr θ ≫
        (retractionPushforward B S hS r₂ hrep₂).map a₂ := by
  refine modules_hom_ext B S hS fun U s => ?_
  have h1 := transferMap_app B S hS r₁ hrep₁ r₂ hrep₂ h hr θ' U.unop
    (a₁.val.app (op ((smallBaseChange B S hS r₁ hrep₁).obj U.unop)) s)
  have h2 := transferMap_app B S hS r₁ hrep₁ r₂ hrep₂ h hr θ U.unop s
  have h3 := modulePullbackChartSection_map B S hS h F₁ a₁
    (transferChartDiagram B S hS r₁ hrep₁ r₂ hrep₂ h hr U.unop) s
  have h4 := congrArg (fun φ : (modulePullback B S hS h).obj F₁ ⟶ F₂' =>
      φ.val.app (op ((smallBaseChange B S hS r₂ hrep₂).obj U.unop))
        (modulePullbackChartSection B S hS h F₁
          (transferChartDiagram B S hS r₁ hrep₁ r₂ hrep₂ h hr U.unop) s)) hθ
  refine h1.trans ?_
  refine (congrArg (θ'.val.app (op ((smallBaseChange B S hS r₂ hrep₂).obj U.unop))) h3.symm).trans
    ?_
  refine h4.trans ?_
  exact congrArg (a₂.val.app (op ((smallBaseChange B S hS r₂ hrep₂).obj U.unop))) h2.symm

/-- **The transfer carries multiplication by a global function to multiplication by its
pullback**: if a global function `a₂` of `X₂` is, on every base-changed chart, the pullback of
the global function `a₁` of `X₁` along the transfer chart map, then multiplication by `a₁`
followed by the transfer is the transfer followed by multiplication by `a₂`. -/
theorem transferMap_comp_globalSmul (θ : (modulePullback B S hS h).obj F₁ ⟶ F₂)
    (a₁ : Stacks.Cohomology.SiteModules.GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X₁.1 X₁.2).O))
    (a₂ : Stacks.Cohomology.SiteModules.GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X₂.1 X₂.2).O))
    (ha : ∀ U : SmallEtale B S hS X₀.1,
      chartDiagramRestrict B S hS h (transferChartDiagram B S hS r₁ hrep₁ r₂ hrep₂ h hr U)
        (a₁.1 (op ((smallBaseChange B S hS r₁ hrep₁).obj U))) =
          a₂.1 (op ((smallBaseChange B S hS r₂ hrep₂).obj U))) :
    (retractionPushforward B S hS r₁ hrep₁).map
        (Stacks.Cohomology.SiteModules.globalSmul _ a₁ F₁) ≫
        transferMap B S hS r₁ hrep₁ r₂ hrep₂ h hr θ =
      transferMap B S hS r₁ hrep₁ r₂ hrep₂ h hr θ ≫
        (retractionPushforward B S hS r₂ hrep₂).map
          (Stacks.Cohomology.SiteModules.globalSmul _ a₂ F₂) := by
  refine modules_hom_ext B S hS fun U
    (s : F₁.val.obj (op ((smallBaseChange B S hS r₁ hrep₁).obj U.unop))) => ?_
  have h1 := transferMap_app B S hS r₁ hrep₁ r₂ hrep₂ h hr θ U.unop
    ((a₁.1 (op ((smallBaseChange B S hS r₁ hrep₁).obj U.unop))) • s)
  have h2 := transferMap_app B S hS r₁ hrep₁ r₂ hrep₂ h hr θ U.unop s
  have h3 := modulePullbackChartSection_smul B S hS h F₁
    (transferChartDiagram B S hS r₁ hrep₁ r₂ hrep₂ h hr U.unop)
    (a₁.1 (op ((smallBaseChange B S hS r₁ hrep₁).obj U.unop))) s
  refine h1.trans ?_
  refine (congrArg (θ.val.app (op ((smallBaseChange B S hS r₂ hrep₂).obj U.unop))) h3).trans ?_
  rw [ha U.unop]
  refine ((θ.val.app (op ((smallBaseChange B S hS r₂ hrep₂).obj U.unop))).hom.map_smul _ _).trans
    ?_
  exact congrArg (fun x => a₂.1 (op ((smallBaseChange B S hS r₂ hrep₂).obj U.unop)) • x) h2.symm

/-! ### Compatibility with the reductions -/

variable {i₁ : X₀ ⟶ X₁} (hi₁ : i₁ ≫ r₁ = 𝟙 X₀) {i₂ : X₀ ⟶ X₂} (hi₂ : i₂ ≫ r₂ = 𝟙 X₀)

/-- The chart map `U ⟶ U ×_{X₀} X₂` followed by the transfer chart map is the chart map
`U ⟶ U ×_{X₀} X₁`. -/
theorem retractionChartMap_comp_transferChartMap (hih : i₂ ≫ h = i₁)
    (U : SmallEtale B S hS X₀.1) :
    retractionChartMap B S hS r₂ hrep₂ i₂ hi₂ U ≫
        transferChartMap B S hS r₁ hrep₁ r₂ hrep₂ h hr U =
      retractionChartMap B S hS r₁ hrep₁ i₁ hi₁ U := by
  apply hrep₁.hom_ext
  · rw [Functor.map_comp, Category.assoc, transferChartMap_fst, ← Category.assoc,
      retractionChartMap_fst, retractionChartMap_fst, Category.assoc,
      show i₂.hom ≫ h.hom = i₁.hom from congrArg (fun f => f.hom) hih]
  · rw [Category.assoc, transferChartMap_snd, retractionChartMap_snd, retractionChartMap_snd]

omit hr in
/-- Chart sections along two chart diagrams with the same charts and equal vertical maps agree. -/
theorem modulePullbackChartSection_mk_congr {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (U : SmallEtale B S hS X.1) (V : SmallEtale B S hS Y.1)
    (g g' : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (hc : U.1.hom ≫ f.hom = yoneda.map g ≫ V.1.hom)
    (hc' : U.1.hom ≫ f.hom = yoneda.map g' ≫ V.1.hom) (hg : g = g') (s : M.val.obj (op V)) :
    modulePullbackChartSection B S hS f M ⟨U, V, g, hc⟩ s =
      modulePullbackChartSection B S hS f M ⟨U, V, g', hc'⟩ s := by
  subst hg
  rfl

/-- **The comparison of Stacks 03LU for `i₂ ≫ h = i₁` carries the chart section along
`U ⟶ U ×_{X₀} X₁` to the chart section along `U ⟶ U ×_{X₀} X₂` of the chart section along the
transfer chart map.** -/
theorem modulePullbackTriangle_hom_app_retractionChartSection (hih : i₂ ≫ h = i₁)
    (U : SmallEtale B S hS X₀.1) (F : Modules.{u, u} B S hS X₁.1 X₁.2)
    (s : F.val.obj (op ((smallBaseChange B S hS r₁ hrep₁).obj U))) :
    ((modulePullbackTriangle B S hS hih).hom.app F).val.app (op U)
        (modulePullbackChartSection B S hS i₁ F (retractionChartDiagram B S hS r₁ hrep₁ i₁ hi₁ U)
          s) =
      modulePullbackChartSection B S hS i₂ ((modulePullback B S hS h).obj F)
        (retractionChartDiagram B S hS r₂ hrep₂ i₂ hi₂ U)
        (modulePullbackChartSection B S hS h F
          (transferChartDiagram B S hS r₁ hrep₁ r₂ hrep₂ h hr U) s) := by
  subst hih
  have hL := modulePullbackCompIso_hom_val_app_modulePullbackUnitSection B S hS i₂ h
    (retractionChartDiagram B S hS r₂ hrep₂ i₂ hi₂ U).g
    (transferChartDiagram B S hS r₁ hrep₁ r₂ hrep₂ h hr U).g
    (retractionChartDiagram B S hS r₂ hrep₂ i₂ hi₂ U).comm
    (transferChartDiagram B S hS r₁ hrep₁ r₂ hrep₂ h hr U).comm F s
  have e1 := modulePullbackUnitSection_eq_modulePullbackChartSection B S hS h F
    (transferChartDiagram B S hS r₁ hrep₁ r₂ hrep₂ h hr U) s
  have e2 := modulePullbackUnitSection_eq_modulePullbackChartSection B S hS i₂
    ((modulePullback B S hS h).obj F) (retractionChartDiagram B S hS r₂ hrep₂ i₂ hi₂ U)
    (modulePullbackChartSection B S hS h F
      (transferChartDiagram B S hS r₁ hrep₁ r₂ hrep₂ h hr U) s)
  have e3 := modulePullbackUnitSection_eq_modulePullbackChartSection B S hS (i₂ ≫ h) F
    (ChartDiagram.comp B S hS i₂ h (retractionChartDiagram B S hS r₂ hrep₂ i₂ hi₂ U).g
      (transferChartDiagram B S hS r₁ hrep₁ r₂ hrep₂ h hr U).g
      (retractionChartDiagram B S hS r₂ hrep₂ i₂ hi₂ U).comm
      (transferChartDiagram B S hS r₁ hrep₁ r₂ hrep₂ h hr U).comm) s
  have e4 := modulePullbackChartSection_mk_congr B S hS (i₂ ≫ h) F U
    ((smallBaseChange B S hS r₁ hrep₁).obj U)
    (retractionChartMap B S hS r₂ hrep₂ i₂ hi₂ U ≫ transferChartMap B S hS r₁ hrep₁ r₂ hrep₂ h hr U)
    (retractionChartMap B S hS r₁ hrep₁ (i₂ ≫ h) hi₁ U)
    (ChartDiagram.comp B S hS i₂ h (retractionChartDiagram B S hS r₂ hrep₂ i₂ hi₂ U).g
      (transferChartDiagram B S hS r₁ hrep₁ r₂ hrep₂ h hr U).g
      (retractionChartDiagram B S hS r₂ hrep₂ i₂ hi₂ U).comm
      (transferChartDiagram B S hS r₁ hrep₁ r₂ hrep₂ h hr U).comm).comm
    (retractionChartDiagram B S hS r₁ hrep₁ (i₂ ≫ h) hi₁ U).comm
    (retractionChartMap_comp_transferChartMap B S hS r₁ hrep₁ r₂ hrep₂ h hr hi₁ hi₂ rfl U) s
  have hL' : ((modulePullbackCompIso B S hS i₂ h).hom.app F).val.app (op U)
      (modulePullbackChartSection B S hS i₂ ((modulePullback B S hS h).obj F)
        (retractionChartDiagram B S hS r₂ hrep₂ i₂ hi₂ U)
        (modulePullbackChartSection B S hS h F
          (transferChartDiagram B S hS r₁ hrep₁ r₂ hrep₂ h hr U) s)) =
      modulePullbackChartSection B S hS (i₂ ≫ h) F
        (retractionChartDiagram B S hS r₁ hrep₁ (i₂ ≫ h) hi₁ U) s := by
    rw [← e2, ← e1]
    exact hL.trans (e3.trans e4)
  rw [modulePullbackTriangle_rfl, ← hL']
  exact congrArg (fun φ : (modulePullback B S hS h ⋙ modulePullback B S hS i₂).obj F ⟶ _ =>
      φ.val.app (op U) _) (Iso.hom_inv_id_app (modulePullbackCompIso B S hS i₂ h) F)

/-- The transfer to `r₂_*(h^*ℱ₁)` followed by the reduction along `i₂` is the reduction along
`i₁` followed by any morphism `τ` acting on chart sections as the comparison of Stacks 03LU
does. -/
theorem transferUnit_comp_reductionMap_of_app (F₁ : Modules.{u, u} B S hS X₁.1 X₁.2)
    (τ : (modulePullback B S hS i₁).obj F₁ ⟶
      (modulePullback B S hS i₂).obj ((modulePullback B S hS h).obj F₁))
    (hτ : ∀ (U : SmallEtale B S hS X₀.1)
      (s : F₁.val.obj (op ((smallBaseChange B S hS r₁ hrep₁).obj U))),
      τ.val.app (op U) (modulePullbackChartSection B S hS i₁ F₁
          (retractionChartDiagram B S hS r₁ hrep₁ i₁ hi₁ U) s) =
        modulePullbackChartSection B S hS i₂ ((modulePullback B S hS h).obj F₁)
          (retractionChartDiagram B S hS r₂ hrep₂ i₂ hi₂ U)
          (modulePullbackChartSection B S hS h F₁
            (transferChartDiagram B S hS r₁ hrep₁ r₂ hrep₂ h hr U) s)) :
    transferUnit B S hS r₁ hrep₁ r₂ hrep₂ h hr F₁ ≫
        reductionMap B S hS r₂ hrep₂ i₂ hi₂ ((modulePullback B S hS h).obj F₁) =
      reductionMap B S hS r₁ hrep₁ i₁ hi₁ F₁ ≫ τ := by
  refine modules_hom_ext B S hS fun U s => ?_
  have h1 := reductionMap_app B S hS r₂ hrep₂ i₂ hi₂ ((modulePullback B S hS h).obj F₁) U.unop
    ((transferUnit B S hS r₁ hrep₁ r₂ hrep₂ h hr F₁).val.app U s)
  have h2 := transferUnit_app B S hS r₁ hrep₁ r₂ hrep₂ h hr F₁ U.unop s
  have h4 := reductionMap_app B S hS r₁ hrep₁ i₁ hi₁ F₁ U.unop s
  have h6 := congrArg (τ.val.app U) h4
  have h7 := congrArg (modulePullbackChartSection B S hS i₂ ((modulePullback B S hS h).obj F₁)
    (retractionChartDiagram B S hS r₂ hrep₂ i₂ hi₂ U.unop)) h2
  exact (h1.trans h7).trans ((hτ U.unop s).symm.trans h6.symm)

/-- **The transfer to `r₂_*(h^*ℱ₁)` is compatible with the reductions**: followed by the
reduction along `i₂` it is the reduction along `i₁` followed by the comparison of Stacks 03LU for
`i₂ ≫ h = i₁`. -/
theorem transferUnit_comp_reductionMap (hih : i₂ ≫ h = i₁) (F₁ : Modules.{u, u} B S hS X₁.1 X₁.2) :
    transferUnit B S hS r₁ hrep₁ r₂ hrep₂ h hr F₁ ≫
        reductionMap B S hS r₂ hrep₂ i₂ hi₂ ((modulePullback B S hS h).obj F₁) =
      reductionMap B S hS r₁ hrep₁ i₁ hi₁ F₁ ≫ (modulePullbackTriangle B S hS hih).hom.app F₁ :=
  transferUnit_comp_reductionMap_of_app B S hS r₁ hrep₁ r₂ hrep₂ h hr hi₁ hi₂ F₁
    ((modulePullbackTriangle B S hS hih).hom.app F₁)
    (fun U s => modulePullbackTriangle_hom_app_retractionChartSection B S hS r₁ hrep₁ r₂ hrep₂ h
      hr hi₁ hi₂ hih U F₁ s)

/-- **The transfer is compatible with the reductions**: followed by the reduction along `i₂` it
is the reduction along `i₁` followed by the comparison of Stacks 03LU for `i₂ ≫ h = i₁` and the
inverse image of `θ` along `i₂`. -/
theorem transferMap_comp_reductionMap (hih : i₂ ≫ h = i₁)
    (θ : (modulePullback B S hS h).obj F₁ ⟶ F₂) :
    transferMap B S hS r₁ hrep₁ r₂ hrep₂ h hr θ ≫ reductionMap B S hS r₂ hrep₂ i₂ hi₂ F₂ =
      reductionMap B S hS r₁ hrep₁ i₁ hi₁ F₁ ≫ (modulePullbackTriangle B S hS hih).hom.app F₁ ≫
        (modulePullback B S hS i₂).map θ := by
  rw [transferMap, Category.assoc, reductionMap_naturality, ← Category.assoc,
    transferUnit_comp_reductionMap B S hS r₁ hrep₁ r₂ hrep₂ h hr hi₁ hi₂ hih, Category.assoc]

end Transfer

end AlgebraicGeometry.Space

end
