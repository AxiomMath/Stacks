module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleAllPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModulePointChartIndependence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapCompDischarge
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealPullback
public import StacksFrontier.RingTheory.MilnorPatching.BaseChangeGlueing
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningStratification.AffineFlatness

/-!
# Sections of modules over a diagram of affine étale charts, as semilinear maps

Sections of inverse and direct images over a diagram of étale charts `d : U ⟶ V` over a
morphism `f : X ⟶ Y` of algebraic spaces, read as maps semilinear over the pullback of regular
functions `𝒪_Y(V) ⟶ 𝒪_X(U)`, and flatness over `Y` read on the sections over such diagrams.

## Main results

* `AlgebraicGeometry.Space.modulePullbackChartSectionₛₗ`,
  `AlgebraicGeometry.Space.modulePushforwardCounitAppₛₗ`: the chart section of an inverse image
  and the chart projection of a direct image, as semilinear maps.
* `AlgebraicGeometry.Space.isBaseChangeAlong_modulePullbackChartSectionₛₗ`: over affine charts
  the sections of the inverse image of a quasi-coherent module are a base change.
* `AlgebraicGeometry.Space.counit_app_modulePullbackChartSection`: the counit of `f^* ⊣ f_*` on
  chart sections.
* `AlgebraicGeometry.Space.flat_sections_of_isFlatOver_chartDiagram`,
  `AlgebraicGeometry.Space.isFlatOver_of_forall_flat_sections`: flatness over `Y` read on the
  sections over affine chart diagrams, in both directions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The chart component of the unit of `f^* ⊣ f_*`, as a map of sections semilinear over the
pullback of regular functions along the vertical morphism of the chart diagram. -/
def modulePullbackChartSectionₛₗ (M : Modules.{u, u} B S hS Y.1 Y.2)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    M.val.obj (op d.V) →ₛₗ[chartDiagramRestrict B S hS f d]
      ((modulePullback B S hS f).obj M).val.obj (op d.U) where
  toFun := modulePullbackChartSection B S hS f M d
  map_add' := modulePullbackChartSection_add B S hS f M d
  map_smul' := modulePullbackChartSection_smul B S hS f M d

/-- The semilinear chart section `modulePullbackChartSectionₛₗ` evaluates as
`modulePullbackChartSection`. -/
theorem modulePullbackChartSectionₛₗ_apply (M : Modules.{u, u} B S hS Y.1 Y.2)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (s : M.val.obj (op d.V)) :
    modulePullbackChartSectionₛₗ B S hS f M d s = modulePullbackChartSection B S hS f M d s :=
  rfl

/-- **Over a diagram of affine charts the sections of the inverse image of a quasi-coherent
module are the base change of the sections.** -/
theorem isBaseChangeAlong_modulePullbackChartSectionₛₗ (M : Modules.{u, u} B S hS Y.1 Y.2)
    (hM : M.IsQuasicoherentOnSite) (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    MilnorPatching.IsBaseChangeAlong (chartDiagramRestrict B S hS f d)
      (modulePullbackChartSectionₛₗ B S hS f M d) :=
  bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS f M hM d hU hV

/-- The chart projection of a direct image, as a map of sections semilinear over the pullback of
regular functions along the vertical morphism of the chart diagram. -/
def modulePushforwardCounitAppₛₗ (F : Modules.{u, u} B S hS X.1 X.2)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    ((modulePushforward B S hS f).obj F).val.obj (op d.V) →ₛₗ[chartDiagramRestrict B S hS f d]
      F.val.obj (op d.U) where
  toFun := modulePushforwardCounitApp B S hS f F d
  map_add' := modulePushforwardCounitApp_add B S hS f F d
  map_smul' := modulePushforwardCounitApp_smul B S hS f F d

/-- The semilinear chart projection `modulePushforwardCounitAppₛₗ` evaluates as
`modulePushforwardCounitApp`. -/
theorem modulePushforwardCounitAppₛₗ_apply (F : Modules.{u, u} B S hS X.1 X.2)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (x : ((modulePushforward B S hS f).obj F).val.obj (op d.V)) :
    modulePushforwardCounitAppₛₗ B S hS f F d x = modulePushforwardCounitApp B S hS f F d x :=
  rfl

/-- **The counit of `f^* ⊣ f_*` on a chart section is the chart projection**: for a section `y`
of `f_*N` over the chart of `Y`, the counit `f^*f_*N ⟶ N` carries the chart section of `y` to the
chart projection of `y`. -/
theorem counit_app_modulePullbackChartSection (N : Modules.{u, u} B S hS X.1 X.2)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (y : ((modulePushforward B S hS f).obj N).val.obj (op d.V)) :
    ((modulePullbackAdjunction B S hS f).counit.app N).val.app (op d.U)
        (modulePullbackChartSection B S hS f ((modulePushforward B S hS f).obj N) d y) =
      modulePushforwardCounitApp B S hS f N d y := by
  rw [← modulePullbackUnitSection_eq_modulePullbackChartSection]
  change ((modulePullbackAdjunction B S hS f).counit.app N).val.app (op d.U)
      (modulePushforwardCounitApp B S hS f _ d
        (((modulePullbackAdjunction B S hS f).unit.app _).val.app (op d.V) y)) = _
  rw [← modulePushforwardCounitApp_map]
  congr 1
  exact congrArg (fun φ => φ.val.app (op d.V) y)
    ((modulePullbackAdjunction B S hS f).right_triangle_components N)

/-! ### Flatness over the target, read on the sections over affine chart diagrams -/

/-- Flatness of the chart restriction over the chart of the target is flatness of the sections
over the regular functions on the chart of the target. -/
private theorem isFlatOver_chartRestrictionSheaf_iff_flat_sections
    (G : Modules.{u, u} B S hS X.1 X.2) (hG : G.IsQuasicoherentOnSite)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    AlgebraicGeometry.IsFlatOver ((BigFppfOver.toScheme B S hS).map d.g).toLRSHom.toShHom
        (chartRestrictionSheaf B S hS X G d.U) ↔
      @Module.Flat (chartRing B S hS Y.1 Y.2 d.V) (G.val.obj (op d.U)) _ _
        (Module.compHom _ (chartDiagramRestrict B S hS f d)) := by
  have : IsAffine (chartScheme d.U) := hU
  have : IsAffine (chartScheme d.V) := hV
  have : SheafOfModules.IsQuasicoherent (chartRestrictionSheaf B S hS X G d.U) :=
    isQuasicoherent_chartRestrictionSheaf B S hS X G hG d.U
  let φ : chartScheme d.U ⟶ chartScheme d.V := (BigFppfOver.toScheme B S hS).map d.g
  let : Module Γ(chartScheme d.V, ⊤) (G.val.obj (op d.U)) := Module.compHom _ φ.appTop.hom
  let : Module Γ(chartScheme d.V, ⊤) Γ(chartRestrictionSheaf B S hS X G d.U, ⊤) :=
    Module.compHom _ φ.appTop.hom
  refine (AlgebraicGeometry.isFlatOver_iff_flat_sections φ
    (chartRestrictionSheaf B S hS X G d.U)).trans ?_
  change _ ↔ @Module.Flat Γ(chartScheme d.V, ⊤) (G.val.obj (op d.U)) _ _
    (Module.compHom _ φ.appTop.hom)
  exact ⟨fun h => Module.Flat.of_semilinearEquiv (RingEquiv.refl _)
      (chartRestrictionSheafTopEquiv B S hS X G d.U).toAddEquiv
      fun a m => (chartRestrictionSheafTopEquiv B S hS X G d.U).map_smul (φ.appTop.hom a) m,
    fun h => Module.Flat.of_semilinearEquiv (RingEquiv.refl _)
      (chartRestrictionSheafTopEquiv B S hS X G d.U).symm.toAddEquiv
      fun a m => (chartRestrictionSheafTopEquiv B S hS X G d.U).symm.map_smul (φ.appTop.hom a) m⟩

/-- **The sections of a quasi-coherent module flat over the target, over a diagram of affine étale
charts, are flat over the regular functions on the chart of the target.** -/
theorem flat_sections_of_isFlatOver_chartDiagram (G : Modules.{u, u} B S hS X.1 X.2)
    (hG : G.IsQuasicoherentOnSite) (hflat : IsFlatOver B S hS X.2 f.hom G)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    @Module.Flat (chartRing B S hS Y.1 Y.2 d.V) (G.val.obj (op d.U)) _ _
      (Module.compHom _ (chartDiagramRestrict B S hS f d)) :=
  (isFlatOver_chartRestrictionSheaf_iff_flat_sections B S hS f G hG d hU hV).1
    ((AlgebraicGeometry.isFlatOver_iff_of_moduleIso _
      (restrictToChartIsoChartRestrictionSheaf B S hS X G d.U)).1 (hflat d))

/-- **Flatness over the target is detected on affine chart diagrams through every point.**  A
quasi-coherent module is flat over the target as soon as every point of the source lies on the
chart of `X` of some diagram of affine étale charts over which its sections are flat over the
regular functions on the chart of `Y`. -/
theorem isFlatOver_of_forall_flat_sections (G : Modules.{u, u} B S hS X.1 X.2)
    (hG : G.IsQuasicoherentOnSite)
    (H : ∀ x : points B S hS X.1, ∃ (d : ChartDiagram B S hS X.1 Y.1 f.hom)
      (_ : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
      (_ : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V))
      (u : etaleChartScheme B S hS d.U), pointOfEtaleChart B S hS d.U u = x ∧
        @Module.Flat (chartRing B S hS Y.1 Y.2 d.V) (G.val.obj (op d.U)) _ _
          (Module.compHom _ (chartDiagramRestrict B S hS f d))) :
    IsFlatOver B S hS X.2 f.hom G := by
  refine isFlatOver_of_forall_isFlatOverAtPoint B S hS f G hG fun x => ?_
  obtain ⟨d, hU, hV, u, rfl, hfl⟩ := H x
  refine (isFlatOverAtPoint_iff_isFlatOverAtOnChartDiagram B S hS f G hG d u).mpr ?_
  exact (AlgebraicGeometry.isFlatOver_iff_of_moduleIso _
    (restrictToChartIsoChartRestrictionSheaf B S hS X G d.U)).2
    ((isFlatOver_chartRestrictionSheaf_iff_flat_sections B S hS f G hG d hU hV).2 hfl) u

end AlgebraicGeometry.Space

end
