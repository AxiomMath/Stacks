module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCofinal
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModulePointChartIndependence
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFiniteTypeModuleFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange

/-!
# Flatness of a module over the target on an affine chart diagram, read on the sections

The declarations of this file are independent of the module
`StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleChartDiagramSections`,
which treats related material in its own terms.

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `d` a commuting square of étale scheme
charts over `f` whose two charts are affine.  For a quasi-coherent `𝒪_X`-module `M`, the condition
of Stacks 05VV on `d` — the restriction of `M` to the chart of `X` is flat over the chart of `Y`,
stalkwise in the sense of Stacks 08KT — holds if and only if the sections of `M` over the chart
of `X` form a flat module over the global functions on the chart of `Y`.

This is `AlgebraicGeometry.isFlatOver_iff_flat_sections` for the restriction of `M` to the chart,
whose sections over the whole chart are the sections of `M` over the chart; it is the form of
`AlgebraicGeometry.Space.flat_sections_of_isFlatOver` for an arbitrary square instead of the
square over the base, and with the converse.

Flatness over the target may moreover be tested on the affine chart diagrams alone, for a
quasi-coherent module: flatness at a point of a chart is flatness at the point of `|X|` beneath
it, which does not depend on the chart (Stacks 05VU), and every point of a chart lies in an
affine open whose image lies in an affine open.

## Main results

* `AlgebraicGeometry.Space.isFlatOverOnChartDiagram_iff_flat_sections`: the equivalence.
* `AlgebraicGeometry.Space.isFlatOver_of_forall_isAffine_chartDiagram`: flatness over the target
  from the affine chart diagrams.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

/-- **Flatness on an affine chart diagram is flatness of the sections.**  For a quasi-coherent
`𝒪_X`-module `M` and a commuting square `d` of étale scheme charts over `f` whose charts are
affine, `M` is flat over `Y` on `d` exactly when `M(d.U)` is a flat module over `Γ(d.V)`, the
scalars acting through the pullback of functions along the vertical morphism of `d`. -/
theorem isFlatOverOnChartDiagram_iff_flat_sections (f : X ⟶ Y)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (hU : IsAffine (chartScheme d.U))
    (hV : IsAffine (chartScheme d.V)) :
    IsFlatOverOnChartDiagram B S hS X.2 M d ↔
      letI : Module Γ(chartScheme d.V, ⊤) (M.val.obj (op d.U)) :=
        Module.compHom _ ((BigFppfOver.toScheme B S hS).map d.g).appTop.hom
      Module.Flat Γ(chartScheme d.V, ⊤) (M.val.obj (op d.U)) := by
  have : SheafOfModules.IsQuasicoherent (chartRestrictionSheaf B S hS X M d.U) :=
    isQuasicoherent_chartRestrictionSheaf B S hS X M hM d.U
  let φ : chartScheme d.U ⟶ chartScheme d.V := (BigFppfOver.toScheme B S hS).map d.g
  have h1 : IsFlatOverOnChartDiagram B S hS X.2 M d ↔
      AlgebraicGeometry.IsFlatOver φ.toLRSHom.toShHom (chartRestrictionSheaf B S hS X M d.U) :=
    AlgebraicGeometry.isFlatOver_iff_of_moduleIso _
      (restrictToChartIsoChartRestrictionSheaf B S hS X M d.U)
  let : Module Γ(chartScheme d.V, ⊤) Γ(chartRestrictionSheaf B S hS X M d.U, ⊤) :=
    Module.compHom _ φ.appTop.hom
  let : Module Γ(chartScheme d.V, ⊤) (M.val.obj (op d.U)) := Module.compHom _ φ.appTop.hom
  let e : (M.val.obj (op d.U) : Type u) ≃+
      (Γ(chartRestrictionSheaf B S hS X M d.U, ⊤) : Type u) :=
    (M.val.presheaf.mapIso
        (asIso (chartOpensTopHom B S hS X d.U)).op).addCommGroupIsoToAddEquiv.trans
      AddEquiv.ulift.symm
  have he : ∀ (a : Γ(chartScheme d.V, ⊤)) (m : M.val.obj (op d.U)), e (a • m) = a • e m :=
    fun a m => congrArg ULift.up (M.val.map_smul (chartOpensTopHom B S hS X d.U).op _ m)
  have he' : ∀ (a : Γ(chartScheme d.V, ⊤)) (y : Γ(chartRestrictionSheaf B S hS X M d.U, ⊤)),
      e.symm (a • y) = a • e.symm y := fun a y =>
    e.injective ((e.apply_symm_apply _).trans
      ((congrArg (a • ·) (e.apply_symm_apply y)).symm.trans (he a (e.symm y)).symm))
  refine h1.trans ((AlgebraicGeometry.isFlatOver_iff_flat_sections φ
    (chartRestrictionSheaf B S hS X M d.U)).trans ⟨fun h => ?_, fun h => ?_⟩)
  · have : Module.Flat Γ(chartScheme d.V, ⊤) Γ(chartRestrictionSheaf B S hS X M d.U, ⊤) := h
    exact Module.Flat.of_semilinearEquiv (RingEquiv.refl Γ(chartScheme d.V, ⊤)) e he
  · have : Module.Flat Γ(chartScheme d.V, ⊤) (M.val.obj (op d.U)) := h
    exact Module.Flat.of_semilinearEquiv (RingEquiv.refl Γ(chartScheme d.V, ⊤)) e.symm he'

/-- The point of `|X|` beneath a point of an open of an étale chart is the point beneath its
image in the chart. -/
theorem pointOfEtaleChart_openChart {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (U : SmallEtale B S hS Z)
    (O : ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Z).obj U)).Opens)
    (u : etaleChartScheme B S hS (openChart B S hS Z U O)) :
    pointOfEtaleChart B S hS (openChart B S hS Z U O) u =
      pointOfEtaleChart B S hS U ((BigFppfOver.toScheme B S hS).map (openSubHom _ O) u) := by
  refine (pointsMap_comp_apply B S hS (yoneda.map (openSubHom _ O)) U.1.hom _).trans ?_
  exact congrArg (pointsMap B S hS _ U.1.hom) (pointsMap_yoneda_map_symm B S hS _ u)

/-- **Flatness over the target is tested on the affine chart diagrams**, for a quasi-coherent
module. -/
theorem isFlatOver_of_forall_isAffine_chartDiagram (f : X ⟶ Y)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (h : ∀ d : ChartDiagram B S hS X.1 Y.1 f.hom, IsAffine (chartScheme d.U) →
      IsAffine (chartScheme d.V) → IsFlatOverOnChartDiagram B S hS X.2 M d) :
    IsFlatOver B S hS X.2 f.hom M := by
  intro d u
  refine (isFlatOverAtPoint_iff_isFlatOverAtOnChartDiagram B S hS f M hM d u).mp ?_
  obtain ⟨P, hP, hvP, -⟩ := exists_isAffineOpen_mem_and_subset
    (show (BigFppfOver.toScheme B S hS).map d.g u ∈ (⊤ : _) from trivial)
  obtain ⟨O, hO, huO, hsub⟩ := exists_isAffineOpen_mem_and_subset
    (show u ∈ (BigFppfOver.toScheme B S hS).map d.g ⁻¹ᵁ P from hvP)
  obtain ⟨y, hy⟩ := (Scheme.Opens.range_ι (X := (BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS X.1).obj d.U)) O).ge huO
  have hO' : IsAffine (chartScheme (d.restrictOpens O P hsub).U) := hO
  have hP' : IsAffine (chartScheme (d.restrictOpens O P hsub).V) := hP
  have hflat := (isFlatOverAtPoint_iff_isFlatOverAtOnChartDiagram B S hS f M hM
    (d.restrictOpens O P hsub) y).mpr (h _ hO' hP' y)
  have hpt : pointOfEtaleChart B S hS (d.restrictOpens O P hsub).U y =
      pointOfEtaleChart B S hS d.U u := by
    refine (pointOfEtaleChart_openChart B S hS d.U O y).trans ?_
    rw [toScheme_map_openSubHom]
    exact congrArg (pointOfEtaleChart B S hS d.U) hy
  rwa [hpt] at hflat

end AlgebraicGeometry.Space

end
