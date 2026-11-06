module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitEndomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionChartValue
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionGenerators
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge

/-!
# Pullback of modules along a morphism of algebraic spaces, on global functions

Let `h : X' ⟶ X` be a morphism of algebraic spaces and let `T`, `T'` be terminal étale charts of
`X` and `X'` (for instance the identity charts of representable spaces) with a commutative
diagram `d` of charts over `h`. An endomorphism of the structure sheaf `𝒪_X` is multiplication
by a global function `a`; its pullback `h^*a`, read through the identification
`h^*𝒪_X ≅ 𝒪_{X'}`, is multiplication by the pullback of `a` along the morphism of schemes of the
diagram. In the language of `CategoryTheory.baseChangeRingHom`: the ring map
`𝒪_X(T) → 𝒪_{X'}(T')` induced by `h^*` is pullback of regular functions.

## Main results

* `AlgebraicGeometry.Space.baseChangeRingHom_modulePullback`: the ring map induced by `h^*` on
  endomorphisms of the structure sheaves is `AlgebraicGeometry.Space.chartDiagramPullback`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X X' : AlgebraicSpaces B S hS} (h : X' ⟶ X)

/-- **The ring map induced by the pullback of modules on the endomorphisms of the structure
sheaves is pullback of regular functions**, at terminal charts related by a chart diagram. -/
theorem baseChangeRingHom_modulePullback (d : ChartDiagram B S hS X'.1 X.1 h.hom)
    (hT : IsTerminal d.V) (hT' : IsTerminal d.U)
    (a : (structureSheaf B S hS X.1 X.2).obj.obj (op d.V)) :
    baseChangeRingHom.{u} (C := Modules.{u, u} B S hS X.1 X.2)
      (D := Modules.{u, u} B S hS X'.1 X'.2)
      (R := (structureSheaf B S hS X.1 X.2).obj.obj (op d.V))
      (R' := (structureSheaf B S hS X'.1 X'.2).obj.obj (op d.U))
      (ρ := Stacks.SheafOfModules.unitEndRingHom.{u} (structureSheaf B S hS X.1 X.2) hT)
      (Stacks.SheafOfModules.unitEndRingHom.{u} (structureSheaf B S hS X'.1 X'.2) hT')
      (Stacks.SheafOfModules.bijective_unitEndRingHom.{u} (structureSheaf B S hS X'.1 X'.2) hT')
      (modulePullback B S hS h) (hF := modulePullback_additive h)
      (modulePullbackUnitIso B S hS h) a =
      chartDiagramPullback B S hS h d a := by
  -- the unit section of `h^*` is semilinear over pullback of regular functions
  have hsmul : ∀ (M : Modules.{u, u} B S hS X.1 X.2)
      (r : ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)).obj.obj (op d.V))
      (s : M.val.obj (op d.V)),
      modulePullbackChartSection B S hS h M d (r • s) =
        chartDiagramPullback B S hS h d r • modulePullbackChartSection B S hS h M d s := by
    intro M r s
    rw [← modulePullbackUnitSection_eq_modulePullbackChartSection,
      ← modulePullbackUnitSection_eq_modulePullbackChartSection]
    have key := (modulePullbackHomFMap B S hS h M _ (𝟙 _)).map_smul d r s
    rw [modulePullbackHomFMap_app, modulePullbackHomFMap_app] at key
    exact key
  let e := modulePullbackUnitIso B S hS h
  let ρ := Stacks.SheafOfModules.unitEndRingHom.{u} (structureSheaf B S hS X.1 X.2) hT
  have key : (e.inv ≫ (modulePullback B S hS h).map (ρ a).asHom ≫ e.hom).val.app (op d.U)
      (1 : (structureRingSheaf B S hS X').obj.obj (op d.U)) =
        chartDiagramPullback B S hS h d a := by
    have h1 := comp_val_app_apply B S hS e.inv
      ((modulePullback B S hS h).map (ρ a).asHom ≫ e.hom)
      (op d.U) (1 : (structureRingSheaf B S hS X').obj.obj (op d.U))
    have h2 := comp_val_app_apply B S hS ((modulePullback B S hS h).map (ρ a).asHom) e.hom
      (op d.U)
      (e.inv.val.app (op d.U) (1 : (structureRingSheaf B S hS X').obj.obj (op d.U)))
    have h3 := modulePullbackUnitIso_inv_val_app_one B S hS h d
    have h4 := modulePullbackChartSection_map B S hS h _ (ρ a).asHom d
      (1 : (structureRingSheaf B S hS X).obj.obj (op d.V))
    have hρa : (ρ a).asHom.val.app (op d.V) (1 : (structureRingSheaf B S hS X).obj.obj (op d.V)) =
        (show (structureRingSheaf B S hS X).obj.obj (op d.V) from a) := by
      have := Stacks.SheafOfModules.unit_app_eq.{u} (structureSheaf B S hS X.1 X.2) (T := d.V)
        (ρ a) 1
      exact this.trans ((one_mul _).trans
        ((Stacks.SheafOfModules.unitEndRingEquiv.{u} _ hT).apply_symm_apply a))
    have h5 : modulePullbackChartSection B S hS h
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O))) d
        (show (structureRingSheaf B S hS X).obj.obj (op d.V) from a) =
          chartDiagramPullback B S hS h d a • modulePullbackChartSection B S hS h
            (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS X.1 X.2).O))) d
            (1 : (structureRingSheaf B S hS X).obj.obj (op d.V)) := by
      -- the unit section of `h^*` is semilinear over pullback of regular functions
      have := hsmul
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O))) a
        (1 : (structureRingSheaf B S hS X).obj.obj (op d.V))
      exact (congrArg (modulePullbackChartSection B S hS h
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O))) d)
          (mul_one (show (structureRingSheaf B S hS X).obj.obj (op d.V) from a)).symm).trans this
    have h6 := (e.hom.val.app (op d.U)).hom.map_smul (chartDiagramPullback B S hS h d a)
      (e.inv.val.app (op d.U) (1 : (structureRingSheaf B S hS X').obj.obj (op d.U)))
    have h7 : e.hom.val.app (op d.U) (e.inv.val.app (op d.U)
        (1 : (structureRingSheaf B S hS X').obj.obj (op d.U))) =
          (1 : (structureRingSheaf B S hS X').obj.obj (op d.U)) :=
      (comp_val_app_apply B S hS e.inv e.hom (op d.U) _).symm.trans
        (congrArg
          (fun m => m.val.app (op d.U) (1 : (structureRingSheaf B S hS X').obj.obj (op d.U)))
          e.inv_hom_id)
    refine h1.trans (h2.trans ?_)
    refine (congrArg (fun x => e.hom.val.app (op d.U)
      (((modulePullback B S hS h).map (ρ a).asHom).val.app (op d.U) x)) h3).trans ?_
    refine (congrArg (fun x => e.hom.val.app (op d.U) x) h4).trans ?_
    refine (congrArg (fun x => e.hom.val.app (op d.U) (modulePullbackChartSection B S hS h
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O))) d x))
      hρa).trans ?_
    refine (congrArg (fun x => e.hom.val.app (op d.U) x) h5).trans ?_
    refine (congrArg (fun x => e.hom.val.app (op d.U) (chartDiagramPullback B S hS h d a • x))
      h3.symm).trans ?_
    refine h6.trans ?_
    refine (congrArg (fun x => chartDiagramPullback B S hS h d a • x) h7).trans ?_
    exact mul_one (show (structureRingSheaf B S hS X').obj.obj (op d.U) from
      chartDiagramPullback B S hS h d a)
  have hm := map_baseChangeRingHom.{u} (C := Modules.{u, u} B S hS X.1 X.2)
    (D := Modules.{u, u} B S hS X'.1 X'.2)
    (R := (structureSheaf B S hS X.1 X.2).obj.obj (op d.V))
    (R' := (structureSheaf B S hS X'.1 X'.2).obj.obj (op d.U)) (ρ := ρ)
    (Stacks.SheafOfModules.unitEndRingHom.{u} (structureSheaf B S hS X'.1 X'.2) hT')
    (Stacks.SheafOfModules.bijective_unitEndRingHom.{u} (structureSheaf B S hS X'.1 X'.2) hT')
    (modulePullback B S hS h) (hF := modulePullback_additive h) e a
  exact ((Stacks.SheafOfModules.unitEndRingEquiv.{u} (structureSheaf B S hS X'.1 X'.2)
    hT').apply_symm_apply _).symm.trans ((congrArg (Stacks.SheafOfModules.unitEndRingEquiv.{u}
      (structureSheaf B S hS X'.1 X'.2) hT') (End.ext (y := End.of _) hm)).trans key)

end AlgebraicGeometry.Space

end
