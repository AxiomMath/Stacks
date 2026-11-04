module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModule
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictToChartSchemeSectionsTransport
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.QuasicoherentCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartCechVanishingUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts

/-!
# The structure sheaf read on the sections over a chart

Two readings of morphisms out of the structure sheaf of an algebraic space on the sections over a
single étale chart, in the shape the counterexample to Stacks 082Q as written consumes them.

## Main results

* `AlgebraicGeometry.Space.eq_zero_of_unit_app_one_eq_zero`: a morphism out of the structure
  sheaf is zero once it kills `1` over a chart to which every chart maps.
* `AlgebraicGeometry.Space.one_eq_zero_of_isZero_unit`: the functions on every chart vanish when
  the structure sheaf is zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

/-- **A morphism out of the structure sheaf vanishes once it kills `1` over a chart to which every
chart maps.** -/
theorem eq_zero_of_unit_app_one_eq_zero {X : AlgebraicSpaces B S hS}
    {Q : Modules.{u, u} B S hS X.1 X.2}
    (q : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O) ⟶ Q)
    (U : SmallEtale B S hS X.1) (hU : ∀ V : SmallEtale B S hS X.1, Nonempty (V ⟶ U))
    (h : q.val.app (op U) (1 : chartRing B S hS X.1 X.2 U) = 0) : q = 0 := by
  refine SheafOfModules.hom_ext ?_
  refine PresheafOfModules.hom_ext fun V => ?_
  obtain ⟨i⟩ := hU V.unop
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  have h1 : q.val.app V (1 : chartRing B S hS X.1 X.2 V.unop) = 0 := by
    have := PresheafOfModules.naturality_apply q.val i.op (1 : chartRing B S hS X.1 X.2 U)
    have h0 : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)).val.map i.op
          (1 : chartRing B S hS X.1 X.2 U) = (1 : chartRing B S hS X.1 X.2 V.unop) :=
      PresheafOfModules.unit_map_one _ _
    rw [h0] at this
    exact this.trans ((congrArg (Q.val.map i.op).hom h).trans (map_zero _))
  have key : ∀ x' : chartRing B S hS X.1 X.2 V.unop, q.val.app V x' = 0 := fun x' =>
    calc (q.val.app V).hom x' = (q.val.app V).hom (x' • (1 : chartRing B S hS X.1 X.2 V.unop)) :=
          congrArg _ (mul_one x').symm
      _ = x' • (q.val.app V).hom (1 : chartRing B S hS X.1 X.2 V.unop) :=
          (q.val.app V).hom.map_smul x' _
      _ = x' • 0 := congrArg _ h1
      _ = 0 := smul_zero _
  exact key x

/-- **The functions on every chart vanish when the structure sheaf is zero.** -/
theorem one_eq_zero_of_isZero_unit {X : AlgebraicSpaces B S hS} (U : SmallEtale B S hS X.1)
    (hz : IsZero (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O))) :
    (1 : chartRing B S hS X.1 X.2 U) = 0 := by
  have h := congrArg (fun f => (SheafOfModules.Hom.val f).app (op U)
    (1 : chartRing B S hS X.1 X.2 U)) (hz.eq_of_src (𝟙 _) 0)
  exact h

end AlgebraicGeometry.Space
