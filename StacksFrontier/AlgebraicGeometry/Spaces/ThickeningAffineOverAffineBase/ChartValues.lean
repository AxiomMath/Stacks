module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GlobalFunctionsAtlas

/-!
# Values of global regular functions on scheme charts

A global regular function on an algebraic space `X` restricts to a regular function on every
scheme chart `v : h_V ⟶ X`, compatibly with morphisms of charts and with pullback of global
functions.  On a represented algebraic space `h_V` every regular function on `V` is such a
restriction.

## Main definitions

* `AlgebraicGeometry.Space.globalChartValue`: the value of a global function on a scheme chart.
* `AlgebraicGeometry.Space.representableGlobalFunction`: the global function on `h_V` attached to a
  regular function on `V`.

## Main results

* `AlgebraicGeometry.Space.globalChartValue_comp`: chart values are compatible with morphisms of
  charts.
* `AlgebraicGeometry.Space.globalChartValue_globalFunctionsMap`: the chart value of a pulled-back
  global function is the chart value along the composite chart.
* `AlgebraicGeometry.Space.globalChartValue_representableFunction`: the chart values of
  `representableGlobalFunction V c` are the pullbacks of `c`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The value of a global regular function on a scheme chart. -/
def globalChartValue {X : AlgebraicSpaces B S hS} (f : globalFunctions' B S hS X.1)
    {V : BigFppfOver B S hS} (v : yoneda.obj V ⟶ X.1) :
    Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
  ((globalFunctionsChartEquiv B S hS X).val f).val (op (CostructuredArrow.mk v))

/-- The value of a global function on the chart `yoneda.map a ≫ v` is the pullback along `a` of
its value on the chart `v`. -/
theorem globalChartValue_comp {X : AlgebraicSpaces B S hS} (f : globalFunctions' B S hS X.1)
    {V V' : BigFppfOver B S hS} (a : V' ⟶ V) (v : yoneda.obj V ⟶ X.1) :
    globalChartValue B S hS f (yoneda.map a ≫ v) =
      ((BigFppfOver.toScheme B S hS).map a).appTop (globalChartValue B S hS f v) :=
  (((globalFunctionsChartEquiv B S hS X).val f).property
    (CostructuredArrow.homMk a rfl : CostructuredArrow.mk (yoneda.map a ≫ v) ⟶
      CostructuredArrow.mk v).op).symm

/-- Equal charts give equal values of a global function. -/
theorem globalChartValue_congr {X : AlgebraicSpaces B S hS} (f : globalFunctions' B S hS X.1)
    {V : BigFppfOver B S hS} {v v' : yoneda.obj V ⟶ X.1} (h : v = v') :
    globalChartValue B S hS f v = globalChartValue B S hS f v' := by
  subst h; rfl

/-- The value of the pullback of `f` along `g : Y ⟶ X` on a chart `v` of `Y` is the value of `f`
on the chart `v ≫ g.hom` of `X`. -/
theorem globalChartValue_globalFunctionsMap {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X)
    (f : globalFunctions' B S hS X.1) {V : BigFppfOver B S hS} (v : yoneda.obj V ⟶ Y.1) :
    globalChartValue B S hS (globalFunctionsMap B S hS g f) v =
      globalChartValue B S hS f (v ≫ g.hom) := by
  unfold globalChartValue
  rw [globalFunctionsMap_chart]
  rfl

/-- The global function on a represented algebraic space attached to a regular function. -/
def representableGlobalFunction (V : BigFppfOver B S hS)
    (c : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    globalFunctions' B S hS (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ :
      AlgebraicSpaces B S hS).1 :=
  (globalFunctionsChartEquiv B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩).val.symm
    ⟨fun j ↦ ((BigFppfOver.toScheme B S hS).map (yoneda.preimage j.unop.hom)).appTop c,
      fun {j k} φ ↦ by
        have hφ : yoneda.preimage k.unop.hom =
            φ.unop.left ≫ yoneda.preimage j.unop.hom := yoneda.map_injective <| by
          rw [Functor.map_comp, Functor.map_preimage, Functor.map_preimage]
          exact (CostructuredArrow.w φ.unop).symm
        change ((BigFppfOver.toScheme B S hS).map φ.unop.left).appTop
          (((BigFppfOver.toScheme B S hS).map (yoneda.preimage j.unop.hom)).appTop c) =
          ((BigFppfOver.toScheme B S hS).map (yoneda.preimage k.unop.hom)).appTop c
        rw [hφ, Functor.map_comp, Scheme.Hom.comp_appTop]
        rfl⟩

/-- The value of `representableGlobalFunction V c` on a chart `v : h_V' ⟶ h_V` is the pullback of
`c` along the morphism `V' ⟶ V` corresponding to `v`. -/
theorem globalChartValue_representableFunction (V : BigFppfOver B S hS)
    (c : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) {V' : BigFppfOver B S hS}
    (v : yoneda.obj V' ⟶ yoneda.obj V) :
    globalChartValue B S hS (X := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
      (representableGlobalFunction B S hS V c) v =
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage v)).appTop c := by
  unfold globalChartValue representableGlobalFunction
  rw [RingEquiv.apply_symm_apply]
  rfl

end AlgebraicGeometry.Space

end
