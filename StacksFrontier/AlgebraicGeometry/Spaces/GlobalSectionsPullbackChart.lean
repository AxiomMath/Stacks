module

public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsSquareComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionChartValue

/-!
# The pullback of a global section, on a chart

For a morphism `g : Y' ⟶ Y` of algebraic spaces and an `𝒪_Y`-module `M`, a global section `s` of
`M` pulls back to a global section of `g^*M`: the global section of `g_*g^*M` that is the unit of
the adjunction of **Stacks 03LU** applied to `s`, read on `Y'` through the comparison of global
sections of **Stacks 0732**.  This file computes its value on an étale chart of `Y'`: over a
commutative diagram of étale scheme charts `V' ⟶ V` above `g`, it is the chart section
`AlgebraicGeometry.Space.modulePullbackChartSection` of the value of `s` on `V`.

## Main results

* `AlgebraicGeometry.Space.pushforwardTerminalHomEquiv_hom_app_chart`: the geometric comparison of
  global sections of a direct image, on a chart, is the chart projection of the direct image.
* `AlgebraicGeometry.Space.modulePullbackGlobalSection_val_chartDiagram`: **the pullback of a
  global section, on a chart diagram, is the chart section of its value.**

## References

* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Cohomology.SiteModules (globalSectionsFunctor)
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Sheaves.RingedToposModules (pullbackAdjPushforwardModules)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : AlgebraicSpaces B S hS}

/-- **The geometric comparison of global sections of a direct image, on a chart.**  For a global
section `t` of `f_*E`, the global section of `E` it corresponds to takes, on a chart of `X` above
the base change of a chart `V` of `Y`, the value of the chart projection of `t` on `V`. -/
theorem pushforwardTerminalHomEquiv_hom_app_chart (f : X ⟶ Y)
    (E : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (t : ⊤_ (Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) ⟶
      (smallEtaleDirectImage B S hS f).obj E)
    (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op) :
    ((smallEtaleRingedToposModulesHom B S hS f).toToposHom.pushforwardTerminalHomEquiv E t).hom.app
        j.right (terminalSheafSection (SmallEtale.topology B S hS X.1) j.right) =
      (moduleChartProjection B S hS f V j).app E
        (t.hom.app (op V) (terminalSheafSection (SmallEtale.topology B S hS Y.1) (op V))) := by
  set k := (smallEtaleRingedToposModulesHom B S hS f).toToposHom.pushforwardTerminalHomEquiv E t
  have ht : t = (((smallEtaleRingedToposModulesHom B S hS f).toToposHom.pushforwardTerminalHomEquiv
        (⊤_ (Sheaf (SmallEtale.topology B S hS X.1) (Type u)))).symm (𝟙 _)) ≫
      (smallEtaleRingedToposModulesHom B S hS f).toToposHom.pushforward.map k :=
    (Equiv.symm_apply_apply
      ((smallEtaleRingedToposModulesHom B S hS f).toToposHom.pushforwardTerminalHomEquiv E)
        t).symm.trans
      (MorphismOfTopoi.pushforwardTerminalHomEquiv_symm_eq
        (smallEtaleRingedToposModulesHom B S hS f).toToposHom E k _)
  rw [ht]
  refine Eq.trans ?_ (NatTrans.naturality_apply (moduleChartProjection B S hS f V j) k _).symm
  exact congrArg (k.hom.app j.right) (eq_terminalSheafSection _).symm

/-- The unit of the adjunction of **Stacks 03LU** is, on sections, the unit of the adjunction of
**Stacks 03D7** for the small étale ringed topoi: the two differ by the comparison of the two
spellings of the direct image, which is the identity on sections. -/
theorem modulePullbackAdjunction_unit_app_val_app (g : X ⟶ Y)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (V : (SmallEtale B S hS Y.1)ᵒᵖ) (x : M.val.obj V) :
    ((modulePullbackAdjunction B S hS g).unit.app M).val.app V x =
      ((pullbackAdjPushforwardModules
        (smallEtaleRingedToposModulesHom B S hS g)).unit.app M).val.app V x := by
  have h : (modulePullbackAdjunction B S hS g).unit.app M =
      (pullbackAdjPushforwardModules (smallEtaleRingedToposModulesHom B S hS g)).unit.app M ≫
        (modulePushforwardIso B S hS g).hom.app ((modulePullback B S hS g).obj M) := by
    have h₁ := (modulePullbackAdjunction B S hS g).homEquiv_id M
    have h₂ := Adjunction.homEquiv_ofNatIsoRight_apply
      (pullbackAdjPushforwardModules (smallEtaleRingedToposModulesHom B S hS g))
      (modulePushforwardIso B S hS g) (𝟙 ((modulePullback B S hS g).obj M))
    have h₃ := (pullbackAdjPushforwardModules
      (smallEtaleRingedToposModulesHom B S hS g)).homEquiv_id M
    exact h₁.symm.trans (h₂.trans (congrArg (· ≫ _) h₃))
  exact (congrArg (fun φ : M ⟶ (modulePushforward B S hS g).obj ((modulePullback B S hS g).obj M) ↦
      φ.val.app V x) h).trans
    ((comp_val_app_apply B S hS _ _ V x).trans
      (modulePushforwardIso_hom_app_val_app B S hS g _ V _))

/-- **The pullback of a global section, on a chart diagram, is the chart section of its value.**
For a morphism `g : X ⟶ Y` of algebraic spaces, an `𝒪_Y`-module `M` and a global section `s` of
`M`, the global section of `g^*M` obtained from the unit of **Stacks 03LU** and the comparison of
global sections of **Stacks 0732** takes, on the chart `d.U` of a chart diagram `d` above `g`, the
value `AlgebraicGeometry.Space.modulePullbackChartSection` of the value of `s` on `d.V`. -/
theorem modulePullbackGlobalSection_val_chartDiagram (g : X ⟶ Y)
    (M : Modules.{u, u} B S hS Y.1 Y.2)
    (s : (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj M)
    (d : ChartDiagram B S hS X.1 Y.1 g.hom) :
    (((globalSectionsPushforwardIsoSite B S hS g).hom.app
        ((modulePullback B S hS g).obj M)).hom
      (((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).map
          ((modulePullbackAdjunction B S hS g).unit.app M)).hom s)).val (op d.U) =
      modulePullbackChartSection B S hS g M d (s.val (op d.V)) := by
  refine (congrArg (fun σ : ((modulePullback B S hS g).obj M).sections ↦ σ.val (op d.U))
    (globalSectionsPushforwardIsoSite_hom_app_apply_set g _ _)).trans ?_
  refine (pushforwardTerminalHomEquiv_hom_app_chart g _ _ d.V
    (indexOfChartDiagram B S hS g d)).trans ?_
  exact congrArg (fun z ↦ (moduleChartProjection B S hS g d.V
    (indexOfChartDiagram B S hS g d)).app
      (moduleSetSheaf B S hS X ((modulePullback B S hS g).obj M)) z)
    (modulePullbackAdjunction_unit_app_val_app g M (op d.V) (s.val (op d.V)))

end AlgebraicGeometry.Space

end
