module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackGlobalSectionSmul
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSheafRingUnit

/-!
# The image of a global function under a morphism of algebraic spaces, chart by chart

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `s` a global section of `𝒪_Y`, read as a
morphism out of the terminal sheaf of sets.  Its image `f♯(s)` under the morphism of small étale
ringed topoi, `Stacks.Sheaves.RingedToposModules.pullbackTerminalSection`, is the global section
of `𝒪_X` that the pullback of modules multiplies by
(`Stacks.Sheaves.RingedToposModules.pullbackModules_map_globalSectionToEnd_unit`).  It is built
from the inverse image of sheaves, which has no description on sections.  This file computes it
on charts: over the source chart of a commutative diagram of étale scheme charts over `f` it is
the pullback of the value of `s` on the target chart along the vertical morphism of schemes.

## Main results

* `AlgebraicGeometry.Space.pullbackTerminalSection_hom_app_chartDiagram`: **`f♯(s)` over `d.U`
  is the pullback of `s` over `d.V` along `d.g`**, for every commutative diagram `d` of étale
  scheme charts over `f`.

## Implementation notes

The section `f♯(s)` is the composite `1 ≅ f⁻¹1 ⟶ f⁻¹𝒪_Y ⟶ 𝒪_X` of the inverse image of `s` with
the inverse-image form of the structure map.  Its transpose along `f⁻¹ ⊣ f_*` is `s` followed by
the direct-image form `𝒪_Y ⟶ f_*𝒪_X` of the structure map, which is
`AlgebraicGeometry.Space.structureSharp`; the chart projection of the direct image is natural in
the sheaf (`AlgebraicGeometry.Space.directImageChartProjection_map`) and carries the structure
map to pullback of regular functions
(`AlgebraicGeometry.Space.directImageChartProjection_structureSharpSet_chartDiagram`).  What is
left is that the chart projection of the unit at the terminal sheaf is a section of a terminal
sheaf, of which there is only one.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.RingedToposModules (pullbackTerminalSection)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **The image `f♯(s)` of a global section `s` of `𝒪_Y`, over the source chart of a commutative
diagram `d` of étale scheme charts over `f`, is the pullback of the value of `s` over the target
chart along the vertical morphism of schemes of the diagram.** -/
theorem pullbackTerminalSection_hom_app_chartDiagram (f : X ⟶ Y)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (s : ⊤_ (Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) ⟶ structureSetSheaf B S hS Y) :
    (pullbackTerminalSection (smallEtaleRingedToposModulesHom B S hS f) s).hom.app (op d.U)
        (Sheaf.terminalSheafSection _ (op d.U)) =
      (chartDiagramPullback B S hS f d).hom
        (s.hom.app (op d.V) (Sheaf.terminalSheafSection _ (op d.V))) := by
  let g := smallEtaleRingedToposModulesHom B S hS f
  let j : StructuredArrow (op (chartBaseChange B S hS f d.V)) (comparisonFunctor B S hS X).op :=
    StructuredArrow.mk (Y := op d.U) (baseChangeArrowOfChartDiagram B S hS f d).op
  let π := directImageChartProjection B S hS f d.V j
  let adj := g.toToposHom.adj
  let k := (sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).map
    g.fSharpInverseImage
  let m := g.toToposHom.inverseImage.map s ≫ k
  have hm : adj.homEquiv _ _ m = s ≫ structureSharpSet B S hS f := by
    refine (adj.homEquiv_naturality_left _ _).trans ?_
    refine congrArg (fun φ => s ≫ φ) ?_
    refine g.fSharp_adjunct.symm.trans ?_
    exact congrArg (fun φ => (sheafCompose (SmallEtale.topology B S hS Y.1)
      (forget RingCat.{u})).map φ) (ringFsharp_eq_structureSharp B S hS f)
  let pt := Sheaf.terminalSheafSection (SmallEtale.topology B S hS Y.1) (op d.V)
  have e1 := congrArg (fun φ => π.app (structureSetSheaf B S hS X) (φ.hom.app (op d.V) pt))
    ((adj.homEquiv_unit _ _ _).symm.trans hm)
  have e2 := directImageChartProjection_map B S hS f d.V j m
    ((adj.unit.app (⊤_ (Sheaf (SmallEtale.topology B S hS Y.1) (Type u)))).hom.app (op d.V) pt)
  have e3 := directImageChartProjection_structureSharpSet_chartDiagram B S hS f d
    (s.hom.app (op d.V) pt)
  have hpt : (g.toToposHom.inverseImageTerminalIso.hom.hom.app (op d.U)
      (π.app (g.toToposHom.inverseImage.obj (⊤_ (Sheaf (SmallEtale.topology B S hS Y.1)
        (Type u))))
        ((adj.unit.app (⊤_ (Sheaf (SmallEtale.topology B S hS Y.1) (Type u)))).hom.app
          (op d.V) pt))) = Sheaf.terminalSheafSection _ (op d.U) :=
    Sheaf.eq_terminalSheafSection _
  have hTm : g.toToposHom.inverseImageTerminalIso.hom ≫
      pullbackTerminalSection (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Y) g s = m := by
    change g.toToposHom.inverseImageTerminalIso.hom ≫
      g.toToposHom.inverseImageTerminalIso.inv ≫ m = m
    exact Iso.hom_inv_id_assoc _ _
  have e4 := congrArg (fun φ => φ.hom.app (op d.U)
    (π.app (g.toToposHom.inverseImage.obj (⊤_ (Sheaf (SmallEtale.topology B S hS Y.1)
        (Type u))))
      ((adj.unit.app (⊤_ (Sheaf (SmallEtale.topology B S hS Y.1) (Type u)))).hom.app
        (op d.V) pt))) hTm
  refine (congrArg _ hpt).symm.trans (e4.trans ?_)
  exact e2.symm.trans (e1.trans e3)

end AlgebraicGeometry.Space

end
