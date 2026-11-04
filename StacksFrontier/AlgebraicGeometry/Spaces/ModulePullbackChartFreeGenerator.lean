module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackChartGeneratorMultiple
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeGeneratorSieveDescent

/-!
# The inverse image of a free generator over a chart diagram is a free generator

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`, `ℳ` an invertible `𝒪_Y`-module and
`d` a commuting square of étale charts over `f`, with `ℳ` free over the chart `d.V` of `Y` on a
compatible family `e`. Then the restrictions of the inverse image of `e(d.V)` along the square
(`AlgebraicGeometry.Space.modulePullbackChartSectionRestrict`) form a compatible family freely
generating `f^*ℳ` over every chart over `d.U`.

## Main definitions

* `AlgebraicGeometry.Space.modulePullbackChartGenerator`: the inverse image of a free generator
  along a chart diagram, over the charts over the source chart.

## Main results

* `AlgebraicGeometry.Space.bijective_smul_modulePullbackChartGenerator`: the inverse image family
  freely generates `f^*ℳ` over every chart over `d.U`.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (M : Modules.{u, u} B S hS Y.1 Y.2)

/-- **The inverse image of a free generator along a chart diagram, over the charts over the
source chart.** -/
noncomputable def modulePullbackChartGenerator (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (e : (W : SmallEtale B S hS Y.1) → (W ⟶ d.V) → M.val.obj (op W))
    (W : SmallEtale B S hS X.1) (k : W ⟶ d.U) :
    ((modulePullback B S hS f).obj M).val.obj (op W) :=
  modulePullbackChartSectionRestrict B S hS f M d (e d.V (𝟙 d.V)) k

/-- The inverse image family is compatible with restriction. -/
theorem modulePullbackChartGenerator_compat (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (e : (W : SmallEtale B S hS Y.1) → (W ⟶ d.V) → M.val.obj (op W))
    (W W' : SmallEtale B S hS X.1) (k : W ⟶ d.U) (h : W' ⟶ W) :
    (((modulePullback B S hS f).obj M).val.map h.op).hom
        (modulePullbackChartGenerator B S hS f M d e W k) =
      modulePullbackChartGenerator B S hS f M d e W' (h ≫ k) :=
  modulePullbackChartSectionRestrict_map B S hS f M d _ k h

/-- At the identity chart the inverse image family is the inverse image of the generator. -/
theorem modulePullbackChartGenerator_id (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (e : (W : SmallEtale B S hS Y.1) → (W ⟶ d.V) → M.val.obj (op W)) :
    modulePullbackChartGenerator B S hS f M d e d.U (𝟙 d.U) =
      (modulePullbackChartFMap B S hS f M).app d (e d.V (𝟙 d.V)) := by
  unfold modulePullbackChartGenerator modulePullbackChartSectionRestrict
  exact congrArg (fun k ↦ (ConcreteCategory.hom k) ((modulePullbackChartFMap B S hS f M).app d
    (e d.V (𝟙 d.V)))) (((modulePullback B S hS f).obj M).val.map_id (op d.U))

/-- **The inverse image family freely generates `f^*ℳ` over every chart over `d.U`.** -/
theorem bijective_smul_modulePullbackChartGenerator
    (hM : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS Y)
      (structureRingSheaf B S hS Y).property M)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (e : (W : SmallEtale B S hS Y.1) → (W ⟶ d.V) → M.val.obj (op W))
    (hcompat : ∀ (W W' : SmallEtale B S hS Y.1) (k : W ⟶ d.V) (g : W' ⟶ W),
      (M.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hbij : ∀ (W : SmallEtale B S hS Y.1) (k : W ⟶ d.V),
      Function.Bijective fun r : chartRing B S hS Y.1 Y.2 W ↦ r • e W k)
    (W : SmallEtale B S hS X.1) (k : W ⟶ d.U) :
    Function.Bijective fun r : chartRing B S hS X.1 X.2 W ↦
      r • modulePullbackChartGenerator B S hS f M d e W k := by
  obtain ⟨T, hT, hloc⟩ := exists_sieve_bijective_smul_modulePullbackChartSection B S hS f M hM d
    e hcompat hbij
  refine bijective_smul_of_sieve B S hS X ((modulePullback B S hS f).obj M) W _ (T.pullback k)
    ((SmallEtale.topology B S hS X.1).pullback_stable k hT) fun W' j hj => ?_
  have h := hloc (j ≫ k) hj W' (𝟙 W')
  rw [Category.id_comp] at h
  have he : chartRestrictLinear ((modulePullback B S hS f).obj M) j
      (modulePullbackChartGenerator B S hS f M d e W k) =
      modulePullbackChartSectionRestrict B S hS f M d (e d.V (𝟙 d.V)) (j ≫ k) :=
    modulePullbackChartGenerator_compat B S hS f M d e W W' k j
  rwa [he]

end AlgebraicGeometry.Space

end
