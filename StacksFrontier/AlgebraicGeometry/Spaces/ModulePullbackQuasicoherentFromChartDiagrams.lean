module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModulePullbackSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpaceGlobalPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackQuasicoherence

/-!
# The pullback of a quasi-coherent module along an arbitrary morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`.  Stacks 03GA asserts that the pullback `f^*` of Stacks 03LU carries quasi-coherent
`𝒪_Y`-modules to quasi-coherent `𝒪_X`-modules.  This file proves that for an arbitrary `f` and
an arbitrary quasi-coherent module, with no further input.

An étale scheme chart `W` of `X` which is the chart of `X` of a commuting square of étale
scheme charts over `f` whose chart of `Y` is affine
(`AlgebraicGeometry.Space.HasAffineChartDiagram`) has the property that the composite
`chartSpace W ⟶ X ⟶ Y` factors through the structure morphism of an affine étale chart of `Y`,
so the pullback of a quasi-coherent module along that composite is quasi-coherent by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_affineChartFactorization`; the
composition comparison of Stacks 03LU rewrites it as the pullback of `f^*F` to the chart space.
Those charts cover the final object of the small étale site of `X` by
`AlgebraicGeometry.Space.mem_topology_of_hasAffineChartDiagram`, and quasi-coherence is detected
on any covering family of charts.

## Main definitions

* `AlgebraicGeometry.Space.affineChartDiagramCharts`: the étale scheme charts of `X` carrying an
  affine chart diagram over `f`, as a family indexed by itself.

## Main results

* `AlgebraicGeometry.Space.coversTop_affineChartDiagramCharts`: that family covers the final
  object of the small étale site of `X`.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`:
  **Stacks 03GA** for an arbitrary morphism of algebraic spaces and an arbitrary quasi-coherent
  module.
* `AlgebraicGeometry.Space.quasicoherentPullbackFunctor`: the induced functor
  `QCoh(𝒪_Y) ⥤ QCoh(𝒪_X)`, which is the form in which the source states Stacks 03GA.

## Implementation notes

The geometric input is the one the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackQuasicoherence.lean` record as
missing: that the étale charts of `X` whose composite with `f` factors through an affine étale
chart of `Y` cover `X`.  Those notes look for it as a descent of a covering through the
comparison of Stacks 03G1 from the spaces-étale site of Stacks 03G0; it is available instead,
and proved directly, as `AlgebraicGeometry.Space.mem_topology_of_hasAffineChartDiagram`, which
lifts a point of a chart of `X` to a point of a chart carrying an affine chart diagram.  So
`AlgebraicGeometry.Space.HasLocalInverseImagePresentations`, the inverse-image factor of
Stacks 03DO that `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback` carries, is not
needed for the conclusion; it is a statement about `f⁻¹F` before extension of scalars and is
not deduced here.

The family of charts is indexed by the subtype of the charts having the property, rather than by
an abstract type with a map, because
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_coversTop_etaleModulePullback` asks for an
index type in `Type (u + 1)`, which is the universe of the objects of the small étale site.

## References

* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- The étale scheme charts of `X` carrying an affine chart diagram over `f`, as a family
indexed by the subtype of charts having that property. -/
def affineChartDiagramCharts (f : X ⟶ Y) :
    {W : SmallEtale B S hS X.1 // HasAffineChartDiagram B S hS f W} → SmallEtale B S hS X.1 :=
  Subtype.val

/-- **The charts of `X` carrying an affine chart diagram over `f` cover the final object of the
small étale site of `X`.**

The sieve of the morphisms into a chart `U` whose source admits a morphism to a member of the
family contains every morphism out of a member, and such a sieve is covering by
`AlgebraicGeometry.Space.mem_topology_of_hasAffineChartDiagram`. -/
theorem coversTop_affineChartDiagramCharts (f : X ⟶ Y) :
    (SmallEtale.topology B S hS X.1).CoversTop (affineChartDiagramCharts B S hS f) := fun U =>
  mem_topology_of_hasAffineChartDiagram B S hS f U _
    fun {W} _ hW => ⟨⟨W, hW⟩, ⟨𝟙 W⟩⟩

/-- **[Stacks, Tag 03GA].**  The pullback `f^*F` of Stacks 03LU of a quasi-coherent
`𝒪_Y`-module along an arbitrary morphism `f : X ⟶ Y` of algebraic spaces is quasi-coherent.

On the chart space of a chart of `X` carrying an affine chart diagram over `f` the pullback of
`F` along the composite with `f` is quasi-coherent, because that composite factors through the
structure morphism of an affine étale chart of `Y`; the composition comparison of Stacks 03LU
turns that into quasi-coherence of the pullback of `f^*F` to the chart space, and those charts
cover the final object of the small étale site of `X`. -/
@[stacks 03GA "the pullback functor preserves quasi-coherence"]
theorem isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS Y.1 Y.2) (hF : F.IsQuasicoherentOnSite) :
    ((modulePullback B S hS f).obj F).IsQuasicoherentOnSite := by
  refine isQuasicoherentOnSite_of_coversTop_etaleModulePullback B S hS X
    (affineChartDiagramCharts B S hS f) (coversTop_affineChartDiagramCharts B S hS f) _
    fun i => ?_
  obtain ⟨-, V, q, hq, hVaff⟩ := i.2
  have hfac : chartToSpace B S hS X i.1 ≫ f =
      chartSpaceMapOver B S hS q ≫ chartToSpace B S hS Y V :=
    (chartSpaceMapOver_comp_chartToSpace B S hS f q hq).symm
  refine SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X i.1)
      (isEtale_chartToSpace B S hS X i.1)).app _) ?_
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((modulePullbackCompIso B S hS (chartToSpace B S hS X i.1) f).app F).symm
    (isQuasicoherentOnSite_modulePullback_of_affineChartFactorization B S hS
      (chartToSpace B S hS X i.1 ≫ f) V hVaff (chartSpaceMapOver B S hS q) hfac F hF)

/-- **[Stacks, Tag 03GA], in the form the source states it.**  The pullback of Stacks 03LU
along an arbitrary morphism of algebraic spaces restricts to a functor
`QCoh(𝒪_Y) ⥤ QCoh(𝒪_X)` between the categories of quasi-coherent modules of Stacks 03G9. -/
@[stacks 03GA "the induced functor on quasi-coherent modules"]
noncomputable def quasicoherentPullbackFunctor (f : X ⟶ Y) :
    QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2 ⥤
      QuasicoherentSheaves.{u, u} B S hS X.1 X.2 :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ modulePullback B S hS f)
    fun F => isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS f
      F.obj F.property

end AlgebraicGeometry.Space

end
