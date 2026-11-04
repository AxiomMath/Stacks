module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeVanishingQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.HomDescent

/-!
# The chart vanishing criterion with the chart of the source in its own spelling

`AlgebraicGeometry.Space.val_app_eq_zero_iff_lTensor_chartSpace` states the vanishing criterion
for the base change of a map of quasi-coherent modules over a diagram of affine étale charts
entirely in the *chart-space* spelling: the extension of scalars on its right-hand side is the
one attached to the diagram of identity charts of the two chart spaces.  This file moves two of
the three components of that right-hand side back to the chart diagram itself — the algebra
structure, and the ring of the chart of the source — leaving only the base ring of the tensor
product in the chart-space spelling.

## Main results

* `AlgebraicGeometry.Space.val_app_eq_zero_iff_lTensor_chartRing`: the criterion with the
  extension of scalars taken along `AlgebraicGeometry.Space.chartDiagramAlgebra` of the given
  diagram, over the ring `𝒪_X(d.U)` of the chart of the source in its own spelling.

## Implementation notes

**What the three identifications cost.**  Each of the three identifications turning the
chart-space right-hand side into `𝒪_X(d.U) ⊗_{𝒪_Y(d.V)} u(d.V)` holds by `rfl`, but performing
them simultaneously under a `LinearMap.lTensor` exceeds the heartbeat limit.  Performed one per
declaration, as here, they separate cleanly into two cheap ones and one expensive one:

* the two `AlgebraicGeometry.Space.chartDiagramAlgebra` instances are the same term — the
  vertical morphism of `AlgebraicGeometry.Space.chartSpaceIdChartDiagram` is literally the
  vertical morphism of the given diagram, and
  `AlgebraicGeometry.Space.chartDiagramPullback` depends on the diagram only through it — and
  substituting one for the other costs nothing;
* the ring of the identity chart of the chart space of `d.U` is the ring of `d.U`, and
  substituting it for the *left* tensor factor costs nothing;
* the ring of the identity chart of the chart space of `d.V` is the ring of `d.V`, and
  substituting it for the *base ring of the tensor product* does not terminate inside the
  limit.  That conversion has to unfold the base ring inside `TensorProduct`, whose carrier is
  a quotient by a relation mentioning the scalar action of that very ring, and the two spellings
  of the map on sections — the sections of the chart restriction over the identity chart, and
  the sections over the chart — are forced to change with it, because the map determines the
  ring it is linear over.

So the base ring of the tensor product is left in the chart-space spelling, and the two cheap
conversions are made.  Nothing is lost: the base ring carries no geometric input.  The
hypotheses a ring-level consumer must supply about it — flatness of the sections of the target
module over the ring of the affine base, the scalar towers, and the vanishing of a base change —
are statements about `Γ(S, ⊤)` and about the modules, each of which is one further cheap
identification away from its chart spelling
(`AlgebraicGeometry.Space.etaleModulePullback_chartToSpace_obj_val_obj_idEtaleChart`).  What the
conversions here buy is the component that *does* carry geometric input: the left tensor factor
`𝒪_X(d.U)`, the ring of functions of the affine chart of the source, which is where the ideal of
Stacks 083K is seen to act by zero.

**The chart bijectivity is not needed for any of this.**  A second route to the statement in
the spelling of the chart diagram goes through bijectivity of
`AlgebraicGeometry.Space.modulePullbackChartBaseChange` at a quasi-coherent module over an affine
chart diagram.  The identifications here reach the same conclusion, for the two components that
matter, without it.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- The map on sections of the restriction of a map of modules to an étale scheme chart `V`,
over the identity chart of the algebraic space represented by `V`, is its map on sections over
`V`.

This is the map counterpart of
`AlgebraicGeometry.Space.etaleModulePullback_chartToSpace_obj_val_obj_idEtaleChart`:
restriction along an étale morphism is restriction of sections
(`AlgebraicGeometry.Space.QuasiCoherentDescent.etaleModulePullback_map_val_app`), and
postcomposing the identity chart with the structure morphism of `V` gives `V` back. -/
theorem etaleModulePullback_chartToSpace_map_val_app_idEtaleChart
    {F G : Modules.{u, u} B S hS Y.1 Y.2} (u : F ⟶ G) (V : SmallEtale B S hS Y.1) :
    ((etaleModulePullback B S hS (chartToSpace B S hS Y V)
          (isEtale_chartToSpace B S hS Y V)).map u).val.app
        (op (idEtaleChart B S hS ((SmallEtale.toOver B S hS Y.1).obj V))) =
      u.val.app (op V) :=
  QuasiCoherentDescent.etaleModulePullback_map_val_app B S hS
    (chartToSpace B S hS Y V) (isEtale_chartToSpace B S hS Y V) u _

/-- The chart-space criterion with the algebra structure replaced by the one of the given chart
diagram.  The two `AlgebraicGeometry.Space.chartDiagramAlgebra` instances are the same term,
because `AlgebraicGeometry.Space.chartSpaceIdChartDiagram` carries the same vertical morphism
and `AlgebraicGeometry.Space.chartDiagramPullback` sees nothing else. -/
private theorem val_app_eq_zero_iff_lTensor_chartDiagramAlgebra (f : X ⟶ Y)
    {F G : Modules.{u, u} B S hS Y.1 Y.2} (hF : F.IsQuasicoherentOnSite)
    (hG : G.IsQuasicoherentOnSite) (u : F ⟶ G)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    letI : Algebra
        (chartRing B S hS (chartSpace B S hS Y d.V).1 (chartSpace B S hS Y d.V).2
          (chartSpaceIdChartDiagram B S hS f d).V)
        (chartRing B S hS (chartSpace B S hS X d.U).1 (chartSpace B S hS X d.U).2
          (chartSpaceIdChartDiagram B S hS f d).U) := chartDiagramAlgebra B S hS f d
    ((modulePullback B S hS f).map u).val.app (op d.U) = 0 ↔
      LinearMap.lTensor
          (chartRing B S hS (chartSpace B S hS X d.U).1 (chartSpace B S hS X d.U).2
            (chartSpaceIdChartDiagram B S hS f d).U)
          (((etaleModulePullback B S hS (chartToSpace B S hS Y d.V)
              (isEtale_chartToSpace B S hS Y d.V)).map u).val.app
            (op (chartSpaceIdChartDiagram B S hS f d).V)).hom = 0 :=
  val_app_eq_zero_iff_lTensor_chartSpace B S hS f hF hG u d hU hV

/-- **Over a diagram of affine étale charts, the base change of a map of quasi-coherent modules
vanishes on the sections over the chart of `X` exactly when the extension of scalars of its
sections over the chart of `Y` along the diagram vanishes.**

No presentation is assumed.  This is
`AlgebraicGeometry.Space.val_app_eq_zero_iff_lTensor_chartSpace` with the algebra structure and
the left tensor factor moved back to the chart diagram: the extension of scalars is taken along
`AlgebraicGeometry.Space.chartDiagramAlgebra` of `d`, of the ring `𝒪_X(d.U)` of functions on the
affine chart of the source.  The base ring of the tensor product, and with it the spelling of the
map on sections of `u`, stay in the chart-space reading; see the implementation notes of this
file for why, and for why nothing is lost. -/
theorem val_app_eq_zero_iff_lTensor_chartRing (f : X ⟶ Y)
    {F G : Modules.{u, u} B S hS Y.1 Y.2} (hF : F.IsQuasicoherentOnSite)
    (hG : G.IsQuasicoherentOnSite) (u : F ⟶ G)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    letI : Algebra
        (chartRing B S hS (chartSpace B S hS Y d.V).1 (chartSpace B S hS Y d.V).2
          (chartSpaceIdChartDiagram B S hS f d).V)
        (chartRing B S hS X.1 X.2 d.U) := chartDiagramAlgebra B S hS f d
    ((modulePullback B S hS f).map u).val.app (op d.U) = 0 ↔
      LinearMap.lTensor (chartRing B S hS X.1 X.2 d.U)
          (((etaleModulePullback B S hS (chartToSpace B S hS Y d.V)
              (isEtale_chartToSpace B S hS Y d.V)).map u).val.app
            (op (chartSpaceIdChartDiagram B S hS f d).V)).hom = 0 :=
  val_app_eq_zero_iff_lTensor_chartDiagramAlgebra B S hS f hF hG u d hU hV

end AlgebraicGeometry.Space

end
