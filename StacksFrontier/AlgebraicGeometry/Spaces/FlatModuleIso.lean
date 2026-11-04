module

public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModule

/-!
# Flatness of a module on an algebraic space is invariant under isomorphism

`AlgebraicGeometry.Space.IsFlatOver` of Stacks 05VV tests a module on an algebraic space
chartwise: on every commuting square of étale scheme charts the restriction of the module to
the source chart is flat over the target chart, in the stalkwise sense of Stacks 08KT.  This
file shows the predicate only depends on the isomorphism class of the module.

## Main results

* `AlgebraicGeometry.Space.isFlatOverOnChartDiagram_iff_of_iso`: flatness on one square of
  charts is invariant under an isomorphism of modules.
* `AlgebraicGeometry.Space.isFlatOver_iff_of_iso` and
  `AlgebraicGeometry.Space.IsFlatOver.of_iso`: flatness over the target is invariant under an
  isomorphism of modules.

## Implementation notes

The two ingredients are `AlgebraicGeometry.Space.restrictToChartIso`, which restricts an
isomorphism of `𝒪_X`-modules to an étale chart, and
`AlgebraicGeometry.flatOverAt_iff_of_iso`, the corresponding invariance for a module on a
scheme over a scheme, proved from the linear equivalence of stalks that an isomorphism of
sheaves of modules induces.

The module universe is the universe of the structure rings, as it is for
`AlgebraicGeometry.Space.IsFlatOver` itself; `AlgebraicGeometry.Space.restrictToChart` lands
in the modules of the chart scheme only there, which is what
`AlgebraicGeometry.flatOverAt_iff_of_iso` consumes.

## References

* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 08KT](https://stacks.math.columbia.edu/tag/08KT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)

/-- Flatness over the target chart of the restriction of a module to the source chart of one
commuting square of étale scheme charts is invariant under an isomorphism of modules. -/
theorem isFlatOverOnChartDiagram_iff_of_iso {f : X ⟶ Y}
    {F G : Modules.{u, u} B S hS X hX} (e : F ≅ G) (d : ChartDiagram B S hS X Y f) :
    IsFlatOverOnChartDiagram B S hS hX F d ↔ IsFlatOverOnChartDiagram B S hS hX G d :=
  forall_congr' fun x =>
    flatOverAt_iff_of_iso ((BigFppfOver.toScheme B S hS).map d.g)
      (restrictToChartIso B S hS hX e d.U) x

/-- **Flatness over the target is invariant under an isomorphism of modules.**  An
`𝒪_X`-module isomorphic to one flat over `Y` along `f` is itself flat over `Y` along `f`. -/
theorem isFlatOver_iff_of_iso (f : X ⟶ Y) {F G : Modules.{u, u} B S hS X hX} (e : F ≅ G) :
    IsFlatOver B S hS hX f F ↔ IsFlatOver B S hS hX f G :=
  forall_congr' fun d => isFlatOverOnChartDiagram_iff_of_iso B S hS hX e d

/-- Flatness over the target transfers along an isomorphism of modules. -/
theorem IsFlatOver.of_iso {f : X ⟶ Y} {F G : Modules.{u, u} B S hS X hX} (e : F ≅ G)
    (h : IsFlatOver B S hS hX f F) : IsFlatOver B S hS hX f G :=
  (isFlatOver_iff_of_iso B S hS hX f e).mp h

end AlgebraicGeometry.Space

end
