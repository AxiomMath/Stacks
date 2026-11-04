module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.GermSourceAndTarget.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint

/-!
# Flatness of a morphism of algebraic spaces at a point

A morphism of algebraic spaces over a scheme `S` is flat at a point `x` of its source when the
morphism of germs it induces in every pointed étale scheme chart at `x` is flat on local rings.
This is the pointwise refinement of `AlgebraicGeometry.Space.IsFlat`, which tests flatness of
the chart morphisms themselves.

## Main definitions

* `AlgebraicGeometry.Space.IsFlatAt`: **Stacks 03ML**, part (2), flatness at a point of the
  source.

## Main results

There are no propositional results. The definition is an abbreviation, so the pointed-chart
API of `AlgebraicGeometry.Space.HoldsOnEveryEtaleChartAtPoint` applies to it directly; in
particular the equivalence with the corresponding some-chart condition, which is Tag 04NC,
transfers because flatness of a germ morphism is étale local on source and target
(`AlgebraicGeometry.MorphismOfGerms.isEtaleLocalOnSourceAndTarget_isFlat`).

## Implementation notes

Part (1) of Tag 03ML, flatness of the morphism itself, is
`AlgebraicGeometry.Space.IsFlat` in `StacksFrontier/AlgebraicGeometry/Spaces/Flat.lean`. Part (2)
cannot be stated there: the pointed chart condition of Tag 04NC lives in
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleChartAtPoint.lean`, which depends on that module.

## References

* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 04NC](https://stacks.math.columbia.edu/tag/04NC)
* [Stacks Project, Tag 04ND](https://stacks.math.columbia.edu/tag/04ND)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 03ML, part (2).** A morphism of algebraic spaces over `S` is *flat at* a point `x`
of its source when the morphism of germs it induces in every pointed étale scheme chart at `x`
is flat on local rings. -/
@[stacks 03ML "part (2)"]
abbrev IsFlatAt (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) (x : points B S hS F) : Prop :=
  HoldsOnEveryEtaleChartAtPoint B S hS (@MorphismOfGerms.IsFlat.{u}) f x

end AlgebraicGeometry.Space

end
