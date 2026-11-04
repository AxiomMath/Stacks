module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.GorensteinFiber
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.AtAPoint

/-!
# Gorenstein morphisms of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is *Gorenstein at* a point of its source
when it is flat there and the local ring of its fibre is Noetherian and Gorenstein in
pointed étale scheme charts at that point; it is *Gorenstein* when this holds at every point
of its source.

## Main definitions

* `AlgebraicGeometry.Space.IsGorensteinAt` is Gorensteinness at a point of the source.
* `AlgebraicGeometry.Space.IsGorenstein` is Gorensteinness of the morphism.

## Implementation notes

Both conjuncts are pointed-chart conditions of Tag 04NC, so they are phrased with
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChartAtPoint`: the first through the flatness
predicate `AlgebraicGeometry.Space.IsFlatAt` of Tag 03ML, the second through the germ-level
predicate `AlgebraicGeometry.HasGorensteinFiberLocalRing` of Tag 0E13. Both are étale local
on source and target, so by Tag 04NC each may equally be tested on a single pointed chart.

`AlgebraicGeometry.HasGorensteinFiberLocalRing` includes Noetherianity of the fibre local
ring rather than assuming it, so these predicates make sense with no standing hypothesis
that the fibres are locally Noetherian; on a morphism satisfying that hypothesis
(`AlgebraicGeometry.Space.HasLocallyNoetherianFibersAtPoints`, Tag 0CUX) they are the
conditions of Tag 0E14. Both are abbreviations, so the pointed-chart API applies to them
directly and no separate interface is needed. This follows the Cohen–Macaulay case,
`AlgebraicGeometry.Space.IsCohenMacaulayAt` of Tag 0E0V.

## References

* [Stacks Project, Tag 0E14](https://stacks.math.columbia.edu/tag/0E14)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 0E14, part (1).** A morphism of algebraic spaces over `S` is *Gorenstein at* a
point `x` of its source when it is flat at `x` and the local ring of its fibre is Noetherian
and Gorenstein in every pointed étale scheme chart at `x`. -/
@[stacks 0E14 "part (1): at a point"]
abbrev IsGorensteinAt (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (x : points B S hS X) : Prop :=
  IsFlatAt B S hS f x ∧
    HoldsOnEveryEtaleChartAtPoint B S hS (@HasGorensteinFiberLocalRing.{u}) f x

/-- **Stacks 0E14, part (2).** A morphism of algebraic spaces over `S` is *Gorenstein* when
it is Gorenstein at every point of its source. -/
@[stacks 0E14 "part (2): morphism"]
abbrev IsGorenstein (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) : Prop :=
  ∀ x : points B S hS X, IsGorensteinAt B S hS f x

end AlgebraicGeometry.Space

end
