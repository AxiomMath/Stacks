module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Fpqc.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FinitenessFpqcLocality

/-!
# Finite presentation of morphisms of algebraic spaces is fpqc local on the base

Let `S` be a scheme contained in a big fppf site `B`. A morphism of algebraic spaces over `S`
is of finite presentation when it is locally of finite presentation, quasi-compact and
quasi-separated (**Stacks 03XP**, part (3)). Each of the three conditions is local on the base
for the fpqc topology of **Stacks 03YH** — local finite presentation by **Stacks 041T**,
quasi-compactness by **Stacks 041L**, quasi-separatedness by **Stacks 041N** — and locality on
the base passes to an infimum of morphism properties, so being of finite presentation is fpqc
local on the base as well.

## Main results

* `AlgebraicGeometry.Space.finitePresentation_isLocalAtTarget_fpqc`: **Stacks 041V**.

## Implementation notes

The conjunction of Stacks 03XP, part (3) is nested as `P ∧ (Q ∧ R)`, so the infimum of morphism
properties is taken twice; the inner one, quasi-compactness together with quasi-separatedness,
is named first so that the outer one has an instance to find.

The index universe of a covering family is a free universe parameter of
`AlgebraicGeometry.Space.Topology.precoverage` and stays free here, as it does in the three
localities being combined.

## References

* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 041L](https://stacks.math.columbia.edu/tag/041L)
* [Stacks Project, Tag 041N](https://stacks.math.columbia.edu/tag/041N)
* [Stacks Project, Tag 041T](https://stacks.math.columbia.edu/tag/041T)
* [Stacks Project, Tag 041V](https://stacks.math.columbia.edu/tag/041V)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Quasi-compactness together with quasi-separatedness, as a property of morphisms of algebraic
spaces over `S`, is local on the base for the fpqc topology of Stacks 03YH: it is the infimum of
the properties of Stacks 041L and Stacks 041N.

This is the inner conjunct of being of finite presentation (Stacks 03XP, part (3)). -/
instance quasiCompact_and_quasiSeparated_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) =>
        IsQuasiCompact B S hS f.hom ∧ IsQuasiSeparated B S hS f.hom)
      (Topology.precoverage.{u, v} .fpqc B S hS) :=
  MorphismProperty.IsLocalAtTarget.inf
    (P := quasiCompactProperty B S hS)
    (Q := quasiSeparatedProperty B S hS)

/-- **Stacks 041V.** Being of finite presentation is, for morphisms of algebraic spaces over
`S`, local on the base for the fpqc topology of Stacks 03YH.

Being of finite presentation is being locally of finite presentation (Stacks 041T) together with
quasi-compactness (Stacks 041L) and quasi-separatedness (Stacks 041N). -/
@[stacks 041V, sga "4 IV 8.5.5" "more general"]
instance finitePresentation_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) => IsFinitePresentation B S hS f.hom)
      (Topology.precoverage.{u, v} .fpqc B S hS) :=
  MorphismProperty.IsLocalAtTarget.inf
    (P := fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) =>
      IsLocallyOfFinitePresentation B S hS f.hom)
    (Q := fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) =>
      IsQuasiCompact B S hS f.hom ∧ IsQuasiSeparated B S hS f.hom)

end AlgebraicGeometry.Space

end
