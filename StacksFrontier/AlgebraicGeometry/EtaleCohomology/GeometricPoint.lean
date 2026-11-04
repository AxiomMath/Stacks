module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.KrullTopology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisActionStalks.Basic

/-!
# Geometric points, their étale neighborhoods, and their absolute Galois groups

A geometric point of a scheme `S` is a morphism `Spec Ω ⟶ S` from the spectrum of an
algebraically closed field `Ω`. Since `Spec Ω` has a unique point, such a morphism has a
well-defined image in the underlying space of `S`, and the geometric point is said to lie
over that image. An étale neighborhood of a geometric point is a scheme étale over `S`
together with a lift of the geometric point to it; these form a category, whose morphisms are
the morphisms over `S` compatible with the chosen lifts.

The morphism of a geometric point is the same datum as a point `s` of `S` together with a
field embedding of the residue field `κ(s)` into `Ω`. Inside `Ω` the relative separable
closure of `κ(s)` is a separable algebraic closure of `κ(s)`, and its Galois group over
`κ(s)` — with its Krull topology — is the absolute Galois group at the geometric point. The
geometric point is called *algebraic* when `Ω` is itself an algebraic closure of `κ(s)`.

This module re-exports
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic`, which defines
geometric points, the points they lie over and the category of étale neighborhoods, and
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisActionStalks.Basic`, which defines the
separable closure, the absolute Galois group and algebraic geometric points.

## References

* [Stacks Project, Tag 03PO](https://stacks.math.columbia.edu/tag/03PO)
* [Stacks Project, Tag 03QX](https://stacks.math.columbia.edu/tag/03QX)
-/
