module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.Topology.KrullDimension
public import StacksCore.Tactic.StacksAttribute

/-!
# Proper intersections of closed subvarieties and of cycles

Two closed subvarieties `W, V` of a variety `X`, of dimensions `s` and `r`, intersect properly
when `dim (W ∩ V) ≤ r + s - dim X`. Two cycles intersect properly when every pair of
components occurring in them with a nonzero coefficient does.

## Main definitions

* `AlgebraicGeometry.IntersectProperly`: the dimension criterion for two irreducible closed
  subsets of a scheme.
* `AlgebraicGeometry.AlgebraicCycle.IntersectProperly`: the same criterion applied to every pair
  of components occurring in two cycles.

## Main results

* `AlgebraicGeometry.intersectProperly_iff` and
  `AlgebraicGeometry.AlgebraicCycle.intersectProperly_iff`: the defining criteria.
* `AlgebraicGeometry.intersectProperly_of_add_le`: proper intersection from a lower bound on the
  dimensions of the two subvarieties and upper bounds on those of their intersection and of the
  ambient scheme.

## Implementation notes

Closed subvarieties are represented by irreducible closed subsets. Their intersection carries the
subspace topology, so its topological Krull dimension is `⊥` when it is empty. The inequality is
written with the ambient dimension added on the left, which avoids subtracting extended
dimensions. The coefficients of a cycle may lie in any type with a zero.

## References

* [Stacks Project, Tag 0AZQ](https://stacks.math.columbia.edu/tag/0AZQ)
-/

@[expose] public section

open TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

/-- Two irreducible closed subsets of a scheme **intersect properly** when their intersection
has at most the expected dimension, namely `dim (W ∩ V) ≤ dim W + dim V - dim X`. -/
@[stacks 0AZQ "closed subvarieties"]
public def IntersectProperly (W V : IrreducibleCloseds X) : Prop :=
  topologicalKrullDim (↥((W : Set X) ∩ (V : Set X))) + topologicalKrullDim X ≤
    topologicalKrullDim (W : Set X) + topologicalKrullDim (V : Set X)

/-- The dimension criterion defining proper intersection of two closed subvarieties. -/
public theorem intersectProperly_iff (W V : IrreducibleCloseds X) :
    IntersectProperly W V ↔
      topologicalKrullDim (↥((W : Set X) ∩ (V : Set X))) + topologicalKrullDim X ≤
        topologicalKrullDim (W : Set X) + topologicalKrullDim (V : Set X) :=
  Iff.rfl

/-- Two irreducible closed subsets intersect properly when natural numbers `a ≤ dim W`,
`b ≤ dim V`, `dim (W ∩ V) ≤ e` and `dim X ≤ m` satisfy `e + m ≤ a + b`. -/
public theorem intersectProperly_of_add_le (W V : IrreducibleCloseds X) {a b e m : ℕ}
    (hW : (a : WithBot ℕ∞) ≤ topologicalKrullDim (W : Set X))
    (hV : (b : WithBot ℕ∞) ≤ topologicalKrullDim (V : Set X))
    (hint : topologicalKrullDim (↥((W : Set X) ∩ (V : Set X))) ≤ (e : WithBot ℕ∞))
    (hamb : topologicalKrullDim X ≤ (m : WithBot ℕ∞)) (h : e + m ≤ a + b) :
    IntersectProperly W V :=
  le_trans (add_le_add hint hamb) (le_trans (by exact_mod_cast h) (add_le_add hW hV))

namespace AlgebraicCycle

/-- Two algebraic cycles **intersect properly** when every pair of components occurring in them
with a nonzero coefficient intersects properly. -/
@[stacks 0AZQ "cycles"]
public def IntersectProperly {R : Type*} [Zero R] (α β : AlgebraicCycle X R) : Prop :=
  ∀ W V : IrreducibleCloseds X, α W.isIrreducible.genericPoint ≠ 0 →
    β V.isIrreducible.genericPoint ≠ 0 → AlgebraicGeometry.IntersectProperly W V

/-- The componentwise criterion defining proper intersection of two cycles. -/
public theorem intersectProperly_iff {R : Type*} [Zero R] (α β : AlgebraicCycle X R) :
    IntersectProperly α β ↔
      ∀ W V : IrreducibleCloseds X, α W.isIrreducible.genericPoint ≠ 0 →
        β V.isIrreducible.genericPoint ≠ 0 → AlgebraicGeometry.IntersectProperly W V :=
  Iff.rfl

end AlgebraicCycle

end AlgebraicGeometry

end
