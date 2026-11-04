module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Weighted Dynkin diagrams

The proper connected subgraphs of minus-two indices of a numerical type are
classified by the finite Dynkin diagrams `A`, `B`, `C`, `D`, `E₆`, `E₇`, `E₈`,
`F₄` and `G₂`. This file names those nine families, records for each the
numbers of vertices it admits, the edges of a chosen ordering of its vertices,
and the relative weights of its vertices, and assembles them into the
numerical data an ordered proper subgraph of a numerical type must carry.

The weights are relative: a configuration of shape `d` and scale `w` has
vertex weights `d.weightFactor r * w`. The intersection number along an edge
is the larger of its two endpoint weights, the diagonal entry at a vertex is
minus twice its weight, and every other off-diagonal entry vanishes — that is,
the restricted intersection matrix is `w` times the Cartan matrix of `d`.

## Main definitions

* `AlgebraicGeometry.DynkinShape`: the nine families.
* `AlgebraicGeometry.DynkinShape.Allows`: the admissible numbers of vertices.
* `AlgebraicGeometry.DynkinShape.Edge`: the edges of an ordered diagram.
* `AlgebraicGeometry.DynkinShape.weightFactor`: the relative vertex weights.
* `AlgebraicGeometry.NumericalType.IsDynkinConfiguration`: the full numerical
  data of an ordered proper Dynkin subgraph.

## Implementation notes

The vertices of a diagram on `t` vertices are `Fin t`, ordered so that
`0, …, t - 1` is the main chain of a type `A`, `B`, `C`, `F₄` or `G₂` diagram;
in type `D` the final vertex is the extra leaf attached to the penultimate
vertex of the main arm, and in type `E` it is the extra branch.

`IsDynkinConfiguration` also records the multiplicity inequalities: at each
vertex the weighted sum of the multiplicities of its neighbours in the diagram
is at most twice its own weighted multiplicity, which is what the components
outside the subgraph contribute.

## References

* [Stacks Project, Tag 0C8Q](https://stacks.math.columbia.edu/tag/0C8Q)
-/

@[expose] public section

open scoped BigOperators

namespace AlgebraicGeometry

/-- The weighted Dynkin diagram families occurring as proper connected
subgraphs of minus-two indices. -/
public inductive DynkinShape where
  | A | B | C | D | E6 | E7 | E8 | F4 | G2
  deriving DecidableEq

/-- The numbers of vertices allowed for each family. -/
public def DynkinShape.Allows (d : DynkinShape) (t : ℕ) : Prop :=
  match d with
  | .A | .B | .C => 2 ≤ t
  | .D => 4 ≤ t
  | .E6 => t = 6
  | .E7 => t = 7
  | .E8 => t = 8
  | .F4 => t = 4
  | .G2 => t = 2

/-- The edges of an ordered Dynkin diagram. In type D the final vertex is
attached to the penultimate vertex of the main arm; in type E the final vertex
is the extra branch. -/
@[sga "3 XXI 7.4.6" "partial"]
public def DynkinShape.Edge {t : ℕ} (d : DynkinShape) (r s : Fin t) : Prop :=
  let chain := r.val + 1 = s.val ∨ s.val + 1 = r.val
  match d with
  | .A | .B | .C | .F4 | .G2 => chain
  | .D =>
      ((chain ∧ r.val < t - 1 ∧ s.val < t - 1) ∨
        (r.val = t - 3 ∧ s.val = t - 1) ∨
        (s.val = t - 3 ∧ r.val = t - 1))
  | .E6 =>
      ((chain ∧ r.val < 5 ∧ s.val < 5) ∨
        (r.val = 2 ∧ s.val = 5) ∨ (s.val = 2 ∧ r.val = 5))
  | .E7 =>
      ((chain ∧ r.val < 6 ∧ s.val < 6) ∨
        (r.val = 3 ∧ s.val = 6) ∨ (s.val = 3 ∧ r.val = 6))
  | .E8 =>
      ((chain ∧ r.val < 7 ∧ s.val < 7) ∨
        (r.val = 4 ∧ s.val = 7) ∨ (s.val = 4 ∧ r.val = 7))

/-- The relative vertex weights in the chosen ordering. -/
public def DynkinShape.weightFactor {t : ℕ} (d : DynkinShape) (r : Fin t) : ℤ :=
  match d with
  | .B => if r.val + 1 = t then 1 else 2
  | .C => if r.val + 1 = t then 2 else 1
  | .F4 => if r.val < 2 then 1 else 2
  | .G2 => if r.val = 0 then 1 else 3
  | _ => 1

namespace NumericalType

/-- The full numerical data of an ordered proper Dynkin subgraph. The edge
intersection is the larger of the two endpoint weights, and every other
off-diagonal entry vanishes. -/
public def IsDynkinConfiguration {t : ℕ} (T : NumericalType)
    (v : Fin t → Fin T.componentCount) (d : DynkinShape) (w : ℤ) : Prop := by
  classical
  exact d.Allows t ∧ 0 < w ∧
    (∀ r, T.weight (v r) = d.weightFactor r * w) ∧
    (∀ r s, T.intersection (v r) (v s) =
      if r = s then -2 * d.weightFactor r * w
      else if d.Edge r s then
        max (d.weightFactor r) (d.weightFactor s) * w else 0) ∧
    (∀ r, (∑ s : Fin t,
      if d.Edge r s then
        max (d.weightFactor r) (d.weightFactor s) * T.multiplicity (v s)
      else 0) ≤ 2 * d.weightFactor r * T.multiplicity (v r))

end NumericalType

end AlgebraicGeometry
