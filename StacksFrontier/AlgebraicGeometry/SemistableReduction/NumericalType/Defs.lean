module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Numerical types

A *numerical type* is the combinatorial shadow of a semistable model of a curve: positive integer
multiplicities and weights, nonnegative component genera, and a connected symmetric intersection
matrix whose weighted rows vanish and whose entries in each row are divisible by that row's
weight.

This file defines numerical types, equivalence of numerical types, minus-one and minus-two
indices, and minimal numerical types.

## Main definitions

* `AlgebraicGeometry.NumericalType`: the structure itself.
* `AlgebraicGeometry.NumericalType.Equivalent`: equivalence under a relabelling of components.
* `AlgebraicGeometry.NumericalType.IsMinusOneIndex`: component genus zero and diagonal
  intersection the negative of the weight.
* `AlgebraicGeometry.NumericalType.IsMinusTwoIndex`: component genus zero and diagonal
  intersection minus twice the weight.
* `AlgebraicGeometry.NumericalType.IsMinimal`: no minus-one index.

## Implementation notes

The index set `{1, …, n}` is `Fin T.componentCount`. A relabelling is an `Equiv` between the two
index types, which also records that the two numerical types have the same number of components.
The genus of a numerical type is determined by its numerical data and so is not a field.

## References

* [Stacks Project, Tag 0C6Z](https://stacks.math.columbia.edu/tag/0C6Z)
* [Stacks Project, Tag 0C70](https://stacks.math.columbia.edu/tag/0C70)
* [Stacks Project, Tag 0C76](https://stacks.math.columbia.edu/tag/0C76)
* [Stacks Project, Tag 0C7A](https://stacks.math.columbia.edu/tag/0C7A)
* [Stacks Project, Tag 0C7E](https://stacks.math.columbia.edu/tag/0C7E)
-/

@[expose] public section

open scoped BigOperators

namespace AlgebraicGeometry

/-! ### Numerical types -/

/-- A **numerical type**: positive integer multiplicities and weights, nonnegative component
genera, and a connected symmetric intersection matrix whose weighted rows vanish and whose entries
in each row are divisible by that row's weight. -/
@[stacks 0C6Z]
public structure NumericalType where
  /-- The number of components. -/
  componentCount : ℕ
  /-- A numerical type has at least one component. -/
  componentCount_pos : 0 < componentCount
  /-- The multiplicity `mᵢ` of each component. -/
  multiplicity : Fin componentCount → ℤ
  /-- The intersection number `aᵢⱼ` of two components. -/
  intersection : Fin componentCount → Fin componentCount → ℤ
  /-- The weight `wᵢ` of each component. -/
  weight : Fin componentCount → ℤ
  /-- The genus `gᵢ` attached to each component. -/
  componentGenus : Fin componentCount → ℤ
  /-- Every multiplicity is positive. -/
  multiplicity_pos : ∀ i, 0 < multiplicity i
  /-- Every weight is positive. -/
  weight_pos : ∀ i, 0 < weight i
  /-- Every component genus is nonnegative. -/
  componentGenus_nonneg : ∀ i, 0 ≤ componentGenus i
  /-- The intersection matrix is symmetric. -/
  intersection_symm : ∀ i j, intersection i j = intersection j i
  /-- Off-diagonal intersection numbers are nonnegative. -/
  intersection_nonneg : ∀ i j, i ≠ j → 0 ≤ intersection i j
  /-- No proper nonempty collection of components has zero intersection with its complement. -/
  connected : ¬ ∃ I : Set (Fin componentCount),
    I.Nonempty ∧ (I ≠ Set.univ) ∧
      (∀ i, i ∈ I → ∀ j, j ∉ I → intersection i j = 0)
  /-- The intersection matrix annihilates the multiplicity vector. -/
  intersection_mul_multiplicity : ∀ i, ∑ j, intersection i j * multiplicity j = 0
  /-- The weight of a component divides every entry in its row of the intersection matrix. -/
  weight_dvd_intersection : ∀ i j, weight i ∣ intersection i j

/-- The component index type of a numerical type is nonempty. -/
public instance (T : NumericalType) : NeZero T.componentCount :=
  ⟨Nat.ne_of_gt T.componentCount_pos⟩

namespace NumericalType

/-! ### Equivalence of numerical types -/

/-- Two numerical types are **equivalent** if a bijective relabelling of their components preserves
all four families of numerical data. -/
@[stacks 0C70]
public def Equivalent (T T' : NumericalType) : Prop :=
  ∃ e : Fin T.componentCount ≃ Fin T'.componentCount,
    (∀ i, T.multiplicity i = T'.multiplicity (e i)) ∧
    (∀ i j, T.intersection i j = T'.intersection (e i) (e j)) ∧
    (∀ i, T.weight i = T'.weight (e i)) ∧
    (∀ i, T.componentGenus i = T'.componentGenus (e i))

/-! ### Minus-one indices -/

/-- An index is a minus-one index if its component genus is zero and its diagonal intersection
number is the negative of its weight. -/
@[stacks 0C76]
public abbrev IsMinusOneIndex (T : NumericalType) (i : Fin T.componentCount) : Prop :=
  T.componentGenus i = 0 ∧ T.intersection i i = -T.weight i

/-! ### Minimal numerical types -/

/-- A numerical type is **minimal** if it has no minus-one index. -/
@[stacks 0C7A] public abbrev IsMinimal (T : NumericalType) : Prop :=
  ¬ ∃ i : Fin T.componentCount, IsMinusOneIndex T i

/-! ### Minus-two indices -/

/-- An index is a minus-two index if its component genus is zero and its diagonal intersection
number is negative twice its weight. -/
@[stacks 0C7E]
public abbrev IsMinusTwoIndex (T : NumericalType) (i : Fin T.componentCount) : Prop :=
  T.componentGenus i = 0 ∧ T.intersection i i = -2 * T.weight i

end NumericalType

end AlgebraicGeometry
