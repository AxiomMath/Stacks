module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Dimension.Equidimensional
public import StacksFrontier.Topology.Dimension.Krull

/-!
# Relative dimension of a morphism of schemes

For a morphism of schemes locally of finite type, the relative dimension at a point of the
source is the local Krull dimension of the scheme-theoretic fibre through that point. Bounding
it pointwise, and then at every point, gives the two notions of relative dimension at most `d`.
A morphism is said to have relative dimension `d` when the stronger, uniform condition holds:
every nonempty fibre is equidimensional of dimension `d`.

## Main definitions

* `AlgebraicGeometry.RelativeDimensionLEAt` is relative dimension at most `d` at a point.
* `AlgebraicGeometry.RelativeDimensionLE` is relative dimension at most `d` at every point.
* `AlgebraicGeometry.RelativeDimension` says that every nonempty fibre is equidimensional of
  dimension `d`.

## Main results

The `*_iff` lemmas expose the defining pointwise and fibrewise conditions, and
`AlgebraicGeometry.RelativeDimensionLE.at` specializes a global bound to a point.

## Implementation notes

The point of the fibre corresponding to `x : X` is `f.asFiber x`. The dimension of a nonempty
fibre is represented by its topological Krull dimension; together with
`TopologicalSpace.Equidimensional`, this says precisely that the fibre is equidimensional of the
specified dimension. The local finite-type assumption is carried as a typeclass argument, in
accordance with Mathlib's convention for properties of scheme morphisms.

## References

* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A locally finite type morphism `f : X ⟶ S` has relative dimension at most `d` at
`x : X` if the local Krull dimension of the fibre over `f x` at its point corresponding to `x`
is at most `d`. -/
@[stacks 02NJ "part (1)"]
public def RelativeDimensionLEAt {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (d : ℕ) (x : X) : Prop :=
  topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ (d : WithBot ℕ∞)

/-- A locally finite type morphism has relative dimension at most `d` if it does so at every
point of its source. -/
@[stacks 02NJ "part (2)"]
public abbrev RelativeDimensionLE {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (d : ℕ) : Prop :=
  ∀ x : X, RelativeDimensionLEAt f d x

/-- A locally finite type morphism has relative dimension `d` if every nonempty fibre is
equidimensional and has topological Krull dimension `d`. -/
@[stacks 02NJ "part (3)"]
public def RelativeDimension {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (d : ℕ) : Prop :=
  ∀ s : S, Nonempty (f.fiber s) →
    (TopologicalSpace.Equidimensional (f.fiber s) ∧
      topologicalKrullDim (f.fiber s) = (d : WithBot ℕ∞))

/-- The defining local-dimension inequality for relative dimension at most `d` at a point. -/
@[simp]
public theorem relativeDimensionLEAt_iff {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (d : ℕ) (x : X) :
    RelativeDimensionLEAt f d x ↔
      topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ (d : WithBot ℕ∞) :=
  Iff.rfl

/-- Relative dimension is at most `d` exactly when it is at most `d` at every point. -/
@[simp]
public theorem relativeDimensionLE_iff {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (d : ℕ) :
    RelativeDimensionLE f d ↔ ∀ x : X, RelativeDimensionLEAt f d x :=
  Iff.rfl

/-- The fibrewise characterization of a morphism of relative dimension `d`. -/
@[simp]
public theorem relativeDimension_iff {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (d : ℕ) :
    RelativeDimension f d ↔
      ∀ s : S, Nonempty (f.fiber s) →
        (TopologicalSpace.Equidimensional (f.fiber s) ∧
          topologicalKrullDim (f.fiber s) = (d : WithBot ℕ∞)) :=
  Iff.rfl

/-- A global relative-dimension bound holds at each point of the source. -/
public theorem RelativeDimensionLE.at {X S : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] {d : ℕ} (hf : RelativeDimensionLE f d) (x : X) :
    RelativeDimensionLEAt f d x :=
  hf x

end AlgebraicGeometry
