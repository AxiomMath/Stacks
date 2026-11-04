module

public import Mathlib.Topology.Defs.Basic

/-!
# Isolated points

## Main results

* `IsIsolatedPoint` (Stacks 06RM): a point of a topological space is isolated when the singleton it
  spans is open.
* `isIsolatedPoint_iff`: unfolding of the definition.
-/

@[expose] public section

/-- **Stacks 06RM.** A point `x` of a topological space `X` is *isolated* if `{x}` is open in
`X`. -/
@[stacks 06RM]
def IsIsolatedPoint {X : Type*} [TopologicalSpace X] (x : X) : Prop :=
  IsOpen ({x} : Set X)

/-- A point is isolated exactly when the singleton it spans is open; this unfolds
`IsIsolatedPoint`. -/
theorem isIsolatedPoint_iff {X : Type*} [TopologicalSpace X] (x : X) :
    IsIsolatedPoint x ↔ IsOpen ({x} : Set X) := Iff.rfl
