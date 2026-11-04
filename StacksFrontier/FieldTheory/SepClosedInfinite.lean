module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.Perfect

/-!
# A separably closed field is infinite

A finite field is perfect, so a finite separably closed field would be algebraically closed;
algebraically closed fields are infinite.

## Main results

* `IsSepClosed.infinite`: a separably closed field is infinite.

## Implementation notes

Mathlib's analogue for `IsAlgClosed` fields is an instance, but this one must not be: making it
one adds a branch that every unsolvable `Infinite _` goal has to explore, and that is enough to
push `AlgebraicGeometry.Space.exists_mono_biproduct_idealSheaf_cokernel_support_subset` over the
heartbeat limit. Lowering the priority does not help, since priority reorders a search without
pruning it. Apply it by name.
-/

@[expose] public section

/-- A separably closed field is infinite: a finite field is perfect, so a finite separably
closed field would be algebraically closed, and algebraically closed fields are infinite.

Not an instance: see the implementation notes. Apply it by name. -/
public theorem IsSepClosed.infinite (K : Type*) [Field K] [IsSepClosed K] : Infinite K :=
  not_finite_iff_infinite.mp fun _ ↦ not_finite K

end
