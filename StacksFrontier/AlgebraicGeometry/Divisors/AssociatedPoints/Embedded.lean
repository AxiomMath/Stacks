module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
public import StacksCore.Tactic.StacksAttribute

/-!
# Embedded points and embedded components

An *embedded* associated point of a sheaf of modules is an associated point which is a proper
specialization of another associated point. The embedded points of a scheme are the embedded
associated points of its structure sheaf, and their closures are the embedded components.

## Main definitions

* `AlgebraicGeometry.IsEmbeddedAssociatedPoint`: an embedded associated point of a sheaf of
  modules.
* `AlgebraicGeometry.IsEmbeddedPoint`: an embedded point of a scheme.
* `AlgebraicGeometry.IsEmbeddedComponent`: an embedded component of a scheme.
* `AlgebraicGeometry.HasNoEmbeddedAssociatedPoints` and
  `AlgebraicGeometry.HasNoEmbeddedPoints`: the corresponding absence predicates.

## Main results

* `Topology.eq_of_specializes_isGenericPoint`: a point specializing to the generic point of an
  irreducible component is that point.

## Implementation notes

`AlgebraicGeometry.IsEmbeddedAssociatedPoint`, `AlgebraicGeometry.IsEmbeddedPoint` and
`AlgebraicGeometry.IsEmbeddedComponent` correspond respectively to parts (1), (2) and (3) of the
definition in Stacks 05AK. As for associated points, quasi-coherence is not needed to form these
notions, so they are defined for every sheaf of modules. The condition that the specializing point
be different records the word "another", and hence the failure of maximality. An embedded component
is specified as the closure of its embedded point; such a closure is automatically closed and
irreducible. All the predicates are abbreviations, so that clients can use their logical forms
directly.

The specialization relation is Mathlib's `Specializes`, written `x' ⤳ x`.

## References

* [Stacks Project, Tag 05AK](https://stacks.math.columbia.edu/tag/05AK)
-/

@[expose] public section

universe u

namespace Topology

/-- A point specializing to the generic point of an irreducible component is that point: its
closure would otherwise be a strictly larger irreducible closed set. -/
lemma eq_of_specializes_isGenericPoint {T : Type*} [TopologicalSpace T] [T0Space T] {Z : Set T}
    (hZ : Z ∈ irreducibleComponents T) {x : T} (hx : IsGenericPoint x Z) {y : T}
    (hyx : y ⤳ x) : y = x := by
  have hsub : Z ⊆ closure ({y} : Set T) := by
    rw [← hx.def]
    exact closure_minimal (by simpa using specializes_iff_mem_closure.mp hyx) isClosed_closure
  exact (hx.eq (show IsGenericPoint y Z from
    (hZ.2 isIrreducible_singleton.closure hsub).antisymm hsub)).symm

end Topology

namespace AlgebraicGeometry

/-- **Stacks 05AK, part (1).** An associated point is *embedded* when it is a proper
specialization of another associated point. -/
@[stacks 05AK "part (1)"]
noncomputable abbrev IsEmbeddedAssociatedPoint {X : Scheme.{u}} (F : X.Modules) (x : X) : Prop :=
  Stacks.Divisors.IsAssociatedPoint F x ∧
    ∃ x' : X, Stacks.Divisors.IsAssociatedPoint F x' ∧ x' ⤳ x ∧ x' ≠ x

/-- A sheaf of modules has no embedded associated points. -/
noncomputable abbrev HasNoEmbeddedAssociatedPoints {X : Scheme.{u}} (F : X.Modules) : Prop :=
  ∀ x : X, ¬ IsEmbeddedAssociatedPoint F x

/-- **Stacks 05AK, part (2).** An embedded point of a scheme is an embedded associated point of
its structure sheaf. -/
@[stacks 05AK "part (2)"]
noncomputable abbrev IsEmbeddedPoint (X : Scheme.{u}) (x : X) : Prop :=
  IsEmbeddedAssociatedPoint (SheafOfModules.unit X.ringCatSheaf) x

/-- A scheme has no embedded points. -/
noncomputable abbrev HasNoEmbeddedPoints (X : Scheme.{u}) : Prop := ∀ x : X, ¬ IsEmbeddedPoint X x

/-- **Stacks 05AK, part (3).** An embedded component is the closure of an embedded point. -/
@[stacks 05AK "part (3)"]
noncomputable abbrev IsEmbeddedComponent (X : Scheme.{u}) (Z : Set X) : Prop :=
  ∃ x : X, IsEmbeddedPoint X x ∧ Z = closure ({x} : Set X)

end AlgebraicGeometry
