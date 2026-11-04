module

public import StacksFrontier.AlgebraicGeometry.AssociatedPointsMono.Basic
public import StacksFrontier.Topology.Specialization.Defs
public import Mathlib.Topology.Sober

/-!
# Embedded points and embedded components

An associated point of a sheaf of modules is *embedded* when it is a proper specialization of
another associated point, so that it is not maximal for the specialization order among the
associated points. The embedded points of a scheme are the embedded associated points of its
structure sheaf, and their closures are its embedded components.

## Main definitions

* `Stacks.AlgebraicGeometry.EmbeddedPoints.IsEmbeddedAssociatedPoint`: an embedded associated
  point of a sheaf of modules.
* `Stacks.AlgebraicGeometry.EmbeddedPoints.IsEmbeddedPoint`: an embedded point of a scheme.
* `Stacks.AlgebraicGeometry.EmbeddedPoints.IsEmbeddedComponent`: an embedded component of a
  scheme.
* `Stacks.AlgebraicGeometry.EmbeddedPoints.HasNoEmbeddedAssociatedPoints` and
  `Stacks.AlgebraicGeometry.EmbeddedPoints.HasNoEmbeddedPoints`: the absence predicates.

## Implementation notes

Quasi-coherence is not needed to form these notions, so, as for associated points, they are
defined for every sheaf of modules; in particular they apply to the quasi-coherent sheaves of
the source. The specialization relation is Mathlib's `Specializes`, which
`StacksFrontier/Topology/Specialization/Defs.lean` records as the Stacks specialization relation
of Tag 0061: `x' ⤳ x` says that `x` lies in the closure of `{x'}`. The requirement that the
specializing point be a *different* associated point is the word "another" of the source, and
is what makes the condition a failure of maximality rather than a triviality.

An embedded component is specified as the closure of its embedded point; such a closure is
automatically closed and irreducible. All the predicates are abbreviations, so that clients can
use their logical forms directly without unfolding lemmas.

## References

* [Stacks Project, Tag 05AK](https://stacks.math.columbia.edu/tag/05AK)
* [Stacks Project, Tag 02OJ](https://stacks.math.columbia.edu/tag/02OJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.AssociatedPointsMono

namespace Stacks.AlgebraicGeometry.EmbeddedPoints

universe u

variable {X : Scheme.{u}}

/-- **Stacks 02OJ, part (3).** A point is associated to a scheme when it is associated to its
structure sheaf. -/
public noncomputable abbrev IsSchemeAssociatedPoint (X : Scheme.{u}) (x : X) : Prop :=
  IsAssociatedPoint (SheafOfModules.unit X.ringCatSheaf) x

/-- **Stacks 05AK, part (1).** An associated point of a sheaf of modules is *embedded* when it
is a proper specialization of another associated point. -/
public noncomputable abbrev IsEmbeddedAssociatedPoint (F : X.Modules) (x : X) : Prop :=
  IsAssociatedPoint F x ∧ ∃ x' : X, IsAssociatedPoint F x' ∧ x' ⤳ x ∧ x' ≠ x

/-- A sheaf of modules has no embedded associated points. -/
public noncomputable abbrev HasNoEmbeddedAssociatedPoints (F : X.Modules) : Prop :=
  ∀ x : X, ¬ IsEmbeddedAssociatedPoint F x

/-- **Stacks 05AK, part (2).** An embedded point of a scheme is an embedded associated point of
its structure sheaf. -/
public noncomputable abbrev IsEmbeddedPoint (X : Scheme.{u}) (x : X) : Prop :=
  IsEmbeddedAssociatedPoint (SheafOfModules.unit X.ringCatSheaf) x

/-- A scheme has no embedded points. -/
public noncomputable abbrev HasNoEmbeddedPoints (X : Scheme.{u}) : Prop :=
  ∀ x : X, ¬ IsEmbeddedPoint X x

/-- **Stacks 05AK, part (3).** An embedded component of a scheme is the closure of an embedded
point. -/
public noncomputable abbrev IsEmbeddedComponent (X : Scheme.{u}) (Z : Set X) : Prop :=
  ∃ x : X, IsEmbeddedPoint X x ∧ Z = closure ({x} : Set X)

/-- An embedded point is an associated point which is not maximal for the specialization order
among the associated points. This is the reading of Tag 05AK that `HasNoEmbeddedPoints` is used
through: a scheme has no embedded points exactly when every associated point is maximal. -/
public theorem isEmbeddedPoint_iff (X : Scheme.{u}) (x : X) :
    IsEmbeddedPoint X x ↔
      IsSchemeAssociatedPoint X x ∧
        ∃ x' : X, IsSchemeAssociatedPoint X x' ∧ x' ⤳ x ∧ x' ≠ x :=
  Iff.rfl

/-- A scheme has no embedded points exactly when no associated point is a proper specialization
of another associated point. -/
public theorem hasNoEmbeddedPoints_iff (X : Scheme.{u}) :
    HasNoEmbeddedPoints X ↔
      ∀ x x' : X, IsSchemeAssociatedPoint X x → IsSchemeAssociatedPoint X x' → x' ⤳ x → x' = x :=
  ⟨fun h x x' hx hx' hspec => by
    by_contra hne
    exact h x ⟨hx, x', hx', hspec, hne⟩,
   fun h x hx => hx.2.choose_spec.2.2 (h x _ hx.1 hx.2.choose_spec.1 hx.2.choose_spec.2.1)⟩

/-- An embedded component is closed. -/
public theorem isClosed_of_isEmbeddedComponent {Z : Set X} (hZ : IsEmbeddedComponent X Z) :
    IsClosed Z := by
  obtain ⟨x, -, rfl⟩ := hZ
  exact isClosed_closure

/-- An embedded component is irreducible. -/
public theorem isIrreducible_of_isEmbeddedComponent {Z : Set X} (hZ : IsEmbeddedComponent X Z) :
    IsIrreducible Z := by
  obtain ⟨x, -, rfl⟩ := hZ
  exact (isIrreducible_singleton (x := x)).closure

end Stacks.AlgebraicGeometry.EmbeddedPoints

end
