module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Basic

/-!
# Modifications of integral schemes

A modification of an integral scheme is a proper birational morphism from an integral scheme.
Unlike an alteration, a modification is required to be birational rather than merely generically
finite, so it induces an isomorphism of function fields.

## Main definitions

* `AlgebraicGeometry.IsModification`: the predicate that a morphism to an integral scheme is a
  modification.

## Main results

* `AlgebraicGeometry.isModification_iff` characterizes modifications by their three defining
  properties.

## Implementation notes

The integrality of the target is retained as a typeclass assumption expressing the context in
which the notion is defined. The remaining conditions form an abbreviation, so the existing APIs
for birationality, properness, and integrality are directly available after taking the
corresponding projection.

## References

* [Stacks Project, Tag 0AAZ](https://stacks.math.columbia.edu/tag/0AAZ)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A morphism `f : X' ⟶ X` to an integral scheme is a **modification** if `X'` is
integral and `f` is birational and proper. -/
@[stacks 0AAZ]
public abbrev IsModification {X X' : Scheme.{u}} [IsIntegral X] (f : X' ⟶ X) : Prop :=
  IsBirational f ∧ IsProper f ∧ IsIntegral X'

/-- The defining characterization of a modification. -/
public theorem isModification_iff {X X' : Scheme.{u}} [IsIntegral X] (f : X' ⟶ X) :
    IsModification f ↔ IsBirational f ∧ IsProper f ∧ IsIntegral X' :=
  Iff.rfl

namespace IsModification

/-- A modification is birational. -/
public theorem isBirational {X X' : Scheme.{u}} [IsIntegral X] {f : X' ⟶ X}
    (hf : IsModification f) : IsBirational f := hf.1

/-- A modification is proper. -/
public theorem isProper {X X' : Scheme.{u}} [IsIntegral X] {f : X' ⟶ X}
    (hf : IsModification f) : IsProper f := hf.2.1

/-- The source of a modification is integral. -/
public theorem source_isIntegral {X X' : Scheme.{u}} [IsIntegral X] {f : X' ⟶ X}
    (hf : IsModification f) : IsIntegral X' := hf.2.2

end IsModification

/-- A proper birational morphism from an integral scheme to an integral scheme is a
modification. -/
public theorem isModification_of {X X' : Scheme.{u}} [IsIntegral X] (f : X' ⟶ X)
    (hbir : IsBirational f) (hproper : IsProper f) (hX' : IsIntegral X') :
    IsModification f :=
  ⟨hbir, hproper, hX'⟩

/-- The identity of an integral scheme is a modification: it is proper, and birational because
it is the identity on generic points and on every stalk. -/
public theorem isModification_id (X : Scheme.{u}) [IsIntegral X] :
    IsModification (CategoryTheory.CategoryStruct.id X) :=
  ⟨⟨by simpa using Set.bijOn_id (genericPoints X), fun _ _ => inferInstance⟩,
    inferInstance, inferInstance⟩

end AlgebraicGeometry
