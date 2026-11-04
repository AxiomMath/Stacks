module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.CompletelyDecomposed
public import StacksCore.Tactic.StacksAttribute

/-!
# Envelopes of schemes

An envelope of a scheme is a proper morphism to it which is completely decomposed. Envelopes
are the morphisms along which Chow groups may be computed by descent.

## Main definitions

* `AlgebraicGeometry.IsEnvelope` says that a morphism of schemes is an envelope.

## Main results

* `AlgebraicGeometry.isEnvelope_iff` characterizes envelopes by properness and complete
  decomposition.
* `AlgebraicGeometry.IsEnvelope.isProper` and
  `AlgebraicGeometry.IsEnvelope.isCompletelyDecomposed` give the two defining properties.
* `AlgebraicGeometry.isEnvelope_of` builds an envelope from the two properties.

## Implementation notes

The notion is an abbreviation for the conjunction of Mathlib's properness predicate and the
completely decomposed predicate `AlgebraicGeometry.IsCompletelyDecomposed`.

## References

* [Stacks Project, Tag 0GU5](https://stacks.math.columbia.edu/tag/0GU5)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- An **envelope** is a proper, completely decomposed morphism of schemes. -/
@[stacks 0GU5]
abbrev IsEnvelope {X Y : Scheme.{u}} (f : Y ⟶ X) : Prop :=
  IsProper f ∧ IsCompletelyDecomposed f

/-- A morphism is an envelope exactly when it is proper and completely decomposed. -/
theorem isEnvelope_iff {X Y : Scheme.{u}} (f : Y ⟶ X) :
    IsEnvelope f ↔ IsProper f ∧ IsCompletelyDecomposed f := Iff.rfl

/-- An envelope is proper. -/
theorem IsEnvelope.isProper {X Y : Scheme.{u}} {f : Y ⟶ X} (hf : IsEnvelope f) :
    IsProper f := hf.1

/-- An envelope is completely decomposed. -/
theorem IsEnvelope.isCompletelyDecomposed {X Y : Scheme.{u}} {f : Y ⟶ X} (hf : IsEnvelope f) :
    IsCompletelyDecomposed f := hf.2

/-- A proper, completely decomposed morphism is an envelope. -/
theorem isEnvelope_of {X Y : Scheme.{u}} (f : Y ⟶ X) (hproper : IsProper f)
    (hcd : IsCompletelyDecomposed f) : IsEnvelope f := ⟨hproper, hcd⟩

end AlgebraicGeometry
