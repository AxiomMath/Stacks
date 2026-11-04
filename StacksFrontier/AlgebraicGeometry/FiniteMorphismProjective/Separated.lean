module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# A finite morphism factoring through a separated morphism factors through it by a closed immersion

The last step of the proof of [Stacks, Tag 0B3I] is this: the morphism `σ : X ⟶ 𝐏(E)` built from
the generators is an immersion — a closed immersion into an affine chart, followed by the open
immersion of that chart — and *because `X` is finite over the base* its image is closed, so `σ`
is a closed immersion. The source spends three citations on it (Lemma 29.45.11, Lemma 29.42.7 and
Schemes, Lemma 26.10.4); over Mathlib's API it is two steps:

* an immersion is a monomorphism, because it is a preimmersion;
* a morphism whose composite with a *separated* morphism is finite is itself finite.

A finite monomorphism is a closed immersion, which is Mathlib's
`AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono`.

Nothing in this file mentions `Proj` or a projective bundle: the statement is about an arbitrary
separated morphism `p` out of an arbitrary scheme, so it applies to `𝐏ⁿ_S ⟶ S`, to the projective
bundle `𝐏(E) ⟶ S` once that morphism is known separated, and to any other target.

## Main results

* `Stacks.FiniteMorphismProjective.isClosedImmersion_of_isImmersion`: **an immersion over a
  separated morphism, whose composite with it is finite, is a closed immersion.**
* `Stacks.FiniteMorphismProjective.isClosedImmersion_of_isImmersion_of_eq`: the same with the
  composite replaced by a morphism equal to it, which is the form the applications use.

## Implementation notes

The hypothesis is finiteness of the composite rather than finiteness of the source over the base
because that is the shape the hypothesis of the tagged statement has: `f = σ ≫ p` is finite, and `σ` is the
morphism whose closedness is wanted. Universal closedness would be enough for the topological
half — a universally closed morphism has closed image, so
`AlgebraicGeometry.IsClosedImmersion.of_isPreimmersion` applies — but finiteness is what the statement
gives and it reaches the conclusion without passing through the range at all.

## References

* [Stacks Project, Tag 0B3I](https://stacks.math.columbia.edu/tag/0B3I)
* [Stacks Project, Tag 01W6](https://stacks.math.columbia.edu/tag/01W6)
* [Stacks Project, Tag 01IQ](https://stacks.math.columbia.edu/tag/01IQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.FiniteMorphismProjective

universe u

/-- **An immersion over a separated morphism whose composite with it is finite is a closed
immersion.** The immersion is a monomorphism, and it is finite because finiteness of a composite
with a separated morphism descends to the first factor; a finite monomorphism is a closed
immersion. -/
public theorem isClosedImmersion_of_isImmersion {X P S : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ S)
    [IsImmersion i] [IsSeparated p] [IsFinite (i ≫ p)] : IsClosedImmersion i := by
  have hfin : IsFinite i :=
    MorphismProperty.HasOfPostcompProperty.of_postcomp (W := @IsFinite)
      (W' := @IsSeparated) i p inferInstance inferInstance
  exact (IsClosedImmersion.iff_isFinite_and_mono i).2 ⟨hfin, inferInstance⟩

/-- If `i : X ⟶ P` is an immersion, `p : P ⟶ S` is separated and `i ≫ p = f` for a finite
morphism `f : X ⟶ S`, then `i` is a closed immersion. -/
public theorem isClosedImmersion_of_isImmersion_of_eq {X P S : Scheme.{u}} (i : X ⟶ P)
    (p : P ⟶ S) {f : X ⟶ S} [IsImmersion i] [IsSeparated p] [IsFinite f] (hf : i ≫ p = f) :
    IsClosedImmersion i :=
  have : IsFinite (i ≫ p) := hf ▸ ‹IsFinite f›
  isClosedImmersion_of_isImmersion i p

end Stacks.FiniteMorphismProjective

end
