module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TopologicalInvarianceFundamental.UniversalHomeomorphismEquivalence

/-!
# Finiteness of étale morphisms along a universal homeomorphism

Let `f : X ⟶ Y` be a universal homeomorphism and `g : V ⟶ Y` étale. Then `g` is finite if and
only if its base change `V ×_Y X ⟶ X` is finite. One direction is stability of finiteness under
base change; the other is
`AlgebraicGeometry.isFinite_of_isFinite_pullback_snd_of_universalHomeomorphism`, the step that
restricts the equivalence of small étale sites of [Stacks, Tag 04DZ] to the finite étale covers
in the proof of [Stacks, Tag 0BQN].

## Main results

* `AlgebraicGeometry.isFinite_pullback_snd_iff_of_universalHomeomorphism` — the equivalence.

## References

* [Stacks Project, Tag 0BQN](https://stacks.math.columbia.edu/tag/0BQN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Finiteness of an étale morphism is detected on a universal homeomorphism.** Let
`f : X ⟶ Y` be a universal homeomorphism and let `g : V ⟶ Y` be étale. Then `g` is finite if
and only if its base change along `f` is finite. -/
theorem isFinite_pullback_snd_iff_of_universalHomeomorphism {X Y : Scheme.{u}} (f : X ⟶ Y)
    [UniversalHomeomorphism f] {V : Scheme.{u}} (g : V ⟶ Y) [Etale g] :
    IsFinite (pullback.snd g f) ↔ IsFinite g :=
  ⟨fun _ ↦ isFinite_of_isFinite_pullback_snd_of_universalHomeomorphism f g, fun hg ↦
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsFinite)
      (IsPullback.of_hasPullback g f) hg⟩

end AlgebraicGeometry

end
