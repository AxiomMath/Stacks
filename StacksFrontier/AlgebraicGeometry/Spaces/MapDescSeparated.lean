module

public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent

/-!
# An isomorphism of presheaves is a closed immersion of algebraic spaces

An isomorphism of presheaves on the big fppf site of a scheme `S` is a closed immersion of
algebraic spaces over `S`.

## Main results

* `AlgebraicGeometry.Space.isClosedImmersion_of_isIso`: an isomorphism of presheaves on the big
  fppf site of `S` is a closed immersion of algebraic spaces.

## References

* [Stacks Project, Tag 03KN](https://stacks.math.columbia.edu/tag/03KN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- An isomorphism of presheaves on the big fppf site of `S` is a closed immersion of algebraic
spaces. -/
theorem isClosedImmersion_of_isIso (f : X ⟶ Y) [IsIso f] : IsClosedImmersion B S hS f := by
  refine ⟨Functor.relativelyRepresentable.of_isIso yoneda f, fun a b g fst snd sq => ?_⟩
  have : IsIso (yoneda.map snd) := sq.isIso_snd_of_isIso
  have : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map _
  change AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map snd)
  infer_instance

end AlgebraicGeometry.Space

end
