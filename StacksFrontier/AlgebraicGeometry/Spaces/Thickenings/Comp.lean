module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings

/-!
# Composition of thickenings of algebraic spaces

If `X ⊂ X'` is a thickening of a closed subspace `X' ⊂ X''` of an algebraic space `X''`, then
`X` is a thickening of `X''`. The composite closed subspace is the image of `X` under the
inclusion of `X'`.

## Main results

* `AlgebraicGeometry.Space.isThickening_image`: **Stacks 0BPH**, thickenings of algebraic
  spaces compose.

## Implementation notes

A closed subspace is a subfunctor of its ambient algebraic space, so the composite of the two
inclusions is not itself the inclusion of a subfunctor of `X''`; the subfunctor it presents is
`CategoryTheory.Subfunctor.image`, which `CategoryTheory.Subfunctor.range_comp` identifies with
the range of the composite. The proof therefore proves the statement for that range, where the
canonical comparison `CategoryTheory.Subfunctor.toRange` is an isomorphism because the
composite of the two inclusions is a monomorphism, and transports it along the identification.
Both halves of the definition of a thickening then follow from the corresponding statement for
the composite: closed immersions of algebraic spaces are stable under composition, and
surjectivity on points is functorial.

## References

* [Stacks Project, Tag 0BPH](https://stacks.math.columbia.edu/tag/0BPH)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0BPH.** A thickening `X ⊂ X'` of a closed subspace `X' ⊂ X''` of an algebraic
space `X''` which is itself a thickening of `X''` presents `X` as a thickening of `X''`, the
composite closed subspace being the image of `X` under the inclusion of `X'`. -/
@[stacks 0BPH]
theorem isThickening_image (X'' : AlgebraicSpaces B S hS) (X' : Subfunctor X''.1)
    (hX' : IsThickening B S hS X'' X') (X : Subfunctor X'.toFunctor)
    (hX : IsThickening B S hS ⟨X'.toFunctor, hX'.1.1⟩ X) :
    IsThickening B S hS X'' (X.image X'.ι) := by
  have hrange : Subfunctor.range (X.ι ≫ X'.ι) = X.image X'.ι := by
    rw [Subfunctor.range_comp, Subfunctor.range_ι]
  rw [← hrange]
  have : Mono (X.ι ≫ X'.ι) := mono_comp _ _
  set m : X.toFunctor ⟶ X''.1 := X.ι ≫ X'.ι with hm
  have hclosed : IsClosedImmersion B S hS m := by
    have : MorphismProperty.IsStableUnderComposition
        (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsMultiplicative.toIsStableUnderComposition
    have := MorphismProperty.IsStableUnderComposition.inverseImage
      (P := (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}))
      (BigFppfOver.toScheme B S hS)
    exact MorphismProperty.comp_mem _ X.ι X'.ι hX.1.2 hX'.1.2
  have hsurj : Function.Surjective (pointsMap B S hS X.toFunctor m) := by
    rw [hm, pointsMap_comp]
    exact hX'.2.comp hX.2
  refine ⟨⟨isAlgebraicSpace_of_iso B S hS (asIso (Subfunctor.toRange m)).symm hX.1.1, ?_⟩, ?_⟩
  · exact (MorphismProperty.cancel_left_of_respectsIso _ (Subfunctor.toRange m)
      (Subfunctor.range m).ι).mp (by rwa [Subfunctor.toRange_ι])
  · apply Function.Surjective.of_comp (g := pointsMap B S hS X.toFunctor (Subfunctor.toRange m))
    rwa [← pointsMap_comp, Subfunctor.toRange_ι]

end AlgebraicGeometry.Space

end
