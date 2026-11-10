module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms

/-!
# Permanence of local separatedness

A morphism of algebraic spaces over a scheme `S` is locally separated when its relative
diagonal is an immersion. This file records the two permanence properties of that
condition: it is stable under arbitrary base change, and it passes from a composite to the
first factor.

## Main results

* `AlgebraicGeometry.Space.isLocallySeparated_baseChange`: every base change of a locally
  separated morphism is locally separated.
* `AlgebraicGeometry.Space.isLocallySeparated_of_comp`: if a composite is locally
  separated, so is its first factor.

## Implementation notes

Both results are purely formal consequences of the fact that the immersion property of
morphisms of algebraic spaces is `CategoryTheory.MorphismProperty.presheaf` applied to a
property of scheme morphisms, hence stable under base change by
`CategoryTheory.MorphismProperty.relative_isStableUnderBaseChange`. Local separatedness is
then the `CategoryTheory.MorphismProperty.diagonal` of that property, so base-change
stability is inherited and the statement for the first factor of a composite reduces to the
Cartesian square `CategoryTheory.Limits.diagonal_comp_isPullback` relating the two relative
diagonals.

As in `StacksFrontier/AlgebraicGeometry/Spaces/Morphisms.lean`, nothing here uses the
algebraic-space axioms, so both statements are given for an arbitrary morphism of presheaves
on the big fppf site of `S`; for morphisms of algebraic spaces they are the source
statements.

## References

* [Stacks Project, Tag 03KL](https://stacks.math.columbia.edu/tag/03KL)
* [Stacks Project, Tag 03KR](https://stacks.math.columbia.edu/tag/03KR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Limits

/-- The relative diagonal of a composite `f ≫ g` is obtained from the relative diagonal of
`f` by the base change along `CategoryTheory.Limits.pullback.mapDesc f f g`. -/
private lemma diagonal_comp_isPullback
    {C : Type u} [Category C] [HasPullbacks C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    IsPullback (𝟙 X) (pullback.diagonal f) (pullback.diagonal (f ≫ g))
      (pullback.mapDesc f f g) := by
  have hmfst : pullback.mapDesc f f g ≫ pullback.fst (f ≫ g) (f ≫ g) =
      pullback.fst f f := by
    simp only [pullback.mapDesc, pullback.map, pullback.lift_fst, Category.comp_id]
  have hmsnd : pullback.mapDesc f f g ≫ pullback.snd (f ≫ g) (f ≫ g) =
      pullback.snd f f := by
    simp only [pullback.mapDesc, pullback.map, pullback.lift_snd, Category.comp_id]
  refine IsPullback.mk' ?_ (fun _ _ _ h₁ _ => by simpa using h₁) ?_
  · apply pullback.hom_ext <;> simp [hmfst, hmsnd]
  · intro T a b h
    refine ⟨a, by simp, ?_⟩
    have hfst : a = b ≫ pullback.fst f f := by
      simpa [hmfst] using congrArg (· ≫ pullback.fst (f ≫ g) (f ≫ g)) h
    have hsnd : a = b ≫ pullback.snd f f := by
      simpa [hmsnd] using congrArg (· ≫ pullback.snd (f ≫ g) (f ≫ g)) h
    apply pullback.hom_ext
    · simpa [Category.assoc, pullback.diagonal_fst] using hfst
    · simpa [Category.assoc, pullback.diagonal_snd] using hsnd

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

/-- **Stacks 03KL.** Local separatedness of a morphism of algebraic spaces is
preserved by arbitrary base change of its target. -/
theorem isLocallySeparated_baseChange
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hf : IsLocallySeparated B S hS f) :
    IsLocallySeparated B S hS (pullback.snd f g) := by
  let P := MorphismProperty.presheaf <| MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have : P.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  change P.diagonal (pullback.snd f g)
  exact P.diagonal.pullback_snd f g (show P.diagonal f from hf)

/-- **Stacks 03KR.** If a composite is locally separated, so is its first
factor. -/
theorem isLocallySeparated_of_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfg : IsLocallySeparated B S hS (f ≫ g)) :
    IsLocallySeparated B S hS f := by
  let P : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)
  have : P.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange P
  change IsImmersion B S hS (pullback.diagonal (f ≫ g)) at hfg
  change IsImmersion B S hS (pullback.diagonal f)
  exact MorphismProperty.of_isPullback (diagonal_comp_isPullback f g) hfg

end AlgebraicGeometry.Space

end
