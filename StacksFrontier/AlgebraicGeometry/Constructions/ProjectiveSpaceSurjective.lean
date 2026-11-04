module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceRationalPoint

/-!
# Projective space is surjective over its base

The structure morphism `ℙⁿ_S ⟶ S` of projective `n`-space over a scheme `S` is surjective.

## Main results

* `AlgebraicGeometry.projectiveSpaceOver.surjective`: `ℙⁿ_S ⟶ S` is surjective.

## Implementation notes

`AlgebraicGeometry.exists_section_projectiveSpaceOver` gives a section of the structure
morphism, so the structure morphism is a split epimorphism; a split epimorphism of schemes is
surjective because `AlgebraicGeometry.Surjective.of_comp` cancels the section off the left of
the identity, which is surjective.

## References

* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.projectiveSpaceOver

/-- **The structure morphism of projective `n`-space over a scheme is surjective.** It has a
section, so it is a split epimorphism. -/
instance surjective (n : ℕ) (S : Scheme.{u}) : Surjective (projectiveSpaceOver n S ↘ S) := by
  obtain ⟨s, hs⟩ := exists_section_projectiveSpaceOver S n
  have : Surjective (s ≫ (projectiveSpaceOver n S ↘ S)) := by rw [hs]; infer_instance
  exact Surjective.of_comp (f := s) _

end AlgebraicGeometry.projectiveSpaceOver

end
