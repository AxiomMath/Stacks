module

public import StacksFrontier.AlgebraicGeometry.Blowup.ClassifyingMorphism

/-!
# Blowing up an effective Cartier divisor

[Stacks, Tag 0807]: if the centre of a blowup is already an effective Cartier divisor, the
blowup morphism is an isomorphism.

This is a corollary of the universal property [Stacks, Tag 0806]
(`Stacks.Blowup.isTerminal_blowUp`): when `I` itself is an effective Cartier divisor, the
identity of `X` is an object of the category `C` of schemes over `X` on which the inverse image
of the centre is an effective Cartier divisor, and the blowup is a final object of `C`, so the
unique morphism `X ⟶ Bl_I X` over `X` is inverse to the blowup morphism.

## Main results

* `Stacks.Blowup.isIso_blowUpToBase_of_isEffectiveCartierDivisor`: **[Stacks, Tag 0807]**.
  Unconditional.

## Implementation notes

The tag says "the blowup is the identity"; what is proved here is that its structure morphism is
an isomorphism, which is the same statement for schemes over `X` and is how the Stacks Project
uses it — in particular in the proof of [Stacks, Tag 080H] part (1), where it is applied to the
inverse image of a divisor on the blowup of a different centre.

Morphisms of `Stacks.Blowup.CartierOver` are `CategoryTheory.InducedCategory.Hom`, so the
morphism over `X` given by the blowup morphism is `CategoryTheory.InducedCategory.homMk` of a
`CategoryTheory.Over.homMk`, and the two triangles are read off with
`CategoryTheory.Over.w` and the uniqueness half of finality.

## References

* [Stacks Project, Tag 0806](https://stacks.math.columbia.edu/tag/0806)
* [Stacks Project, Tag 0807](https://stacks.math.columbia.edu/tag/0807)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.Blowup

/-- **[Stacks, Tag 0807].** Blowing up a scheme in an effective Cartier divisor does not change
it: the blowup morphism is an isomorphism.

The identity of `X` lies in the category `C` of [Stacks, Tag 0806] precisely because `I` is an
effective Cartier divisor, and the blowup is a final object of `C`
(`Stacks.Blowup.isTerminal_blowUp`), so the classifying morphism of the identity is a two-sided
inverse of the blowup morphism. -/
@[stacks 0807]
public theorem isIso_blowUpToBase_of_isEffectiveCartierDivisor {X : Scheme.{u}}
    (I : X.IdealSheafData) (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) :
    IsIso (AlgebraicGeometry.blowUpToBase I) := by
  classical
  obtain ⟨hB, ⟨hT⟩⟩ := isTerminal_blowUp I
  have hX : IsCartierOver I (Over.mk (𝟙 X)) := by
    show Stacks.Divisors.IsEffectiveCartierDivisor (I.comap (𝟙 X))
    simpa using hI
  let T : CartierOver I := ⟨Over.mk (AlgebraicGeometry.blowUpToBase I), hB⟩
  let Y : CartierOver I := ⟨Over.mk (𝟙 X), hX⟩
  let g : Y ⟶ T := hT.from Y
  let f : T ⟶ Y :=
    InducedCategory.homMk (Over.homMk (AlgebraicGeometry.blowUpToBase I) (by simp [T, Y]))
  exact ⟨⟨g.hom.left, congrArg (fun k : T ⟶ T => k.hom.left) (hT.hom_ext (f ≫ g) (𝟙 T)),
    Over.w g.hom⟩⟩

end Stacks.Blowup

end
