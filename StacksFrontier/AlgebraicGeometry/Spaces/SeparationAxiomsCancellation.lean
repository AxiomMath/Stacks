module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.LocallySeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation

/-!
# The three separation axioms all cancel the second factor of a composite (Stacks 03KR)

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of algebraic spaces over `S`. **Stacks 03KR** has three assertions, one for each of
the three separation axioms of **Stacks 03HL**:

* (1) if `g ∘ f` is separated then so is `f`;
* (2) if `g ∘ f` is locally separated then so is `f`;
* (3) if `g ∘ f` is quasi-separated then so is `f`.

This file states all three as a single result,
`AlgebraicGeometry.Space.separationAxioms_of_comp`. Each assertion is a condition on `f ≫ g`,
so inside the one statement the three appear as implications with those conditions as their
antecedents, which is the form the source gives them in.

The source's proof is one argument run three times: the relative diagonal of `f ≫ g` factors as
`X ⟶ X ×_Y X ⟶ X ×_Z X`, the first map of that factorisation is a base change of the relative
diagonal of `f ≫ g` along the second
(`CategoryTheory.Limits.pullback.diagonal_comp_isPullback`), and each of the three axioms is a
condition on the relative diagonal — being a closed immersion, an immersion, quasi-compact —
that is stable under base change. The three instances of it are already in the library, and
this result is their conjunction; see the implementation notes.

## Main results

* `AlgebraicGeometry.Space.separationAxioms_of_comp`: the whole of **Stacks 03KR**, all three
  parts, for a composite of morphisms of algebraic spaces over `S`.

## Implementation notes

The three parts are `AlgebraicGeometry.Space.isSeparated_of_comp` (in
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions`),
`AlgebraicGeometry.Space.isLocallySeparated_of_comp` (in
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.LocallySeparated`) and
`AlgebraicGeometry.Space.isQuasiSeparated_of_comp` (in
`StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation`), and the statement below is
their conjunction, so it needs nothing of `X`, `Y` and `Z` beyond being presheaves on the big
fppf site of `S`: the argument uses only that the relative diagonal of `f` is a base change of
the relative diagonal of `f ≫ g`, which is a fact about the ambient category. The source's
hypothesis that `X`, `Y` and `Z` are algebraic spaces over `S` is therefore not assumed, and
the statement specialises to it; it is the same generality the three parts are stated at.

## References

* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
* [Stacks Project, Tag 03KR](https://stacks.math.columbia.edu/tag/03KR)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

/-- **Stacks 03KR.** Let `S` be a scheme contained in the big fppf site `B` and let
`f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over `S`. Then:

1. if `f ≫ g` is separated, so is `f`;
2. if `f ≫ g` is locally separated, so is `f`; and
3. if `f ≫ g` is quasi-separated, so is `f`.

Each of the three separation axioms is a condition on the relative diagonal which is stable
under base change, and the relative diagonal of `f` is a base change of that of `f ≫ g` along
the comparison map `X ×_Y X ⟶ X ×_Z X`. -/
@[stacks 03KR]
theorem separationAxioms_of_comp (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (IsSeparated B S hS (f ≫ g) → IsSeparated B S hS f) ∧
      (IsLocallySeparated B S hS (f ≫ g) → IsLocallySeparated B S hS f) ∧
      (IsQuasiSeparated B S hS (f ≫ g) → IsQuasiSeparated B S hS f) :=
  ⟨isSeparated_of_comp B S hS f g, isLocallySeparated_of_comp B S hS f g,
    isQuasiSeparated_of_comp B S hS f g⟩

end AlgebraicGeometry.Space

end
