module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SeparatedAndClosed

/-!
# Quasi-separatedness across a morphism of thickenings of algebraic spaces

A morphism of thickenings of algebraic spaces over a scheme `S` is a commutative square

```
X --a--→ Y
|        |
i        j
↓        ↓
X' --b-→ Y'
```

whose vertical arrows are the inclusions of thickenings. This file proves that `a` is
quasi-separated exactly when `b` is: the *quasi-separated* half of part (6) of Stacks 09ZY,
which `StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SeparatedAndClosed` leaves open while
proving the separated half.

The argument is the one that file runs for separatedness, with quasi-compactness in place of
universal closedness and with no reduction step in front of it. Quasi-separatedness *is*
quasi-compactness of the relative diagonal (**Stacks 03HL**, part (3)), so the two diagonals may
be compared directly: they sit in the commutative square `Δₐ ≫ c = i ≫ Δ_b` over the comparison
`c : X ×[Y] X ⟶ X' ×[Y'] X'`, and `c` is a closed immersion by
`AlgebraicGeometry.Space.isClosedImmersion_pullbackMap`. A closed immersion is quasi-compact
(**Stacks 04CG**), so quasi-compactness of `Δₐ` makes `Δₐ ≫ c = i ≫ Δ_b` quasi-compact
(**Stacks 03HG**), and `Δ_b` is then quasi-compact because `i` is surjective (**Stacks 040W**,
part (2)). The converse direction is formal: `i ≫ b = a ≫ j` is quasi-separated as a composite
of quasi-separated morphisms (**Stacks 03KQ**), a closed immersion being quasi-separated, and
quasi-separatedness passes to a first factor (**Stacks 03KR**).

## Main results

* `AlgebraicGeometry.Space.isQuasiSeparated_iff_isQuasiSeparated_of_isClosedImmersion_square`:
  the comparison for a commutative square whose vertical arrows are closed immersions, the left
  one surjective — the form in which it is proved.
* `AlgebraicGeometry.Space.isQuasiSeparated_iff_isQuasiSeparated_of_isThickening`:
  **Stacks 09ZY**, the quasi-separated half of part (6).

## Implementation notes

The implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SeparatedAndClosed` record this half as
needing "the two remaining clauses of Stacks 03KN for the comparison `c`, namely that it is
quasi-compact and that quasi-separatedness of `j` makes it so". Neither is needed: that file's
own `AlgebraicGeometry.Space.isClosedImmersion_pullbackMap` already gives `c` as a *closed
immersion* for an arbitrary closed immersion `j`, using only part (3) of Stacks 03KN, and a
closed immersion is quasi-compact by
`AlgebraicGeometry.Space.isQuasiCompact_of_isClosedImmersion'`. So the quasi-compactness of `c`
that the note asks for is available from part (3) alone.

As in that file, the only properties of the inclusions used are that they are closed immersions
and that `i` is surjective; the square need not be cartesian, and surjectivity of the right-hand
inclusion `j` is never used.

## References

* [Stacks Project, Tag 03HG](https://stacks.math.columbia.edu/tag/03HG)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
* [Stacks Project, Tag 03KN](https://stacks.math.columbia.edu/tag/03KN)
* [Stacks Project, Tag 03KQ](https://stacks.math.columbia.edu/tag/03KQ)
* [Stacks Project, Tag 03KR](https://stacks.math.columbia.edu/tag/03KR)
* [Stacks Project, Tag 040W](https://stacks.math.columbia.edu/tag/040W)
* [Stacks Project, Tag 04CG](https://stacks.math.columbia.edu/tag/04CG)
* [Stacks Project, Tag 09ZY](https://stacks.math.columbia.edu/tag/09ZY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Square

variable {X X' Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 09ZY, the quasi-separated half of part (6), in the form it is proved.** In a
commutative square `a ≫ j = i ≫ b` of morphisms of algebraic spaces over `S` whose vertical
arrows are closed immersions, the left one surjective, `a` is quasi-separated if and only if `b`
is.

Quasi-separatedness is quasi-compactness of the relative diagonal, and the two relative
diagonals sit in the commutative square `Δₐ ≫ c = i ≫ Δ_b` of
`AlgebraicGeometry.Space.pullback_diagonal_comp_pullbackMap`, whose comparison `c` is a closed
immersion, hence quasi-compact. -/
theorem isQuasiSeparated_iff_isQuasiSeparated_of_isClosedImmersion_square
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hY : IsAlgebraicSpace B S hS Y) (hY' : IsAlgebraicSpace B S hS Y')
    {i : X ⟶ X'} {j : Y ⟶ Y'} (a : X ⟶ Y) (b : X' ⟶ Y')
    (hi : IsClosedImmersion B S hS i) (hisurj : IsSurjective B S hS i)
    (hj : IsClosedImmersion B S hS j) (hw : a ≫ j = i ≫ b) :
    IsQuasiSeparated B S hS a ↔ IsQuasiSeparated B S hS b := by
  have hXX : IsAlgebraicSpace B S hS (pullback a a) :=
    isAlgebraicSpace_pullback B S hS a a hX hX hY
  have hX'X' : IsAlgebraicSpace B S hS (pullback b b) :=
    isAlgebraicSpace_pullback B S hS b b hX' hX' hY'
  constructor
  · intro ha
    have h : IsQuasiCompact B S hS
        (pullback.diagonal a ≫ pullback.map a a b b i i j hw hw) :=
      isQuasiCompact_comp B S hS hXX hX'X' _ _ ha
        (isQuasiCompact_of_isClosedImmersion' B S hS
          (isClosedImmersion_pullbackMap B S hS hi hj hw))
    rw [pullback_diagonal_comp_pullbackMap B S hS hw] at h
    exact isQuasiCompact_of_comp_surjective B S hS hX hX' hX'X' i
      (i ≫ pullback.diagonal b) (pullback.diagonal b) rfl hisurj h
  · intro hb
    refine isQuasiSeparated_of_comp B S hS a j ?_
    rw [hw]
    exact isQuasiSeparated_comp B S hS hX hX' i b
      (isQuasiCompact_of_isClosedImmersion' B S hS
        (isSeparated_of_isClosedImmersion B S hS i hi)) hb

end Square

section Thickening

variable {X Y : AlgebraicSpaces B S hS} {G : Subfunctor X.1} {H : Subfunctor Y.1}

/-- **Stacks 09ZY, the quasi-separated half of part (6).** In a morphism of thickenings of
algebraic spaces over `S` the morphism on the closed subspaces is quasi-separated if and only if
the morphism on the ambient spaces is.

The separated half of the same part is
`AlgebraicGeometry.Space.isSeparated_iff_isSeparated_of_isThickening`; together they are the
whole of part (6). -/
@[stacks 09ZY "part (6): the quasi-separated half"]
theorem isQuasiSeparated_iff_isQuasiSeparated_of_isThickening
    (hG : IsThickening B S hS X G) (hH : IsThickening B S hS Y H)
    (f : Arrow.mk G.ι ⟶ Arrow.mk H.ι) :
    IsQuasiSeparated B S hS f.left ↔ IsQuasiSeparated B S hS f.right :=
  isQuasiSeparated_iff_isQuasiSeparated_of_isClosedImmersion_square B S hS hG.1.1 X.2
    hH.1.1 Y.2 f.left f.right hG.1.2 hG.2 hH.1.2 (Arrow.w f)

end Thickening

end AlgebraicGeometry.Space

end
