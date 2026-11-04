module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallySeparatedDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedSecondDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedDiagonalTFAE

/-!
# Stacks 04YZ: separation of the first diagonal read off the second

Let `S` be a scheme contained in a big fppf site `B` and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
algebraic stacks over `S`, with no representability hypothesis. Write

`Δ_{f,1} : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳`,  `Δ_{f,2} : 𝒳 ⟶ 𝒳 ×_{Δ_{f,1}, 𝒳 ×_𝒴 𝒳, Δ_{f,1}} 𝒳`

for its first and second relative diagonals, the second being the relative diagonal of the
first. **Stacks 04YZ** asserts three chains of equivalences:

1. `Δ_{f,1}` is separated ⟺ `Δ_{f,2}` is a closed immersion ⟺ `Δ_{f,2}` is proper ⟺ `Δ_{f,2}`
   is universally closed;
2. `Δ_{f,1}` is quasi-separated ⟺ `Δ_{f,2}` is of finite type ⟺ `Δ_{f,2}` is quasi-compact;
3. `Δ_{f,1}` is locally separated ⟺ `Δ_{f,2}` is an immersion.

Both diagonals are representable by algebraic spaces, and every condition above is read in the
relative sense of Section 04XB; being a closed immersion or an immersion is read at parts (2) and
(3) of Stacks 04YL.

## Main results

* `AlgebraicGeometry.Stack.isSeparated_firstRelativeDiagonal_tfae`: **Stacks 04YZ**, part (1).
* `AlgebraicGeometry.Stack.isQuasiSeparated_firstRelativeDiagonal_tfae`: **Stacks 04YZ**,
  part (2).
* `AlgebraicGeometry.Stack.isLocallySeparated_firstRelativeDiagonal_iff_isImmersion_second`:
  **Stacks 04YZ**, part (3).

## References

* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 04YQ](https://stacks.math.columbia.edu/tag/04YQ)
* [Stacks Project, Tag 04YS](https://stacks.math.columbia.edu/tag/04YS)
* [Stacks Project, Tag 04YT](https://stacks.math.columbia.edu/tag/04YT)
* [Stacks Project, Tag 04YU](https://stacks.math.columbia.edu/tag/04YU)
* [Stacks Project, Tag 04YZ](https://stacks.math.columbia.edu/tag/04YZ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` the
following are equivalent: the first relative diagonal `Δ_{f,1}` is separated; the second relative
diagonal `Δ_{f,2}` is a closed immersion, part (2) of Stacks 04YL; `Δ_{f,2}` is proper;
`Δ_{f,2}` is universally closed — the last two, and the first, in the relative sense of
Stacks 04XB. -/
@[stacks 04YZ "part (1)"]
theorem isSeparated_firstRelativeDiagonal_tfae (f : 𝒳 ⟶ 𝒴) :
    List.TFAE
      [IsSeparated B S hS (relativeDiagonalAlgebraicStacks B S hS f).hom,
       AlgebraicStacks.IsClosedImmersion B S hS
         (relativeDiagonalAlgebraicStacks B S hS (relativeDiagonalAlgebraicStacks B S hS f)),
       IsProper B S hS
         (relativeDiagonalAlgebraicStacks B S hS
           (relativeDiagonalAlgebraicStacks B S hS f)).hom,
       UniversallyClosed B S hS
         (relativeDiagonalAlgebraicStacks B S hS
           (relativeDiagonalAlgebraicStacks B S hS f)).hom] :=
  isSeparated_relativeDiagonal_tfae B S hS (relativeDiagonalAlgebraicStacks B S hS f)
    (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f)

/-- For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` the
following are equivalent: the first relative diagonal `Δ_{f,1}` is quasi-separated; the second
relative diagonal `Δ_{f,2}` is of finite type; `Δ_{f,2}` is quasi-compact — all three in the
relative sense of Stacks 04XB. -/
@[stacks 04YZ "part (2)"]
theorem isQuasiSeparated_firstRelativeDiagonal_tfae (f : 𝒳 ⟶ 𝒴) :
    List.TFAE
      [IsQuasiSeparated B S hS (relativeDiagonalAlgebraicStacks B S hS f).hom,
       IsFiniteType B S hS
         (relativeDiagonalAlgebraicStacks B S hS
           (relativeDiagonalAlgebraicStacks B S hS f)).hom,
       IsQuasiCompact B S hS
         (relativeDiagonalAlgebraicStacks B S hS
           (relativeDiagonalAlgebraicStacks B S hS f)).hom] := by
  have hΔ₁ : IsRepresentableByAlgebraicSpaces B S hS
      (relativeDiagonalAlgebraicStacks B S hS f).hom.hom :=
    isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f
  have hlft := (isLocallyOfFiniteType_relativeDiagonal_of_isRepresentableByAlgebraicSpaces
    B S hS (relativeDiagonalAlgebraicStacks B S hS f) hΔ₁).2
  tfae_have 1 ↔ 3 := (isQuasiCompact_relativeDiagonal_iff_isQuasiSeparated B S hS
    (relativeDiagonalAlgebraicStacks B S hS f) hΔ₁).symm
  tfae_have 2 → 3 := fun h U y hy F hF he => (h U y hy F hF he).2
  tfae_have 3 → 2 := fun h U y hy F hF he => ⟨hlft U y hy F hF he, h U y hy F hF he⟩
  tfae_finish

/-- The first relative diagonal `Δ_{f,1}` of a 1-morphism
`f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is locally separated, in the relative sense of
Stacks 04XB, if and only if the second relative diagonal `Δ_{f,2}` is an immersion, part (3) of
Stacks 04YL. -/
@[stacks 04YZ "part (3)"]
theorem isLocallySeparated_firstRelativeDiagonal_iff_isImmersion_second (f : 𝒳 ⟶ 𝒴) :
    IsLocallySeparated B S hS (relativeDiagonalAlgebraicStacks B S hS f).hom ↔
      AlgebraicStacks.IsImmersion B S hS
        (relativeDiagonalAlgebraicStacks B S hS (relativeDiagonalAlgebraicStacks B S hS f)) :=
  isLocallySeparated_iff_isImmersion_relativeDiagonalAlgebraicStacks B S hS
    (relativeDiagonalAlgebraicStacks B S hS f)
    (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f)

end AlgebraicGeometry.Stack

end
