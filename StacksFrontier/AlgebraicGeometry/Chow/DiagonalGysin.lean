module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection
public import StacksFrontier.AlgebraicGeometry.Divisors.Relative.SmoothSection
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Immersion

/-!
# Gysin maps for diagonals

Let `f : X ⟶ Y` be a smooth morphism of schemes locally of finite type over the base situation
of chapter 42 of the Stacks Project. Then the diagonal `Δ : X ⟶ X ×_Y X` is a regular immersion,
so the Gysin map

`Δ^! ∈ A^*(X ⟶ X ×_Y X)^∧`

of section 42.59 is available; when `f` has constant relative dimension `d` it lies in
`A^d(X ⟶ X ×_Y X)`.

## Main results

* `Stacks.Chow.isRegularImmersion_diagonal_of_smooth`: the diagonal of a smooth morphism is a
  regular immersion.
* `Stacks.Chow.gysinMapExists_diagonal_of_smooth`: the Gysin map exists for the diagonal of a
  smooth morphism, in the sense of Stacks 0FF3.

## References

* [Stacks Project, Section 42.60 (Tag 0FBR)](https://stacks.math.columbia.edu/tag/0FBR)
* [Stacks Project, Tag 067R](https://stacks.math.columbia.edu/tag/067R)
* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace Stacks.Chow

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The diagonal `Δ : X ⟶ X ×_Y X` of a smooth morphism is a regular immersion. -/
@[stacks 0FBR "the diagonal of a smooth morphism is a regular immersion",
  sga "6 VII 1.10" "special case",
  sga "6 VIII 1.3" "special case"]
theorem isRegularImmersion_diagonal_of_smooth [Smooth f] :
    Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion (pullback.diagonal f) :=
  Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_section (pullback.fst f f)
    (pullback.diagonal f) (pullback.diagonal_fst f)

/-- The Gysin map exists for the diagonal of a smooth morphism, in the sense of Stacks 0FF3. -/
@[stacks 0FBR "the Gysin map Δ^! is available for the diagonal"]
theorem gysinMapExists_diagonal_of_smooth [Smooth f] :
    GysinMapExists (pullback.diagonal f) :=
  GysinMapExists.of_isImmersion _

end Stacks.Chow

end
