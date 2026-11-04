module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleSquareZeroExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionQuotientRealization

/-!
# Realizations of square-zero extensions, for `EtaleSquareZeroExtension`

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `E` a square-zero extension of the small
étale structure sheaf of `X`, as an algebra over `f⁻¹𝒪_Y` (the data of Stacks 05ZT). A
*realization* of `E` is a first-order thickening `X ⊂ X'` over `Y` realizing `E`: this is
`AlgebraicGeometry.Space.SquareZeroExtension.ToposRealization`. This file names it in the
namespace of `AlgebraicGeometry.Space.EtaleSquareZeroExtension`, so that field notation on a
realization of `E : EtaleSquareZeroExtension f` finds the declarations stated there.

## Main definitions

* `AlgebraicGeometry.Space.EtaleSquareZeroExtension.Realization`.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry.Space.EtaleSquareZeroExtension

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}

/-- **A realization of a square-zero extension** `E` of `𝒪_X` relative to `f : X ⟶ Y`, a
first-order thickening `X ⊂ X'` over `Y` with `i⁻¹𝒪_{X'} ≅ 𝒜` compatibly with the maps to `𝒪_X`
and with the algebra structures over `f⁻¹𝒪_Y`: the realization
`AlgebraicGeometry.Space.SquareZeroExtension.ToposRealization` of the underlying extension. -/
abbrev Realization (E : EtaleSquareZeroExtension f) : Type _ :=
  SquareZeroExtension.ToposRealization E

end AlgebraicGeometry.Space.EtaleSquareZeroExtension

end
