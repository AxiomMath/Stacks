module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ChowLemma.Main

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ChowLemma.Approximation
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation

/-!
# Chow's lemma for algebraic spaces

Let `f : X ⟶ Y` be a separated morphism of finite type of algebraic spaces over a scheme `S`,
with `Y` separated and Noetherian. Then there are a dense open subspace `U ⊆ X`, a
`U`-admissible blowup `X' ⟶ X` and an immersion `X' ⟶ ℙⁿ_Y` over `Y` (Stacks 088U, Knutson IV
Theorem 3.1).

This file registers Stacks 088U on
`AlgebraicGeometry.Space.C1573.exists_isAdmissibleBlowup_isImmersion_projectiveSpace`, proved by
viewing everything over `Spec ℤ` (Stacks 03I5), where Noetherian approximation applies.

## References

* [Stacks Project, Tag 088U](https://stacks.math.columbia.edu/tag/088U)
* [Kn, IV, Theorem 3.1]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

add_to_stacks 088U
  AlgebraicGeometry.Space.C1573.exists_isAdmissibleBlowup_isImmersion_projectiveSpace

end AlgebraicGeometry.Space

end
