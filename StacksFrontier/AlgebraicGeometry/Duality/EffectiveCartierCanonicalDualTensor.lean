module

public import StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierIdealDualTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualTensorSheafHomCanonical

/-!
# The canonical map of Tag 08JD at the ideal sheaf and at `i_* 𝒪_D`

Let `X` be a scheme and `D ⊆ X` an effective Cartier divisor with closed immersion
`i : D ⟶ X` and ideal sheaf `ℐ_D`. Both `ℐ_D[0]` and `(i_* 𝒪_D)[0]` are perfect objects of
`D(𝒪_X)` — the first because `ℐ_D` is invertible, the second because it is the third term of a
short exact sequence of invertible modules
(`Stacks.Divisors.isPerfect_singleFunctor_idealShortComplex_X₃`). This file records the
consequence for the **canonical** map of [Stacks, Tag 08JD],

`K ⊗^L_{𝒪_X} E^∨ ⟶ R ℰom_{𝒪_X}(E, K)`,

at those two objects: it is an isomorphism.

`Stacks.Divisors.idealDualTensorIso` and `Stacks.Divisors.divisorQuotientDualTensorIso` already
record the *isomorphism* `K ⊗^L E^∨ ≅ R ℰom(E, K)` at the same two objects, but by the route of
[Stacks, Tag 0BYS]; what the two statements below add is that the canonical map of
[Stacks, Tag 08JD] is the morphism underlying it, through
`AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_isPerfect_canonical`.

The second statement is the input the proof of [Stacks, Tag 0AA4] needs on `X`: the source
rewrites `R ℰom_{𝒪_X}(i_* 𝒪_D, K)` as `K ⊗^L_{𝒪_X} (i_* 𝒪_D)^∨` by that canonical map, and
`Stacks.Divisors.idealDerivedSheafHomIso` identifies `(i_* 𝒪_D)^∨` with `(i_* 𝒩)[-1]`.

## Main results

* `Stacks.Divisors.isIso_derivedTensorDualToSheafHom_negativeTwist`: the canonical map of
  [Stacks, Tag 08JD] is an isomorphism at `E = ℐ_D`.
* `Stacks.Divisors.isIso_derivedTensorDualToSheafHom_idealShortComplex_X₃`: the canonical map of
  [Stacks, Tag 08JD] is an isomorphism at `E = i_* 𝒪_D`.

## References

* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 0AA4](https://stacks.math.columbia.edu/tag/0AA4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]

/-- **The canonical map of [Stacks, Tag 08JD] is an isomorphism at the ideal sheaf of an
effective Cartier divisor**: `K ⊗^L_{𝒪_X} ℐ_D^∨ ⟶ R ℰom_{𝒪_X}(ℐ_D, K)`. The ideal sheaf is
invertible, hence perfect in degree zero. -/
theorem isIso_derivedTensorDualToSheafHom_negativeTwist (K : DerivedCategory X.Modules) :
    IsIso (AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom
      (Stacks.SheafOfModules.ringedSite X.sheaf)
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct
        (Stacks.SheafOfModules.ringedSite X.sheaf))
      ((DerivedCategory.singleFunctor X.Modules 0).obj (negativeTwist' D)) K) :=
  AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_isPerfect_canonical
    (Stacks.SheafOfModules.ringedSite X.sheaf) _ K
    (AlgebraicGeometry.RingedSite.isPerfect_singleFunctor_of_isInvertible
      (Stacks.SheafOfModules.ringedSite X.sheaf) 0 (negativeTwist' D))

/-- **The canonical map of [Stacks, Tag 08JD] is an isomorphism at `i_* 𝒪_D`**:

`K ⊗^L_{𝒪_X} (i_* 𝒪_D)^∨ ⟶ R ℰom_{𝒪_X}(i_* 𝒪_D, K)`.

`(i_* 𝒪_D)[0]` is perfect, being the third term of the short exact sequence
`0 ⟶ ℐ_D ⟶ 𝒪_X ⟶ i_* 𝒪_D ⟶ 0` of invertible modules. This is the step the source's proof of
[Stacks, Tag 0AA4] performs on `X`. -/
theorem isIso_derivedTensorDualToSheafHom_idealShortComplex_X₃ (K : DerivedCategory X.Modules) :
    IsIso (AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom
      (Stacks.SheafOfModules.ringedSite X.sheaf)
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct
        (Stacks.SheafOfModules.ringedSite X.sheaf))
      ((DerivedCategory.singleFunctor X.Modules 0).obj (idealShortComplex D).X₃) K) :=
  AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_isPerfect_canonical
    (Stacks.SheafOfModules.ringedSite X.sheaf) _ K
    (isPerfect_singleFunctor_idealShortComplex_X₃ D)

end Stacks.Divisors

end
