module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedSpaceDifferentials
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangent

/-!
# The naive cotangent complex of a morphism of ringed spaces

For a morphism of ringed spaces `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)`, the naive cotangent complex
`NL_f = NL_{X/Y}` is the naive cotangent complex of the homomorphism of sheaves of rings
`f^{-1}𝒪_Y ⟶ 𝒪_X` on `X`, the transpose of the structure map `f^♯ : 𝒪_Y ⟶ f_*𝒪_X` across the
inverse image/pushforward adjunction.

## Main definitions

* `AlgebraicGeometry.RingedSpace.naiveCotangentComplex` is `NL_{X/Y}`.

## Main results

* `AlgebraicGeometry.RingedSpace.naiveCotangentComplex_X_negOne`: the degree `-1` term is the
  conormal sheaf of the canonical polynomial presentation of `𝒪_X` over `f^{-1}𝒪_Y`.
* `AlgebraicGeometry.RingedSpace.naiveCotangentComplex_X_zero`: the degree `0` term is the
  scalar extension of its relative differentials.
* `AlgebraicGeometry.RingedSpace.naiveCotangentComplex_isZero_X`: the remaining terms vanish.
* `AlgebraicGeometry.RingedSpace.naiveCotangentComplex_d_negOne_zero`: the one nonzero
  differential is the conormal map.

## Implementation notes

The homomorphism `f^{-1}𝒪_Y ⟶ 𝒪_X` is
`Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap`, the one over which the sheaf
of relative differentials `Ω_{X/Y}` of a morphism of ringed spaces is defined.

Everything is stated for `RingedSpace.{u, u}`, a ringed space whose structure sheaf and
underlying topological space lie in one universe.

## References

* [Stacks Project, Tag 08TN](https://stacks.math.columbia.edu/tag/08TN)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageSheaf inverseImageStructureMap)

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The naive cotangent complex `NL_f = NL_{X/Y}` of a morphism of ringed spaces
`f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)`: the naive cotangent complex of the homomorphism of sheaves of rings
`f^{-1}𝒪_Y ⟶ 𝒪_X` on `X`. -/
@[stacks 08TN]
noncomputable def naiveCotangentComplex :
    CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology X.carrier) X.sheaf)) ℤ :=
  Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u}
    (Opens.grothendieckTopology X.carrier) (inverseImageSheaf f) X.sheaf
    (inverseImageStructureMap f)

/-- The conormal sheaf of the canonical presentation of `𝒪_X` over `f^{-1}𝒪_Y` is the degree
`-1` term of `NL_{X/Y}`. -/
@[simp] theorem naiveCotangentComplex_X_negOne :
    (naiveCotangentComplex f).X (-1) =
      (Stacks.SheafOfModules.canonicalConormalSequence.{u, u, u, u}
        (Opens.grothendieckTopology X.carrier) (inverseImageSheaf f) X.sheaf
        (inverseImageStructureMap f)).X₁ :=
  Stacks.SheafOfModules.naiveCotangentComplex_X_negOne.{u, u, u, u}
    (Opens.grothendieckTopology X.carrier) (inverseImageSheaf f) X.sheaf
    (inverseImageStructureMap f)

/-- The scalar extension to `𝒪_X` of the relative differentials of the canonical
presentation is the degree `0` term of `NL_{X/Y}`. -/
@[simp] theorem naiveCotangentComplex_X_zero :
    (naiveCotangentComplex f).X 0 =
      (Stacks.SheafOfModules.canonicalConormalSequence.{u, u, u, u}
        (Opens.grothendieckTopology X.carrier) (inverseImageSheaf f) X.sheaf
        (inverseImageStructureMap f)).X₂ :=
  Stacks.SheafOfModules.naiveCotangentComplex_X_zero.{u, u, u, u}
    (Opens.grothendieckTopology X.carrier) (inverseImageSheaf f) X.sheaf
    (inverseImageStructureMap f)

/-- `NL_{X/Y}` has no terms outside degrees `-1` and `0`. -/
theorem naiveCotangentComplex_isZero_X (i : ℤ) (hneg : i ≠ -1) (hzero : i ≠ 0) :
    Limits.IsZero ((naiveCotangentComplex f).X i) :=
  Stacks.SheafOfModules.naiveCotangentComplex_isZero_X.{u, u, u, u}
    (Opens.grothendieckTopology X.carrier) (inverseImageSheaf f) X.sheaf
    (inverseImageStructureMap f) i hneg hzero

/-- The only nonzero differential of `NL_{X/Y}` is the conormal map. -/
theorem naiveCotangentComplex_d_negOne_zero :
    (naiveCotangentComplex f).d (-1) 0 =
      eqToHom (naiveCotangentComplex_X_negOne f) ≫
        (Stacks.SheafOfModules.canonicalConormalSequence.{u, u, u, u}
          (Opens.grothendieckTopology X.carrier) (inverseImageSheaf f) X.sheaf
          (inverseImageStructureMap f)).f ≫
        eqToHom (naiveCotangentComplex_X_zero f).symm :=
  Stacks.SheafOfModules.naiveCotangentComplex_d_negOne_zero.{u, u, u, u}
    (Opens.grothendieckTopology X.carrier) (inverseImageSheaf f) X.sheaf
    (inverseImageStructureMap f)

end AlgebraicGeometry.RingedSpace

end
