module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleStructureSheafInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.Basic

/-!
# The section of a retracted first-order thickening

Let `Y ⊂ Y'` be a first-order thickening of algebraic spaces with inclusion `t`, and suppose `t`
has a retraction `ρ : Y' ⟶ Y`, `t ≫ ρ = 𝟙`. This is the situation of the trivial square-zero
extensions `Spec A ⊂ Spec A[M]` of the tangent functor (Stacks 07Y9), retracted by the constants
`A ⟶ A[M]`. Then the extension `0 → 𝒞_{Y/Y'} → t⁻¹𝒪_{Y'} → 𝒪_Y → 0` of the thickening is split
by `t⁻¹(ρ^♯) : 𝒪_Y = (t ≫ ρ)⁻¹𝒪_Y ⟶ t⁻¹𝒪_{Y'}`. This is the splitting through which the solutions
of the extension problem of a flat `f : X ⟶ Y` (Stacks 0D17) become extensions of
`f⁻¹𝒪_Y`-algebras.

## Main definitions

* `AlgebraicGeometry.Space.FlatThickeningDeformation.retractionSection`: the section
  `𝒪_Y ⟶ t⁻¹𝒪_{Y'}`.

## Main results

* `AlgebraicGeometry.Space.FlatThickeningDeformation.retractionSection_comp_reduction`: it is a
  section of the reduction `t⁻¹𝒪_{Y'} ⟶ 𝒪_Y`.

## References

* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
* [Stacks Project, Tag 07Y9](https://stacks.math.columbia.edu/tag/07Y9)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space.FlatThickeningDeformation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y' : AlgebraicSpaces B S hS} {Z : ClosedSubspaces B S hS Y'.1}
  (hZ : IsFirstOrderThickening B S hS Y' Z.1)
  (ρ : Y' ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
  (hρ : subspaceInclusion B S hS Y' Z ≫ ρ = 𝟙 _)

variable (B S hS) in
/-- The structure map `(𝟙 Y)⁻¹𝒪_Y ⟶ 𝒪_Y` of the identity is an isomorphism (the identity is
étale, Stacks 03LV). -/
theorem isIso_structureSharpInverseImage_id (Y : AlgebraicSpaces B S hS) :
    IsIso (structureSharpInverseImage B S hS (𝟙 Y)) :=
  isIso_fSharpInverseImage_of_isEtale B S hS (𝟙 Y) (isEtale_of_isIso B S hS (𝟙 Y.obj))

/-- **The section of a retracted first-order thickening**: `t⁻¹(ρ^♯)`, read on
`𝒪_Y ≅ (𝟙 Y)⁻¹𝒪_Y = (t ≫ ρ)⁻¹𝒪_Y`, a ring map `𝒪_Y ⟶ t⁻¹𝒪_{Y'}`. -/
def retractionSection :
    (smallEtaleRingedTopos B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).O ⟶
      (baseExtension hZ).extension :=
  haveI := isIso_structureSharpInverseImage_id B S hS
    (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)
  inv (structureSharpInverseImage B S hS (𝟙 _)) ≫
    inverseImageStructureSheafMapOfEq B S hS (subspaceInclusion B S hS Y' Z) ρ hρ

/-- **The section is a section of the reduction** `t⁻¹𝒪_{Y'} ⟶ 𝒪_Y`. -/
theorem retractionSection_comp_reduction :
    retractionSection hZ ρ hρ ≫ (baseExtension hZ).reduction = 𝟙 _ := by
  have := isIso_structureSharpInverseImage_id B S hS
    (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)
  refine (Category.assoc _ _ _).trans ((IsIso.inv_comp_eq _).2 ?_)
  refine Eq.trans ?_ (Category.comp_id _).symm
  exact inverseImageStructureSheafMapOfEq_comp_structureSharpInverseImage B S hS _ ρ hρ

/-- The section of a retracted first-order thickening splits the base reduction of the extension
problem of any `f : X ⟶ Y`. -/
theorem retractionSection_comp_problem_baseReduction {X : AlgebraicSpaces B S hS}
    (f : X ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) :
    retractionSection hZ ρ hρ ≫ (problem f hZ).baseReduction = 𝟙 _ :=
  retractionSection_comp_reduction hZ ρ hρ

end AlgebraicGeometry.Space.FlatThickeningDeformation

end
