module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorExceptionalImmersion
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpectrum.NoetherianModelClauses
public import StacksFrontier.AlgebraicGeometry.LocalIso.ClosedImmersionNeighbourhood
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The corners of the two-generator square over a Noetherian ring

Let `A` be a **Noetherian** ring and `f₁, f₂ ∈ A`, the data of [Stacks, Example 0EVH] after the
reduction of [Stacks, Tag 0B8W].  This file records that the modification
`X' = Proj (A[T₀,T₁]/(f₂T₀-f₁T₁))` and the exceptional line `E = 𝐏¹_Z` are then **locally
Noetherian**, and instantiates at the closed immersion `E ⟶ X'` the statement that a morphism of
finite locally free modules which becomes an isomorphism on a closed subscheme is an isomorphism
over an open neighbourhood of it.

## Main results

* `Stacks.AlmostBlowUp.isLocallyNoetherian_proj_modificationGrading`: the modification is
  locally Noetherian.
* `Stacks.AlmostBlowUp.isLocallyNoetherian_proj_exceptionalGrading`: the exceptional line is
  locally Noetherian.
* `Stacks.AlmostBlowUp.exists_isIso_restrictFunctor_map_near_exceptional`: a morphism of finite
  locally free `𝒪_{X'}`-modules whose restriction to `E` is an isomorphism is an isomorphism over
  an open neighbourhood of `E`.

## References

* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.IsoLocus

universe u

namespace Stacks.AlmostBlowUp

attribute [local instance] MvPolynomial.gradedAlgebra modificationSubmoduleGraded

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (f₁ f₂ : A)

/-- The modification of the two-generator square over a Noetherian ring is locally Noetherian. -/
@[ega "II 2.7.1" "locally Noetherian"]
theorem isLocallyNoetherian_proj_modificationGrading :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    IsLocallyNoetherian (Proj (modificationGrading A f₁ f₂)) :=
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  AlgebraicGeometry.isLocallyNoetherian_of_isOpenImmersion
    (Stacks.GradedRegrading.projIso (coe_modificationSubmoduleGrading A f₁ f₂)).inv

/-- The exceptional line of the two-generator square over a Noetherian ring is locally
Noetherian. -/
@[ega "II 2.7.1" "locally Noetherian"]
theorem isLocallyNoetherian_proj_exceptionalGrading :
    IsLocallyNoetherian (Proj (exceptionalGrading A f₁ f₂)) :=
  Stacks.AlgebraicGeometry.Proj.isLocallyNoetherian_proj (exceptionalGrading A f₁ f₂)

/-- A morphism of finite locally free modules on the modification whose restriction to the
exceptional line is an isomorphism is an isomorphism over an open neighbourhood of the exceptional
line. -/
theorem exists_isIso_restrictFunctor_map_near_exceptional
    {F G : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).Modules}
    (hF : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F)
    (hG : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G)
    (α : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded; F ⟶ G)
    (hα : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      IsIso ((Scheme.Modules.pullback (exceptionalToModification A f₁ f₂)).map α)) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    ∃ U : (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).Opens,
      Set.range (exceptionalToModification A f₁ f₂).base ⊆ (U : Set _) ∧
        IsIso ((Scheme.Modules.restrictFunctor U.ι).map α) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  have := isLocallyNoetherian_proj_modificationGrading A f₁ f₂
  have := hF
  have := hG
  exact exists_isIso_restrictFunctor_map_of_isIso_pullback_of_isLocallyNoetherian
    (exceptionalToModification A f₁ f₂) α hα

end Stacks.AlmostBlowUp

end
