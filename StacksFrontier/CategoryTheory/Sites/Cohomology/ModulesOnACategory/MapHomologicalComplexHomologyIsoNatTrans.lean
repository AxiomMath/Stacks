module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.QuasiCoherenceOfTopCohomology
import all StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.QuasiCoherenceOfTopCohomology

/-!
# The cohomology comparisons of exact functors and a natural transformation between them

For a natural transformation `τ : F ⟶ G ⋙ H` of exact functors between abelian categories, the
map induced by `τ` on the degree-`n` cohomology of a complex is carried to `τ` by the cohomology
comparisons `Functor.mapHomologicalComplexHomologyIso`.

## Main results

* `Stacks.ModulesOnACategory.TopCohomology.mapHomologicalComplexHomologyIso_hom_app_mapNatTrans`:
  the cohomology comparisons carry the map induced by `τ` on cohomology to `τ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace Stacks.ModulesOnACategory.TopCohomology

universe u₁ u₂ u₃ v₁ v₂ v₃

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  {D : Type u₃} [Category.{v₃} D] [Abelian D]

/-- For a natural transformation `τ : F ⟶ G ⋙ H` of exact functors, the map induced by `τ` on
the degree-`n` cohomology of a complex is carried to `τ` by the cohomology comparisons. -/
alias mapHomologicalComplexHomologyIso_hom_app_mapNatTrans := homologyIso_mapNatTrans_compat

end Stacks.ModulesOnACategory.TopCohomology

end
