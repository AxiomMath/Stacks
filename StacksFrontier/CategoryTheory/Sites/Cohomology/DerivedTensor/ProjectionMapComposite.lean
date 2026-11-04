module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionMapAlongEquivalences

/-!
# The projection map of a composite adjunction

Let `a₁ : L₁ ⊣ R₁` with `L₁ : C ⥤ D` and `a₂ : L₂ ⊣ R₂` with `L₂ : D ⥤ E` be adjunctions whose
source and targets carry bifunctors `T_C`, `T_D`, `T_E` and comparisons
`μ₁ : L₁(M ⊗ N) ⟶ L₁M ⊗ L₁N`, `μ₂ : L₂(M ⊗ N) ⟶ L₂M ⊗ L₂N`. The composite adjunction
`L₁ ⋙ L₂ ⊣ R₂ ⋙ R₁` carries the composite comparison
`Stacks.Cohomology.AbstractKunnethMap.compTensor μ₁ μ₂`, and its projection map
`A ⊗ R₁R₂B ⟶ R₁R₂(L₂L₁A ⊗ B)` is the projection map of `a₁` at `(A, R₂B)` followed by `R₁` of
the projection map of `a₂` at `(L₁A, B)` (`projectionMap_comp`).

This is the composition law of the projection formula of [Stacks, Tag 0B56] along a composite
of morphisms of ringed topoi, in the abstract setting of
`Stacks.Cohomology.AbstractKunnethMap.projectionMap`.

## References

* [Stacks Project, Tag 0B56](https://stacks.math.columbia.edu/tag/0B56)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.AbstractKunnethMap

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  (TC : C × C ⥤ C) (TD : D × D ⥤ D) (TE : E × E ⥤ E)
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} (a₁ : L₁ ⊣ R₁) {L₂ : D ⥤ E} {R₂ : E ⥤ D} (a₂ : L₂ ⊣ R₂)
  (μ₁ : TC ⋙ L₁ ⟶ L₁.prod L₁ ⋙ TD) (μ₂ : TD ⋙ L₂ ⟶ L₂.prod L₂ ⋙ TE)

/-- **The projection map of a composite adjunction is the composite of the projection maps**:
for `L₁ ⋙ L₂ ⊣ R₂ ⋙ R₁` with the composite comparison, the projection map at `(A, B)` is the
projection map of `a₁` at `(A, R₂B)` followed by `R₁` of the projection map of `a₂` at
`(L₁A, B)`. Both are adjoint to the composite comparison followed by the counit
`L₂L₁R₁R₂B ⟶ L₂R₂B ⟶ B` in the second factor. -/
theorem projectionMap_comp (A : C) (B : E) :
    projectionMap TC TE (a₁.comp a₂) (compTensor μ₁ μ₂) A B =
      projectionMap TC TD a₁ μ₁ A (R₂.obj B) ≫
        R₁.map (projectionMap TD TE a₂ μ₂ (L₁.obj A) B) := by
  apply ((a₁.comp a₂).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit,
    map_projectionMap_comp_counit TC TE (a₁.comp a₂) (compTensor μ₁ μ₂) A B]
  have h₁ := map_projectionMap_comp_counit TC TD a₁ μ₁ A (R₂.obj B)
  have h₂ := map_projectionMap_comp_counit TD TE a₂ μ₂ (L₁.obj A) B
  have hn := μ₂.naturality (𝟙 (L₁.obj A) ×ₘ a₁.counit.app (R₂.obj B))
  have hε := a₁.counit.naturality (projectionMap TD TE a₂ μ₂ (L₁.obj A) B)
  dsimp at hn hε ⊢
  simp only [Adjunction.comp_counit_app, Functor.map_comp, Category.assoc]
  rw [← L₂.map_comp_assoc (L₁.map (R₁.map _)), hε, L₂.map_comp_assoc, h₂,
    ← L₂.map_comp_assoc, h₁, L₂.map_comp, Category.assoc, reassoc_of% hn, ← TE.map_comp]
  simp only [CategoryTheory.Functor.map_id, prod_comp, Category.id_comp, compTensor_app,
    Category.assoc]

end Stacks.Cohomology.AbstractKunnethMap
