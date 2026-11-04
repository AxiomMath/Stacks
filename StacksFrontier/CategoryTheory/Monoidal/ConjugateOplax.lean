module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Conjugates of monoidal transformations of right adjoints

Let `L₁ ⊣ R₁` and `L₂ ⊣ R₂` be monoidal adjunctions between monoidal categories, i.e. the left
adjoints are oplax monoidal, the right adjoints lax monoidal and the two structures are mates.
A natural transformation `α : L₂ ⟶ L₁` has a conjugate `R₁ ⟶ R₂`. If the conjugate is a monoidal
natural transformation, then `α` is compatible with the two oplax tensorators:

`α_{A ⊗ B} ≫ δ₁(A, B) = δ₂(A, B) ≫ (α_A ⊗ α_B)`.

## Main results

* `CategoryTheory.Adjunction.app_tensor_comp_δ_of_isMonoidal_conjugateEquiv`: the compatibility
  of `α` with the oplax tensorators, from monoidality of its conjugate.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
  [L₁.OplaxMonoidal] [L₂.OplaxMonoidal] [R₁.LaxMonoidal] [R₂.LaxMonoidal]
  [adj₁.IsMonoidal] [adj₂.IsMonoidal]

/-- A transformation of oplax monoidal left adjoints whose conjugate is a monoidal transformation
of the lax monoidal right adjoints is compatible with the oplax tensorators. -/
theorem app_tensor_comp_δ_of_isMonoidal_conjugateEquiv (α : L₂ ⟶ L₁)
    [NatTrans.IsMonoidal (conjugateEquiv adj₁ adj₂ α)] (A B : C) :
    α.app (A ⊗ B) ≫ δ L₁ A B = δ L₂ A B ≫ (α.app A ⊗ₘ α.app B) := by
  apply (adj₂.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← Category.assoc, ← unit_conjugateEquiv adj₁ adj₂ α (A ⊗ B), Category.assoc,
    ← (conjugateEquiv adj₁ adj₂ α).naturality, ← Category.assoc,
    Adjunction.unit_app_tensor_comp_map_δ adj₁, Category.assoc, NatTrans.IsMonoidal.tensor,
    tensorHom_comp_tensorHom_assoc, unit_conjugateEquiv, unit_conjugateEquiv,
    ← tensorHom_comp_tensorHom_assoc, μ_natural,
    ← reassoc_of% (Adjunction.unit_app_tensor_comp_map_δ adj₂ A B)]

end CategoryTheory.Adjunction

end
