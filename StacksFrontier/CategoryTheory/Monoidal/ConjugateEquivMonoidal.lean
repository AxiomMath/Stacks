module

public import StacksFrontier.CategoryTheory.Monoidal.ConjugateMonoidal

/-!
# Conjugates of oplax monoidal transformations of left adjoints

Let `L₁ ⊣ R₁` and `L₂ ⊣ R₂` be monoidal adjunctions (`CategoryTheory.Adjunction.IsMonoidal`):
the left adjoints are oplax monoidal, the right adjoints lax monoidal, compatibly. A natural
transformation `β : L₂ ⟶ L₁` compatible with the oplax structures has a conjugate
`R₁ ⟶ R₂` (`CategoryTheory.conjugateEquiv`) which is a monoidal natural transformation of the
lax structures (`CategoryTheory.Adjunction.isMonoidal_conjugateEquiv`). The converse direction is
`CategoryTheory.Adjunction.conjugateEquiv_symm_app_unit_comp_η` and
`CategoryTheory.Adjunction.conjugateEquiv_symm_app_tensor_comp_δ`.

This is the doctrinal adjunction principle for transformations, used to transport monoidality
between the inverse and the direct images of sheaves, for the Frobenius equivariance of cup
products in the purity half of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `CategoryTheory.Adjunction.isMonoidal_conjugateEquiv`.
* `CategoryTheory.Adjunction.μ_comp_map_comp_homEquiv_symm`: transposing a pairing
  compatibility along a monoidal adjunction of endofunctors.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open MonoidalCategory Functor.OplaxMonoidal Functor.LaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
  [L₁.OplaxMonoidal] [L₂.OplaxMonoidal] [R₁.LaxMonoidal] [R₂.LaxMonoidal]
  [adj₁.IsMonoidal] [adj₂.IsMonoidal]

/-- **The conjugate of an oplax monoidal transformation of left adjoints is monoidal.** For
monoidal adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂` and `β : L₂ ⟶ L₁` compatible with the oplax
structures, the conjugate `R₁ ⟶ R₂` is a monoidal natural transformation. -/
theorem isMonoidal_conjugateEquiv (β : L₂ ⟶ L₁) (hη : β.app (𝟙_ C) ≫ η L₁ = η L₂)
    (hδ : ∀ X Y : C, β.app (X ⊗ Y) ≫ δ L₁ X Y = δ L₂ X Y ≫ (β.app X ⊗ₘ β.app Y)) :
    NatTrans.IsMonoidal (conjugateEquiv adj₁ adj₂ β) where
  unit := by
    apply (adj₂.homEquiv _ _).symm.injective
    rw [homEquiv_counit, homEquiv_counit, Functor.map_comp, Category.assoc,
      conjugateEquiv_counit, β.naturality_assoc, map_ε_comp_counit_app_unit adj₁, hη,
      map_ε_comp_counit_app_unit adj₂]
  tensor X Y := by
    apply (adj₂.homEquiv _ _).symm.injective
    rw [homEquiv_counit, homEquiv_counit, Functor.map_comp, Category.assoc,
      conjugateEquiv_counit, β.naturality_assoc, map_μ_comp_counit_app_tensor adj₁,
      reassoc_of% (hδ (R₁.obj X) (R₁.obj Y)), Functor.map_comp, Category.assoc,
      map_μ_comp_counit_app_tensor adj₂, ← δ_natural_assoc, tensorHom_comp_tensorHom,
      tensorHom_comp_tensorHom, conjugateEquiv_counit, conjugateEquiv_counit]

end CategoryTheory.Adjunction

namespace CategoryTheory.Adjunction

open MonoidalCategory Functor.OplaxMonoidal Functor.LaxMonoidal

section Transpose

variable {C : Type*} [Category* C] [MonoidalCategory C] {Φ Ψ : C ⥤ C} (adj : Φ ⊣ Ψ)
  [Φ.Monoidal] [Ψ.LaxMonoidal] [adj.IsMonoidal]

/-- **Transposing a pairing compatibility along a monoidal adjunction.** Let `Φ ⊣ Ψ` be a
monoidal adjunction of endofunctors, `μ : F ⊗ G ⟶ T` a pairing and `τ_X : X ⟶ Ψ X` for
`X = F, G, T`, with transposes `σ_X : Φ X ⟶ X`. If the `τ` are compatible with `μ` through the
lax structure of `Ψ`, then the `σ` are compatible with `μ` through the monoidal structure of `Φ`:
this is the hypothesis of `Stacks.ExtCup.twistAction_cup`. -/
theorem μ_comp_map_comp_homEquiv_symm {F G T : C} (μ' : F ⊗ G ⟶ T) (τF : F ⟶ Ψ.obj F)
    (τG : G ⟶ Ψ.obj G) (τT : T ⟶ Ψ.obj T)
    (h : (τF ⊗ₘ τG) ≫ μ Ψ F G ≫ Ψ.map μ' = μ' ≫ τT) :
    μ Φ F G ≫ Φ.map μ' ≫ (adj.homEquiv _ _).symm τT =
      ((adj.homEquiv _ _).symm τF ⊗ₘ (adj.homEquiv _ _).symm τG) ≫ μ' := by
  rw [← cancel_epi (δ Φ F G), Functor.Monoidal.δ_μ_assoc]
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply, Adjunction.homEquiv_unit,
    Functor.map_comp, Functor.map_comp, ← Category.assoc, unit_app_tensor_comp_map_δ adj,
    Category.assoc, ← μ_natural_assoc, ← h, tensorHom_comp_tensorHom_assoc]
  congr 2 <;> exact ((adj.homEquiv _ _).apply_symm_apply _).symm.trans
    (Adjunction.homEquiv_unit _ _ _ _)

end Transpose

end CategoryTheory.Adjunction

end
