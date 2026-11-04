module

public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMap
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The projection-formula map of an adjunction along a composite

Let `L₁ ⊣ R₁` and `L₂ ⊣ R₂` be adjunctions, `L₁ : C ⥤ D`, `L₂ : D ⥤ E`, and let `L ⊣ R` be an
adjunction `C ⥤ E` which *is* their composite, read through isomorphisms `λ : L₁ ⋙ L₂ ≅ L` and
`ρ : R₂ ⋙ R₁ ≅ R`. Given bifunctors `A`, `A'`, `B` on `C`, `D`, `E` and comparisons `α₁`, `α₂`, `α`
for `L₁`, `L₂`, `L`, of which the one for `L` is the composite of the other two read through `λ`,
the projection-formula map `CategoryTheory.adjunctionTensorMap` of `L ⊣ R` is the one of `L₁ ⊣ R₁`
followed by `R₁` of the one of `L₂ ⊣ R₂`, read through `λ` and `ρ`.

## Main results

* `CategoryTheory.adjunctionTensorMap_comp_ofNatIso`: the factorization.

## Implementation notes

The statement takes the identification of `L ⊣ R` with the composite as an equality of
adjunctions, `((adj₁.comp adj₂).ofNatIsoLeft λ).ofNatIsoRight ρ = adj`, which is the form in which
it is available for derived pullback and pushforward along a composite of ringed spaces
(`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_comp`). After substituting
it, transposition under `adj` is transposition under `adj₂` and then under `adj₁`
(`CategoryTheory.Adjunction.comp_homEquiv`), and the two sides are compared there, by naturality
of the comparisons and the formula for the counit of a composite.
-/

@[expose] public section

namespace CategoryTheory

open scoped CategoryTheory.Prod

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : D ⥤ E} {R₂ : E ⥤ D} {L : C ⥤ E} {R : E ⥤ C}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj : L ⊣ R)
  (lam : L₁ ⋙ L₂ ≅ L) (ρ : R₂ ⋙ R₁ ≅ R)
  (A : C × C ⥤ C) (A' : D × D ⥤ D) (B : E × E ⥤ E)
  (α₁ : A ⋙ L₁ ⟶ L₁.prod L₁ ⋙ A') (α₂ : A' ⋙ L₂ ⟶ L₂.prod L₂ ⋙ B)
  (α : A ⋙ L ⟶ L.prod L ⋙ B)

/-- **The projection-formula map along a composite of adjunctions.** If `adj` is the composite
`adj₁.comp adj₂` read through `lam : L₁ ⋙ L₂ ≅ L` and `ρ : R₂ ⋙ R₁ ≅ R`, and the comparison `α`
for `L` is `L₂` of the comparison `α₁` for `L₁` followed by the comparison `α₂` for `L₂`, read
through `lam`, then the projection-formula map of `adj₁` at `(R₂ G, H)` followed by `R₁` of that of
`adj₂` at `(G, L₁ H)`, by `ρ`, and by `R` of `lam` in the second tensor factor, is `ρ` in the first
tensor factor followed by the projection-formula map of `adj` at `(G, H)`. -/
theorem adjunctionTensorMap_comp_ofNatIso
    (hadj : ((adj₁.comp adj₂).ofNatIsoLeft lam).ofNatIsoRight ρ = adj)
    (hα : ∀ P Q : C, lam.hom.app (A.obj (P, Q)) ≫ α.app (P, Q) =
      L₂.map (α₁.app (P, Q)) ≫ α₂.app (L₁.obj P, L₁.obj Q) ≫
        B.map (lam.hom.app P ×ₘ lam.hom.app Q))
    (G : E) (H : C) :
    adjunctionTensorMap adj₁ A A' α₁ (R₂.obj G) H ≫
        R₁.map (adjunctionTensorMap adj₂ A' B α₂ G (L₁.obj H)) ≫ ρ.hom.app _ ≫
          R.map (B.map (𝟙 G ×ₘ lam.hom.app H)) =
      A.map (ρ.hom.app G ×ₘ 𝟙 H) ≫ adjunctionTensorMap adj A B α G H := by
  subst hadj
  have nα := bifunctor_comparison_naturality A B α (ρ.hom.app G) (𝟙 H)
  have nα₂ := bifunctor_comparison_naturality A' B α₂ (adj₁.counit.app (R₂.obj G))
    (𝟙 (L₁.obj H))
  have hε : (((adj₁.comp adj₂).ofNatIsoLeft lam).ofNatIsoRight ρ).counit.app G =
      L.map (ρ.inv.app G) ≫ lam.inv.app _ ≫ L₂.map (adj₁.counit.app (R₂.obj G)) ≫
        adj₂.counit.app G := by
    simp [Adjunction.comp]
  have inner : L₂.map (α₁.app (R₁.obj (R₂.obj G), H)) ≫
        L₂.map (A'.map (adj₁.counit.app (R₂.obj G) ×ₘ 𝟙 (L₁.obj H))) ≫
        α₂.app (R₂.obj G, L₁.obj H) ≫ B.map (adj₂.counit.app G ×ₘ 𝟙 (L₂.obj (L₁.obj H))) ≫
          B.map (𝟙 G ×ₘ lam.hom.app H) =
      lam.hom.app (A.obj (R₁.obj (R₂.obj G), H)) ≫ L.map (A.map (ρ.hom.app G ×ₘ 𝟙 H)) ≫
        α.app (R.obj G, H) ≫
        B.map ((((adj₁.comp adj₂).ofNatIsoLeft lam).ofNatIsoRight ρ).counit.app G ×ₘ
          𝟙 (L.obj H)) := by
    rw [reassoc_of% nα, reassoc_of% (hα _ _), hε, reassoc_of% nα₂]
    simp only [Functor.comp_obj, CategoryTheory.Functor.map_id, Category.id_comp,
      Category.assoc, ← B.map_comp, prod_comp, Iso.hom_inv_id_app_assoc, Category.comp_id,
      ← L.map_comp_assoc, Iso.hom_inv_id_app]
    simp
  unfold adjunctionTensorMap
  rw [← Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.homEquiv_ofNatIsoLeft_apply, Adjunction.comp_homEquiv, Equiv.trans_apply,
    ← ρ.hom.naturality, Functor.comp_map, ← R₁.map_comp_assoc,
    ← Adjunction.homEquiv_naturality_right, ← Category.assoc,
    ← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_left]
  simp only [Category.assoc, Functor.map_comp, Functor.comp_obj]
  rw [inner]

end CategoryTheory

end
