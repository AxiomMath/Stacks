module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackMap

/-!
# The transpose comparison does not depend on the presentation of the tensor products

`Stacks.Cohomology.DerivedInternalHomPullback.Transpose.homComparison` is the comparison
`P(hom(A, B)) ⟶ hom(P A, P B)` of a functor `P` with two internal Homs, built from a tensor
product on each side, a tensor–hom bijection on each side and a comparison
`m : T₁ ⋙ P ≅ P.prod P ⋙ T₂` of the tensor products. This file records that replacing each
tensor product by an isomorphic bifunctor, the bijections and the comparison being carried along
those isomorphisms, does not change the comparison.

## Main results

* `Stacks.Cohomology.DerivedInternalHomPullback.Transpose.homComparison_changeOfTensor`.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedInternalHomPullback.Transpose

variable {D₁ D₂ : Type*} [Category D₁] [Category D₂]
  (P : D₁ ⥤ D₂) (H₁ : D₁ᵒᵖ ⥤ D₁ ⥤ D₁) (H₂ : D₂ᵒᵖ ⥤ D₂ ⥤ D₂)
  {T₁ T₁' : D₁ × D₁ ⥤ D₁} {T₂ T₂' : D₂ × D₂ ⥤ D₂}
  (e₁ : ∀ A B C : D₁, (A ⟶ (H₁.obj (op B)).obj C) ≃ (T₁.obj (A, B) ⟶ C))
  (e₂ : ∀ A B C : D₂, (A ⟶ (H₂.obj (op B)).obj C) ≃ (T₂.obj (A, B) ⟶ C))
  (e₁' : ∀ A B C : D₁, (A ⟶ (H₁.obj (op B)).obj C) ≃ (T₁'.obj (A, B) ⟶ C))
  (e₂' : ∀ A B C : D₂, (A ⟶ (H₂.obj (op B)).obj C) ≃ (T₂'.obj (A, B) ⟶ C))
  (m : T₁ ⋙ P ≅ P.prod P ⋙ T₂) (m' : T₁' ⋙ P ≅ P.prod P ⋙ T₂')
  (τ₁ : T₁ ≅ T₁') (τ₂ : T₂ ≅ T₂')

/-- **The transpose comparison is unchanged by a change of presentation of the tensor
products.** If `T₁ ≅ T₁'` and `T₂ ≅ T₂'`, the primed bijections are the unprimed ones
precomposed with these isomorphisms, and the primed comparison is the unprimed one conjugated by
them, then the two transpose comparisons agree. -/
theorem homComparison_changeOfTensor
    (he₁ : ∀ A B C (g : A ⟶ (H₁.obj (op B)).obj C),
      e₁' A B C g = τ₁.inv.app (A, B) ≫ e₁ A B C g)
    (he₂ : ∀ A B C (g : A ⟶ (H₂.obj (op B)).obj C),
      e₂' A B C g = τ₂.inv.app (A, B) ≫ e₂ A B C g)
    (hm : ∀ A B, m'.inv.app (A, B) =
      τ₂.inv.app (P.obj A, P.obj B) ≫ m.inv.app (A, B) ≫ P.map (τ₁.hom.app (A, B)))
    (A B : D₁) :
    homComparison P H₁ H₂ T₁' T₂' e₁' e₂' m' A B = homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m A B := by
  apply (e₂ _ _ _).injective
  rw [homComparison_adjoint]
  have h := homComparison_adjoint P H₁ H₂ T₁' T₂' e₁' e₂' m' A B
  rw [he₂, homComparisonDatum, hm, evaluation, he₁] at h
  rw [homComparisonDatum, evaluation]
  have h' := congrArg (τ₂.hom.app _ ≫ ·) h
  simp only [Iso.hom_inv_id_app_assoc, Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app_assoc] at h'
  exact h'

end Stacks.Cohomology.DerivedInternalHomPullback.Transpose
