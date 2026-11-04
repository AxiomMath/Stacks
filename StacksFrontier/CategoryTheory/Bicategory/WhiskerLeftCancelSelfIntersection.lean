module

public import Mathlib.CategoryTheory.Bicategory.Strict.Basic
public import Mathlib.CategoryTheory.EqToHom

/-!
# Cancelling a morphism of self-intersections on 2-cells, in a strict bicategory

Let `γη : pη ∘ y ⟶ qη ∘ y` and `γξ : pξ ∘ x ⟶ qξ ∘ x` be 2-cells in a strict bicategory,
`c : y ⟶ f ∘ x` an invertible 2-cell, and `Φ` a 1-morphism with `Φ^*γξ = (qη^*c) ∘ γη ∘ (pη^*c⁻¹)`
up to the identifications of the composites. Then for two 1-morphisms `δ₁, δ₂` with
`δ₁ ∘ pη = δ₂ ∘ pη`, `δ₁ ∘ qη = δ₂ ∘ qη` and `δ₁ ∘ Φ = δ₂ ∘ Φ`, the whiskerings `δ₁^*γη` and
`δ₂^*γη` agree, up to the identifications
(`CategoryTheory.Bicategory.whiskerLeft_eq_of_comp_eq_of_selfIntersection`).

The lemma `CategoryTheory.Bicategory.whiskerLeft_eq_of_selfIntersection` expresses each `δ ^*γη`
through the composites `δ ∘ pη`, `δ ∘ qη`, `δ ∘ Φ`, taken as variables.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

namespace CategoryTheory

/-- Two morphisms that are `eqToHom`-sandwiches of one and the same morphism differ by
`eqToHom`s. -/
theorem eq_eqToHom_comp_comp_eqToHom_of_sandwiches {𝒞 : Type*} [Category 𝒞]
    {P₁ Q₁ P₂ Q₂ R R' : 𝒞} {X : P₁ ⟶ Q₁} {Y : P₂ ⟶ Q₂} {M : R ⟶ R'} (a₁ : P₁ = R)
    (b₁ : R' = Q₁) (a₂ : P₂ = R) (b₂ : R' = Q₂) (hX : X = eqToHom a₁ ≫ M ≫ eqToHom b₁)
    (hY : Y = eqToHom a₂ ≫ M ≫ eqToHom b₂) (e₁ : P₁ = P₂) (e₂ : Q₂ = Q₁) :
    X = eqToHom e₁ ≫ Y ≫ eqToHom e₂ := by
  subst hX hY a₁ b₁ e₁ e₂
  simp

end CategoryTheory

namespace CategoryTheory.Bicategory

universe w₀ v₀ u₀

variable {𝔅 : Type u₀} [Bicategory.{w₀, v₀} 𝔅] [Bicategory.Strict 𝔅]

/-- **A whiskering read through the composites with `pη`, `qη` and `Φ`.** -/
theorem whiskerLeft_eq_of_selfIntersection {T A B P Q C : 𝔅} {pη qη : P ⟶ A} {y : A ⟶ C}
    (γη : pη ≫ y ⟶ qη ≫ y) {pξ qξ : Q ⟶ B} {x : B ⟶ C} (γξ : pξ ≫ x ⟶ qξ ≫ x) {f : A ⟶ B}
    (c : y ⟶ f ≫ x) [IsIso c] {Φ : P ⟶ Q} (e₀ : Φ ≫ pξ ≫ x = pη ≫ f ≫ x)
    (e₃ : qη ≫ f ≫ x = Φ ≫ qξ ≫ x)
    (hΦ : Φ ◁ γξ = eqToHom e₀ ≫ ((pη ◁ inv c) ≫ γη ≫ (qη ◁ c)) ≫ eqToHom e₃)
    (δ : T ⟶ P) (dp dq : T ⟶ A) (D : T ⟶ Q) (hp : δ ≫ pη = dp) (hq : δ ≫ qη = dq)
    (hD : δ ≫ Φ = D) (a₁ : δ ≫ pη ≫ y = dp ≫ y) (a₂ : dp ≫ f ≫ x = D ≫ pξ ≫ x)
    (a₃ : D ≫ qξ ≫ x = dq ≫ f ≫ x) (a₄ : dq ≫ y = δ ≫ qη ≫ y) :
    δ ◁ γη = eqToHom a₁ ≫ ((dp ◁ c) ≫ eqToHom a₂ ≫ (D ◁ γξ) ≫ eqToHom a₃ ≫ (dq ◁ inv c)) ≫
      eqToHom a₄ := by
  subst hp hq hD
  simp only [Category.assoc]
  rw [comp_whiskerLeft δ Φ γξ, hΦ, comp_whiskerLeft, comp_whiskerLeft]
  simp only [whiskerLeft_comp, Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv,
    whiskerLeft_eqToHom, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  simp only [← Category.assoc, ← whiskerLeft_comp, IsIso.hom_inv_id, whiskerLeft_id,
    Category.id_comp]
  simp only [Category.assoc, Category.comp_id, eqToHom_trans, eqToHom_refl]

/-- **A morphism of self-intersections is injective on 2-cells of sections with equal
projections.** -/
theorem whiskerLeft_eq_of_comp_eq_of_selfIntersection {T A B P Q C : 𝔅} {pη qη : P ⟶ A}
    {y : A ⟶ C} (γη : pη ≫ y ⟶ qη ≫ y) {pξ qξ : Q ⟶ B} {x : B ⟶ C} (γξ : pξ ≫ x ⟶ qξ ≫ x)
    {f : A ⟶ B} (c : y ⟶ f ≫ x) [IsIso c] {Φ : P ⟶ Q} (e₀ : Φ ≫ pξ ≫ x = pη ≫ f ≫ x)
    (e₃ : qη ≫ f ≫ x = Φ ≫ qξ ≫ x)
    (hΦ : Φ ◁ γξ = eqToHom e₀ ≫ ((pη ◁ inv c) ≫ γη ≫ (qη ◁ c)) ≫ eqToHom e₃)
    {δ₁ δ₂ : T ⟶ P} (hp : δ₁ ≫ pη = δ₂ ≫ pη) (hq : δ₁ ≫ qη = δ₂ ≫ qη) (hΦδ : δ₁ ≫ Φ = δ₂ ≫ Φ)
    (e₁ : δ₁ ≫ pη ≫ y = δ₂ ≫ pη ≫ y) (e₂ : δ₂ ≫ qη ≫ y = δ₁ ≫ qη ≫ y) :
    δ₁ ◁ γη = eqToHom e₁ ≫ (δ₂ ◁ γη) ≫ eqToHom e₂ := by
  have hpξ : (δ₂ ≫ Φ) ≫ pξ ≫ x = (δ₂ ≫ pη) ≫ f ≫ x := by
    rw [Strict.assoc, e₀, ← Strict.assoc]
  have hqξ : (δ₂ ≫ Φ) ≫ qξ ≫ x = (δ₂ ≫ qη) ≫ f ≫ x := by
    rw [Strict.assoc, ← e₃, ← Strict.assoc]
  refine eq_eqToHom_comp_comp_eqToHom_of_sandwiches _ _ _ _
    (whiskerLeft_eq_of_selfIntersection γη γξ c e₀ e₃ hΦ δ₁ (δ₂ ≫ pη) (δ₂ ≫ qη) (δ₂ ≫ Φ) hp hq
      hΦδ (by rw [← Strict.assoc, hp]) hpξ.symm hqξ (by rw [← hq, Strict.assoc]))
    (whiskerLeft_eq_of_selfIntersection γη γξ c e₀ e₃ hΦ δ₂ (δ₂ ≫ pη) (δ₂ ≫ qη) (δ₂ ≫ Φ) rfl rfl
      rfl (Strict.assoc _ _ _).symm hpξ.symm hqξ (Strict.assoc _ _ _)) e₁ e₂

end CategoryTheory.Bicategory
