module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Transitions between direct images along a triangle of inverse images

Let `J₀ ⊣ K₀` and `J₁ ⊣ K₁` be adjunctions out of a category `C`, let `s : D₁ ⥤ D₀`, and let
`J₀ ≅ J₁ ⋙ s` (for closed immersions `j₀ = s ≫ j₁` of algebraic spaces: `j₀^* ≅ s^* j₁^*`).  For
`P : D₁` and a morphism `φ : s P ⟶ Q`, the unit of `J₀ ⊣ K₀`, the comparison and the counit of
`J₁ ⊣ K₁` give a map `K₁ P ⟶ K₀ Q`, `CategoryTheory.Adjunction.pushTransition`.  Through the two
adjunctions it acts on transposes by `α ↦ s α ≫ φ`
(`CategoryTheory.Adjunction.homEquiv_comp_pushTransition`); in particular, for `P = J₁ F` and the
comparison `s J₁ F ≅ J₀ F` as `φ`, it carries the unit of `J₁ ⊣ K₁` to the unit of `J₀ ⊣ K₀`
(`CategoryTheory.Adjunction.unit_comp_pushTransition`).
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {C D₀ D₁ : Type*} [Category* C] [Category* D₀] [Category* D₁]
  {J₀ : C ⥤ D₀} {K₀ : D₀ ⥤ C} {J₁ : C ⥤ D₁} {K₁ : D₁ ⥤ C}
  (adj₀ : J₀ ⊣ K₀) (adj₁ : J₁ ⊣ K₁) {s : D₁ ⥤ D₀} (tri : J₀ ≅ J₁ ⋙ s)

/-- The map `K₁ P ⟶ K₀ Q` induced by `φ : s P ⟶ Q` through the comparison `J₀ ≅ J₁ ⋙ s`. -/
def pushTransition (P : D₁) {Q : D₀} (φ : s.obj P ⟶ Q) : K₁.obj P ⟶ K₀.obj Q :=
  adj₀.unit.app (K₁.obj P) ≫ K₀.map (tri.hom.app (K₁.obj P) ≫ s.map (adj₁.counit.app P) ≫ φ)

/-- The transition `K₁ P ⟶ K₀ Q` is the unit of `J₀ ⊣ K₀` at `K₁ P` followed by the direct image
of the composite of the comparison, `s` applied to the counit of `J₁ ⊣ K₁` at `P`, and `φ`. -/
theorem pushTransition_eq (P : D₁) {Q : D₀} (φ : s.obj P ⟶ Q) :
    pushTransition adj₀ adj₁ tri P φ =
      adj₀.unit.app (K₁.obj P) ≫
        K₀.map (tri.hom.app (K₁.obj P) ≫ s.map (adj₁.counit.app P) ≫ φ) := rfl

/-- Composition with the transition, through the adjunction `J₀ ⊣ K₀`. -/
theorem comp_pushTransition {G : C} {P : D₁} {Q : D₀} (φ : s.obj P ⟶ Q) (f : G ⟶ K₁.obj P) :
    f ≫ pushTransition adj₀ adj₁ tri P φ =
      adj₀.homEquiv G Q (J₀.map f ≫ tri.hom.app (K₁.obj P) ≫ s.map (adj₁.counit.app P) ≫ φ) := by
  rw [pushTransition, Adjunction.homEquiv_unit, ← Category.assoc, ← adj₀.unit_naturality,
    Category.assoc, ← K₀.map_comp]

/-- **The transition acts on transposes by `α ↦ s α ≫ φ`.** -/
theorem homEquiv_comp_pushTransition {G : C} {P : D₁} {Q : D₀} (φ : s.obj P ⟶ Q)
    (α : J₁.obj G ⟶ P) :
    adj₁.homEquiv G P α ≫ pushTransition adj₀ adj₁ tri P φ =
      adj₀.homEquiv G Q (tri.hom.app G ≫ s.map α ≫ φ) := by
  rw [comp_pushTransition]
  congr 1
  have h₁ := tri.hom.naturality (adj₁.homEquiv G P α)
  simp only [Functor.comp_map] at h₁
  rw [reassoc_of% h₁, ← s.map_comp_assoc]
  congr 2
  simp [Adjunction.homEquiv_unit]

/-- **The transition carries the unit of `J₁ ⊣ K₁` to the unit of `J₀ ⊣ K₀`.** -/
@[reassoc]
theorem unit_comp_pushTransition (F : C) :
    adj₁.unit.app F ≫ pushTransition adj₀ adj₁ tri (J₁.obj F) (tri.inv.app F) =
      adj₀.unit.app F := by
  have h := homEquiv_comp_pushTransition adj₀ adj₁ tri (tri.inv.app F) (𝟙 (J₁.obj F))
  rw [Adjunction.homEquiv_id, CategoryTheory.Functor.map_id] at h
  simpa [Adjunction.homEquiv_unit] using h

/-- When the counit at `P` and `φ` are invertible, the transition is the unit followed by the
direct image of an isomorphism `J₀ K₁ P ⟶ Q`. -/
theorem exists_isIso_pushTransition (P : D₁) {Q : D₀} (φ : s.obj P ⟶ Q)
    [IsIso (adj₁.counit.app P)] [IsIso φ] :
    ∃ l : J₀.obj (K₁.obj P) ⟶ Q, IsIso l ∧
      pushTransition adj₀ adj₁ tri P φ = adj₀.unit.app (K₁.obj P) ≫ K₀.map l :=
  ⟨_, inferInstance, rfl⟩

end CategoryTheory.Adjunction
