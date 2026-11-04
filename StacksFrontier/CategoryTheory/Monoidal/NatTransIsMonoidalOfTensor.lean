module

public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Monoidal natural transformations from the compatibility with the tensorators

`CategoryTheory.NatTrans.isMonoidal_of_tensor`: a natural transformation `τ : F ⟶ G` from a lax
monoidal functor to a monoidal functor which is compatible with the tensorators and invertible at
the unit object is monoidal. The compatibility with the units follows from the left and right
unitality of `F` and `G`: both `ε F ≫ τ_𝟙` and `ε G`, whiskered by `G(𝟙)`, are determined by the
left unitor of `G(𝟙)`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace CategoryTheory.NatTrans

variable {C D : Type*} [Category C] [MonoidalCategory C] [Category D] [MonoidalCategory D]
  {F G : C ⥤ D} [F.LaxMonoidal] [G.Monoidal]

/-- **A natural transformation into a monoidal functor which is compatible with the tensorators
and invertible at the unit is monoidal**: the compatibility with the units follows from the left
and right unitality of both functors. -/
theorem isMonoidal_of_tensor (τ : F ⟶ G) [IsIso (τ.app (𝟙_ C))]
    (h : ∀ X Y, μ F X Y ≫ τ.app (X ⊗ Y) = (τ.app X ⊗ₘ τ.app Y) ≫ μ G X Y) :
    NatTrans.IsMonoidal τ where
  unit := by
    let a := ε F ≫ τ.app (𝟙_ C)
    let M := μ G (𝟙_ C) (𝟙_ C) ≫ G.map (λ_ (𝟙_ C)).hom
    have h1 : 𝟙_ D ◁ τ.app (𝟙_ C) ≫ a ▷ G.obj (𝟙_ C) ≫ M =
        𝟙_ D ◁ τ.app (𝟙_ C) ≫ ε G ▷ G.obj (𝟙_ C) ≫ M := by
      have e1 : 𝟙_ D ◁ τ.app (𝟙_ C) ≫ a ▷ G.obj (𝟙_ C) =
          ε F ▷ F.obj (𝟙_ C) ≫ (τ.app (𝟙_ C) ⊗ₘ τ.app (𝟙_ C)) := by
        rw [MonoidalCategory.whisker_exchange, MonoidalCategory.tensorHom_def,
          MonoidalCategory.comp_whiskerRight, Category.assoc]
      rw [← Category.assoc, e1, Category.assoc, ← Category.assoc _ (μ G _ _), ← h,
        Category.assoc, ← τ.naturality, ← Category.assoc, ← Category.assoc,
        Category.assoc (ε F ▷ _), ← Functor.LaxMonoidal.left_unitality,
        ← MonoidalCategory.leftUnitor_naturality, Functor.LaxMonoidal.left_unitality G (𝟙_ C)]
    have h2 : a ▷ G.obj (𝟙_ C) = ε G ▷ G.obj (𝟙_ C) := by
      rw [← cancel_epi (𝟙_ D ◁ τ.app (𝟙_ C)), ← cancel_mono M]
      simpa only [Category.assoc] using h1
    have h3 : a ▷ 𝟙_ D = ε G ▷ 𝟙_ D := (cancel_epi (𝟙_ D ◁ η G)).1 <| by
      rw [MonoidalCategory.whisker_exchange, MonoidalCategory.whisker_exchange, h2]
    change a = ε G
    rw [← cancel_mono (ρ_ (G.obj (𝟙_ C))).inv, MonoidalCategory.rightUnitor_inv_naturality,
      MonoidalCategory.rightUnitor_inv_naturality, h3]
  tensor := h

end CategoryTheory.NatTrans
