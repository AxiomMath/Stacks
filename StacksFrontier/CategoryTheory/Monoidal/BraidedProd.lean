module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# The product of two braided monoidal categories

The product `C₁ × C₂` of two monoidal categories carries Mathlib's componentwise monoidal
structure `CategoryTheory.MonoidalCategory.prodMonoidal`. This file adds the componentwise
braiding and symmetry, and records that the two projections are strict braided functors and
that the product `F.prod' G` of two braided functors is braided.

## Main definitions

* `CategoryTheory.MonoidalCategory.prodBraided`: the braiding of `C₁ × C₂`, componentwise.
* `CategoryTheory.MonoidalCategory.prodSymmetric`: the symmetry of `C₁ × C₂`, componentwise.
* `CategoryTheory.MonoidalCategory.fstBraided`, `CategoryTheory.MonoidalCategory.sndBraided`:
  the projections `C₁ × C₂ ⥤ Cᵢ` as braided functors.
* `CategoryTheory.MonoidalCategory.prod'Braided`: `F.prod' G` is braided when `F` and `G` are.
-/

@[expose] public section

universe v₀ v₁ v₂ u₀ u₁ u₂

namespace CategoryTheory.MonoidalCategory

open BraidedCategory

variable {C₁ : Type u₁} [Category.{v₁} C₁] [MonoidalCategory C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [MonoidalCategory C₂]

section Braided

variable [BraidedCategory C₁] [BraidedCategory C₂]

/-- The componentwise braiding of the product of two braided monoidal categories. -/
instance prodBraided : BraidedCategory (C₁ × C₂) where
  braiding X Y := (β_ X.1 Y.1).prod (β_ X.2 Y.2)
  braiding_naturality_right X Y Z f := by
    ext <;> simp [BraidedCategory.braiding_naturality_right]
  braiding_naturality_left f Z := by
    ext <;> simp [BraidedCategory.braiding_naturality_left]
  hexagon_forward X Y Z := by
    ext <;> simp
  hexagon_reverse X Y Z := by
    ext <;> simp

/-- The forward braiding of `C₁ × C₂` is the pair of the forward braidings of the components. -/
@[simp]
theorem prodBraided_braiding_hom (X Y : C₁ × C₂) :
    (β_ X Y).hom = ((β_ X.1 Y.1).hom, (β_ X.2 Y.2).hom) :=
  rfl

/-- The inverse braiding of `C₁ × C₂` is the pair of the inverse braidings of the components. -/
@[simp]
theorem prodBraided_braiding_inv (X Y : C₁ × C₂) :
    (β_ X Y).inv = ((β_ X.1 Y.1).inv, (β_ X.2 Y.2).inv) :=
  rfl

/-- The first projection is a strict monoidal functor. -/
instance fstMonoidal : (Prod.fst C₁ C₂).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _ }

/-- The second projection is a strict monoidal functor. -/
instance sndMonoidal : (Prod.snd C₁ C₂).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _ }

omit [BraidedCategory C₁] [BraidedCategory C₂] in
/-- The unit morphism `ε` of the first projection is the identity. -/
@[simp] theorem fst_ε : Functor.LaxMonoidal.ε (Prod.fst C₁ C₂) = 𝟙 _ := rfl

omit [BraidedCategory C₁] [BraidedCategory C₂] in
/-- The tensorator `μ X Y` of the first projection is the identity. -/
@[simp] theorem fst_μ (X Y : C₁ × C₂) : Functor.LaxMonoidal.μ (Prod.fst C₁ C₂) X Y = 𝟙 _ := rfl

omit [BraidedCategory C₁] [BraidedCategory C₂] in
/-- The counit morphism `η` of the first projection is the identity. -/
@[simp] theorem fst_η : Functor.OplaxMonoidal.η (Prod.fst C₁ C₂) = 𝟙 _ := rfl

omit [BraidedCategory C₁] [BraidedCategory C₂] in
/-- The cotensorator `δ X Y` of the first projection is the identity. -/
@[simp] theorem fst_δ (X Y : C₁ × C₂) : Functor.OplaxMonoidal.δ (Prod.fst C₁ C₂) X Y = 𝟙 _ := rfl

omit [BraidedCategory C₁] [BraidedCategory C₂] in
/-- The unit morphism `ε` of the second projection is the identity. -/
@[simp] theorem snd_ε : Functor.LaxMonoidal.ε (Prod.snd C₁ C₂) = 𝟙 _ := rfl

omit [BraidedCategory C₁] [BraidedCategory C₂] in
/-- The tensorator `μ X Y` of the second projection is the identity. -/
@[simp] theorem snd_μ (X Y : C₁ × C₂) : Functor.LaxMonoidal.μ (Prod.snd C₁ C₂) X Y = 𝟙 _ := rfl

omit [BraidedCategory C₁] [BraidedCategory C₂] in
/-- The counit morphism `η` of the second projection is the identity. -/
@[simp] theorem snd_η : Functor.OplaxMonoidal.η (Prod.snd C₁ C₂) = 𝟙 _ := rfl

omit [BraidedCategory C₁] [BraidedCategory C₂] in
/-- The cotensorator `δ X Y` of the second projection is the identity. -/
@[simp] theorem snd_δ (X Y : C₁ × C₂) : Functor.OplaxMonoidal.δ (Prod.snd C₁ C₂) X Y = 𝟙 _ := rfl

/-- The first projection is a braided functor. -/
instance fstBraided : (Prod.fst C₁ C₂).Braided where

/-- The second projection is a braided functor. -/
instance sndBraided : (Prod.snd C₁ C₂).Braided where

variable {D : Type u₀} [Category.{v₀} D] [MonoidalCategory D] [BraidedCategory D]
  (F : D ⥤ C₁) (G : D ⥤ C₂)

/-- The product of two braided functors is braided. -/
instance prod'Braided [F.Braided] [G.Braided] : (F.prod' G).Braided where
  braided X Y := by
    ext
    · simp
    · simp

end Braided

/-- The componentwise symmetry of the product of two symmetric monoidal categories. -/
instance prodSymmetric [SymmetricCategory C₁] [SymmetricCategory C₂] :
    SymmetricCategory (C₁ × C₂) where
  symmetry X Y := by ext <;> simp

end CategoryTheory.MonoidalCategory
