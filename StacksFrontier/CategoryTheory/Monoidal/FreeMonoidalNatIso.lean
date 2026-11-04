module

public import Mathlib.CategoryTheory.Monoidal.Free.Basic
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Monoidal natural isomorphisms out of a free monoidal category

Let `Φ₁, Φ₂ : F(C) ⥤ D` be monoidal functors out of the free monoidal category on a type `C`.
Isomorphisms `Φ₁(X) ≅ Φ₂(X)` on the generators `X : C` extend uniquely to a monoidal natural
isomorphism `Φ₁ ≅ Φ₂`: on `𝟙` it is `ε₁⁻¹ ≫ ε₂`, on `X ⊗ Y` it is `μ₁⁻¹ ≫ (τ_X ⊗ τ_Y) ≫ μ₂`, and
naturality with respect to the formal associators and unitors is the associativity and unitality
of `Φ₁` and `Φ₂`.

## Main definitions

* `CategoryTheory.FreeMonoidalCategory.liftNatIso`: the monoidal natural isomorphism `Φ₁ ≅ Φ₂`
  extending isomorphisms on the generators.

## Main results

* `CategoryTheory.FreeMonoidalCategory.liftNatIso_app_of`,
  `CategoryTheory.FreeMonoidalCategory.liftNatIso_app_tensor`: its components on the generators
  and on tensor products.
* `CategoryTheory.FreeMonoidalCategory.isMonoidal_liftNatIso`: it is monoidal.
-/

@[expose] public noncomputable section

universe v' u u'

namespace CategoryTheory.FreeMonoidalCategory

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

local notation "F" => FreeMonoidalCategory

variable {C : Type u} {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  (Φ₁ Φ₂ : F C ⥤ D) [Φ₁.Monoidal] [Φ₂.Monoidal] (τ : ∀ X : C, Φ₁.obj (of X) ≅ Φ₂.obj (of X))

section Project

variable {D' : Type*} [Category D'] [MonoidalCategory D'] (f : C → D')

/-- The unit morphism `ε` of `project f` is the identity of `𝟙_ D'`. -/
@[simp] theorem project_ε : ε (project f) = 𝟙 (𝟙_ D') := rfl

/-- The counit morphism `η` of `project f` is the identity of `𝟙_ D'`. -/
@[simp] theorem project_η : η (project f) = 𝟙 (𝟙_ D') := rfl

/-- The tensorator `μ` of `project f` is the identity. -/
@[simp] theorem project_μ (X Y : F C) :
    μ (project f) X Y = 𝟙 ((project f).obj X ⊗ (project f).obj Y) := rfl

/-- The oplax tensorator `δ` of `project f` is the identity. -/
@[simp] theorem project_δ (X Y : F C) :
    δ (project f) X Y = 𝟙 ((project f).obj X ⊗ (project f).obj Y) := rfl

/-- `project f` sends `X ⊗ Y` to the tensor product of the images of `X` and `Y`. -/
@[simp] theorem project_obj_tensor (X Y : F C) :
    (project f).obj (X ⊗ Y) = (project f).obj X ⊗ (project f).obj Y := rfl

/-- `project f` sends the formal unit to `𝟙_ D'`. -/
@[simp] theorem project_obj_unit : (project f).obj (𝟙_ (F C)) = 𝟙_ D' := rfl

/-- `project f` sends the generator `of X` to `f X`. -/
@[simp] theorem project_obj_of (X : C) : (project f).obj (of X) = f X := rfl

end Project

/-- The components of the extension of `τ`, by recursion on formal expressions. -/
def liftNatIsoApp : ∀ X : F C, Φ₁.obj X ≅ Φ₂.obj X
  | of X => τ X
  | unit => (εIso Φ₁).symm ≪≫ εIso Φ₂
  | tensor X Y => (μIso Φ₁ X Y).symm ≪≫ tensorIso (liftNatIsoApp X) (liftNatIsoApp Y) ≪≫
      μIso Φ₂ X Y

/-- The component of `liftNatIsoApp` at `X ⊗ Y` is the tensor product of its components at `X`
and `Y`, conjugated by the tensorators of `Φ₁` and `Φ₂`. -/
theorem liftNatIsoApp_tensor (X Y : F C) :
    liftNatIsoApp Φ₁ Φ₂ τ (X ⊗ Y) = (μIso Φ₁ X Y).symm ≪≫
      tensorIso (liftNatIsoApp Φ₁ Φ₂ τ X) (liftNatIsoApp Φ₁ Φ₂ τ Y) ≪≫ μIso Φ₂ X Y :=
  rfl

/-- The component of `liftNatIsoApp` at the formal unit is `ε₁⁻¹ ≫ ε₂`. -/
theorem liftNatIsoApp_unit :
    liftNatIsoApp Φ₁ Φ₂ τ (𝟙_ (F C)) = (εIso Φ₁).symm ≪≫ εIso Φ₂ :=
  rfl

private theorem naturality_inv_of_hom {X Y : F C} (e : X ≅ Y)
    (h : Φ₁.map e.hom ≫ (liftNatIsoApp Φ₁ Φ₂ τ Y).hom =
      (liftNatIsoApp Φ₁ Φ₂ τ X).hom ≫ Φ₂.map e.hom) :
    Φ₁.map e.inv ≫ (liftNatIsoApp Φ₁ Φ₂ τ X).hom =
      (liftNatIsoApp Φ₁ Φ₂ τ Y).hom ≫ Φ₂.map e.inv := by
  rw [← cancel_epi (Φ₁.map e.hom), ← Functor.map_comp_assoc, e.hom_inv_id, Functor.map_id,
    Category.id_comp, reassoc_of% h, ← Functor.map_comp, e.hom_inv_id, Functor.map_id,
    Category.comp_id]

private theorem naturality_associator (X Y Z : F C) :
    Φ₁.map (α_ X Y Z).hom ≫ (liftNatIsoApp Φ₁ Φ₂ τ (X ⊗ (Y ⊗ Z))).hom =
      (liftNatIsoApp Φ₁ Φ₂ τ ((X ⊗ Y) ⊗ Z)).hom ≫ Φ₂.map (α_ X Y Z).hom := by
  simp only [liftNatIsoApp_tensor, Iso.trans_hom, Iso.symm_hom, μIso_hom, μIso_inv,
    tensorIso_hom, map_associator, Category.assoc, μ_δ_assoc, ← tensorHom_id, ← id_tensorHom,
    tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id, μ_δ, μ_δ_assoc]
  conv_rhs => rw [← Category.id_comp (liftNatIsoApp Φ₁ Φ₂ τ Z).hom,
    ← tensorHom_comp_tensorHom_assoc, associator_naturality_assoc,
    tensorHom_comp_tensorHom_assoc, Category.comp_id]

private theorem naturality_leftUnitor (X : F C) :
    Φ₁.map (λ_ X).hom ≫ (liftNatIsoApp Φ₁ Φ₂ τ X).hom =
      (liftNatIsoApp Φ₁ Φ₂ τ (𝟙_ (F C) ⊗ X)).hom ≫ Φ₂.map (λ_ X).hom := by
  simp only [liftNatIsoApp_tensor, liftNatIsoApp_unit, Iso.trans_hom, Iso.symm_hom, μIso_hom,
    μIso_inv, εIso_hom, εIso_inv, tensorIso_hom, map_leftUnitor, Category.assoc, μ_δ_assoc]
  rw [tensorHom_def, Category.assoc, whisker_exchange_assoc, ← comp_whiskerRight_assoc,
    Category.assoc, ε_η, Category.comp_id, leftUnitor_naturality]

private theorem naturality_rightUnitor (X : F C) :
    Φ₁.map (ρ_ X).hom ≫ (liftNatIsoApp Φ₁ Φ₂ τ X).hom =
      (liftNatIsoApp Φ₁ Φ₂ τ (X ⊗ 𝟙_ (F C))).hom ≫ Φ₂.map (ρ_ X).hom := by
  simp only [liftNatIsoApp_tensor, liftNatIsoApp_unit, Iso.trans_hom, Iso.symm_hom, μIso_hom,
    μIso_inv, εIso_hom, εIso_inv, tensorIso_hom, map_rightUnitor, Category.assoc, μ_δ_assoc]
  rw [tensorHom_def', Category.assoc, ← whisker_exchange_assoc, ← whiskerLeft_comp_assoc,
    Category.assoc, ε_η, Category.comp_id, rightUnitor_naturality]

/-- Naturality of `liftNatIsoApp` is preserved under `⊗ₘ`. -/
private theorem naturality_tensorHom {X Y X' Y' : F C} (f : X ⟶ Y) (g : X' ⟶ Y')
    (hf : Φ₁.map f ≫ (liftNatIsoApp Φ₁ Φ₂ τ Y).hom = (liftNatIsoApp Φ₁ Φ₂ τ X).hom ≫ Φ₂.map f)
    (hg : Φ₁.map g ≫ (liftNatIsoApp Φ₁ Φ₂ τ Y').hom =
      (liftNatIsoApp Φ₁ Φ₂ τ X').hom ≫ Φ₂.map g) :
    Φ₁.map (f ⊗ₘ g) ≫ (liftNatIsoApp Φ₁ Φ₂ τ (Y ⊗ Y')).hom =
      (liftNatIsoApp Φ₁ Φ₂ τ (X ⊗ X')).hom ≫ Φ₂.map (f ⊗ₘ g) := by
  simp only [liftNatIsoApp_tensor, Iso.trans_hom, Iso.symm_hom, μIso_hom, μIso_inv,
    tensorIso_hom, map_tensor, Category.assoc, μ_δ_assoc, tensorHom_comp_tensorHom_assoc, hf, hg]

/-- Naturality of the extension of `τ`. -/
theorem liftNatIsoApp_naturality {X Y : F C} (f : X ⟶ Y) :
    Φ₁.map f ≫ (liftNatIsoApp Φ₁ Φ₂ τ Y).hom = (liftNatIsoApp Φ₁ Φ₂ τ X).hom ≫ Φ₂.map f := by
  induction f using Hom.inductionOn with
  | id X => simp
  | α_hom X Y Z => exact naturality_associator Φ₁ Φ₂ τ X Y Z
  | α_inv X Y Z =>
    exact naturality_inv_of_hom Φ₁ Φ₂ τ (α_ X Y Z) (naturality_associator Φ₁ Φ₂ τ X Y Z)
  | l_hom X => exact naturality_leftUnitor Φ₁ Φ₂ τ X
  | l_inv X => exact naturality_inv_of_hom Φ₁ Φ₂ τ (λ_ X) (naturality_leftUnitor Φ₁ Φ₂ τ X)
  | ρ_hom X => exact naturality_rightUnitor Φ₁ Φ₂ τ X
  | ρ_inv X => exact naturality_inv_of_hom Φ₁ Φ₂ τ (ρ_ X) (naturality_rightUnitor Φ₁ Φ₂ τ X)
  | comp f g hf hg => rw [Functor.map_comp, Category.assoc, hg, reassoc_of% hf, Functor.map_comp]
  | whiskerLeft X f hf => simpa using naturality_tensorHom Φ₁ Φ₂ τ (𝟙 X) f (by simp) hf
  | whiskerRight f Z hf => simpa using naturality_tensorHom Φ₁ Φ₂ τ f (𝟙 Z) hf (by simp)

/-- **Monoidal natural isomorphisms out of a free monoidal category.** The natural isomorphism
`Φ₁ ≅ Φ₂` extending the isomorphisms `τ` on the generators. -/
def liftNatIso : Φ₁ ≅ Φ₂ :=
  NatIso.ofComponents (liftNatIsoApp Φ₁ Φ₂ τ) (liftNatIsoApp_naturality Φ₁ Φ₂ τ)

/-- The component of `liftNatIso` at `X` is `liftNatIsoApp` at `X`. -/
@[simp]
theorem liftNatIso_app (X : F C) : (liftNatIso Φ₁ Φ₂ τ).app X = liftNatIsoApp Φ₁ Φ₂ τ X :=
  rfl

/-- The component of `liftNatIso` at a generator `of X` is `τ X`. -/
@[simp]
theorem liftNatIso_app_of (X : C) : (liftNatIso Φ₁ Φ₂ τ).app (of X) = τ X :=
  rfl

/-- The component of `liftNatIso` at `X ⊗ Y` is the tensor product of its components at `X`
and `Y`, conjugated by the tensorators of `Φ₁` and `Φ₂`. -/
theorem liftNatIso_app_tensor (X Y : F C) :
    (liftNatIso Φ₁ Φ₂ τ).app (X ⊗ Y) = (μIso Φ₁ X Y).symm ≪≫
      tensorIso ((liftNatIso Φ₁ Φ₂ τ).app X) ((liftNatIso Φ₁ Φ₂ τ).app Y) ≪≫ μIso Φ₂ X Y :=
  rfl

/-- The extension of `τ` is a monoidal natural transformation. -/
instance isMonoidal_liftNatIso : NatTrans.IsMonoidal (liftNatIso Φ₁ Φ₂ τ).hom where
  unit := by
    change ε Φ₁ ≫ ((εIso Φ₁).symm ≪≫ εIso Φ₂).hom = ε Φ₂
    simp
  tensor X Y := by
    change μ Φ₁ X Y ≫ ((μIso Φ₁ X Y).symm ≪≫ tensorIso _ _ ≪≫ μIso Φ₂ X Y).hom = _
    simp
    rfl

end CategoryTheory.FreeMonoidalCategory
