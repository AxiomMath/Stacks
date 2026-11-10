module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Mates of adjunctions between sheaves, on sections

Generic identities, over arbitrary sites, used to compare a mate of adjunctions between
categories of sheaves of modules with a mate of adjunctions between categories of sheaves of
types section by section: composites on sections, the unit square of a mate on sections, and
the detection of a morphism out of a left adjoint by its transpose on sections.  They are kept
over variables so that instantiating them involves no unfolding of the concrete functors.

## Main results

* `Stacks.CategoryTheory.SheafOfModules.mateEquiv_symm_unit_val_app`
* `Stacks.CategoryTheory.Sheaf.mateEquiv_symm_unit_hom_app`
* `Stacks.CategoryTheory.Sheaf.eq_of_unit_hom_app`
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Stacks.CategoryTheory

/-- A composite of three morphisms of sheaves of modules, on sections. -/
theorem SheafOfModules.comp₃_val_app {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat} {M₁ M₂ M₃ M₄ : SheafOfModules R} (a : M₁ ⟶ M₂) (b : M₂ ⟶ M₃)
    (c : M₃ ⟶ M₄) (W : Cᵒᵖ) (z : M₁.val.obj W) :
    (a ≫ b ≫ c).val.app W z = c.val.app W (b.val.app W (a.val.app W z)) := rfl

/-- A composite of three natural transformations of functors into sheaves of types, at an
object, on sections. -/
theorem Sheaf.comp₃_app_hom_app.{t} {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {F₁ F₂ F₃ F₄ : D ⥤ Sheaf J (Type t)} (a : F₁ ⟶ F₂)
    (b : F₂ ⟶ F₃) (c : F₃ ⟶ F₄) (X : D) (W : Cᵒᵖ) (z : (F₁.obj X).obj.obj W) :
    ((a ≫ b ≫ c).app X).hom.app W z =
      (c.app X).hom.app W ((b.app X).hom.app W ((a.app X).hom.app W z)) := rfl

/-- A composite of two morphisms of sheaves of modules, on sections. -/
theorem SheafOfModules.comp₂_val_app {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat} {M₁ M₂ M₃ : SheafOfModules R} (a : M₁ ⟶ M₂) (b : M₂ ⟶ M₃)
    (W : Cᵒᵖ) (z : M₁.val.obj W) :
    (a ≫ b).val.app W z = b.val.app W (a.val.app W z) := rfl

/-- A composite of two morphisms of sheaves of types, on sections. -/
theorem Sheaf.comp₂_hom_app.{t} {C : Type*} [Category C] {J : GrothendieckTopology C}
    {F₁ F₂ F₃ : Sheaf J (Type t)} (a : F₁ ⟶ F₂) (b : F₂ ⟶ F₃) (W : Cᵒᵖ) (z : F₁.obj.obj W) :
    (a ≫ b).hom.app W z = b.hom.app W (a.hom.app W z) := rfl

/-- An equation `a ≫ b = c ≫ d` of morphisms of sheaves of modules, on sections. -/
theorem SheafOfModules.comp_val_app_eq {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat} {M₁ M₂ M₃ M₄ : SheafOfModules R} {a : M₁ ⟶ M₂} {b : M₂ ⟶ M₄}
    {c : M₁ ⟶ M₃} {d : M₃ ⟶ M₄} (h : a ≫ b = c ≫ d) (W : Cᵒᵖ) (z : M₁.val.obj W) :
    b.val.app W (a.val.app W z) = d.val.app W (c.val.app W z) := by
  rw [← comp₂_val_app, h, comp₂_val_app]

/-- Two morphisms out of a left adjoint into sheaves of types agree as soon as their transposes
agree on sections. -/
theorem Sheaf.eq_of_unit_hom_app.{t} {C₁ C₂ : Type*} [Category C₁] [Category C₂]
    {J₁ : GrothendieckTopology C₁} {J₂ : GrothendieckTopology C₂}
    {L : Sheaf J₁ (Type t) ⥤ Sheaf J₂ (Type t)} {Q : Sheaf J₂ (Type t) ⥤ Sheaf J₁ (Type t)}
    (adj : L ⊣ Q) {A : Sheaf J₁ (Type t)} {B : Sheaf J₂ (Type t)} (φ ψ : L.obj A ⟶ B)
    (h : ∀ (W : C₁ᵒᵖ) (s : A.obj.obj W), (Q.map φ).hom.app W ((adj.unit.app A).hom.app W s) =
      (Q.map ψ).hom.app W ((adj.unit.app A).hom.app W s)) : φ = ψ := by
  apply (adj.homEquiv A B).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply Sheaf.hom_ext
  ext W s
  exact h W s

section MateUnit

variable {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
  {J₁ : GrothendieckTopology C₁} {J₂ : GrothendieckTopology C₂} {J₃ : GrothendieckTopology C₃}
  {J₄ : GrothendieckTopology C₄} {R₁ : Sheaf J₁ RingCat} {R₂ : Sheaf J₂ RingCat}
  {R₃ : Sheaf J₃ RingCat} {R₄ : Sheaf J₄ RingCat}
  {G : SheafOfModules R₁ ⥤ SheafOfModules R₃} {H : SheafOfModules R₂ ⥤ SheafOfModules R₄}
  {L₁ : SheafOfModules R₁ ⥤ SheafOfModules R₂} {Q₁ : SheafOfModules R₂ ⥤ SheafOfModules R₁}
  {L₂ : SheafOfModules R₃ ⥤ SheafOfModules R₄} {Q₂ : SheafOfModules R₄ ⥤ SheafOfModules R₃}

/-- The unit square of a mate of sheaves of modules, on sections. -/
theorem SheafOfModules.mateEquiv_symm_unit_val_app (adj₁ : L₁ ⊣ Q₁) (adj₂ : L₂ ⊣ Q₂)
    (θ : Q₁ ⋙ G ⟶ H ⋙ Q₂) (K : SheafOfModules R₁) (W : C₃ᵒᵖ) (s : (G.obj K).val.obj W) :
    (Q₂.map (((mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _ θ)).app K)).val.app W
        ((adj₂.unit.app (G.obj K)).val.app W s) =
      (θ.app (L₁.obj K)).val.app W ((G.map (adj₁.unit.app K)).val.app W s) := by
  exact congrArg (fun m => m.val.app W s)
    (unit_mateEquiv_symm adj₁ adj₂ (TwoSquare.mk _ _ _ _ θ) K).symm

end MateUnit

section SetMateUnit

universe t

variable {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
  {J₁ : GrothendieckTopology C₁} {J₂ : GrothendieckTopology C₂} {J₃ : GrothendieckTopology C₃}
  {J₄ : GrothendieckTopology C₄}
  {G : Sheaf J₁ (Type t) ⥤ Sheaf J₃ (Type t)} {H : Sheaf J₂ (Type t) ⥤ Sheaf J₄ (Type t)}
  {L₁ : Sheaf J₁ (Type t) ⥤ Sheaf J₂ (Type t)} {Q₁ : Sheaf J₂ (Type t) ⥤ Sheaf J₁ (Type t)}
  {L₂ : Sheaf J₃ (Type t) ⥤ Sheaf J₄ (Type t)} {Q₂ : Sheaf J₄ (Type t) ⥤ Sheaf J₃ (Type t)}

/-- The unit square of a mate of sheaves of types, on sections. -/
theorem Sheaf.mateEquiv_symm_unit_hom_app (adj₁ : L₁ ⊣ Q₁) (adj₂ : L₂ ⊣ Q₂)
    (θ : Q₁ ⋙ G ⟶ H ⋙ Q₂) (K : Sheaf J₁ (Type t)) (W : C₃ᵒᵖ) (s : (G.obj K).obj.obj W) :
    (Q₂.map (((mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _ θ)).app K)).hom.app W
        ((adj₂.unit.app (G.obj K)).hom.app W s) =
      (θ.app (L₁.obj K)).hom.app W ((G.map (adj₁.unit.app K)).hom.app W s) := by
  exact congrArg (fun m => m.hom.app W s)
    (unit_mateEquiv_symm adj₁ adj₂ (TwoSquare.mk _ _ _ _ θ) K).symm

end SetMateUnit

end Stacks.CategoryTheory

end
