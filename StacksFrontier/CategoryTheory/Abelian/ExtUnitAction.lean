module

public import Mathlib.CategoryTheory.Monoidal.Category
public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The action of `Ext(𝟙, 𝟙)` on objects with exact tensor

Let `C` be an abelian monoidal category and `c ∈ Ext^n(𝟙, 𝟙)`. For an object `F` such that
tensoring with `F` on the right is exact, the image of `c` under the exact functor `- ⊗ F`,
conjugated by the left unitor, is a class

`c · F ∈ Ext^n(F, F)`   (`Stacks.ExtUnitAction.action`).

It is natural in `F` for every morphism between such objects
(`Stacks.ExtUnitAction.mk₀_comp_action`), with no compatibility to check: a morphism `φ : F ⟶ F'`
is a natural transformation `- ⊗ F ⟶ - ⊗ F'` of exact functors, and those intertwine the two
actions on `Ext` (`Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor`).

For sheaves of `Λ`-modules on a site, `Ext^n(𝟙, 𝟙) = Hⁿ(Λ)` and `c · F` is the cup product with
the cohomology class `c` on the flat sheaf `F`.

## Main definitions

* `Stacks.ExtUnitAction.action`: `c · F ∈ Ext^n(F, F)`.

## Main results

* `Stacks.ExtUnitAction.mk₀_comp_action`: naturality in `F`.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory

namespace Stacks.ExtUnitAction

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [HasExt.{w} C]

/-- **The action of a class `c ∈ Ext^n(𝟙, 𝟙)` on an object `F` with exact tensor**: the image of
`c` under the exact functor `- ⊗ F`, conjugated by the left unitor `𝟙 ⊗ F ≅ F`. -/
def action {n : ℕ} (c : Ext.{w} (𝟙_ C) (𝟙_ C) n) (F : C) [(tensorRight F).Additive]
    [PreservesFiniteLimits (tensorRight F)] [PreservesFiniteColimits (tensorRight F)] :
    Ext.{w} F F n :=
  (Ext.mk₀ (λ_ F).inv).comp ((c.mapExactFunctor (tensorRight F)).comp (Ext.mk₀ (λ_ F).hom)
    (add_zero n)) (zero_add n)

/-- **The action is natural in the object**: for `φ : F ⟶ F'` between objects with exact tensor,
`φ ∘ (c · F) = (c · F') ∘ φ`. -/
theorem mk₀_comp_action [EnoughInjectives C] {n : ℕ} (c : Ext.{w} (𝟙_ C) (𝟙_ C) n) {F F' : C}
    [(tensorRight F).Additive] [PreservesFiniteLimits (tensorRight F)]
    [PreservesFiniteColimits (tensorRight F)] [(tensorRight F').Additive]
    [PreservesFiniteLimits (tensorRight F')] [PreservesFiniteColimits (tensorRight F')]
    (φ : F ⟶ F') :
    (Ext.mk₀ φ).comp (action c F') (zero_add n) = (action c F).comp (Ext.mk₀ φ) (add_zero n) := by
  have key := Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor ((tensoringRight C).map φ) (𝟙_ C) n c
  have h₁ : φ ≫ (λ_ F').inv = (λ_ F).inv ≫ ((tensoringRight C).map φ).app (𝟙_ C) := by
    simp
  have h₂ : ((tensoringRight C).map φ).app (𝟙_ C) ≫ (λ_ F').hom = (λ_ F).hom ≫ φ := by
    simp
  have key' : (Ext.mk₀ (((tensoringRight C).map φ).app (𝟙_ C))).comp
      (c.mapExactFunctor (tensorRight F')) (zero_add n) =
      (c.mapExactFunctor (tensorRight F)).comp (Ext.mk₀ (((tensoringRight C).map φ).app (𝟙_ C)))
        (add_zero n) := key
  have step : (Ext.mk₀ (((tensoringRight C).map φ).app (𝟙_ C))).comp
      ((c.mapExactFunctor (tensorRight F')).comp (Ext.mk₀ (λ_ F').hom) (add_zero n)) (zero_add n) =
      ((c.mapExactFunctor (tensorRight F)).comp (Ext.mk₀ (λ_ F).hom) (add_zero n)).comp
        (Ext.mk₀ φ) (add_zero n) := by
    rw [← Ext.comp_assoc_of_third_deg_zero, key', Ext.comp_assoc_of_third_deg_zero,
      Ext.mk₀_comp_mk₀, h₂, ← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero]
  unfold action
  rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, h₁, ← Ext.mk₀_comp_mk₀,
    Ext.comp_assoc_of_second_deg_zero, step]
  exact (Ext.comp_assoc_of_third_deg_zero _ _ _ _).symm


/-- Conjugating an `Ext` class by degree-zero morphisms on both sides. -/
@[sga "4½ Etat_0 4.3" "special case"]
def sandwich {X X' Y Y' : C} {n : ℕ} (f : X' ⟶ X) (e : Ext.{w} X Y n) (g : Y ⟶ Y') :
    Ext.{w} X' Y' n :=
  (Ext.mk₀ f).comp (e.comp (Ext.mk₀ g) (add_zero n)) (zero_add n)

omit [MonoidalCategory C] in
/-- Conjugating `e` by `f` and `g`, then by `f₁` and `g₁`, is conjugating `e` by `f₁ ≫ f` and
`g ≫ g₁`. -/
theorem sandwich_sandwich {X X' X'' Y Y' Y'' : C} {n : ℕ} (f₁ : X'' ⟶ X') (f : X' ⟶ X)
    (e : Ext.{w} X Y n) (g : Y ⟶ Y') (g₁ : Y' ⟶ Y'') :
    sandwich f₁ (sandwich f e g) g₁ = sandwich (f₁ ≫ f) e (g ≫ g₁) := by
  simp only [sandwich, ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
    Ext.comp_assoc_of_third_deg_zero]

omit [MonoidalCategory C] in
/-- Conjugating by identities is the identity. -/
theorem sandwich_id {X Y : C} {n : ℕ} (e : Ext.{w} X Y n) : sandwich (𝟙 X) e (𝟙 Y) = e := by
  simp [sandwich]

/-- The action `c · F` is the conjugate of the image of `c` under `- ⊗ F` by the left unitor. -/
theorem action_eq_sandwich {n : ℕ} (c : Ext.{w} (𝟙_ C) (𝟙_ C) n) (F : C)
    [(tensorRight F).Additive] [PreservesFiniteLimits (tensorRight F)]
    [PreservesFiniteColimits (tensorRight F)] :
    action c F = sandwich (λ_ F).inv (c.mapExactFunctor (tensorRight F)) (λ_ F).hom :=
  rfl

omit [MonoidalCategory C] in
/-- From `f ∘ X = Y ∘ g` with `f` invertible, `X = f⁻¹ ∘ Y ∘ g`. -/
theorem eq_sandwich_of_mk₀_comp {X X' Y Y' : C} {n : ℕ} (f : X ≅ X') (g : Y ⟶ Y')
    (x : Ext.{w} X' Y' n) (y : Ext.{w} X Y n)
    (h : (Ext.mk₀ f.hom).comp x (zero_add n) = y.comp (Ext.mk₀ g) (add_zero n)) :
    x = sandwich f.inv y g := by
  rw [sandwich, ← h, ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, Iso.inv_hom_id]
  simp

omit [MonoidalCategory C] in
/-- The image under an exact functor `L` of the conjugate of `e` by `f` and `g` is the conjugate
of `L(e)` by `L f` and `L g`. -/
theorem mapExactFunctor_sandwich {D : Type*} [Category* D] [Abelian D] [HasExt.{w} D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {X X' Y Y' : C} {n : ℕ} (f : X' ⟶ X) (e : Ext.{w} X Y n) (g : Y ⟶ Y') :
    (sandwich f e g).mapExactFunctor L = sandwich (L.map f) (e.mapExactFunctor L) (L.map g) := by
  simp only [sandwich, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]

section Functor

variable {D : Type*} [Category* D] [Abelian D] [MonoidalCategory D] [HasExt.{w} D]
  [EnoughInjectives C] (Φ : C ⥤ D) [Φ.Monoidal] [Φ.Additive] [PreservesFiniteLimits Φ]
  [PreservesFiniteColimits Φ]

/-- **The image of a class `c ∈ Ext^n(𝟙, 𝟙)` under an exact monoidal functor**, read in
`Ext^n(𝟙, 𝟙)` of the target through `ε : 𝟙 ≅ Φ 𝟙`. -/
def mapClass {n : ℕ} (c : Ext.{w} (𝟙_ C) (𝟙_ C) n) : Ext.{w} (𝟙_ D) (𝟙_ D) n :=
  sandwich (Functor.LaxMonoidal.ε Φ) (c.mapExactFunctor Φ) (Functor.OplaxMonoidal.η Φ)

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- **Exact monoidal functors carry the action to the action**: `Φ(c · F) = Φ(c) · Φ(F)`. -/
theorem mapExactFunctor_action {n : ℕ} (c : Ext.{w} (𝟙_ C) (𝟙_ C) n) (F : C)
    [(tensorRight F).Additive] [PreservesFiniteLimits (tensorRight F)]
    [PreservesFiniteColimits (tensorRight F)] [(tensorRight (Φ.obj F)).Additive]
    [PreservesFiniteLimits (tensorRight (Φ.obj F))]
    [PreservesFiniteColimits (tensorRight (Φ.obj F))] :
    (action c F).mapExactFunctor Φ = action (mapClass Φ c) (Φ.obj F) := by
  let μF : Φ ⋙ tensorRight (Φ.obj F) ≅ tensorRight F ⋙ Φ :=
    NatIso.ofComponents (fun X => Functor.Monoidal.μIso Φ X F)
      (fun f => Functor.LaxMonoidal.μ_natural_left Φ f F)
  have key := Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor μF.hom (𝟙_ C) n c
  rw [← Stacks.ExtFunctorial.mapExactFunctor_comp_functor,
    ← Stacks.ExtFunctorial.mapExactFunctor_comp_functor] at key
  have h1 := eq_sandwich_of_mk₀_comp (μF.app (𝟙_ C)) _ _ _ key
  have hc : c.mapExactFunctor Φ = sandwich (Functor.OplaxMonoidal.η Φ) (mapClass Φ c)
      (Functor.LaxMonoidal.ε Φ) := by
    rw [mapClass, sandwich_sandwich, Functor.Monoidal.η_ε, sandwich_id]
  have hlu : Functor.LaxMonoidal.ε Φ ▷ Φ.obj F ≫ (μF.app (𝟙_ C)).hom ≫ Φ.map (λ_ F).hom =
      (λ_ (Φ.obj F)).hom :=
    (Functor.LaxMonoidal.left_unitality Φ F).symm
  have hlu' : Φ.map (λ_ F).inv ≫ (μF.app (𝟙_ C)).inv ≫ Functor.OplaxMonoidal.η Φ ▷ Φ.obj F =
      (λ_ (Φ.obj F)).inv := by
    rw [← cancel_mono (λ_ (Φ.obj F)).hom, Iso.inv_hom_id, ← hlu]
    simp only [Category.assoc]
    rw [← comp_whiskerRight_assoc, Functor.Monoidal.η_ε, id_whiskerRight, Category.id_comp,
      Iso.inv_hom_id_assoc, ← Φ.map_comp, Iso.inv_hom_id, Φ.map_id]
  rw [action_eq_sandwich, mapExactFunctor_sandwich, h1, hc, mapExactFunctor_sandwich,
    sandwich_sandwich, sandwich_sandwich, action_eq_sandwich]
  congr 1
  rw [← hlu', Category.assoc]
  rfl

end Functor

end Stacks.ExtUnitAction
