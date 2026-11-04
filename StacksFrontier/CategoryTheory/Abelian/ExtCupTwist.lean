module

public import StacksFrontier.CategoryTheory.Abelian.ExtCupProduct

/-!
# Twisted equivariance of the cup product

Let `Φ` be an exact lax monoidal endofunctor of an abelian monoidal category `C`, and let
`σ_F : Φ F ⟶ F` be a morphism for each coefficient `F`. Then `Φ` acts on `Ext^i(𝟙, F)` by
`a ↦ σ_F ∘ Φ(a)`, read through `ε : 𝟙 ⟶ Φ 𝟙` (`Stacks.ExtCup.twistAction`).

If the morphisms `σ` are compatible with a pairing `μ : F ⊗ G ⟶ T`, in the sense that
`μ_Φ ≫ Φ μ ≫ σ_T = (σ_F ⊗ σ_G) ≫ μ`, then the action commutes with the cup product
`Stacks.ExtCup.cup μ` (`Stacks.ExtCup.twistAction_cup`).

## Main definitions

* `Stacks.ExtCup.twistAction`: `a ↦ σ ∘ Φ(a)` on `Ext^i(𝟙, F)`.

## Main results

* `Stacks.ExtCup.twistAction_cup`: the action commutes with the cup product.
-/

@[expose] public noncomputable section

universe w v u

namespace Stacks.ExtCup

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [HasExt.{w} C]
  [EnoughInjectives C] (Φ : C ⥤ C) [Φ.LaxMonoidal] [Φ.Additive] [PreservesFiniteLimits Φ]
  [PreservesFiniteColimits Φ]

/-- **The action of an exact lax monoidal endofunctor on `Ext` out of the unit**, twisted by
`σ : Φ F ⟶ F`: the class `a` goes to `Φ(a)`, read out of the unit through `ε : 𝟙 ⟶ Φ 𝟙`,
followed by `σ`. -/
def twistAction {F : C} (σ : Φ.obj F ⟶ F) {i : ℕ} (a : Ext.{w} (𝟙_ C) F i) :
    Ext.{w} (𝟙_ C) F i :=
  (mapUnit Φ a).comp (Ext.mk₀ σ) (add_zero i)

omit [EnoughInjectives C] in
/-- The twisted action is additive. -/
theorem twistAction_add {F : C} (σ : Φ.obj F ⟶ F) {i : ℕ} (a a' : Ext.{w} (𝟙_ C) F i) :
    twistAction Φ σ (a + a') = twistAction Φ σ a + twistAction Φ σ a' := by
  simp [twistAction, mapUnit, Ext.mapExactFunctor_add]

/-- **The twisted action commutes with the cup product.** If `σ_F : Φ F ⟶ F`,
`σ_G : Φ G ⟶ G` and `σ_T : Φ T ⟶ T` are compatible with the pairing `μ : F ⊗ G ⟶ T`, that is
`μ_Φ ≫ Φ μ ≫ σ_T = (σ_F ⊗ σ_G) ≫ μ`, then acting on `a ∪_μ b` is the cup product of the
actions on `a` and on `b`. -/
theorem twistAction_cup {F G T : C} [(tensorRight G).Additive]
    [PreservesFiniteLimits (tensorRight G)] [PreservesFiniteColimits (tensorRight G)]
    [(tensorRight (Φ.obj G)).Additive] [PreservesFiniteLimits (tensorRight (Φ.obj G))]
    [PreservesFiniteColimits (tensorRight (Φ.obj G))]
    (μ : F ⊗ G ⟶ T) (σF : Φ.obj F ⟶ F) (σG : Φ.obj G ⟶ G) (σT : Φ.obj T ⟶ T)
    (hσ : Functor.LaxMonoidal.μ Φ F G ≫ Φ.map μ ≫ σT = (σF ⊗ₘ σG) ≫ μ)
    {i j n : ℕ} (h : j + i = n) (a : Ext.{w} (𝟙_ C) F i) (b : Ext.{w} (𝟙_ C) G j) :
    twistAction Φ σT (cup μ a b h) = cup μ (twistAction Φ σF a) (twistAction Φ σG b) h := by
  unfold twistAction
  rw [mapUnit_cup, cup_comp_mk₀, cup_comp_mk₀_right, comp_mk₀_cup, Category.assoc, hσ,
    tensorHom_def, Category.assoc]

end Stacks.ExtCup

end
