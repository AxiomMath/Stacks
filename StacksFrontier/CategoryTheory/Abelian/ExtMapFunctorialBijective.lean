module

public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial

/-!
# Bijections of `Ext` groups from adjunctions and biproducts

Consequences of the functoriality of `CategoryTheory.Abelian.Ext.mapExactFunctor` in the exact
functor (`StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial`).

## Main results

* `Stacks.ExtFunctorial.extAdjunction_bijective` — for an adjunction `L ⊣ R` of exact functors,
  `x ↦ η_A ∘ R x` is a bijection `Ext^n(L A, B) → Ext^n(A, R B)`, with inverse `y ↦ L y ∘ ε_B`.
* `Stacks.ExtFunctorial.ext_biprod_bijective`, `Stacks.ExtFunctorial.ext_finiteBiprod_bijective`
  — restriction along the inclusions of a (finite) biproduct identifies `Ext^n(⨁ X_k, Y)` with
  `∏ Ext^n(X_k, Y)`.
-/

@[expose] public noncomputable section

universe w w' v v' u u'

namespace Stacks.ExtFunctorial

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]

attribute [local instance] Ext.subsingleton_of_injective comp_preservesFiniteLimits
  comp_preservesFiniteColimits

/-- **`Ext` and adjunctions.** For an adjunction `L ⊣ R` between abelian categories with both
functors exact, the map `Ext^n(L A, B) → Ext^n(A, R B)` sending `x` to the composite of the unit
`A ⟶ R L A` with `R x` is bijective; its inverse sends `y` to the composite of `L y` with the
counit `L R B ⟶ B`. -/
public lemma extAdjunction_bijective [HasExt.{w} C] [HasExt.{w'} D] [EnoughInjectives C]
    [EnoughInjectives D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.Additive] [PreservesFiniteLimits L]
    [PreservesFiniteColimits L] [R.Additive] [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] (A : C) (B : D) (n : ℕ) :
    Function.Bijective (fun x : Ext.{w'} (L.obj A) B n =>
      (Ext.mk₀ (adj.unit.app A)).comp (x.mapExactFunctor R) (zero_add n)) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun y => (y.mapExactFunctor L).comp (Ext.mk₀ (adj.counit.app B)) (add_zero n), ?_, ?_⟩
  · intro x
    have key := mk₀_comp_mapExactFunctor adj.counit (L.obj A) n x
    rw [mapExactFunctor_id (L.obj A) n x] at key
    simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
      mapExactFunctor_comp_functor R L (L.obj A) n x, Ext.comp_assoc_of_third_deg_zero]
    rw [← key, Ext.mk₀_comp_mk₀_assoc]
    simp
  · intro y
    have key := mk₀_comp_mapExactFunctor adj.unit A n y
    rw [mapExactFunctor_id A n y] at key
    simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
      mapExactFunctor_comp_functor L R A n y]
    rw [← Ext.comp_assoc _ _ _ (zero_add n) (add_zero n) (by omega), key,
      Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
    simp

/-- **`Ext` out of a biproduct.** If `X` is a biproduct of `X₁` and `X₂`, with inclusions `i₁, i₂`
and projections `p₁, p₂`, then restriction along the inclusions identifies `Ext^n(X, Y)` with
`Ext^n(X₁, Y) × Ext^n(X₂, Y)`. -/
public lemma ext_biprod_bijective [HasExt.{w} C] {X X₁ X₂ Y : C} (i₁ : X₁ ⟶ X) (i₂ : X₂ ⟶ X)
    (p₁ : X ⟶ X₁) (p₂ : X ⟶ X₂) (h₁ : i₁ ≫ p₁ = 𝟙 X₁) (h₂ : i₂ ≫ p₂ = 𝟙 X₂)
    (h₁₂ : i₁ ≫ p₂ = 0) (h₂₁ : i₂ ≫ p₁ = 0) (h : p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙 X) (n : ℕ) :
    Function.Bijective (fun x : Ext.{w} X Y n =>
      ((Ext.mk₀ i₁).comp x (zero_add n), (Ext.mk₀ i₂).comp x (zero_add n))) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun y => (Ext.mk₀ p₁).comp y.1 (zero_add n) + (Ext.mk₀ p₂).comp y.2 (zero_add n), ?_, ?_⟩
  · intro x
    simp only [Ext.mk₀_comp_mk₀_assoc, ← Ext.add_comp, ← Ext.mk₀_add, h, Ext.mk₀_id_comp]
  · rintro ⟨y₁, y₂⟩
    simp only [Ext.comp_add, Ext.mk₀_comp_mk₀_assoc, h₁, h₂, h₁₂, h₂₁, Ext.mk₀_id_comp,
      Ext.mk₀_zero, Ext.zero_comp, add_zero, zero_add]

/-- **`Ext` out of a finite biproduct.** If `X` is a finite biproduct of the `X k`, with inclusions
`i k` and projections `p k`, then restriction along the inclusions identifies `Ext^n(X, Y)` with
the product of the `Ext^n(X k, Y)`. -/
public lemma ext_finiteBiprod_bijective [HasExt.{w} C] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y : C} {Xs : ι → C} (i : ∀ k, Xs k ⟶ X) (p : ∀ k, X ⟶ Xs k)
    (hip : ∀ k l, i k ≫ p l = if h : k = l then eqToHom (congrArg Xs h) else 0)
    (h : ∑ k, p k ≫ i k = 𝟙 X) (n : ℕ) :
    Function.Bijective (fun x : Ext.{w} X Y n => fun k => (Ext.mk₀ (i k)).comp x (zero_add n)) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun y => ∑ k, (Ext.mk₀ (p k)).comp (y k) (zero_add n), ?_, ?_⟩
  · intro x
    simp only [Ext.mk₀_comp_mk₀_assoc, ← Ext.sum_comp, ← Ext.mk₀_sum, h, Ext.mk₀_id_comp]
  · intro y
    funext k
    simp only [Ext.comp_sum, Ext.mk₀_comp_mk₀_assoc, hip]
    rw [Finset.sum_eq_single k]
    · simp
    · intro l _ hlk
      rw [dite_eq_right (Ne.symm hlk), Ext.mk₀_zero, Ext.zero_comp]
    · simp

end Stacks.ExtFunctorial

end
