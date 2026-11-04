module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RelativeTraceMap

/-!
# Moving the degree of a trace map into its source

For a functor `Φ` commuting with shifts and a trace `t : Φ(B) ⟶ L[c₀]`, the trace map
`Stacks.RelativeDuality.traceMap` is `y ↦ t[m] ∘ Φ(y)` on `Hom(A, B[m])`. This file shows that
its bijectivity in degree `m` at `A` is its bijectivity in degree `m + n` at any `A'` with
`A' ≅ A[n]`, and that in degree `0` it is the bijectivity of `y ↦ t ∘ Φ(y)` on honest morphisms.
Together, bijectivity in every degree at `A` reduces to bijectivity in degree `0` at the shifts
of `A`.

## Main results

* `Stacks.RelativeDuality.bijective_traceMap_iff_of_isIso`.
* `Stacks.RelativeDuality.bijective_traceMap_zero_iff`.
-/

@[expose] public section

open CategoryTheory

attribute [-instance] CategoryTheory.catToReflQuiver

namespace Stacks.RelativeDuality

section

variable {C : Type*} [Category* C] [HasShift C ℤ]

/-- Composition on the left with an invertible shifted morphism is bijective. -/
lemma bijective_shiftedHom_comp_of_isIso {A₃ A₁ B : C} {n m m' : ℤ} (δ : A₃ ⟶ A₁⟦n⟧) [IsIso δ]
    (hm : m + n = m') :
    Function.Bijective
      (fun y : ShiftedHom A₁ B m => ShiftedHom.comp (δ : ShiftedHom A₃ A₁ n) y hm) := by
  have e : (fun y : ShiftedHom A₁ B m => ShiftedHom.comp (δ : ShiftedHom A₃ A₁ n) y hm) =
      (fun w => δ ≫ w ≫ (shiftFunctorAdd' C m n m' hm).inv.app B) ∘
        (fun y : A₁ ⟶ B⟦m⟧ => (shiftFunctor C n).map y) := by
    funext y
    rfl
  rw [e]
  refine Function.Bijective.comp ⟨fun w₁ w₂ h => ?_, fun w => ?_⟩
    ⟨(shiftFunctor C n).map_injective, (shiftFunctor C n).map_surjective⟩
  · exact (cancel_epi δ).1 (by simpa using h)
  · exact ⟨inv δ ≫ w ≫ (shiftFunctorAdd' C m n m' hm).hom.app B, by simp⟩

end

section

variable {C C' : Type*} [Category* C] [Category* C'] [Preadditive C] [Preadditive C']
  [HasShift C ℤ] [HasShift C' ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C' n).Additive]
  (Φ : C ⥤ C') [Φ.CommShift ℤ] [Φ.Additive] {B : C} {L : C'} {c₀ : ℤ}
  (t : ShiftedHom (Φ.obj B) L c₀)

omit [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C' n).Additive] in
/-- The trace map commutes with composition with any shifted morphism. -/
lemma traceMap_comp {A₁ A₃ : C} {n : ℤ} (δ : ShiftedHom A₃ A₁ n) {m m' c c' : ℤ}
    (hm : m + n = m') (h : c₀ + m = c) (h' : c₀ + m' = c') (hc : c + n = c')
    (y : ShiftedHom A₁ B m) :
    traceMap Φ t A₃ m' c' h' (δ.comp y hm) = (δ.map Φ).comp (traceMap Φ t A₁ m c h y) hc := by
  simp only [traceMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ShiftedHom.map_comp]
  exact ShiftedHom.comp_assoc _ _ _ _ _ (by omega)

omit [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C' n).Additive] in
/-- **Bijectivity of the trace map moves along an isomorphism `A₃ ≅ A₁[n]`**, from degree `m` at
`A₁` to degree `m + n` at `A₃`. -/
theorem bijective_traceMap_iff_of_isIso {A₁ A₃ : C} {n : ℤ} (δ : A₃ ⟶ A₁⟦n⟧) [IsIso δ]
    {m m' c c' : ℤ} (hm : m + n = m') (h : c₀ + m = c) (h' : c₀ + m' = c') (hc : c + n = c') :
    Function.Bijective (traceMap Φ t A₃ m' c' h') ↔
      Function.Bijective (traceMap Φ t A₁ m c h) := by
  have hδ : IsIso (ShiftedHom.map (δ : ShiftedHom A₃ A₁ n) Φ) := by
    unfold ShiftedHom.map
    infer_instance
  have e : ⇑(traceMap Φ t A₃ m' c' h') ∘
      (fun y : ShiftedHom A₁ B m => ShiftedHom.comp (δ : ShiftedHom A₃ A₁ n) y hm) =
      (fun z : ShiftedHom (Φ.obj A₁) L c =>
        ShiftedHom.comp (ShiftedHom.map (δ : ShiftedHom A₃ A₁ n) Φ) z hc) ∘
        traceMap Φ t A₁ m c h := by
    funext y
    exact traceMap_comp Φ t δ hm h h' hc y
  rw [← Function.Bijective.of_comp_iff _ (bijective_shiftedHom_comp_of_isIso δ hm), e]
  exact Function.Bijective.of_comp_iff' (bijective_shiftedHom_comp_of_isIso _ hc) _

omit [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C' n).Additive] in
/-- **In degree `0` the trace map is `y ↦ t ∘ Φ(y)`** on honest morphisms `A ⟶ B`. -/
theorem bijective_traceMap_zero_iff (A : C) (h : c₀ + 0 = c₀) :
    Function.Bijective (traceMap Φ t A 0 c₀ h) ↔
      Function.Bijective (fun y : A ⟶ B => (Φ.map y : Φ.obj A ⟶ Φ.obj B) ≫ t) := by
  have e : (fun y : A ⟶ B => (Φ.map y : Φ.obj A ⟶ Φ.obj B) ≫ t) =
      traceMap Φ t A 0 c₀ h ∘ ShiftedHom.homEquiv (0 : ℤ) rfl := by
    funext y
    simp only [Function.comp_apply, ShiftedHom.homEquiv_apply, traceMap, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk, ShiftedHom.map_mk₀]
    exact (ShiftedHom.mk₀_comp (0 : ℤ) rfl (Φ.map y) t).symm
  rw [e, Equiv.bijective_comp]

end

end Stacks.RelativeDuality
