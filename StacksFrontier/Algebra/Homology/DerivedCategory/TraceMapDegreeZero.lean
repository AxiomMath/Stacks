module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RelativeTraceMap
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.HomologicalDualityDegreeZero

/-!
# The trace map through a functor which is exact in degree zero

Let `Φ : D⁺(𝒜) ⥤ D⁺(𝒜')` be a triangulated functor carrying every object `X[0]` to an object
living in degree `0` only, with `H⁰(Φ((-)[0])) ≅ G` for an exact functor `G : 𝒜 ⥤ 𝒜'` (for
instance the derived functor of an exact functor, or the derived direct image along a finite
morphism). For a further functor `R` and a trace `t : R(Φ(M'[0])) ⟶ L[c₀]`, the trace map
`y ↦ t[m] ∘ R(Φ(y))` on `Ext^m_𝒜(M, M')` is the trace map of `R` at `G(M)[0]` on `G(y)`, read
through the identifications `Φ(-[0]) ≅ G(-)[0]`
(`Stacks.RelativeDuality.traceMap_comp_extPlus_degreeZero`).

Also: changing the trace along a *shifted* morphism `ε : B' ⟶ B[d]`
(`Stacks.RelativeDuality.traceMap_comp_shiftedHom`), the form in which a Gysin (purity) class
enters the trace map.

These are formal steps of the reduction of relative duality along an étale boundary divisor of a
family of curves, in the proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.RelativeDuality.traceMap_comp_shiftedHom`.
* `Stacks.RelativeDuality.traceMap_comp_extPlus_degreeZero`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Stacks.RelativeDuality

section ShiftedChange

variable {C C' : Type*} [Category* C] [Category* C'] [Preadditive C] [Preadditive C']
  [HasShift C ℤ] [HasShift C' ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C' n).Additive]
  {Φ : C ⥤ C'} [Φ.CommShift ℤ] [Φ.Additive] {B : C} {L : C'} {c₀ : ℤ}

omit [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C' n).Additive] in
/-- **Changing the trace along a shifted morphism `ε : B' ⟶ B[d]`**: the trace map of `t` at
`ε[q] ∘ y` is the trace map of `t[d] ∘ Φ(ε)` at `y`. -/
lemma traceMap_comp_shiftedHom (t : ShiftedHom (Φ.obj B) L c₀) {B' : C} {d : ℤ}
    (ε : ShiftedHom B' B d) {c₀' : ℤ} (hc : c₀ + d = c₀') (A : C) {q m c : ℤ}
    (hm : d + q = m) (h : c₀ + m = c) (h' : c₀' + q = c) (y : ShiftedHom A B' q) :
    traceMap Φ t A m c h (y.comp ε hm) = traceMap Φ ((ε.map Φ).comp t hc) A q c h' y := by
  simp only [traceMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ShiftedHom.map_comp]
  exact ShiftedHom.comp_assoc _ _ _ _ _ (by omega)

end ShiftedChange

section DegreeZero

open Stacks.TopTruncationExt Stacks.HomologicalDuality

universe w w'

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A] [HasExt.{w} A]
  [EnoughInjectives A]
  {A' : Type*} [Category* A'] [Abelian A'] [HasDerivedCategory A'] [HasExt.{w'} A']
  (Φ : DerivedCategory.Plus A ⥤ DerivedCategory.Plus A') [Φ.CommShift ℤ] [Φ.IsTriangulated]
  (hΦ : ∀ X : A, ((Φ ⋙ DerivedCategory.Plus.ι).obj
    ((DerivedCategory.Plus.singleFunctor A 0).obj X)).IsLE 0)
  (hΦ' : ∀ X : A, ((Φ ⋙ DerivedCategory.Plus.ι).obj
    ((DerivedCategory.Plus.singleFunctor A 0).obj X)).IsGE 0)
  (G : A ⥤ A') [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (η : topHomology (Φ ⋙ DerivedCategory.Plus.ι) 0 ≅ G)
  {C' : Type*} [Category* C'] [Preadditive C'] [HasShift C' ℤ]
  [∀ n : ℤ, (shiftFunctor C' n).Additive]
  (R : DerivedCategory.Plus A' ⥤ C') [R.CommShift ℤ] [R.Additive]

omit [∀ n : ℤ, (shiftFunctor C' n).Additive] in
/-- **The trace map through `Φ` is that of `R` on `G`**: for `y ∈ Ext^m_𝒜(M, M')` and a trace
`t : R(Φ(M'[0])) ⟶ L[c₀]`, `t[m] ∘ R(Φ(y)) = t'[m] ∘ R(G(y)) ∘ R(κ_M)` with
`κ : Φ(-[0]) ≅ G(-)[0]` (`Stacks.HomologicalDuality.degreeZeroIso`) and `t' = t ∘ R(κ_{M'}⁻¹)`. -/
theorem traceMap_comp_extPlus_degreeZero {M M' : A} {L : C'} {c₀ : ℤ}
    (t : ShiftedHom ((Φ ⋙ R).obj ((DerivedCategory.Plus.singleFunctor A 0).obj M')) L c₀)
    (m : ℕ) {c : ℤ} (h : c₀ + (m : ℤ) = c) (y : Ext.{w} M M' m) :
    traceMap (Φ ⋙ R) t ((DerivedCategory.Plus.singleFunctor A 0).obj M) m c h (extPlus y) =
      (ShiftedHom.mk₀ (0 : ℤ) rfl (R.map (degreeZeroIso Φ hΦ hΦ' G η M).hom)).comp
        (traceMap R ((ShiftedHom.mk₀ (0 : ℤ) rfl
            (R.map (degreeZeroIso Φ hΦ hΦ' G η M').inv)).comp t (add_zero c₀))
          ((DerivedCategory.Plus.singleFunctor A' 0).obj (G.obj M)) m c h
          (extPlus (y.mapExactFunctor G : Ext.{w'} _ _ m)))
        (add_zero c) := by
  have k := extPlus_map_degreeZeroIso Φ hΦ hΦ' G η y
  have k' : (extPlus y).map Φ =
      (ShiftedHom.mk₀ (0 : ℤ) rfl (degreeZeroIso Φ hΦ hΦ' G η M).hom).comp
        ((extPlus (y.mapExactFunctor G : Ext.{w'} _ _ m)).comp
          (ShiftedHom.mk₀ (0 : ℤ) rfl (degreeZeroIso Φ hΦ hΦ' G η M').inv)
          (zero_add _)) (add_zero _) := by
    rw [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, ← Category.assoc, ← k, Category.assoc,
      ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
  rw [traceMap_apply, traceMap_apply, ShiftedHom.comp_map, k', ShiftedHom.map_comp,
    ShiftedHom.map_comp, ShiftedHom.map_mk₀, ShiftedHom.map_mk₀]
  simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
  simp only [ShiftedHom.comp, CategoryTheory.Functor.map_comp, Category.assoc]

end DegreeZero

end Stacks.RelativeDuality

end
