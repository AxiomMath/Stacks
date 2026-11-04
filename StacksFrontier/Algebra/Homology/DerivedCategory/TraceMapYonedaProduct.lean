module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RelativeTraceMap

/-!
# The trace map and the Yoneda product

Let `Φ : C ⥤ C'` be a functor commuting with the shifts and `t : Φ(B) ⟶ L[c₀]` a trace, with trace
map `T(y) = t[m] ∘ Φ(y)` on `Hom(A, B[m])` (`Stacks.RelativeDuality.traceMap`). For a shifted
morphism `w : A ⟶ A'[n]` and `y : A' ⟶ B[m]`, the trace map of the Yoneda product `y[n] ∘ w` is
`T(y)[n] ∘ Φ(w)` (`Stacks.RelativeDuality.traceMap_shiftedHom_comp`). In degree `0` this is the
naturality of the trace map in `A` (`Stacks.RelativeDuality.traceMap_mk₀_comp`), in degree `1` its
compatibility with connecting morphisms (`Stacks.RelativeDuality.traceMap_comp_shift`).

For the direct image `Φ = Rf̄_*` of a proper family of curves `f̄ : X̄ → S`, `A = B = Λ_X̄`,
`L = Λ_S`, `c₀ = -2` and a unit `η : Λ_S ⟶ Rf̄_* Λ_X̄`, it says that the trace map pairs a class
`y` with the class `ŵ = Φ(w) ∘ η` of `w` through the global cup product:
`T(y) ∘ ŵ = t ∘ Φ(y ∘ w) ∘ η`, i.e. `(y, w) ↦ tr(y ∪ w)` with the Yoneda product of `Ext_X̄(Λ, Λ)`.
This is the form in which Poincaré duality on a fibre (a perfect cup product pairing) enters
relative duality for a smooth projective curve, in the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.RelativeDuality.traceMap_shiftedHom_comp`.
* `Stacks.RelativeDuality.traceMap_shiftedHom_comp_comp`.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.RelativeDuality

section YonedaProduct

variable {C C' : Type*} [Category* C] [Category* C'] [Preadditive C] [Preadditive C']
  [HasShift C ℤ] [HasShift C' ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C' n).Additive]
  {Φ : C ⥤ C'} [Φ.CommShift ℤ] [Φ.Additive] {B : C} {L : C'} {c₀ : ℤ}
  {t : ShiftedHom (Φ.obj B) L c₀}

omit [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C' n).Additive] in
/-- **The trace map of a Yoneda product**: for `w : A ⟶ A'[n]` and `y : A' ⟶ B[m]`, the trace map
of `y[n] ∘ w` is `T(y)[n] ∘ Φ(w)`. -/
lemma traceMap_shiftedHom_comp {A A' : C} {n : ℤ} (w : ShiftedHom A A' n) {m m' c c' : ℤ}
    (hm : m + n = m') (h : c₀ + m = c) (h' : c₀ + m' = c') (hc : c + n = c')
    (y : ShiftedHom A' B m) :
    traceMap Φ t A m' c' h' (w.comp y hm) = (w.map Φ).comp (traceMap Φ t A' m c h y) hc := by
  simp only [traceMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ShiftedHom.map_comp]
  exact ShiftedHom.comp_assoc _ _ _ _ _ (by omega)

omit [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C' n).Additive] in
/-- **The trace pairing is the trace of the Yoneda product**: for `y : B ⟶ B[m]`, `w : A ⟶ B[n]`
and any `u : E ⟶ Φ(A)[d]`, the trace map of `y` composed with the class `Φ(w) ∘ u` is the trace
map of `y[n] ∘ w` composed with `u`. For `Φ = Rf̄_*` and `u` the unit `Λ_S ⟶ Rf̄_* Λ_X̄`, this is
`T(y) ∘ ŵ = tr(y ∪ w)`. -/
lemma traceMap_shiftedHom_comp_comp {A : C} {E : C'} {d n : ℤ} (u : ShiftedHom E (Φ.obj A) d)
    (w : ShiftedHom A B n) {m m' c c' e e' : ℤ} (hm : m + n = m') (h : c₀ + m = c)
    (h' : c₀ + m' = c') (hc : c + n = c') (he : n + d = e) (he' : c + e = e')
    (hc' : c' + d = e') (y : ShiftedHom B B m) :
    (u.comp (w.map Φ) he).comp (traceMap Φ t B m c h y) he' =
      u.comp (traceMap Φ t A m' c' h' (w.comp y hm)) hc' := by
  rw [traceMap_shiftedHom_comp w hm h h' hc y]
  exact ShiftedHom.comp_assoc _ _ _ _ _ (by omega)

end YonedaProduct

end Stacks.RelativeDuality

end
