module

public import Mathlib.CategoryTheory.Shift.ShiftedHom
import Mathlib.Tactic.Ring

/-!
# Iterated composites of a morphism `X ⟶ X⟦d⟧`

Let `C` be a category with a shift by `ℤ` and `f : X ⟶ X⟦d⟧` a morphism, with `d : ℕ`. Its
`t`-fold composite

`f⟦d(t - 1)⟧ ∘ ⋯ ∘ f⟦d⟧ ∘ f : X ⟶ X⟦dt⟧`

is `CategoryTheory.ShiftedHom.iterate f t`, defined by `iterate f 0 = 𝟙` and
`iterate f (t + 1) = f⟦dt⟧ ∘ iterate f t` (the composition `CategoryTheory.ShiftedHom.comp` of
shifted morphisms). Shifting it back by `-dt` gives the composite

`f⟦-d⟧ ∘ f⟦-2d⟧ ∘ ⋯ ∘ f⟦-dt⟧ : X⟦-dt⟧ ⟶ X`

of the translates of `f` by negative multiples of `d`, each followed by the identification
`X⟦d⟧⟦-dk⟧ = X⟦-d(k - 1)⟧`; this is `CategoryTheory.ShiftedHom.negIterate f t`, defined by
peeling off the factor `f⟦-dt⟧` applied first.

## Main definitions

* `CategoryTheory.ShiftedHom.iterate`: `f⟦d(t - 1)⟧ ∘ ⋯ ∘ f⟦d⟧ ∘ f : X ⟶ X⟦dt⟧`.
* `CategoryTheory.ShiftedHom.negIterate`: `f⟦-d⟧ ∘ ⋯ ∘ f⟦-dt⟧ : X⟦-dt⟧ ⟶ X`.

## Main results

* `CategoryTheory.ShiftedHom.iterate_succ'`: `iterate f (t + 1) = iterate f t⟦d⟧ ∘ f`.
* `CategoryTheory.ShiftedHom.negIterate_eq`: `negIterate f t` is the translate of
  `iterate f t` by `-dt`.
* `CategoryTheory.ShiftedHom.negIterate_comp`: `f ∘ negIterate f t` is the translate by `d` of
  `negIterate f (t + 1)`.
* `CategoryTheory.ShiftedHom.map_iterate`: a functor commuting with the shift sends `iterate f t`
  to `iterate (F f) t`.
-/

@[expose] public noncomputable section

namespace CategoryTheory.ShiftedHom

open Category

variable {C : Type*} [Category* C] [HasShift C ℤ] {D : Type*} [Category* D] [HasShift D ℤ]
  {X : C}

/-- **The `t`-fold composite `f⟦d(t - 1)⟧ ∘ ⋯ ∘ f⟦d⟧ ∘ f : X ⟶ X⟦dt⟧`** of a morphism
`f : X ⟶ X⟦d⟧`: the identity for `t = 0`, and `f⟦dt⟧ ∘ iterate f t` for `t + 1`. -/
def iterate (d : ℕ) (f : ShiftedHom X X (d : ℤ)) : (t : ℕ) → ShiftedHom X X ((d * t : ℕ) : ℤ)
  | 0 => mk₀ _ (by simp) (𝟙 X)
  | t + 1 => (iterate d f t).comp f (by push_cast; ring)

/-- The `0`-fold composite `iterate f 0` is the identity of `X`, in degree zero. -/
@[simp]
theorem iterate_zero (d : ℕ) (f : ShiftedHom X X (d : ℤ)) :
    iterate d f 0 = mk₀ _ (by simp) (𝟙 X) :=
  rfl

/-- `iterate f (t + 1) = f⟦dt⟧ ∘ iterate f t`. -/
theorem iterate_succ (d : ℕ) (f : ShiftedHom X X (d : ℤ)) (t : ℕ) :
    iterate d f (t + 1) = (iterate d f t).comp f (by push_cast; ring) :=
  rfl

/-- Composing with an identity in degree zero on either side, with arbitrary degree
bookkeeping. -/
theorem mk₀_id_comp_eq_comp_mk₀_id {a m₀ c : ℤ} (hm₀ : m₀ = 0) (f : ShiftedHom X X a)
    (h₁ : a + m₀ = c) (h₂ : m₀ + a = c) :
    (mk₀ m₀ hm₀ (𝟙 X)).comp f h₁ = f.comp (mk₀ m₀ hm₀ (𝟙 X)) h₂ := by
  subst hm₀
  obtain rfl : c = a := by rw [← h₁, add_zero]
  rw [mk₀_id_comp, comp_mk₀_id]

/-- **`iterate f (t + 1) = iterate f t⟦d⟧ ∘ f`**: the composite can also be built by composing
with `f` first. -/
theorem iterate_succ' (d : ℕ) (f : ShiftedHom X X (d : ℤ)) (t : ℕ) :
    iterate d f (t + 1) = f.comp (iterate d f t) (by push_cast; ring) := by
  induction t with
  | zero => exact mk₀_id_comp_eq_comp_mk₀_id _ f _ _
  | succ t ih =>
    rw [iterate_succ d f (t + 1)]
    conv_lhs => rw [ih]
    rw [comp_assoc (a₁₂ := ((d * (t + 1) : ℕ) : ℤ)) (a₂₃ := ((d * (t + 1) : ℕ) : ℤ))
      (a := ((d * (t + 1 + 1) : ℕ) : ℤ)) _ _ _ (by push_cast; ring)
      (by push_cast; ring) (by push_cast; ring)]
    rfl

/-- **`f⟦-d⟧ ∘ f⟦-2d⟧ ∘ ⋯ ∘ f⟦-dt⟧ : X⟦-dt⟧ ⟶ X`**, for `f : X ⟶ X⟦d⟧`, each factor followed by
the identification `X⟦d⟧⟦-dk⟧ = X⟦-d(k - 1)⟧`: the identification `X⟦0⟧ = X` for `t = 0`, and
`negIterate f t ∘ f⟦-d(t + 1)⟧` for `t + 1`. -/
def negIterate (d : ℕ) (f : ShiftedHom X X (d : ℤ)) : (t : ℕ) → ((X⟦-((d * t : ℕ) : ℤ)⟧) ⟶ X)
  | 0 => (shiftFunctorZero' C _ (by simp)).hom.app X
  | t + 1 => f⟦-((d * (t + 1) : ℕ) : ℤ)⟧' ≫
      (shiftFunctorAdd' C (d : ℤ) (-((d * (t + 1) : ℕ) : ℤ)) (-((d * t : ℕ) : ℤ))
        (by push_cast; ring)).inv.app X ≫ negIterate d f t

/-- `negIterate f 0` is the identification `X⟦0⟧ = X`. -/
theorem negIterate_zero (d : ℕ) (f : ShiftedHom X X (d : ℤ)) :
    negIterate d f 0 = (shiftFunctorZero' C _ (by simp)).hom.app X :=
  rfl

/-- `negIterate f (t + 1)` is `negIterate f t ∘ f⟦-d(t + 1)⟧`, through the identification
`X⟦d⟧⟦-d(t + 1)⟧ = X⟦-dt⟧`. -/
theorem negIterate_succ (d : ℕ) (f : ShiftedHom X X (d : ℤ)) (t : ℕ) :
    negIterate d f (t + 1) = f⟦-((d * (t + 1) : ℕ) : ℤ)⟧' ≫
      (shiftFunctorAdd' C (d : ℤ) (-((d * (t + 1) : ℕ) : ℤ)) (-((d * t : ℕ) : ℤ))
        (by push_cast; ring)).inv.app X ≫ negIterate d f t :=
  rfl

/-- The coherence behind `negIterate_eq`: the two identifications `X⟦a⟧⟦d⟧⟦-a'⟧ ≅ X`, for
`a + d = a'`. -/
theorem shiftFunctorAdd'_inv_app_comp_shiftFunctorCompIsoId (a d a' : ℤ) (h : a + d = a')
    (X : C) :
    (shiftFunctorAdd' C d (-a') (-a) (by rw [← h]; ring)).inv.app (X⟦a⟧) ≫
        (shiftFunctorCompIsoId C a (-a) (add_neg_cancel a)).hom.app X =
      ((shiftFunctorAdd' C a d a' h).inv.app X)⟦-a'⟧' ≫
        (shiftFunctorCompIsoId C a' (-a') (add_neg_cancel a')).hom.app X := by
  have e := shiftFunctorAdd'_assoc_inv_app (C := C) a d (-a') a' (-a) 0 h (by rw [← h]; ring)
    (by rw [h, add_neg_cancel]) X
  simp only [shiftFunctorCompIsoId, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [← reassoc_of% e]

/-- The translate by `b` of the identity in degree `a`, for `a = 0` and `b = 0`, followed by
the identification `X⟦a⟧⟦b⟧ = X`, is the identification `X⟦b⟧ = X`. -/
theorem mk₀_id_shift_comp_shiftFunctorCompIsoId (a b : ℤ) (ha : a = 0) (hb : b = 0)
    (h : a + b = 0) :
    (mk₀ a ha (𝟙 X))⟦b⟧' ≫ (shiftFunctorCompIsoId C a b h).hom.app X =
      (shiftFunctorZero' C b hb).hom.app X := by
  subst ha hb
  simp only [mk₀, id_comp, shiftFunctorCompIsoId, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, shiftFunctorZero', eqToIso_refl, Iso.refl_trans]
  rw [shiftFunctorAdd'_zero_add_inv_app, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp

/-- **`negIterate f t` is the translate of `iterate f t` by `-dt`**, followed by the
identification `X⟦dt⟧⟦-dt⟧ = X`. -/
theorem negIterate_eq (d : ℕ) (f : ShiftedHom X X (d : ℤ)) (t : ℕ) :
    negIterate d f t = (iterate d f t)⟦-((d * t : ℕ) : ℤ)⟧' ≫
      (shiftFunctorCompIsoId C _ _ (add_neg_cancel _)).hom.app X := by
  induction t with
  | zero => exact (mk₀_id_shift_comp_shiftFunctorCompIsoId _ _ (by simp) (by simp) _).symm
  | succ t ih =>
    rw [negIterate_succ, ih, iterate_succ' d f t]
    simp only [comp, Functor.map_comp, assoc]
    congr 1
    rw [← NatTrans.naturality_assoc, Functor.comp_map,
      shiftFunctorAdd'_inv_app_comp_shiftFunctorCompIsoId _ _ _ (by push_cast; ring)]

/-- The coherence behind `shift_shiftFunctorCompIsoId_comp`: the two identifications
`X⟦d⟧⟦a⟧⟦-a⟧ ≅ X⟦d⟧`, for `d + a = a'`. -/
theorem shiftFunctorCompIsoId_hom_app_shift (a d a' : ℤ) (h : d + a = a') (X : C) :
    (shiftFunctorCompIsoId C a (-a) (add_neg_cancel a)).hom.app (X⟦d⟧) =
      ((shiftFunctorAdd' C d a a' h).inv.app X)⟦-a⟧' ≫
        (shiftFunctorAdd' C (-a') d (-a) (by rw [← h]; ring)).hom.app (X⟦a'⟧) ≫
        ((shiftFunctorCompIsoId C a' (-a') (add_neg_cancel a')).hom.app X)⟦d⟧' := by
  have e₁ := shiftFunctorAdd'_assoc_inv_app (C := C) d a (-a) a' 0 d h (add_neg_cancel a)
    (by rw [h, ← h]; ring) X
  have e₂ := shiftFunctorAdd'_assoc_inv_app (C := C) a' (-a') d 0 (-a) d (add_neg_cancel a')
    (by rw [← h]; ring) (by rw [add_neg_cancel, zero_add]) X
  simp only [shiftFunctorCompIsoId, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp]
  rw [← shiftFunctorAdd'_add_zero_inv_app, ← shiftFunctorAdd'_zero_add_inv_app, e₂,
    Iso.hom_inv_id_app_assoc, e₁]

/-- **Composing a translate back to degree zero with a shifted morphism**: for
`g : Y ⟶ X⟦a⟧` and `f : X ⟶ Z⟦d⟧` with `d + a = a'`, the translate `g⟦-a⟧ : Y⟦-a⟧ ⟶ X`
followed by `f` is the translate by `d` of the translate `(f ∘ g)⟦-a'⟧ : Y⟦-a'⟧ ⟶ Z`, through
`Y⟦-a⟧ = Y⟦-a'⟧⟦d⟧`. -/
theorem shift_shiftFunctorCompIsoId_comp {Y Z : C} {a d a' : ℤ} (g : ShiftedHom Y X a)
    (f : ShiftedHom X Z d) (h : d + a = a') :
    (g⟦-a⟧' ≫ (shiftFunctorCompIsoId C a (-a) (add_neg_cancel a)).hom.app X) ≫ f =
      (shiftFunctorAdd' C (-a') d (-a) (by rw [← h]; ring)).hom.app Y ≫
        ((g.comp f h)⟦-a'⟧' ≫
          (shiftFunctorCompIsoId C a' (-a') (add_neg_cancel a')).hom.app Z)⟦d⟧' := by
  have n₁ := (shiftFunctorCompIsoId C a (-a) (add_neg_cancel a)).hom.naturality f
  have n₂ := (shiftFunctorAdd' C (-a') d (-a) (by rw [← h]; ring)).hom.naturality (g.comp f h)
  simp only [Functor.comp_map, Functor.id_map] at n₁ n₂
  rw [assoc, ← n₁, shiftFunctorCompIsoId_hom_app_shift a d a' h, Functor.map_comp,
    ← reassoc_of% n₂]
  simp only [comp, Functor.map_comp, assoc]

/-- **`f ∘ negIterate f t` is the translate by `d` of `negIterate f (t + 1)`**, through
`X⟦-dt⟧ = X⟦-d(t + 1)⟧⟦d⟧`. -/
theorem negIterate_comp (d : ℕ) (f : ShiftedHom X X (d : ℤ)) (t : ℕ) :
    negIterate d f t ≫ f =
      (shiftFunctorAdd' C (-((d * (t + 1) : ℕ) : ℤ)) (d : ℤ) (-((d * t : ℕ) : ℤ))
        (by push_cast; ring)).hom.app X ≫ (negIterate d f (t + 1))⟦(d : ℤ)⟧' := by
  rw [negIterate_eq, negIterate_eq, iterate_succ,
    shift_shiftFunctorCompIsoId_comp (a' := ((d * (t + 1) : ℕ) : ℤ)) _ _ (by push_cast; ring)]

/-- **A functor commuting with the shift sends `iterate f t` to `iterate (F f) t`.** -/
theorem map_iterate (F : C ⥤ D) [F.CommShift ℤ] (d : ℕ) (f : ShiftedHom X X (d : ℤ)) (t : ℕ) :
    (iterate d f t).map F = iterate d (f.map F) t := by
  induction t with
  | zero => simp
  | succ t ih => rw [iterate_succ, map_comp, ih, iterate_succ]

end CategoryTheory.ShiftedHom
