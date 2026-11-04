module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import StacksCore.Tactic.StacksAttribute

/-! ## Diagram Lemmas -/

add_to_stacks 05QA "part 1" CategoryTheory.Abelian.epi_of_epi_of_epi_of_mono
add_to_stacks 05QA "part 2" CategoryTheory.Abelian.mono_of_epi_of_mono_of_mono
add_to_stacks 05QB CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono

@[expose] public section

namespace CategoryTheory.ShortComplex

open Limits

variable {C : Type*} [Category* C] [Abelian C]

/-- If `T` is exact with `T.g` an epimorphism, then `T.f, T.g ≫ u` is exact iff `u` is a
monomorphism. -/
lemma exact_mk_f_g_comp_iff_mono (T : ShortComplex C) (hT : T.Exact) [Epi T.g] {Z : C}
    (u : T.X₃ ⟶ Z) :
    (ShortComplex.mk T.f (T.g ≫ u) (by rw [← Category.assoc, T.zero, zero_comp])).Exact ↔
      Mono u := by
  let φ : T ⟶ ShortComplex.mk T.f (T.g ≫ u) (by simp) :=
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := u }
  constructor
  · intro h
    exact mono_of_epi_of_epi_of_mono φ h inferInstance inferInstance inferInstance
  · intro _
    exact (exact_iff_of_epi_of_isIso_of_mono φ).1 hT

/-- If `T` is exact with `T.f` a monomorphism, then `u ≫ T.f, T.g` is exact iff `u` is an
epimorphism. -/
lemma exact_mk_comp_f_g_iff_epi (T : ShortComplex C) (hT : T.Exact) [Mono T.f] {Z : C}
    (u : Z ⟶ T.X₁) :
    (ShortComplex.mk (u ≫ T.f) T.g (by rw [Category.assoc, T.zero, comp_zero])).Exact ↔
      Epi u := by
  let φ : ShortComplex.mk (u ≫ T.f) T.g (by simp) ⟶ T :=
    { τ₁ := u, τ₂ := 𝟙 _, τ₃ := 𝟙 _ }
  constructor
  · intro h
    exact epi_of_mono_of_epi_of_mono φ h inferInstance inferInstance inferInstance
  · intro _
    exact (exact_iff_of_epi_of_isIso_of_mono φ).2 hT

/-- Exactness test, with the second map given as a factorisation `c = b ≫ u`. -/
lemma exact_iff_mono_of_exact_of_epi {X₁ X₂ X₃ Z : C} {a : X₁ ⟶ X₂} {b : X₂ ⟶ X₃} {w : a ≫ b = 0}
    (h : (mk a b w).Exact) [Epi b] {c : X₂ ⟶ Z} (u : X₃ ⟶ Z) (hc : c = b ≫ u) (w' : a ≫ c = 0) :
    (mk a c w').Exact ↔ Mono u := by
  subst hc; exact exact_mk_f_g_comp_iff_mono (mk a b w) h u

/-- Exactness test, with the first map given as a factorisation `c = u ≫ a`. -/
lemma exact_iff_epi_of_exact_of_mono {Z X₁ X₂ X₃ : C} {a : X₁ ⟶ X₂} {b : X₂ ⟶ X₃} {w : a ≫ b = 0}
    (h : (mk a b w).Exact) [Mono a] {c : Z ⟶ X₂} (u : Z ⟶ X₁) (hc : c = u ≫ a) (w' : c ≫ b = 0) :
    (mk c b w').Exact ↔ Epi u := by
  subst hc; exact exact_mk_comp_f_g_iff_epi (mk a b w) h u

end CategoryTheory.ShortComplex
