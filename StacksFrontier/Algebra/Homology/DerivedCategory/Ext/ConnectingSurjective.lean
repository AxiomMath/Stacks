module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.SetTheory.Cardinal.Finite
import StacksCore.Tactic.StacksAttribute

/-!
# Surjectivity of a connecting map of `Ext` from a cardinality bound

Let `0 → X₁ → X₂ → X₃ → 0` be a short exact sequence in an abelian category and `O` an object.
The covariant long exact sequence of `Ext(O, -)` reads, around degree `n + 1`,

`Ext^n(O, X₃) --δ--> Ext^{n+1}(O, X₁) → Ext^{n+1}(O, X₂) → Ext^{n+1}(O, X₃) → Ext^{n+2}(O, X₁)`,

with `δ x = x ∘ e` the Yoneda product with the class `e` of the extension. If
`Ext^{n+2}(O, X₁) = 0` the map `Ext^{n+1}(O, X₂) → Ext^{n+1}(O, X₃)` is onto; if moreover
`Ext^{n+1}(O, X₂)` is finite of cardinality at most that of `Ext^{n+1}(O, X₃)`, it is a
bijection, so `Ext^{n+1}(O, X₁) → Ext^{n+1}(O, X₂)` is zero and `δ` is onto.

This is the homological half of the nondegeneracy of the cup product on the first cohomology of
a curve: with `O = X₁ = X₃ = Λ` the constant sheaf, `δ` is the cup product with the class `e`,
and the cardinality bound on `H²` of the extension comes from a finite étale cover.

## Main results

* `CategoryTheory.Abelian.Ext.surjective_comp_extClass_of_natCard_le`: `δ` is onto.
* `CategoryTheory.Abelian.Ext.natCard_le_of_subsingleton`: for a short exact sequence with
  `Ext^{n+1}(O, X₁) = 0`, `#Ext^n(O, X₃) ≤ #Ext^n(O, X₂)`.
* `CategoryTheory.Abelian.Ext.surjective_extClass_comp_of_natCard_le`,
  `CategoryTheory.Abelian.Ext.natCard_le_of_subsingleton_contravariant`: the same two statements
  for the contravariant long exact sequence of `Ext(-, Y)`, with connecting map `x ↦ e ∘ x`.
* `CategoryTheory.Abelian.Ext.contravariant_hom_ext_one_exact`,
  `CategoryTheory.Abelian.Ext.covariant_hom_ext_one_exact`: the two six-term exact sequences
  `0 → Hom(X₃, N) → Hom(X₂, N) → Hom(X₁, N) → Ext¹(X₃, N) → Ext¹(X₂, N) → Ext¹(X₁, N)` and
  `0 → Hom(N, X₁) → Hom(N, X₂) → Hom(N, X₃) → Ext¹(N, X₁) → Ext¹(N, X₂) → Ext¹(N, X₃)`
  (Stacks 05E2). Stacks defines `Ext(A, B)` as the group of Yoneda extensions; here it is
  Mathlib's `Ext`, and `Hom(A, B)` is `Ext A B 0`, identified with `A ⟶ B` by `Ext.addEquiv₀`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Abelian.Ext

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {S : ShortComplex C} (hS : S.ShortExact) (O : C)

include hS in
/-- **The map `Ext^n(O, X₂) → Ext^n(O, X₃)` is onto when `Ext^{n+1}(O, X₁) = 0`.** -/
theorem surjective_comp_mk₀_g_of_subsingleton (n : ℕ)
    (h : Subsingleton (Ext O S.X₁ (n + 1))) :
    Function.Surjective (fun x : Ext O S.X₂ n => x.comp (mk₀ S.g) (add_zero n)) := fun x₃ =>
  covariant_sequence_exact₃ O hS x₃ rfl (Subsingleton.elim _ _)

include hS in
/-- **`#Ext^n(O, X₃) ≤ #Ext^n(O, X₂)` when `Ext^{n+1}(O, X₁) = 0`** and `Ext^n(O, X₂)` is
finite. -/
theorem natCard_le_of_subsingleton (n : ℕ) (h : Subsingleton (Ext O S.X₁ (n + 1)))
    [Finite (Ext O S.X₂ n)] : Nat.card (Ext O S.X₃ n) ≤ Nat.card (Ext O S.X₂ n) :=
  Nat.card_le_card_of_surjective _ (surjective_comp_mk₀_g_of_subsingleton hS O n h)

/-- **The connecting map `x ↦ x ∘ e : Ext^n(O, X₃) → Ext^{n+1}(O, X₁)` is onto** when
`Ext^{n+2}(O, X₁) = 0` and `Ext^{n+1}(O, X₂)` is finite of cardinality at most that of
`Ext^{n+1}(O, X₃)`. -/
theorem surjective_comp_extClass_of_natCard_le (n : ℕ)
    (h : Subsingleton (Ext O S.X₁ (n + 2))) [Finite (Ext O S.X₂ (n + 1))]
    (hcard : Nat.card (Ext O S.X₂ (n + 1)) ≤ Nat.card (Ext O S.X₃ (n + 1))) :
    Function.Surjective (fun x : Ext O S.X₃ n => x.comp hS.extClass rfl) := by
  have hsurj := surjective_comp_mk₀_g_of_subsingleton hS O (n + 1) h
  have hinj := (hsurj.bijective_of_nat_card_le hcard).1
  intro y
  have hy : y.comp (mk₀ S.f) (add_zero _) = 0 := by
    apply hinj
    change (y.comp (mk₀ S.f) (add_zero _)).comp (mk₀ S.g) (add_zero _) =
      (0 : Ext O S.X₂ (n + 1)).comp (mk₀ S.g) (add_zero _)
    rw [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, S.zero, mk₀_zero, comp_zero, zero_comp]
  exact covariant_sequence_exact₁ O hS y hy rfl

include hS in
/-- **The map `Ext^n(X₂, Y) → Ext^n(X₁, Y)` is onto when `Ext^{n+1}(X₃, Y) = 0`.** -/
theorem surjective_mk₀_f_comp_of_subsingleton (Y : C) (n : ℕ)
    (h : Subsingleton (Ext S.X₃ Y (n + 1))) :
    Function.Surjective (fun x : Ext S.X₂ Y n => (mk₀ S.f).comp x (zero_add n)) := fun x₁ =>
  contravariant_sequence_exact₁ hS Y x₁ (add_comm 1 n) (Subsingleton.elim _ _)

include hS in
/-- **`#Ext^n(X₁, Y) ≤ #Ext^n(X₂, Y)` when `Ext^{n+1}(X₃, Y) = 0`** and `Ext^n(X₂, Y)` is
finite. -/
theorem natCard_le_of_subsingleton_contravariant (Y : C) (n : ℕ)
    (h : Subsingleton (Ext S.X₃ Y (n + 1))) [Finite (Ext S.X₂ Y n)] :
    Nat.card (Ext S.X₁ Y n) ≤ Nat.card (Ext S.X₂ Y n) :=
  Nat.card_le_card_of_surjective _ (surjective_mk₀_f_comp_of_subsingleton hS Y n h)

/-- **The contravariant connecting map `x ↦ e ∘ x : Ext^n(X₁, Y) → Ext^{n+1}(X₃, Y)` is onto**
when `Ext^{n+2}(X₃, Y) = 0` and `Ext^{n+1}(X₂, Y)` is finite of cardinality at most that of
`Ext^{n+1}(X₁, Y)`. -/
theorem surjective_extClass_comp_of_natCard_le (Y : C) (n : ℕ)
    (h : Subsingleton (Ext S.X₃ Y (n + 2))) [Finite (Ext S.X₂ Y (n + 1))]
    (hcard : Nat.card (Ext S.X₂ Y (n + 1)) ≤ Nat.card (Ext S.X₁ Y (n + 1))) :
    Function.Surjective (fun x : Ext S.X₁ Y n => hS.extClass.comp x (add_comm 1 n)) := by
  have hsurj := surjective_mk₀_f_comp_of_subsingleton hS Y (n + 1) h
  have hinj := (hsurj.bijective_of_nat_card_le hcard).1
  intro y
  have hy : (mk₀ S.g).comp y (zero_add _) = 0 := by
    apply hinj
    change (mk₀ S.f).comp ((mk₀ S.g).comp y (zero_add _)) (zero_add _) =
      (mk₀ S.f).comp (0 : Ext S.X₂ Y (n + 1)) (zero_add _)
    rw [← comp_assoc_of_second_deg_zero, mk₀_comp_mk₀, S.zero, mk₀_zero, zero_comp, comp_zero]
  exact contravariant_sequence_exact₃ hS Y y hy (add_comm 1 n)

/-- **Stacks 05E2 (1).** For a short exact sequence `0 → X₁ → X₂ → X₃ → 0` and an object `N`,
the sequence
`0 → Hom(X₃, N) → Hom(X₂, N) → Hom(X₁, N) → Ext¹(X₃, N) → Ext¹(X₂, N) → Ext¹(X₁, N)`
is exact: the six-term sequence `Ext⁰(X₃, N) → ⋯ → Ext¹(X₁, N)` is exact and its first map,
precomposition with `X₂ → X₃`, is injective. -/
@[stacks 05E2 "(1), with Mathlib's derived-category `Ext` in place of Yoneda extensions and
`Hom(A, N)` as `Ext A N 0` (see `Ext.addEquiv₀`)"]
theorem contravariant_hom_ext_one_exact (N : C) :
    (contravariantSequence hS N 0 1 (add_zero 1)).Exact ∧
      Function.Injective ((mk₀ S.g).precomp N (zero_add 0)) := by
  have := hS.epi_g
  exact ⟨contravariantSequence_exact hS N 0 1 (add_zero 1), precomp_mk₀_injective_of_epi N S.g⟩

/-- **Stacks 05E2 (2).** For a short exact sequence `0 → X₁ → X₂ → X₃ → 0` and an object `N`,
the sequence
`0 → Hom(N, X₁) → Hom(N, X₂) → Hom(N, X₃) → Ext¹(N, X₁) → Ext¹(N, X₂) → Ext¹(N, X₃)`
is exact: the six-term sequence `Ext⁰(N, X₁) → ⋯ → Ext¹(N, X₃)` is exact and its first map,
postcomposition with `X₁ → X₂`, is injective. -/
@[stacks 05E2 "(2), with Mathlib's derived-category `Ext` in place of Yoneda extensions and
`Hom(N, A)` as `Ext N A 0` (see `Ext.addEquiv₀`)"]
theorem covariant_hom_ext_one_exact (N : C) :
    (covariantSequence N hS 0 1 (zero_add 1)).Exact ∧
      Function.Injective ((mk₀ S.f).postcomp N (add_zero 0)) := by
  have := hS.mono_f
  exact ⟨covariantSequence_exact N hS 0 1 (zero_add 1), postcomp_mk₀_injective_of_mono N S.f⟩

end CategoryTheory.Abelian.Ext

end
