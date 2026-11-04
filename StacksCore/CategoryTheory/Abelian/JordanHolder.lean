module

public import StacksCore.CategoryTheory.Abelian.Subobject
public import StacksCore.CategoryTheory.Subobject.NoetherianObject

/-! ## Finite filtrations with simple subquotients

Stacks tag 0FCJ: an object `X` of an abelian category is Artinian and Noetherian if and
only if there is a finite filtration `0 = A₀ ⊆ A₁ ⊆ ⋯ ⊆ Aₙ = X` by subobjects whose
successive quotients `Aᵢ₊₁/Aᵢ` are simple.

The `⟸` direction is an induction along the filtration using 0FCH and 0FCI on
`0 ⟶ Aᵢ ⟶ Aᵢ₊₁ ⟶ Aᵢ₊₁/Aᵢ ⟶ 0`, with `isArtinianObject_of_simple` /
`isNoetherianObject_of_simple` as the base case.

The `⟹` direction produces the chain from `Subobject X` satisfying both chain conditions,
by the order-theoretic `exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le`, and then
converts each covering `Aᵢ ⋖ Aᵢ₊₁` into simplicity of the quotient.

## Relation to mathlib

Only the last step above depends on anything provisional: it uses
`Subobject.simple_cokernel_ofLE` from `StacksCore.CategoryTheory.Abelian.Subobject`, which is
a cut-down stand-in for `covBy_iff_cokernel_is_simple` of mathlib#41424. See the module
docstring there for what to delete once that pull request lands. Nothing in the present
file needs to change at that point beyond the name of that one lemma.

Stacks 0FCK, the Jordan–Hölder uniqueness statement, is not proved here. It additionally
needs `IsModularLattice (Subobject A)` from mathlib#41424 — now available, ported
(delete-on-bump) in `StacksCore.CategoryTheory.Abelian.Subobject` — together with the instance
`[IsModularLattice X] : JordanHolderLattice X` from mathlib#41445, which is already merged
upstream but is *not* in our pinned mathlib revision, so it requires a bump.
-/

@[expose] public section

variable {C : Type*} [Category* C] [CategoryTheory.Abelian C]

namespace CategoryTheory

open Limits

/-- The short exact sequence `0 ⟶ A ⟶ B ⟶ B/A ⟶ 0` for subobjects `A ≤ B`. -/
private lemma shortExact_cokernel_ofLE {X : C} {A B : Subobject X} (h : A ≤ B) :
    (ShortComplex.mk (Subobject.ofLE A B h) (cokernel.π (Subobject.ofLE A B h))
      (by simp)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance

/-- If `A ≤ B` are subobjects of `X` with `A` Artinian and simple quotient, then `B` is
Artinian. This is 0FCH applied to `0 ⟶ A ⟶ B ⟶ B/A ⟶ 0`. -/
lemma isArtinianObject_of_le {X : C} {A B : Subobject X} (h : A ≤ B) [IsArtinianObject (A : C)]
    [Simple (cokernel (Subobject.ofLE A B h))] : IsArtinianObject (B : C) := by
  have := isArtinianObject_of_simple (cokernel (Subobject.ofLE A B h))
  exact (shortExact_cokernel_ofLE h).isArtinianObject_X₂

/-- If `A ≤ B` are subobjects of `X` with `A` Noetherian and simple quotient, then `B` is
Noetherian. This is 0FCI applied to `0 ⟶ A ⟶ B ⟶ B/A ⟶ 0`. -/
lemma isNoetherianObject_of_le {X : C} {A B : Subobject X} (h : A ≤ B) [IsNoetherianObject (A : C)]
    [Simple (cokernel (Subobject.ofLE A B h))] : IsNoetherianObject (B : C) := by
  have := isNoetherianObject_of_simple (cokernel (Subobject.ofLE A B h))
  exact (shortExact_cokernel_ofLE h).isNoetherianObject_X₂

/-- Induction along a filtration `a 0 = ⊥, …, a n = ⊤`: a property holding for `⊥` and
passing from `a i` to `a (i + 1)` holds for `⊤`. -/
private lemma subobject_top_of_filtration {X : C} (P : Subobject X → Prop) (a : ℕ → Subobject X)
    (n : ℕ) (h0 : a 0 = ⊥) (hn : a n = ⊤) (hbot : P ⊥)
    (hstep : ∀ i, i < n → P (a i) → P (a (i + 1))) : P ⊤ := by
  have key : ∀ i, i ≤ n → P (a i) := fun i => by
    induction i with
    | zero => exact fun _ => h0 ▸ hbot
    | succ k ih => exact fun (hk : k < n) => hstep k hk (ih hk.le)
  exact hn ▸ key n le_rfl

/-- An object carrying a finite filtration with simple subquotients is Artinian. -/
lemma isArtinianObject_of_filtration {X : C} (a : ℕ → Subobject X) (n : ℕ)
    (h0 : a 0 = ⊥) (hn : a n = ⊤) (hle : ∀ i, i < n → a i ≤ a (i + 1))
    (hs : ∀ i (hi : i < n), Simple (cokernel (Subobject.ofLE _ _ (hle i hi)))) :
    IsArtinianObject X := by
  have := subobject_top_of_filtration (fun A => IsArtinianObject (A : C)) a n h0 hn
    (isArtinianObject_of_isZero (IsZero.of_iso (isZero_zero C) Subobject.botCoeIsoZero))
    fun i hi _ => by
      have := hs i hi
      exact isArtinianObject_of_le (hle i hi)
  exact isArtinianObject_of_mono (inv (⊤ : Subobject X).arrow)

/-- An object carrying a finite filtration with simple subquotients is Noetherian. -/
lemma isNoetherianObject_of_filtration {X : C} (a : ℕ → Subobject X) (n : ℕ)
    (h0 : a 0 = ⊥) (hn : a n = ⊤) (hle : ∀ i, i < n → a i ≤ a (i + 1))
    (hs : ∀ i (hi : i < n), Simple (cokernel (Subobject.ofLE _ _ (hle i hi)))) :
    IsNoetherianObject X := by
  have := subobject_top_of_filtration (fun A => IsNoetherianObject (A : C)) a n h0 hn
    (isNoetherianObject_of_isZero (IsZero.of_iso (isZero_zero C) Subobject.botCoeIsoZero))
    fun i hi _ => by
      have := hs i hi
      exact isNoetherianObject_of_le (hle i hi)
  exact isNoetherianObject_of_mono (inv (⊤ : Subobject X).arrow)

/-- An Artinian and Noetherian object carries a finite filtration with simple
subquotients. -/
lemma exists_filtration_of_isArtinianObject_of_isNoetherianObject (X : C)
    [IsArtinianObject X] [IsNoetherianObject X] :
    ∃ (a : ℕ → Subobject X) (n : ℕ) (hle : ∀ i, i < n → a i ≤ a (i + 1)),
      a 0 = ⊥ ∧ a n = ⊤ ∧
        ∀ i (hi : i < n), Simple (cokernel (Subobject.ofLE _ _ (hle i hi))) := by
  obtain ⟨a, h0, n, hn, hcov⟩ :=
    exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le (bot_le : (⊥ : Subobject X) ≤ ⊤)
  exact ⟨a, n, fun i hi => (hcov i hi).le, h0, hn,
    fun i hi => Subobject.simple_cokernel_ofLE _ (hcov i hi)⟩

/-- **Stacks 0FCJ**: an object of an abelian category is Artinian and Noetherian if and
only if it admits a finite filtration by subobjects with simple successive quotients. -/
@[stacks 0FCJ]
lemma isArtinianObject_and_isNoetherianObject_iff_exists_filtration (X : C) :
    (IsArtinianObject X ∧ IsNoetherianObject X) ↔
      ∃ (a : ℕ → Subobject X) (n : ℕ) (hle : ∀ i, i < n → a i ≤ a (i + 1)),
        a 0 = ⊥ ∧ a n = ⊤ ∧
          ∀ i (hi : i < n), Simple (cokernel (Subobject.ofLE _ _ (hle i hi))) := by
  refine ⟨fun ⟨_, _⟩ => exists_filtration_of_isArtinianObject_of_isNoetherianObject X,
    fun ⟨a, n, hle, h0, hn, hs⟩ => ⟨?_, ?_⟩⟩
  · exact isArtinianObject_of_filtration a n h0 hn hle hs
  · exact isNoetherianObject_of_filtration a n h0 hn hle hs

end CategoryTheory
