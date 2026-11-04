module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.HomologySequence
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak

/-!
# Weak Serre classes and the long exact sequence of a triangulated functor

Let `Φ : D⁺(𝒜) ⥤ D⁺(ℬ)` be a triangulated functor and `P` a weak Serre class of `ℬ`
(Tag 0754). For a short exact sequence `0 → G₁ → G₂ → G₃ → 0` in `𝒜`, if every `Hᵠ(Φ(G₁))` and
every `Hᵠ(Φ(G₃))` lies in `P`, then so does every `Hᵠ(Φ(G₂))`. This holds because `Hᵠ(Φ(G₂))` is
the middle term of the five-term exact piece
`Hᵠ⁻¹(Φ(G₃)) → Hᵠ(Φ(G₁)) → Hᵠ(Φ(G₂)) → Hᵠ(Φ(G₃)) → Hᵠ⁺¹(Φ(G₁))` of the long exact sequence
(Tag 02MO (2)).

By induction this gives the dévissage along a tower. Suppose a family `Xₙ` has short exact
sequences `0 → X₀ → Xₙ₊₁ → Xₙ → 0`, as the levels of a flat ℓ-adic sheaf do. If every
`Hᵠ(Φ(X₀))` lies in `P`, then every `Hᵠ(Φ(Xₙ))` does.

## Main results

* `Stacks.EtaleCohomology.prop_singleHomology_X₂_of_shortExact`: closure of `P` along a short
  exact sequence.
* `Stacks.EtaleCohomology.prop_singleHomology_of_shortExact_tower`: the dévissage along a tower.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace Stacks.EtaleCohomology

variable {A B : Type*} [Category* A] [Abelian A] [HasDerivedCategory A] [Category* B] [Abelian B]
  [HasDerivedCategory B]

variable (Φ : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B) [Φ.CommShift ℤ] [Φ.IsTriangulated]
  (P : ObjectProperty B) [P.IsWeakSerreClass]

/-- **A weak Serre class along a short exact sequence.** If every `Hᵠ(Φ(G₁))` and every
`Hᵠ(Φ(G₃))` lies in a weak Serre class, so does every `Hᵠ(Φ(G₂))`. -/
theorem prop_singleHomology_X₂_of_shortExact {S : ShortComplex A} (hS : S.ShortExact)
    (h₁ : ∀ q, P ((singleHomology Φ q).obj S.X₁)) (h₃ : ∀ q, P ((singleHomology Φ q).obj S.X₃))
    (q : ℤ) : P ((singleHomology Φ q).obj S.X₂) :=
  ObjectProperty.prop_mid_of_exact₄ P.prop_obj₂_of_exact
    (f₀ := singleHomologyδ Φ hS (q - 1) q (by omega)) (f₁ := (singleHomology Φ q).map S.f)
    (f₂ := (singleHomology Φ q).map S.g) (f₃ := singleHomologyδ Φ hS q (q + 1) rfl)
    (singleHomologyδ_comp_map Φ hS (q - 1) q (by omega))
    (by rw [← Functor.map_comp, S.zero, Functor.map_zero])
    (singleHomology_map_comp_δ Φ hS q (q + 1) rfl)
    (singleHomology_exact₁ Φ hS (q - 1) q (by omega)) (singleHomology_exact₂ Φ hS q)
    (singleHomology_exact₃ Φ hS q (q + 1) rfl) (h₃ (q - 1)) (h₁ q) (h₃ q) (h₁ (q + 1))

/-- **Dévissage along a tower.** Let `Xₙ` be a family of objects with short exact sequences
`0 → X₀ → Xₙ₊₁ → Xₙ → 0` (given up to isomorphism of their terms). If every `Hᵠ(Φ(X₀))` lies in
a weak Serre class, then so does every `Hᵠ(Φ(Xₙ))`. -/
theorem prop_singleHomology_of_shortExact_tower (X : ℕ → A) (S : ℕ → ShortComplex A)
    (hS : ∀ n, (S n).ShortExact) (e₁ : ∀ n, (S n).X₁ ≅ X 0) (e₂ : ∀ n, (S n).X₂ ≅ X (n + 1))
    (e₃ : ∀ n, (S n).X₃ ≅ X n) (h₀ : ∀ q, P ((singleHomology Φ q).obj (X 0))) :
    ∀ (n : ℕ) (q : ℤ), P ((singleHomology Φ q).obj (X n)) := by
  intro n
  induction n with
  | zero => exact h₀
  | succ n ih =>
    intro q
    refine P.prop_of_iso ((singleHomology Φ q).mapIso (e₂ n)) ?_
    exact prop_singleHomology_X₂_of_shortExact Φ P (hS n)
      (fun q => P.prop_of_iso ((singleHomology Φ q).mapIso (e₁ n)).symm (h₀ q))
      (fun q => P.prop_of_iso ((singleHomology Φ q).mapIso (e₃ n)).symm (ih q)) q

end Stacks.EtaleCohomology
