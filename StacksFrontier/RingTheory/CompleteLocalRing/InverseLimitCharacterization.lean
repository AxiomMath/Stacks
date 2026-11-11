module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Complete local rings as inverse limits of their adic truncations

Let `(R, 𝔪)` be a local ring. The Stacks project calls `R` a *complete local ring* when the
canonical map
`R ⟶ lim_n R / 𝔪ⁿ`
to the `𝔪`-adic completion of `R` is an isomorphism, where the limit is taken over the tower of
truncation maps `R / 𝔪ⁿ → R / 𝔪ᵏ` for `k ≤ n`. A footnote stresses that this is *more* than
being able to lift compatible families: it also demands `⋂ₙ 𝔪ⁿ = (0)`, i.e. that `R` be
separated, which some texts spell out by saying that `R` is "complete and separated".

The definition itself is `IsCompleteLocalRing` in
`StacksFrontier.RingTheory.CompleteLocalRing.Defs`, phrased with Mathlib's `AdicCompletion`. The
later results of the Cohen structure theorem section state completeness as Mathlib's
`IsAdicComplete (IsLocalRing.maximalIdeal R) R`, the conjunction of `IsHausdorff` (the
footnote's separatedness) and `IsPrecomplete` (convergence of Cauchy sequences). This module
connects that condition with the source's map into an inverse limit in elementary terms.

## Main results

* `IsLocalRing.isAdicComplete_maximalIdeal_iff_forall_compatible_existsUnique_mk_eq`:
  for a local ring `R`, `IsAdicComplete (maximalIdeal R) R` holds if and only if every
  compatible family `f : (n : ℕ) → R ⧸ 𝔪ⁿ` — compatible meaning that
  `Ideal.Quotient.factor` carries `f n` to `f k` whenever `k ≤ n` — is induced by a *unique*
  element of `R`. Existence of such an element says the canonical map `R → lim_n R / 𝔪ⁿ` is
  surjective, uniqueness says it is injective. The uniqueness clause applied to the zero
  family is exactly `⋂ₙ 𝔪ⁿ = (0)`.

## Implementation notes

The inverse limit is not named as an object here: the `∃!` spells it by its universal property,
with the truncations `Ideal.Quotient.mk (𝔪ⁿ)` and transition maps `Ideal.Quotient.factor` the
source writes down. Going right, a compatible family is lifted to a Cauchy sequence of
representatives, `IsPrecomplete.prec` produces a limit, and `IsHausdorff.haus` makes it unique.
Going left, separatedness is the uniqueness clause for the zero family and precompleteness is
existence for the family of truncations of a Cauchy sequence. The one translation needed
throughout is `(J • ⊤ : Submodule R R) = J` for an ideal `J`, which turns `SModEq` modulo
`𝔪ⁿ • ⊤` into equality of residues modulo `𝔪ⁿ`.
-/

@[expose] public section

universe u

open IsLocalRing

/-- **A local ring is complete exactly when it is the inverse limit of its adic truncations.**

Let `(R, 𝔪)` be a local ring. Then `R` is `𝔪`-adically complete if and only if for every
family `f` of residues `f n : R ⧸ 𝔪ⁿ` that is compatible with the truncation maps
`R ⧸ 𝔪ⁿ → R ⧸ 𝔪ᵏ` for `k ≤ n`, there is a *unique* `r : R` whose residue modulo `𝔪ⁿ` is
`f n` for every `n`.

This is the Stacks project's definition of a complete local ring: a compatible family is an
element of `lim_n R / 𝔪ⁿ`, existence of `r` says the canonical map `R → lim_n R / 𝔪ⁿ` is
surjective, and uniqueness says it is injective, so the two together say that this ring map is
an isomorphism. Uniqueness for the zero family is the separatedness `⋂ₙ 𝔪ⁿ = (0)` that the
source's footnote insists on; it corresponds to the `IsHausdorff` half of `IsAdicComplete`,
while existence corresponds to the `IsPrecomplete` half. -/
theorem IsLocalRing.isAdicComplete_maximalIdeal_iff_forall_compatible_existsUnique_mk_eq
    (R : Type u) [CommRing R] [IsLocalRing R] :
    IsAdicComplete (maximalIdeal R) R ↔
      ∀ f : (n : ℕ) → R ⧸ maximalIdeal R ^ n,
        (∀ (k n : ℕ) (h : k ≤ n),
            Ideal.Quotient.factor (Ideal.pow_le_pow_right h) (f n) = f k) →
          ∃! r : R, ∀ n : ℕ, Ideal.Quotient.mk (maximalIdeal R ^ n) r = f n := by
  have key : ∀ (J : Ideal R) (x y : R),
      (x ≡ y [SMOD (J • ⊤ : Submodule R R)]) ↔
        Ideal.Quotient.mk J x = Ideal.Quotient.mk J y := by
    intro J x y
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.Quotient.eq]
  constructor
  · intro hc f hf
    choose x hx using fun n : ℕ =>
      Ideal.Quotient.mk_surjective (I := maximalIdeal R ^ n) (f n)
    obtain ⟨L, hL⟩ := IsPrecomplete.prec hc.toIsPrecomplete fun {k n} h => by
      rw [key, hx k, ← hf k n h, ← hx n, Ideal.Quotient.factor_mk]
    have hLmk : ∀ n : ℕ, Ideal.Quotient.mk (maximalIdeal R ^ n) L = f n := fun n => by
      rw [← hx n, ← (key _ _ _).mp (hL n)]
    refine ⟨L, hLmk, fun r hr => sub_eq_zero.mp <| hc.haus _ fun n => ?_⟩
    rw [key, map_sub, hr n, hLmk n, sub_self, map_zero]
  · intro H
    refine { toIsHausdorff := ⟨fun y hy => ?_⟩, toIsPrecomplete := ⟨fun g hg => ?_⟩ }
    · obtain ⟨r, -, huniq⟩ := H (fun _ => 0) (fun _ _ _ => by simp)
      exact (huniq y fun n => by simpa using (key _ _ _).mp (hy n)).trans
        (huniq 0 fun _ => by simp).symm
    · obtain ⟨L, hL, -⟩ := H (fun n => Ideal.Quotient.mk (maximalIdeal R ^ n) (g n))
        fun k n h => by
          rw [Ideal.Quotient.factor_mk]
          exact ((key _ _ _).mp (hg h)).symm
      exact ⟨L, fun n => (key _ _ _).mpr (hL n).symm⟩

end
