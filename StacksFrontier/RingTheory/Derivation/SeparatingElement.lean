module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# An element with nonvanishing differential at finitely many primes, in characteristic `p`

Let `R` be a ring of characteristic `p`, `D : R → M` a derivation, and `S` a finite set of pairwise
incomparable points of `Spec R` (for instance the minimal primes of a noetherian ring). Suppose
that for every `P ∈ S` some `x_P ∈ R` has `D x_P ≠ 0` at `P`, i.e. `ℓ_P (D x_P) ≠ 0` for an
`R`-linear `ℓ_P : M → κ(P)`. Then a single `u ∈ R` has `D u ≠ 0` at every `P ∈ S`.

By prime avoidance there is `s_P ∈ ⋂_{Q ∈ S, Q ≠ P} Q` not in `P`, and `u = ∑_P s_P ^ p x_P` works:
`D (s ^ p) = p s ^ (p - 1) D s = 0`, so `D u = ∑_P s_P ^ p D x_P`, and at `P` every term but the
one of `P` vanishes, `s_Q` lying in `P` for `Q ≠ P`, while `s_P` is a unit of `κ(P)`.

For the differentials of a smooth curve over a field of characteristic `p` this gives a separating
element on every component at once, the input of a separating finite Noether normalization: the
divisor of the Gysin map of `R² g_!` in the reduction of the weight bound of Weil II
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) is cut out by such a normalization.

## Main results

* `Derivation.exists_forall_ne_zero_of_charP`.
* `KaehlerDifferential.exists_forall_minimalPrimes_ne_zero`: for the Kähler differentials, at the
  minimal primes of a noetherian ring.
-/

@[expose] public section

namespace Derivation

variable {K R M : Type*} [CommRing K] [CommRing R] [Algebra K R] [AddCommGroup M] [Module R M]
  [Module K M] [IsScalarTower K R M]

omit [IsScalarTower K R M] in
/-- In characteristic `p`, a derivation into any module kills `p`-th powers:
`D (s ^ p) = p s ^ (p - 1) D s = 0` (`Derivation.map_pow_charP_eq_zero` is the case `M = R`). -/
@[ega "0 21.1.5" "(i)"]
private theorem map_pow_charP (D : Derivation K R M) (p : ℕ) [CharP R p] (s : R) :
    D (s ^ p) = 0 := by
  rw [leibniz_pow, ← Nat.cast_smul_eq_nsmul R, CharP.cast_eq_zero, zero_smul]

omit [IsScalarTower K R M] in
/-- **An element with nonvanishing differential at finitely many incomparable primes**, in
characteristic `p`: if for every `P ∈ S` some `x` has `ℓ_P (D x) ≠ 0`, one `u` does for all `P`. -/
theorem exists_forall_ne_zero_of_charP (D : Derivation K R M) (p : ℕ) [CharP R p] [NeZero p]
    (S : Finset (PrimeSpectrum R))
    (hanti : ∀ P ∈ S, ∀ Q ∈ S, Q.asIdeal ≤ P.asIdeal → Q = P)
    (ℓ : ∀ P : PrimeSpectrum R, M →ₗ[R] P.asIdeal.ResidueField)
    (hx : ∀ P ∈ S, ∃ x : R, ℓ P (D x) ≠ 0) :
    ∃ u : R, ∀ P ∈ S, ℓ P (D u) ≠ 0 := by
  classical
  -- prime avoidance: `s P ∈ ⋂_{Q ≠ P} Q` and `s P ∉ P`
  have hs : ∀ P ∈ S, ∃ s : R, s ∉ P.asIdeal ∧ ∀ Q ∈ S, Q ≠ P → s ∈ Q.asIdeal := by
    intro P hP
    have hnle : ¬ (S.erase P).inf PrimeSpectrum.asIdeal ≤ P.asIdeal := by
      rw [Ideal.IsPrime.inf_le' P.isPrime]
      rintro ⟨Q, hQ, hQP⟩
      exact (Finset.ne_of_mem_erase hQ) (hanti P hP Q (Finset.mem_of_mem_erase hQ) hQP)
    obtain ⟨s, hsinf, hsP⟩ := Set.not_subset.1 hnle
    refine ⟨s, hsP, fun Q hQ hQP => ?_⟩
    exact (Finset.inf_le (f := PrimeSpectrum.asIdeal) (Finset.mem_erase.2 ⟨hQP, hQ⟩)) hsinf
  choose! s hsP hsQ using hs
  choose! x hxP using hx
  refine ⟨∑ Q ∈ S, s Q ^ p * x Q, fun P hP => ?_⟩
  have hterm : ∀ P Q, ℓ P (D (s Q ^ p * x Q)) = algebraMap R _ (s Q) ^ p * ℓ P (D (x Q)) :=
    fun P Q => by
      rw [leibniz, map_pow_charP D p, smul_zero, add_zero, LinearMap.map_smul, Algebra.smul_def,
        map_pow]
  simp only [map_sum, hterm]
  rw [Finset.sum_eq_single_of_mem P hP fun Q hQ hQP => ?_]
  · refine mul_ne_zero (pow_ne_zero _ ?_) (hxP P hP)
    rw [Ne, Ideal.algebraMap_residueField_eq_zero]
    exact hsP P hP
  · rw [(Ideal.algebraMap_residueField_eq_zero).2 (hsQ Q hQ P hP (Ne.symm hQP)),
      zero_pow (NeZero.ne p), zero_mul]

open TensorProduct in
/-- **A separating element at every minimal prime**, in characteristic `p`: if `R` is a noetherian
`K`-algebra of characteristic `p` whose differentials do not vanish at any minimal prime `P`
(`κ(P) ⊗ Ω[R/K] ≠ 0`), some `u ∈ R` has `du ≠ 0` in `κ(P) ⊗ Ω[R/K]` at every minimal prime. -/
theorem _root_.KaehlerDifferential.exists_forall_minimalPrimes_ne_zero (K R : Type*) [CommRing K]
    [CommRing R] [Algebra K R] [IsNoetherianRing R] (p : ℕ) [CharP R p] [NeZero p]
    (h : ∀ P : PrimeSpectrum R, P.asIdeal ∈ minimalPrimes R →
      Nontrivial (P.asIdeal.ResidueField ⊗[R] Ω[R⁄K])) :
    ∃ u : R, ∀ P : PrimeSpectrum R, P.asIdeal ∈ minimalPrimes R →
      (1 : P.asIdeal.ResidueField) ⊗ₜ[R] KaehlerDifferential.D K R u ≠ 0 := by
  classical
  have hfin : {P : PrimeSpectrum R | P.asIdeal ∈ minimalPrimes R}.Finite :=
    (minimalPrimes.finite_of_isNoetherianRing R).preimage
      fun _ _ _ _ h => PrimeSpectrum.ext h
  set S := hfin.toFinset
  -- a functional on `κ(P) ⊗ Ω` which is nonzero on some `1 ⊗ dx`
  have hx : ∀ P : PrimeSpectrum R, P.asIdeal ∈ minimalPrimes R →
      ∃ (f : P.asIdeal.ResidueField ⊗[R] Ω[R⁄K] →ₗ[P.asIdeal.ResidueField]
          P.asIdeal.ResidueField) (x : R),
        f ((1 : P.asIdeal.ResidueField) ⊗ₜ[R] KaehlerDifferential.D K R x) ≠ 0 := by
    intro P hP
    have := h P hP
    obtain ⟨x, hx⟩ : ∃ x : R,
        (1 : P.asIdeal.ResidueField) ⊗ₜ[R] KaehlerDifferential.D K R x ≠ 0 := by
      by_contra! hall
      have hω : ∀ (ω : Ω[R⁄K]) (c : P.asIdeal.ResidueField), c ⊗ₜ[R] ω = 0 := fun ω c => by
        have hle : Submodule.span R (Set.range (KaehlerDifferential.D K R)) ≤
            LinearMap.ker (TensorProduct.mk R P.asIdeal.ResidueField Ω[R⁄K] c) :=
          Submodule.span_le.2 (by
            rintro _ ⟨y, rfl⟩
            change c ⊗ₜ[R] KaehlerDifferential.D K R y = 0
            rw [show c ⊗ₜ[R] KaehlerDifferential.D K R y =
              c • ((1 : P.asIdeal.ResidueField) ⊗ₜ[R] KaehlerDifferential.D K R y) by
                rw [smul_tmul', smul_eq_mul, mul_one], hall y, smul_zero])
        exact hle (by rw [KaehlerDifferential.span_range_derivation]; trivial)
      have hall0 : ∀ v : P.asIdeal.ResidueField ⊗[R] Ω[R⁄K], v = 0 := by
        intro v
        induction v using TensorProduct.induction_on with
        | zero => rfl
        | tmul c ω => exact hω ω c
        | add a b ha hb => rw [ha, hb, add_zero]
      obtain ⟨v, hv⟩ := exists_ne (0 : P.asIdeal.ResidueField ⊗[R] Ω[R⁄K])
      exact hv (hall0 v)
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero P.asIdeal.ResidueField hx
    exact ⟨f, x, hf⟩
  choose! f x hfx using hx
  let ℓ : ∀ P : PrimeSpectrum R, Ω[R⁄K] →ₗ[R] P.asIdeal.ResidueField := fun P =>
    ((f P).restrictScalars R).comp (TensorProduct.mk R P.asIdeal.ResidueField Ω[R⁄K] 1)
  obtain ⟨u, hu⟩ := Derivation.exists_forall_ne_zero_of_charP (KaehlerDifferential.D K R) p S
    (fun P hP Q hQ hQP => by
      rw [hfin.mem_toFinset] at hP hQ
      exact PrimeSpectrum.ext (le_antisymm hQP (hP.2 ⟨Q.isPrime, bot_le⟩ hQP)))
    ℓ (fun P hP => ⟨x P, hfx P (hfin.mem_toFinset.1 hP)⟩)
  refine ⟨u, fun P hP hzero => hu P (hfin.mem_toFinset.2 hP) ?_⟩
  show f P ((1 : P.asIdeal.ResidueField) ⊗ₜ[R] KaehlerDifferential.D K R u) = 0
  rw [hzero, map_zero]

end Derivation
