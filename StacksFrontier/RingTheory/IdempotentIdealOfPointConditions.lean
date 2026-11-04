module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Noetherian.Nilpotent

/-!
# An ideal whose conormal module is torsion and which lies in the primes it meets

Let `R` be a Noetherian ring, `π ∈ R` a nonzerodivisor and `J ⊆ R` an ideal. Suppose that
`π ^ N J ⊆ J ^ 2` for some `N`, and that `J ⊆ 𝔮` for every prime `𝔮 ∌ π` contained in a maximal
ideal containing `J`. Then `J` is idempotent, `J ^ 2 = J`.

## Main results

* `Ideal.isIdempotentElem_of_span_pow_mul_le_sq`: the statement above.
-/


@[expose] public section

namespace Ideal

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

omit [IsNoetherianRing R] in
/-- If `π ^ N J ⊆ J ^ 2`, then `π ^ (N k) J ⊆ J ^ (k + 1)` for every `k`. -/
theorem span_pow_mul_mul_le_pow_succ {π : R} {J : Ideal R} {N : ℕ}
    (hN : Ideal.span {π ^ N} * J ≤ J ^ 2) (k : ℕ) :
    Ideal.span {π ^ (N * k)} * J ≤ J ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc Ideal.span {π ^ (N * (k + 1))} * J
        = Ideal.span {π ^ N} * (Ideal.span {π ^ (N * k)} * J) := by
          rw [← mul_assoc, Ideal.span_singleton_mul_span_singleton, ← pow_add, mul_add,
            mul_one, add_comm]
      _ ≤ Ideal.span {π ^ N} * J ^ (k + 1) := Ideal.mul_mono_right ih
      _ = (Ideal.span {π ^ N} * J) * J ^ k := by rw [pow_succ', mul_assoc]
      _ ≤ J ^ 2 * J ^ k := Ideal.mul_mono_left hN
      _ = J ^ (k + 1 + 1) := by rw [← pow_add]; ring_nf

/-- **An ideal with torsion conormal module lying in the primes it meets is idempotent.** Let
`R` be a Noetherian ring, `π` a nonzerodivisor of `R` and `J` an ideal with
`π ^ N J ⊆ J ^ 2`. If `J ⊆ 𝔮` for every prime `𝔮` not containing `π` that lies in a maximal
ideal containing `J`, then `J * J = J`. -/
theorem isIdempotentElem_of_span_pow_mul_le_sq {π : R} (hπ : π ∈ nonZeroDivisors R)
    {J : Ideal R} {N : ℕ} (hN : Ideal.span {π ^ N} * J ≤ J ^ 2)
    (hpt : ∀ q m : Ideal R, q.IsPrime → m.IsMaximal → q ≤ m → J ≤ m → π ∉ q → J ≤ q) :
    IsIdempotentElem J := by
  classical
  have hfin := minimalPrimes.finite_of_isNoetherianRing R
  let T : Finset (Ideal R) := hfin.toFinset.filter fun q => ¬ J ≤ q
  let 𝔟 : Ideal R := ∏ q ∈ T, q
  have hmemT : ∀ q, q ∈ T ↔ q ∈ minimalPrimes R ∧ ¬ J ≤ q := fun q => by
    simp [T, Set.Finite.mem_toFinset]
  have hπmin : ∀ q ∈ minimalPrimes R, π ∉ q := fun q hq hπq =>
    notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hπq hq hπ
  have hcop : J ⊔ 𝔟 = ⊤ := by
    refine Ideal.sup_prod_eq_top fun q hq => ?_
    obtain ⟨hqmin, hJq⟩ := (hmemT q).mp hq
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    exact hJq (hpt q m hqmin.1.1 hm (le_sup_right.trans hle) (le_sup_left.trans hle)
      (hπmin q hqmin))
  have hnil : J * 𝔟 ≤ nilradical R := by
    rw [nilradical_eq_sInf]
    refine le_sInf fun p hp => ?_
    have _ : p.IsPrime := hp
    obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le (J := p) bot_le
    have hq' : q ∈ minimalPrimes R := by simpa [minimalPrimes] using hq
    refine le_trans ?_ hqp
    by_cases hJq : J ≤ q
    · exact Ideal.mul_le_left.trans hJq
    · exact Ideal.mul_le_right.trans (Ideal.prod_le_inf.trans
        (Finset.inf_le (f := id) ((hmemT q).mpr ⟨hq', hJq⟩)))
  obtain ⟨e, he⟩ := IsNoetherianRing.isNilpotent_nilradical R
  have hJbe : J ^ e * 𝔟 ^ e = ⊥ := by
    rw [← mul_pow]
    exact le_bot_iff.mp ((Ideal.pow_right_mono hnil e).trans (le_of_eq he))
  have hkill : ∀ x ∈ J, ∀ c ∈ 𝔟 ^ e, x * c = 0 := by
    intro x hx c hc
    have hmem : π ^ (N * e) * x * c ∈ J ^ e * 𝔟 ^ e := by
      refine Ideal.mul_mem_mul ?_ hc
      have h1 : π ^ (N * e) * x ∈ J ^ (e + 1) :=
        span_pow_mul_mul_le_pow_succ hN e
          (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hx)
      exact Ideal.pow_le_pow_right (Nat.le_succ e) h1
    rw [hJbe, Ideal.mem_bot, mul_assoc] at hmem
    exact (mem_nonZeroDivisors_iff.mp (pow_mem hπ (N * e))).1 _ hmem
  obtain ⟨j, hj, c, hc, hjc⟩ := Submodule.mem_sup.mp
    ((Ideal.sup_pow_eq_top (n := e) hcop).symm ▸ Submodule.mem_top : (1 : R) ∈ J ⊔ 𝔟 ^ e)
  refine le_antisymm Ideal.mul_le_right fun x hx => ?_
  have hx' : x = x * j := by
    calc x = x * (j + c) := by rw [hjc, mul_one]
      _ = x * j := by rw [mul_add, hkill x hx c hc, add_zero]
  rw [hx']
  exact Ideal.mul_mem_mul hx hj

end Ideal
