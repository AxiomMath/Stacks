module

public import StacksFrontier.Algebra.Polynomial.PadicResultant

/-!
# Mumford's resultant lemma for an `ℓ`-adically dense set of integral polynomials

`Stacks.Polynomial.eq_of_norm_resultant_intPoly_eq` determines a monic polynomial `P` over `ℚ_ℓ`
from the norms `‖Res(P, R)‖` for the integral polynomials `R` with `p ∤ R(0)`. The proof uses the
condition `p ∤ R(0)` only through one property of this set of polynomials: every `S ∈ ℤ_ℓ[X]` is,
modulo every power of `ℓ`, congruent to a member of the set of the same degree. This file proves
the lemma for an arbitrary set of integral polynomials with that property, and shows that the
polynomials congruent modulo `p` to a constant prime to `p` form such a set
(`Stacks.Polynomial.exists_intPoly_map_toZModPow_eq_modEq_const`).

That is the set needed for an arbitrary endomorphism `α` of an abelian variety in characteristic
`p` ([Mumford, *Abelian varieties*, §19, Theorem 4]): for `R ≡ c (mod p)` with `p ∤ c`, the
derivative of `R(α)` at the identity is multiplication by `c`, so `R(α)` is étale and its kernel
has `deg R(α)` points. The set `p ∤ R(0)` of the Frobenius case is too large there.

## Main results

* `Stacks.Polynomial.norm_resultant_eq_of_intPoly_of_dense`: the extension of the hypothesis to
  all `S ∈ ℤ_ℓ[X]` by continuity.
* `Stacks.Polynomial.eq_of_norm_resultant_intPoly_eq_of_dense`: the lemma for a dense set.
* `Stacks.Polynomial.exists_intPoly_map_toZModPow_eq_modEq_const`: the density of the
  polynomials which are congruent to a constant prime to `p` modulo `p`.
-/

@[expose] public noncomputable section

open Polynomial Filter Topology

namespace Stacks.Polynomial

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- For primes `p ≠ ℓ`, any residues `a k` modulo `ℓ^N` and `t k` modulo `p` are attained by
integers `b k`, with `b d ≠ 0` at a chosen index `d`. -/
theorem exists_intCast_eq_dvd_sub_ne_zero (p : ℕ) (hp : p.Prime) (hpℓ : p ≠ ℓ) (N : ℕ)
    (a t : ℕ → ℤ) (d : ℕ) : ∃ b : ℕ → ℤ, (∀ k, ((b k : ℤ) : ZMod (ℓ ^ N)) = a k) ∧
      (∀ k, (p : ℤ) ∣ b k - t k) ∧ b d ≠ 0 := by
  classical
  have hcop : IsCoprime ((ℓ : ℤ) ^ N) (p : ℤ) := by
    refine IsCoprime.pow_left ?_
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact (Nat.coprime_primes hℓ.out hp).2 (Ne.symm hpℓ)
  obtain ⟨u, v, huv⟩ := hcop
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : ℕ → ℤ, b₀ = fun k => a k + (ℓ : ℤ) ^ N * (u * (t k - a k)) :=
    ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b : ℕ → ℤ,
      b = fun k => if k = d ∧ b₀ k = 0 then (ℓ : ℤ) ^ N * p else b₀ k := ⟨_, rfl⟩
  have hl : ((ℓ : ZMod (ℓ ^ N))) ^ N = 0 := by
    rw [← Nat.cast_pow]
    exact ZMod.natCast_self _
  have hb₀N : ∀ k, ((b₀ k : ℤ) : ZMod (ℓ ^ N)) = ((a k : ℤ) : ZMod (ℓ ^ N)) := fun k => by
    rw [hb₀]
    push_cast
    rw [hl]
    ring
  -- modulo `p`, `b₀ k` is `t k`
  have hb₀p : ∀ k, (p : ℤ) ∣ b₀ k - t k := fun k => by
    refine ⟨v * (a k - t k), ?_⟩
    rw [hb₀]
    dsimp only
    linear_combination (t k - a k) * huv
  refine ⟨b, fun k => ?_, fun k => ?_, ?_⟩ <;> rw [hbdef] <;> dsimp only <;> split_ifs with h
  · rw [← hb₀N, h.2]
    push_cast
    rw [hl]
    ring
  · exact hb₀N k
  · have h1 := hb₀p k
    rw [h.2, zero_sub, dvd_neg] at h1
    exact (dvd_mul_left (p : ℤ) ((ℓ : ℤ) ^ N)).sub h1
  · exact hb₀p k
  · exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hℓ.out.ne_zero))
      (by exact_mod_cast hp.ne_zero)
  · exact fun h0 => h ⟨rfl, h0⟩

/-- A polynomial with prescribed coefficients `b j` for `j ≤ d` and `b d ≠ 0` has degree `d`. -/
theorem exists_natDegree_eq_coeff_eq_ite {A : Type*} [Semiring A] (b : ℕ → A) (d : ℕ)
    (hbd : b d ≠ 0) : ∃ R : A[X], R.natDegree = d ∧ ∀ j, R.coeff j = if j ≤ d then b j else 0 := by
  classical
  have hc : ∀ j, (∑ k ∈ Finset.range (d + 1), monomial k (b k)).coeff j =
      if j ≤ d then b j else 0 := fun j => by
    simp only [finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq', Finset.mem_range,
      Nat.lt_succ_iff]
  refine ⟨_, le_antisymm (natDegree_le_iff_coeff_eq_zero.2 fun j hj => ?_)
    (le_natDegree_of_ne_zero ?_), hc⟩
  · rw [hc, ite_eq_right (by exact_mod_cast not_le.2 hj)]
  · rwa [hc, ite_eq_left le_rfl]

/-- **Integral approximation with a prescribed reduction modulo `p`.** For primes `p ≠ ℓ`, every
`S ∈ ℤ_ℓ[X]` is congruent modulo `ℓ^N` to an integral polynomial `R` of the same degree which is
congruent modulo `p` to a constant prime to `p`: `p ∤ R(0)` and `p ∣ R_k` for `k ≠ 0`. -/
theorem exists_intPoly_map_toZModPow_eq_modEq_const (p : ℕ) (hp : p.Prime) (hpℓ : p ≠ ℓ)
    (S : ℤ_[ℓ][X]) (N : ℕ) : ∃ R : ℤ[X], R.natDegree = S.natDegree ∧
      (¬ (p : ℤ) ∣ R.coeff 0 ∧ ∀ k, k ≠ 0 → (p : ℤ) ∣ R.coeff k) ∧
      (R.map (Int.castRingHom ℤ_[ℓ])).map (PadicInt.toZModPow N) =
        S.map (PadicInt.toZModPow N) := by
  obtain ⟨b, hb, hbp, hbd⟩ := exists_intCast_eq_dvd_sub_ne_zero p hp hpℓ N
    (fun k => ((PadicInt.toZModPow N (S.coeff k)).val : ℤ)) (fun k => if k = 0 then 1 else 0)
    S.natDegree
  obtain ⟨R, hRdeg, hRc⟩ := exists_natDegree_eq_coeff_eq_ite b S.natDegree hbd
  have hp1 : ¬ (p : ℤ) ∣ 1 := fun h => hp.not_dvd_one (by exact_mod_cast h)
  refine ⟨R, hRdeg, ⟨?_, fun k hk => ?_⟩, ?_⟩
  · rw [hRc, ite_eq_left (Nat.zero_le _)]
    exact fun h => hp1 (by simpa using dvd_sub h (hbp 0))
  · rw [hRc]
    split_ifs
    · simpa [hk] using hbp k
    · exact dvd_zero _
  ext j
  rw [coeff_map, coeff_map, coeff_map, hRc]
  split_ifs with hj
  · rw [eq_intCast, map_intCast, hb]
    simp
  · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hj)]
    simp

/-- **The hypothesis of Mumford's lemma extends from a dense set of integral polynomials to all
of `ℤ_ℓ[X]`.** Let `good` be a set of integral polynomials such that every `S ∈ ℤ_ℓ[X]` is,
modulo every `ℓ^N`, congruent to a member of `good` of the same degree. If
`‖Res(P, R)‖ = ‖Res(T, R)‖` for every `R ∈ good` with `Res(Q, R) ≠ 0`, then the same holds for
every `S ∈ ℤ_ℓ[X]` with `Res(Q, S) ≠ 0`: the resultants are continuous in the coefficients. -/
theorem norm_resultant_eq_of_intPoly_of_dense (good : ℤ[X] → Prop)
    (hdense : ∀ (S : ℤ_[ℓ][X]) (N : ℕ), ∃ R : ℤ[X], R.natDegree = S.natDegree ∧ good R ∧
      (R.map (Int.castRingHom ℤ_[ℓ])).map (PadicInt.toZModPow N) = S.map (PadicInt.toZModPow N))
    (P T Q : ℚ_[ℓ][X])
    (H : ∀ R : ℤ[X], good R → Q.resultant (R.map (Int.castRingHom ℚ_[ℓ])) ≠ 0 →
      ‖P.resultant (R.map (Int.castRingHom ℚ_[ℓ]))‖ = ‖T.resultant (R.map (Int.castRingHom ℚ_[ℓ]))‖)
    (S : ℤ_[ℓ][X]) (hS : Q.resultant (S.map PadicInt.Coe.ringHom) ≠ 0) :
    ‖P.resultant (S.map PadicInt.Coe.ringHom)‖ = ‖T.resultant (S.map PadicInt.Coe.ringHom)‖ := by
  set n := S.natDegree
  have hinjZ : Function.Injective (Int.castRingHom ℚ_[ℓ]) := RingHom.injective_int _
  have hinjS : Function.Injective (PadicInt.Coe.ringHom (p := ℓ)) := Subtype.val_injective
  choose R hRdeg hR0 hRS using fun N : ℕ => hdense S N
  set S' := S.map PadicInt.Coe.ringHom
  have hS'deg : S'.natDegree = n := natDegree_map_eq_of_injective hinjS S
  set R' : ℕ → ℚ_[ℓ][X] := fun N => (R N).map (Int.castRingHom ℚ_[ℓ])
  have hR'deg : ∀ N, (R' N).natDegree = n := fun N =>
    (natDegree_map_eq_of_injective hinjZ _).trans (hRdeg N)
  -- coefficientwise convergence
  have hconv : Tendsto (fun N => fun k : Fin (n + 1) => (R' N).coeff k) atTop
      (𝓝 fun k : Fin (n + 1) => S'.coeff k) := by
    refine tendsto_pi_nhds.2 fun k => ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_)
      (by
        have := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (Padic.norm_p_lt_one (p := ℓ))).norm
        rwa [norm_zero] at this)
    have hc := congrArg (fun F => F.coeff k) (hRS N)
    simp only [coeff_map] at hc
    have hmem : (Int.castRingHom ℤ_[ℓ] ((R N).coeff k) - S.coeff k) ∈
        RingHom.ker (PadicInt.toZModPow (p := ℓ) N) := by
      rw [RingHom.mem_ker, map_sub, hc, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hmem
    obtain ⟨y, hy⟩ := hmem
    have : (R' N).coeff k - S'.coeff k = ((ℓ : ℚ_[ℓ]) ^ N) * PadicInt.Coe.ringHom y := by
      have := congrArg PadicInt.Coe.ringHom hy
      simp only [map_sub, map_mul, map_pow, map_natCast, eq_intCast, map_intCast] at this
      simp only [R', S', coeff_map, eq_intCast]
      exact this
    rw [this, norm_mul]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    exact (PadicInt.norm_coe y).trans_le (PadicInt.norm_le_one y)
  have hlim : ∀ F : ℚ_[ℓ][X], Tendsto (fun N => F.resultant (R' N)) atTop
      (𝓝 (F.resultant S')) := fun F => by
    have := ((continuous_resultant_sum_C_mul_X_pow F F.natDegree n).tendsto _).comp hconv
    simp only [Function.comp_def] at this
    rw [sum_fin_C_coeff_mul_X_pow S' hS'deg.le] at this
    rw [hS'deg]
    exact this.congr fun N => by rw [sum_fin_C_coeff_mul_X_pow _ (hR'deg N).le, hR'deg N]
  have hev : ∀ᶠ N in atTop, Q.resultant (R' N) ≠ 0 :=
    (hlim Q).eventually (isOpen_ne.mem_nhds hS)
  exact tendsto_nhds_unique ((hlim P).norm.congr' (hev.mono fun N hN => H (R N) (hR0 N) hN))
    (hlim T).norm

/-- **Mumford's resultant lemma over `ℚ_ℓ` for a dense set of integral polynomials.** Let `good`
be a set of integral polynomials such that every `S ∈ ℤ_ℓ[X]` is, modulo every `ℓ^N`,
congruent to a member of `good` of the same degree, let `χ`, `P` be monic of the same degree over
`ℚ_ℓ` and `D ≠ 0`. If `‖Res(P, R)‖ = ‖Res(χ, R)‖` for every `R ∈ good` with `Res(D χ, R) ≠ 0`,
then `P = χ`. -/
theorem eq_of_norm_resultant_intPoly_eq_of_dense (good : ℤ[X] → Prop)
    (hdense : ∀ (S : ℤ_[ℓ][X]) (N : ℕ), ∃ R : ℤ[X], R.natDegree = S.natDegree ∧ good R ∧
      (R.map (Int.castRingHom ℤ_[ℓ])).map (PadicInt.toZModPow N) = S.map (PadicInt.toZModPow N))
    (χ P D : ℚ_[ℓ][X]) (hχ : χ.Monic) (hP : P.Monic) (hdeg : P.natDegree = χ.natDegree)
    (hD : D ≠ 0)
    (H : ∀ R : ℤ[X], good R →
      (D * χ).resultant (R.map (Int.castRingHom ℚ_[ℓ])) ≠ 0 →
      ‖P.resultant (R.map (Int.castRingHom ℚ_[ℓ]))‖ =
        ‖χ.resultant (R.map (Int.castRingHom ℚ_[ℓ]))‖) :
    P = χ := by
  refine eq_of_norm_resultant_eq χ P D hχ hP hdeg hD fun S hS hres => ?_
  obtain ⟨S', rfl⟩ : S ∈ Polynomial.lifts (PadicInt.Coe.ringHom (p := ℓ)) :=
    (lifts_iff_coeff_lifts S).2 fun k => ⟨⟨S.coeff k, hS k⟩, rfl⟩
  exact norm_resultant_eq_of_intPoly_of_dense good hdense P χ (D * χ) H S' hres

end Stacks.Polynomial
