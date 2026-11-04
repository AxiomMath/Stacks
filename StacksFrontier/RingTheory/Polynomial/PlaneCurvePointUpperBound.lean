module

public import StacksFrontier.RingTheory.Polynomial.StepanovUpperBound
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The upper bound `q + O(√q)` for the Frobenius points of a plane curve

Let `K` be an algebraically closed field of characteristic `p`, `q = p ^ e` with `e ≥ 1`, and
`Ψ ∈ K[X][Y]` monic irreducible of `Y`-degree `m` and weight `w` (that is, the coefficient of
`Yⁱ` has degree `≤ w (m - i)`), with `∂Ψ/∂Y ≠ 0`. For `R, D` of weighted degree `≤ r`, the points
`P = (a, b)` of `Ψ = 0` with `∂Ψ/∂Y(P) ≠ 0`, `a ^ q = a`, `D(P) ≠ 0` and `D(P) b ^ q = R(P)`
number at most `q + C √q`, where `C` depends only on `m`, `w` and `r`.

This is `Polynomial.Bivariate.card_mul_le_of_stepanov` with the parameters
`ρ = p ^ ⌊e/2⌋`, `σ = p ^ ⌈e/2⌉`, `k = 1` if `e` is even and `k = ⌊√p⌋` if `e` is odd, and
`aV ≈ σ/m`, `aW ≈ kρ/m`; small `q` are covered by the trivial bound `m q`.

## Main results

* `Polynomial.Bivariate.card_le_mul_of_frobenius`: the trivial bound `#S ≤ q m`.
* `Polynomial.Bivariate.exists_card_le_add_mul_sqrt`: the bound `#S ≤ q + C √q`.
-/

@[expose] public section

open Polynomial
open scoped Polynomial.Bivariate

namespace Polynomial.Bivariate

variable {K : Type*} [Field K]

/-- **The trivial bound.** Points of `Ψ = 0` whose first coordinate satisfies `a ^ q = a`
(`q ≥ 2`) number at most `q · deg_Y Ψ`. -/
theorem card_le_mul_of_frobenius {Ψ : K[X][Y]} (hΨ : Ψ.Monic) {q : ℕ} (hq : 1 < q)
    (S : Finset (K × K)) (hS : ∀ P ∈ S, Ψ.evalEval P.1 P.2 = 0 ∧ P.1 ^ q = P.1) :
    S.card ≤ q * Ψ.natDegree := by
  classical
  have hX : (X ^ q - X : K[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hq
  refine (card_le_card_mul_of_fibres (X ^ q - X : K[X]).roots.toFinset S
    (fun a => Ψ.map (evalRingHom a)) (D := Ψ.natDegree) (fun P hP => ⟨?_, ?_, ?_⟩)
    (fun a _ => natDegree_map_le)).trans (Nat.mul_le_mul_right _ ?_)
  · refine Multiset.mem_toFinset.mpr ((mem_roots hX).mpr ?_)
    simp [(hS P hP).2]
  · exact (hΨ.map _).ne_zero
  · rw [IsRoot, map_evalRingHom_eval]
    exact (hS P hP).1
  · exact (Multiset.toFinset_card_le _).trans ((card_roots' _).trans
      (FiniteField.X_pow_card_sub_X_natDegree_eq K hq).le)

/-- Floor division by `m > 0` is sandwiched: `m * (n / m) ≤ n < m * (n / m) + m`. -/
private theorem mul_div_bounds {m : ℕ} (hm : 0 < m) (n : ℕ) :
    m * (n / m) ≤ n ∧ n < m * (n / m) + m :=
  ⟨Nat.mul_div_le _ _, by simpa [mul_add_one] using Nat.lt_mul_div_succ n hm⟩

/-- The arithmetic behind the choice of parameters: for `σ` large and `k² ρ ≤ σ`, suitable
`aV`, `aW` exist. -/
theorem exists_stepanov_parameters (m w r : ℕ) (hm : 0 < m) :
    ∃ σ₀ C₀ : ℕ, ∀ ρ σ k : ℕ, 1 ≤ k → 1 ≤ ρ → k ^ 2 * ρ ≤ σ → σ₀ ≤ σ → ∃ aV aW : ℕ,
      m * (aV + w * (m - 1)) < σ ∧
      k * (m * (ρ * (aV + w * (m - 1) + (k - 1) * (w * m)) + (aW + r * (m - 1)) + 1)) <
        (m * (aW + 1)) * (m * (aV + 1)) ∧
      m * (aV + w * (m - 1) + σ * (aW + w * (m - 1))) ≤ k * ρ * σ + σ * C₀ := by
  set A := m * (w * (m - 1) + 1)
  set c := A + w * m ^ 2 + 1
  set B := c + m * (r * m + 1)
  refine ⟨max (2 * (A * (c + 1)) + 1) (4 * B ^ 2), 1 + c + m * (w * (m - 1)), ?_⟩
  intro ρ σ k hk hρ1 hkρ hσ
  obtain ⟨hσ1, hσ2⟩ := max_le_iff.mp hσ
  have hk2 : k ^ 2 ≤ σ := le_trans (Nat.le_mul_of_pos_right _ hρ1) hkρ
  have hkk : k ≤ k ^ 2 := Nat.le_self_pow two_ne_zero k
  have hρ : k * ρ ≤ σ := le_trans (Nat.mul_le_mul_right _ hkk) hkρ
  have hAc : A ≤ A * (c + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  obtain ⟨hmt1, hmt2⟩ := mul_div_bounds hm (σ - 1)
  set t := (σ - 1) / m
  have ht3 : w * (m - 1) + 1 ≤ t := (Nat.le_div_iff_mul_le hm).mpr (by
    have : (w * (m - 1) + 1) * m = A := by
      simp only [A]
      ring
    omega)
  obtain ⟨hmw1, hmw2⟩ := mul_div_bounds hm (k * ρ + c)
  set aW := (k * ρ + c) / m
  have htu : t - w * (m - 1) + w * (m - 1) = t := Nat.sub_add_cancel (by omega)
  refine ⟨t - w * (m - 1), aW, ?_, ?_, ?_⟩
  · rw [htu]
    omega
  · rw [htu]
    have hkB : 2 * (k * B) ≤ σ := by
      have : (2 * (k * B)) ^ 2 ≤ σ ^ 2 := by
        calc (2 * (k * B)) ^ 2 = k ^ 2 * (4 * B ^ 2) := by ring
          _ ≤ σ * σ := Nat.mul_le_mul hk2 hσ2
          _ = σ ^ 2 := by ring
      exact (Nat.pow_le_pow_iff_left (by norm_num)).mp this
    set Yv := m * (t - w * (m - 1) + 1)
    have hY : σ ≤ Yv + A := by
      have hu : (t - w * (m - 1) + 1) + (w * (m - 1) + 1) = t + 2 := by omega
      have h' : Yv + A = m * t + 2 * m := by
        simp only [Yv, A]
        rw [← mul_add, hu]
        ring
      omega
    have hwm : (k - 1) * (w * m) * (k * m * ρ) ≤ σ * (w * m ^ 2) := by
      calc (k - 1) * (w * m) * (k * m * ρ) ≤ k * (w * m) * (k * m * ρ) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
        _ = (k ^ 2 * ρ) * (w * m ^ 2) := by ring
        _ ≤ σ * (w * m ^ 2) := Nat.mul_le_mul_right _ hkρ
    have hrm : k * m * (r * (m - 1)) ≤ k * m * (r * m) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    have e1 : k * ρ * (m * t) + k * ρ ≤ k * ρ * σ := by
      have := Nat.mul_le_mul_left (k * ρ) (show m * t + 1 ≤ σ by omega)
      rwa [mul_add, mul_one] at this
    have e2 : k * (m * aW) ≤ k * (k * ρ) + k * c := by
      have := Nat.mul_le_mul_left k hmw1
      rwa [mul_add] at this
    have e3 : k * (k * ρ) ≤ σ := by
      have : k * (k * ρ) = k ^ 2 * ρ := by ring
      omega
    have expand : k * (m * (ρ * (t + (k - 1) * (w * m)) + (aW + r * (m - 1)) + 1)) =
        k * ρ * (m * t) + (k - 1) * (w * m) * (k * m * ρ) + k * (m * aW) +
          k * m * (r * (m - 1)) + k * m := by ring
    have hrhs : k * ρ * σ + c * σ + σ ≤ (k * ρ + c + 1) * Yv + (k * ρ * A + c * A + A) := by
      have h := Nat.mul_le_mul_left (k * ρ + c + 1) hY
      have e : (k * ρ + c + 1) * (Yv + A) = (k * ρ + c + 1) * Yv + (k * ρ * A + c * A + A) := by
        ring
      have e' : (k * ρ + c + 1) * σ = k * ρ * σ + c * σ + σ := by ring
      omega
    have h1 : k * ρ * A ≤ σ * A := Nat.mul_le_mul_right _ hρ
    have hB : k * B = k * c + k * m * (r * m) + k * m := by simp only [B]; ring
    have hcA : A * (c + 1) = c * A + A := by ring
    have hcσ : c * σ = σ * A + σ * (w * m ^ 2) + σ := by simp only [c]; ring
    rw [expand]
    calc _ < (k * ρ + c + 1) * Yv := by omega
      _ ≤ m * (aW + 1) * Yv := Nat.mul_le_mul_right _ hmw2
  · rw [htu]
    have hmt : m * t ≤ σ := by omega
    calc m * (t + σ * (aW + w * (m - 1))) = m * t + σ * (m * aW) + σ * (m * (w * (m - 1))) := by
          ring
      _ ≤ σ + σ * (k * ρ + c) + σ * (m * (w * (m - 1))) := by
          gcongr
      _ = k * ρ * σ + σ * (1 + c + m * (w * (m - 1))) := by ring

/-- The choice `k = 1` (`e` even) or `k = ⌊√p⌋` (`e` odd), with `ρ = p ^ ⌊e/2⌋`,
`σ = p ^ (e - ⌊e/2⌋)`: then `k ≤ p`, `k² ρ ≤ σ ≤ 4 k² ρ`. -/
theorem exists_stepanov_k (p e : ℕ) (hp : p.Prime) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ p ∧ k ^ 2 * p ^ (e / 2) ≤ p ^ (e - e / 2) ∧
      p ^ (e - e / 2) ≤ 4 * k ^ 2 * p ^ (e / 2) := by
  have hp2 := hp.two_le
  rcases Nat.even_or_odd e with he | he
  · have h : e - e / 2 = e / 2 := by
      obtain ⟨j, rfl⟩ := he
      omega
    rw [h]
    exact ⟨1, le_rfl, by omega, by simp, by nlinarith [Nat.one_le_pow (e / 2) p (by omega)]⟩
  · have hb : e - e / 2 = e / 2 + 1 := by
      obtain ⟨j, rfl⟩ := he
      omega
    rw [hb, pow_succ]
    have hk1 : 1 ≤ Nat.sqrt p := Nat.sqrt_pos.mpr (by omega)
    have hk2 : Nat.sqrt p ^ 2 ≤ p := Nat.sqrt_le' p
    have hk3 : p < (Nat.sqrt p + 1) ^ 2 := Nat.lt_succ_sqrt' p
    refine ⟨Nat.sqrt p, hk1, Nat.sqrt_le_self p, ?_, ?_⟩
    · rw [mul_comm]
      exact Nat.mul_le_mul_left _ hk2
    · have : p ≤ 4 * Nat.sqrt p ^ 2 := by nlinarith
      calc p ^ (e / 2) * p ≤ p ^ (e / 2) * (4 * Nat.sqrt p ^ 2) := Nat.mul_le_mul_left _ this
        _ = 4 * Nat.sqrt p ^ 2 * p ^ (e / 2) := by ring

/-- **The upper bound `q + C √q`.** For given `m`, `w`, `r` there is a constant `C` such that,
over every algebraically closed field `K` of characteristic `p` and for every `q = p ^ e` with
`e ≥ 1`, every finite set `S` of twisted Frobenius points of a monic irreducible `Ψ` of
`Y`-degree `m` and weight `w` with `∂Ψ/∂Y ≠ 0`, at which `∂Ψ/∂Y` does not vanish, has
`#S ≤ q + C √q`. -/
theorem exists_card_le_add_mul_sqrt (m w r : ℕ) :
    ∃ C : ℝ, ∀ (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p] (e : ℕ),
      0 < e → ∀ Ψ R D : K[X][Y], Ψ.Monic → Irreducible Ψ → derivative Ψ ≠ 0 →
      Ψ.natDegree = m → WeightedDegreeLE w (w * m) Ψ → WeightedDegreeLE w r R →
      WeightedDegreeLE w r D → ∀ S : Finset (K × K),
      (∀ P ∈ S, Ψ.evalEval P.1 P.2 = 0 ∧ (derivative Ψ).evalEval P.1 P.2 ≠ 0 ∧
        P.1 ^ p ^ e = P.1 ∧ D.evalEval P.1 P.2 ≠ 0 ∧
        D.evalEval P.1 P.2 * P.2 ^ p ^ e = R.evalEval P.1 P.2) →
      (S.card : ℝ) ≤ (p : ℝ) ^ e + C * √((p : ℝ) ^ e) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨0, fun K _ _ p _ _ e he Ψ R D hΨ hirr _ hm _ _ _ S hS => ?_⟩
    simpa [eq_one_of_monic_natDegree_zero hΨ hm] using hirr.not_isUnit
  obtain ⟨σ₀, C₀, hpar⟩ := exists_stepanov_parameters m w r hm
  refine ⟨max (2 * (C₀ : ℝ)) (((m : ℝ) - 1) * σ₀), fun K _ _ p _ _ e he Ψ R D hΨ hirr hder hmΨ
    hΨw hR hD S hS => ?_⟩
  have : PerfectRing K p := PerfectField.toPerfectRing p
  have hp := (Fact.out : p.Prime)
  set a := e / 2
  set b := e - e / 2
  have hab : e = a + b := by omega
  obtain ⟨k, hk1, hkp, hkρ, hkσ⟩ := exists_stepanov_k p e hp
  set ρ := p ^ a
  set σ := p ^ b
  have hρ1 : 1 ≤ ρ := Nat.one_le_pow _ _ hp.pos
  have hq : (p : ℝ) ^ e = (ρ : ℝ) * σ := by
    rw [hab, pow_add]
    simp [ρ, σ]
  by_cases hσ : σ₀ ≤ σ
  · obtain ⟨aV, aW, hV, hcount, hfin⟩ := hpar ρ σ k hk1 hρ1 hkρ hσ
    have hkq : k * p ^ a ≤ p ^ (a + b) := by
      rw [pow_add]
      calc k * p ^ a ≤ k ^ 2 * p ^ a := Nat.mul_le_mul_right _ (Nat.le_self_pow two_ne_zero k)
        _ ≤ σ := hkρ
        _ ≤ p ^ a * σ := Nat.le_mul_of_pos_left _ hρ1
    have hmain : k * S.card ≤ k * ρ * σ + σ * C₀ :=
      (card_mul_le_of_stepanov p hΨ hirr hder hmΨ hΨw hR hD hkp hkq hV hcount S
        (by rwa [← hab])).trans hfin
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    -- `σ ≤ 2 k √q`
    have hσk : (σ : ℝ) ≤ 2 * k * √((p : ℝ) ^ e) := by
      rw [show (2 * k * √((p : ℝ) ^ e) : ℝ) = √((2 * k) ^ 2 * (p : ℝ) ^ e) by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]]
      refine Real.le_sqrt_of_sq_le ?_
      rw [hq]
      have h1 : (σ : ℝ) ≤ 4 * k ^ 2 * ρ := by exact_mod_cast hkσ
      have h2 : (0 : ℝ) ≤ σ := by positivity
      nlinarith
    have hcard : (S.card : ℝ) ≤ ρ * σ + C₀ * (σ / k) := by
      have h : (k : ℝ) * S.card ≤ k * ρ * σ + σ * C₀ := by exact_mod_cast hmain
      have e : (ρ : ℝ) * σ + C₀ * (σ / k) = (k * ρ * σ + σ * C₀) / k := by
        field_simp
      rw [e, le_div_iff₀ hk0]
      linarith
    calc (S.card : ℝ) ≤ ρ * σ + C₀ * (σ / k) := hcard
      _ ≤ ρ * σ + C₀ * (2 * √((p : ℝ) ^ e)) := by
          gcongr
          rw [div_le_iff₀ hk0]
          linarith
      _ = (p : ℝ) ^ e + (2 * C₀) * √((p : ℝ) ^ e) := by rw [hq]; ring
      _ ≤ (p : ℝ) ^ e + max (2 * (C₀ : ℝ)) (((m : ℝ) - 1) * σ₀) * √((p : ℝ) ^ e) := by
          gcongr
          exact le_max_left _ _
  · push Not at hσ
    have hq1 : 1 < p ^ e := Nat.one_lt_pow he.ne' hp.one_lt
    have htriv := card_le_mul_of_frobenius hΨ hq1 S fun P hP => ⟨(hS P hP).1, (hS P hP).2.2.1⟩
    rw [hmΨ] at htriv
    have hρσ : ρ ≤ σ := Nat.pow_le_pow_right hp.pos (by omega)
    have hsq : (p : ℝ) ^ e ≤ σ₀ * √((p : ℝ) ^ e) := by
      have hσ0 : (0 : ℝ) ≤ σ := by positivity
      have h1 : (p : ℝ) ^ e ≤ (σ : ℝ) ^ 2 := by
        rw [hq, sq]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hρσ) hσ0
      have h2 : √((p : ℝ) ^ e) ≤ σ₀ :=
        ((Real.sqrt_le_sqrt h1).trans_eq (Real.sqrt_sq hσ0)).trans (by exact_mod_cast hσ.le)
      calc (p : ℝ) ^ e = √((p : ℝ) ^ e) * √((p : ℝ) ^ e) :=
            (Real.mul_self_sqrt (by positivity)).symm
        _ ≤ σ₀ * √((p : ℝ) ^ e) := mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    calc (S.card : ℝ) ≤ (p : ℝ) ^ e * m := by exact_mod_cast htriv
      _ = (p : ℝ) ^ e + (m - 1) * (p : ℝ) ^ e := by ring
      _ ≤ (p : ℝ) ^ e + (m - 1) * (σ₀ * √((p : ℝ) ^ e)) := by
          gcongr
      _ = (p : ℝ) ^ e + ((m - 1) * σ₀) * √((p : ℝ) ^ e) := by ring
      _ ≤ (p : ℝ) ^ e + max (2 * (C₀ : ℝ)) (((m : ℝ) - 1) * σ₀) * √((p : ℝ) ^ e) := by
          gcongr
          exact le_max_right _ _

end Polynomial.Bivariate
