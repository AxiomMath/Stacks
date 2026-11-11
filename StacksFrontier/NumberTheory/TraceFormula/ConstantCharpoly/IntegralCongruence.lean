module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import StacksFrontier.NumberTheory.TraceFormula.ConstantCharpoly.IntegralCongruenceBasic

/-!
# Integral congruences for factorizations over `𝔽_ℓ⟦X⟧`

Let `R = 𝔽_ℓ⟦X⟧` sit inside an algebraically closed field `Λ`, and let `P_v` be a family of
monic polynomials over `R` with unit constant coefficients, indexed by a set `V` with degrees
`deg v`. Suppose that over `Λ` each `P_v` factors as a product of monic blocks `B_{j,v}` of
degree `d_j`, and that there are nonzero scalars `γ_j` such that the rescaled coefficients
`(B_{j,v})_{d_j - i} · γ_j^{i deg v}` are algebraic over the prime field. If some `w₀` has
positive degree, then for every `N` there is `M ≥ 1` such that the coefficients of `P_v` have no
terms in degrees `1, …, N - 1` as soon as `M` divides `deg v`.

The coefficients of the monic factors `B_{j,v}` are integral over `R`. At `w₀` the constant
coefficient of each block is a unit of the integral closure `O` of `R` in `Λ`, and multiplying it
by `γ_j^{d_j deg w₀}` gives an algebraic element; hence `γ_j` and `γ_j⁻¹` lie in `O`. Some power
`γ_j^M` is then congruent to `1` modulo `X^N O`, so for `M ∣ deg v` each block is congruent modulo
`X^N O` to its rescaling, which has algebraic coefficients. Multiplying the blocks, each
coefficient of `P_v` is congruent modulo `X^N O` to an algebraic element, and
`Stacks.TraceFormula.coeff_eq_zero_of_algebraMap_sub_eq_mul` concludes.

## Main results

* `Stacks.TraceFormula.coeff_coeff_eq_zero_of_eq_prod`: the theorem above.
-/

@[expose] public noncomputable section

open scoped Polynomial PowerSeries

namespace Stacks.TraceFormula

variable {ℓ : ℕ} [Fact ℓ.Prime] {Λ : Type*} [Field Λ] [Algebra (ZMod ℓ)⟦X⟧ Λ]

/-- If `b` and `b⁻¹` are integral over `𝔽_ℓ⟦X⟧` and `b γ^D` is algebraic over the prime field
for some `D > 0`, then `γ` and `γ⁻¹` are integral over `𝔽_ℓ⟦X⟧`. -/
public theorem isIntegral_and_isIntegral_inv_of_isAlgebraic_mul_pow
    (hι : Function.Injective (algebraMap (ZMod ℓ)⟦X⟧ Λ)) {b γ : Λ} {D : ℕ} (hD : 0 < D)
    (hb : IsIntegral (ZMod ℓ)⟦X⟧ b) (hb' : IsIntegral (ZMod ℓ)⟦X⟧ b⁻¹) (hb0 : b ≠ 0)
    (halg : IsAlgebraic (⊥ : Subfield Λ) (b * γ ^ D)) :
    IsIntegral (ZMod ℓ)⟦X⟧ γ ∧ IsIntegral (ZMod ℓ)⟦X⟧ γ⁻¹ := by
  have ha := isIntegral_of_isAlgebraic_bot hι halg
  have ha' := isIntegral_of_isAlgebraic_bot hι halg.inv
  refine ⟨IsIntegral.of_pow hD ?_, IsIntegral.of_pow hD ?_⟩
  · have : γ ^ D = b⁻¹ * (b * γ ^ D) := by rw [← mul_assoc, inv_mul_cancel₀ hb0, one_mul]
    rw [this]
    exact hb'.mul ha
  · have : γ⁻¹ ^ D = b * (b * γ ^ D)⁻¹ := by
      rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hb0, one_mul, inv_pow]
    rw [this]
    exact hb.mul ha'

/-- Let `P` be a polynomial over `𝔽_ℓ⟦X⟧` which factors over `Λ` as `∏ B_j`, where the `B_j` have
integral coefficients, and let `Q_j` be polynomials with coefficients integral over `𝔽_ℓ⟦X⟧`
and algebraic over the prime field, coefficientwise congruent to `B_j` modulo `X^N`. Then every
coefficient of `P` is congruent modulo `X^N` to an element algebraic over the prime field. -/
public theorem exists_isAlgebraic_sub_eq_mul {m N : ℕ} (P : (ZMod ℓ)⟦X⟧[X])
    (B Q : Fin m → Λ[X]) (hfac : P.map (algebraMap (ZMod ℓ)⟦X⟧ Λ) = ∏ j, B j)
    (hBint : ∀ j k, IsIntegral (ZMod ℓ)⟦X⟧ ((B j).coeff k))
    (hQint : ∀ j k, IsIntegral (ZMod ℓ)⟦X⟧ ((Q j).coeff k))
    (hQalg : ∀ j k, IsAlgebraic (⊥ : Subfield Λ) ((Q j).coeff k))
    (hcong : ∀ j k, ∃ z : Λ, IsIntegral (ZMod ℓ)⟦X⟧ z ∧
      (Q j).coeff k - (B j).coeff k = algebraMap (ZMod ℓ)⟦X⟧ Λ (PowerSeries.X ^ N) * z)
    (i : ℕ) :
    ∃ b z : Λ, IsAlgebraic (⊥ : Subfield Λ) b ∧ IsIntegral (ZMod ℓ)⟦X⟧ z ∧
      algebraMap (ZMod ℓ)⟦X⟧ Λ (P.coeff i) - b =
        algebraMap (ZMod ℓ)⟦X⟧ Λ (PowerSeries.X ^ N) * z := by
  let O := integralClosure (ZMod ℓ)⟦X⟧ Λ
  let I : Ideal O := Ideal.span {algebraMap (ZMod ℓ)⟦X⟧ O (PowerSeries.X ^ N)}
  have hlift : ∀ f : Λ[X], (∀ k, IsIntegral (ZMod ℓ)⟦X⟧ (f.coeff k)) →
      ∃ q : O[X], q.map (algebraMap O Λ) = f := fun f hf =>
    (Polynomial.mem_lifts f).1 ((Polynomial.lifts_iff_coeff_lifts f).2 fun k => ⟨⟨_, hf k⟩, rfl⟩)
  choose B' hB' using fun j => hlift (B j) (hBint j)
  choose Q' hQ' using fun j => hlift (Q j) (hQint j)
  have hcoe : ∀ (q : O[X]) k, ((q.coeff k : O) : Λ) = (q.map (algebraMap O Λ)).coeff k :=
    fun q k => by rw [Polynomial.coeff_map]; rfl
  have hP' : P.map (algebraMap (ZMod ℓ)⟦X⟧ O) = ∏ j, B' j := by
    apply Polynomial.map_injective (algebraMap O Λ) Subtype.val_injective
    rw [Polynomial.map_map, Polynomial.map_prod, ← IsScalarTower.algebraMap_eq]
    simp only [hB']
    exact hfac
  have hQB : ∀ j, (Q' j).map (Ideal.Quotient.mk I) = (B' j).map (Ideal.Quotient.mk I) := by
    intro j
    ext k
    rw [Polynomial.coeff_map, Polynomial.coeff_map, Ideal.Quotient.eq]
    obtain ⟨z, hz, hzeq⟩ := hcong j k
    refine Ideal.mem_span_singleton'.2 ⟨⟨z, hz⟩, Subtype.ext ?_⟩
    simp only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, Subalgebra.coe_algebraMap, hcoe,
      hQ', hB']
    rw [hzeq, mul_comm]
  have hmap : (P.map (algebraMap _ O)).map (Ideal.Quotient.mk I) =
      (∏ j, Q' j).map (Ideal.Quotient.mk I) := by
    rw [hP', Polynomial.map_prod, Polynomial.map_prod]
    simp only [hQB]
  have hi := congrArg (fun f => f.coeff i) hmap
  simp only [Polynomial.coeff_map] at hi
  rw [Ideal.Quotient.eq] at hi
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hi
  refine ⟨((∏ j, Q' j).coeff i : Λ), a, ?_, a.2, ?_⟩
  · rw [hcoe, Polynomial.map_prod]
    simp only [hQ']
    exact (Polynomial.isIntegral_coeff_prod _ _ (fun j _ k => (hQalg j k).isIntegral) i).isAlgebraic
  · have := congrArg (fun x : O => (x : Λ)) ha
    simp only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, Subalgebra.coe_algebraMap] at this
    rw [← this, mul_comm]

/-- **Integral congruences in characteristic `ℓ`.** Let `R = 𝔽_ℓ⟦X⟧` embed into an
algebraically closed field `Λ`, and let `P_v` (`v ∈ V`) be monic polynomials over `R` with unit
constant coefficients which factor over `Λ` as products `∏_j B_{j,v}` of monic polynomials of
degrees `d_j`. Let `γ_j ∈ Λ` be nonzero with `(B_{j,v})_{d_j - i} · γ_j^{i deg v}` algebraic over
the prime field for all `j`, `v` and `i ≤ d_j`, and let `deg w₀ > 0` for some `w₀`. Then for every
`N` there is `M ≥ 1` such that, whenever `M ∣ deg v`, every coefficient of `P_v` has vanishing
coefficients in degrees `1, …, N - 1`. -/
public theorem coeff_coeff_eq_zero_of_eq_prod {Λ : Type*} [Field Λ] [IsAlgClosed Λ]
    (ι : PowerSeries (ZMod ℓ) →+* Λ) (hι : Function.Injective ι)
    {V : Type*} (deg : V → ℕ) (P : V → Polynomial (PowerSeries (ZMod ℓ)))
    (hP : ∀ v, (P v).Monic) (hP0 : ∀ v, IsUnit ((P v).coeff 0))
    {m : ℕ} (d : Fin m → ℕ) (B : Fin m → V → Polynomial Λ)
    (hB : ∀ j v, (B j v).Monic) (hBd : ∀ j v, (B j v).natDegree = d j)
    (hfac : ∀ v, (P v).map ι = ∏ j, B j v)
    (γ : Fin m → Λ) (hγ : ∀ j, γ j ≠ 0)
    (halg : ∀ j v i, i ≤ d j →
      IsAlgebraic (⊥ : Subfield Λ) ((B j v).coeff (d j - i) * γ j ^ (i * deg v)))
    (w₀ : V) (hw₀ : 0 < deg w₀) (N : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ v, M ∣ deg v → ∀ i c, 1 ≤ c → c < N →
      PowerSeries.coeff c ((P v).coeff i) = 0 := by
  let : Algebra (ZMod ℓ)⟦X⟧ Λ := ι.toAlgebra
  have hι' : Function.Injective (algebraMap (ZMod ℓ)⟦X⟧ Λ) := hι
  have hfac' : ∀ v, (P v).map (algebraMap (ZMod ℓ)⟦X⟧ Λ) = ∏ j, B j v := hfac
  have hBint : ∀ j v k, IsIntegral (ZMod ℓ)⟦X⟧ ((B j v).coeff k) := fun j v k =>
    Polynomial.isIntegral_coeff_of_dvd (P v) (B j v) (hP v) (hB j v)
      (hfac' v ▸ Finset.dvd_prod_of_mem _ (Finset.mem_univ j)) k
  -- the constant coefficients of the blocks at `w₀` are units of the integral closure
  set b : Fin m → Λ := fun j => (B j w₀).coeff 0 with hb
  obtain ⟨u, hu⟩ := hP0 w₀
  have hprod : ∏ j, b j = algebraMap (ZMod ℓ)⟦X⟧ Λ u := by
    rw [hu, ← Polynomial.coeff_map, hfac' w₀, Polynomial.coeff_zero_prod]
  have hbinv : ∀ j, b j * ((∏ k ∈ Finset.univ.erase j, b k) *
      algebraMap (ZMod ℓ)⟦X⟧ Λ ↑u⁻¹) = 1 := by
    intro j
    rw [← mul_assoc, Finset.mul_prod_erase _ _ (Finset.mem_univ j), hprod, ← map_mul,
      Units.mul_inv, map_one]
  have hb0 : ∀ j, b j ≠ 0 := fun j => left_ne_zero_of_mul_eq_one (hbinv j)
  have hbI : ∀ j, IsIntegral (ZMod ℓ)⟦X⟧ (b j) := fun j => hBint j w₀ 0
  have hbI' : ∀ j, IsIntegral (ZMod ℓ)⟦X⟧ (b j)⁻¹ := fun j => by
    rw [inv_eq_of_mul_eq_one_right (hbinv j)]
    exact (IsIntegral.prod _ fun k _ => hbI k).mul isIntegral_algebraMap
  -- hence `γ_j` and `γ_j⁻¹` are integral when `d_j > 0`
  have hγI : ∀ j, 0 < d j → IsIntegral (ZMod ℓ)⟦X⟧ (γ j) ∧ IsIntegral (ZMod ℓ)⟦X⟧ (γ j)⁻¹ := by
    intro j hj
    refine isIntegral_and_isIntegral_inv_of_isAlgebraic_mul_pow hι' (Nat.mul_pos hj hw₀)
      (hbI j) (hbI' j) (hb0 j) ?_
    simpa [hb] using halg j w₀ (d j) le_rfl
  -- powers of `γ_j` congruent to `1` modulo `X^N`
  have hM : ∀ j, ∃ M : ℕ, 0 < M ∧ ∀ n, M ∣ n → ∀ i ≤ d j, ∃ z : Λ,
      IsIntegral (ZMod ℓ)⟦X⟧ z ∧
        γ j ^ (i * n) - 1 = algebraMap (ZMod ℓ)⟦X⟧ Λ (PowerSeries.X ^ N) * z := by
    intro j
    rcases Nat.eq_zero_or_pos (d j) with h0 | hpos
    · refine ⟨1, one_pos, fun n _ i hi => ⟨0, isIntegral_zero, ?_⟩⟩
      obtain rfl : i = 0 := by omega
      simp
    · obtain ⟨M, hM0, hM⟩ :=
        exists_forall_dvd_pow_sub_one_eq_mul hι' (hγ j) (hγI j hpos).1 (hγI j hpos).2 N
      exact ⟨M, hM0, fun n hn i _ => hM _ (hn.mul_left i)⟩
  choose Mj hMj0 hMj using hM
  refine ⟨∏ j, Mj j, Finset.prod_pos fun j _ => hMj0 j, ?_⟩
  intro v hv i c hc1 hcN
  have hMv : ∀ j, Mj j ∣ deg v := fun j =>
    (Finset.dvd_prod_of_mem Mj (Finset.mem_univ j)).trans hv
  -- the rescaled blocks, with algebraic coefficients
  let Q : Fin m → Λ[X] := fun j => ∑ k ∈ Finset.range (d j + 1),
    Polynomial.monomial k ((B j v).coeff k * γ j ^ ((d j - k) * deg v))
  have hzero : ∀ j k, ¬ k ≤ d j → (B j v).coeff k = 0 := fun j k hk =>
    Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hBd]; omega)
  have hQ : ∀ j k, (Q j).coeff k = (B j v).coeff k * γ j ^ ((d j - k) * deg v) := by
    intro j k
    simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq',
      Finset.mem_range]
    split_ifs with hk
    · rfl
    · rw [hzero j k (by omega), zero_mul]
  have hpowI : ∀ j k, IsIntegral (ZMod ℓ)⟦X⟧ (γ j ^ ((d j - k) * deg v)) := by
    intro j k
    rcases Nat.eq_zero_or_pos (d j) with h0 | hpos
    · simp [h0, isIntegral_one]
    · exact (hγI j hpos).1.pow _
  obtain ⟨b', z, hb', hz, h⟩ := exists_isAlgebraic_sub_eq_mul (N := N) (P v) (fun j => B j v) Q
    (hfac' v) (fun j k => hBint j v k)
    (fun j k => by rw [hQ]; exact (hBint j v k).mul (hpowI j k))
    (fun j k => by
      rw [hQ]
      by_cases hk : k ≤ d j
      · have := halg j v (d j - k) (Nat.sub_le _ _)
        rwa [Nat.sub_sub_self hk] at this
      · rw [hzero j k hk, zero_mul]
        exact isAlgebraic_zero)
    (fun j k => by
      by_cases hk : k ≤ d j
      · obtain ⟨z, hz, hzeq⟩ := hMj j (deg v) (hMv j) (d j - k) (Nat.sub_le _ _)
        refine ⟨(B j v).coeff k * z, (hBint j v k).mul hz, ?_⟩
        rw [hQ]
        linear_combination (B j v).coeff k * hzeq
      · refine ⟨0, isIntegral_zero, ?_⟩
        simp only [hQ, hzero j k hk, zero_mul, sub_zero, mul_zero])
    i
  exact coeff_eq_zero_of_algebraMap_sub_eq_mul hι' hb' hz h hc1 hcN

end Stacks.TraceFormula
