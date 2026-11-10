module

public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.FieldTheory.Perfect
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.CharP.Algebra

/-!
# Independence of Frobenius powers over a space of small vanishing order

Let `K` be a perfect field of characteristic `p`, let `σ = p ^ a`, and let `U ⊆ K⟦X⟧` be a
finite-dimensional subspace all of whose nonzero elements have order `< σ`. If
`y₁, …, yₙ ∈ K⟦X⟧` are linearly independent over `K`, then

  `u₁ y₁ ^ σ + ⋯ + uₙ yₙ ^ σ = 0` with `uᵢ ∈ U` forces `u₁ = ⋯ = uₙ = 0`.

This is the independence lemma at the heart of Bombieri's version of Stepanov's method: choosing
a basis of `U` with distinct orders, the terms of the sum have orders in distinct residue classes
modulo `σ`, so they cannot cancel. We prove it by induction on `dim U`, splitting off an element
of minimal order and keeping track of the residue modulo `σ` of the order of a nonzero sum.

## Main results

* `PowerSeries.eq_zero_of_sum_mul_pow_eq_zero`: the independence lemma.
-/

@[expose] public section

namespace PowerSeries

variable {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectRing K p]

private lemma eq_of_add_mul_eq {σ o₁ o₂ t₁ t₂ : ℕ} (h₁ : o₁ < σ) (h₂ : o₂ < σ)
    (h : o₁ + σ * t₁ = o₂ + σ * t₂) : o₁ = o₂ := by
  have := congrArg (· % σ) h
  simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂] using this

private lemma aux (a : ℕ) {ι : Type*} [Fintype ι] {y : ι → K⟦X⟧} (hy : LinearIndependent K y) :
    ∀ (n : ℕ) (U : Submodule K K⟦X⟧) [FiniteDimensional K U], Module.finrank K U = n →
      (∀ u ∈ U, u ≠ 0 → u.order < (p ^ a : ℕ)) →
      ∀ u : ι → K⟦X⟧, (∀ i, u i ∈ U) →
        ((∑ i, u i * y i ^ p ^ a = 0) → ∀ i, u i = 0) ∧
        (∑ i, u i * y i ^ p ^ a ≠ 0 → ∃ v ∈ U, v ≠ 0 ∧
          ∃ N : ℕ, (∑ i, u i * y i ^ p ^ a).order = (v.order.toNat + p ^ a * N : ℕ)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro U _ hn hU u hu
  set σ := p ^ a
  by_cases hbot : U = ⊥
  · have h0 : ∀ i, u i = 0 := fun i => by simpa [hbot] using hu i
    simp [h0]
  -- an element `e` of `U` of minimal order `o₀`
  have hex : ∃ o : ℕ, ∃ u ∈ U, u ≠ 0 ∧ u.order = o := by
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    exact ⟨v.order.toNat, v, hv, hv0, (ENat.natCast_toNat (order_eq_top.not.mpr hv0)).symm⟩
  classical
  set o₀ := Nat.find hex
  obtain ⟨e, he, he0, heo⟩ := Nat.find_spec hex
  have hmin : ∀ v ∈ U, v ≠ 0 → (o₀ : ℕ∞) ≤ v.order := by
    intro v hv hv0
    have hfin : v.order ≠ ⊤ := order_eq_top.not.mpr hv0
    rw [← ENat.natCast_toNat hfin]
    exact_mod_cast Nat.find_min' hex ⟨v, hv, hv0, (ENat.natCast_toNat hfin).symm⟩
  have hγ : coeff o₀ e ≠ 0 := by
    have := coeff_order he0
    rwa [heo, ENat.toNat_natCast] at this
  -- the subspace `U'` of elements of `U` whose coefficient of index `o₀` vanishes
  set U' : Submodule K K⟦X⟧ := U ⊓ LinearMap.ker (coeff o₀)
  have hU'le : U' ≤ U := inf_le_left
  have hU'lt : U' < U := lt_of_le_of_ne hU'le fun h => by
    have : e ∈ U' := h ▸ he
    exact hγ (LinearMap.mem_ker.mp (Submodule.mem_inf.mp this).2)
  have : FiniteDimensional K U' := Submodule.finiteDimensional_of_le hU'le
  have hrank : Module.finrank K U' < n := hn ▸ Submodule.finrank_lt_finrank_of_lt hU'lt
  have hU' : ∀ v ∈ U', v ≠ 0 → v.order < (σ : ℕ) := fun v hv hv0 => hU v (hU'le hv) hv0
  have hU'o : ∀ v ∈ U', v ≠ 0 → (o₀ : ℕ∞) < v.order := by
    intro v hv hv0
    refine lt_of_le_of_ne (hmin v (hU'le hv) hv0) fun h => ?_
    have hc := coeff_order hv0
    rw [← h, ENat.toNat_natCast] at hc
    exact hc (LinearMap.mem_ker.mp (Submodule.mem_inf.mp hv).2)
  -- decompose `u i = c i • e + u' i`
  set c : ι → K := fun i => coeff o₀ (u i) / coeff o₀ e
  set u' : ι → K⟦X⟧ := fun i => u i - c i • e
  have hu' : ∀ i, u' i ∈ U' := by
    intro i
    refine Submodule.mem_inf.mpr ⟨U.sub_mem (hu i) (U.smul_mem _ he), ?_⟩
    simp [u', c, LinearMap.mem_ker, div_mul_cancel₀ _ hγ]
  obtain ⟨ih1, ih2⟩ := ih _ hrank U' rfl hU' u' hu'
  have : CharP K⟦X⟧ p := charP_of_injective_algebraMap (algebraMap K K⟦X⟧).injective p
  set fr := iterateFrobeniusEquiv K p a
  set z : K⟦X⟧ := ∑ i, fr.symm (c i) • y i
  have hzpow : z ^ σ = ∑ i, c i • y i ^ σ := by
    rw [sum_pow_char_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_pow]
    congr 1
    have := fr.apply_symm_apply (c i)
    rwa [iterateFrobeniusEquiv_def] at this
  have hsplit : ∑ i, u i * y i ^ σ = e * z ^ σ + ∑ i, u' i * y i ^ σ := by
    rw [hzpow, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [u', sub_mul, smul_mul_assoc, mul_smul_comm]
    abel
  by_cases hz : z = 0
  · -- all `c i` vanish, so `u = u'`
    have hc0 : ∀ i, c i = 0 := by
      intro i
      have := (Fintype.linearIndependent_iff.mp hy) (fun i => fr.symm (c i)) hz i
      simpa using this
    have huu : ∀ i, u' i = u i := fun i => by simp [u', hc0 i]
    simp only [huu] at ih1 ih2
    refine ⟨ih1, fun hne => ?_⟩
    obtain ⟨v, hv, hv0, N, hN⟩ := ih2 hne
    exact ⟨v, hU'le hv, hv0, N, hN⟩
  · -- the term `e * z ^ σ` has order `o₀ + σ * ord z`
    have hzfin : z.order ≠ ⊤ := order_eq_top.not.mpr hz
    set t := z.order.toNat
    have hA : (e * z ^ σ).order = (o₀ + σ * t : ℕ) := by
      rw [order_mul, order_pow, heo, ← ENat.natCast_toNat hzfin, nsmul_eq_mul]
      push_cast; ring
    have key : ∃ v ∈ U, v ≠ 0 ∧ ∃ N : ℕ,
        (∑ i, u i * y i ^ σ).order = (v.order.toNat + σ * N : ℕ) := by
      rw [hsplit]
      have heord : e.order.toNat = o₀ := by rw [heo, ENat.toNat_natCast]
      by_cases hB : ∑ i, u' i * y i ^ σ = 0
      · exact ⟨e, he, he0, t, by rw [hB, add_zero, hA, heord]⟩
      · obtain ⟨v, hv, hv0, N, hN⟩ := ih2 hB
        have hvfin : v.order ≠ ⊤ := order_eq_top.not.mpr hv0
        have hvlt : v.order.toNat < σ := by
          have := hU' v hv hv0
          rw [← ENat.natCast_toNat hvfin] at this
          exact_mod_cast this
        have hvgt : o₀ < v.order.toNat := by
          have := hU'o v hv hv0
          rw [← ENat.natCast_toNat hvfin] at this
          exact_mod_cast this
        have ho₀σ : o₀ < σ := hvgt.trans hvlt
        have hne : (e * z ^ σ).order ≠ (∑ i, u' i * y i ^ σ).order := by
          rw [hA, hN]
          intro h
          have := eq_of_add_mul_eq ho₀σ hvlt (by exact_mod_cast h)
          omega
        rw [order_add_of_order_ne _ _ hne]
        rcases le_total (e * z ^ σ).order (∑ i, u' i * y i ^ σ).order with hle | hle
        · exact ⟨e, he, he0, t, by rw [min_eq_left hle, hA, heord]⟩
        · exact ⟨v, hU'le hv, hv0, N, by rw [min_eq_right hle, hN]⟩
    refine ⟨fun h0 => ?_, fun _ => key⟩
    obtain ⟨v, -, -, N, hN⟩ := key
    rw [h0, order_zero] at hN
    exact absurd hN (ENat.top_ne_natCast _)

/-- **Independence of Frobenius powers.** Let `K` be a perfect field of characteristic `p`, let
`U ⊆ K⟦X⟧` be a finite-dimensional subspace whose nonzero elements have order `< p ^ a`, and let
`y : ι → K⟦X⟧` be linearly independent over `K`. If `∑ uᵢ yᵢ ^ (p ^ a) = 0` with all `uᵢ ∈ U`,
then every `uᵢ` vanishes. -/
theorem eq_zero_of_sum_mul_pow_eq_zero (a : ℕ) (U : Submodule K K⟦X⟧) [FiniteDimensional K U]
    (hU : ∀ u ∈ U, u ≠ 0 → u.order < (p ^ a : ℕ)) {ι : Type*} [Fintype ι] {y : ι → K⟦X⟧}
    (hy : LinearIndependent K y) {u : ι → K⟦X⟧} (hu : ∀ i, u i ∈ U)
    (h : ∑ i, u i * y i ^ p ^ a = 0) (i : ι) : u i = 0 :=
  (aux p a hy _ U rfl hU u hu).1 h i

end PowerSeries
