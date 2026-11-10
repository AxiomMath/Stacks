module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Polynomials over `ℚ_ℓ` are determined by the norms of their resultants

Let `ℓ ≠ p` be primes and `χ`, `P` monic polynomials of the same degree over `ℚ_ℓ`. If
`‖Res(P, R)‖ = ‖Res(χ, R)‖` for every `R ∈ ℤ[X]` with `p ∤ R(0)` (and `Res(χ, R) ≠ 0`), then
`P = χ` (`Stacks.Polynomial.eq_of_norm_resultant_intPoly_eq`). This is the lemma behind
[Mumford, *Abelian varieties*, §19, Theorem 4]: for an endomorphism `F` of an abelian variety,
`|det R(T_ℓ F)|_ℓ = |deg R(F)|_ℓ`, so the characteristic polynomial of `F` on the Tate module is
the polynomial `χ_F` with `deg R(F) = Res(χ_F, R)`. The restriction `p ∤ R(0)` is what makes
`R(F)` separable when `F` is a Frobenius.

The proof needs no roots. By continuity of the resultant in the coefficients, and integer
approximation with constant term prime to `p`, the hypothesis extends to all `R ∈ ℤ_ℓ[X]`
(`Stacks.Polynomial.norm_resultant_eq_of_intPoly`). For a monic irreducible factor `Q` of `χ` and
`S = ℓ^k Q` integral, `Res(χ, S + ℓ^s) = ℓ^{s deg Q} Res(χ / Q, S + ℓ^s) → 0`, while
`Res(P, S + ℓ^s) → Res(P, S)`, which is nonzero unless `Q ∣ P`; so `Q ∣ P`, and `Q` cancels
(`Stacks.Polynomial.eq_of_norm_resultant_eq`).

## Main results

* `Stacks.Polynomial.eq_of_norm_resultant_eq`: the statement for `R` integral over `ℤ_ℓ`.
* `Stacks.Polynomial.eq_of_norm_resultant_intPoly_eq`: the statement for `R ∈ ℤ[X]`, `p ∤ R(0)`.
-/

@[expose] public noncomputable section

open Polynomial Filter Topology

namespace Stacks.Polynomial

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- Mapping along `f` and then along a retraction `g` of `f` is the identity. -/
private theorem map_map_eq_self_of_leftInverse {A B : Type*} [Semiring A] [Semiring B]
    (f : A →+* B) (g : B →+* A) (h : ∀ a, g (f a) = a) (F : A[X]) : (F.map f).map g = F := by
  rw [Polynomial.map_map, show g.comp f = RingHom.id A from RingHom.ext h, Polynomial.map_id]

/-- The resultant `Res(F, S + c)` is a polynomial function of `c`. -/
theorem exists_eval_eq_resultant_add_C {K : Type*} [Field K] (F S : K[X]) (m n : ℕ) :
    ∃ Q : K[X], ∀ c : K, Q.eval c = F.resultant (S + C c) m n := by
  refine ⟨(F.map C).resultant (S.map C + C X) m n, fun c => ?_⟩
  rw [← coe_evalRingHom, ← resultant_map_map]
  congr 1
  · exact map_map_eq_self_of_leftInverse _ _ (fun a => by simp) F
  · rw [Polynomial.map_add, map_C]
    congr 1
    · exact map_map_eq_self_of_leftInverse _ _ (fun a => by simp) S
    · simp

/-- `ℓ ^ s → 0` in `ℚ_ℓ` as `s → ∞`. -/
private theorem tendsto_pow_prime_atTop_nhds_zero :
    Tendsto (fun s : ℕ => (ℓ : ℚ_[ℓ]) ^ s) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one

/-- `Res(F, S + ℓ^s) → Res(F, S)` as `s → ∞`, in `ℚ_ℓ`. -/
theorem tendsto_resultant_add_C_pow (F S : ℚ_[ℓ][X]) (m n : ℕ) :
    Tendsto (fun s : ℕ => F.resultant (S + C ((ℓ : ℚ_[ℓ]) ^ s)) m n) atTop
      (𝓝 (F.resultant S m n)) := by
  obtain ⟨Q, hQ⟩ := exists_eval_eq_resultant_add_C F S m n
  have := (Q.continuous.tendsto 0).comp tendsto_pow_prime_atTop_nhds_zero
  simp only [Function.comp_def, hQ] at this
  rwa [C_0, add_zero] at this

/-- For `T ≠ 0`, `Res(T, S + c) = 0` for only finitely many `c`: an irreducible factor of `T`
divides `S + c` for at most one `c`. -/
theorem finite_setOf_resultant_add_C_eq_zero {K : Type*} [Field K] (T S : K[X])
    (hT : T ≠ 0) : {c : K | T.resultant (S + C c) = 0}.Finite := by
  classical
  have key : ∀ c : {c : K | T.resultant (S + C c) = 0},
      ∃ q ∈ (UniqueFactorizationMonoid.normalizedFactors T).toFinset, q ∣ S + C (c : K) := by
    rintro ⟨c, hc⟩
    have hnc := ((resultant_eq_zero_iff).1 hc).2
    by_contra hno
    push Not at hno
    refine hnc (isCoprime_of_irreducible_dvd (fun h => hT h.1) fun z hz hzT hzS => ?_)
    obtain ⟨q, hq, hzq⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hT hz hzT
    exact hno q (Multiset.mem_toFinset.2 hq) (hzq.symm.dvd.trans hzS)
  choose g hg hgd using key
  have hinj : Function.Injective g := by
    rintro ⟨c, hc⟩ ⟨c', hc'⟩ h
    by_contra hne
    have hne' : c - c' ≠ 0 := sub_ne_zero.2 fun e => hne (Subtype.ext e)
    have hd := dvd_sub (hgd ⟨c, hc⟩) (h ▸ hgd ⟨c', hc'⟩)
    rw [add_sub_add_left_eq_sub, ← C_sub] at hd
    have hirr := UniqueFactorizationMonoid.irreducible_of_normalized_factor _
      (Multiset.mem_toFinset.1 (hg ⟨c, hc⟩))
    exact hirr.not_isUnit (isUnit_of_dvd_unit hd (isUnit_C.2 (Ne.isUnit hne')))
  exact Set.finite_coe_iff.1 (Finite.of_injective
    (β := (UniqueFactorizationMonoid.normalizedFactors T).toFinset)
    (fun c => ⟨g c, hg c⟩) fun a b h => hinj (congrArg Subtype.val h))

/-- For `T ≠ 0`, `Res(T, S + ℓ^s) ≠ 0` for all large `s`, in `ℚ_ℓ`. -/
theorem eventually_resultant_add_C_pow_ne_zero (T S : ℚ_[ℓ][X]) (hT : T ≠ 0) :
    ∀ᶠ s : ℕ in atTop, T.resultant (S + C ((ℓ : ℚ_[ℓ]) ^ s)) ≠ 0 := by
  classical
  have hfin := (finite_setOf_resultant_add_C_eq_zero T S hT).preimage
    (f := fun s : ℕ => (ℓ : ℚ_[ℓ]) ^ s) fun a _ b _ h =>
      Nat.pow_right_injective hℓ.out.two_le (Nat.cast_injective (by exact_mod_cast h))
  rw [← Nat.cofinite_eq_atTop]
  exact hfin.eventually_cofinite_notMem

/-- `Res(Q, a Q + c) = c ^ d` for `Q` monic of degree `d`. -/
theorem resultant_C_mul_add_C {K : Type*} [Field K] (Q : K[X]) (hQ : Q.Monic) (a c : K) :
    Q.resultant (C a * Q + C c) Q.natDegree Q.natDegree = c ^ Q.natDegree := by
  rw [resultant_comm, show C a * Q + C c = C c + Q * C a by ring,
    resultant_add_mul_left _ _ _ _ _ (by simp) le_rfl, resultant_C_left, hQ.coeff_natDegree,
    one_pow, mul_one, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

/-- `Res(F G, S) = Res(F, S) Res(G, S)` for nonzero `F`, `G`, with the default degrees. -/
theorem resultant_mul_left' {K : Type*} [Field K] (F G S : K[X]) (hF : F ≠ 0) (hG : G ≠ 0) :
    (F * G).resultant S = F.resultant S * G.resultant S := by
  rw [natDegree_mul hF hG, resultant_mul_left _ _ _ _ le_rfl]

/-- Every polynomial over `ℚ_ℓ` becomes integral after multiplication by a power of `ℓ`. -/
theorem exists_norm_pow_mul_coeff_le_one (Q : ℚ_[ℓ][X]) :
    ∃ k : ℕ, ∀ j, ‖(ℓ : ℚ_[ℓ]) ^ k * Q.coeff j‖ ≤ 1 := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (∑ j ∈ Finset.range (Q.natDegree + 1), ‖Q.coeff j‖)
    (by exact_mod_cast hℓ.out.one_lt : (1 : ℝ) < ℓ)
  refine ⟨k, fun j => ?_⟩
  have hpos : (0 : ℝ) < (ℓ : ℝ) ^ k := pow_pos (by exact_mod_cast hℓ.out.pos) k
  rw [norm_mul, norm_pow, Padic.norm_p, inv_pow, ← div_eq_inv_mul, div_le_one hpos]
  by_cases hj : j ≤ Q.natDegree
  · refine le_trans ?_ hk.le
    exact Finset.single_le_sum (f := fun j => ‖Q.coeff j‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hj), norm_zero]
    exact hpos.le

/-- If `‖Res(P, S)‖ = ‖Res(χ, S)‖` for every integral `S` with `Res(D χ, S) ≠ 0`, then every
monic irreducible factor `Q` of the monic `χ` divides `P`. -/
theorem dvd_of_norm_resultant_eq (χ P D Q : ℚ_[ℓ][X]) (hχ : χ.Monic) (hD : D ≠ 0)
    (hQm : Q.Monic) (hQi : Irreducible Q) (hQχ : Q ∣ χ)
    (H : ∀ S : ℚ_[ℓ][X], (∀ k, ‖S.coeff k‖ ≤ 1) → (D * χ).resultant S ≠ 0 →
      ‖P.resultant S‖ = ‖χ.resultant S‖) : Q ∣ P := by
  obtain ⟨χ', rfl⟩ := hQχ
  have hnχ : (Q * χ').natDegree = Q.natDegree + χ'.natDegree :=
    hQm.natDegree_mul (hQm.of_mul_monic_left hχ)
  by_contra hQP
  obtain ⟨k, hk⟩ := exists_norm_pow_mul_coeff_le_one Q
  set S := C ((ℓ : ℚ_[ℓ]) ^ k) * Q with hS
  have hℓ0 : (ℓ : ℚ_[ℓ]) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hℓ.out.ne_zero)
  have hSdeg : S.natDegree = Q.natDegree := natDegree_C_mul hℓ0
  have hSs : ∀ s : ℕ, (S + C ((ℓ : ℚ_[ℓ]) ^ s)).natDegree = Q.natDegree := fun s => by
    rw [natDegree_add_C, hSdeg]
  have hint : ∀ s : ℕ, ∀ j, ‖(S + C ((ℓ : ℚ_[ℓ]) ^ s)).coeff j‖ ≤ 1 := fun s j => by
    rw [coeff_add, coeff_C, hS, coeff_C_mul]
    refine (Padic.nonarchimedean _ _).trans (max_le (hk j) ?_)
    split_ifs
    · rw [norm_pow, Padic.norm_p]
      exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast hℓ.out.one_le))
    · simp
  have hcop : IsCoprime P S := by
    have h1 : IsCoprime Q P := (hQi.coprime_iff_not_dvd).2 hQP
    have h2 : IsCoprime P (C ((ℓ : ℚ_[ℓ]) ^ k)) :=
      ⟨0, C ((ℓ : ℚ_[ℓ]) ^ k)⁻¹, by rw [zero_mul, zero_add, ← C_mul, inv_mul_cancel₀ hℓ0, C_1]⟩
    exact h2.mul_right h1.symm
  have hR : Tendsto (fun s : ℕ => (Q * χ').resultant (S + C ((ℓ : ℚ_[ℓ]) ^ s))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℕ => ((ℓ : ℚ_[ℓ]) ^ s) ^ Q.natDegree) atTop (𝓝 0) := by
      have := (tendsto_pow_prime_atTop_nhds_zero (ℓ := ℓ)).pow Q.natDegree
      rwa [zero_pow hQi.natDegree_pos.ne'] at this
    have := h1.mul (tendsto_resultant_add_C_pow χ' S χ'.natDegree Q.natDegree)
    rw [zero_mul] at this
    refine this.congr fun s => ?_
    rw [hnχ, hSs, resultant_mul_left _ _ _ _ (hSs s).le, hS, resultant_C_mul_add_C Q hQm]
  have hev := (eventually_resultant_add_C_pow_ne_zero (D * (Q * χ')) S
    (mul_ne_zero hD hχ.ne_zero)).mono fun s hs => H _ (hint s) hs
  have hlim : Tendsto (fun s : ℕ => ‖P.resultant (S + C ((ℓ : ℚ_[ℓ]) ^ s))‖) atTop (𝓝 0) := by
    refine (hR.norm.congr' (hev.mono fun s hs => hs.symm)).trans ?_
    simp
  have hL' : Tendsto (fun s : ℕ => ‖P.resultant (S + C ((ℓ : ℚ_[ℓ]) ^ s))‖) atTop
      (𝓝 ‖P.resultant S‖) := by
    rw [hSdeg]
    exact (tendsto_resultant_add_C_pow P S P.natDegree Q.natDegree).norm.congr fun s => by
      rw [hSs]
  exact resultant_ne_zero P S hcop (norm_eq_zero.1 (tendsto_nhds_unique hL' hlim))

/-- **Polynomials over `ℚ_ℓ` with the same resultant norms are equal.** Let `χ` and `P` be
monic of the same degree over `ℚ_ℓ` and `D ≠ 0`. If `‖Res(P, S)‖ = ‖Res(χ, S)‖` for every `S`
with integral coefficients and `Res(D χ, S) ≠ 0`, then `P = χ`. For a monic irreducible
factor `Q` of `χ` and `S = ℓ^k Q` integral, `Res(χ, S + ℓ^s) → 0` while `Res(P, S + ℓ^s)` tends
to `Res(P, S) ≠ 0` unless `Q ∣ P`; then `Q` cancels. -/
theorem eq_of_norm_resultant_eq (χ P D : ℚ_[ℓ][X]) (hχ : χ.Monic) (hP : P.Monic)
    (hdeg : P.natDegree = χ.natDegree) (hD : D ≠ 0)
    (H : ∀ S : ℚ_[ℓ][X], (∀ k, ‖S.coeff k‖ ≤ 1) → (D * χ).resultant S ≠ 0 →
      ‖P.resultant S‖ = ‖χ.resultant S‖) : P = χ := by
  induction hn : χ.natDegree using Nat.strong_induction_on generalizing χ P D with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [eq_one_of_monic_natDegree_zero hχ hn, eq_one_of_monic_natDegree_zero hP (hdeg.trans hn)]
  obtain ⟨Q, hQm, hQi, hQχ⟩ := exists_monic_irreducible_factor χ
    (fun hu => by rw [natDegree_eq_zero_of_isUnit hu] at hn; omega)
  have hQP := dvd_of_norm_resultant_eq χ P D Q hχ hD hQm hQi hQχ H
  obtain ⟨χ', rfl⟩ := hQχ
  have hχ' : χ'.Monic := hQm.of_mul_monic_left hχ
  have hdQ : 0 < Q.natDegree := hQi.natDegree_pos
  have hnχ : (Q * χ').natDegree = Q.natDegree + χ'.natDegree := hQm.natDegree_mul hχ'
  obtain ⟨P', rfl⟩ := hQP
  have hP' : P'.Monic := hQm.of_mul_monic_left hP
  have hnP : (Q * P').natDegree = Q.natDegree + P'.natDegree := hQm.natDegree_mul hP'
  have hdeg' : P'.natDegree = χ'.natDegree := by omega
  rw [ih χ'.natDegree (by omega) χ' P' (D * Q) hχ' hP' hdeg' (mul_ne_zero hD hQm.ne_zero)
    (fun S hS hres => ?_) rfl]
  have hres' : (D * (Q * χ')).resultant S ≠ 0 := by rwa [← mul_assoc]
  have h := H S hS hres'
  rw [resultant_mul_left' _ _ _ hQm.ne_zero hP'.ne_zero,
    resultant_mul_left' _ _ _ hQm.ne_zero hχ'.ne_zero, norm_mul, norm_mul] at h
  have hQS : Q.resultant S ≠ 0 := by
    intro h0
    apply hres'
    rw [resultant_mul_left' _ _ _ hD (mul_ne_zero hQm.ne_zero hχ'.ne_zero),
      resultant_mul_left' _ _ _ hQm.ne_zero hχ'.ne_zero, h0, zero_mul, mul_zero]
  exact mul_left_cancel₀ (norm_ne_zero_iff.2 hQS) h

/-- **Integer approximation with a constant term prime to `p`.** For `S ∈ ℤ_ℓ[X]` of degree `d`,
a prime `p ≠ ℓ` and `N`, there is `R ∈ ℤ[X]` of degree `d` with `p ∤ R(0)` and `R ≡ S mod ℓ^N`. -/
theorem exists_intPoly_map_toZModPow_eq (p : ℕ) (hp : p.Prime) (hpℓ : p ≠ ℓ) (S : ℤ_[ℓ][X])
    (N : ℕ) : ∃ R : ℤ[X], R.natDegree = S.natDegree ∧ ¬ (p : ℤ) ∣ R.coeff 0 ∧
      (R.map (Int.castRingHom ℤ_[ℓ])).map (PadicInt.toZModPow N) =
        S.map (PadicInt.toZModPow N) := by
  classical
  set d := S.natDegree
  let a : ℕ → ℤ := fun k => ((PadicInt.toZModPow N (S.coeff k)).val : ℤ)
  have hℓN : ¬ (p : ℤ) ∣ (ℓ : ℤ) ^ N := by
    intro h
    have h' : p ∣ ℓ ^ N := by exact_mod_cast h
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ.out).1 (hp.dvd_of_dvd_pow h'))
  let e : ℕ → ℤ := fun k =>
    if k = 0 then (if (p : ℤ) ∣ a 0 then 1 else 0) else if k = d ∧ a d = 0 then 1 else 0
  let b : ℕ → ℤ := fun k => a k + (ℓ : ℤ) ^ N * e k
  have hb : ∀ k, ((b k : ℤ) : ZMod (ℓ ^ N)) = ((a k : ℤ) : ZMod (ℓ ^ N)) := fun k => by
    have hz : (((ℓ : ℤ) ^ N : ℤ) : ZMod (ℓ ^ N)) = 0 := by
      push_cast
      exact_mod_cast ZMod.natCast_self (ℓ ^ N)
    simp only [b, Int.cast_add, Int.cast_mul, hz, zero_mul, add_zero]
  have hb0 : ¬ (p : ℤ) ∣ b 0 := by
    by_cases h : (p : ℤ) ∣ a 0
    · intro h'
      simp only [b, e, ite_true, ite_eq_left h, mul_one] at h'
      exact hℓN ((Int.dvd_add_right h).1 h')
    · simp [b, e, h]
  have hbd : b d ≠ 0 := by
    by_cases hd : d = 0
    · intro h0
      apply hb0
      rw [← hd, h0]
      exact dvd_zero _
    · by_cases h : a d = 0
      · simp only [b, e, ite_eq_right hd, h, and_self, ite_true, mul_one, zero_add]
        exact pow_ne_zero _ (by exact_mod_cast hℓ.out.ne_zero)
      · simp [b, e, hd, h]
  let R : ℤ[X] := ∑ k ∈ Finset.range (d + 1), monomial k (b k)
  have hRc : ∀ j, R.coeff j = if j ≤ d then b j else 0 := fun j => by
    simp only [R, finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq', Finset.mem_range,
      Nat.lt_succ_iff]
  have hRdeg : R.natDegree = d := by
    refine le_antisymm (natDegree_le_iff_coeff_eq_zero.2 fun j hj => ?_) ?_
    · rw [hRc, ite_eq_right (not_le.2 hj)]
    · exact le_natDegree_of_ne_zero (by rwa [hRc, ite_eq_left le_rfl])
  refine ⟨R, hRdeg, by rwa [hRc, ite_eq_left (Nat.zero_le _)], ?_⟩
  ext j
  rw [coeff_map, coeff_map, coeff_map, hRc]
  split_ifs with hj
  · rw [eq_intCast, map_intCast, hb]
    simp [a]
  · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hj)]
    simp

/-- The resultant `Res(F, ∑_{k ≤ n} c_k X^k)` is a continuous function of `c`. -/
theorem continuous_resultant_sum_C_mul_X_pow {K : Type*} [Field K] [TopologicalSpace K]
    [IsTopologicalRing K] (F : K[X]) (m n : ℕ) :
    Continuous fun c : Fin (n + 1) → K =>
      F.resultant (∑ k : Fin (n + 1), C (c k) * X ^ (k : ℕ)) m n := by
  refine (MvPolynomial.continuous_eval ((F.map MvPolynomial.C).resultant
    (∑ k : Fin (n + 1), C (MvPolynomial.X k) * X ^ (k : ℕ)) m n)).congr fun c => ?_
  rw [← resultant_map_map]
  congr 1
  · exact map_map_eq_self_of_leftInverse _ _ (fun a => by simp) F
  · simp [Polynomial.map_sum]

/-- `∑_{k ≤ n} R_k X^k = R` for `deg R ≤ n`. -/
theorem sum_fin_C_coeff_mul_X_pow {R : Type*} [Semiring R] (S : R[X]) {n : ℕ}
    (hS : S.natDegree ≤ n) : ∑ k : Fin (n + 1), C (S.coeff k) * X ^ (k : ℕ) = S := by
  conv_rhs => rw [S.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hS)]
  exact Fin.sum_univ_eq_sum_range (fun k => C (S.coeff k) * X ^ k) (n + 1)

/-- **Passage from integer polynomials to `ℤ_ℓ`-polynomials.** For polynomials `P`, `T` over
`ℚ_ℓ`, a prime `p ≠ ℓ` and `Q ≠ 0`: if `‖Res(P, R)‖ = ‖Res(T, R)‖` for every `R ∈ ℤ[X]` with
`p ∤ R(0)` and `Res(Q, R) ≠ 0`, then the same holds for every `R ∈ ℤ_ℓ[X]` with
`Res(Q, R) ≠ 0`. -/
theorem norm_resultant_eq_of_intPoly (p : ℕ) (hp : p.Prime) (hpℓ : p ≠ ℓ) (P T Q : ℚ_[ℓ][X])
    (H : ∀ R : ℤ[X], ¬ (p : ℤ) ∣ R.coeff 0 → Q.resultant (R.map (Int.castRingHom ℚ_[ℓ])) ≠ 0 →
      ‖P.resultant (R.map (Int.castRingHom ℚ_[ℓ]))‖ = ‖T.resultant (R.map (Int.castRingHom ℚ_[ℓ]))‖)
    (S : ℤ_[ℓ][X]) (hS : Q.resultant (S.map PadicInt.Coe.ringHom) ≠ 0) :
    ‖P.resultant (S.map PadicInt.Coe.ringHom)‖ = ‖T.resultant (S.map PadicInt.Coe.ringHom)‖ := by
  set n := S.natDegree
  choose R hRdeg hR0 hRS using fun N : ℕ => exists_intPoly_map_toZModPow_eq p hp hpℓ S N
  set S' := S.map PadicInt.Coe.ringHom
  have hS'deg : S'.natDegree = n := natDegree_map_eq_of_injective Subtype.val_injective S
  set R' : ℕ → ℚ_[ℓ][X] := fun N => (R N).map (Int.castRingHom ℚ_[ℓ])
  have hR'deg : ∀ N, (R' N).natDegree = n := fun N =>
    (natDegree_map_eq_of_injective (RingHom.injective_int _) _).trans (hRdeg N)
  -- coefficientwise convergence
  have hconv : Tendsto (fun N => fun k : Fin (n + 1) => (R' N).coeff k) atTop
      (𝓝 fun k : Fin (n + 1) => S'.coeff k) := by
    refine tendsto_pi_nhds.2 fun k => ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_)
      (g := fun N => ‖(ℓ : ℚ_[ℓ]) ^ N‖) (by
        simpa only [norm_zero] using (tendsto_pow_prime_atTop_nhds_zero (ℓ := ℓ)).norm)
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

/-- **Mumford's resultant lemma over `ℚ_ℓ`** ([Mumford, *Abelian varieties*, §19, the lemma
before Theorem 4], in the form used for Theorem 4). Let `ℓ ≠ p` be primes, `χ`, `P` monic of the
same degree over `ℚ_ℓ` and `D ≠ 0`. If `‖Res(P, R)‖ = ‖Res(χ, R)‖` for every `R ∈ ℤ[X]` with
`p ∤ R(0)` and `Res(D χ, R) ≠ 0`, then `P = χ`. -/
theorem eq_of_norm_resultant_intPoly_eq (p : ℕ) (hp : p.Prime) (hpℓ : p ≠ ℓ)
    (χ P D : ℚ_[ℓ][X]) (hχ : χ.Monic) (hP : P.Monic) (hdeg : P.natDegree = χ.natDegree)
    (hD : D ≠ 0)
    (H : ∀ R : ℤ[X], ¬ (p : ℤ) ∣ R.coeff 0 →
      (D * χ).resultant (R.map (Int.castRingHom ℚ_[ℓ])) ≠ 0 →
      ‖P.resultant (R.map (Int.castRingHom ℚ_[ℓ]))‖ =
        ‖χ.resultant (R.map (Int.castRingHom ℚ_[ℓ]))‖) :
    P = χ := by
  refine eq_of_norm_resultant_eq χ P D hχ hP hdeg hD fun S hS hres => ?_
  obtain ⟨S', rfl⟩ : S ∈ Polynomial.lifts (PadicInt.Coe.ringHom (p := ℓ)) :=
    (lifts_iff_coeff_lifts S).2 fun k => ⟨⟨S.coeff k, hS k⟩, rfl⟩
  exact norm_resultant_eq_of_intPoly p hp hpℓ P χ (D * χ) H S' hres

end Stacks.Polynomial
