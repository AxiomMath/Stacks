module

public import StacksFrontier.RingTheory.HilbertSamuel.Defs
public import StacksFrontier.RingTheory.HilbertSamuel.Function
public import StacksFrontier.RingTheory.HilbertFunction.Numerical
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# The degrees of the numerical polynomials `φ_{I,M}` and `χ_{I,M}` do not depend on `I`

Let `(R, m)` be a Noetherian local ring, let `I ⊆ R` be an ideal of definition, that is an
ideal with `√I = m`, and let `M` be a finite `R`-module. Every finite `R`-module annihilated
by a power of `I` has finite length, so the two functions

  `φ_{I,M}(n) = length_R (I ^ n M / I ^ (n + 1) M)`  and
  `χ_{I,M}(n) = length_R (M / I ^ (n + 1) M)`

are defined for all `n ≥ 0`, and they are numerical polynomials (Proposition 00K8). Their
degrees are invariants of `R` and `M` alone: changing the ideal of definition changes the
polynomials, but not their degrees. For `χ` this is immediate from the comparison
`χ_{I,M}(n) ≤ χ_{I',M}(a n)` of Lemma 00K7, and for `φ` it follows because
`φ_{I,M}(n) = χ_{I,M}(n) - χ_{I,M}(n - 1)` for `n ≥ 1`.

## Main results

* `Ideal.exists_degree_eq_of_eventually_eval_eq_length_quotient_smul_pow`: the degree of the
  numerical polynomial `φ_{I,M}`, and the degree of the numerical polynomial `χ_{I,M}`, are
  independent of the ideal of definition `I`.

## Implementation notes

Neither Mathlib nor this project has a type of numerical polynomials, so "the degree of the
numerical polynomial `φ_{I,M}`" is spelled by way of the rational polynomials that compute the
function: a numerical polynomial (Tag 00JX) agrees at all large `n` with a unique `P ∈ ℚ[t]`,
whose degree is the degree of the numerical polynomial. So the invariance proved here is that
*every* `P ∈ ℚ[t]` agreeing with `φ_{I,M}` at all large `n`, for *any* ideal of definition `I`,
has one and the same degree `d`, and likewise `e` for `χ_{I,M}`. Degrees are compared in
`WithBot ℕ`, so the case `M = 0`, where both polynomials are `0` and both degrees are `⊥ = -∞`,
is included; this is the value `-∞` of Definition 00KA.

The two halves of the proof are:

* for `χ`, the polynomial comparison `HilbertSamuel.poly_cmp` applied to the two inequalities
  `χ_{I,M}(n) ≤ χ_{I',M}(a n)` and `χ_{I',M}(n) ≤ χ_{I,M}(a' n)` of Lemma 00K7; substituting
  `a n` for `n` does not change a degree, so the two degrees bound each other;
* for `φ`, the identity `φ_{I,M}(n) = χ_{I,M}(n) - χ_{I,M}(n - 1)`, which comes from additivity
  of length along `I ^ (n + 1) M ⊆ I ^ n M ⊆ M`. It forces a polynomial `P` computing `φ_{I,M}`
  to be the forward difference `Q - Q(t - 1)` of any polynomial `Q` computing `χ_{I,M}`, and the
  degree of a forward difference depends on `Q` only through its degree, being `deg Q - 1` for
  nonconstant `Q` and `-∞` for constant `Q` (`degree_delta_congr`).

Being an ideal of definition (Tag 07DU) is spelled `I.radical = IsLocalRing.maximalIdeal R`,
and `I ^ n M` as `I ^ n • (⊤ : Submodule R M)`, so that the subquotient `I ^ n M / I ^ (n + 1) M`
is `↥(I ^ n • ⊤) ⧸ (I ^ (n + 1) • ⊤).submoduleOf (I ^ n • ⊤)`; these are the spellings of
`Ideal.exists_eventually_length_quotient_smul_pow_eq_sum_choose_mul` (Tag 00K8), which provides
the polynomial computing `χ_{I,M}` for each ideal of definition `I`. Finiteness of the lengths is
carried inside the hypotheses on `P`, in the shape
`∃ p : ℕ, Module.length R … = p ∧ P.eval (n : ℚ) = p`, again as in 00K8.

## References

* [Stacks Project, Tag 00K9](https://stacks.math.columbia.edu/tag/00K9)

## Tags

Hilbert function, numerical polynomial, ideal of definition, degree, length
-/

open Filter IsLocalRing Polynomial
open _root_.Stacks.HilbertFunction.NumericalPoly

/-! ### Uniqueness and comparison of computing polynomials -/

/-- A polynomial eventually nonnegative on `ℕ` and there bounded by a second polynomial has
degree at most that of the second one. This is `HilbertSamuel.poly_cmp` at `c = 0`, whose
hypothesis `q ≠ 0` is ruled out by the nonnegativity when `q = 0`. -/
private lemma degree_le_of_eventually_eval_le {p q : ℚ[X]}
    (hp : ∀ᶠ n : ℕ in atTop, 0 ≤ p.eval (n : ℚ))
    (hpq : ∀ᶠ n : ℕ in atTop, p.eval (n : ℚ) ≤ q.eval (n : ℚ)) : p.degree ≤ q.degree := by
  rcases eq_or_ne q 0 with rfl | hq
  · refine le_of_eq (congrArg Polynomial.degree (eq_of_eventually_eval_natCast_eq ?_))
    filter_upwards [hp, hpq] with n h1 h2
    simp only [eval_zero] at h2 ⊢
    linarith
  · exact HilbertSamuel.poly_cmp p q 0
      (by filter_upwards [hpq] with n hn; linarith) hq
      (HilbertSamuel.nonneg_leadingCoeff_of_eventually_nonneg p hp)

/-! ### Rescaling and shifting the variable -/

private lemma degree_comp_C_mul_X (P : ℚ[X]) {k : ℚ} (hk : k ≠ 0) :
    (P.comp (C k * X)).degree = P.degree := by
  rw [degree_comp (by rw [degree_C_mul_X hk]; exact zero_lt_one), degree_C_mul_X hk, mul_one]

private lemma eval_comp_C_mul_X (P : ℚ[X]) (k x : ℚ) :
    (P.comp (C k * X)).eval x = P.eval (k * x) := by
  simp [eval_comp]

/-! ### The forward difference of a rational polynomial

The degree of `Q - Q(t - 1)` depends on `Q` only through the degree of `Q`: it is `deg Q - 1` for
a nonconstant `Q`, since the leading terms cancel while the coefficient in degree `deg Q - 1` of
the difference is `deg Q` times the leading coefficient of `Q`, and it is `-∞` for constant `Q`.
-/

private lemma delta_eq_zero_of_natDegree_eq_zero {Q : ℚ[X]} (h : Q.natDegree = 0) :
    Q - Q.comp (X - C 1) = 0 := by
  obtain ⟨c, rfl⟩ := Polynomial.natDegree_eq_zero.mp h
  simp

/-- Composing with `X - 1` is the Taylor shift by `-1`. -/
private lemma comp_X_sub_one_eq_taylor (Q : ℚ[X]) : Q.comp (X - C 1) = taylor (-1 : ℚ) Q := by
  rw [taylor_apply, map_neg, sub_eq_add_neg]

private lemma degree_delta_of_one_le {Q : ℚ[X]} (h : 1 ≤ Q.natDegree) :
    (Q - Q.comp (X - C 1)).degree = ((Q.natDegree - 1 : ℕ) : WithBot ℕ) := by
  have hQ0 : Q ≠ 0 := fun h0 => by simp [h0] at h
  rw [comp_X_sub_one_eq_taylor]
  have hdegQ : Q.degree = (Q.natDegree : WithBot ℕ) := degree_eq_natDegree hQ0
  have hlt : (Q - taylor (-1 : ℚ) Q).degree < (Q.natDegree : WithBot ℕ) := by
    rw [← hdegQ]
    exact degree_sub_lt_left (degree_taylor Q _).symm hQ0
      (leadingCoeff_taylor (r := -1) (f := Q)).symm
  have hcoeff_comp : (taylor (-1 : ℚ) Q).coeff (Q.natDegree - 1)
      = Q.coeff (Q.natDegree - 1) - (Q.natDegree : ℚ) * Q.coeff Q.natDegree := by
    rw [taylor_coeff]
    have hnd : (hasseDeriv (Q.natDegree - 1) Q).natDegree < 2 := by
      rw [natDegree_hasseDeriv]; omega
    rw [eval_eq_sum_range' hnd, Finset.sum_range_succ, Finset.sum_range_one,
      hasseDeriv_coeff, hasseDeriv_coeff]
    have e1 : 0 + (Q.natDegree - 1) = Q.natDegree - 1 := by omega
    have e2 : 1 + (Q.natDegree - 1) = Q.natDegree := by omega
    rw [e1, e2, Nat.choose_self, Nat.choose_symm (by omega : 1 ≤ Q.natDegree),
      Nat.choose_one_right]
    push_cast
    ring
  have hcoeff : (Q - taylor (-1 : ℚ) Q).coeff (Q.natDegree - 1)
      = (Q.natDegree : ℚ) * Q.coeff Q.natDegree := by
    rw [coeff_sub, hcoeff_comp]; ring
  have hne : (Q - taylor (-1 : ℚ) Q).coeff (Q.natDegree - 1) ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero (by positivity) (leadingCoeff_ne_zero.mpr hQ0)
  have hDne : Q - taylor (-1 : ℚ) Q ≠ 0 := fun h0 => by rw [h0] at hne; simp at hne
  refine le_antisymm ?_ (le_degree_of_ne_zero hne)
  have hnatlt : (Q - taylor (-1 : ℚ) Q).natDegree < Q.natDegree :=
    (natDegree_lt_iff_degree_lt hDne).mpr hlt
  rw [degree_eq_natDegree hDne]
  exact Nat.cast_le.mpr (by omega)

/-- The degree of the forward difference `Q - Q(t - 1)` is determined by the degree of `Q`. -/
private lemma degree_delta_congr {Q Q' : ℚ[X]} (h : Q.degree = Q'.degree) :
    (Q - Q.comp (X - C 1)).degree = (Q' - Q'.comp (X - C 1)).degree := by
  have hnd : Q.natDegree = Q'.natDegree := natDegree_eq_of_degree_eq h
  rcases Nat.eq_zero_or_pos Q.natDegree with h0 | h1
  · rw [delta_eq_zero_of_natDegree_eq_zero h0,
      delta_eq_zero_of_natDegree_eq_zero (by omega : Q'.natDegree = 0)]
  · rw [degree_delta_of_one_le h1, degree_delta_of_one_le (by omega : 1 ≤ Q'.natDegree), hnd]

/-! ### A polynomial computing `χ_{I,M}` for every ideal of definition

Proposition 00K8 presents `χ_{I,M}` as an eventual `ℤ`-combination of binomial coefficients;
`binomSum r b` is the rational polynomial `∑_{i ≤ r} b i (t choose i)` computing it.
-/

/-- Proposition 00K8: for an ideal of definition `I` the function
`χ_{I,M}(n) = length_R (M / I ^ (n + 1) M)` is computed at all large `n` by a rational
polynomial. -/
private lemma exists_computes_chi {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I.radical = maximalIdeal R) (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    ∃ Q : ℚ[X], ∀ᶠ n : ℕ in atTop, ∃ q : ℕ,
      Module.length R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) = q ∧
        Q.eval (n : ℚ) = (q : ℚ) := by
  obtain ⟨r, _, b, hab⟩ :=
    Ideal.exists_eventually_length_quotient_smul_pow_eq_sum_choose_mul I hI M
  refine ⟨binomSum r b, hab.mono fun n hn => ?_⟩
  obtain ⟨q, hq1, hq2⟩ := hn.2
  exact ⟨q, hq1, by rw [binomSum_eval]; exact_mod_cast hq2.symm⟩

/-! ### `φ_{I,M}` is the forward difference of `χ_{I,M}` -/

/-- Additivity of length along `I ^ (n + 1) M ⊆ I ^ n M ⊆ M` reads
`φ_{I,M}(n) = χ_{I,M}(n) - χ_{I,M}(n - 1)`, so a polynomial computing `φ_{I,M}` is the forward
difference of any polynomial computing `χ_{I,M}`. -/
private lemma eq_delta_of_computes_phi {R : Type*} [CommRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] (P Q : ℚ[X])
    (hP : ∀ᶠ n : ℕ in atTop, ∃ p : ℕ,
      Module.length R (↥(I ^ n • (⊤ : Submodule R M)) ⧸
          (I ^ (n + 1) • (⊤ : Submodule R M)).submoduleOf (I ^ n • ⊤)) = p ∧
        P.eval (n : ℚ) = (p : ℚ))
    (hQ : ∀ᶠ n : ℕ in atTop, ∃ q : ℕ,
      Module.length R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) = q ∧
        Q.eval (n : ℚ) = (q : ℚ)) :
    P = Q - Q.comp (X - C 1) := by
  refine eq_of_eventually_eval_natCast_eq ?_
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hP
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hQ
  refine eventually_atTop.mpr ⟨max N₁ (N₂ + 1), fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : N₂ + 1 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨p, hp1, hp2⟩ := hN₁ n hn1
  obtain ⟨q1, hq11, hq12⟩ := hN₂ n (by omega)
  obtain ⟨q0, hq01, hq02⟩ := hN₂ (n - 1) (by omega)
  have hq01' : Module.length R (M ⧸ (I ^ n • (⊤ : Submodule R M))) = q0 := by
    have hnn : n = (n - 1) + 1 := by omega
    rw [hnn]; exact hq01
  have hle : (I ^ (n + 1) • (⊤ : Submodule R M)) ≤ I ^ n • ⊤ :=
    Submodule.smul_mono (Ideal.pow_le_pow_right (Nat.le_succ n)) le_rfl
  have hadd := length_quotient_eq_length_add_length_quotient
    (I ^ n • (⊤ : Submodule R M)) (I ^ (n + 1) • (⊤ : Submodule R M)) hle
  rw [hq11, hp1, hq01'] at hadd
  have hnat : q1 = p + q0 := by
    have hcast : ((q1 : ℕ∞)) = ((p + q0 : ℕ) : ℕ∞) := by rw [hadd]; push_cast; ring
    exact_mod_cast hcast
  have hcastQ : ((n : ℚ) - 1) = ((n - 1 : ℕ) : ℚ) := by
    have h1n : (1 : ℕ) ≤ n := by omega
    rw [Nat.cast_sub h1n, Nat.cast_one]
  rw [hp2, eval_sub, eval_comp, eval_sub, eval_X, eval_C, hcastQ, hq02, hq12, hnat]
  push_cast
  ring

/-! ### Independence of the ideal of definition -/

/-- Lemma 00K7 in the form `χ_{I,M}(n) ≤ χ_{J,M}(k n)` forces the degree of a polynomial
computing `χ_{I,M}` to be at most that of one computing `χ_{J,M}`: rescaling the variable of a
polynomial does not change its degree. -/
private lemma degree_le_of_chi_le {R : Type*} [CommRing R] (I J : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] (P Q : ℚ[X]) (k : ℕ) (hk : 0 < k)
    (hcmp : ∀ n : ℕ, 1 ≤ n → hilbertSamuel_chi I M n ≤ hilbertSamuel_chi J M (k * n))
    (hP : ∀ᶠ n : ℕ in atTop, ∃ q : ℕ,
      Module.length R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) = q ∧
        P.eval (n : ℚ) = (q : ℚ))
    (hQ : ∀ᶠ n : ℕ in atTop, ∃ q : ℕ,
      Module.length R (M ⧸ (J ^ (n + 1) • (⊤ : Submodule R M))) = q ∧
        Q.eval (n : ℚ) = (q : ℚ)) :
    P.degree ≤ Q.degree := by
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hP
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hQ
  have key : ∀ n : ℕ, max N₁ (max N₂ 1) ≤ n →
      0 ≤ P.eval (n : ℚ) ∧ P.eval (n : ℚ) ≤ (Q.comp (C (k : ℚ) * X)).eval (n : ℚ) := by
    intro n hn
    obtain ⟨hn1, hn2, hn3⟩ : N₁ ≤ n ∧ N₂ ≤ n ∧ 1 ≤ n := by simpa only [max_le_iff] using hn
    obtain ⟨p, hp1, hp2⟩ := hN₁ n hn1
    obtain ⟨q, hq1, hq2⟩ := hN₂ (k * n) (by nlinarith)
    have hcmpn := hcmp n hn3
    rw [hilbertSamuel_chi, hilbertSamuel_chi, hp1, hq1] at hcmpn
    have hpq : p ≤ q := by exact_mod_cast hcmpn
    refine ⟨by rw [hp2]; positivity, ?_⟩
    rw [eval_comp_C_mul_X, hp2, show (k : ℚ) * n = ((k * n : ℕ) : ℚ) by push_cast; ring, hq2]
    exact_mod_cast hpq
  have h0 : ∀ᶠ n : ℕ in atTop, 0 ≤ P.eval (n : ℚ) :=
    eventually_atTop.mpr ⟨_, fun n hn => (key n hn).1⟩
  have h1 : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) ≤ (Q.comp (C (k : ℚ) * X)).eval (n : ℚ) :=
    eventually_atTop.mpr ⟨_, fun n hn => (key n hn).2⟩
  calc P.degree ≤ (Q.comp (C (k : ℚ) * X)).degree := degree_le_of_eventually_eval_le h0 h1
    _ = Q.degree := degree_comp_C_mul_X Q (by positivity)

/-- **Lemma 00K9(2).** Two polynomials computing `χ_{I,M}` and `χ_{J,M}` for ideals of definition
`I` and `J` have the same degree. -/
private lemma degree_eq_degree_of_computes_chi {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I J : Ideal R) (hI : I.radical = maximalIdeal R) (hJ : J.radical = maximalIdeal R)
    (P Q : ℚ[X])
    (hP : ∀ᶠ n : ℕ in atTop, ∃ q : ℕ,
      Module.length R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) = q ∧
        P.eval (n : ℚ) = (q : ℚ))
    (hQ : ∀ᶠ n : ℕ in atTop, ∃ q : ℕ,
      Module.length R (M ⧸ (J ^ (n + 1) • (⊤ : Submodule R M))) = q ∧
        Q.eval (n : ℚ) = (q : ℚ)) :
    P.degree = Q.degree := by
  obtain ⟨k, hk, hkle⟩ := chi_change_ideal_of_definition M I J hI hJ
  obtain ⟨l, hl, hlle⟩ := chi_change_ideal_of_definition M J I hJ hI
  exact le_antisymm (degree_le_of_chi_le I J M P Q k hk hkle hP hQ)
    (degree_le_of_chi_le J I M Q P l hl hlle hQ hP)

/-- **Stacks 00K9.** Let `R` be a Noetherian local ring and let `M` be a finite `R`-module. Then
there are `d e : WithBot ℕ`, depending on `R` and `M` only, such that for every ideal of
definition `I ⊆ R` (that is, `I.radical = m`): every polynomial `P ∈ ℚ[t]` agreeing with the
Hilbert function `φ_{I,M}(n) = length_R (I ^ n M / I ^ (n + 1) M)` for all `n ≫ 0` has degree
`d`, and every polynomial `P ∈ ℚ[t]` agreeing with `χ_{I,M}(n) = length_R (M / I ^ (n + 1) M)`
for all `n ≫ 0` has degree `e`. That is, the degrees of the numerical polynomials `φ_{I,M}` and
`χ_{I,M}` are independent of the ideal of definition `I`. -/
@[stacks 00K9 "The degree of a numerical polynomial is spelled as the degree of any rational
polynomial computing it at all large `n`, and independence of `I` as the two degrees being
quantified outside the ideal of definition. Part (1) of the tag is the first conjunct, part (2)
the second.", ega "0 16.2.3" "special case"]
public theorem Ideal.exists_degree_eq_of_eventually_eval_eq_length_quotient_smul_pow
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ d e : WithBot ℕ, ∀ I : Ideal R, I.radical = maximalIdeal R → ∀ P : ℚ[X],
      ((∀ᶠ n : ℕ in atTop, ∃ p : ℕ,
            Module.length R (↥(I ^ n • (⊤ : Submodule R M)) ⧸
              (I ^ (n + 1) • (⊤ : Submodule R M)).submoduleOf (I ^ n • ⊤)) = p ∧
            P.eval (n : ℚ) = (p : ℚ)) → P.degree = d) ∧
      ((∀ᶠ n : ℕ in atTop, ∃ q : ℕ,
            Module.length R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) = q ∧
            P.eval (n : ℚ) = (q : ℚ)) → P.degree = e) := by
  obtain ⟨Qm, hQm⟩ := exists_computes_chi (maximalIdeal R) (radical_maximalIdeal R) M
  refine ⟨(Qm - Qm.comp (X - C 1)).degree, Qm.degree, fun I hI P => ⟨?_, ?_⟩⟩
  · intro hP
    obtain ⟨Q, hQ⟩ := exists_computes_chi I hI M
    rw [eq_delta_of_computes_phi I M P Q hP hQ]
    exact degree_delta_congr (degree_eq_degree_of_computes_chi M I (maximalIdeal R) hI
      (radical_maximalIdeal R) Q Qm hQ hQm)
  · intro hP
    exact degree_eq_degree_of_computes_chi M I (maximalIdeal R) hI (radical_maximalIdeal R)
      P Qm hP hQm
