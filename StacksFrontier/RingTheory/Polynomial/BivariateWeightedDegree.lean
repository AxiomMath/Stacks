module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Weighted degree of bivariate polynomials

For `g ∈ R[X][Y]` and weights `1` on `X` and `w` on `Y`, we say `g` has *weighted degree at most
`n`* if `deg (coeff_j g) + w j ≤ n` for every `j` with `coeff_j g ≠ 0`. This filtration is closed
under sums, products, powers and derivatives, and reduction modulo a polynomial `Ψ` monic in `Y`
does not increase it when `Ψ` itself has weighted degree `w · deg_Y Ψ`.

## Main definitions

* `Polynomial.Bivariate.WeightedDegreeLE`: the predicate of having weighted degree at most `n`.
* `Polynomial.Bivariate.monomialXY`: the monomial `Xⁱ Yʲ` of `R[X][Y]`.

## Main results

* `Polynomial.Bivariate.WeightedDegreeLE.mul`: weighted degrees add under multiplication.
* `Polynomial.Bivariate.WeightedDegreeLE.modByMonic`: reduction modulo a monic `Ψ` of weighted
  degree `w · deg_Y Ψ` preserves weighted degree.
* `Polynomial.Bivariate.mem_span_monomialXY_of_natDegree_lt`: a polynomial of `Y`-degree `< m`
  all of whose coefficients have degree `≤ N` lies in the span of the `m (N + 1)` monomials
  `Xⁱ Yʲ`, `i ≤ N`, `j < m`.
-/

@[expose] public section

open Polynomial
open scoped Polynomial.Bivariate

namespace Polynomial.Bivariate

variable {R : Type*} [CommRing R]

/-- `g` has weighted degree at most `n` for the weights `1` on `X` and `w` on `Y`. -/
def WeightedDegreeLE (w n : ℕ) (g : R[X][Y]) : Prop :=
  ∀ j, g.coeff j ≠ 0 → (g.coeff j).natDegree + w * j ≤ n

namespace WeightedDegreeLE

variable {w n n' : ℕ} {g h : R[X][Y]}

/-- The zero polynomial has weighted degree at most `n`. -/
theorem zero : WeightedDegreeLE w n (0 : R[X][Y]) := fun j hj => absurd (by simp) hj

/-- Weighted degree at most `n` implies weighted degree at most `n'` for `n ≤ n'`. -/
theorem mono (hg : WeightedDegreeLE w n g) (hn : n ≤ n') : WeightedDegreeLE w n' g :=
  fun j hj => (hg j hj).trans hn

/-- A sum of polynomials of weighted degree at most `n` has weighted degree at most `n`. -/
theorem add (hg : WeightedDegreeLE w n g) (hh : WeightedDegreeLE w n h) :
    WeightedDegreeLE w n (g + h) := by
  intro j hj
  rw [coeff_add] at hj ⊢
  by_cases hgj : g.coeff j = 0
  · rw [hgj, zero_add] at hj ⊢; exact hh j hj
  by_cases hhj : h.coeff j = 0
  · rw [hhj, add_zero] at hj ⊢; exact hg j hj
  have := natDegree_add_le (g.coeff j) (h.coeff j)
  have h1 := hg j hgj
  have h2 := hh j hhj
  omega

/-- The negation of a polynomial of weighted degree at most `n` has weighted degree at most `n`. -/
theorem neg (hg : WeightedDegreeLE w n g) : WeightedDegreeLE w n (-g) := by
  intro j hj
  rw [coeff_neg, natDegree_neg]
  exact hg j (by simpa using hj)

/-- A difference of polynomials of weighted degree at most `n` has weighted degree at most `n`. -/
theorem sub (hg : WeightedDegreeLE w n g) (hh : WeightedDegreeLE w n h) :
    WeightedDegreeLE w n (g - h) := by
  rw [sub_eq_add_neg]; exact hg.add hh.neg

/-- If `deg a + w j ≤ n`, then `C a * Y ^ j` has weighted degree at most `n`. -/
theorem C_mul_X_pow {a : R[X]} {j : ℕ} (ha : a.natDegree + w * j ≤ n) :
    WeightedDegreeLE w n (C a * X ^ j) := by
  intro j' hj'
  rw [coeff_C_mul_X_pow] at hj' ⊢
  split_ifs at hj' ⊢ with h
  · subst h; exact ha
  · exact absurd rfl hj'

/-- If `deg a ≤ n`, then the constant `C a` has weighted degree at most `n`. -/
theorem C {a : R[X]} (ha : a.natDegree ≤ n) : WeightedDegreeLE w n (C a : R[X][Y]) := by
  simpa using C_mul_X_pow (w := w) (j := 0) (a := a) (by simpa using ha)

/-- A scalar multiple of a polynomial of weighted degree at most `n` has weighted degree at most
`n`. -/
theorem smul (hg : WeightedDegreeLE w n g) (c : R) : WeightedDegreeLE w n (c • g) := by
  intro j hj
  rw [coeff_smul] at hj ⊢
  exact (Nat.add_le_add_right (natDegree_smul_le c _) _).trans (hg j fun h => by simp [h] at hj)

/-- A finite sum of polynomials of weighted degree at most `n` has weighted degree at most `n`. -/
theorem sum {ι : Type*} (s : Finset ι) {f : ι → R[X][Y]}
    (hf : ∀ i ∈ s, WeightedDegreeLE w n (f i)) : WeightedDegreeLE w n (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- If `g` and `h` have weighted degrees at most `n` and `n'`, then `g * h` has weighted degree at
most `n + n'`. -/
theorem mul (hg : WeightedDegreeLE w n g) (hh : WeightedDegreeLE w n' h) :
    WeightedDegreeLE w (n + n') (g * h) := by
  intro j hj
  rw [coeff_mul] at hj ⊢
  have key : ∀ x ∈ Finset.antidiagonal j, g.coeff x.1 * h.coeff x.2 ≠ 0 →
      (g.coeff x.1 * h.coeff x.2).natDegree + w * j ≤ n + n' := by
    intro x hx hne
    have hx' := Finset.mem_antidiagonal.mp hx
    have h1 := hg x.1 (left_ne_zero_of_mul hne)
    have h2 := hh x.2 (right_ne_zero_of_mul hne)
    have : w * j = w * x.1 + w * x.2 := by rw [← mul_add, hx']
    have := natDegree_mul_le (p := g.coeff x.1) (q := h.coeff x.2)
    omega
  obtain ⟨x₀, hx₀, hne₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hj
  have := key x₀ hx₀ hne₀
  refine (Nat.add_le_add_right (natDegree_sum_le_of_forall_le _ _ (n := n + n' - w * j)
    fun x hx => ?_) _).trans (by omega)
  by_cases hne : g.coeff x.1 * h.coeff x.2 = 0
  · simp [hne]
  have := key x hx hne
  omega

/-- The polynomial `1` has weighted degree at most `n`. -/
theorem one : WeightedDegreeLE w n (1 : R[X][Y]) := by
  simpa using C (w := w) (n := n) (a := (1 : R[X])) (by simp)

/-- If `g` has weighted degree at most `n`, then `g ^ k` has weighted degree at most `k * n`. -/
theorem pow (hg : WeightedDegreeLE w n g) (k : ℕ) : WeightedDegreeLE w (k * n) (g ^ k) := by
  induction k with
  | zero => simpa using one
  | succ k ih => rw [pow_succ, Nat.succ_mul]; exact ih.mul hg

/-- The `Y`-derivative of a polynomial of weighted degree at most `n` has weighted degree at most
`n`. -/
theorem derivative (hg : WeightedDegreeLE w n g) : WeightedDegreeLE w n (derivative g) := by
  intro j hj
  rw [coeff_derivative] at hj ⊢
  have hgj : g.coeff (j + 1) ≠ 0 := fun h => by simp [h] at hj
  have := hg (j + 1) hgj
  have h2 := natDegree_mul_le (p := g.coeff (j + 1)) (q := ((j : R[X]) + 1))
  have h3 : ((j : R[X]) + 1).natDegree = 0 := by
    rw [show ((j : R[X]) + 1) = ((j + 1 : ℕ) : R[X]) by push_cast; ring, natDegree_natCast]
  have : w * j ≤ w * (j + 1) := Nat.mul_le_mul_left _ (Nat.le_succ j)
  omega

/-- Every `Y`-coefficient of a polynomial of weighted degree at most `n` has degree at most `n`. -/
theorem coeff_natDegree_le (hg : WeightedDegreeLE w n g) (j : ℕ) : (g.coeff j).natDegree ≤ n := by
  by_cases hj : g.coeff j = 0
  · simp [hj]
  · exact (Nat.le_add_right _ _).trans (hg j hj)

/-- Reduction modulo a monic `Ψ` of weighted degree `w · deg_Y Ψ` preserves weighted degree. -/
theorem modByMonic {Ψ : R[X][Y]} (hΨ : Ψ.Monic) (hΨw : WeightedDegreeLE w (w * Ψ.natDegree) Ψ)
    (hg : WeightedDegreeLE w n g) : WeightedDegreeLE w n (g %ₘ Ψ) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · intro j hj; exact absurd (Subsingleton.elim _ _) hj
  by_cases hΨ0 : Ψ.natDegree = 0
  · rw [eq_one_of_monic_natDegree_zero hΨ hΨ0, modByMonic_one]; exact zero
  induction hd : g.natDegree using Nat.strong_induction_on generalizing g with
  | _ d ih =>
  by_cases hlt : g.natDegree < Ψ.natDegree
  · rwa [(modByMonic_eq_self_iff hΨ).mpr ((degree_le_natDegree).trans_lt
      (by rwa [degree_eq_natDegree hΨ.ne_zero, Nat.cast_lt]))]
  push Not at hlt
  have hg0 : g ≠ 0 := by rintro rfl; simp at hlt; omega
  have hlc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg0
  have hlcdeg : g.leadingCoeff.natDegree + w * g.natDegree ≤ n := hg _ hlc
  set a := g.natDegree - Ψ.natDegree
  have ha : a + Ψ.natDegree = g.natDegree := Nat.sub_add_cancel hlt
  set t := Polynomial.C g.leadingCoeff * X ^ a * Ψ
  have hlct : (Polynomial.C g.leadingCoeff * X ^ a).leadingCoeff * Ψ.leadingCoeff ≠ 0 := by
    rwa [leadingCoeff_C_mul_X_pow, hΨ.leadingCoeff, mul_one]
  have htdeg : t.natDegree = g.natDegree := by
    simp only [t]; rw [natDegree_mul' hlct, natDegree_C_mul_X_pow _ _ hlc, ha]
  have htlc : t.leadingCoeff = g.leadingCoeff := by
    simp only [t]; rw [leadingCoeff_mul' hlct, leadingCoeff_C_mul_X_pow, hΨ.leadingCoeff, mul_one]
  have ht : WeightedDegreeLE w n t := by
    have h1 : WeightedDegreeLE w (g.leadingCoeff.natDegree + w * a)
        (Polynomial.C g.leadingCoeff * X ^ a) := C_mul_X_pow le_rfl
    refine (h1.mul hΨw).mono ?_
    have : w * a + w * Ψ.natDegree = w * g.natDegree := by rw [← mul_add, ha]
    omega
  have hdvd : Ψ ∣ g - (g - t) := ⟨Polynomial.C g.leadingCoeff * X ^ a, by simp only [t]; ring⟩
  rw [modByMonic_eq_of_dvd_sub hΨ hdvd]
  by_cases hz : g - t = 0
  · rw [hz, zero_modByMonic]; exact zero
  have ht0 : t ≠ 0 := fun h => hlc (by rw [← htlc, h, leadingCoeff_zero])
  have hdeg : (g - t).natDegree < g.natDegree := by
    refine (natDegree_lt_iff_degree_lt hz).mpr ?_
    refine (degree_eq_natDegree hg0).symm ▸ degree_sub_lt_left ?_ hg0 htlc.symm
    rw [degree_eq_natDegree hg0, degree_eq_natDegree ht0, htdeg]
  exact ih _ (hd ▸ hdeg) (hg.sub ht) rfl

end WeightedDegreeLE

/-- The monomial `Xⁱ Yʲ` of `R[X][Y]`. -/
noncomputable def monomialXY (ij : ℕ × ℕ) : R[X][Y] := Polynomial.C (X ^ ij.1) * X ^ ij.2

/-- The coefficient of `Xⁱ Yʲ` in the monomial `monomialXY ij` is `1` if `ij = (i, j)` and `0`
otherwise. -/
theorem coeff_coeff_monomialXY (ij : ℕ × ℕ) (i j : ℕ) :
    ((monomialXY ij : R[X][Y]).coeff j).coeff i = if ij = (i, j) then 1 else 0 := by
  obtain ⟨i', j'⟩ := ij
  simp only [monomialXY, coeff_C_mul_X_pow, Prod.mk.injEq]
  by_cases hj : j = j'
  · subst hj; simp [coeff_X_pow, eq_comm]
  · simp [hj, Ne.symm hj]

/-- If `i + w j ≤ n`, then the monomial `Xⁱ Yʲ` has weighted degree at most `n`. -/
theorem WeightedDegreeLE.monomialXY {w n : ℕ} {ij : ℕ × ℕ} (h : ij.1 + w * ij.2 ≤ n) :
    WeightedDegreeLE w n (monomialXY ij : R[X][Y]) :=
  WeightedDegreeLE.C_mul_X_pow ((Nat.add_le_add_right (natDegree_X_pow_le _) _).trans h)

/-- Distinct monomials `Xⁱ Yʲ` are linearly independent. -/
theorem eq_zero_of_sum_smul_monomialXY_eq_zero {K : Type*} [Field K] {s : Finset (ℕ × ℕ)}
    {c : ℕ × ℕ → K} (h : ∑ ij ∈ s, c ij • (monomialXY ij : K[X][Y]) = 0) {ij : ℕ × ℕ}
    (hij : ij ∈ s) : c ij = 0 := by
  have := congrArg (fun g : K[X][Y] => (g.coeff ij.2).coeff ij.1) h
  simp only [finsetSum_coeff, coeff_smul, smul_eq_mul, coeff_coeff_monomialXY, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Polynomial.coeff_zero, Prod.mk.eta] at this
  simpa [hij] using this

/-- A polynomial of `Y`-degree `< m` whose coefficients all have degree `≤ N` lies in the span of
the monomials `Xⁱ Yʲ` with `i ≤ N` and `j < m`. -/
theorem mem_span_monomialXY_of_natDegree_lt {K : Type*} [Field K] [DecidableEq K[X][Y]]
    {g : K[X][Y]} {m N : ℕ} (hm : g.natDegree < m) (hN : ∀ j, (g.coeff j).natDegree ≤ N) :
    g ∈ Submodule.span K
      (((Finset.range (N + 1) ×ˢ Finset.range m).image (monomialXY (R := K)) :
        Finset K[X][Y]) : Set K[X][Y]) := by
  rw [as_sum_range' g m hm]
  refine Submodule.sum_mem _ fun j hj => ?_
  rw [← C_mul_X_pow_eq_monomial, as_sum_range' (g.coeff j) (N + 1) (Nat.lt_succ_of_le (hN j)),
    map_sum, Finset.sum_mul]
  refine Submodule.sum_mem _ fun i hi => ?_
  rw [← C_mul_X_pow_eq_monomial, map_mul, mul_assoc,
    show (Polynomial.C (Polynomial.C ((g.coeff j).coeff i)) : K[X][Y]) =
      algebraMap K K[X][Y] ((g.coeff j).coeff i) from rfl, ← Algebra.smul_def]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product]
  exact ⟨(i, j), ⟨hi, hj⟩, rfl⟩

end Polynomial.Bivariate
