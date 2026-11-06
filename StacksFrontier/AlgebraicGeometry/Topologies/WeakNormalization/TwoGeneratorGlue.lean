module

public import Mathlib.Algebra.Polynomial.Homogenize
public import StacksFrontier.AlgebraicGeometry.TwoGeneratorSquare
public import StacksFrontier.RingTheory.MvPolynomial.BinaryFormBasis

/-!
# Glueing functions on the two charts of the two-generator almost blowup

Let `f₁, f₂` be elements of a commutative ring `A`. The modification of the two-generator almost
blowup square is `X' = Proj (A[T₀,T₁]/(f₂T₀-f₁T₁))`, covered by the two standard charts `D₊(T₀)`
and `D₊(T₁)`. A function on `X'` is a pair of functions on the two charts agreeing on the
overlap, and the content of [Stacks, Tag 0EVJ] is that such a pair is constant.

This file carries the polynomial algebra behind that. Dehomogenizing at `T₁` turns a form of
degree `d` into a polynomial of degree at most `d`, bijectively
(`Stacks.eq_of_aeval_X_one_eq`), and turns the relation `f₂T₀-f₁T₁` into the
linear form `f₂X-f₁`. So the whole statement becomes an assertion about `A[X]`: if
`X^p (βX^n - ρ)` is a multiple of `f₁ - f₂X`, then `β` and the reversal of `ρ` are both congruent
to one constant, modulo `f₁-f₂X` and `f₂-f₁X` respectively.

The reversal is `Polynomial.reflect`, which is exactly the change of chart: on `D₊(T₀)` the
coordinate is `T₁/T₀` and on `D₊(T₁)` it is `T₀/T₁`, so the two dehomogenizations of one form of
degree `d` are `reflect d` of each other.

## Main results

* `Stacks.AlmostBlowUp.exists_const_of_reflect_glue`: **the polynomial heart**. From
  `X^K (βX^m - ρ) = (f₂ - f₁X) W` with `deg ρ ≤ m` and `K ≥ 1` it produces a constant `a` with
  `β ≡ a` modulo `f₂-f₁X` and `reflect m ρ ≡ a` modulo `f₁-f₂X`.
* `Stacks.AlmostBlowUp.exists_const_of_relationForm_mem`: the same statement for the
  two-generator square, read on homogeneous forms and the relation ideal: a pair of forms whose
  chart fractions agree on the overlap is, on each chart, the fraction of a constant.

## Implementation notes

The splitting `W = X^N q + r` with `r` supported below `N` is
`Stacks.AlmostBlowUp.exists_X_pow_mul_add_eq`, proved by iterating `Polynomial.divX` rather than
through `Polynomial.modByMonic`: the degree bound of the latter needs `Nontrivial A`, and `A` here
is an arbitrary commutative ring.

Passing a conclusion in `A[X]` back to the relation ideal uses `Polynomial.homogenize` to build a
cofactor of the right degree and then the injectivity of dehomogenization on forms of a fixed
degree; on the chart `D₊(T₀)` this happens after one application of `Polynomial.reflect`, which
`Polynomial.reflect_reflect` undoes.

## References

* [Stacks Project, Tag 0EVJ](https://stacks.math.columbia.edu/tag/0EVJ)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
-/

@[expose] public noncomputable section

open Polynomial

namespace Stacks.AlmostBlowUp

universe u

variable {A : Type u} [CommRing A]

/-! ### Splitting off the high-degree part of a polynomial -/

/-- Every polynomial splits as `X ^ N * q + r` with `r` having no coefficient in degree `N` or
above.  Stated with vanishing coefficients rather than with a degree bound, so that it holds over
a ring that may be trivial. -/
theorem exists_X_pow_mul_add_eq (N : ℕ) (W : Polynomial A) :
    ∃ q r : Polynomial A, W = X ^ N * q + r ∧ ∀ i, N ≤ i → r.coeff i = 0 := by
  induction N with
  | zero => exact ⟨W, 0, by simp, fun i _ => by simp⟩
  | succ N ih =>
    obtain ⟨q, r, hW, hr⟩ := ih
    refine ⟨q.divX, X ^ N * C (q.coeff 0) + r, ?_, ?_⟩
    · have hq := X_mul_divX_add q
      calc W = X ^ N * q + r := hW
        _ = X ^ N * (X * q.divX + C (q.coeff 0)) + r := by rw [hq]
        _ = X ^ (N + 1) * q.divX + (X ^ N * C (q.coeff 0) + r) := by ring
    · intro i hi
      have h1 : (X ^ N * C (q.coeff 0) : Polynomial A).coeff i = 0 := by
        obtain ⟨j, rfl⟩ : ∃ j, i = (j + 1) + N := ⟨i - N - 1, by omega⟩
        rw [coeff_X_pow_mul, coeff_C]
        simp
      rw [coeff_add, h1, hr i (by omega), add_zero]

/-! ### The linear forms of the two charts -/

/-- A linear polynomial has degree at most one. -/
theorem natDegree_sub_C_mul_X_le (c d : A) :
    (C c - C d * X : Polynomial A).natDegree ≤ 1 :=
  le_trans (natDegree_sub_le _ _) (max_le (by simp)
    (le_trans natDegree_mul_le (by
      have h := natDegree_X_le (R := A)
      have h2 := natDegree_C d
      omega)))

/-- Reversing a linear polynomial exchanges its two coefficients. -/
theorem reflect_one_sub_C_mul_X (c d : A) :
    reflect 1 (C c - C d * X : Polynomial A) = C c * X - C d := by
  have h0 : (C d : Polynomial A).natDegree ≤ 0 := by simp
  rw [reflect_sub, reflect_C, reflect_mul (C d) X h0 natDegree_X_le (F := 0) (G := 1),
    reflect_C, reflect_one_X, pow_one, pow_zero, mul_one, mul_one]

/-- A linear polynomial has degree at most one. -/
theorem natDegree_C_mul_X_sub_C_le (c d : A) :
    (C c * X - C d : Polynomial A).natDegree ≤ 1 :=
  by rw [← natDegree_neg, neg_sub]; exact natDegree_sub_C_mul_X_le d c

/-- Reversing `c * X - d` gives `c - d * X`. -/
theorem reflect_one_C_mul_X_sub_C (c d : A) :
    reflect 1 (C c * X - C d : Polynomial A) = C c - C d * X := by
  rw [← reflect_one_sub_C_mul_X, reflect_reflect]

/-! ### The polynomial heart of Tag 0EVJ -/

/-- Reversing `X ^ K * ρ` at `K + m` gives the reversal of `ρ` at `m`. -/
private theorem reflect_X_pow_mul_add (K m : ℕ) {ρ : Polynomial A} (hρ : ρ.natDegree ≤ m) :
    reflect (K + m) (X ^ K * ρ) = reflect m ρ := by
  rw [reflect_mul (X ^ K) ρ (natDegree_X_pow_le _) hρ, reflect_monomial,
    revAt_le (le_refl _), Nat.sub_self, pow_zero, one_mul]

/-- **The polynomial heart of [Stacks, Tag 0EVJ].**  Suppose `X ^ K * (β X ^ m - ρ)` is a
multiple of the linear form `f₂ - f₁ X`, with `K ≥ 1` and `deg ρ ≤ m`.  Then there is a constant
`a` with `β ≡ a` modulo `f₂ - f₁ X` and `reflect m ρ ≡ a` modulo `f₁ - f₂ X`.

The constant is `β` minus `f₂ - f₁X` times the part of the cofactor in degrees `≥ K + m`: that
difference is `X ^ K ρ` plus `f₂-f₁X` times the low part of the cofactor, divided by `X ^ (K+m)`,
and both summands have degree at most `K + m`, so the quotient is a constant.  Reversing that
identity at `K + m` turns `X ^ K ρ` into `reflect m ρ` and `f₂ - f₁X` into `f₂X - f₁`, which is
the second congruence. -/
theorem exists_const_of_reflect_glue (f₁ f₂ : A) (β ρ : Polynomial A) (m K : ℕ) (hK : 1 ≤ K)
    (hρ : ρ.natDegree ≤ m) (W : Polynomial A)
    (hW : X ^ K * (β * X ^ m - ρ) = (C f₂ - C f₁ * X) * W) :
    ∃ (a : A) (q V : Polynomial A),
      β - C a = (C f₂ - C f₁ * X) * q ∧
      reflect m ρ - C a = (C f₁ - C f₂ * X) * V := by
  obtain ⟨j, hj⟩ : ∃ j, K + m = 1 + j := ⟨K + m - 1, by omega⟩
  obtain ⟨q, r, hWsplit, hr⟩ := exists_X_pow_mul_add_eq (K + m) W
  obtain ⟨α, hα⟩ : ∃ α : Polynomial A, α = β - (C f₂ - C f₁ * X) * q := ⟨_, rfl⟩
  have hL1 : (C f₂ - C f₁ * X : Polynomial A).natDegree ≤ 1 := natDegree_sub_C_mul_X_le f₂ f₁
  have hstar : X ^ (K + m) * α = X ^ K * ρ + (C f₂ - C f₁ * X) * r := by
    have hLW : (C f₂ - C f₁ * X) * (X ^ (K + m) * q + r)
        = X ^ (K + m) * β - X ^ K * ρ := by
      rw [← hWsplit, ← hW]; ring
    rw [hα]; linear_combination -hLW
  have hrdeg : r.natDegree ≤ j :=
    natDegree_le_iff_coeff_eq_zero.mpr fun N hN => hr N (by omega)
  have hdegstar : (X ^ (K + m) * α).natDegree ≤ K + m := by
    rw [hstar]
    refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
    · exact le_trans natDegree_mul_le (by
        have := natDegree_X_pow_le (R := A) K; omega)
    · exact le_trans natDegree_mul_le (by omega)
  have hconst : α.natDegree ≤ 0 :=
    natDegree_le_iff_coeff_eq_zero.mpr fun N hN => by
      have h := (natDegree_le_iff_coeff_eq_zero.mp hdegstar) (N + (K + m)) (by omega)
      rwa [coeff_X_pow_mul] at h
  obtain ⟨a, ha⟩ : ∃ a : A, α = C a := ⟨α.coeff 0, eq_C_of_natDegree_le_zero hconst⟩
  rw [ha] at hstar
  refine ⟨a, q, reflect j r, by rw [← ha, hα]; ring, ?_⟩
  have e1 : reflect (K + m) (X ^ (K + m) * C a) = C a :=
    (reflect_X_pow_mul_add (K + m) 0 (by simp)).trans ((reflect_C a 0).trans (by simp))
  have e3 : reflect (K + m) ((C f₂ - C f₁ * X) * r)
      = (C f₂ * X - C f₁) * reflect j r := by
    rw [hj, reflect_mul _ _ hL1 hrdeg, reflect_one_sub_C_mul_X]
  have hre := congrArg (reflect (K + m)) hstar
  rw [e1, reflect_add, reflect_X_pow_mul_add K m hρ, e3] at hre
  rw [hre]; ring

/-! ### Splitting a binary form of even degree between the two charts -/

/-- A monomial in two variables is homogeneous of its total degree. -/
theorem monomial_two_mem (a b : ℕ) :
    (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b : MvPolynomial (Fin 2) A) ∈
      MvPolynomial.homogeneousSubmodule (Fin 2) A (a + b) := by
  refine (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
    (MvPolynomial.IsHomogeneous.mul ?_ ?_)
  · simpa using (MvPolynomial.isHomogeneous_X A (0 : Fin 2)).pow a
  · simpa using (MvPolynomial.isHomogeneous_X A (1 : Fin 2)).pow b

/-- A monomial in two variables is homogeneous of any degree equal to its total degree. -/
theorem monomial_two_mem_of_add_eq {a b c : ℕ} (h : a + b = c) :
    (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b : MvPolynomial (Fin 2) A) ∈
      MvPolynomial.homogeneousSubmodule (Fin 2) A c :=
  h ▸ monomial_two_mem a b

/-- **Every binary form of degree `2n` is `T₁ⁿ` times a form of degree `n` plus `T₀ⁿ` times a form
of degree `n`.**  Each monomial `T₀ⁱT₁ʲ` with `i + j = 2n` has `j ≥ n` or `i ≥ n`, so it is
divisible by `T₁ⁿ` or by `T₀ⁿ`.

This is why the two standard charts already generate the functions on their overlap, and hence
why `H¹(X', 𝒪_{X'})` vanishes. -/
theorem exists_isHomogeneous_X_one_pow_mul_add (n : ℕ) {P : MvPolynomial (Fin 2) A}
    (hP : P.IsHomogeneous (n * 2)) :
    ∃ Q₀ Q₁ : MvPolynomial (Fin 2) A, Q₀.IsHomogeneous n ∧ Q₁.IsHomogeneous n ∧
      P = MvPolynomial.X 1 ^ n * Q₀ + MvPolynomial.X 0 ^ n * Q₁ := by
  classical
  obtain ⟨d, hd⟩ : ∃ d, d = n * 2 := ⟨_, rfl⟩
  rw [← hd] at hP
  set a : ℕ → A := fun j => P.coeff (MvPolynomial.binaryExponent d j) with ha
  have hPsum := MvPolynomial.eq_sum_binaryMonomial d P hP
  refine ⟨∑ j ∈ (Finset.range (d + 1)).filter (fun j => n ≤ j),
      a j • (MvPolynomial.X 0 ^ (d - j) * MvPolynomial.X 1 ^ (j - n)),
    ∑ j ∈ (Finset.range (d + 1)).filter (fun j => ¬ n ≤ j),
      a j • (MvPolynomial.X 0 ^ (n - j) * MvPolynomial.X 1 ^ j), ?_, ?_, ?_⟩
  · refine (MvPolynomial.mem_homogeneousSubmodule _ _).mp
      (Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_)
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    exact monomial_two_mem_of_add_eq (by omega)
  · refine (MvPolynomial.mem_homogeneousSubmodule _ _).mp
      (Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_)
    simp only [Finset.mem_filter, Finset.mem_range, not_le] at hj
    exact monomial_two_mem_of_add_eq (by omega)
  · have h₀ : ∀ j ∈ (Finset.range (d + 1)).filter (fun j => n ≤ j),
        MvPolynomial.X 1 ^ n * (a j • (MvPolynomial.X 0 ^ (d - j) * MvPolynomial.X 1 ^ (j - n)))
          = a j • MvPolynomial.binaryMonomial A d j := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj
      rw [mul_smul_comm, MvPolynomial.binaryMonomial]
      congr 1
      calc (MvPolynomial.X 1 ^ n * (MvPolynomial.X 0 ^ (d - j) * MvPolynomial.X 1 ^ (j - n))
              : MvPolynomial (Fin 2) A)
          = MvPolynomial.X 0 ^ (d - j) * MvPolynomial.X 1 ^ (n + (j - n)) := by
            rw [pow_add]; ring
        _ = MvPolynomial.X 0 ^ (d - j) * MvPolynomial.X 1 ^ j := by
            rw [show n + (j - n) = j from by omega]
    have h₁ : ∀ j ∈ (Finset.range (d + 1)).filter (fun j => ¬ n ≤ j),
        MvPolynomial.X 0 ^ n * (a j • (MvPolynomial.X 0 ^ (n - j) * MvPolynomial.X 1 ^ j))
          = a j • MvPolynomial.binaryMonomial A d j := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_range, not_le] at hj
      rw [mul_smul_comm, MvPolynomial.binaryMonomial]
      congr 1
      calc (MvPolynomial.X 0 ^ n * (MvPolynomial.X 0 ^ (n - j) * MvPolynomial.X 1 ^ j)
              : MvPolynomial (Fin 2) A)
          = MvPolynomial.X 0 ^ (n + (n - j)) * MvPolynomial.X 1 ^ j := by
            rw [pow_add]; ring
        _ = MvPolynomial.X 0 ^ (d - j) * MvPolynomial.X 1 ^ j := by
            rw [show n + (n - j) = d - j from by omega]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_congr rfl h₀, Finset.sum_congr rfl h₁,
      Finset.sum_filter_add_sum_filter_not]
    exact hPsum

/-! ### Dehomogenizing at `T₁` over a commutative ring

Dehomogenizing at `T₁` is evaluation at `T₀ = X`, `T₁ = 1`, the map
`MvPolynomial.aeval ![X, 1]` that `Polynomial.homogenize` is a section of on each graded piece.
Nothing below uses inverses, so `A` is an arbitrary commutative ring. -/

/-- Dehomogenizing a form of degree `n` at `T₁` cannot raise the degree above `n`. -/
theorem natDegree_aeval_X_one_le {n : ℕ} {g : MvPolynomial (Fin 2) A} (hg : g.IsHomogeneous n) :
    (MvPolynomial.aeval ![X, (1 : Polynomial A)] g).natDegree ≤ n := by
  classical
  rw [g.as_sum, map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun v hv => ?_
  have hvn : n = ∑ i ∈ v.support, v i := hg.degree_eq_sum_deg_support hv
  have hv0 : v 0 ≤ n := by
    rw [hvn]
    by_cases h : v 0 = 0
    · simp [h]
    · exact Finset.single_le_sum (f := fun i => v i) (fun _ _ => Nat.zero_le _)
        (Finsupp.mem_support_iff.mpr h)
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ fun i => pow_zero _,
    Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, mul_one]
  refine le_trans Polynomial.natDegree_mul_le ?_
  simp only [Polynomial.algebraMap_eq, Polynomial.natDegree_C, zero_add]
  exact (Polynomial.natDegree_X_pow_le _).trans hv0

/-- Dehomogenizing at `T₁` is injective on forms of a fixed degree. -/
theorem eq_of_aeval_X_one_eq {n : ℕ} {g h : MvPolynomial (Fin 2) A} (hg : g.IsHomogeneous n)
    (hh : h.IsHomogeneous n)
    (hgh : MvPolynomial.aeval ![X, (1 : Polynomial A)] g =
      MvPolynomial.aeval ![X, (1 : Polynomial A)] h) : g = h := by
  rw [← Polynomial.homogenize_eq_of_isHomogeneous hg rfl,
    ← Polynomial.homogenize_eq_of_isHomogeneous hh rfl, hgh]

/-! ### The relation ideal of the two-generator square -/

/-- The homogeneous relation `f₂T₀ - f₁T₁` of the two-generator square. -/
def relationForm (A : Type u) [CommRing A] (f₁ f₂ : A) : MvPolynomial (Fin 2) A :=
  MvPolynomial.C f₂ * MvPolynomial.X 0 - MvPolynomial.C f₁ * MvPolynomial.X 1

/-- The relation ideal is the principal ideal generated by `relationForm A f₁ f₂`. -/
theorem relationIdeal_eq_span_relationForm (A : Type u) [CommRing A] (f₁ f₂ : A) :
    relationIdeal A f₁ f₂ = Ideal.span {relationForm A f₁ f₂} := rfl

/-- The relation `f₂T₀ - f₁T₁` is homogeneous of degree `1`. -/
theorem isHomogeneous_relationForm (f₁ f₂ : A) :
    (relationForm A f₁ f₂).IsHomogeneous 1 :=
  (MvPolynomial.mem_homogeneousSubmodule 1 _).mp (relation_mem_homogeneousSubmodule A f₁ f₂)

/-- Dehomogenizing the relation at `T₁` gives the linear form `f₂X - f₁`. -/
theorem dehomogenize_relationForm (f₁ f₂ : A) :
    MvPolynomial.aeval ![X, (1 : Polynomial A)] (relationForm A f₁ f₂) = C f₂ * X - C f₁ := by
  simp [relationForm, Polynomial.algebraMap_eq]

/-- A form lies in the relation ideal as soon as it is the relation times a form. -/
theorem mem_relationIdeal_of_eq_mul (f₁ f₂ : A) {Z Q : MvPolynomial (Fin 2) A}
    (h : Z = relationForm A f₁ f₂ * Q) : Z ∈ relationIdeal A f₁ f₂ :=
  Ideal.mem_span_singleton'.mpr ⟨Q, by rw [h, relationForm]; ring⟩

/-- A form of degree `N` whose dehomogenization at `T₁` is the dehomogenization of the relation
times a polynomial of degree at most `N - 1` lies in the relation ideal. -/
theorem mem_relationIdeal_of_dehomogenize_eq (f₁ f₂ : A) {N : ℕ} (hN : 1 ≤ N)
    {Z : MvPolynomial (Fin 2) A} (hZ : Z.IsHomogeneous N) {c : Polynomial A}
    (hc : c.natDegree ≤ N - 1)
    (h : MvPolynomial.aeval ![X, (1 : Polynomial A)] Z = (C f₂ * X - C f₁) * c) :
    Z ∈ relationIdeal A f₁ f₂ := by
  refine mem_relationIdeal_of_eq_mul f₁ f₂ (Q := c.homogenize (N - 1)) ?_
  refine eq_of_aeval_X_one_eq hZ ?_ ?_
  · have h1 : ((relationForm A f₁ f₂) * c.homogenize (N - 1)).IsHomogeneous (1 + (N - 1)) :=
      (isHomogeneous_relationForm f₁ f₂).mul (Polynomial.isHomogeneous_homogenize c)
    rwa [show 1 + (N - 1) = N by omega] at h1
  · rw [map_mul, dehomogenize_relationForm, Polynomial.aeval_homogenize_X_one _ hc, h]

/-- **Tag 0EVJ on forms.**  Let `P₀` and `P₁` be forms of degrees `n` and `m` whose chart
fractions `P₀/T₀ⁿ` and `P₁/T₁ᵐ` agree on the overlap of the two standard charts — which is the
displayed membership, after clearing denominators.  Then there is one constant `a` such that
`P₀/T₀ⁿ` and `P₁/T₁ᵐ` are both the constant `a`, on their respective charts. -/
theorem exists_const_of_relationForm_mem (f₁ f₂ : A) {n m p q : ℕ} (hp : 1 ≤ p)
    {P₀ P₁ : MvPolynomial (Fin 2) A} (hP₀ : P₀.IsHomogeneous n) (hP₁ : P₁.IsHomogeneous m)
    (hrel : MvPolynomial.X 0 ^ p * MvPolynomial.X 1 ^ q *
        (MvPolynomial.X 1 ^ m * P₀ - MvPolynomial.X 0 ^ n * P₁) ∈ relationIdeal A f₁ f₂) :
    ∃ (a : A) (j : ℕ),
      MvPolynomial.X 0 ^ j * P₀ - MvPolynomial.C a * MvPolynomial.X 0 ^ (j + n)
        ∈ relationIdeal A f₁ f₂ ∧
      MvPolynomial.X 1 ^ j * P₁ - MvPolynomial.C a * MvPolynomial.X 1 ^ (j + m)
        ∈ relationIdeal A f₁ f₂ := by
  obtain ⟨W, hW⟩ := Ideal.mem_span_singleton'.mp hrel
  have hW' : W * relationForm A f₁ f₂ = MvPolynomial.X 0 ^ p * MvPolynomial.X 1 ^ q *
      (MvPolynomial.X 1 ^ m * P₀ - MvPolynomial.X 0 ^ n * P₁) := hW
  have hdeh := congrArg (MvPolynomial.aeval ![X, (1 : Polynomial A)]) hW'
  simp only [map_mul, map_sub, map_pow, dehomogenize_relationForm,
    MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, one_mul,
    mul_one] at hdeh
  have hpoly : X ^ p * (MvPolynomial.aeval ![X, (1 : Polynomial A)] P₁ * X ^ n
      - MvPolynomial.aeval ![X, (1 : Polynomial A)] P₀)
      = (C f₁ - C f₂ * X) * MvPolynomial.aeval ![X, (1 : Polynomial A)] W := by
    linear_combination hdeh
  obtain ⟨a, q', V, h₁, h₀⟩ := exists_const_of_reflect_glue f₂ f₁
    (MvPolynomial.aeval ![X, (1 : Polynomial A)] P₁)
    (MvPolynomial.aeval ![X, (1 : Polynomial A)] P₀) n p hp
    (natDegree_aeval_X_one_le hP₀) (MvPolynomial.aeval ![X, (1 : Polynomial A)] W) hpoly
  obtain ⟨j, hjq, hjV, hj1⟩ : ∃ j : ℕ, q'.natDegree ≤ j - 1 ∧ V.natDegree ≤ j - 1 ∧ 1 ≤ j :=
    ⟨max q'.natDegree V.natDegree + 1, by omega, by omega, by omega⟩
  have hhom : ∀ (i : Fin 2) (P : MvPolynomial (Fin 2) A) (e : ℕ), P.IsHomogeneous e →
      (MvPolynomial.X i ^ j * P - MvPolynomial.C a * MvPolynomial.X i ^ (j + e)).IsHomogeneous
        (j + e) := fun i P e hP => by
    have hXpow : ∀ e : ℕ,
        ((MvPolynomial.X i : MvPolynomial (Fin 2) A) ^ e).IsHomogeneous e := fun e => by
      simpa using (MvPolynomial.isHomogeneous_X A i).pow e
    refine MvPolynomial.IsHomogeneous.sub ((hXpow j).mul hP) ?_
    simpa using (MvPolynomial.isHomogeneous_C (Fin 2) a).mul (hXpow (j + e))
  refine ⟨a, j, ?_, ?_⟩
  · -- the chart `D₊(T₀)`, reached after one reversal
    have hdh : MvPolynomial.aeval ![X, (1 : Polynomial A)] (MvPolynomial.X 0 ^ j * P₀
          - MvPolynomial.C a * MvPolynomial.X 0 ^ (j + n))
        = X ^ j * MvPolynomial.aeval ![X, (1 : Polynomial A)] P₀ - C a * X ^ (j + n) := by
      simp [Polynomial.algebraMap_eq]
    obtain ⟨N1, hN1, hNsum⟩ : ∃ N1 : ℕ, V.natDegree ≤ N1 ∧ j + n = 1 + N1 :=
      ⟨j + n - 1, by omega, by omega⟩
    have hVdeg : (reflect N1 V).natDegree ≤ N1 :=
      le_trans natDegree_reflect_le (max_le (le_refl _) hN1)
    refine mem_relationIdeal_of_dehomogenize_eq f₁ f₂ (by omega) (hhom 0 P₀ n hP₀)
      (le_trans hVdeg (by omega)) ?_
    rw [hdh]
    have hrefl : reflect (j + n)
        (X ^ j * MvPolynomial.aeval ![X, (1 : Polynomial A)] P₀ - C a * X ^ (j + n))
        = (C f₂ - C f₁ * X) * V := by
      rw [reflect_sub, reflect_X_pow_mul_add j n (natDegree_aeval_X_one_le hP₀),
        reflect_C_mul, reflect_monomial, revAt_le (le_refl _), Nat.sub_self, pow_zero, mul_one]
      exact h₀
    have hrefl' : reflect (j + n) ((C f₂ * X - C f₁) * reflect N1 V)
        = (C f₂ - C f₁ * X) * V := by
      rw [hNsum, reflect_mul _ _ (natDegree_C_mul_X_sub_C_le f₂ f₁) hVdeg,
        reflect_one_C_mul_X_sub_C, reflect_reflect]
    have := congrArg (reflect (j + n)) (hrefl.trans hrefl'.symm)
    rwa [reflect_reflect, reflect_reflect] at this
  · -- the chart `D₊(T₁)`, where dehomogenization applies directly
    have hdh : MvPolynomial.aeval ![X, (1 : Polynomial A)] (MvPolynomial.X 1 ^ j * P₁
          - MvPolynomial.C a * MvPolynomial.X 1 ^ (j + m))
        = MvPolynomial.aeval ![X, (1 : Polynomial A)] P₁ - C a := by
      simp [Polynomial.algebraMap_eq]
    have hqdeg : (-q').natDegree ≤ j + m - 1 := by
      rw [natDegree_neg]; omega
    refine mem_relationIdeal_of_dehomogenize_eq f₁ f₂ (by omega) (hhom 1 P₁ m hP₁) hqdeg ?_
    rw [hdh, h₁]; ring

end Stacks.AlmostBlowUp

end
