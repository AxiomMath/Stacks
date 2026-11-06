module

import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Topology.Sheaves.Presheaf

public import StacksFrontier.RingTheory.HilbertFunction
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Hilbert functions over a Noetherian local ring are numerical polynomials

Let `(R, 𝔪)` be a Noetherian local ring, let `I ⊆ R` be an ideal of definition and let `M` be a
finite `R`-module. This file proves that the two functions

  `φ_{I,M}(n) = length_R (I ^ n M / I ^ (n + 1) M)`  and
  `χ_{I,M}(n) = length_R (M / I ^ (n + 1) M)`

take finite values and are numerical polynomials, i.e. agree for `n ≫ 0` with a `ℤ`-linear
combination of the binomial coefficients `n choose i`.

Finiteness of the values is Hopkins–Levitzki: `𝔪 ^ k ⊆ I` for some `k`, so each of the two
modules is a finite module annihilated by a power of `I`, hence a finite module over an Artinian
quotient of `R`, hence of finite length.

For `φ_{I,M}` fix `t` with `𝔪 ^ t ⊆ I` and, for a submodule `N ⊆ M`, put
`P_N(d) = I ^ d N + I ^ (d + 1) M`. Then `P_⊤(d) = I ^ d M` and `P_{𝔪 ^ t M}(d) = I ^ (d + 1) M`,
so `φ_{I,M}(d)` is the length of `P_⊤(d) / P_{𝔪 ^ t M}(d)`. Additivity of length refines that
along any chain `⊤ = N_0 ⊇ ⋯ ⊇ N_u = 𝔪 ^ t M`, and refining `𝔪 ^ i M ⊇ 𝔪 ^ (i + 1) M` one
generator at a time reduces the claim to a *cyclic* step: `N = Rν + N'` with `𝔪 ν ⊆ N'`.

A cyclic step is Hilbert–Serre over the residue field. Write `I = (x_1, …, x_s)` and
`k = R/𝔪`. Every `P_N(d) / P_{N'}(d)` is killed by `𝔪`, and evaluation `f ↦ f(x) ν` carries the
homogeneous polynomials of degree `d` onto `I ^ d Rν`, hence onto `P_N(d) / P_{N'}(d)`; the
degree-`d` kernels span a homogeneous ideal containing every polynomial with coefficients in
`𝔪`, so they descend to the graded pieces of a homogeneous ideal `J ⊆ k[X_1, …, X_s]`. Thus
`length_R (P_N(d) / P_{N'}(d)) = dim_k (k[X_1, …, X_s]/J)_d`, which is a numerical polynomial.

For `χ_{I,M}` the argument is a difference argument: additivity of length along
`I ^ (n + 1) M ⊆ I ^ n M ⊆ M` gives `χ_{I,M}(n + 1) - χ_{I,M}(n) = φ_{I,M}(n + 1)`, and a
function whose forward difference is a numerical polynomial is a numerical polynomial.

## Main results

* `Stacks.HilbertFunction.NumericalPoly.solution`: the statement of Stacks Tag 00K8.

## Implementation notes

`IsNumericalPoly` is the source's notion of numerical polynomial (Tag 00JX) for the abelian
group `ℤ`, written for a function `ℕ → ℤ`; it is private to this file, as is the whole calculus
of numerical polynomials proved here: closure under a shift `f (n + 1)`, the padding of the
coefficient family that puts two numerical polynomials over a common `r`, and Tag 00JZ, that a
function whose forward difference is a numerical polynomial is one.

`length_quotient_eq_length_add_length_quotient` is additivity of length along a pair
`Q ≤ P ≤ M` of submodules, in the subquotient shape `↥P ⧸ Q.submoduleOf P` that the main
statement uses; it holds over any ring and for arbitrary lengths in `ℕ∞`.

The source proves the statement for `φ_{I,M}` in one step rather than through a chain: the
graded ring `S = ⨁_{d ≥ 0} I ^ d / I ^ (d + 1)` is Noetherian with `S₊` generated in degree one
and `N = ⨁_{d ≥ 0} I ^ d M / I ^ (d + 1) M` is a finite graded `S`-module, so `d ↦ [N_d]` is a
numerical polynomial with values in `K'₀(S_0) = K'₀(R/I)` (Tag 00K1), and the length
homomorphism of the Artinian ring `R/I` (Tag 00JD) carries it to `φ_{I,M}`. The route taken here
refines the filtration until the degree-zero part of the graded ring is the *field* `k = R/𝔪`,
which replaces `K'₀(R/I)` by `ℤ` and needs only Hilbert–Serre over a field, at the cost of the
two inductions (on a generating set of `𝔪 ^ i M`, and on `i`) that produce the chain.

## References

* [Stacks Project, Tag 00K8](https://stacks.math.columbia.edu/tag/00K8)
* [Stacks Project, Tag 00K3](https://stacks.math.columbia.edu/tag/00K3), Hilbert–Serre for a
  graded quotient of a polynomial ring over a field
* [Stacks Project, Tag 00JZ](https://stacks.math.columbia.edu/tag/00JZ), antidifferences of
  numerical polynomials
-/

namespace Polynomial

open Filter

/-- Two rational polynomials agreeing at all large natural numbers are equal: their difference
has infinitely many roots. -/
theorem eq_of_eventually_eval_natCast_eq {p q : ℚ[X]}
    (h : ∀ᶠ n : ℕ in atTop, p.eval (n : ℚ) = q.eval (n : ℚ)) : p = q := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  exact eq_of_infinite_eval_eq p q (Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => ((n + N : ℕ) : ℚ)) (fun a b hab => by simpa using hab)
    (fun n => hN _ (Nat.le_add_left N n)))

end Polynomial

namespace Stacks.HilbertFunction.NumericalPoly

open Filter Finset

/-! ### The binomial polynomials

Tag 00JX presents a numerical polynomial as an eventual `ℤ`-combination of binomial coefficients,
while Definition 00KA presents one by a rational polynomial computing it. `binomPoly i` is the
rational polynomial `X choose i`, and `binomSum r a` is the combination
`∑_{i ≤ r} a i (X choose i)` realizing such a presentation as an honest polynomial.
-/

section BinomialPoly

open Polynomial

/-- The rational polynomial `X choose i`, of degree `i`, whose value at a natural number `n` is
the binomial coefficient `n.choose i`. -/
@[sga "6 V 2.5"]
noncomputable def binomPoly (i : ℕ) : ℚ[X] :=
  C ((i.factorial : ℚ)⁻¹) * descPochhammer ℚ i

/-- The polynomial `binomPoly i` has degree `i`. -/
theorem binomPoly_degree (i : ℕ) : (binomPoly i).degree = i := by
  rw [binomPoly, degree_C_mul (by positivity),
    degree_eq_natDegree (monic_descPochhammer ℚ i).ne_zero, descPochhammer_natDegree]

/-- The value of `binomPoly i` at a natural number `n` is the binomial coefficient
`n.choose i`. -/
theorem binomPoly_eval (i n : ℕ) : (binomPoly i).eval (n : ℚ) = (n.choose i : ℚ) := by
  rw [binomPoly, eval_mul, eval_C, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- A `ℤ`-combination of `binomPoly i` for `i < k` has degree `< k`. -/
theorem degree_sum_binomPoly_lt (k : ℕ) (a : ℕ → ℤ) :
    (∑ i ∈ range k, C (a i : ℚ) * binomPoly i).degree < (k : WithBot ℕ) := by
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  refine Finset.sup_lt_iff (WithBot.bot_lt_coe k) |>.mpr fun i hi => ?_
  rcases eq_or_ne (a i) 0 with h | h
  · simp [h]
  · rw [degree_C_mul (Int.cast_ne_zero.mpr h), binomPoly_degree]
    exact Nat.cast_lt.mpr (mem_range.mp hi)

/-- The rational polynomial `∑_{i ≤ r} a i (X choose i)`. -/
noncomputable def binomSum (r : ℕ) (a : ℕ → ℤ) : ℚ[X] :=
  ∑ i ∈ range (r + 1), C (a i : ℚ) * binomPoly i

/-- The value of `binomSum r a` at a natural number `n` is the integer
`∑_{i ≤ r} (n choose i) * a i`. -/
theorem binomSum_eval (r : ℕ) (a : ℕ → ℤ) (n : ℕ) :
    (binomSum r a).eval (n : ℚ) = ((∑ i ∈ range (r + 1), (n.choose i : ℤ) * a i : ℤ) : ℚ) := by
  simp only [binomSum, eval_finsetSum, eval_mul, eval_C, binomPoly_eval, Int.cast_sum,
    Int.cast_mul]
  exact Finset.sum_congr rfl fun i _ => by push_cast; ring

/-- If the top coefficient `a r` is nonzero, then `binomSum r a` has degree exactly `r`. -/
theorem binomSum_degree (r : ℕ) (a : ℕ → ℤ) (h : a r ≠ 0) : (binomSum r a).degree = r := by
  rw [binomSum, Finset.sum_range_succ, degree_add_eq_right_of_degree_lt,
    degree_C_mul (Int.cast_ne_zero.mpr h), binomPoly_degree]
  rw [degree_C_mul (Int.cast_ne_zero.mpr h), binomPoly_degree]
  exact degree_sum_binomPoly_lt r a

end BinomialPoly

/-- The maximal ideal of a local ring is its own radical, being prime. -/
theorem radical_maximalIdeal (R : Type*) [CommRing R] [IsLocalRing R] :
    (IsLocalRing.maximalIdeal R).radical = IsLocalRing.maximalIdeal R :=
  ((IsLocalRing.maximalIdeal.isMaximal R).isPrime).radical

/-! ### Numerical polynomials -/

/-- A function `f : ℕ → ℤ` is a *numerical polynomial* if there are `r ∈ ℕ` and integers
`a 0, …, a r` with `f n = ∑ i ≤ r, (n choose i) * a i` for all `n ≫ 0`. This is the source's
Tag 00JX for the abelian group `ℤ`. -/
private def IsNumericalPoly (f : ℕ → ℤ) : Prop :=
  ∃ (r : ℕ) (a : ℕ → ℤ), ∀ᶠ n : ℕ in atTop,
    f n = ∑ i ∈ range (r + 1), (n.choose i : ℤ) * a i

private lemma IsNumericalPoly.congr {f g : ℕ → ℤ} (h : IsNumericalPoly f)
    (hfg : ∀ᶠ n : ℕ in atTop, g n = f n) : IsNumericalPoly g := by
  obtain ⟨r, a, ha⟩ := h
  exact ⟨r, a, (ha.and hfg).mono fun n hn => hn.2.trans hn.1⟩

/-- Padding a coefficient family with zeros does not change the associated combination of
binomial coefficients. -/
private lemma sum_choose_mul_pad {r r' : ℕ} (h : r ≤ r') (a : ℕ → ℤ) (n : ℕ) :
    ∑ i ∈ range (r' + 1), (n.choose i : ℤ) * (if i ≤ r then a i else 0)
      = ∑ i ∈ range (r + 1), (n.choose i : ℤ) * a i := by
  have hsub : range (r + 1) ⊆ range (r' + 1) := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have hzero : ∀ x ∈ range (r' + 1), x ∉ range (r + 1) →
      (n.choose x : ℤ) * (if x ≤ r then a x else 0) = 0 := by
    intro x _ hx
    have hxr : ¬ x ≤ r := by
      simp only [Finset.mem_range, not_lt] at hx
      omega
    simp [hxr]
  rw [← Finset.sum_subset hsub hzero]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hir : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  simp [hir]

private lemma IsNumericalPoly.zero : IsNumericalPoly (fun _ => (0 : ℤ)) :=
  ⟨0, 0, Filter.Eventually.of_forall fun n => by simp⟩

private lemma IsNumericalPoly.add {f g : ℕ → ℤ} (hf : IsNumericalPoly f)
    (hg : IsNumericalPoly g) : IsNumericalPoly fun n => f n + g n := by
  obtain ⟨r₁, a, ha⟩ := hf
  obtain ⟨r₂, b, hb⟩ := hg
  refine ⟨max r₁ r₂, fun i => (if i ≤ r₁ then a i else 0) + (if i ≤ r₂ then b i else 0), ?_⟩
  filter_upwards [ha, hb] with n hna hnb
  rw [hna, hnb, ← sum_choose_mul_pad (le_max_left r₁ r₂) a n,
    ← sum_choose_mul_pad (le_max_right r₁ r₂) b n, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Pascal's rule, summed: the combination of the `(n + 1) choose i` for `i ≤ r` rewritten as a
combination of the `n choose i` for `i ≤ r`. -/
private lemma sum_choose_succ_mul (n : ℕ) (a : ℕ → ℤ) (r : ℕ) :
    ∑ i ∈ range (r + 1), ((n + 1).choose i : ℤ) * a i
      = (∑ i ∈ range (r + 1), (n.choose i : ℤ) * (a i + a (i + 1)))
        - (n.choose r : ℤ) * a (r + 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ (fun i => ((n + 1).choose i : ℤ) * a i) (r + 1),
      Finset.sum_range_succ (fun i => (n.choose i : ℤ) * (a i + a (i + 1))) (r + 1), ih]
    have h := Nat.choose_succ_succ n r
    push_cast [h]
    ring

private lemma IsNumericalPoly.shift {f : ℕ → ℤ} (h : IsNumericalPoly f) :
    IsNumericalPoly fun n => f (n + 1) := by
  obtain ⟨r, a, ha⟩ := h
  obtain ⟨N, hN⟩ := eventually_atTop.mp ha
  refine ⟨r, fun i => (if i ≤ r then a i else 0) + (if i + 1 ≤ r then a (i + 1) else 0),
    eventually_atTop.mpr ⟨N, fun n hn => ?_⟩⟩
  show f (n + 1) = ∑ i ∈ range (r + 1), (n.choose i : ℤ) *
    ((if i ≤ r then a i else 0) + (if i + 1 ≤ r then a (i + 1) else 0))
  have hA : ∀ i ∈ range (r + 1), ((n + 1).choose i : ℤ) * a i
      = ((n + 1).choose i : ℤ) * (if i ≤ r then a i else 0) := fun i hi => by
    have hir : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    simp [hir]
  have hlast : ¬ r + 1 ≤ r := by omega
  rw [hN (n + 1) (by omega), Finset.sum_congr rfl hA,
    sum_choose_succ_mul n (fun i => if i ≤ r then a i else 0) r]
  simp [hlast]

/-- A function with vanishing forward difference from `N` on is constant from `N` on. -/
private lemma eq_of_forwardDifference_eq_zero {g : ℕ → ℤ} {N : ℕ}
    (h : ∀ n, N ≤ n → g (n + 1) = g n) : ∀ n, N ≤ n → g n = g N := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction m with
  | zero => simp
  | succ m ih => rw [show N + (m + 1) = (N + m) + 1 from by omega, h _ (by omega), ih]

/-- **Stacks 00JZ** for `A = ℤ`: a function whose forward difference is a numerical polynomial
is a numerical polynomial. -/
private lemma IsNumericalPoly.of_forwardDifference {f : ℕ → ℤ}
    (h : IsNumericalPoly fun n => f (n + 1) - f n) : IsNumericalPoly f := by
  obtain ⟨r, a, ha⟩ := h
  obtain ⟨N, hN⟩ := eventually_atTop.mp ha
  have hFdiff : ∀ n : ℕ, (∑ i ∈ range (r + 1), (((n + 1).choose (i + 1) : ℤ) * a i))
        - (∑ i ∈ range (r + 1), ((n.choose (i + 1) : ℤ) * a i))
      = ∑ i ∈ range (r + 1), (n.choose i : ℤ) * a i := by
    intro n
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hp := Nat.choose_succ_succ n i
    push_cast [hp]
    ring
  have hstep : ∀ n : ℕ, N ≤ n →
      f (n + 1) - ∑ i ∈ range (r + 1), (((n + 1).choose (i + 1) : ℤ) * a i)
        = f n - ∑ i ∈ range (r + 1), ((n.choose (i + 1) : ℤ) * a i) := by
    intro n hn
    have h1 : f (n + 1) - f n = ∑ i ∈ range (r + 1), (n.choose i : ℤ) * a i := hN n hn
    have h2 := hFdiff n
    linarith
  have key := eq_of_forwardDifference_eq_zero
    (g := fun n => f n - ∑ i ∈ range (r + 1), ((n.choose (i + 1) : ℤ) * a i)) hstep
  refine ⟨r + 1, Function.update (fun j : ℕ => a (j - 1)) 0
      (f N - ∑ i ∈ range (r + 1), ((N.choose (i + 1) : ℤ) * a i)),
    eventually_atTop.mpr ⟨N, fun n hn => ?_⟩⟩
  have hn' : f n - ∑ i ∈ range (r + 1), ((n.choose (i + 1) : ℤ) * a i)
      = f N - ∑ i ∈ range (r + 1), ((N.choose (i + 1) : ℤ) * a i) := key n hn
  have e1 : ∀ i ∈ range (r + 1), (n.choose (i + 1) : ℤ) *
      Function.update (fun j : ℕ => a (j - 1)) 0
        (f N - ∑ i ∈ range (r + 1), ((N.choose (i + 1) : ℤ) * a i)) (i + 1)
      = (n.choose (i + 1) : ℤ) * a i := fun i _ => by
    rw [Function.update_of_ne (Nat.succ_ne_zero i), Nat.succ_sub_one]
  rw [Finset.sum_range_succ', Finset.sum_congr rfl e1, Function.update_self,
    Nat.choose_zero_right, Nat.cast_one, one_mul]
  linarith

/-- Tag 00K3's `ℕ`-indexed numerical polynomials are numerical polynomials in the sense used
here: the two differ only in indexing the coefficient family by `Fin (r + 1)` rather than by `ℕ`.
-/
private lemma isNumericalPoly_of_byNaturalArgs {f : ℕ → ℤ}
    (h : Stacks.HilbertFunction.PolynomialQuotient.IsNumericalPolynomialByNaturalArgs f) :
      IsNumericalPoly f := by
  obtain ⟨r, a, ha⟩ := h
  refine ⟨r, fun i => if hi : i < r + 1 then a ⟨i, hi⟩ else 0, ha.mono fun n hn => ?_⟩
  rw [hn, ← Fin.sum_univ_eq_sum_range
    (fun i => (n.choose i : ℤ) * (if hi : i < r + 1 then a ⟨i, hi⟩ else 0)) (r + 1)]
  exact Finset.sum_congr rfl fun i _ => by simp [i.isLt]

/-! ### Finiteness of the lengths -/

/-- If the radical of `I` is the maximal ideal, every power `R ⧸ I ^ k` (`k ≠ 0`) is Artinian. -/
private lemma isArtinianRing_quotient_pow {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {I : Ideal R} (hI : I.radical = IsLocalRing.maximalIdeal R) {k : ℕ}
    (hk : k ≠ 0) : IsArtinianRing (R ⧸ I ^ k) := by
  refine IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ ⟨⟨?_, ?_⟩, ?_⟩
  · exact (IsLocalRing.maximalIdeal.isMaximal R).isPrime
  · calc I ^ k ≤ I := Ideal.pow_le_self hk
      _ ≤ I.radical := Ideal.le_radical
      _ = _ := hI
  · rintro q ⟨hq, hqle⟩ -
    rw [← hI, ← Ideal.radical_pow I hk]
    exact hq.radical_le_iff.mpr hqle

/-- A finite module annihilated by an ideal with Artinian quotient has finite length. -/
private lemma length_ne_top_of_smul_top_eq_bot {R : Type*} [CommRing R] [IsNoetherianRing R]
    {J : Ideal R} (hJ : IsArtinianRing (R ⧸ J)) {N : Type*} [AddCommGroup N] [Module R N]
    [Module.Finite R N] (h : J • (⊤ : Submodule R N) = ⊥) : Module.length R N ≠ ⊤ := by
  have h1 : Module.Finite (R ⧸ J) (N ⧸ (J • ⊤ : Submodule R N)) :=
    Module.Finite.of_restrictScalars_finite R _ _
  have h2 : IsArtinian R (N ⧸ (J • ⊤ : Submodule R N)) :=
    isArtinian_of_surjective_algebraMap (R := R ⧸ J) (S := R) Ideal.Quotient.mk_surjective
  have h3 : Module.length R (N ⧸ (J • ⊤ : Submodule R N)) ≠ ⊤ := Module.length_ne_top
  rwa [(Submodule.quotEquivOfEqBot _ h).length_eq] at h3

/-- An ideal annihilates the quotient by any submodule containing its product with the module. -/
private lemma smul_top_quotient_eq_bot {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N]
    [Module R N] (J : Ideal R) (P : Submodule R N) (h : J • (⊤ : Submodule R N) ≤ P) :
    J • (⊤ : Submodule R (N ⧸ P)) = ⊥ := by
  rw [eq_bot_iff, Submodule.smul_le]
  intro a ha x _
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective P x
  rw [Submodule.mem_bot, ← LinearMap.map_smul, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  exact h (Submodule.smul_mem_smul ha trivial)

/-- `I` carries `I ^ n M` into `I ^ (n + 1) M`. -/
private lemma smul_top_le_submoduleOf {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] (I : Ideal R) (n : ℕ) :
    I • (⊤ : Submodule R ↥(I ^ n • (⊤ : Submodule R M)))
      ≤ (I ^ (n + 1) • (⊤ : Submodule R M)).submoduleOf (I ^ n • ⊤) := by
  rw [Submodule.smul_le]
  intro a ha y _
  have hy : (y : M) ∈ I ^ n • (⊤ : Submodule R M) := y.2
  have h2 : a • (y : M) ∈ I ^ (n + 1) • (⊤ : Submodule R M) := by
    have h3 := Submodule.smul_mem_smul (N := (I ^ n • (⊤ : Submodule R M))) ha hy
    rwa [← Submodule.mul_smul, ← pow_succ'] at h3
  exact h2

/-! ### Additivity of length in a subquotient -/

/-- The subquotient `↥P ⧸ Q.submoduleOf P` has the length of the image of `P` in `M ⧸ Q`. -/
private lemma length_subquotient_eq_length_map_mkQ {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M] (P Q : Submodule R M) :
    Module.length R (↥P ⧸ Q.submoduleOf P) = Module.length R ↥(P.map Q.mkQ) := by
  have e := (LinearMap.quotKerEquivRange (Q.mkQ.domRestrict P)).length_eq
  rwa [LinearMap.ker_domRestrict, Submodule.ker_mkQ, LinearMap.range_domRestrict] at e

/-- Length is additive along `Q ≤ P ≤ M`, in the subquotient shape `↥P ⧸ Q.submoduleOf P`. -/
theorem length_quotient_eq_length_add_length_quotient {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M] (P Q : Submodule R M) (h : Q ≤ P) :
    Module.length R (M ⧸ Q)
      = Module.length R (↥P ⧸ Q.submoduleOf P) + Module.length R (M ⧸ P) := by
  have e1 : Module.length R (M ⧸ Q)
      = Module.length R ↥(P.map Q.mkQ) + Module.length R ((M ⧸ Q) ⧸ P.map Q.mkQ) :=
    Module.length_eq_add_of_exact _ _ (Submodule.injective_subtype _)
      (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  have e2 : Module.length R ((M ⧸ Q) ⧸ P.map Q.mkQ) = Module.length R (M ⧸ P) :=
    (Submodule.quotientQuotientEquivQuotient Q P h).length_eq
  rw [e1, e2, length_subquotient_eq_length_map_mkQ]

/-! ### The two functions and their finiteness -/

/-- The Hilbert function `φ_{I,M}(n) = length_R (I ^ n M / I ^ (n + 1) M)`, as a natural
number. -/
private noncomputable def phi {R : Type*} [CommRing R] (I : Ideal R) (M : Type*) [AddCommGroup M]
    [Module R M] (n : ℕ) : ℕ :=
  (Module.length R (↥(I ^ n • (⊤ : Submodule R M)) ⧸
    (I ^ (n + 1) • (⊤ : Submodule R M)).submoduleOf (I ^ n • ⊤))).toNat

/-- The function `χ_{I,M}(n) = length_R (M / I ^ (n + 1) M)`, as a natural number. -/
private noncomputable def chi {R : Type*} [CommRing R] (I : Ideal R) (M : Type*) [AddCommGroup M]
    [Module R M] (n : ℕ) : ℕ :=
  (Module.length R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))).toNat

/-! ### The filtration attached to a submodule, and its length increments

For a submodule `N ≤ M` write `P N d = I ^ d N + I ^ (d + 1) M`. Then `P ⊤ d = I ^ d M`, and
`P (𝔪 ^ t M) d = I ^ (d + 1) M` as soon as `𝔪 ^ t ⊆ I`, so the Hilbert function is the length
increment of the pair `(⊤, 𝔪 ^ t M)`. The point of the construction is the identity
`I ^ j • P N d = P N (d + j)`: the associated graded object is generated in degree `0`. -/

section Filtration

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The `d`-th step `I ^ d N + I ^ (d + 1) M` of the `I`-adic filtration of `M` attached to a
submodule `N` of `M`. -/
private def filt (I : Ideal R) (N : Submodule R M) (d : ℕ) : Submodule R M :=
  I ^ d • N ⊔ I ^ (d + 1) • (⊤ : Submodule R M)

private lemma filt_mono (I : Ideal R) {N N' : Submodule R M} (h : N' ≤ N) (d : ℕ) :
    filt I N' d ≤ filt I N d :=
  sup_le_sup_right (Submodule.smul_mono le_rfl h) _

private lemma le_filt (I : Ideal R) (N : Submodule R M) (d : ℕ) :
    I ^ (d + 1) • (⊤ : Submodule R M) ≤ filt I N d := le_sup_right

/-- `I ^ (d + 1) M ⊆ I ^ d M`. -/
private lemma pow_succ_smul_top_le (I : Ideal R) (d : ℕ) :
    I ^ (d + 1) • (⊤ : Submodule R M) ≤ I ^ d • (⊤ : Submodule R M) :=
  Submodule.smul_mono (Ideal.pow_le_pow_right (Nat.le_succ d)) le_rfl

private lemma filt_top (I : Ideal R) (d : ℕ) :
    filt I (⊤ : Submodule R M) d = I ^ d • (⊤ : Submodule R M) :=
  sup_eq_left.mpr (pow_succ_smul_top_le I d)

private lemma filt_smul_top (I : Ideal R) {J : Ideal R} (hJ : J ≤ I) (d : ℕ) :
    filt I (J • (⊤ : Submodule R M)) d = I ^ (d + 1) • (⊤ : Submodule R M) := by
  refine sup_eq_right.mpr ?_
  rw [← Submodule.mul_smul, pow_succ]
  exact Submodule.smul_mono (Ideal.mul_mono le_rfl hJ) le_rfl

/-- `I ^ j` carries the `d`-th step of the filtration onto the `(d + j)`-th: the associated graded
module is generated in degree zero. -/
private lemma smul_filt (I : Ideal R) (N : Submodule R M) (d j : ℕ) :
    I ^ j • filt I N d = filt I N (d + j) := by
  have h1 : I ^ j • (I ^ d • N) = I ^ (d + j) • N := by
    rw [← Submodule.mul_smul, ← pow_add, add_comm]
  have h2 : I ^ j • (I ^ (d + 1) • (⊤ : Submodule R M))
      = I ^ (d + j + 1) • (⊤ : Submodule R M) := by
    rw [← Submodule.mul_smul, ← pow_add, show j + (d + 1) = d + j + 1 from by omega]
  rw [filt, filt, Submodule.smul_sup, h1, h2]

private lemma filt_sup_span_singleton (I : Ideal R) (ν : M) (N' : Submodule R M) (d : ℕ) :
    filt I (Submodule.span R {ν} ⊔ N') d
      = I ^ d • Submodule.span R {ν} ⊔ filt I N' d := by
  rw [filt, filt, Submodule.smul_sup, sup_assoc]

/-- The length of `M ⧸ A`, as a natural number. It is the honest length whenever `A` contains a
power of an ideal of definition; see `len_ne_top`. -/
private noncomputable def len (A : Submodule R M) : ℕ := (Module.length R (M ⧸ A)).toNat

/-- The length increment of a pair `N' ≤ N` of submodules at level `d`: the length of
`P N d / P N' d`. -/
private noncomputable def lenIncr (I : Ideal R) (N N' : Submodule R M) (d : ℕ) : ℤ :=
  (len (filt I N' d) : ℤ) - (len (filt I N d) : ℤ)

private lemma lenIncr_self (I : Ideal R) (N : Submodule R M) (d : ℕ) : lenIncr I N N d = 0 := by
  simp [lenIncr]

private lemma lenIncr_add (I : Ideal R) (N N' N'' : Submodule R M) (d : ℕ) :
    lenIncr I N N'' d = lenIncr I N N' d + lenIncr I N' N'' d := by
  simp only [lenIncr]; ring

/-- The length increment of a pair `N ≤ N` is a numerical polynomial. -/
private lemma isNumericalPoly_lenIncr_self (I : Ideal R) (N : Submodule R M) :
    IsNumericalPoly (lenIncr I N N) :=
  IsNumericalPoly.zero.congr (Filter.Eventually.of_forall fun d => lenIncr_self I N d)

/-- Length increments of `N ≥ N' ≥ N''` that are numerical polynomials add up to one. -/
private lemma isNumericalPoly_lenIncr_trans (I : Ideal R) {N N' N'' : Submodule R M}
    (h₁ : IsNumericalPoly (lenIncr I N N')) (h₂ : IsNumericalPoly (lenIncr I N' N'')) :
    IsNumericalPoly (lenIncr I N N'') :=
  (h₁.add h₂).congr (Filter.Eventually.of_forall fun d => lenIncr_add I N N' N'' d)

/-! ### Monomials and the `I`-adic filtration

The two lemmas below are the arithmetic behind the cyclic step: if `x : Fin s → R` generates `I`,
then `aeval x` carries the homogeneous polynomials of degree `d` into `I ^ d`, and the image of
that space under `f ↦ (aeval x f) • ν` is all of `I ^ d • Rν`. So `⨁_d I ^ d ν / (…)` is a
graded quotient of a polynomial ring generated in degree zero. -/

/-- A homogeneous polynomial of degree `d` all of whose coefficients lie in an ideal `A`, evaluated
at a generating family of `I`, lands in `A * I ^ d`. -/
private lemma aeval_mem_mul_pow {s : ℕ} (x : Fin s → R) (A : Ideal R) {d : ℕ}
    {f : MvPolynomial (Fin s) R} (hf : f.IsHomogeneous d) (hco : ∀ α, f.coeff α ∈ A) :
    MvPolynomial.aeval x f ∈ A * (Ideal.span (Set.range x)) ^ d := by
  classical
  rw [f.as_sum, map_sum]
  refine Ideal.sum_mem _ fun α hα => ?_
  have hsum : ∑ i ∈ α.support, α i = d := by
    have h := hf (MvPolynomial.mem_support_iff.mp hα)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  rw [MvPolynomial.aeval_monomial]
  refine Ideal.mul_mem_mul (by simpa using hco α) ?_
  have h1 : ∀ i ∈ α.support, x i ^ α i ∈ (Ideal.span (Set.range x)) ^ (α i) := fun i _ =>
    Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) _
  have h2 := Ideal.prod_mem_prod h1
  rw [Finset.prod_pow_eq_pow_sum, hsum] at h2
  simpa [Finsupp.prod] using h2

/-- A homogeneous polynomial of degree `d` evaluated at a generating family of `I` lands in
`I ^ d`. -/
private lemma aeval_mem_pow {s : ℕ} (x : Fin s → R) {d : ℕ}
    {f : MvPolynomial (Fin s) R} (hf : f.IsHomogeneous d) :
    MvPolynomial.aeval x f ∈ (Ideal.span (Set.range x)) ^ d := by
  simpa using aeval_mem_mul_pow x ⊤ hf fun _ => trivial

/-- Evaluation at a generating family of `I`, applied to the homogeneous polynomials of degree
`d` and multiplied into `ν`, covers `I ^ d • Rν`. -/
private lemma smul_span_singleton_le_map {s : ℕ} (x : Fin s → R) (ν : M) (d : ℕ) :
    (Ideal.span (Set.range x)) ^ d • Submodule.span R {ν} ≤
      Submodule.map ((LinearMap.toSpanSingleton R M ν) ∘ₗ (MvPolynomial.aeval x).toLinearMap)
        (MvPolynomial.homogeneousSubmodule (Fin s) R d) := by
  induction d with
  | zero =>
    rw [pow_zero, Submodule.one_smul, Submodule.span_le]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have h1 : (1 : MvPolynomial (Fin s) R) ∈ MvPolynomial.homogeneousSubmodule (Fin s) R 0 :=
      (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_one _ _)
    simpa using Submodule.mem_map_of_mem
      (f := (LinearMap.toSpanSingleton R M y) ∘ₗ (MvPolynomial.aeval x).toLinearMap) h1
  | succ d ih =>
    rw [pow_succ', Submodule.mul_smul, Submodule.smul_le]
    intro a ha y hy
    obtain ⟨f, hf, hfy⟩ := ih hy
    have hf' : f.IsHomogeneous d := by simpa using hf
    refine Submodule.span_induction (p := fun b _ => b • y ∈ _) ?_ ?_ ?_ ?_ ha
    · rintro b ⟨i, rfl⟩
      refine ⟨MvPolynomial.X i * f, ?_, ?_⟩
      · have hmul := (MvPolynomial.isHomogeneous_X R i).mul hf'
        rw [add_comm] at hmul
        simpa using hmul
      · simp [LinearMap.toSpanSingleton, ← hfy, mul_smul]
    · simp
    · intro u v _ _ hu hv
      rw [add_smul]
      exact Submodule.add_mem _ hu hv
    · intro c u _ hu
      rw [smul_assoc]
      exact Submodule.smul_mem _ _ hu

end Filtration

/-! ### The cyclic step, presented over the residue field

Fix a generating family `x : Fin s → R` of `I`, an element `ν : M` and a submodule `N' ≤ M`, and
write `P d = I ^ d N' + I ^ (d + 1) M`. Evaluation `f ↦ f(x) ν` carries the homogeneous
polynomials of degree `d` in `R[X_1, …, X_s]` *onto* `I ^ d Rν`, hence onto
`(I ^ d Rν + P d)/P d`; the degree-`d` kernel is `relCyc x ν N' d`, and the union of those kernels
spans an ideal `relIdeal x ν N'` which is homogeneous.

If moreover `𝔪 ν ⊆ N'` then every polynomial with coefficients in `𝔪` lies in `relIdeal x ν N'`,
so the ideal descends to a homogeneous ideal `relIdealRes x ν N'` of `k[X_1, …, X_s]`,
`k = R/𝔪`, and the length increment at level `d` is the Hilbert function of that ideal in degree
`d`. Tag 00K3 then says it is a numerical polynomial. -/

section GradedPresentation

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {s : ℕ}
  (x : Fin s → R) (ν : M) (N' : Submodule R M)

/-- Evaluation at a generating family of `I`, multiplied into `ν`, carries the homogeneous
polynomials of degree `d` exactly onto `I ^ d • Rν`. -/
private lemma map_toSpanSingleton_homogeneousSubmodule (d : ℕ) :
    Submodule.map ((LinearMap.toSpanSingleton R M ν) ∘ₗ (MvPolynomial.aeval x).toLinearMap)
        (MvPolynomial.homogeneousSubmodule (Fin s) R d)
      = (Ideal.span (Set.range x)) ^ d • Submodule.span R {ν} := by
  refine le_antisymm ?_ (smul_span_singleton_le_map x ν d)
  rintro y ⟨f, hf, rfl⟩
  exact Submodule.smul_mem_smul (aeval_mem_pow x
    ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hf)) (Submodule.mem_span_singleton_self ν)

/-- `f ↦ f(x) ν` read modulo the `d`-th step of the filtration attached to `N'`. -/
private noncomputable def evalCyc (d : ℕ) :
    MvPolynomial (Fin s) R →ₗ[R] M ⧸ filt (Ideal.span (Set.range x)) N' d :=
  (filt (Ideal.span (Set.range x)) N' d).mkQ ∘ₗ
    LinearMap.toSpanSingleton R M ν ∘ₗ (MvPolynomial.aeval x).toLinearMap

/-- The homogeneous relations of degree `d` between the classes of the `x ^ α ν`, `|α| = d`. -/
private noncomputable def relCyc (d : ℕ) : Submodule R (MvPolynomial (Fin s) R) :=
  LinearMap.ker (evalCyc x ν N' d) ⊓ MvPolynomial.homogeneousSubmodule (Fin s) R d

private lemma mem_relCyc {d : ℕ} {f : MvPolynomial (Fin s) R} :
    f ∈ relCyc x ν N' d ↔
      MvPolynomial.aeval x f • ν ∈ filt (Ideal.span (Set.range x)) N' d ∧ f.IsHomogeneous d := by
  rw [relCyc, Submodule.mem_inf, MvPolynomial.mem_homogeneousSubmodule, LinearMap.mem_ker]
  show (filt (Ideal.span (Set.range x)) N' d).mkQ (MvPolynomial.aeval x f • ν) = 0 ∧ _ ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

private lemma X_mul_mem_relCyc_succ (i : Fin s) {d : ℕ} {f : MvPolynomial (Fin s) R}
    (hf : f ∈ relCyc x ν N' d) : MvPolynomial.X i * f ∈ relCyc x ν N' (d + 1) := by
  rw [mem_relCyc] at hf ⊢
  obtain ⟨hker, hhom⟩ := hf
  refine ⟨?_, ?_⟩
  · have hz : MvPolynomial.aeval x (MvPolynomial.X i * f)
        = x i * MvPolynomial.aeval x f := by simp
    rw [hz, mul_smul]
    have hxi : x i ∈ (Ideal.span (Set.range x)) ^ 1 := by
      rw [pow_one]; exact Ideal.subset_span (Set.mem_range_self i)
    have h2 := Submodule.smul_mem_smul hxi hker
    rwa [smul_filt] at h2
  · have h3 := (MvPolynomial.isHomogeneous_X R i).mul hhom
    rwa [add_comm] at h3

private lemma X_mul_mem_iSup_relCyc (i : Fin s) {f : MvPolynomial (Fin s) R}
    (hf : f ∈ ⨆ d, relCyc x ν N' d) : MvPolynomial.X i * f ∈ ⨆ d, relCyc x ν N' d := by
  have key : (⨆ d, relCyc x ν N' d)
      ≤ Submodule.comap (LinearMap.mulLeft R (MvPolynomial.X i)) (⨆ d, relCyc x ν N' d) :=
    iSup_le fun d _ hg => Submodule.mem_iSup_of_mem (d + 1) (X_mul_mem_relCyc_succ x ν N' i hg)
  exact key hf

private lemma mul_mem_iSup_relCyc (c : MvPolynomial (Fin s) R) :
    ∀ f ∈ (⨆ d, relCyc x ν N' d), c * f ∈ (⨆ d, relCyc x ν N' d) := by
  induction c using MvPolynomial.induction_on with
  | C a =>
    intro f hf
    rw [← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ a hf
  | add p q hp hq =>
    intro f hf
    rw [add_mul]
    exact Submodule.add_mem _ (hp f hf) (hq f hf)
  | mul_X p i hp =>
    intro f hf
    rw [mul_assoc]
    exact hp _ (X_mul_mem_iSup_relCyc x ν N' i hf)

/-- The ideal of all relations: the `R`-span of the homogeneous relations of every degree. It is an
ideal because `I` is generated by the `x i`, so `X i` carries `relCyc x ν N' d` into
`relCyc x ν N' (d + 1)`. -/
private noncomputable def relIdeal : Ideal (MvPolynomial (Fin s) R) where
  carrier := ↑(⨆ d, relCyc x ν N' d)
  add_mem' ha hb := Submodule.add_mem _ ha hb
  zero_mem' := Submodule.zero_mem _
  smul_mem' c _ hf := mul_mem_iSup_relCyc x ν N' c _ hf

private lemma mem_relIdeal {f : MvPolynomial (Fin s) R} :
    f ∈ relIdeal x ν N' ↔ f ∈ ⨆ d, relCyc x ν N' d := Iff.rfl

private lemma homogeneousComponent_mem_relCyc (d : ℕ) {f : MvPolynomial (Fin s) R}
    (hf : f ∈ relIdeal x ν N') : MvPolynomial.homogeneousComponent d f ∈ relCyc x ν N' d := by
  rw [mem_relIdeal] at hf
  have key : (⨆ e, relCyc x ν N' e)
      ≤ Submodule.comap (MvPolynomial.homogeneousComponent d) (relCyc x ν N' d) := by
    refine iSup_le fun e g hg => ?_
    rw [Submodule.mem_comap, MvPolynomial.homogeneousComponent_of_mem hg.2]
    split
    · next h => subst h; exact hg
    · exact Submodule.zero_mem _
  exact key hf

private lemma mem_relCyc_of_mem_relIdeal {d : ℕ} {f : MvPolynomial (Fin s) R}
    (hf : f ∈ relIdeal x ν N') (hhom : f.IsHomogeneous d) : f ∈ relCyc x ν N' d := by
  have h := homogeneousComponent_mem_relCyc x ν N' d hf
  rwa [MvPolynomial.homogeneousComponent_eq_self hhom] at h

private lemma relIdeal_eq_span :
    relIdeal x ν N' = Ideal.span (⋃ d, (relCyc x ν N' d : Set (MvPolynomial (Fin s) R))) := by
  refine le_antisymm ?_ (Ideal.span_le.mpr ?_)
  · intro f hf
    rw [mem_relIdeal] at hf
    refine (iSup_le fun d => ?_ : (⨆ d, relCyc x ν N' d)
      ≤ (Ideal.span (⋃ d, (relCyc x ν N' d : Set (MvPolynomial (Fin s) R)))).restrictScalars R) hf
    exact fun g hg => Ideal.subset_span (Set.mem_iUnion.mpr ⟨d, hg⟩)
  · exact Set.iUnion_subset fun d g hg =>
      (mem_relIdeal x ν N').mpr (Submodule.mem_iSup_of_mem d hg)

/-- Evaluation restricted to the homogeneous polynomials of degree `d`. -/
private noncomputable def evalCycHomog (d : ℕ) :
    ↥(MvPolynomial.homogeneousSubmodule (Fin s) R d) →ₗ[R]
      M ⧸ filt (Ideal.span (Set.range x)) N' d :=
  (evalCyc x ν N' d) ∘ₗ (MvPolynomial.homogeneousSubmodule (Fin s) R d).subtype

private lemma ker_evalCycHomog (d : ℕ) :
    LinearMap.ker (evalCycHomog x ν N' d)
      = Submodule.comap (MvPolynomial.homogeneousSubmodule (Fin s) R d).subtype
          (relCyc x ν N' d) := by
  rw [evalCycHomog, LinearMap.ker_comp, relCyc, Submodule.comap_inf,
    Submodule.comap_subtype_self, inf_top_eq]

private lemma range_evalCycHomog (d : ℕ) :
    LinearMap.range (evalCycHomog x ν N' d)
      = Submodule.map (filt (Ideal.span (Set.range x)) N' d).mkQ
          (filt (Ideal.span (Set.range x)) (Submodule.span R {ν} ⊔ N') d) := by
  rw [evalCycHomog, LinearMap.range_comp, Submodule.range_subtype, evalCyc,
    filt_sup_span_singleton, Submodule.map_sup, Submodule.map_comp,
    map_toSpanSingleton_homogeneousSubmodule]
  simp

/-- The length increment of the cyclic step is the length of a quotient of the homogeneous
polynomials of degree `d`. -/
private lemma length_subquotient_eq_length_quotient_relCyc (d : ℕ) :
    Module.length R (↥(filt (Ideal.span (Set.range x)) (Submodule.span R {ν} ⊔ N') d) ⧸
        (filt (Ideal.span (Set.range x)) N' d).submoduleOf
          (filt (Ideal.span (Set.range x)) (Submodule.span R {ν} ⊔ N') d))
      = Module.length R (↥(MvPolynomial.homogeneousSubmodule (Fin s) R d) ⧸
          Submodule.comap (MvPolynomial.homogeneousSubmodule (Fin s) R d).subtype
            (relCyc x ν N' d)) := by
  have e := (LinearMap.quotKerEquivRange (evalCycHomog x ν N' d)).length_eq
  rw [ker_evalCycHomog, range_evalCycHomog] at e
  exact (length_subquotient_eq_length_map_mkQ _ _).trans e.symm

end GradedPresentation

section ResiduePresentation

variable {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {s : ℕ} (x : Fin s → R) (ν : M) (N' : Submodule R M)

omit [IsLocalRing R] in
private lemma isHomogeneous_map {k : Type*} [CommRing k] (q : R →+* k) {d : ℕ}
    {f : MvPolynomial (Fin s) R} (hf : f.IsHomogeneous d) :
    (MvPolynomial.map q f).IsHomogeneous d := by
  intro α hα
  refine hf ?_
  rw [MvPolynomial.coeff_map] at hα
  exact fun h => hα (by rw [h, map_zero])

omit [IsLocalRing R] in
private lemma map_homogeneousComponent {k : Type*} [CommRing k] (q : R →+* k) (d : ℕ)
    (f : MvPolynomial (Fin s) R) :
    MvPolynomial.map q (MvPolynomial.homogeneousComponent d f)
      = MvPolynomial.homogeneousComponent d (MvPolynomial.map q f) := by
  ext α
  simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_homogeneousComponent]
  split <;> simp

/-- Reduction of coefficients modulo `𝔪`, on the homogeneous polynomials of degree `d`. -/
private noncomputable def homogPart (d : ℕ) :
    ↥(MvPolynomial.homogeneousSubmodule (Fin s) R d) →ₗ[R]
      ↥(MvPolynomial.homogeneousSubmodule (Fin s) (IsLocalRing.ResidueField R) d) :=
  LinearMap.restrict
    (MvPolynomial.mapAlgHom (Algebra.ofId R (IsLocalRing.ResidueField R))).toLinearMap
    (q := (MvPolynomial.homogeneousSubmodule (Fin s) (IsLocalRing.ResidueField R) d
      ).restrictScalars R)
    (fun _ hf => (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
      (isHomogeneous_map _ ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hf)))

private lemma homogPart_coe (d : ℕ) (f : ↥(MvPolynomial.homogeneousSubmodule (Fin s) R d)) :
    ((homogPart d f : ↥(MvPolynomial.homogeneousSubmodule (Fin s) (IsLocalRing.ResidueField R) d))
      : MvPolynomial (Fin s) (IsLocalRing.ResidueField R))
      = MvPolynomial.map (algebraMap R (IsLocalRing.ResidueField R))
        (f : MvPolynomial (Fin s) R) := rfl

private lemma homogPart_surjective (d : ℕ) :
    Function.Surjective (homogPart (R := R) (s := s) d) := by
  intro g
  obtain ⟨f, hf⟩ := MvPolynomial.map_surjective
    (algebraMap R (IsLocalRing.ResidueField R)) Ideal.Quotient.mk_surjective
    (g : MvPolynomial (Fin s) (IsLocalRing.ResidueField R))
  refine ⟨⟨MvPolynomial.homogeneousComponent d f,
    MvPolynomial.homogeneousComponent_mem d f⟩, Subtype.ext ?_⟩
  rw [homogPart_coe, map_homogeneousComponent, hf, MvPolynomial.homogeneousComponent_eq_self
    ((MvPolynomial.mem_homogeneousSubmodule _ _).mp g.2)]

/-- Because `𝔪 ν ⊆ N'`, a polynomial all of whose coefficients lie in `𝔪` is a relation. -/
private lemma mem_relIdeal_of_map_eq_zero
    (hmν : IsLocalRing.maximalIdeal R • Submodule.span R {ν} ≤ N')
    {f : MvPolynomial (Fin s) R}
    (hf : MvPolynomial.map (algebraMap R (IsLocalRing.ResidueField R)) f = 0) :
    f ∈ relIdeal x ν N' := by
  have hco : ∀ α, f.coeff α ∈ IsLocalRing.maximalIdeal R := by
    intro α
    have h0 : (algebraMap R (IsLocalRing.ResidueField R)) (f.coeff α) = 0 := by
      rw [← MvPolynomial.coeff_map, hf, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    exact (IsLocalRing.residue_eq_zero_iff _).mp h0
  rw [mem_relIdeal, ← MvPolynomial.sum_homogeneousComponent f]
  refine Submodule.sum_mem _ fun d _ => Submodule.mem_iSup_of_mem d ?_
  rw [mem_relCyc]
  refine ⟨?_, MvPolynomial.homogeneousComponent_isHomogeneous d f⟩
  have hcod : ∀ α, (MvPolynomial.homogeneousComponent d f).coeff α
      ∈ IsLocalRing.maximalIdeal R := by
    intro α
    rw [MvPolynomial.coeff_homogeneousComponent]
    split
    · exact hco α
    · exact Submodule.zero_mem _
  have h1 := aeval_mem_mul_pow x (IsLocalRing.maximalIdeal R)
    (MvPolynomial.homogeneousComponent_isHomogeneous d f) hcod
  have h2 : ((IsLocalRing.maximalIdeal R) * (Ideal.span (Set.range x)) ^ d) • Submodule.span R {ν}
      ≤ filt (Ideal.span (Set.range x)) N' d := by
    rw [mul_comm, Submodule.mul_smul]
    exact le_trans (Submodule.smul_mono le_rfl hmν) le_sup_left
  exact h2 (Submodule.smul_mem_smul h1 (Submodule.mem_span_singleton_self ν))

/-- The ideal of relations, pushed to the residue field. -/
private noncomputable def relIdealRes :
    Ideal (MvPolynomial (Fin s) (IsLocalRing.ResidueField R)) :=
  Ideal.map (MvPolynomial.map (algebraMap R (IsLocalRing.ResidueField R))) (relIdeal x ν N')

private lemma relIdealRes_isHomogeneous :
    (relIdealRes x ν N').IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin s) (IsLocalRing.ResidueField R)) := by
  rw [relIdealRes, relIdeal_eq_span, Ideal.map_span]
  refine Ideal.homogeneous_span _ _ ?_
  rintro g ⟨f, hf, rfl⟩
  obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hf
  exact ⟨d, (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
    (isHomogeneous_map _ ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hd.2))⟩

private lemma mem_relIdealRes_iff
    (hmν : IsLocalRing.maximalIdeal R • Submodule.span R {ν} ≤ N') {d : ℕ}
    {f : MvPolynomial (Fin s) R} (hhom : f.IsHomogeneous d) :
    MvPolynomial.map (algebraMap R (IsLocalRing.ResidueField R)) f ∈ relIdealRes x ν N'
      ↔ f ∈ relCyc x ν N' d := by
  refine ⟨fun h => ?_, fun h => Ideal.mem_map_of_mem _ ((mem_relIdeal x ν N').mpr
    (Submodule.mem_iSup_of_mem d h))⟩
  have hsurj : Function.Surjective
      (MvPolynomial.map (algebraMap R (IsLocalRing.ResidueField R)) (σ := Fin s)) :=
    MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have h1 : f ∈ Ideal.comap (MvPolynomial.map (algebraMap R (IsLocalRing.ResidueField R)))
      (relIdealRes x ν N') := h
  rw [relIdealRes, Ideal.comap_map_of_surjective _ hsurj] at h1
  have hker : Ideal.comap (MvPolynomial.map (algebraMap R (IsLocalRing.ResidueField R)))
      (⊥ : Ideal (MvPolynomial (Fin s) (IsLocalRing.ResidueField R))) ≤ relIdeal x ν N' :=
    fun g hg => mem_relIdeal_of_map_eq_zero x ν N' hmν (by simpa using hg)
  rw [sup_eq_left.mpr hker] at h1
  exact mem_relCyc_of_mem_relIdeal x ν N' h1 hhom

/-- The degree-`d` piece of a homogeneous ideal, as a subspace of the degree-`d` homogeneous
polynomials. -/
private noncomputable def homogPiece
    (J : Ideal (MvPolynomial (Fin s) (IsLocalRing.ResidueField R))) (d : ℕ) :
    Submodule (IsLocalRing.ResidueField R)
      ↥(MvPolynomial.homogeneousSubmodule (Fin s) (IsLocalRing.ResidueField R) d) :=
  Submodule.comap
    (MvPolynomial.homogeneousSubmodule (Fin s) (IsLocalRing.ResidueField R) d).subtype
    (J.restrictScalars (IsLocalRing.ResidueField R))

private lemma finrank_quotient_homogPiece
    (J : Ideal (MvPolynomial (Fin s) (IsLocalRing.ResidueField R))) (d : ℕ) :
    Module.finrank (IsLocalRing.ResidueField R)
        (↥(MvPolynomial.homogeneousSubmodule (Fin s) (IsLocalRing.ResidueField R) d) ⧸
          homogPiece J d)
      = Stacks.HilbertFunction.PolynomialQuotient.hilbertFunction J d := by
  have hfin : Module.Finite (IsLocalRing.ResidueField R)
      ↥(MvPolynomial.homogeneousSubmodule (Fin s) (IsLocalRing.ResidueField R) d) :=
    Module.Finite.iff_fg.mpr (MvPolynomial.homogeneousSubmodule_fg _ _ d)
  have hcomap : Submodule.comap
      (MvPolynomial.homogeneousSubmodule (Fin s) (IsLocalRing.ResidueField R) d).subtype
      ((J.restrictScalars (IsLocalRing.ResidueField R)) ⊓
        MvPolynomial.homogeneousSubmodule (Fin s) (IsLocalRing.ResidueField R) d)
      = homogPiece J d := by
    rw [Submodule.comap_inf, Submodule.comap_subtype_self, inf_top_eq, homogPiece]
  have hrank : Module.finrank (IsLocalRing.ResidueField R) ↥(homogPiece J d)
      = Module.finrank (IsLocalRing.ResidueField R)
        ↥((J.restrictScalars (IsLocalRing.ResidueField R)) ⊓
          MvPolynomial.homogeneousSubmodule (Fin s) (IsLocalRing.ResidueField R) d) := by
    rw [← hcomap]
    exact (Submodule.comapSubtypeEquivOfLe inf_le_right).finrank_eq
  have hadd := Submodule.finrank_quotient_add_finrank (homogPiece J d)
  rw [Stacks.HilbertFunction.PolynomialQuotient.hilbertFunction,
    Stacks.HilbertFunction.PolynomialQuotient.gradedPieceI,
      Stacks.HilbertFunction.PolynomialQuotient.gradedPieceS,
    ← hadd, hrank]
  omega

/-- The presentation of the degree-`d` piece over the residue field. -/
private noncomputable def evalRes (d : ℕ) :
    ↥(MvPolynomial.homogeneousSubmodule (Fin s) R d) →ₗ[R]
      (↥(MvPolynomial.homogeneousSubmodule (Fin s) (IsLocalRing.ResidueField R) d) ⧸
        homogPiece (relIdealRes x ν N') d) :=
  LinearMap.restrictScalars R (Submodule.mkQ (homogPiece (relIdealRes x ν N') d)) ∘ₗ homogPart d

private lemma evalRes_surjective (d : ℕ) : Function.Surjective (evalRes x ν N' d) :=
  (Submodule.mkQ_surjective _).comp (homogPart_surjective d)

private lemma ker_evalRes (hmν : IsLocalRing.maximalIdeal R • Submodule.span R {ν} ≤ N')
    (d : ℕ) : LinearMap.ker (evalRes x ν N' d)
      = Submodule.comap (MvPolynomial.homogeneousSubmodule (Fin s) R d).subtype
          (relCyc x ν N' d) := by
  ext f
  rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
  show (Submodule.mkQ (homogPiece (relIdealRes x ν N') d)) (homogPart d f) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, homogPiece, Submodule.mem_comap,
    Submodule.subtype_apply, Submodule.restrictScalars_mem, homogPart_coe]
  exact mem_relIdealRes_iff x ν N' hmν ((MvPolynomial.mem_homogeneousSubmodule _ _).mp f.2)

/-- **The cyclic step, computed.** The length increment of the pair `(Rν + N', N')` at level `d`
is the Hilbert function, in degree `d`, of a homogeneous ideal of `k[X_1, …, X_s]`. -/
private lemma length_subquotient_eq_hilbertFunction
    (hmν : IsLocalRing.maximalIdeal R • Submodule.span R {ν} ≤ N') (d : ℕ) :
    Module.length R (↥(filt (Ideal.span (Set.range x)) (Submodule.span R {ν} ⊔ N') d) ⧸
        (filt (Ideal.span (Set.range x)) N' d).submoduleOf
          (filt (Ideal.span (Set.range x)) (Submodule.span R {ν} ⊔ N') d))
      = (Stacks.HilbertFunction.PolynomialQuotient.hilbertFunction (relIdealRes x ν N') d : ℕ∞) :=
        by
  have hfin : Module.Finite (IsLocalRing.ResidueField R)
      ↥(MvPolynomial.homogeneousSubmodule (Fin s) (IsLocalRing.ResidueField R) d) :=
    Module.Finite.iff_fg.mpr (MvPolynomial.homogeneousSubmodule_fg _ _ d)
  have hfin2 : Module.Finite (IsLocalRing.ResidueField R)
      (↥(MvPolynomial.homogeneousSubmodule (Fin s) (IsLocalRing.ResidueField R) d) ⧸
        homogPiece (relIdealRes x ν N') d) :=
    Module.Finite.of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
  have hEq := (LinearMap.quotKerEquivOfSurjective (evalRes x ν N' d)
    (evalRes_surjective x ν N' d)).length_eq
  rw [ker_evalRes x ν N' hmν] at hEq
  rw [length_subquotient_eq_length_quotient_relCyc x ν N' d, hEq,
    Module.length_eq_of_surjective (R := IsLocalRing.ResidueField R) (S := R)
      Ideal.Quotient.mk_surjective, Module.length_eq_finrank, finrank_quotient_homogPiece]

end ResiduePresentation

section Local'

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {I : Ideal R}
  {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]

private lemma len_ne_top (hI : I.radical = IsLocalRing.maximalIdeal R) {A : Submodule R M} {j : ℕ}
    (h : I ^ (j + 1) • (⊤ : Submodule R M) ≤ A) : Module.length R (M ⧸ A) ≠ ⊤ :=
  length_ne_top_of_smul_top_eq_bot (J := I ^ (j + 1))
    (isArtinianRing_quotient_pow hI (Nat.succ_ne_zero j)) (smul_top_quotient_eq_bot _ _ h)

/-- Additivity of length along `B ≤ A ≤ M`, in the form used here: the length of `A / B` is the
difference of the lengths of `M ⧸ B` and `M ⧸ A`. -/
private lemma coe_length_submoduleOf (hI : I.radical = IsLocalRing.maximalIdeal R)
    {A B : Submodule R M} (hBA : B ≤ A) {j : ℕ} (hB : I ^ (j + 1) • (⊤ : Submodule R M) ≤ B) :
    ((Module.length R (↥A ⧸ B.submoduleOf A)).toNat : ℤ) = (len B : ℤ) - (len A : ℤ) := by
  have hkey := length_quotient_eq_length_add_length_quotient A B hBA
  have hBtop : Module.length R (M ⧸ B) ≠ ⊤ := len_ne_top hI hB
  have hAtop : Module.length R (M ⧸ A) ≠ ⊤ := len_ne_top hI (hB.trans hBA)
  have hq : Module.length R (↥A ⧸ B.submoduleOf A) ≠ ⊤ := by
    intro h
    rw [hkey, h, top_add] at hBtop
    exact hBtop rfl
  have : len B = (Module.length R (↥A ⧸ B.submoduleOf A)).toNat + len A := by
    simp only [len]
    rw [hkey, ENat.toNat_add hq hAtop]
  rw [this]
  push_cast
  ring

private lemma lenIncr_eq_length (hI : I.radical = IsLocalRing.maximalIdeal R)
    {N N' : Submodule R M} (hle : N' ≤ N) (d : ℕ) :
    lenIncr I N N' d
      = ((Module.length R (↥(filt I N d) ⧸ (filt I N' d).submoduleOf (filt I N d))).toNat : ℤ) :=
  (coe_length_submoduleOf hI (filt_mono I hle d) (le_filt I N' d)).symm

private lemma coe_phi_eq_lenIncr (hI : I.radical = IsLocalRing.maximalIdeal R) {t : ℕ}
    (ht : IsLocalRing.maximalIdeal R ^ t ≤ I) (d : ℕ) :
    (phi I M d : ℤ) = lenIncr I ⊤ (IsLocalRing.maximalIdeal R ^ t • (⊤ : Submodule R M)) d := by
  rw [lenIncr, filt_top, filt_smul_top I ht, phi]
  exact coe_length_submoduleOf hI (pow_succ_smul_top_le I d) (j := d) le_rfl

/-- The cyclic step for an ideal presented by a generating family: the length increment is the
Hilbert function of the homogeneous ideal `relIdealRes x ν N'` of `k[X_1, …, X_s]`, hence a
numerical polynomial by Tag 00K3. -/
private lemma isNumericalPoly_lenIncr_cyclic_span {s : ℕ} (x : Fin s → R)
    (hx : (Ideal.span (Set.range x)).radical = IsLocalRing.maximalIdeal R) (ν : M)
    (N' : Submodule R M) (hmν : IsLocalRing.maximalIdeal R • Submodule.span R {ν} ≤ N') :
    IsNumericalPoly (lenIncr (Ideal.span (Set.range x)) (Submodule.span R {ν} ⊔ N') N') := by
  refine (isNumericalPoly_of_byNaturalArgs
    (Stacks.HilbertFunction.PolynomialQuotient.isNumericalPolynomialByNaturalArgs_hilbertFunction
      (relIdealRes x ν N')
      (relIdealRes_isHomogeneous x ν N'))).congr ?_
  filter_upwards with d
  rw [lenIncr_eq_length hx le_sup_right d,
    length_subquotient_eq_hilbertFunction x ν N' hmν d]
  simp

/-- **The cyclic step.** If `N = Rν + N'` with `𝔪 ν ⊆ N'`, then `d ↦ ℓ(P N d / P N' d)` is a
numerical polynomial. -/
private lemma isNumericalPoly_lenIncr_cyclic (hI : I.radical = IsLocalRing.maximalIdeal R) (ν : M)
    (N' : Submodule R M) (hmν : IsLocalRing.maximalIdeal R • Submodule.span R {ν} ≤ N') :
    IsNumericalPoly (lenIncr I (Submodule.span R {ν} ⊔ N') N') := by
  obtain ⟨s, x, hx⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
  subst hx
  exact isNumericalPoly_lenIncr_cyclic_span x hI ν N' hmν

/-- **The `𝔪`-step.** If `𝔪 (span s + N') ⊆ N'`, then `d ↦ ℓ(P (span s + N') d / P N' d)` is a
numerical polynomial: refine by cyclic extensions, one generator at a time. -/
private lemma isNumericalPoly_lenIncr_of_finset (hI : I.radical = IsLocalRing.maximalIdeal R) :
    ∀ (s : Finset M) (N' : Submodule R M),
      IsLocalRing.maximalIdeal R • (Submodule.span R (s : Set M) ⊔ N') ≤ N' →
      IsNumericalPoly (lenIncr I (Submodule.span R (s : Set M) ⊔ N') N') := by
  classical
  intro s
  induction s using Finset.induction with
  | empty =>
    intro N' _
    have h0 : Submodule.span R ((∅ : Finset M) : Set M) ⊔ N' = N' := by simp
    rw [h0]
    exact isNumericalPoly_lenIncr_self I N'
  | insert a s _ ih =>
    intro N' hsm
    have hins : Submodule.span R ((insert a s : Finset M) : Set M) ⊔ N'
        = Submodule.span R {a} ⊔ (Submodule.span R (s : Set M) ⊔ N') := by
      rw [Finset.coe_insert, Submodule.span_insert, sup_assoc]
    rw [hins] at hsm ⊢
    have hmono : Submodule.span R (s : Set M) ⊔ N'
        ≤ Submodule.span R {a} ⊔ (Submodule.span R (s : Set M) ⊔ N') := le_sup_right
    have h1 : IsNumericalPoly
        (lenIncr I (Submodule.span R {a} ⊔ (Submodule.span R (s : Set M) ⊔ N'))
          (Submodule.span R (s : Set M) ⊔ N')) :=
      isNumericalPoly_lenIncr_cyclic hI a _ (by
        have hla : IsLocalRing.maximalIdeal R • Submodule.span R ({a} : Set M)
            ≤ IsLocalRing.maximalIdeal R • (Submodule.span R ({a} : Set M) ⊔
              (Submodule.span R (s : Set M) ⊔ N')) := Submodule.smul_mono le_rfl le_sup_left
        exact ((hla.trans hsm).trans le_sup_right))
    have h2 : IsNumericalPoly (lenIncr I (Submodule.span R (s : Set M) ⊔ N') N') :=
      ih N' ((Submodule.smul_mono le_rfl hmono).trans hsm)
    exact isNumericalPoly_lenIncr_trans I h1 h2

private lemma isNumericalPoly_lenIncr_step (hI : I.radical = IsLocalRing.maximalIdeal R)
    (N N' : Submodule R M) (hle : N' ≤ N)
    (h : IsLocalRing.maximalIdeal R • N ≤ N') : IsNumericalPoly (lenIncr I N N') := by
  classical
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian N
  have hsplit : Submodule.span R (s : Set M) ⊔ N' = N := by
    rw [hs]; exact sup_eq_left.mpr hle
  have hmain := isNumericalPoly_lenIncr_of_finset hI s N' (by rw [hsplit]; exact h)
  rwa [hsplit] at hmain

/-- **The general step**, by induction on `t`: if `𝔪 ^ t N ⊆ N' ⊆ N` then `d ↦ ℓ(P N d / P N' d)`
is a numerical polynomial. -/
private lemma isNumericalPoly_lenIncr (hI : I.radical = IsLocalRing.maximalIdeal R) :
    ∀ (t : ℕ) (N N' : Submodule R M), N' ≤ N → IsLocalRing.maximalIdeal R ^ t • N ≤ N' →
      IsNumericalPoly (lenIncr I N N') := by
  intro t
  induction t with
  | zero =>
    intro N N' hle h
    rw [pow_zero, Submodule.one_smul] at h
    have : N = N' := le_antisymm h hle
    subst this
    exact isNumericalPoly_lenIncr_self I N
  | succ t ih =>
    intro N N' hle h
    set N'' := IsLocalRing.maximalIdeal R • N ⊔ N' with hN''
    have hle1 : N'' ≤ N := sup_le Submodule.smul_le_right hle
    have hle2 : N' ≤ N'' := le_sup_right
    have h1 : IsNumericalPoly (lenIncr I N N'') :=
      isNumericalPoly_lenIncr_step hI N N'' hle1 le_sup_left
    have h2 : IsNumericalPoly (lenIncr I N'' N') := by
      refine ih N'' N' hle2 ?_
      rw [hN'', Submodule.smul_sup]
      refine sup_le ?_ (Submodule.smul_le_right.trans le_rfl)
      rw [← Submodule.mul_smul, ← pow_succ]
      exact h
    exact isNumericalPoly_lenIncr_trans I h1 h2

private theorem isNumericalPoly_phi_of_radical (hI : I.radical = IsLocalRing.maximalIdeal R) :
    IsNumericalPoly (fun d => (phi I M d : ℤ)) := by
  obtain ⟨t, ht⟩ := Ideal.exists_pow_le_of_le_radical_of_fg_radical
    (I := IsLocalRing.maximalIdeal R) (J := I) (by rw [hI])
    (by rw [hI]; exact IsNoetherian.noetherian _)
  refine IsNumericalPoly.congr
    (isNumericalPoly_lenIncr hI t ⊤ (IsLocalRing.maximalIdeal R ^ t • ⊤) le_top le_rfl)
    (Filter.Eventually.of_forall fun d => coe_phi_eq_lenIncr hI ht d)

end Local'

section Local

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {I : Ideal R}
  (hI : I.radical = IsLocalRing.maximalIdeal R) {M : Type*} [AddCommGroup M] [Module R M]
  [Module.Finite R M]

include hI

private lemma length_phi_ne_top (n : ℕ) :
    Module.length R (↥(I ^ n • (⊤ : Submodule R M)) ⧸
      (I ^ (n + 1) • (⊤ : Submodule R M)).submoduleOf (I ^ n • ⊤)) ≠ ⊤ := by
  refine length_ne_top_of_smul_top_eq_bot (J := I) ?_
    (smul_top_quotient_eq_bot I _ (smul_top_le_submoduleOf I n))
  rw [← pow_one I]
  exact isArtinianRing_quotient_pow hI one_ne_zero

private lemma length_chi_ne_top (n : ℕ) :
    Module.length R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) ≠ ⊤ :=
  length_ne_top_of_smul_top_eq_bot (J := I ^ (n + 1))
    (isArtinianRing_quotient_pow hI (Nat.succ_ne_zero n)) (smul_top_quotient_eq_bot _ _ le_rfl)

private lemma coe_phi (n : ℕ) :
    (phi I M n : ℕ∞) = Module.length R (↥(I ^ n • (⊤ : Submodule R M)) ⧸
      (I ^ (n + 1) • (⊤ : Submodule R M)).submoduleOf (I ^ n • ⊤)) :=
  ENat.natCast_toNat (length_phi_ne_top hI n)

private lemma coe_chi (n : ℕ) :
    (chi I M n : ℕ∞) = Module.length R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) :=
  ENat.natCast_toNat (length_chi_ne_top hI n)

/-- `χ_{I,M}(n + 1) - χ_{I,M}(n) = φ_{I,M}(n + 1)`, from additivity of length along
`I ^ (n + 2) M ⊆ I ^ (n + 1) M ⊆ M`. -/
private lemma chi_succ (n : ℕ) : chi I M (n + 1) = phi I M (n + 1) + chi I M n := by
  have h := length_quotient_eq_length_add_length_quotient
    (I ^ (n + 1) • (⊤ : Submodule R M)) (I ^ (n + 2) • (⊤ : Submodule R M))
    (pow_succ_smul_top_le I (n + 1))
  rw [← coe_chi hI (n + 1), ← coe_phi hI (n + 1), ← coe_chi hI n] at h
  exact_mod_cast h

/-! ### The Hilbert function is a numerical polynomial -/

/-- **The Hilbert function is a numerical polynomial.** Refine `⊤ ⊇ 𝔪 ^ t M` (for `𝔪 ^ t ⊆ I`)
by cyclic extensions; each cyclic step contributes the Hilbert function of a homogeneous ideal of
`k[X_1, …, X_s]`, `k = R/𝔪`, which is a numerical polynomial by Tag 00K3. -/
private theorem isNumericalPoly_phi : IsNumericalPoly fun n => (phi I M n : ℤ) :=
  isNumericalPoly_phi_of_radical hI

/-- **Stacks 00K8 for `χ_{I,M}`**, from the statement for `φ_{I,M}` and Tag 00JZ. -/
private theorem isNumericalPoly_chi : IsNumericalPoly fun n => (chi I M n : ℤ) := by
  refine IsNumericalPoly.of_forwardDifference
    (((isNumericalPoly_phi (I := I) hI (M := M)).shift).congr ?_)
  filter_upwards with n
  rw [chi_succ hI n]
  push_cast
  ring

end Local

/-- For an ideal of definition `I` of a Noetherian local ring `R` and a finite `R`-module `M`, the
functions `φ_{I,M}(n) = length_R (I ^ n M / I ^ (n + 1) M)` and
`χ_{I,M}(n) = length_R (M / I ^ (n + 1) M)` take finite values and agree for `n ≫ 0` with
`ℤ`-linear combinations of the binomial coefficients `n choose i`, `i ≤ r`. -/
public theorem solution {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R)
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ (r : ℕ) (a b : ℕ → ℤ), ∀ᶠ n : ℕ in Filter.atTop,
      (∃ p : ℕ, Module.length R (↥(I ^ n • (⊤ : Submodule R M)) ⧸
            (I ^ (n + 1) • (⊤ : Submodule R M)).submoduleOf (I ^ n • ⊤)) = p ∧
          (p : ℤ) = ∑ i ∈ Finset.range (r + 1), (n.choose i : ℤ) * a i) ∧
      (∃ q : ℕ, Module.length R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) = q ∧
          (q : ℤ) = ∑ i ∈ Finset.range (r + 1), (n.choose i : ℤ) * b i) := by
  obtain ⟨r₁, a, ha⟩ := isNumericalPoly_phi (I := I) hI (M := M)
  obtain ⟨r₂, b, hb⟩ := isNumericalPoly_chi (I := I) hI (M := M)
  refine ⟨max r₁ r₂, fun i => if i ≤ r₁ then a i else 0, fun i => if i ≤ r₂ then b i else 0, ?_⟩
  filter_upwards [ha, hb] with n hna hnb
  refine ⟨⟨phi I M n, (coe_phi hI (M := M) n).symm, ?_⟩,
    ⟨chi I M n, (coe_chi hI (M := M) n).symm, ?_⟩⟩
  · rw [sum_choose_mul_pad (le_max_left r₁ r₂) a n]
    exact hna
  · rw [sum_choose_mul_pad (le_max_right r₁ r₂) b n]
    exact hnb

end Stacks.HilbertFunction.NumericalPoly

/-!
# Hilbert functions over a Noetherian local ring are numerical polynomials

Let `(R, m)` be a Noetherian local ring, let `I ⊆ R` be an ideal of definition, that is an
ideal whose radical is `m`, and let `M` be a finite `R`-module. Every `R`-module annihilated by
a power of `I` then has finite length, so the two functions

  `φ_{I,M}(n) = length_R (I ^ n • M / I ^ (n + 1) • M)`  and
  `χ_{I,M}(n) = length_R (M / I ^ (n + 1) • M)`

are defined for all `n ≥ 0`. Both are *numerical polynomials*: there are `r ∈ ℕ` and integers
`a₀, …, a_r` with `φ_{I,M}(n) = ∑_{i = 0}^r (n choose i) * aᵢ` for all `n ≫ 0`, and likewise
for `χ_{I,M}` with its own coefficients. Note that the coefficients must be allowed to be
negative, so the values are compared in `ℤ`.

## Main results

* `Ideal.exists_eventually_length_quotient_smul_pow_eq_sum_choose_mul`: the Hilbert function
  `φ_{I,M}` and the function `χ_{I,M}` of a finite module over a Noetherian local ring are
  numerical polynomials.

## Implementation notes

Mathlib has no notion of numerical polynomial, so the
source's definition (Tag 00JX, for the abelian group `A = ℤ`) is written out inline as a
`ℤ`-linear combination of the binomial coefficients `n choose i`, valid for all large `n`. The
rational polynomial `P ∈ ℚ[t]` with `P(n) = φ_{I,M}(n)` for `n ≫ 0`, which the source builds on
this proposition in Definition 09CA, is `∑ᵢ aᵢ * (t choose i)`.

Being an ideal of definition (Tag 07DU) is spelled as `I.radical = IsLocalRing.maximalIdeal R`,
and `I ^ n • M` as `I ^ n • (⊤ : Submodule R M)`, so that the subquotient `I ^ n M / I ^ (n+1) M`
is `↥(I ^ n • ⊤) ⧸ (I ^ (n + 1) • ⊤).submoduleOf (I ^ n • ⊤)`. Finiteness of the two lengths is
part of the conclusion, in the shape `∃ p : ℕ, Module.length R … = p`, rather than being hidden
behind `ENat.toNat`; the source records it in the discussion preceding the definitions of
`φ_{I,M}` and `χ_{I,M}`. The two functions are governed by a single `r`, which is no weaker than
one `r` per function since the shorter coefficient family may be padded with zeros.

Faithfulness. (1) Every hypothesis is used: without `I.radical = IsLocalRing.maximalIdeal R` the
lengths are infinite (take `R = k[[x, y]]`, `I = (x)`, `M = R`), so the conclusion fails
outright, and Noetherianness of `R` and finiteness of `M` are what make the graded ring
`⨁_d I ^ d / I ^ (d + 1)` Noetherian and its module `⨁_d I ^ d M / I ^ (d + 1) M` finite.
(2) The scalars are the source's throughout: both lengths are lengths of `R`-modules, not of
modules over `R / I` or over the associated graded ring. (3) The source names no canonical map
here; what has to be pinned are the two functions themselves, and they are, at the value of
every `n`, together with the index convention `I ^ (n + 1)` of the source. (4) A witness: for a
discrete valuation ring `R` with `I = m` and `M = R` one has `φ_{I,M} ≡ 1` and
`χ_{I,M}(n) = n + 1`, so the conclusion holds with a nonzero coefficient family of degree `1`.

## References

* [Stacks Project, Tag 00K8](https://stacks.math.columbia.edu/tag/00K8)

## Tags

Hilbert function, numerical polynomial, ideal of definition, length
-/

/-- **Stacks 00K8.** Let `R` be a Noetherian local ring, let `I ⊆ R` be an ideal of definition
(`I.radical` is the maximal ideal of `R`) and let `M` be a finite `R`-module. Then the Hilbert
function `n ↦ length_R (I ^ n • M / I ^ (n + 1) • M)` and the function
`n ↦ length_R (M / I ^ (n + 1) • M)` are numerical polynomials: each takes finite values which,
for all `n ≫ 0`, are given by a `ℤ`-linear combination of the binomial coefficients
`n choose 0, …, n choose r`. -/
@[stacks 00K8, ega "0 16.2.1" "local case"]
public theorem Ideal.exists_eventually_length_quotient_smul_pow_eq_sum_choose_mul
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I.radical = IsLocalRing.maximalIdeal R)
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ (r : ℕ) (a b : ℕ → ℤ), ∀ᶠ n : ℕ in Filter.atTop,
      (∃ p : ℕ, Module.length R (↥(I ^ n • (⊤ : Submodule R M)) ⧸
            (I ^ (n + 1) • (⊤ : Submodule R M)).submoduleOf (I ^ n • ⊤)) = p ∧
          (p : ℤ) = ∑ i ∈ Finset.range (r + 1), (n.choose i : ℤ) * a i) ∧
      (∃ q : ℕ, Module.length R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) = q ∧
          (q : ℤ) = ∑ i ∈ Finset.range (r + 1), (n.choose i : ℤ) * b i) :=
    by apply Stacks.HilbertFunction.NumericalPoly.solution; assumption
