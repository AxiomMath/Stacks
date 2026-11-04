module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Span
public import StacksFrontier.RingTheory.AbsolutelyIntegrallyClosed.Absolute

/-!
# The equational lemma behind the Hochster–Huneke theorem

Let `B` be an absolutely integrally closed domain of characteristic `p` and let `x, y ∈ B` be
nonzero. This file proves the two elementary halves of the argument showing that a relation
`s z ∈ (x, y)` among parameters becomes trivial in `B`.

The first half, `IsAbsolutelyIntegrallyClosed.mem_span_pair_of_frobenius_relation`, is the
*equational lemma*: if the Frobenius powers of `s` satisfy a relation
`s^Q - ∑_{j < n} c_j (xy)^{Q - p^j} s^{p^j} ∈ (x^Q, y^Q)` with `Q = p^n`, then `s ∈ (x, y)B`. One
solves the two additive (`p`-polynomial) equations
`w^Q - ∑ c_j y^{Q - p^j} w^{p^j} = α` and `w'^Q - ∑ c_j x^{Q - p^j} w'^{p^j} = β` in `B`; then
`L = s - x w - y w'` satisfies `L^Q = ∑ c_j (xy)^{Q - p^j} L^{p^j}`, so `L / xy` is a root of the
monic polynomial `X^Q - ∑ c_j X^{p^j}` and lies in `B` because `B` is integrally closed.

The second half, `exists_frobenius_relation`, produces such a relation inside a Noetherian ring
`T` from a uniform annihilation hypothesis: if `x, y` is a regular sequence on `T`,
`s z = a x + b y` in `T`, and `x^N`, `y^N` kill every class `u` with `z^q u ∈ (x^q, y^q)`, then
each `s^{p^j}` is congruent to `(xy)^{p^j - N} v_j` modulo `(x^{p^j}, y^{p^j})`, and the ascending
chain of submodules of `T/(x^N, y^N)` spanned by the classes of the `v_j` stabilizes.

## Main results

* `IsAbsolutelyIntegrallyClosed.mem_span_pair_of_frobenius_relation`: the equational lemma.
* `exists_mul_pow_sub_mem_span_pow_pair`: if `x, y` is a regular sequence and `x^N w`, `y^N w`
  lie in `(x^q, y^q)`, then `w ≡ (xy)^{q - N} v` modulo `(x^q, y^q)`.
* `exists_frobenius_relation`: the Frobenius relation in a Noetherian ring.

## References

* M. Hochster and C. Huneke, *Infinite integral extensions and big Cohen–Macaulay algebras*,
  Ann. of Math. 135 (1992), 53–89.
* C. Huneke and G. Lyubeznik, *Absolute integral closure in positive characteristic*,
  Adv. Math. 210 (2007), 498–504.
-/

@[expose] public section

open Polynomial Finset

namespace IsAbsolutelyIntegrallyClosed

variable {B : Type*} [CommRing B] [IsDomain B] {p : ℕ} [Fact p.Prime] [CharP B p]

/-- The part subtracted in the additive polynomial
`X ^ Q - (∑_{j < n} C (c j * g ^ (Q - p ^ j)) * X ^ p ^ j + C e)` has degree less than `Q = p ^ n`,
each exponent `p ^ j` with `j < n` being smaller than `Q`. -/
private theorem natDegree_sum_C_mul_X_pow_add_C_lt {n : ℕ} (hp : 1 < p) (hQ : 0 < p ^ n)
    (c : ℕ → B) : ∀ (g : B) (e : B),
    (∑ j ∈ range n, C (c j * g ^ (p ^ n - p ^ j)) * X ^ p ^ j + C e).natDegree < p ^ n := by
  intro g e
  refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ (by simpa using hQ))
  by_cases hn : n = 0
  · subst hn; simpa using hQ
  have : (∑ j ∈ range n, C (c j * g ^ (p ^ n - p ^ j)) * X ^ p ^ j).natDegree ≤ p ^ (n - 1) :=
    natDegree_sum_le_of_forall_le _ _ fun j hj =>
      (natDegree_C_mul_X_pow_le _ _).trans
        (Nat.pow_le_pow_right (by omega) (by have := mem_range.mp hj; omega))
  exact lt_of_le_of_lt this (Nat.pow_lt_pow_right hp (by omega))

/-- In an absolutely integrally closed domain every additive (`p`-polynomial) equation
`w ^ Q - ∑_{j < n} c_j g ^ (Q - p ^ j) w ^ p ^ j = e` with `Q = p ^ n` has a solution, the
corresponding monic polynomial of degree `Q` having a root there. -/
private theorem exists_pow_sub_sum_mul_pow_eq {n : ℕ} (hB : IsAbsolutelyIntegrallyClosed B)
    (hQ : 0 < p ^ n) (c : ℕ → B)
    (hlow : ∀ (g : B) (e : B),
      (∑ j ∈ range n, C (c j * g ^ (p ^ n - p ^ j)) * X ^ p ^ j + C e).natDegree < p ^ n) :
    ∀ g e : B, ∃ w : B,
      w ^ p ^ n - ∑ j ∈ range n, c j * g ^ (p ^ n - p ^ j) * w ^ p ^ j = e := by
  intro g e
  set f : B[X] := X ^ p ^ n - (∑ j ∈ range n, C (c j * g ^ (p ^ n - p ^ j)) * X ^ p ^ j + C e)
  have hlt := hlow g e
  have hf : f.Monic := monic_X_pow_sub (degree_le_natDegree.trans_lt (by exact_mod_cast hlt))
  have hdeg : f.natDegree = p ^ n := by
    rw [natDegree_sub_eq_left_of_natDegree_lt (by simpa using hlt), natDegree_X_pow]
  obtain ⟨w, hw⟩ := (isAbsolutelyIntegrallyClosed_iff_exists_root B).mp hB f hf (by omega)
  refine ⟨w, ?_⟩
  simp only [f, eval_sub, eval_add, eval_pow, eval_X, eval_C, eval_finset_sum, eval_mul] at hw
  linear_combination hw

/-- If `L ^ Q = ∑_{j < n} c_j (xy) ^ (Q - p ^ j) L ^ p ^ j` with `Q = p ^ n`, then the quotient
`lam = L / xy` in a `B`-algebra is a root of the monic polynomial
`X ^ Q - ∑_{j < n} C (c j) * X ^ p ^ j`, hence is integral over `B`. -/
private theorem isIntegral_div_of_pow_sub_sum_eq_zero {K : Type*} [Field K] [Algebra B K]
    {n : ℕ} {c : ℕ → B} {x y L : B} {lam : K} (hpj : ∀ j ∈ range n, p ^ j < p ^ n)
    (hlow : ∀ (g : B) (e : B),
      (∑ j ∈ range n, C (c j * g ^ (p ^ n - p ^ j)) * X ^ p ^ j + C e).natDegree < p ^ n)
    (hd : algebraMap B K (x * y) ≠ 0)
    (hlam : lam * algebraMap B K (x * y) = algebraMap B K L)
    (hL : L ^ p ^ n - ∑ j ∈ range n, c j * (x * y) ^ (p ^ n - p ^ j) * L ^ p ^ j = 0) :
    IsIntegral B lam := by
  set g : B[X] := X ^ p ^ n - ∑ j ∈ range n, C (c j) * X ^ p ^ j
  have hg : g.Monic := by
    refine monic_X_pow_sub (degree_le_natDegree.trans_lt ?_)
    have := hlow 1 0
    simp only [one_pow, mul_one, map_zero, add_zero] at this
    exact_mod_cast this
  refine ⟨g, hg, ?_⟩
  have hmul : algebraMap B K (x * y) ^ p ^ n * eval₂ (algebraMap B K) lam g = 0 := by
    simp only [g, eval₂_sub, eval₂_X_pow, eval₂_finset_sum, eval₂_mul, eval₂_C, mul_sub,
      mul_sum]
    have h1 : algebraMap B K (x * y) ^ p ^ n * lam ^ p ^ n = algebraMap B K (L ^ p ^ n) := by
      rw [← mul_pow, mul_comm, hlam, map_pow]
    have h2 : ∀ j ∈ range n, algebraMap B K (x * y) ^ p ^ n *
        (algebraMap B K (c j) * lam ^ p ^ j) =
        algebraMap B K (c j * (x * y) ^ (p ^ n - p ^ j) * L ^ p ^ j) := by
      intro j hj
      rw [← Nat.sub_add_cancel (hpj j hj).le, pow_add]
      simp only [Nat.add_sub_cancel, map_mul, map_pow, ← hlam]
      ring
    rw [h1, sum_congr rfl h2, ← map_sum, ← map_sub, hL, map_zero]
  exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero _ hd)

/-- **The equational lemma.** In an absolutely integrally closed domain `B` of characteristic `p`,
let `x, y` be nonzero and suppose that for `Q = p^n` the element `s` satisfies
`s^Q - ∑_{j < n} c_j (xy)^{Q - p^j} s^{p^j} = α x^Q + β y^Q`. Then `s ∈ (x, y)`. -/
theorem mem_span_pair_of_frobenius_relation (hB : IsAbsolutelyIntegrallyClosed B)
    {x y s α β : B} (hx : x ≠ 0) (hy : y ≠ 0) (n : ℕ) (c : ℕ → B)
    (h : s ^ p ^ n - ∑ j ∈ range n, c j * (x * y) ^ (p ^ n - p ^ j) * s ^ p ^ j =
      α * x ^ p ^ n + β * y ^ p ^ n) :
    s ∈ Ideal.span {x, y} := by
  classical
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hpj : ∀ j ∈ range n, p ^ j < p ^ n := fun j hj =>
    Nat.pow_lt_pow_right hp (mem_range.mp hj)
  have hQ : 0 < p ^ n := pow_pos (by omega) n
  -- a polynomial `X ^ Q - (lower terms)` with all lower terms of degree `< Q` is monic of
  -- degree `Q`, so the additive equations have solutions in `B`
  have hlow := natDegree_sum_C_mul_X_pow_add_C_lt hp hQ c
  have root := exists_pow_sub_sum_mul_pow_eq hB hQ c hlow
  obtain ⟨w, hw⟩ := root y α
  obtain ⟨w', hw'⟩ := root x β
  set L := s - x * w - y * w' with hLdef
  have hpow : ∀ k, L ^ p ^ k = s ^ p ^ k - x ^ p ^ k * w ^ p ^ k - y ^ p ^ k * w' ^ p ^ k := by
    intro k
    rw [hLdef, sub_pow_char_pow, sub_pow_char_pow, mul_pow, mul_pow]
  have key : ∀ j ∈ range n, c j * (x * y) ^ (p ^ n - p ^ j) * L ^ p ^ j =
      c j * (x * y) ^ (p ^ n - p ^ j) * s ^ p ^ j -
        x ^ p ^ n * (c j * y ^ (p ^ n - p ^ j) * w ^ p ^ j) -
        y ^ p ^ n * (c j * x ^ (p ^ n - p ^ j) * w' ^ p ^ j) := by
    intro j hj
    rw [hpow, ← pow_sub_mul_pow x (hpj j hj).le, ← pow_sub_mul_pow y (hpj j hj).le, mul_pow]
    ring
  have hL : L ^ p ^ n - ∑ j ∈ range n, c j * (x * y) ^ (p ^ n - p ^ j) * L ^ p ^ j = 0 := by
    rw [sum_congr rfl key, sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, hpow n]
    linear_combination h - x ^ p ^ n * hw - y ^ p ^ n * hw'
  -- `L / xy` is integral over `B`, hence lies in `B`
  let K := FractionRing B
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  have hd : algebraMap B K (x * y) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective B K)).mpr hxy
  set lam : K := algebraMap B K L / algebraMap B K (x * y)
  have hlam : lam * algebraMap B K (x * y) = algebraMap B K L := div_mul_cancel₀ _ hd
  have hint : IsIntegral B lam := isIntegral_div_of_pow_sub_sum_eq_zero hpj hlow hd hlam hL
  have : IsIntegrallyClosed B := hB.isIntegrallyClosed
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hLb : L = x * y * b := by
    apply IsFractionRing.injective B K
    rw [map_mul, hb, ← hlam, mul_comm]
  rw [Ideal.mem_span_pair]
  refine ⟨w + y * b, w', ?_⟩
  have : s = L + x * w + y * w' := by rw [hLdef]; ring
  rw [this, hLb]
  ring

section Noetherian

variable {T : Type*} [CommRing T]

/-- If `x` is a nonzerodivisor and `y` is a nonzerodivisor modulo `x`, then every power of `y` is
a nonzerodivisor modulo every power of `x`. -/
theorem mem_span_singleton_pow_of_pow_mul_mem {x y : T} (hx : IsSMulRegular T x)
    (hy : ∀ c : T, y * c ∈ Ideal.span {x} → c ∈ Ideal.span {x}) (a b : ℕ) {c : T}
    (h : y ^ a * c ∈ Ideal.span {x ^ b}) : c ∈ Ideal.span {x ^ b} := by
  have hb : ∀ b : ℕ, ∀ c : T, y * c ∈ Ideal.span {x ^ b} → c ∈ Ideal.span {x ^ b} := by
    intro b
    induction b with
    | zero => intro c _; simp
    | succ b ih =>
      intro c hc
      have hc' : c ∈ Ideal.span {x ^ b} :=
        ih c (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow x b.le_succ) hc)
      obtain ⟨c', rfl⟩ := Ideal.mem_span_singleton'.mp hc'
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hc
      have hreg : IsSMulRegular T (x ^ b) := hx.pow b
      have : y * c' = d * x := by
        apply hreg
        simp only [smul_eq_mul]
        linear_combination (-1 : T) * hd
      obtain ⟨e, rfl⟩ :=
        Ideal.mem_span_singleton'.mp (hy c' (Ideal.mem_span_singleton'.mpr ⟨d, this.symm⟩))
      exact Ideal.mem_span_singleton'.mpr ⟨e, by ring⟩
  induction a generalizing c with
  | zero => simpa using h
  | succ a ih =>
    exact hb b c (ih (by rw [← mul_assoc, ← pow_succ]; exact h))

/-- Multiplying an element of `(x^e, y^e)` by `(xy)^{q - e}` lands in `(x^q, y^q)`. -/
theorem mul_pow_sub_mem_span_pow_pair {x y t : T} {e q : ℕ} (heq : e ≤ q)
    (ht : t ∈ Ideal.span {x ^ e, y ^ e}) : (x * y) ^ (q - e) * t ∈ Ideal.span {x ^ q, y ^ q} := by
  obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp ht
  refine Ideal.mem_span_pair.mpr ⟨a * y ^ (q - e), b * x ^ (q - e), ?_⟩
  rw [← pow_sub_mul_pow x heq, ← pow_sub_mul_pow y heq, mul_pow]
  ring

/-- **The intersection lemma.** Let `x, y` be a regular sequence on `T` and `N ≤ q`. If `x^N w`
and `y^N w` lie in `(x^q, y^q)`, then `w` is congruent to a multiple of `(xy)^{q - N}` modulo
`(x^q, y^q)`. -/
theorem exists_mul_pow_sub_mem_span_pow_pair {x y : T} (hx : IsSMulRegular T x)
    (hy : ∀ c : T, y * c ∈ Ideal.span {x} → c ∈ Ideal.span {x}) {N q : ℕ} (hNq : N ≤ q) {w : T}
    (h₁ : x ^ N * w ∈ Ideal.span {x ^ q, y ^ q}) (h₂ : y ^ N * w ∈ Ideal.span {x ^ q, y ^ q}) :
    ∃ v : T, w - (x * y) ^ (q - N) * v ∈ Ideal.span {x ^ q, y ^ q} := by
  have hxN : IsSMulRegular T (x ^ N) := hx.pow N
  have hxqN : IsSMulRegular T (x ^ (q - N)) := hx.pow (q - N)
  obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp h₁
  rw [← pow_sub_mul_pow x hNq] at hαβ
  -- `y^q β ∈ (x^N)`, so `β = x^N β'`
  have hβ : y ^ q * β ∈ Ideal.span {x ^ N} :=
    Ideal.mem_span_singleton'.mpr ⟨w - α * x ^ (q - N), by linear_combination (-1 : T) * hαβ⟩
  obtain ⟨β', rfl⟩ := Ideal.mem_span_singleton'.mp
    (mem_span_singleton_pow_of_pow_mul_mem hx hy q N hβ)
  have hw : w = α * x ^ (q - N) + β' * y ^ q := by
    apply hxN
    simp only [smul_eq_mul]
    linear_combination (-1 : T) * hαβ
  obtain ⟨γ, δ, hγδ⟩ := Ideal.mem_span_pair.mp h₂
  rw [hw, ← pow_sub_mul_pow x hNq] at hγδ
  -- `y^q (δ - y^N β') ∈ (x^{q - N})`
  have hδ : y ^ q * (δ - y ^ N * β') ∈ Ideal.span {x ^ (q - N)} :=
    Ideal.mem_span_singleton'.mpr ⟨y ^ N * α - γ * x ^ N, by
      linear_combination (-1 : T) * hγδ⟩
  obtain ⟨ε, hε⟩ := Ideal.mem_span_singleton'.mp
    (mem_span_singleton_pow_of_pow_mul_mem hx hy q (q - N) hδ)
  have hα : y ^ N * α = γ * x ^ N + ε * y ^ q := by
    apply hxqN
    simp only [smul_eq_mul]
    linear_combination (-1 : T) * hγδ - y ^ q * hε
  rw [← pow_sub_mul_pow y hNq] at hα
  -- `y^N (α - ε y^{q - N}) ∈ (x^N)`
  have hα' : y ^ N * (α - ε * y ^ (q - N)) ∈ Ideal.span {x ^ N} :=
    Ideal.mem_span_singleton'.mpr ⟨γ, by linear_combination (-1 : T) * hα⟩
  obtain ⟨ζ, hζ⟩ := Ideal.mem_span_singleton'.mp
    (mem_span_singleton_pow_of_pow_mul_mem hx hy N N hα')
  refine ⟨ε, Ideal.mem_span_pair.mpr ⟨ζ, β', ?_⟩⟩
  rw [hw, ← pow_sub_mul_pow x hNq, mul_pow]
  linear_combination x ^ (q - N) * hζ

/-- Each Frobenius power of `s` is congruent to a multiple of `(xy) ^ (p ^ j - N)` modulo
`(x ^ p ^ j, y ^ p ^ j)`: raising `s z = a x + b y` to the power `p ^ j` puts `z ^ p ^ j s ^ p ^ j`
in that ideal, so the intersection lemma applies. -/
private theorem exists_pow_sub_mul_pow_sub_mem_span_pow_pair {p : ℕ} [Fact p.Prime] [CharP T p]
    {x y z s a b : T} (hx : IsSMulRegular T x)
    (hy : ∀ c : T, y * c ∈ Ideal.span {x} → c ∈ Ideal.span {x})
    (hs : s * z = a * x + b * y) (N : ℕ)
    (hN : ∀ (q : ℕ) (u : T), z ^ q * u ∈ Ideal.span {x ^ q, y ^ q} →
      x ^ N * u ∈ Ideal.span {x ^ q, y ^ q} ∧ y ^ N * u ∈ Ideal.span {x ^ q, y ^ q}) :
    ∀ j : ℕ, ∃ v : T, N ≤ p ^ j →
      s ^ p ^ j - (x * y) ^ (p ^ j - N) * v ∈ Ideal.span {x ^ p ^ j, y ^ p ^ j} := by
  intro j
  by_cases hj : N ≤ p ^ j
  · have hmem : z ^ p ^ j * s ^ p ^ j ∈ Ideal.span {x ^ p ^ j, y ^ p ^ j} := by
      refine Ideal.mem_span_pair.mpr ⟨a ^ p ^ j, b ^ p ^ j, ?_⟩
      rw [← mul_pow, ← mul_pow, ← add_pow_char_pow, ← mul_pow, mul_comm z s, hs]
    obtain ⟨h₁, h₂⟩ := hN _ _ hmem
    obtain ⟨v, hv⟩ := exists_mul_pow_sub_mem_span_pow_pair hx hy hj h₁ h₂
    exact ⟨v, fun _ => hv⟩
  · exact ⟨0, fun h => absurd h hj⟩

/-- **Noetherian stabilization.** The ascending chain of submodules of `T ⧸ (x ^ N, y ^ N)` spanned
by the classes of `v N, …, v (m - 1)` stabilizes, so for some `n ≥ N` the class of `v n` is a
combination of the classes of the earlier `v j` with coefficients supported in `[N, n)`. -/
private theorem exists_finsupp_sub_sum_mem_span_pow_pair [IsNoetherianRing T] (x y : T) (N : ℕ)
    (v : ℕ → T) :
    ∃ (n : ℕ) (l : ℕ →₀ T), N ≤ n ∧ ↑l.support ⊆ Set.Ico N n ∧
      v n - ∑ j ∈ range n, l j * v j ∈ Ideal.span {x ^ N, y ^ N} := by
  classical
  set I : Ideal T := Ideal.span {x ^ N, y ^ N}
  let W : ℕ →o Submodule T (T ⧸ I) :=
    ⟨fun m => Submodule.span T ((fun j => Submodule.Quotient.mk (p := I) (v j)) '' Set.Ico N m),
      fun m m' h => Submodule.span_mono (Set.image_mono (Set.Ico_subset_Ico_right h))⟩
  obtain ⟨m₀, hm₀⟩ := (monotone_stabilizes_iff_noetherian.mpr inferInstance) W
  set n := max m₀ N
  have hNn : N ≤ n := le_max_right _ _
  have hstab : W (n + 1) = W n := by
    rw [← hm₀ n (le_max_left _ _), ← hm₀ (n + 1) (by omega)]
  have hmem : Submodule.Quotient.mk (p := I) (v n) ∈ W n := by
    rw [← hstab]
    exact Submodule.subset_span ⟨n, ⟨hNn, by omega⟩, rfl⟩
  obtain ⟨l, hl, hlv⟩ := (Finsupp.mem_span_image_iff_linearCombination T).mp hmem
  have hsupp : l.support ⊆ range n := fun j hj => by
    have := hl hj
    simp only [Set.mem_Ico] at this
    exact mem_range.mpr this.2
  rw [Finsupp.linearCombination_apply] at hlv
  rw [Finsupp.sum_of_support_subset l hsupp
    (fun i a => a • Submodule.Quotient.mk (p := I) (v i)) (fun _ _ => zero_smul _ _)] at hlv
  have h2 : Submodule.Quotient.mk (p := I) (∑ j ∈ range n, l j * v j) =
      ∑ j ∈ range n, l j • Submodule.Quotient.mk (p := I) (v j) := by
    rw [← Submodule.mkQ_apply, map_sum]
    exact sum_congr rfl fun j _ => by rw [← smul_eq_mul, map_smul, Submodule.mkQ_apply]
  have hI : v n - ∑ j ∈ range n, l j * v j ∈ I :=
    (Submodule.Quotient.eq I).mp (hlv.symm.trans h2.symm)
  exact ⟨n, l, hNn, hl, hI⟩

/-- **The Frobenius relation.** Let `T` be a Noetherian ring of characteristic `p`, let `x, y` be
a regular sequence on `T` (in the sense that `x` is a nonzerodivisor and `y` a nonzerodivisor
modulo `x`) and let `s z = a x + b y`. Suppose `x^N` and `y^N` kill, modulo `(x^q, y^q)`, every `u`
with `z^q u ∈ (x^q, y^q)`. Then for some `n` the element `s` satisfies a relation
`s^Q - ∑_{j < n} c_j (xy)^{Q - p^j} s^{p^j} ∈ (x^Q, y^Q)` with `Q = p^n`. -/
theorem exists_frobenius_relation [IsNoetherianRing T] {p : ℕ} [Fact p.Prime] [CharP T p]
    {x y z s a b : T} (hx : IsSMulRegular T x)
    (hy : ∀ c : T, y * c ∈ Ideal.span {x} → c ∈ Ideal.span {x})
    (hs : s * z = a * x + b * y) (N : ℕ)
    (hN : ∀ (q : ℕ) (u : T), z ^ q * u ∈ Ideal.span {x ^ q, y ^ q} →
      x ^ N * u ∈ Ideal.span {x ^ q, y ^ q} ∧ y ^ N * u ∈ Ideal.span {x ^ q, y ^ q}) :
    ∃ (n : ℕ) (c : ℕ → T) (α β : T),
      s ^ p ^ n - ∑ j ∈ range n, c j * (x * y) ^ (p ^ n - p ^ j) * s ^ p ^ j =
        α * x ^ p ^ n + β * y ^ p ^ n := by
  classical
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  -- each Frobenius power of `s` is a multiple of `(xy)^{p^j - N}` modulo `(x^{p^j}, y^{p^j})`
  choose v hv using exists_pow_sub_mul_pow_sub_mem_span_pow_pair hx hy hs N hN
  -- the ascending chain of submodules of `T ⧸ (x^N, y^N)` spanned by the classes of the `v j`
  obtain ⟨n, l, hNn, hl, hI⟩ := exists_finsupp_sub_sum_mem_span_pow_pair x y N v
  have hQ : N ≤ p ^ n := hNn.trans (Nat.lt_pow_self hp).le
  set J : Ideal T := Ideal.span {x ^ p ^ n, y ^ p ^ n}
  have htop : s ^ p ^ n - (x * y) ^ (p ^ n - N) * v n ∈ J := hv n hQ
  have hmid : (x * y) ^ (p ^ n - N) * (v n - ∑ j ∈ range n, l j * v j) ∈ J :=
    mul_pow_sub_mem_span_pow_pair hQ hI
  have hterm : ∀ j ∈ range n,
      l j * ((x * y) ^ (p ^ n - N) * v j - (x * y) ^ (p ^ n - p ^ j) * s ^ p ^ j) ∈ J := by
    intro j hj
    by_cases hlj : j ∈ l.support
    · have hNj : N ≤ p ^ j := by
        have := hl hlj
        simp only [Set.mem_Ico] at this
        exact this.1.trans (Nat.lt_pow_self hp).le
      have hjn : p ^ j ≤ p ^ n := Nat.pow_le_pow_right (by omega) (mem_range.mp hj).le
      have hsplit : (x * y) ^ (p ^ n - N) = (x * y) ^ (p ^ n - p ^ j) * (x * y) ^ (p ^ j - N) := by
        rw [← pow_add]; congr 1; omega
      have := mul_pow_sub_mem_span_pow_pair (x := x) (y := y) (q := p ^ n) hjn (hv j hNj)
      refine J.mul_mem_left _ ?_
      have heq : (x * y) ^ (p ^ n - N) * v j - (x * y) ^ (p ^ n - p ^ j) * s ^ p ^ j =
          -((x * y) ^ (p ^ n - p ^ j) * (s ^ p ^ j - (x * y) ^ (p ^ j - N) * v j)) := by
        rw [hsplit]; ring
      rw [heq]
      exact J.neg_mem this
    · rw [Finsupp.notMem_support_iff.mp hlj, zero_mul]
      exact J.zero_mem
  have hsum : ∑ j ∈ range n, l j * ((x * y) ^ (p ^ n - N) * v j) =
      (x * y) ^ (p ^ n - N) * ∑ j ∈ range n, l j * v j := by
    rw [mul_sum]
    exact sum_congr rfl fun _ _ => by ring
  have htot : s ^ p ^ n - ∑ j ∈ range n, l j * (x * y) ^ (p ^ n - p ^ j) * s ^ p ^ j ∈ J := by
    convert J.add_mem (J.add_mem htop hmid) (J.sum_mem hterm) using 1
    simp only [mul_sub, sum_sub_distrib]
    rw [hsum]
    have : ∀ j ∈ range n, l j * (x * y) ^ (p ^ n - p ^ j) * s ^ p ^ j =
        l j * ((x * y) ^ (p ^ n - p ^ j) * s ^ p ^ j) := fun _ _ => by ring
    rw [sum_congr rfl this]
    ring
  obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp htot
  exact ⟨n, l, α, β, hαβ.symm⟩

/-- **Colon killing from a good Noetherian subring.** Let `B` be an absolutely integrally closed
domain of characteristic `p` and `φ : T → B` a ring map from a Noetherian ring of characteristic
`p`. If `x, y` is a regular sequence on `T`, `s z = a x + b y` in `T`, and `x^N`, `y^N` kill every
`u` with `z^q u ∈ (x^q, y^q)` modulo `(x^q, y^q)`, then `φ s ∈ (φ x, φ y)B` as soon as `φ x` and
`φ y` are nonzero. -/
theorem mem_span_pair_of_mul_eq (hB : IsAbsolutelyIntegrallyClosed B) [IsNoetherianRing T]
    [CharP T p] (φ : T →+* B) {x y z s a b : T} (hx : IsSMulRegular T x)
    (hy : ∀ c : T, y * c ∈ Ideal.span {x} → c ∈ Ideal.span {x})
    (hs : s * z = a * x + b * y) (N : ℕ)
    (hN : ∀ (q : ℕ) (u : T), z ^ q * u ∈ Ideal.span {x ^ q, y ^ q} →
      x ^ N * u ∈ Ideal.span {x ^ q, y ^ q} ∧ y ^ N * u ∈ Ideal.span {x ^ q, y ^ q})
    (hφx : φ x ≠ 0) (hφy : φ y ≠ 0) :
    φ s ∈ Ideal.span {φ x, φ y} := by
  obtain ⟨n, c, α, β, h⟩ := exists_frobenius_relation (p := p) hx hy hs N hN
  refine hB.mem_span_pair_of_frobenius_relation hφx hφy n (fun j => φ (c j))
    (α := φ α) (β := φ β) ?_
  simpa only [map_sub, map_sum, map_mul, map_pow, map_add] using congrArg φ h

end Noetherian

end IsAbsolutelyIntegrallyClosed
