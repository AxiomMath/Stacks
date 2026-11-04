module

public import StacksFrontier.NumberTheory.BombieriStepanov.Basic

/-!
# The Bombieri–Stepanov upper bound

Let `K` be a function field over the finite field `k` with `q = r²` elements, `r` a power of the
characteristic `p`. Let `P₀` be a place of degree one with residue field `k`. Suppose every
`o ≥ γ` is the pole order at `P₀` of some function with no other pole. By Riemann–Roch this holds
with `γ = 2g`, `g` the genus.

Let `σ : K → K` preserve every `L(n P₀)`. Let `S` be a finite set of places other than `P₀`, of
positive degree, at which each `g ∈ L(n P₀)` satisfies `σ g ≡ b^q` and `g ≡ b` modulo the
maximal ideal for some `b`. With `σ = id`, `S` can be any set of rational places other than `P₀`.
Then

`#S + 1 ≤ q + (2γ + 1) r`  as soon as  `r > γ² + 3γ + 1`.

This is the argument of Stepanov as streamlined by Bombieri. Take bases `h_i` of `L(m P₀)`,
`m = r - 1`, and `g_j` of `L(n P₀)`, made of functions of distinct pole orders. Counting gives a
nontrivial relation `∑_j f_j^r σ(g_j) = 0` with `f_j` in the span of the `h_i`: the domain has
`q^{(r - γ)(n - γ + 1)}` elements, more than `L((r m + n) P₀)`. The auxiliary function
`Φ = ∑_j f_j^r g_j^q = (∑_j f_j g_j^r)^r` is nonzero, because the products `h_i g_j^r` have
distinct pole orders `(γ + i) + r (γ + j)`. It lies in `L((r m + q n) P₀)`, and it vanishes to
order at least `r` at every place of `S`. Write `g_j ≡ b_j`. Then `Φ ≡ (∑_j f_j b_j^r)^r` modulo
the `q`-th power of the maximal ideal. The `r`-th root `∑_j f_j b_j^r` vanishes at the place,
since its `r`-th power is `≡ ∑_j f_j^r σ(g_j) = 0`. Zeros are bounded by poles, so
`r #S ≤ r m + q n`.

## Main results

* `Stacks.BombieriStepanov.sum_ne_zero_of_val_injOn`: a sum whose nonzero terms have pairwise
  distinct valuations is nonzero.
* `Stacks.BombieriStepanov.finite_and_natCard_divisorSpace_le`: `#L(D) ≤ q ^ (deg D + 1)`.
* `Stacks.BombieriStepanov.mul_sum_deg_le`: the Bombieri–Stepanov bound.
* `Stacks.BombieriStepanov.sum_deg_add_one_le`: its numerical form,
  `∑_{P ∈ S} deg P + 1 ≤ q + (2g + 1) √q` for `√q > g² + 3g + 1`.
* `Stacks.BombieriStepanov.card_le_of_isResidueRational`: at most `q + (2g + 1) √q`
  residue-rational places of degree one.

## References

* E. Bombieri, *Counting points on curves over finite fields (d'après S. A. Stepanov)*,
  Séminaire Bourbaki 430 (1973).
* H. Stichtenoth, *Algebraic function fields and codes*, Section 5.2.
-/

@[expose] public noncomputable section

namespace Stacks.BombieriStepanov

open Finset

variable {k K Pl : Type*} [Field k] [Field K] [Algebra k K]

/-! ### Arithmetic in `WithTop ℤ` -/

/-- A positive multiple of `⊤` in `WithTop ℤ` is `⊤`. -/
theorem nsmul_top_withTop {n : ℕ} (hn : n ≠ 0) : n • (⊤ : WithTop ℤ) = ⊤ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [succ_nsmul, WithTop.add_top]

/-- In `WithTop ℤ`, if `1 ≤ n • z` with `n ≠ 0`, then `n ≤ n • z`. -/
theorem natCast_le_nsmul_of_one_le_nsmul {n : ℕ} (hn : n ≠ 0) {z : WithTop ℤ}
    (h : ((1 : ℤ) : WithTop ℤ) ≤ n • z) : (((n : ℤ)) : WithTop ℤ) ≤ n • z := by
  induction z with
  | top => rw [nsmul_top_withTop hn]; exact le_top
  | coe a =>
    rw [← WithTop.coe_nsmul] at h ⊢
    have h' : (1 : ℤ) ≤ n • a := WithTop.coe_le_coe.1 h
    rw [nsmul_eq_mul] at h'
    have hn' : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have ha : 1 ≤ a := by
      by_contra hlt
      push Not at hlt
      nlinarith
    refine WithTop.coe_le_coe.2 ?_
    rw [nsmul_eq_mul]
    nlinarith

/-- In `WithTop ℤ`, if `1 ≤ z`, then `n ≤ n • z`. -/
theorem natCast_le_nsmul_of_one_le (n : ℕ) {z : WithTop ℤ} (h : ((1 : ℤ) : WithTop ℤ) ≤ z) :
    (((n : ℤ)) : WithTop ℤ) ≤ n • z := by
  have := nsmul_le_nsmul_right h n
  rwa [← WithTop.coe_nsmul, nsmul_eq_mul, mul_one] at this

/-! ### Sums of elements of distinct valuations -/

/-- **Distinct valuations do not cancel.** If the nonzero terms of a finite sum have pairwise
distinct valuations and some term is nonzero, the sum is nonzero. -/
theorem sum_ne_zero_of_val_injOn (w : AddValuation K (WithTop ℤ)) {T : Type*} (s : Finset T)
    (x : T → K) (hne : ∃ t ∈ s, x t ≠ 0)
    (hinj : ∀ t ∈ s, ∀ t' ∈ s, x t ≠ 0 → x t' ≠ 0 → w (x t) = w (x t') → t = t') :
    ∑ t ∈ s, x t ≠ 0 := by
  classical
  set s' := s.filter fun t => x t ≠ 0 with hs'
  have hsne : s'.Nonempty := by
    obtain ⟨t, ht, hx⟩ := hne
    exact ⟨t, by simp [hs', ht, hx]⟩
  obtain ⟨j, hj, hmin⟩ := s'.exists_min_image (fun t => w (x t)) hsne
  have hj' : j ∈ s ∧ x j ≠ 0 := by simpa [hs'] using hj
  have hsum : ∑ t ∈ s, x t = ∑ t ∈ s', x t := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs with h0
    · rfl
    · push Not at h0
      exact h0
  have hxj : w (x j) ≠ ⊤ := (AddValuation.ne_top_iff w).2 hj'.2
  have hrest : w (x j) < w (∑ t ∈ s'.erase j, x t) := by
    refine AddValuation.map_lt_sum w hxj fun t ht => ?_
    obtain ⟨htj, hts⟩ := Finset.mem_erase.1 ht
    have hts' : t ∈ s ∧ x t ≠ 0 := by simpa [hs'] using hts
    exact lt_of_le_of_ne (hmin t hts) fun e => htj (hinj j hj'.1 t hts'.1 hj'.2 hts'.2 e).symm
  have htot : w (∑ t ∈ s', x t) = w (x j) := by
    rw [← Finset.add_sum_erase s' _ hj, AddValuation.map_add_eq_of_lt_left w hrest]
  intro h0
  rw [← hsum, h0, AddValuation.map_zero] at htot
  exact hxj htot.symm

/-! ### Closure properties of `L(m P₀)` -/

section Closure

variable {v : Pl → AddValuation K (WithTop ℤ)} {P₀ : Pl}

/-- The constant `1` lies in `L(0 · P₀)`. -/
theorem one_mem_poleSpace : (1 : K) ∈ poleSpace v P₀ 0 := by
  refine ⟨?_, fun P _ => ?_⟩ <;> simp [AddValuation.map_one]

/-- If `f ∈ L(a P₀)` and `g ∈ L(b P₀)`, then `f * g ∈ L((a + b) P₀)`. -/
theorem mul_mem_poleSpace {a b : ℕ} {f g : K} (hf : f ∈ poleSpace v P₀ a)
    (hg : g ∈ poleSpace v P₀ b) : f * g ∈ poleSpace v P₀ (a + b) := by
  refine ⟨?_, fun P hP => ?_⟩
  · rw [AddValuation.map_mul]
    have := add_le_add hf.1 hg.1
    refine le_trans (le_of_eq ?_) this
    rw [← WithTop.coe_add]
    congr 1
    push_cast
    ring
  · rw [AddValuation.map_mul]
    exact add_nonneg (hf.2 P hP) (hg.2 P hP)

/-- If `f ∈ L(a P₀)`, then `f ^ n ∈ L(n a P₀)`. -/
theorem pow_mem_poleSpace {a : ℕ} {f : K} (hf : f ∈ poleSpace v P₀ a) (n : ℕ) :
    f ^ n ∈ poleSpace v P₀ (n * a) := by
  induction n with
  | zero => simpa using one_mem_poleSpace
  | succ n ih =>
    rw [pow_succ, show (n + 1) * a = n * a + a by ring]
    exact mul_mem_poleSpace ih hf

/-- `L(a P₀)` is closed under addition. -/
theorem add_mem_poleSpace {a : ℕ} {f g : K} (hf : f ∈ poleSpace v P₀ a)
    (hg : g ∈ poleSpace v P₀ a) : f + g ∈ poleSpace v P₀ a :=
  ⟨AddValuation.map_le_add _ hf.1 hg.1,
    fun P hP => AddValuation.map_le_add _ (hf.2 P hP) (hg.2 P hP)⟩

/-- A finite sum of elements of `L(a P₀)` lies in `L(a P₀)`. -/
theorem sum_mem_poleSpace {a : ℕ} {T : Type*} (s : Finset T) {f : T → K}
    (hf : ∀ t ∈ s, f t ∈ poleSpace v P₀ a) : ∑ t ∈ s, f t ∈ poleSpace v P₀ a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero_mem_poleSpace (v := v) P₀ a
  | insert t s ht ih =>
    rw [Finset.sum_insert ht]
    exact add_mem_poleSpace (hf t (Finset.mem_insert_self t s))
      (ih fun u hu => hf u (Finset.mem_insert_of_mem hu))

/-- If `f ∈ L(a P₀)` and `c ∈ k`, then `c f ∈ L(a P₀)`. -/
theorem smul_mem_poleSpace [Fintype k] {a : ℕ} {f : K} (hf : f ∈ poleSpace v P₀ a) (c : k) :
    algebraMap k K c * f ∈ poleSpace v P₀ a :=
  ⟨hf.1.trans (le_val_algebraMap_mul _ c f),
    fun P hP => (hf.2 P hP).trans (le_val_algebraMap_mul _ c f)⟩

/-- `L(a P₀)` is closed under subtraction. -/
theorem sub_mem_poleSpace' {a : ℕ} {f g : K} (hf : f ∈ poleSpace v P₀ a)
    (hg : g ∈ poleSpace v P₀ a) : f - g ∈ poleSpace v P₀ a :=
  ⟨AddValuation.map_le_sub _ hf.1 hg.1,
    fun P hP => AddValuation.map_le_sub _ (hf.2 P hP) (hg.2 P hP)⟩

end Closure

/-! ### The auxiliary function vanishes to order `r` -/

section Vanishing

variable (p e : ℕ) [Fact p.Prime] [CharP K p]

/-- The local computation at a place `P` of `S`. Let `g_j ≡ b_j` and `σ(g_j) ≡ b_j^q` with
`q = r²`, `r = p^e`. Let the `f_j` be integral and satisfy `∑_j f_j^r σ(g_j) = 0`. Then
`Φ = ∑_j f_j^r g_j^q` vanishes to order at least `r`. -/
theorem le_val_auxiliary (w : AddValuation K (WithTop ℤ)) {T : Type*} (s : Finset T)
    (f g σg b : T → K) (hf : ∀ j ∈ s, 0 ≤ w (f j))
    (hb : ∀ j ∈ s, ((1 : ℤ) : WithTop ℤ) ≤ w (g j - b j))
    (hσb : ∀ j ∈ s, ((1 : ℤ) : WithTop ℤ) ≤ w (σg j - b j ^ (p ^ e * p ^ e)))
    (hrel : ∑ j ∈ s, f j ^ p ^ e * σg j = 0) :
    (((p ^ e : ℕ) : ℤ) : WithTop ℤ) ≤ w (∑ j ∈ s, f j ^ p ^ e * g j ^ (p ^ e * p ^ e)) := by
  set r := p ^ e with hr
  have hr0 : r ≠ 0 := pow_ne_zero e (Fact.out : p.Prime).ne_zero
  have hq : r * r = p ^ (e + e) := by rw [hr, ← pow_add]
  set y := ∑ j ∈ s, f j * b j ^ r with hy
  have hyr : y ^ r = ∑ j ∈ s, f j ^ r * b j ^ (r * r) := by
    rw [hy, hr, sum_pow_char_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow, ← pow_mul]
  -- the difference `Φ - y^r`
  have hdiff : ∑ j ∈ s, f j ^ r * g j ^ (r * r) - y ^ r
      = ∑ j ∈ s, f j ^ r * (g j - b j) ^ (r * r) := by
    rw [hyr, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hq, sub_pow_char_pow, ← hq]
    ring
  have hdiffval : (((r : ℕ) : ℤ) : WithTop ℤ)
      ≤ w (∑ j ∈ s, f j ^ r * g j ^ (r * r) - y ^ r) := by
    rw [hdiff]
    refine AddValuation.map_le_sum w fun j hj => ?_
    rw [AddValuation.map_mul, AddValuation.map_pow, AddValuation.map_pow]
    have h1 : 0 ≤ r • w (f j) := nsmul_nonneg (hf j hj) r
    have h2 : (((r * r : ℕ) : ℤ) : WithTop ℤ) ≤ (r * r) • w (g j - b j) :=
      natCast_le_nsmul_of_one_le (r * r) (hb j hj)
    have h3 : (((r : ℕ) : ℤ) : WithTop ℤ) ≤ (((r * r : ℕ) : ℤ) : WithTop ℤ) := by
      exact_mod_cast Nat.le_mul_of_pos_left r (Nat.pos_of_ne_zero hr0)
    calc (((r : ℕ) : ℤ) : WithTop ℤ) = 0 + (((r : ℕ) : ℤ) : WithTop ℤ) := (zero_add _).symm
      _ ≤ r • w (f j) + (r * r) • w (g j - b j) := add_le_add h1 (h3.trans h2)
  -- `y^r` vanishes
  have hyrval : ((1 : ℤ) : WithTop ℤ) ≤ w (y ^ r) := by
    have : y ^ r = ∑ j ∈ s, f j ^ r * (b j ^ (r * r) - σg j) := by
      rw [hyr]
      have := hrel
      rw [← sub_zero (∑ j ∈ s, f j ^ r * b j ^ (r * r)), ← this, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this]
    refine AddValuation.map_le_sum w fun j hj => ?_
    rw [AddValuation.map_mul, AddValuation.map_pow, AddValuation.map_sub_swap]
    calc ((1 : ℤ) : WithTop ℤ) = 0 + ((1 : ℤ) : WithTop ℤ) := (zero_add _).symm
      _ ≤ r • w (f j) + w (σg j - b j ^ (r * r)) :=
        add_le_add (nsmul_nonneg (hf j hj) r) (hσb j hj)
  have hyrval' : (((r : ℕ) : ℤ) : WithTop ℤ) ≤ w (y ^ r) := by
    rw [AddValuation.map_pow] at hyrval ⊢
    exact natCast_le_nsmul_of_one_le_nsmul hr0 hyrval
  have := AddValuation.map_le_add w hyrval' hdiffval
  rwa [add_sub_cancel] at this

end Vanishing

/-! ### Riemann–Roch spaces of effective divisors -/

section DivisorSpace

variable (v : Pl → AddValuation K (WithTop ℤ))

/-- The Riemann–Roch space `L(D)` of an effective divisor `D`: the `f` with `ord_P f ≥ -D(P)` at
every place. -/
def divisorSpace (D : Pl → ℕ) : Set K :=
  {f | ∀ P, ((-(D P : ℤ) : ℤ) : WithTop ℤ) ≤ v P f}

variable {v} {deg : Pl → ℕ}

/-- `L(D)` is finite with at most `q ^ (deg D + 1)` elements, `D` being supported on a finite set
`U` containing a residue-rational place `P₀` of degree one. The orders at `P₀` of the nonzero
elements lie in `[-D(P₀), deg D - D(P₀)]`. -/
theorem finite_and_natCard_divisorSpace_le [Fintype k] (hD : HasDegreeFormula v deg) {P₀ : Pl}
    (hP₀ : deg P₀ = 1) (hres : IsResidueRational (k := k) (v P₀)) (D : Pl → ℕ) (U : Finset Pl)
    (hU : ∀ P, P ∉ U → D P = 0) (hP₀U : P₀ ∈ U) :
    (divisorSpace v D).Finite ∧
      Nat.card (divisorSpace v D) ≤ Fintype.card k ^ (∑ P ∈ U, deg P * D P + 1) := by
  classical
  set B : ℤ := ∑ P ∈ U.erase P₀, (deg P : ℤ) * D P with hB
  have hmem : ∀ f ∈ divisorSpace v D, f ≠ 0 →
      ordZ (v P₀) f ∈ Finset.Icc (-(D P₀ : ℤ)) B := by
    intro f hf hf0
    have hle : ∀ P, -(D P : ℤ) ≤ ordZ (v P) f := fun P => (le_ordZ_iff hf0 _).2 (hf P)
    have h := sum_ordZ_le_zero hD hf0 U fun P hP => by
      have := hle P
      rw [hU P hP] at this
      simpa using this
    rw [← Finset.add_sum_erase U _ hP₀U, hP₀] at h
    have hrest : -B ≤ ∑ P ∈ U.erase P₀, (deg P : ℤ) * ordZ (v P) f := by
      rw [hB, ← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun P _ => ?_
      have := hle P
      have hdeg : (0 : ℤ) ≤ deg P := Nat.cast_nonneg _
      nlinarith
    refine Finset.mem_Icc.2 ⟨hle P₀, ?_⟩
    push_cast at h
    linarith
  obtain ⟨hfin, hcard⟩ := finite_and_natCard_le_of_ordZ_mem hres (divisorSpace v D)
    (fun P => by simp) (fun f hf g hg c P => AddValuation.map_le_sub _ (hf P)
      ((hg P).trans (le_val_algebraMap_mul _ c g))) _ hmem
  refine ⟨hfin, hcard.trans (Nat.pow_le_pow_right Fintype.card_pos ?_)⟩
  rw [Int.card_Icc]
  have hsplit : ((∑ P ∈ U, deg P * D P : ℕ) : ℤ) = D P₀ + B := by
    rw [← Finset.add_sum_erase U _ hP₀U, hP₀, hB]
    push_cast
    ring
  have hBnn : 0 ≤ B := Finset.sum_nonneg fun P _ => by positivity
  omega

end DivisorSpace

/-! ### The Bombieri–Stepanov bound -/

/-- **The Bombieri–Stepanov bound, in its general form.** Let `r = p ^ e`, `Q = r²`, and let `P₀`
be a residue-rational place of degree one with `#L(o P₀) ≥ q ^ (o + 1 - g)` for every `o`. Let
`σ : K → K` send `L(n P₀)` into `L(n P₁)` for a place `P₁` of degree one. Let `S` be a finite set
of places other than `P₀` at which `σ y ≡ y ^ Q` for every `y ∈ L(n P₀)`. If `m < r` and
`r m + n + 1 < (m + 1 - g)(n + 1 - g)`, then `r · ∑_{P ∈ S} deg P ≤ r m + Q n`. -/
theorem mul_sum_deg_le [Fintype k] (p e : ℕ) [Fact p.Prime] [CharP K p]
    {v : Pl → AddValuation K (WithTop ℤ)} {deg : Pl → ℕ} (hD : HasDegreeFormula v deg)
    {P₀ P₁ : Pl} (hP₀ : deg P₀ = 1) (hP₁ : deg P₁ = 1) (hres : IsResidueRational (k := k) (v P₀))
    (g : ℕ) (hRR : ∀ o, Fintype.card k ^ (o + 1 - g) ≤ Nat.card (poleSpace v P₀ o))
    (σ : K → K) (n : ℕ) (hσ : ∀ y ∈ poleSpace v P₀ n, σ y ∈ poleSpace v P₁ n)
    (m : ℕ) (hm : m < p ^ e) (hmn : p ^ e * m + n + 1 < (m + 1 - g) * (n + 1 - g))
    (S : Finset Pl) (hS₀ : P₀ ∉ S)
    (hS : ∀ P ∈ S, ∀ y ∈ poleSpace v P₀ n,
      ((1 : ℤ) : WithTop ℤ) ≤ v P (σ y - y ^ (p ^ e * p ^ e))) :
    p ^ e * ∑ P ∈ S, deg P ≤ p ^ e * m + p ^ e * p ^ e * n := by
  classical
  set r := p ^ e with hr
  have hr0 : r ≠ 0 := pow_ne_zero e (Fact.out : p.Prime).ne_zero
  have hq1 : 1 < Fintype.card k := Fintype.one_lt_card
  -- the finite spaces `L(m P₀)` and `L(n P₀)`
  have hLm := finite_and_natCard_poleSpace_le hD hP₀ hres m
  have hLn := finite_and_natCard_poleSpace_le hD hP₀ hres n
  -- the orders occurring in `L(n P₀)`, with representatives
  set J : Finset ℤ := (Finset.Icc (-(n : ℤ)) 0).filter
    (fun z => ∃ y ∈ poleSpace v P₀ n, y ≠ 0 ∧ ordZ (v P₀) y = z) with hJ
  have hJcard : n + 1 - g ≤ J.card := by
    have hc := (finite_and_natCard_le_of_ordZ_mem hres (poleSpace v P₀ n)
      (zero_mem_poleSpace P₀ n) (fun f hf g hg c => sub_mem_poleSpace hf hg c) J
      fun f hf hf0 => Finset.mem_filter.2
        ⟨ordZ_mem_Icc_of_mem_poleSpace hD hP₀ hf hf0, f, hf, hf0, rfl⟩).2
    exact (Nat.pow_le_pow_iff_right hq1).1 ((hRR n).trans hc)
  have hrep : ∀ z : J, ∃ y ∈ poleSpace v P₀ n, y ≠ 0 ∧ ordZ (v P₀) y = z := fun z =>
    (Finset.mem_filter.1 z.2).2
  choose gz hgzL hgz0 hgzord using hrep
  -- the counting
  have : Finite (poleSpace v P₀ m) := hLm.1.to_subtype
  set D' : Pl → ℕ := Pi.single P₀ (r * m) + Pi.single P₁ n with hD'
  have hT := finite_and_natCard_divisorSpace_le hD hP₀ hres D' {P₀, P₁}
    (fun P hP => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hP
      simp [hD', hP.1, hP.2]) (by simp)
  have : Finite (divisorSpace v D') := hT.1.to_subtype
  have hTsum : ∑ P ∈ ({P₀, P₁} : Finset Pl), deg P * D' P ≤ r * m + n := by
    by_cases h01 : P₀ = P₁
    · subst h01
      simp [hD', hP₀]
    · rw [Finset.sum_pair h01]
      simp [hD', h01, Ne.symm h01, hP₀, hP₁]
  let Ψ : (J → poleSpace v P₀ m) → divisorSpace v D' := fun f =>
    ⟨∑ z, (f z : K) ^ r * σ (gz z), by
      intro P
      refine AddValuation.map_le_sum _ fun z _ => ?_
      rw [AddValuation.map_mul, AddValuation.map_pow]
      have hf := (f z).2
      have hσz := hσ _ (hgzL z)
      have h1 : (((-((Pi.single P₀ (r * m) : Pl → ℕ) P : ℤ)) : ℤ) : WithTop ℤ) ≤ r • v P (f z) := by
        by_cases hP : P = P₀
        · subst hP
          have := nsmul_le_nsmul_right hf.1 r
          rw [← WithTop.coe_nsmul] at this
          refine le_trans (le_of_eq ?_) this
          simp
        · simpa [Pi.single_apply, hP] using nsmul_nonneg (hf.2 P hP) r
      have h2 : (((-((Pi.single P₁ n : Pl → ℕ) P : ℤ)) : ℤ) : WithTop ℤ) ≤ v P (σ (gz z)) := by
        by_cases hP : P = P₁
        · subst hP
          simpa using hσz.1
        · simpa [Pi.single_apply, hP] using hσz.2 P hP
      have := add_le_add h1 h2
      refine le_trans (le_of_eq ?_) this
      rw [← WithTop.coe_add]
      congr 1
      simp only [hD', Pi.add_apply, Nat.cast_add]
      ring⟩
  have hnotinj : ¬ Function.Injective Ψ := by
    intro hinj
    have hle := Nat.card_le_card_of_injective Ψ hinj
    rw [Nat.card_fun] at hle
    have hlow : Fintype.card k ^ ((m + 1 - g) * (n + 1 - g)) ≤
        Nat.card (poleSpace v P₀ m) ^ Nat.card J := by
      rw [Nat.card_eq_fintype_card (α := J), Fintype.card_coe]
      calc Fintype.card k ^ ((m + 1 - g) * (n + 1 - g))
          ≤ Fintype.card k ^ ((m + 1 - g) * J.card) :=
            Nat.pow_le_pow_right Fintype.card_pos (Nat.mul_le_mul_left _ hJcard)
        _ = (Fintype.card k ^ (m + 1 - g)) ^ J.card := by rw [pow_mul]
        _ ≤ Nat.card (poleSpace v P₀ m) ^ J.card := Nat.pow_le_pow_left (hRR m) _
    have hup : Nat.card (divisorSpace v D') ≤ Fintype.card k ^ (r * m + n + 1) :=
      hT.2.trans (Nat.pow_le_pow_right Fintype.card_pos (by omega))
    have := (Nat.pow_lt_pow_iff_right hq1).2 hmn
    omega
  obtain ⟨f, f', hff', hΨ⟩ : ∃ f f', f ≠ f' ∧ Ψ f = Ψ f' := by
    by_contra h
    push Not at h
    exact hnotinj fun a b hab => by_contra fun hne => h a b hne hab
  -- the difference
  set φ : J → K := fun z => (f z : K) - f' z with hφ
  have hφL : ∀ z, φ z ∈ poleSpace v P₀ m := fun z => sub_mem_poleSpace' (f z).2 (f' z).2
  have hφne : ∃ z, φ z ≠ 0 := by
    by_contra h
    push Not at h
    exact hff' (funext fun z => Subtype.ext (sub_eq_zero.1 (h z)))
  have hrel : ∑ z, φ z ^ r * σ (gz z) = 0 := by
    have := congrArg Subtype.val hΨ
    simp only [Ψ] at this
    rw [hφ]
    simp only [hr, sub_pow_char_pow, sub_mul, Finset.sum_sub_distrib]
    rw [← hr, this, sub_self]
  -- the auxiliary function
  set G := ∑ z, φ z * gz z ^ r with hG
  set Φ := ∑ z, φ z ^ r * gz z ^ (r * r) with hΦ
  have hΦG : Φ = G ^ r := by
    rw [hΦ, hG, hr, sum_pow_char_pow]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [mul_pow, ← pow_mul]
  have hG0 : G ≠ 0 := by
    refine sum_ne_zero_of_val_injOn (v P₀) _ _ ?_ ?_
    · obtain ⟨z, hz⟩ := hφne
      exact ⟨z, Finset.mem_univ _, mul_ne_zero hz (pow_ne_zero _ (hgz0 z))⟩
    · intro z _ z' _ hz hz' heq
      have hφz : φ z ≠ 0 := left_ne_zero_of_mul hz
      have hφz' : φ z' ≠ 0 := left_ne_zero_of_mul hz'
      have hord := congrArg (fun x => x) heq
      rw [← coe_ordZ hz, ← coe_ordZ hz'] at hord
      have hord' := WithTop.coe_injective hord
      rw [ordZ_mul hφz (pow_ne_zero _ (hgz0 z)), ordZ_mul hφz' (pow_ne_zero _ (hgz0 z')),
        ordZ_pow (hgz0 z), ordZ_pow (hgz0 z'), hgzord, hgzord] at hord'
      have ha := Finset.mem_Icc.1 (ordZ_mem_Icc_of_mem_poleSpace hD hP₀ (hφL z) hφz)
      have ha' := Finset.mem_Icc.1 (ordZ_mem_Icc_of_mem_poleSpace hD hP₀ (hφL z') hφz')
      have hdiff : (r : ℤ) * ((z : ℤ) - z') = ordZ (v P₀) (φ z') - ordZ (v P₀) (φ z) := by
        linarith
      have hzero : (z : ℤ) - z' = 0 := by
        have hlt : |(r : ℤ) * ((z : ℤ) - z')| < r := by
          rw [hdiff, abs_lt]
          have : (m : ℤ) < r := by exact_mod_cast hm
          constructor <;> linarith
        have hr' : (0 : ℤ) < r := by exact_mod_cast Nat.pos_of_ne_zero hr0
        rcases lt_trichotomy ((z : ℤ) - z') 0 with h | h | h
        · rw [abs_lt] at hlt
          nlinarith
        · exact h
        · rw [abs_lt] at hlt
          nlinarith
      exact Subtype.ext (by linarith)
  have hΦ0 : Φ ≠ 0 := by rw [hΦG]; exact pow_ne_zero _ hG0
  -- the pole and the zeros of `Φ`
  have hΦL : Φ ∈ poleSpace v P₀ (r * m + r * r * n) := by
    refine sum_mem_poleSpace _ fun z _ => ?_
    exact mul_mem_poleSpace (pow_mem_poleSpace (hφL z) r) (pow_mem_poleSpace (hgzL z) (r * r))
  have hzero : ∀ P ∈ S, ((r : ℤ) : WithTop ℤ) ≤ v P Φ := by
    intro P hP
    have hPP₀ : P ≠ P₀ := fun h => hS₀ (h ▸ hP)
    have := le_val_auxiliary p e (v P) Finset.univ φ gz (fun z => σ (gz z)) gz
      (fun z _ => (hφL z).2 P hPP₀) (fun z _ => by simp) (fun z _ => hS P hP _ (hgzL z))
      hrel
    exact_mod_cast this
  have hsum := sum_ordZ_le_zero hD hΦ0 (insert P₀ S) fun P hP =>
    (le_ordZ_iff hΦ0 0).2 (hΦL.2 P fun h => hP (h ▸ Finset.mem_insert_self _ _))
  rw [Finset.sum_insert hS₀, hP₀] at hsum
  push_cast at hsum
  have hP₀ord : -((r * m + r * r * n : ℕ) : ℤ) ≤ ordZ (v P₀) Φ := (le_ordZ_iff hΦ0 _).2 hΦL.1
  have hSord : (r : ℤ) * ∑ P ∈ S, (deg P : ℤ) ≤ ∑ P ∈ S, (deg P : ℤ) * ordZ (v P) Φ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun P hP => ?_
    have := (le_ordZ_iff hΦ0 _).2 (hzero P hP)
    have hdeg : (0 : ℤ) ≤ deg P := Nat.cast_nonneg _
    nlinarith
  have : ((r * ∑ P ∈ S, deg P : ℕ) : ℤ) ≤ ((r * m + r * r * n : ℕ) : ℤ) := by
    push_cast at hP₀ord hSord ⊢
    linarith
  exact_mod_cast this

/-- **The Bombieri–Stepanov bound, numerical form.** In the situation of `mul_sum_deg_le`, let
`#L(o P₀) ≥ q ^ (o + 1 - g)` for every `o` (Riemann's inequality) and `r > g² + 3g + 1`. Then
`∑_{P ∈ S} deg P + 1 ≤ r² + (2g + 1) r`. -/
theorem sum_deg_add_one_le [Fintype k] (p e : ℕ) [Fact p.Prime] [CharP K p]
    {v : Pl → AddValuation K (WithTop ℤ)} {deg : Pl → ℕ} (hD : HasDegreeFormula v deg)
    {P₀ P₁ : Pl} (hP₀ : deg P₀ = 1) (hP₁ : deg P₁ = 1) (hres : IsResidueRational (k := k) (v P₀))
    (g : ℕ) (hRR : ∀ o, Fintype.card k ^ (o + 1 - g) ≤ Nat.card (poleSpace v P₀ o))
    (hr : g ^ 2 + 3 * g + 1 < p ^ e) (σ : K → K)
    (hσ : ∀ n, ∀ y ∈ poleSpace v P₀ n, σ y ∈ poleSpace v P₁ n)
    (S : Finset Pl) (hS₀ : P₀ ∉ S)
    (hS : ∀ P ∈ S, ∀ n, ∀ y ∈ poleSpace v P₀ n,
      ((1 : ℤ) : WithTop ℤ) ≤ v P (σ y - y ^ (p ^ e * p ^ e))) :
    ∑ P ∈ S, deg P + 1 ≤ p ^ e * p ^ e + (2 * g + 1) * p ^ e := by
  set r := p ^ e with hrdef
  obtain ⟨t, ht⟩ : ∃ t, r = g + t := ⟨r - g, by omega⟩
  have ht' : g ^ 2 + 2 * g + 1 < t := by nlinarith
  have hm : r - 1 < r := by omega
  have hmn : r * (r - 1) + (r + 2 * g) + 1 < (r - 1 + 1 - g) * (r + 2 * g + 1 - g) := by
    rw [show r - 1 + 1 - g = t by omega, show r + 2 * g + 1 - g = t + 2 * g + 1 by omega, ht]
    have h1 : (g + t) * (g + t - 1) + (g + t) = (g + t) * (g + t) := by
      rcases Nat.eq_zero_or_pos (g + t) with h | h
      · rw [h]
      · rw [Nat.mul_sub_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ h)]
    nlinarith
  have h := mul_sum_deg_le p e hD hP₀ hP₁ hres g hRR σ (r + 2 * g) (hσ _) (r - 1) hm hmn S hS₀
    fun P hP y hy => hS P hP _ y hy
  have hr0 : 0 < r := by omega
  have h' : ∑ P ∈ S, deg P ≤ (r - 1) + r * (r + 2 * g) := by
    refine Nat.le_of_mul_le_mul_left ?_ hr0
    calc r * ∑ P ∈ S, deg P ≤ r * (r - 1) + r * r * (r + 2 * g) := h
      _ = r * ((r - 1) + r * (r + 2 * g)) := by ring
  have : (r - 1) + 1 = r := Nat.sub_add_cancel hr0
  nlinarith

/-- At a residue-rational place, `y ≡ y ^ q` for every integral `y`: the residue of `y` is a
constant `c`, and `c ^ q = c`. -/
theorem one_le_val_sub_pow_card [Fintype k] (p e : ℕ) [Fact p.Prime] [CharP K p]
    (hq : Fintype.card k = p ^ e * p ^ e) {w : AddValuation K (WithTop ℤ)}
    (hw : IsResidueRational (k := k) w) {y : K} (hy : 0 ≤ w y) :
    ((1 : ℤ) : WithTop ℤ) ≤ w (y - y ^ (p ^ e * p ^ e)) := by
  have hQ : p ^ e * p ^ e = p ^ (e + e) := by rw [← pow_add]
  have hQ0 : p ^ e * p ^ e ≠ 0 := by
    have := (Fact.out : p.Prime).ne_zero
    positivity
  -- a version for elements of positive order
  have hpos : ∀ t : K, ((1 : ℤ) : WithTop ℤ) ≤ w t →
      ((1 : ℤ) : WithTop ℤ) ≤ w (t - t ^ (p ^ e * p ^ e)) := by
    intro t ht
    refine AddValuation.map_le_sub _ ht ?_
    rw [AddValuation.map_pow]
    calc ((1 : ℤ) : WithTop ℤ) ≤ (((p ^ e * p ^ e : ℕ) : ℤ) : WithTop ℤ) := by
          exact_mod_cast Nat.one_le_iff_ne_zero.2 hQ0
      _ ≤ (p ^ e * p ^ e) • w t := natCast_le_nsmul_of_one_le _ ht
  rcases eq_or_ne y 0 with rfl | hy0
  · simp only [ne_eq, hQ0, not_false_eq_true, zero_pow, sub_self, AddValuation.map_zero]
    exact le_top
  rcases (le_iff_lt_or_eq.1 hy) with hlt | heq
  · refine hpos y ?_
    rw [← coe_ordZ hy0] at hlt ⊢
    exact_mod_cast (show (1 : ℤ) ≤ ordZ w y by exact_mod_cast hlt)
  · obtain ⟨c, hc⟩ := hw y 1 hy0 one_ne_zero (by rw [← heq, AddValuation.map_one])
    rw [mul_one, ← heq] at hc
    set t := y - algebraMap k K c with htdef
    have ht : ((1 : ℤ) : WithTop ℤ) ≤ w t := by
      rcases eq_or_ne t 0 with h0 | h0
      · rw [h0, AddValuation.map_zero]; exact le_top
      · rw [← coe_ordZ h0] at hc ⊢
        exact_mod_cast (show (1 : ℤ) ≤ ordZ w t by exact_mod_cast hc)
    have hyt : y = algebraMap k K c + t := by rw [htdef]; ring
    have hcq : (algebraMap k K c) ^ (p ^ e * p ^ e) = algebraMap k K c := by
      rw [← map_pow, ← hq, FiniteField.pow_card]
    have : y - y ^ (p ^ e * p ^ e) = t - t ^ (p ^ e * p ^ e) := by
      rw [hyt, hQ, add_pow_char_pow, ← hQ, hcq]
      ring
    rw [this]
    exact hpos t ht

/-- **The Bombieri–Stepanov bound for rational places.** Let `K` be a function field over a finite
field with `q = r²` elements, `r = p ^ e`. Let `P₀` be a residue-rational place of degree one with
`#L(o P₀) ≥ q ^ (o + 1 - g)` for every `o`. If `r > g² + 3g + 1`, then any finite set `S` of
residue-rational places of degree one has `#S ≤ q + (2g + 1) √q`. -/
theorem card_le_of_isResidueRational [Fintype k] (p e : ℕ) [Fact p.Prime] [CharP K p]
    (hq : Fintype.card k = p ^ e * p ^ e)
    {v : Pl → AddValuation K (WithTop ℤ)} {deg : Pl → ℕ} (hD : HasDegreeFormula v deg)
    {P₀ : Pl} (hP₀ : deg P₀ = 1) (hres : IsResidueRational (k := k) (v P₀))
    (g : ℕ) (hRR : ∀ o, Fintype.card k ^ (o + 1 - g) ≤ Nat.card (poleSpace v P₀ o))
    (hr : g ^ 2 + 3 * g + 1 < p ^ e) (S : Finset Pl) (hSdeg : ∀ P ∈ S, deg P = 1)
    (hSres : ∀ P ∈ S, IsResidueRational (k := k) (v P)) :
    S.card ≤ p ^ e * p ^ e + (2 * g + 1) * p ^ e := by
  classical
  have h := sum_deg_add_one_le p e hD hP₀ hP₀ hres g hRR hr id (fun n y hy => hy) (S.erase P₀)
    (Finset.notMem_erase P₀ S) fun P hP n y hy => by
      obtain ⟨hPP₀, hPS⟩ := Finset.mem_erase.1 hP
      exact one_le_val_sub_pow_card p e hq (hSres P hPS) (hy.2 P hPP₀)
  rw [Finset.sum_congr rfl fun P hP => hSdeg P (Finset.mem_of_mem_erase hP),
    Finset.sum_const, smul_eq_mul, mul_one] at h
  have := Finset.pred_card_le_card_erase (s := S) (a := P₀)
  omega

end Stacks.BombieriStepanov

end
