module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Separable
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.KrullDimension.Field
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.CompleteLocalRing.Noetherian
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-
# Problem Description

Krasner's lemma (Stacks project Tag 09EI).

Let $A$ be a commutative ring that is a complete local Noetherian domain of
(Krull) dimension $1$, with unique maximal ideal $\mathfrak{m} = \mathfrak{m}_A$.

Let $P(t) \in A[t]$ be a polynomial and let $\alpha \in A$ be a root of $P$ that is
not a root of the formal derivative $P'$, i.e.
$$P(\alpha) = 0 \qquad\text{and}\qquad P'(\alpha) \neq 0.$$

Then for every integer $c \geq 0$ there exists an integer $n \geq 0$ such that
for every polynomial $Q \in A[t]$ all of whose coefficients lie in
$\mathfrak{m}^n$, the polynomial $P + Q$ has a root $\beta \in A$ with
$\beta - \alpha \in \mathfrak{m}^c$.
-/

/-
## Background and context

We use the following standard notions.

1. Domain: `A` is an integral domain (`IsDomain A`): commutative with `1 ≠ 0`
   and no nonzero zero divisors.

2. Local ring of dimension `1`: `A` is local (`IsLocalRing A`) with maximal ideal
   `m = IsLocalRing.maximalIdeal A`, and its Krull dimension `ringKrullDim A`
   equals `1` (as an element of `WithBot ℕ∞`).

3. Completeness: `A` is complete with respect to its `m`-adic topology, encoded as
   `IsAdicComplete (IsLocalRing.maximalIdeal A) A`. (In Mathlib `IsAdicComplete I A`
   bundles both separatedness and completeness of the `I`-adic filtration.)

4. Powers of the maximal ideal: for `k : ℕ`, `m ^ k` is the `k`-th power of the
   ideal `m`, with `m ^ 0 = ⊤ = A`.

5. Polynomials and evaluation: `A[X]` is the polynomial ring in one variable
   (`Polynomial A`). For `P : A[X]` and `α : A`, `P.eval α` is the evaluation,
   the image of `P` under the `A`-algebra homomorphism `A[X] → A` sending
   `X ↦ α`.

6. Formal derivative: `Polynomial.derivative P` is the formal derivative
   `P' = ∑_{i ≥ 1} i a_i t^{i-1}`.

7. Coefficients of a polynomial lying in an ideal: for an ideal `I ⊆ A` and
   `Q : A[X]`, "the coefficients of `Q` are in `I`" means `∀ i, Q.coeff i ∈ I`.

8. Root: `α` is a root of `P` iff `P.eval α = 0`; it is a root of `P'` iff
   `(derivative P).eval α = 0`.

Note on Noetherianity: the Stacks project uses these hypotheses in contexts where
Noetherianity is implicit; we make it explicit via `IsNoetherianRing A` since the
proof relies on it (e.g. `m = √(π)` for any nonzero `π ∈ m`, used in the
Newton-type approximation argument).
-/

open Polynomial IsLocalRing

/-!
## Proof sketch / decomposition (Stacks Tag 09EI)

The informal proof (see the problem description above) is a Newton/Hensel-type
approximation. We decompose it into the named helper lemmas below, each carrying
a one-paragraph rigorous argument as a comment, and then assemble `krasner_lemma`
from them. The substantive analytic kernel is
`IsLocalRing.exists_root_sub_mem_span_singleton_pow` (the contracting Newton
iteration plus the completeness limit); the remaining helpers are
commutative-algebra facts about the dimension-`1` hypothesis.

Throughout, fix a nonzero `π ∈ m`. Since `dim A = 1` and `A` is a domain, the
only primes are `(0)` and `m`; as `π ≠ 0`, the only prime containing `(π)` is
`m`, so `√(π) = m`. This is the engine for: (a) inverting `P'(α)` up to a power
of `π`, and (b) trapping `m ^ n` inside `(π ^ k)`.
-/

variable {A : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]

namespace IsLocalRing

/-- In a local domain of Krull dimension at most `1`, every nonzero prime ideal is the
maximal ideal. -/
theorem eq_maximalIdeal_of_ne_bot (hdim : ringKrullDim A ≤ 1) {p : Ideal A} (hp : p.IsPrime)
    (hne : p ≠ ⊥) : p = maximalIdeal A :=
  have : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr (by exact_mod_cast hdim)
  eq_maximalIdeal (hp.isMaximal_of_ne_bot hne)

/- Argument for `radical_eq_maximalIdeal`: `A` is a `1`-dimensional local domain, so its only
prime ideals are the zero ideal `(0)` and the maximal ideal `m` (the chain `(0) ⊊ m` realizes
dimension `1`, and there are no others). The radical `√I` is the intersection of all primes
containing `I`. Since `I ≠ 0` and `A` is a domain, `(0)` does not contain `I`, so the only
prime containing `I` is `m` (which does, as `I ≤ m`). Hence `√I = m`. -/
/-- **(L1)** In a local domain of Krull dimension at most `1`, the radical of a nonzero ideal
contained in the maximal ideal is the maximal ideal. -/
theorem radical_eq_maximalIdeal (hdim : ringKrullDim A ≤ 1) {I : Ideal A} (hI : I ≠ ⊥)
    (hle : I ≤ maximalIdeal A) : I.radical = maximalIdeal A := by
  rw [Ideal.radical_eq_sInf]
  refine le_antisymm (sInf_le ⟨hle, inferInstance⟩) (le_sInf ?_)
  rintro J ⟨hJle, hJprime⟩
  exact (eq_maximalIdeal_of_ne_bot hdim hJprime fun h => hI (le_bot_iff.mp (hJle.trans h.le))).ge

/-- In a local domain of Krull dimension `1`, the maximal ideal is nonzero. -/
private theorem maximalIdeal_ne_bot_of_ringKrullDim_eq_one
    {R : Type*} [CommRing R] [IsLocalRing R] (hdim : ringKrullDim R = 1) :
    maximalIdeal R ≠ ⊥ := fun h => one_ne_zero <| hdim.symm.trans <|
  ringKrullDim_eq_zero_of_isField (isField_iff_maximalIdeal_eq.mpr h)

/- Argument for `exists_maximalIdeal_pow_le_span_singleton_pow`: for `j ≥ 1` the ideal
`(π ^ j)` is nonzero and contained in `m`, so `√(π ^ j) = m` by (L1). Since `A` is Noetherian,
`m` is finitely generated, and `Ideal.exists_pow_le_of_le_radical_of_fg` gives `n` with
`m ^ n ≤ (π ^ j)`. For `j = 0` we have `(π ^ 0) = ⊤`, so the radical bound is trivial. -/
/-- **(L2)** A power of the maximal ideal lands inside the ideal generated by `π ^ j`, for any
nonzero `π` in the maximal ideal. -/
theorem exists_maximalIdeal_pow_le_span_singleton_pow [IsNoetherianRing A]
    (hdim : ringKrullDim A ≤ 1) {π : A} (hπ : π ≠ 0) (hmem : π ∈ maximalIdeal A) (j : ℕ) :
    ∃ n : ℕ, maximalIdeal A ^ n ≤ Ideal.span {π ^ j} := by
  refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (IsNoetherian.noetherian _)
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [Ideal.radical_top]
  · exact (radical_eq_maximalIdeal hdim
      (by simpa [Ideal.span_singleton_eq_bot] using pow_ne_zero j hπ)
      ((maximalIdeal A).span_singleton_le_iff_mem.mpr
        ((maximalIdeal A).pow_mem_of_mem hmem j hj))).ge

/- Argument for `exists_dvd_pow_of_ne_zero`: the radical `√(d)` is the intersection of the
primes containing `d`. Since `d ≠ 0`, the zero ideal does not contain `d`; so either `d` is a
unit (then `√(d) = ⊤ ∋ π`) or the only prime containing `d` is `m`, giving `√(d) = m ∋ π`.
Either way `π ∈ √(d)`, so `Ideal.mem_radical_iff` gives `mm` with `π ^ mm ∈ (d)`. -/
/-- **(L3)** In a local domain of Krull dimension at most `1`, every nonzero element divides a
power of any given element of the maximal ideal. -/
theorem exists_dvd_pow_of_ne_zero (hdim : ringKrullDim A ≤ 1) {π : A}
    (hmem : π ∈ maximalIdeal A) {d : A} (hd : d ≠ 0) : ∃ mm : ℕ, d ∣ π ^ mm := by
  have hπrad : π ∈ (Ideal.span {d}).radical := by
    rw [Ideal.radical_eq_sInf]
    refine Submodule.mem_sInf.mpr ?_
    rintro J ⟨hJle, hJprime⟩
    exact (eq_maximalIdeal_of_ne_bot hdim hJprime fun h =>
      hd (Ideal.mem_bot.mp (h ▸ hJle (Ideal.mem_span_singleton_self d)))).ge hmem
  exact (Ideal.mem_radical_iff.mp hπrad).imp fun _ => Ideal.mem_span_singleton.mp

/- Argument for `exists_root_sub_mem_span_singleton_pow` (Newton iteration): define `α₀ = α`
and, using the binomial/Taylor expansion `F(x+y) = F(x) + F'(x) y + R(x,y) y²`
(`Polynomial.binomExpansion`), take the Newton step `α_{k+1} = α_k - a * (F(α_k) / π^mm)`.
CAUTION: the naive step `α_{k+1} = α_k - a * F(α_k)` does NOT contract when `mm ≥ 1` (then
`1 - a*F'(α_k)` is a unit, so the residual gains no `π`); the correct step divides out `π^mm`
first. This is well-defined *inside* `A`: by invariant (iii) `F(α_k) ∈ (π ^ mm)` (indeed
`∈ (π ^ (2*mm + L + k)) ⊆ (π ^ mm)`), so `F(α_k) = π^mm * g_k` for some `g_k ∈ A`; set
`α_{k+1} = α_k - a * g_k`. Then `a * (derivative F).eval α_k` is `≡ a*δ = π^mm (mod higher)`,
so `a*g_k` is the genuine Newton correction. One proves by induction the invariants
  (i) `α_k - α ∈ (π ^ (mm + L))`  (hence `∈ (π ^ L)`),
  (ii) `α_{k+1} - α_k ∈ (π ^ (mm + L + k))`,
  (iii) `F(α_k) ∈ (π ^ (2*mm + L + k))`.
The quadratic remainder term (`R · (α_{k+1}-α_k)²`) plus the `a * δ = π^mm` relation make the
residual `F(α_{k+1})` gain one extra power of `π` each step (the standard Hensel doubling, here
tracked linearly which suffices). By (ii) the sequence is `π`-adically — a fortiori
`m`-adically (`π ∈ m`) — Cauchy, so `IsPrecomplete.prec` (from `IsAdicComplete`) yields a limit
`β` with `β ≡ α_k [SMOD m^•]` (use `I^n • ⊤ = I^n`). By (iii) and `m`-adic separatedness
(`IsHausdorff.haus`), `F(β) ∈ ⋂_k (π^•) = 0`. By (i) `β - α ∈ (π ^ L)`.

The hypothesis `1 ≤ L` is essential: with `L = 0` and `mm = 0` the closeness hypothesis would
collapse to a vacuous `∈ span{π^0} = ⊤` and the conclusion would be false (e.g. `X²+X+1` over
`ℤ₃` has no root). -/
/-- **(L4) Newton/Hensel kernel.** Let `A` be `m`-adically complete and `π` a nonzero element
of `m`. Given `a * δ = π ^ mm`, with `F'(α) ≡ δ` modulo `(π ^ (mm + 1))` and
`F(α) ∈ (π ^ (2 * mm + L))` for `L ≥ 1`, the polynomial `F` has a root `β` with
`β - α ∈ (π ^ L)`. -/
theorem exists_root_sub_mem_span_singleton_pow [IsAdicComplete (maximalIdeal A) A] {π : A}
    (hπ : π ≠ 0) (hmem : π ∈ maximalIdeal A) (F : A[X]) (α : A) (δ a : A) (mm L : ℕ)
    (hL : 1 ≤ L) (hinv : a * δ = π ^ mm)
    (hderiv_close : (derivative F).eval α - δ ∈ Ideal.span {π ^ (mm + 1)})
    (hclose : F.eval α ∈ Ideal.span {π ^ (2 * mm + L)}) :
    ∃ β : A, F.eval β = 0 ∧ β - α ∈ Ideal.span {π ^ L} := by
  have hsmul : ∀ n : ℕ,
      maximalIdeal A ^ n • (⊤ : Submodule A A) = (maximalIdeal A ^ n : Ideal A) :=
    fun n => by rw [smul_eq_mul, Ideal.mul_top]
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  rw [Ideal.mem_span_singleton] at hderiv_close hclose
  let Inv : ℕ → A → Prop := fun k x =>
    π ^ (mm + (L' + 1)) ∣ (x - α) ∧ π ^ (2 * mm + (L' + 1) + k) ∣ F.eval x
  have step : ∀ (k : ℕ) (x : A), Inv k x →
      ∃ x' : A, Inv (k + 1) x' ∧ π ^ (mm + (L' + 1) + k) ∣ (x' - x) := by
    rintro k x ⟨hxα, hFx⟩
    obtain ⟨w, hw⟩ := hFx
    set g : A := π ^ (mm + (L' + 1) + k) * w with hg_def
    have hFxg : F.eval x = π ^ mm * g := by
      rw [hw, hg_def]
      ring
    have hg_dvd : π ^ (mm + (L' + 1) + k) ∣ g := ⟨w, rfl⟩
    refine ⟨x - a * g, ⟨?_, ?_⟩, ?_⟩
    · rw [show x - a * g - α = (x - α) - a * g by ring]
      exact dvd_sub hxα ((pow_dvd_pow π (by omega)).trans (hg_dvd.mul_left a))
    · change π ^ (2 * mm + (L' + 1) + k + 1) ∣ F.eval (x - a * g)
      obtain ⟨R, hR⟩ := binomExpansion F x (-(a * g))
      rw [show x - a * g = x + (-(a * g)) by ring, hR]
      have hFp : π ^ (mm + 1) ∣ ((derivative F).eval x - δ) := by
        have h2 : π ^ (mm + 1) ∣ ((derivative F).eval x - (derivative F).eval α) :=
          (pow_dvd_pow π (by omega : mm + 1 ≤ mm + (L' + 1))).trans
            (hxα.trans (sub_dvd_eval_sub x α (derivative F)))
        simpa only [sub_add_sub_cancel] using dvd_add h2 hderiv_close
      obtain ⟨e, he⟩ := hFp
      have hFp_eq : (derivative F).eval x = δ + π ^ (mm + 1) * e := by linear_combination he
      have key : F.eval x + (derivative F).eval x * (-(a * g)) + R * (-(a * g)) ^ 2
          = π ^ (2 * mm + (L' + 1) + k + 1) *
            (-(a * e * w) + R * a ^ 2 * (π ^ (L' + k) * w ^ 2)) := by
        rw [hFxg, hFp_eq, hg_def]
        linear_combination (-(π ^ (mm + (L' + 1) + k) * w)) * hinv
      rw [key]
      exact Dvd.intro _ rfl
    · rw [show x - a * g - x = -(a * g) by ring]
      exact (hg_dvd.mul_left a).neg_right
  -- the Newton iterates, each packaged with the invariant it satisfies
  let S : (k : ℕ) → {x : A // Inv k x} := fun k => Nat.rec
    (⟨α, by simp, by simpa using dvd_trans (pow_dvd_pow π (by omega)) hclose⟩ :
      {x : A // Inv 0 x})
    (fun k p => ⟨_, (step k p.val p.property).choose_spec.left⟩) k
  set f : ℕ → A := fun k => (S k).val
  have hfα : ∀ k, π ^ (mm + (L' + 1)) ∣ (f k - α) := fun k => (S k).property.left
  have hfF : ∀ k, π ^ (2 * mm + (L' + 1) + k) ∣ F.eval (f k) := fun k => (S k).property.right
  have hfstep : ∀ k, π ^ (mm + (L' + 1) + k) ∣ (f (k + 1) - f k) :=
    fun k => (step k (S k).val (S k).property).choose_spec.right
  let hseq : ℕ → A := fun k => (hfα k).choose
  have hh : ∀ k, f k - α = π ^ (mm + (L' + 1)) * hseq k := fun k => (hfα k).choose_spec
  have hhstep : ∀ k, π ^ k ∣ (hseq (k + 1) - hseq k) := fun k => by
    obtain ⟨c, hc⟩ := hfstep k
    exact ⟨c, mul_left_cancel₀ (pow_ne_zero (mm + (L' + 1)) hπ)
      (by linear_combination hc - hh (k + 1) + hh k)⟩
  have htel : ∀ m n, m ≤ n → π ^ m ∣ (hseq n - hseq m) := by
    intro m n hmn
    induction n with
    | zero => simp_all
    | succ n ih =>
      rcases hmn.lt_or_eq with hlt | rfl
      · rw [← sub_add_sub_cancel _ (hseq n)]
        exact dvd_add ((pow_dvd_pow π (by omega)).trans (hhstep n)) (ih (by omega))
      · simp
  have hcauchy : ∀ {m n : ℕ}, m ≤ n →
      hseq m ≡ hseq n [SMOD maximalIdeal A ^ m • (⊤ : Submodule A A)] := by
    intro m n hmn
    rw [SModEq.sub_mem, hsmul m]
    obtain ⟨c, hc⟩ := htel m n hmn
    rw [show hseq m - hseq n = -(hseq n - hseq m) by ring, hc]
    exact neg_mem (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hmem m))
  obtain ⟨hlim, hhlim⟩ := IsPrecomplete.prec' hseq (fun {m n} hmn => hcauchy hmn)
  refine ⟨α + π ^ (mm + (L' + 1)) * hlim, ?_, ?_⟩
  · set β : A := α + π ^ (mm + (L' + 1)) * hlim with hβ_def
    have hβfn : ∀ n, (β - f n) ∈ maximalIdeal A ^ n := by
      intro n
      have hneg : (hlim - hseq n) ∈ maximalIdeal A ^ n := by
        have hlimn := hhlim n
        rw [SModEq.sub_mem, hsmul n] at hlimn
        simpa only [neg_sub] using neg_mem hlimn
      have e : β - f n = π ^ (mm + (L' + 1)) * (hlim - hseq n) := by
        rw [hβ_def]
        linear_combination -(hh n)
      rw [e]
      exact Ideal.mul_mem_left _ _ hneg
    have hFβ : ∀ n, F.eval β ∈ maximalIdeal A ^ n := fun n => by
      obtain ⟨c, hc⟩ := sub_dvd_eval_sub β (f n) F
      obtain ⟨c', hc'⟩ := hfF n
      rw [← sub_add_cancel (F.eval β) (F.eval (f n)), hc, hc', pow_add]
      exact add_mem (Ideal.mul_mem_right _ _ (hβfn n))
        (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hmem n)))
    exact IsHausdorff.haus' (R := A) (I := maximalIdeal A) (F.eval β)
      (fun n => by simpa only [SModEq.zero, hsmul n] using hFβ n)
  · rw [add_sub_cancel_left, Ideal.mem_span_singleton]
    exact dvd_trans (pow_dvd_pow π (by omega : L' + 1 ≤ mm + (L' + 1))) (dvd_mul_right _ hlim)

end IsLocalRing

/-- **Krasner's lemma (Stacks Tag 09EI).** Let `A` be a complete local Noetherian
domain of Krull dimension `1` with maximal ideal `m`. If `α` is a root of `P` that
is not a root of `P'`, then for every `c` there is an `n` such that any polynomial
`Q` whose coefficients all lie in `m ^ n` makes `P + Q` have a root `β` with
`β - α ∈ m ^ c`. -/
@[stacks 09EI]
theorem krasner_lemma
    (A : Type*) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 1)
    [IsAdicComplete (maximalIdeal A) A]
    (P : A[X]) (α : A)
    (hroot : P.eval α = 0)
    (hderiv : (derivative P).eval α ≠ 0) :
    ∀ c : ℕ, ∃ n : ℕ, ∀ Q : A[X], (∀ i, Q.coeff i ∈ (maximalIdeal A) ^ n) →
      ∃ β : A, (P + Q).eval β = 0 ∧ β - α ∈ (maximalIdeal A) ^ c := by
  intro c
  -- STEP 1: choose a nonzero `π ∈ m`.  In a dim-1 local domain `m ≠ ⊥`
  -- (otherwise `A` would be a field, dimension 0), so such `π` exists.
  obtain ⟨π, hπmem, hπne⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (maximalIdeal_ne_bot_of_ringKrullDim_eq_one hdim)
  -- STEP 2: invert `P'(α)` up to a power of `π` (L3).
  set d : A := (derivative P).eval α with hd_def
  obtain ⟨mm, a, ha⟩ := exists_dvd_pow_of_ne_zero hdim.le hπmem hderiv
  have hinv : a * d = π ^ mm := by linear_combination -ha
  -- STEP 3: choose the target depth `L` so that `(π ^ L) ⊆ m ^ c`.  We take
  -- `L = c + 1` (NOT `L = c`): the Newton kernel requires `L ≥ 1`, and `c = 0` is
  -- allowed here, so `L = c` would be illegal at `c = 0`.
  -- This is fine because `(π ^ (c+1)) ⊆ m ^ (c+1) ⊆ m ^ c`.
  -- STEP 4: choose `n` with `m ^ n ⊆ (π ^ (2*mm + (c+1)))` (L2 with `j = 2*mm + c + 1`).
  obtain ⟨n, hn⟩ :=
    exists_maximalIdeal_pow_le_span_singleton_pow hdim.le hπne hπmem (2 * mm + (c + 1))
  refine ⟨n, fun Q hQ => ?_⟩
  have eval_mem : ∀ (R : A[X]) (I : Ideal A), (∀ i, R.coeff i ∈ I) → R.eval α ∈ I := by
    intro R I hcoeff
    rw [Polynomial.eval_eq_sum_range]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hcoeff i)
  -- STEP 5: verify the hypotheses of the Newton kernel for `F = P + Q`,
  -- denominator `δ = P'(α) = d`, approximate inverse `a`, depth `L = c + 1`.
  --   • `hinv : a * d = π ^ mm`  — from STEP 2.
  --   • derivative agreement: `(P+Q)'(α) - d = Q'(α) ∈ m^n ⊆ (π^(2mm+c+1)) ⊆ (π^(mm+1))`
  --     (coeffs of `Q'` are `ℕ`-multiples of coeffs of `Q`, still in `m^n`).
  --   • closeness: `(P+Q)(α) = P(α) + Q(α) = 0 + Q(α) = Q(α) ∈ m^n ⊆ (π^(2mm+c+1))`,
  --     because each `Q.coeff i ∈ m^n` and `Q(α) = ∑ Q.coeff i * α^i` lies in that ideal.
  have hderiv_close : (derivative (P + Q)).eval α - d ∈ Ideal.span {π ^ (mm + 1)} := by
    have hdQ : (derivative Q).eval α ∈ maximalIdeal A ^ n := by
      refine eval_mem _ _ fun i => ?_
      rw [Polynomial.coeff_derivative]
      exact Ideal.mul_mem_right _ _ (hQ (i + 1))
    rw [hd_def, derivative_add, eval_add, add_sub_cancel_left]
    exact hn.trans (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (by omega))) hdQ
  have hclose : (P + Q).eval α ∈ Ideal.span {π ^ (2 * mm + (c + 1))} := by
    rw [eval_add, hroot, zero_add]
    exact hn (eval_mem Q _ hQ)
  obtain ⟨β, hβroot, hβclose⟩ :=
    exists_root_sub_mem_span_singleton_pow hπne hπmem (P + Q) α d a mm (c + 1)
      (Nat.le_add_left 1 c) hinv hderiv_close hclose
  -- STEP 6: transfer `β - α ∈ (π ^ (c+1))` to `β - α ∈ m ^ c` using `π ∈ m`.
  exact ⟨β, hβroot, (Ideal.span_singleton_le_iff_mem _).mpr
    (Ideal.pow_le_pow_right (by omega) (Ideal.pow_mem_pow hπmem (c + 1))) hβclose⟩

/-!
## Descent of finite separable extensions along completion

The remaining declarations use Krasner's lemma to descend a finite separable extension of the
fraction field of the completion of a Noetherian local ring back to the fraction field of the
ring itself.
-/

namespace Krasner

open IntermediateField Polynomial

/-- Scaling an element by a nonzero element of the base domain does not change the field it
generates over the fraction field. -/
private theorem adjoin_simple_smul_eq_adjoin_simple
    {R F E : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [Field E] [Algebra F E] [Algebra R E]
    [IsScalarTower R F E] {r : R} (hr : r ≠ 0) (α : E) : F⟮r • α⟯ = F⟮α⟯ := by
  have hrF : algebraMap R F r ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R F).ne hr
  have hsc : (algebraMap R F r) • α = r • α := IsScalarTower.algebraMap_smul F r α
  apply le_antisymm
  · rw [adjoin_simple_le_iff, ← hsc]
    exact (F⟮α⟯).smul_mem (mem_adjoin_simple_self F α)
  · rw [adjoin_simple_le_iff]
    have hh : (algebraMap R F r)⁻¹ • (r • α) ∈ F⟮r • α⟯ :=
      (F⟮r • α⟯).smul_mem (mem_adjoin_simple_self F (r • α))
    have he : (algebraMap R F r)⁻¹ • (r • α) = α := by
      rw [← hsc, smul_smul, inv_mul_cancel₀ hrF, one_smul]
    rwa [he] at hh

/-- A finite separable extension of the fraction field of a domain has an integral primitive
element over the domain. -/
private theorem exists_integral_primitive_element
    {R F E : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [Algebra.IsSeparable F E] :
    let : Algebra R E := ((algebraMap F E).comp (algebraMap R F)).toAlgebra
    ∃ θ : E, IsIntegral R θ ∧ F⟮θ⟯ = ⊤ := by
  let : Algebra R E := ((algebraMap F E).comp (algebraMap R F)).toAlgebra
  have : IsScalarTower R F E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F E
  have ha : IsAlgebraic R α :=
    (IsFractionRing.isAlgebraic_iff R F E).mpr (Algebra.IsAlgebraic.isAlgebraic α)
  obtain ⟨r, hr, hir⟩ := ha.exists_integral_multiple
  exact ⟨r • α, hir, (adjoin_simple_smul_eq_adjoin_simple hr α).trans hα⟩

/-- Clearing denominators in an algebra generated over a fraction field. -/
private theorem exists_ne_zero_mul_mem_adjoin
    (R : Type*) [CommRing R] [IsDomain R] (F : Type*) [Field F] [Algebra R F]
    [IsFractionRing R F] {E : Type*} [CommRing E] [Algebra F E] [Algebra R E]
    [IsScalarTower R F E] (t : Set E) {u : E} (hu : u ∈ Algebra.adjoin F t) :
    ∃ d : R, d ≠ 0 ∧ algebraMap R E d * u ∈ Algebra.adjoin R t := by
  induction hu using Algebra.adjoin_induction with
  | mem w hw => exact ⟨1, one_ne_zero, by simpa using Algebra.subset_adjoin hw⟩
  | algebraMap c =>
      obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors R) c
      refine ⟨(b : R), nonZeroDivisors.coe_ne_zero b, ?_⟩
      have e : algebraMap R E (b : R) * algebraMap F E c = algebraMap R E a := by
        rw [IsScalarTower.algebraMap_apply R F E (b : R),
          IsScalarTower.algebraMap_apply R F E a, ← map_mul, mul_comm, hab]
      rw [e]
      exact Subalgebra.algebraMap_mem _ a
  | add u v _ _ ihu ihv =>
      obtain ⟨d, hd, hu⟩ := ihu
      obtain ⟨e, he, hv⟩ := ihv
      refine ⟨d * e, mul_ne_zero hd he, ?_⟩
      have h : algebraMap R E (d * e) * (u + v) =
          algebraMap R E e * (algebraMap R E d * u) +
            algebraMap R E d * (algebraMap R E e * v) := by
        rw [map_mul]
        ring
      rw [h]
      exact add_mem (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hu)
        (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hv)
  | mul u v _ _ ihu ihv =>
      obtain ⟨d, hd, hu⟩ := ihu
      obtain ⟨e, he, hv⟩ := ihv
      refine ⟨d * e, mul_ne_zero hd he, ?_⟩
      have h : algebraMap R E (d * e) * (u * v) =
          (algebraMap R E d * u) * (algebraMap R E e * v) := by
        rw [map_mul]
        ring
      rw [h]
      exact Subalgebra.mul_mem _ hu hv

/-- If a field is generated over a fraction field by a set, then it is the fraction field of
the algebra generated by that set over the original domain. -/
private theorem isFractionRing_adjoin
    (R : Type*) [CommRing R] [IsDomain R] (F : Type*) [Field F] [Algebra R F]
    [IsFractionRing R F] {E : Type*} [Field E] [Algebra F E] [Algebra R E]
    [IsScalarTower R F E] {t : Set E} (ht : IntermediateField.adjoin F t = ⊤) :
    IsFractionRing (Algebra.adjoin R t) E := by
  have : FaithfulSMul R E := .trans R F E
  refine IsFractionRing.of_field _ _ fun z => ?_
  obtain ⟨r, hr, s, hs, hz⟩ := IntermediateField.mem_adjoin_iff_div.mp
    (ht ▸ IntermediateField.mem_top (F := F) (x := z))
  obtain ⟨d₁, hd₁, hm₁⟩ := exists_ne_zero_mul_mem_adjoin R F t hr
  obtain ⟨d₂, hd₂, hm₂⟩ := exists_ne_zero_mul_mem_adjoin R F t hs
  have hd : algebraMap R E (d₁ * d₂) ≠ 0 := by
    simpa using (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R E)).2
      (mul_ne_zero hd₁ hd₂)
  refine ⟨⟨algebraMap R E (d₁ * d₂) * r, ?_⟩,
    ⟨algebraMap R E (d₁ * d₂) * s, ?_⟩, ?_⟩
  · rw [map_mul, mul_comm (algebraMap R E d₁), mul_assoc]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hm₁
  · rw [map_mul, mul_assoc]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hm₂
  · rw [hz]
    exact (mul_div_mul_left _ _ hd).symm

/-- An integral primitive element generates a finite order whose fraction field is the
given finite separable extension. -/
private theorem exists_finite_integral_primitive_order
    {R F E : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [Algebra.IsSeparable F E] :
    let : Algebra R E := ((algebraMap F E).comp (algebraMap R F)).toAlgebra
    ∃ θ : E, IsIntegral R θ ∧ F⟮θ⟯ = ⊤ ∧
      Module.Finite R (Algebra.adjoin R {θ}) ∧
        IsFractionRing (Algebra.adjoin R {θ}) E := by
  let : Algebra R E := ((algebraMap F E).comp (algebraMap R F)).toAlgebra
  have : IsScalarTower R F E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨θ, hθ, hgen⟩ := exists_integral_primitive_element (R := R) (F := F) (E := E)
  exact ⟨θ, hθ, hgen, Algebra.finite_adjoin_simple_of_isIntegral hθ,
    isFractionRing_adjoin R F hgen⟩

/-- Every element of a Noetherian local ring's completion can be approximated, to any
maximal-ideal-adic precision, by an element of the original ring. -/
private theorem exists_approx_adicCompletion
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (x : AdicCompletion (IsLocalRing.maximalIdeal A) A) (n : ℕ) :
    ∃ a : A, x - algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) a ∈
      (IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ^ n := by
  let I := IsLocalRing.maximalIdeal A
  obtain ⟨a, ha⟩ :=
    Submodule.Quotient.mk_surjective (I ^ n • (⊤ : Submodule A A)) (x.val n)
  refine ⟨a, ?_⟩
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow,
    ← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval I.fg_of_isNoetherianRing]
  change x.val n - (AdicCompletion.of I A a).val n = 0
  rw [AdicCompletion.of_apply]
  exact sub_eq_zero.mpr ha.symm

/-- A monic polynomial over a local adic completion can be approximated, coefficient by
coefficient, by a monic polynomial of the same degree over the original ring. -/
private theorem exists_monic_approx_adicCompletion
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (P : Polynomial (AdicCompletion (IsLocalRing.maximalIdeal A) A))
    (hP : P.Monic) (n : ℕ) :
    ∃ Q : Polynomial A, Q.Monic ∧ Q.natDegree = P.natDegree ∧
      ∀ i : ℕ, (P - Q.map (algebraMap A
        (AdicCompletion (IsLocalRing.maximalIdeal A) A))).coeff i ∈
          (IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ^ n := by
  classical
  let d := P.natDegree
  choose a ha using fun i : Fin d => exists_approx_adicCompletion (P.coeff i) n
  let Q : Polynomial A := Polynomial.X ^ d +
    ∑ i : Fin d, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)
  have hQ : Q.Monic := Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt a)
  have hdeg : Q.natDegree = d := by
    unfold Q
    rw [Polynomial.natDegree_add_eq_left_of_degree_lt]
    · simp
    · simpa using (Polynomial.degree_sum_fin_lt a)
  refine ⟨Q, hQ, hdeg, fun i => ?_⟩
  simp only [Polynomial.coeff_sub]
  rcases lt_trichotomy i d with hi | rfl | hi
  · have hcoeff : Q.coeff i = a ⟨i, hi⟩ := by
      simp only [Q, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff,
        Polynomial.coeff_C_mul_X_pow]
      rw [Finset.sum_eq_single ⟨i, hi⟩]
      · simp [Nat.ne_of_lt hi]
      · intro j _ hj
        have hij : i ≠ (j : ℕ) := fun h => hj (Fin.ext h.symm)
        simp [hij]
      · simp
    rw [Polynomial.coeff_map, hcoeff]
    simpa using ha ⟨i, hi⟩
  · have hpcoeff : P.coeff d = 1 := by simpa [d] using hP.coeff_natDegree
    have hqcoeff : Q.coeff d = 1 := by
      rw [← hdeg]
      exact hQ.coeff_natDegree
    simp [hpcoeff, hqcoeff]
  · have hpcoeff : P.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hi
    have hqcoeff : Q.coeff i = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rwa [hdeg]
    simp [hpcoeff, hqcoeff]

/-- A finite domain over a complete Noetherian local ring is complete and local. -/
private theorem isNoetherianCompleteLocalRing_of_finite_of_isDomain
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
    [Algebra R S] [Module.Finite R S] (hR : IsNoetherianCompleteLocalRing R) :
    IsNoetherianCompleteLocalRing S := by
  classical
  obtain ⟨m, T, hT, hlocal, ⟨e⟩⟩ := finite_isProduct_isNoetherianCompleteLocalRing hR
    (S := S)
  let : ∀ i, CommRing (T i) := hT
  let : ∀ i, IsLocalRing (T i) := fun i => (hlocal i).isLocal
  have hne : Nonempty (Fin m) := by
    by_contra h
    have : IsEmpty (Fin m) := not_nonempty_iff.mp h
    exact one_ne_zero (e.injective (by ext i; exact isEmptyElim i))
  have : Subsingleton (Fin m) := ⟨by
    intro i j
    by_contra hij
    have hz : (Pi.single i 1 : ∀ k, T k) * Pi.single j 1 = 0 := by
      ext k
      by_cases hik : i = k
      · subst k
        simp [Ne.symm hij]
      · simp [hik]
    have hm : e.symm (Pi.single i 1) * e.symm (Pi.single j 1) = 0 := by
      rw [← map_mul, hz, map_zero]
    rcases mul_eq_zero.mp hm with hi | hj
    · simpa using congrArg (fun x => e x i) hi
    · simpa using congrArg (fun x => e x j) hj⟩
  let : Unique (Fin m) := uniqueOfSubsingleton (Classical.choice hne)
  let f := e.trans (RingEquiv.piUnique T)
  have : IsLocalRing S := f.symm.isLocalRing
  have : IsNoetherianRing R := hR.isNoetherian
  refine ⟨IsNoetherianRing.of_finite R S, inferInstance, ?_⟩
  apply (IsAdicComplete.congr_ringEquiv (IsLocalRing.maximalIdeal S) f).mp
  rw [show Ideal.map f (IsLocalRing.maximalIdeal S) = IsLocalRing.maximalIdeal (T default) from
    IsLocalRing.map_maximalIdeal_of_surjective f.toRingHom f.surjective]
  exact (hlocal default).isComplete

/-- An integral extension of domains of dimension one again has dimension one. -/
@[ega "0 16.1.5" "special case"]
private theorem ringKrullDim_eq_one_of_isIntegral
    {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] [Algebra.IsIntegral R S] [FaithfulSMul R S]
    (hR : ringKrullDim R = 1) : ringKrullDim S = 1 := by
  have hdimR : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hR.le
  have : Ring.DimensionLEOne R := ⟨fun {p} hp hp' => hp'.isMaximal_of_ne_bot hp⟩
  have : Ring.DimensionLEOne S := Ring.DimensionLEOne.of_isIntegral R S
  have hdimS : Ring.KrullDimLE 1 S :=
    Ring.krullDimLE_one_iff_of_noZeroDivisors.mpr fun p hp hp' => hp'.isMaximal hp
  have hn : ¬ ringKrullDim S ≤ 0 := by
    intro h
    have : Ring.KrullDimLE 0 S := Ring.krullDimLE_iff.mpr h
    have hf := isField_of_isIntegral_of_isField (FaithfulSMul.algebraMap_injective R S)
      (Ring.KrullDimLE.isField_of_isDomain (R := S))
    exact one_ne_zero (hR.symm.trans (ringKrullDim_eq_zero_of_isField hf))
  exact le_antisymm (Ring.krullDimLE_iff.mp hdimS) (Order.succ_le_of_lt (lt_of_not_ge hn))

/-- A finite separable extension of the fraction field of a complete Noetherian local
one-dimensional domain has a finite integral primitive order with the same properties. -/
private theorem exists_complete_integral_primitive_order
    {R F E : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [Algebra.IsSeparable F E] (hR : IsNoetherianCompleteLocalRing R)
    (hdim : ringKrullDim R = 1) :
    let : Algebra R E := ((algebraMap F E).comp (algebraMap R F)).toAlgebra
    ∃ θ : E, IsIntegral R θ ∧ F⟮θ⟯ = ⊤ ∧
      Module.Finite R (Algebra.adjoin R {θ}) ∧
      IsFractionRing (Algebra.adjoin R {θ}) E ∧
      IsNoetherianCompleteLocalRing (Algebra.adjoin R {θ}) ∧
      ringKrullDim (Algebra.adjoin R {θ}) = 1 := by
  let : Algebra R E := ((algebraMap F E).comp (algebraMap R F)).toAlgebra
  have : IsScalarTower R F E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FaithfulSMul R E := .trans R F E
  obtain ⟨θ, hθ, hgen, hfin, hfrac⟩ :=
    exists_finite_integral_primitive_order (R := R) (F := F) (E := E)
  have : Module.Finite R (Algebra.adjoin R {θ}) := hfin
  exact ⟨θ, hθ, hgen, hfin, hfrac, isNoetherianCompleteLocalRing_of_finite_of_isDomain hR,
    ringKrullDim_eq_one_of_isIntegral hdim⟩

/-- Clearing denominators and rescaling a root yields a monic equation of the same degree. -/
private theorem exists_monic_aeval_smul_eq_zero
    {R F E : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [CommRing E] [Algebra F E] [Algebra R E]
    [IsScalarTower R F E] (P : F[X]) (hP : P ≠ 0) (α : E)
    (hα : aeval α P = 0) :
    ∃ (r : R) (Q : R[X]), r ≠ 0 ∧ Q.Monic ∧ Q.natDegree = P.natDegree ∧
      aeval (r • α) Q = 0 := by
  let P₀ := IsLocalization.integerNormalization (nonZeroDivisors R) P
  have hP₀ : P₀ ≠ 0 := mt IsFractionRing.integerNormalization_eq_zero_iff.mp hP
  have hroot : aeval α P₀ = 0 :=
    IsLocalization.integerNormalization_aeval_eq_zero (nonZeroDivisors R) P hα
  refine ⟨P₀.leadingCoeff, P₀.integralNormalization, leadingCoeff_ne_zero.mpr hP₀,
    monic_integralNormalization hP₀, ?_, ?_⟩
  · rw [natDegree_integralNormalization]
    obtain ⟨r, hr, he⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) P
    rw [← natDegree_map_eq_of_injective (IsFractionRing.injective R F), he,
      natDegree_smul _ (nonZeroDivisors.ne_zero hr)]
  · rcases subsingleton_or_nontrivial E with hE | hE
    · exact Subsingleton.elim _ _
    · have : FaithfulSMul R E := .trans R F E
      simpa only [Algebra.smul_def] using integralNormalization_aeval_eq_zero hroot
        (fun x hx => (FaithfulSMul.algebraMap_injective R E) (by simpa using hx))

/-- A monic equation for a primitive element whose degree is the extension degree maps to
its minimal polynomial over the fraction field. -/
private theorem map_eq_minpoly_of_primitive_of_natDegree_eq
    {R F E : Type*} [CommRing R] [Field F] [Algebra R F]
    [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
    [FiniteDimensional F E] (θ : E) (hθ : F⟮θ⟯ = ⊤) (P : R[X]) (hP : P.Monic)
    (hroot : aeval θ P = 0) (hdeg : P.natDegree = Module.finrank F E) :
    P.map (algebraMap R F) = minpoly F θ := by
  apply eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (IsIntegral.of_finite F θ))
    (hP.map _)
  · apply minpoly.dvd F θ
    simpa only [aeval_map_algebraMap] using hroot
  · rw [hP.natDegree_map, hdeg, (Field.primitive_element_iff_minpoly_natDegree_eq F θ).mp hθ]

/-- A finite separable extension admits an integral polynomial presentation of minimal
possible degree after rescaling a primitive element by a nonzero element of the base domain. -/
private theorem exists_primitive_element_monic_aeval_eq_zero
    {R F E : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [Field E] [Algebra F E] [Algebra R E]
    [IsScalarTower R F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    ∃ (θ : E) (P : Polynomial R), F⟮θ⟯ = ⊤ ∧ P.Monic ∧
      Polynomial.aeval θ P = 0 ∧ P.natDegree = Module.finrank F E ∧
      Polynomial.aeval θ P.derivative ≠ 0 := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F E
  obtain ⟨r, P, hr, hP, hd, hz⟩ := exists_monic_aeval_smul_eq_zero (R := R)
    (minpoly F α) (minpoly.ne_zero (Algebra.IsIntegral.isIntegral α)) α (minpoly.aeval F α)
  have heq := adjoin_simple_smul_eq_adjoin_simple (F := F) hr α
  have hdeg := hd.trans ((Field.primitive_element_iff_minpoly_natDegree_eq F α).mp hα)
  refine ⟨r • α, P, heq.trans hα, hP, hz, hdeg, ?_⟩
  have hmap := map_eq_minpoly_of_primitive_of_natDegree_eq (r • α) (heq.trans hα)
    P hP hz hdeg
  have hderiv := (Algebra.IsSeparable.isSeparable F (r • α)).aeval_derivative_ne_zero
    (minpoly.aeval F (r • α))
  rw [← hmap] at hderiv
  simpa only [derivative_map, aeval_map_algebraMap] using hderiv

/-- A finite algebra over a local ring remains generated by an element after perturbing
that element by the extended maximal ideal. -/
private theorem adjoin_eq_top_of_sub_mem_maximalIdeal_smul
    {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] {x y : S} (hx : Algebra.adjoin R {x} = ⊤)
    (hxy : x - y ∈ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) :
    Algebra.adjoin R {y} = ⊤ := by
  let N := Algebra.adjoin R {y}
  let J := Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)
  have approx : ∀ z ∈ Algebra.adjoin R {x}, ∃ w ∈ N, z - w ∈ J := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem z hz =>
        obtain rfl : z = x := Set.mem_singleton_iff.mp hz
        exact ⟨y, Algebra.subset_adjoin (Set.mem_singleton y), hxy⟩
    | algebraMap r => exact ⟨algebraMap R S r, N.algebraMap_mem r, by simp⟩
    | add a b _ _ ha hb =>
        obtain ⟨a', ha', haa'⟩ := ha
        obtain ⟨b', hb', hbb'⟩ := hb
        exact ⟨a' + b', N.add_mem ha' hb', by
          convert J.add_mem haa' hbb' using 1; ring⟩
    | mul a b _ _ ha hb =>
        obtain ⟨a', ha', haa'⟩ := ha
        obtain ⟨b', hb', hbb'⟩ := hb
        exact ⟨a' * b', N.mul_mem ha' hb', by
          convert J.add_mem (J.mul_mem_left a hbb') (J.mul_mem_right b' haa') using 1
          ring⟩
  apply Subalgebra.toSubmodule_injective
  apply top_unique
  apply Submodule.le_of_le_smul_of_le_jacobson_bot (Module.Finite.fg_top)
    (le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm)
  intro z _
  obtain ⟨w, hw, hzw⟩ := approx z (hx ▸ Algebra.mem_top)
  apply Submodule.mem_sup.mpr
  refine ⟨w, hw, z - w, ?_, by abel⟩
  rwa [Ideal.smul_top_eq_map]

/-- In a Noetherian local domain of dimension one, every nonzero ideal contains a power
of the maximal ideal. -/
private theorem exists_maximalIdeal_pow_le_of_ne_bot
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 1) (J : Ideal R) (hJ : J ≠ ⊥) :
    ∃ n : ℕ, IsLocalRing.maximalIdeal R ^ n ≤ J := by
  refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (IsNoetherian.noetherian _)
  rw [Ideal.radical_eq_sInf]
  refine le_sInf ?_
  rintro p ⟨hJp, hp⟩
  exact (IsLocalRing.eq_maximalIdeal_of_ne_bot hdim.le hp (ne_bot_of_le_ne_bot hJ hJp)).ge

/-- A finite separable extension of the completed fraction field has a primitive element
satisfying a monic polynomial over the original ring of degree equal to the extension degree. -/
private theorem exists_primitive_element_monic_polynomial_of_completion
    {A F E : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A)]
    (hdim : ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal A) A) = 1)
    [Field F] [Algebra (AdicCompletion (IsLocalRing.maximalIdeal A) A) F]
    [IsFractionRing (AdicCompletion (IsLocalRing.maximalIdeal A) A) F]
    [Field E] [Algebra F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    let R := AdicCompletion (IsLocalRing.maximalIdeal A) A
    letI : Algebra R E := ((algebraMap F E).comp (algebraMap R F)).toAlgebra
    ∃ (β : E) (Q : A[X]), F⟮β⟯ = ⊤ ∧ Q.Monic ∧
      aeval β (Q.map (algebraMap A R)) = 0 ∧ Q.natDegree = Module.finrank F E := by
  let R := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let : Algebra R E := ((algebraMap F E).comp (algebraMap R F)).toAlgebra
  have : IsScalarTower R F E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FaithfulSMul R E := .trans R F E
  obtain ⟨θ, P, hθ, hP, hz, hd, hderiv⟩ :=
    exists_primitive_element_monic_aeval_eq_zero (R := R) (F := F) (E := E)
  let B := Algebra.adjoin R {θ}
  have hi : IsIntegral R θ := ⟨P, hP, hz⟩
  have : Module.Finite R B := Algebra.finite_adjoin_simple_of_isIntegral hi
  have hB : IsNoetherianCompleteLocalRing B := isNoetherianCompleteLocalRing_of_finite_of_isDomain
    (R := R) ⟨inferInstance, inferInstance, inferInstance⟩
  have : IsLocalRing B := hB.isLocal
  have : IsNoetherianRing B := hB.isNoetherian
  have : IsAdicComplete (IsLocalRing.maximalIdeal B) B := hB.isComplete
  have hdimB : ringKrullDim B = 1 := ringKrullDim_eq_one_of_isIntegral hdim
  let θB : B := ⟨θ, Algebra.subset_adjoin (Set.mem_singleton θ)⟩
  have hev : ∀ (x : B) (p : R[X]), (p.map (algebraMap R B)).eval x = 0 ↔ aeval (x : E) p = 0 :=
    fun x p => by rw [eval_map, ← aeval_def, ← aeval_subalgebra_coe, ZeroMemClass.coe_eq_zero]
  let J := Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R)
  have hJ : J ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot (maximalIdeal_ne_bot_of_ringKrullDim_eq_one hdim)
  obtain ⟨c, hc⟩ := exists_maximalIdeal_pow_le_of_ne_bot hdimB J hJ
  obtain ⟨n, hn⟩ := _root_.krasner_lemma B hdimB (P.map (algebraMap R B)) θB
    ((hev θB P).mpr hz) (by rwa [derivative_map, ne_eq, hev]) c
  obtain ⟨Q, hQ, hdeg, happ⟩ := exists_monic_approx_adicCompletion P hP n
  let Q' := Q.map (algebraMap A R)
  have hcoeff : ∀ i, ((Q' - P).map (algebraMap R B)).coeff i ∈
      IsLocalRing.maximalIdeal B ^ n := by
    intro i
    have hle : Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R) ≤
        IsLocalRing.maximalIdeal B := IsLocalRing.map_maximalIdeal_le _
    have hm : (Q' - P).coeff i ∈ IsLocalRing.maximalIdeal R ^ n := by
      simpa only [← coeff_neg, neg_sub] using
        (IsLocalRing.maximalIdeal R ^ n).neg_mem (happ i)
    have hmap := Ideal.mem_map_of_mem (algebraMap R B) hm
    rw [Ideal.map_pow] at hmap
    simpa only [coeff_map] using Ideal.pow_right_mono hle n hmap
  obtain ⟨β, hβ, hclose⟩ := hn ((Q' - P).map (algebraMap R B)) hcoeff
  have hroot : aeval (β : E) Q' = 0 :=
    (hev β Q').mp (by rwa [Polynomial.map_sub, add_sub_cancel] at hβ)
  have hgenB : Algebra.adjoin R {θB} = ⊤ := by
    convert Algebra.adjoin_adjoin_coe_preimage (R := R) (s := {θ}) using 2
    ext b
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact Subtype.ext_iff
  have hβB : Algebra.adjoin R {β} = ⊤ :=
    adjoin_eq_top_of_sub_mem_maximalIdeal_smul hgenB
      (by simpa only [neg_sub] using J.neg_mem (hc hclose))
  have hθmem : θ ∈ F⟮(β : E)⟯ := by
    have hmem : ∀ b ∈ Algebra.adjoin R {β}, (b : E) ∈ F⟮(β : E)⟯ := by
      intro b hb
      induction hb using Algebra.adjoin_induction with
      | mem z hz =>
          obtain rfl := Set.mem_singleton_iff.mp hz
          exact mem_adjoin_simple_self F _
      | algebraMap r =>
          change algebraMap R E r ∈ F⟮(β : E)⟯
          rw [IsScalarTower.algebraMap_apply R F E]
          exact IntermediateField.algebraMap_mem _ _
      | add a b _ _ ha hb => exact add_mem ha hb
      | mul a b _ _ ha hb => exact mul_mem ha hb
    exact hmem θB (hβB ▸ Algebra.mem_top)
  exact ⟨(β : E), Q, top_unique (hθ.symm.le.trans (adjoin_simple_le_iff.mpr hθmem)), hQ, hroot,
    hdeg.trans hd⟩

/-- A primitive element whose equation descends without increasing degree gives a finite
separable extension whose scalar extension is the given field. -/
private theorem exists_intermediateField_tensorProduct_equiv_of_primitive
    {K F E : Type*} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (β : E) (hβ : F⟮β⟯ = ⊤) (Q : K[X]) (hQ : Q.Monic)
    (hroot : aeval β Q = 0) (hdeg : Q.natDegree = Module.finrank F E) :
    ∃ L : IntermediateField K (AlgebraicClosure K),
      FiniteDimensional K L ∧ Algebra.IsSeparable K L ∧
        Nonempty (TensorProduct K F L ≃ₐ[F] E) := by
  have hi : IsIntegral K β := ⟨Q, hQ, hroot⟩
  have hmap := map_eq_minpoly_of_primitive_of_natDegree_eq β hβ Q hQ hroot hdeg
  have hsep : Q.Separable := (Polynomial.separable_map (algebraMap K F)).mp
    (hmap ▸ Algebra.IsSeparable.isSeparable F β)
  have hβsep : IsSeparable K β := hsep.of_dvd (minpoly.dvd K β hroot)
  let L₀ := K⟮β⟯
  have : FiniteDimensional K L₀ := IntermediateField.adjoin.finiteDimensional hi
  have : Algebra.IsSeparable K L₀ :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K E).mpr hβsep
  let g : TensorProduct K F L₀ →ₐ[F] E := AlgHom.liftEquiv K F L₀ E L₀.val
  have hg : Function.Surjective g := by
    rw [← AlgHom.range_eq_top]
    apply top_unique
    rw [← IntermediateField.adjoin_eq_top_iff.mp hβ]
    apply Algebra.adjoin_le
    rw [Set.singleton_subset_iff]
    exact ⟨1 ⊗ₜ[K] (⟨β, mem_adjoin_simple_self K β⟩ : L₀), by
      simp [g, AlgHom.liftEquiv_tmul]⟩
  have hdim : Module.finrank F (TensorProduct K F L₀) ≤ Module.finrank F E := by
    rw [Module.finrank_baseChange, IntermediateField.adjoin.finrank hi, ← hdeg]
    exact Polynomial.natDegree_le_of_dvd (minpoly.dvd K β hroot) hQ.ne_zero
  let e : TensorProduct K F L₀ ≃ₐ[F] E := AlgEquiv.ofBijective g
    (OrzechProperty.bijective_of_surjective_of_finrank_le g.toLinearMap hg hdim)
  let f : L₀ →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let L := f.fieldRange
  let e₀ : L₀ ≃ₐ[K] L := f.equivFieldRange
  have : FiniteDimensional K L := Module.Finite.equiv e₀.toLinearEquiv
  have : Algebra.IsSeparable K L := Algebra.IsSeparable.of_algHom K L₀ e₀.symm.toAlgHom
  exact ⟨L, inferInstance, inferInstance,
    ⟨(Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F) e₀.symm).trans e⟩⟩

/-- **Stacks 09EJ.** Let `A` be a Noetherian local ring whose completion at its maximal ideal is a
one-dimensional domain. A finite separable extension of the fraction field of the completion is
obtained by scalar extension from a finite separable extension of the fraction field of `A`. -/
@[stacks 09EJ]
theorem exists_finite_separable_extension_tensorProduct_equiv
    {A K Khat M : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A)]
    (hAhat_dim : ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal A) A) = 1)
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field Khat]
    [Algebra (AdicCompletion (IsLocalRing.maximalIdeal A) A) Khat]
    [IsFractionRing (AdicCompletion (IsLocalRing.maximalIdeal A) A) Khat]
    [Field M] [Algebra Khat M] [FiniteDimensional Khat M]
    [Algebra.IsSeparable Khat M] :
    let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
    letI : Algebra A Khat :=
      ((algebraMap Ahat Khat).comp (algebraMap A Ahat)).toAlgebra
    letI : Algebra K Khat :=
      (IsFractionRing.lift (A := A) (K := K) (L := Khat) (g := algebraMap A Khat)
        ((IsFractionRing.injective Ahat Khat).comp
          (by
            dsimp only [Ahat]
            exact AdicCompletion.of_injective (IsLocalRing.maximalIdeal A) A))).toAlgebra
    ∃ L : IntermediateField K (AlgebraicClosure K),
      FiniteDimensional K L ∧ Algebra.IsSeparable K L ∧
        Nonempty (TensorProduct K Khat L ≃ₐ[Khat] M) := by
  let R := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let : Algebra A Khat := ((algebraMap R Khat).comp (algebraMap A R)).toAlgebra
  have hinj : Function.Injective (algebraMap A Khat) :=
    (IsFractionRing.injective R Khat).comp
      (AdicCompletion.of_injective (IsLocalRing.maximalIdeal A) A)
  let : Algebra K Khat := (IsFractionRing.lift (K := K) hinj).toAlgebra
  change ∃ L : IntermediateField K (AlgebraicClosure K),
    FiniteDimensional K L ∧ Algebra.IsSeparable K L ∧
      Nonempty (TensorProduct K Khat L ≃ₐ[Khat] M)
  let : Algebra R M := ((algebraMap Khat M).comp (algebraMap R Khat)).toAlgebra
  have : IsScalarTower R Khat M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra K M := ((algebraMap Khat M).comp (algebraMap K Khat)).toAlgebra
  have : IsScalarTower K Khat M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨β, Q, hβ, hQ, hroot, hdeg⟩ :=
    exists_primitive_element_monic_polynomial_of_completion (F := Khat) (E := M) hAhat_dim
  apply exists_intermediateField_tensorProduct_equiv_of_primitive β hβ
    (Q.map (algebraMap A K)) (hQ.map _)
  · have hmaps : (algebraMap K Khat).comp (algebraMap A K) =
        (algebraMap R Khat).comp (algebraMap A R) :=
      RingHom.ext fun a => IsFractionRing.lift_algebraMap (K := K) hinj a
    rwa [← aeval_map_algebraMap Khat, Polynomial.map_map, hmaps,
      ← Polynomial.map_map, aeval_map_algebraMap]
  · rw [hQ.natDegree_map, hdeg]

end Krasner
