module

public import StacksFrontier.RingTheory.HilbertFunction.PolynomialQuotient
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Data.Rat.Star
import Mathlib.Order.Interval.Finset.Box
import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.AffineMonoid.UniqueSums

/-!
# Numerical polynomials in natural arguments and admissible graded modules

The `ℕ`-indexed notion `IsNumericalPolynomialByNaturalArgs` with its closure lemmas and the
first-difference criterion `numerical_polynomial_of_difference`; admissible graded modules
over `k[X_1, …, X_d]`; and admissibility of the kernel of multiplication by the last
variable.
-/

@[expose] public section
-- needed file-wide: `FinModule.cls_eq_of_linearEquiv`, `FinModule.cls_add_of_ses`,
-- `KPrime0.hom_ext`, `xpow_four_term_class` and `hilbertFun_xpow_step_identity` all rewrite
-- through the `FinModule`/`KPrime0` quotient wrappers and the graded-piece subgroup coercions,
-- which only unfold with defeq transparency relaxed.  See also the note before
-- `section MainPieces`, which depends on this option holding for the whole file.
set_option backward.isDefEq.respectTransparency false
universe u

namespace Stacks.HilbertFunction.PolynomialQuotient

variable {k : Type*} [Field k] {d : ℕ}

/-! ## Background fact (Stacks Proposition 10.58.7 / Example 10.58.9, Tags 00K1, 00K2)

For `M = S / I` with `I` a graded ideal, the Hilbert function `H_M`, extended by
`0` to negative degrees, is a numerical polynomial in the sense of
`IsNumericalPolynomial` (Stacks Definition 10.58.3, Tag 00JX). This holds for
every graded ideal, including `I = 0`; the main theorem below strengthens it, for
*nonzero* `I`, with the degree bound `< d - 1`. It is used as an input to the main
theorem (it supplies the representing polynomial whose degree we bound), so it is
placed before it.

It follows from the `ℕ`-indexed statement
`isNumericalPolynomialByNaturalArgs_hilbertFunction`, proved by induction on the
number of variables via the multiplication-by-`X_d` first-difference identity, and
the extension-by-zero lemma
`IsNumericalPolynomialByNaturalArgs.isNumericalPolynomial_extend`. -/

/-- **`ℕ`-indexed numerical polynomial (Stacks Definition, Tag 00JZ).**
`f : ℕ → ℤ` is a numerical polynomial in the `ℕ`-indexed sense if it is eventually
equal to a finite integer combination of binomial coefficients
`n ↦ ∑ i, (n.choose i) • a i`. -/
def IsNumericalPolynomialByNaturalArgs (f : ℕ → ℤ) : Prop :=
  ∃ (r : ℕ) (a : Fin (r + 1) → ℤ),
    ∀ᶠ n in Filter.atTop, f n = ∑ i : Fin (r + 1), (n.choose (i : ℕ)) • a i

/-- If `g : ℕ → ℤ` is a numerical polynomial in the `ℕ`-indexed sense, then its
extension by `0` to `ℤ` is a numerical polynomial in the sense of
`IsNumericalPolynomial`. -/
theorem IsNumericalPolynomialByNaturalArgs.isNumericalPolynomial_extend (g : ℕ → ℤ)
    (h : IsNumericalPolynomialByNaturalArgs g) :
    IsNumericalPolynomial (fun n : ℤ => if 0 ≤ n then (g n.toNat) else 0) := by
  obtain ⟨r, a, ha⟩ := h
  refine ⟨r, a, ?_⟩
  rw [Filter.eventually_atTop] at ha ⊢
  obtain ⟨N, hN⟩ := ha
  refine ⟨(N : ℤ), fun n hn => ?_⟩
  simp only
  have h0 : 0 ≤ n := le_trans (Int.natCast_nonneg N) hn
  rw [ite_eq_left h0]
  have htoNat : (n.toNat : ℤ) = n := Int.toNat_of_nonneg h0
  have hNle : N ≤ n.toNat := by
    have : (N : ℤ) ≤ (n.toNat : ℤ) := by
      rw [htoNat]; exact hn
    exact_mod_cast this
  rw [hN n.toNat hNle]
  apply Finset.sum_congr rfl
  intro i _
  have hc : Ring.choose n (i : ℕ) = ((n.toNat.choose (i : ℕ) : ℕ) : ℤ) := by
    conv_lhs =>
      rw [← htoNat]; rw [Ring.choose_natCast]
  rw [hc, natCast_zsmul]

/-! ### CORE LEMMA overview (Stacks Proposition 10.58.7, Tags 00K1/00K2)

For `M = S / I` with `I` a graded ideal, the Hilbert function
`n ↦ H_M(n) = dim_k(M_n)`, as a `ℕ`-indexed function, is a numerical polynomial in
the `ℕ`-indexed sense.

Argument. Prove the more general
statement that the Hilbert function of *any* finitely generated graded
`S^{(d)} = k[X_1,…,X_d]`-module that is bounded-below with finite-dimensional
graded pieces ("admissible") is a numerical polynomial, by induction on `d`.

* Base `d = 0`: `S^{(0)} = k`, an admissible graded `k`-module is supported in
  finitely many degrees, so `H_M(n) = 0` for `n ≫ 0` — numerical (`binomial_sum`
  with zero coefficients).
* Step `d ≥ 1`: let `x = X_d`. `K = ker(·x)` and `C = M / xM` are admissible
  graded modules over `S^{(d)}/(X_d) ≅ S^{(d-1)}`, so by IH `H_K`, `H_C` are
  numerical. The degreewise rank–nullity identity for `·x : M_{n-1} → M_n` gives
  `H_M(n) - H_M(n-1) = H_C(n) - H_K(n-1)`. The right-hand side is numerical by the
  inductive hypothesis and the closure lemmas below. Hence the first difference of
  `H_M` is numerical, so by `numerical_polynomial_of_difference` `H_M` is numerical. -/

/-! ### Closure lemmas for `IsNumericalPolynomialByNaturalArgs`

`ℕ`-indexed numerical polynomials are closed under eventual equality, addition,
negation, subtraction, and the unit shift `n ↦ g (n - 1)`. -/

/-- If `f = g` eventually and `g` is a
`ℕ`-indexed numerical polynomial, so is `f`. -/
theorem IsNumericalPolynomialByNaturalArgs.congr {f g : ℕ → ℤ}
    (h : ∀ᶠ n in Filter.atTop, f n = g n)
    (hg : IsNumericalPolynomialByNaturalArgs g) : IsNumericalPolynomialByNaturalArgs f := by
  obtain ⟨r, a, ha⟩ := hg
  exact ⟨r, a, h.and ha |>.mono (fun n ⟨h1, h2⟩ => h1.trans h2)⟩

/-- Range-sum reformulation of `IsNumericalPolynomialByNaturalArgs`: `f` is a
`ℕ`-indexed numerical polynomial iff it is eventually a finite range-sum
`∑ i ∈ range (t+1), n.choose i • c i` for some length `t` and coefficient
function `c : ℕ → ℤ`. This is the convenient shape for padding to a common length. -/
theorem isNumericalPolynomialByNaturalArgs_iff_range (f : ℕ → ℤ) :
    IsNumericalPolynomialByNaturalArgs f ↔
      ∃ (t : ℕ) (c : ℕ → ℤ),
        ∀ᶠ n in Filter.atTop, f n = ∑ i ∈ Finset.range (t + 1), n.choose i • c i := by
  constructor
  · rintro ⟨r, a, ha⟩
    refine ⟨r, fun i => if h : i < r + 1 then a ⟨i, h⟩ else 0, ha.mono (fun n hn => ?_)⟩
    rw [hn, Finset.sum_range fun i => n.choose i • (if h : i < r + 1 then a ⟨i, h⟩ else (0 : ℤ))]
    exact Finset.sum_congr rfl fun i _ => by simp [i.isLt]
  · rintro ⟨t, c, hc⟩
    refine ⟨t, fun i => c (i : ℕ), hc.mono (fun n hn => ?_)⟩
    rw [hn, Finset.sum_range fun i => n.choose i • c i]

/-- Zero-padding a range-sum representation out to a longer range. -/
private theorem npba_pad (t T : ℕ) (hT : t + 1 ≤ T + 1) (c : ℕ → ℤ) (n : ℕ) :
    ∑ i ∈ Finset.range (t + 1), n.choose i • c i =
      ∑ i ∈ Finset.range (T + 1), n.choose i • (if i < t + 1 then c i else 0) := by
  have hsub : Finset.range (t + 1) ⊆ Finset.range (T + 1) := by
    intro x hx; rw [Finset.mem_range] at hx ⊢; omega
  rw [← Finset.sum_subset hsub]
  · apply Finset.sum_congr rfl; intro i hi
    rw [Finset.mem_range] at hi; simp [hi]
  · intro i _ hi
    rw [Finset.mem_range] at hi; simp [hi]

/-- Additive closure. -/
theorem IsNumericalPolynomialByNaturalArgs.add {f g : ℕ → ℤ}
    (hf : IsNumericalPolynomialByNaturalArgs f) (hg : IsNumericalPolynomialByNaturalArgs g) :
    IsNumericalPolynomialByNaturalArgs (fun n => f n + g n) := by
  rw [isNumericalPolynomialByNaturalArgs_iff_range] at hf hg ⊢
  obtain ⟨t, c, hc⟩ := hf
  obtain ⟨s, e, he⟩ := hg
  refine ⟨max t s, fun i => (if i < t + 1 then c i else 0) + (if i < s + 1 then e i else 0), ?_⟩
  filter_upwards [hc, he] with n hcn hen
  rw [hcn, hen]
  rw [npba_pad t (max t s) (by omega) c n, npba_pad s (max t s) (by omega) e n]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [smul_add]

/-- Negation closure. -/
theorem IsNumericalPolynomialByNaturalArgs.neg {f : ℕ → ℤ}
    (hf : IsNumericalPolynomialByNaturalArgs f) :
    IsNumericalPolynomialByNaturalArgs (fun n => -f n) := by
  rw [isNumericalPolynomialByNaturalArgs_iff_range] at hf ⊢
  obtain ⟨t, c, hc⟩ := hf
  refine ⟨t, fun i => -c i, hc.mono (fun n hn => ?_)⟩
  rw [hn]
  simp only [smul_neg]
  exact (Finset.sum_neg_distrib _).symm

/-- Subtraction closure. -/
theorem IsNumericalPolynomialByNaturalArgs.sub {f g : ℕ → ℤ}
    (hf : IsNumericalPolynomialByNaturalArgs f) (hg : IsNumericalPolynomialByNaturalArgs g) :
    IsNumericalPolynomialByNaturalArgs (fun n => f n - g n) :=
  (hf.add hg.neg).congr (Filter.Eventually.of_forall fun n => by ring)

/-- The constant range-sum function is a numerical polynomial (the `binomial_sum`
primitive transported to the `ℕ`-indexed range-sum shape). -/
theorem isNumericalPolynomialByNaturalArgs_binomial_sum (t : ℕ) (c : ℕ → ℤ) :
    IsNumericalPolynomialByNaturalArgs
      (fun n => ∑ i ∈ Finset.range (t + 1), n.choose i • c i) := by
  rw [isNumericalPolynomialByNaturalArgs_iff_range]
  exact ⟨t, c, Filter.Eventually.of_forall (fun _ => rfl)⟩

/-- A constant function is a `ℕ`-indexed numerical polynomial. -/
private theorem npba_const (K : ℤ) : IsNumericalPolynomialByNaturalArgs (fun _ : ℕ => K) := by
  refine (isNumericalPolynomialByNaturalArgs_binomial_sum 0 (fun _ => K)).congr ?_
  apply Filter.Eventually.of_forall; intro n; simp

/-- A single binomial coefficient `n ↦ n.choose i` is a `ℕ`-indexed numerical polynomial. -/
private theorem npba_choose (i : ℕ) :
    IsNumericalPolynomialByNaturalArgs (fun n => (n.choose i : ℤ)) := by
  refine (isNumericalPolynomialByNaturalArgs_binomial_sum i
    (fun j => if j = i then 1 else 0)).congr ?_
  apply Filter.Eventually.of_forall
  intro n
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · intro hmem; rw [Finset.mem_range] at hmem; omega

/-- Scalar-multiplication closure: if `f` is a `ℕ`-indexed numerical polynomial then
so is `n ↦ m * f n` (multiply the coefficient function by `m`). -/
private theorem npba_smul (m : ℤ) {f : ℕ → ℤ} (hf : IsNumericalPolynomialByNaturalArgs f) :
    IsNumericalPolynomialByNaturalArgs (fun n => m * f n) := by
  rw [isNumericalPolynomialByNaturalArgs_iff_range] at hf ⊢
  obtain ⟨t, c, hc⟩ := hf
  refine ⟨t, fun i => m * c i, hc.mono (fun n hn => ?_)⟩
  rw [hn, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A single shifted binomial `n ↦ (n-1).choose i` is a `ℕ`-indexed numerical
polynomial, by induction on `i` via Pascal's rule. -/
private theorem npba_shiftBinom (i : ℕ) :
    IsNumericalPolynomialByNaturalArgs (fun n => ((n - 1).choose i : ℤ)) := by
  induction i with
  | zero =>
    refine (npba_const 1).congr ?_
    apply Filter.Eventually.of_forall
    intro n
    simp
  | succ i
    ih =>
    have hsub := IsNumericalPolynomialByNaturalArgs.sub (npba_choose (i + 1)) ih
    refine IsNumericalPolynomialByNaturalArgs.congr ?_ hsub
    rw [Filter.eventually_atTop]
    refine ⟨1, fun n hn => ?_⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    simp only [Nat.add_sub_cancel_left]
    rw [Nat.add_comm 1 m, Nat.choose_succ_succ]
    push_cast
    ring

/-- A finite range-indexed sum of `ℕ`-indexed numerical polynomials is one. -/
private theorem npba_sum_range (N : ℕ) (F : ℕ → ℕ → ℤ)
    (hF : ∀ i ∈ Finset.range N, IsNumericalPolynomialByNaturalArgs (fun n => F i n)) :
    IsNumericalPolynomialByNaturalArgs (fun n => ∑ i ∈ Finset.range N, F i n) := by
  induction N with
  | zero => simpa using npba_const 0
  | succ N
    ih =>
    have hrest : IsNumericalPolynomialByNaturalArgs (fun n => ∑ i ∈ Finset.range N, F i n) :=
      ih fun i hi => hF i (Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hi)))
    refine IsNumericalPolynomialByNaturalArgs.congr (.of_forall fun n => ?_)
      (IsNumericalPolynomialByNaturalArgs.add hrest (hF N (Finset.self_mem_range_succ N)))
    rw [Finset.sum_range_succ]

/-- The unit shift `n ↦ g (n - 1)` of an `ℕ`-indexed numerical polynomial is again one. -/
theorem IsNumericalPolynomialByNaturalArgs.comp_sub_one {g : ℕ → ℤ}
    (hg : IsNumericalPolynomialByNaturalArgs g) :
    IsNumericalPolynomialByNaturalArgs (fun n => g (n - 1)) := by
  rw [isNumericalPolynomialByNaturalArgs_iff_range] at hg
  obtain ⟨t, c, hc⟩ := hg
  rw [Filter.eventually_atTop] at hc
  obtain ⟨N, hN⟩ := hc
  -- For `n ≥ N+1`, `g (n-1) = ∑ i ∈ range (t+1), (n-1).choose i • c i`, a finite sum
  -- of `c i`-multiples of the shifted binomials `npba_shiftBinom i`.
  have hsum :
    IsNumericalPolynomialByNaturalArgs
      (fun n => ∑ i ∈ Finset.range (t + 1), ((n - 1).choose i : ℤ) • c i) := by
    have hmul :
      IsNumericalPolynomialByNaturalArgs
        (fun n => ∑ i ∈ Finset.range (t + 1), c i * ((n - 1).choose i : ℤ)) :=
      npba_sum_range _ _ fun i _ => npba_smul (c i) (npba_shiftBinom i)
    refine IsNumericalPolynomialByNaturalArgs.congr (.of_forall fun n => ?_) hmul
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_eq_mul, mul_comm]
  refine IsNumericalPolynomialByNaturalArgs.congr ?_ hsum
  rw [Filter.eventually_atTop]
  refine ⟨N + 1, fun n hn => ?_⟩
  have hn1 : N ≤ n - 1 := by omega
  rw [hN (n - 1) hn1]
  simp only [natCast_zsmul]

/-- **Antidifference closure (Stacks Lemma, Tag 00JZ).** If the first difference
`n ↦ f n - f (n-1)` of `f : ℕ → ℤ` is a `ℕ`-indexed numerical polynomial, then so
is `f`. -/
theorem numerical_polynomial_of_difference (f : ℕ → ℤ)
    (h : IsNumericalPolynomialByNaturalArgs (fun n => f n - f (n - 1))) :
    IsNumericalPolynomialByNaturalArgs f := by
  -- Reformulate the difference as a range sum.
  rw [isNumericalPolynomialByNaturalArgs_iff_range] at h
  obtain ⟨t, c, hc⟩ := h
  rw [Filter.eventually_atTop] at hc
  obtain ⟨N, hN⟩ := hc
  -- The antidifference candidate: `F n = ∑ i, c i • (n.choose (i+1) + n.choose i)`.
  -- Its first difference is `∑ i, n.choose i • c i = f n - f (n-1)` for `n ≥ N+1`.
  set F : ℕ → ℤ := fun n =>
    ∑ i ∈ Finset.range (t + 1), c i * ((n.choose (i + 1) : ℤ) + (n.choose i : ℤ)) with hF
  -- `F` is a `ℕ`-indexed numerical polynomial.
  have hFnpba : IsNumericalPolynomialByNaturalArgs F := by
    rw [hF]
    apply npba_sum_range
    intro i _
    apply npba_smul
    exact (npba_choose (i + 1)).add (npba_choose i)
  -- The first difference of `F` equals `f n - f (n-1)` for `n ≥ N+1`.
  have hdiff : ∀ n, N + 1 ≤ n → F n - F (n - 1) = f n - f (n - 1) := by
    intro n hn
    rw [hN n (by omega)]
    rw [hF]
    simp only
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    -- write n = m + 1
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [Nat.choose_succ_succ' m i]
    push_cast
    ring
  -- Hence `f - F` is eventually constant equal to `K := f (N+1) - F (N+1)`.
  set K : ℤ := f (N + 1) - F (N + 1) with hK
  have hconst : ∀ n, N + 1 ≤ n → f n - F n = K := by
    intro n hn
    induction n with
    | zero => omega
    | succ m ih =>
      rcases Nat.lt_or_ge (N + 1) (m + 1) with hlt | hge
      · -- m + 1 > N + 1, so m ≥ N + 1
        have hmge : N + 1 ≤ m := by omega
        have hd := hdiff (m + 1) (by omega)
        simp only [Nat.add_sub_cancel] at hd
        have := ih hmge
        linarith [hd, this]
      · -- m + 1 = N + 1
        have : m + 1 = N + 1 := by omega
        rw [this, hK]
  -- So `f n = F n + K` eventually; both are numerical, so `f` is.
  have hsum := IsNumericalPolynomialByNaturalArgs.add hFnpba (npba_const K)
  refine IsNumericalPolynomialByNaturalArgs.congr ?_ hsum
  rw [Filter.eventually_atTop]
  refine ⟨N + 1, fun n hn => ?_⟩
  have := hconst n hn
  show f n = F n + K
  linarith [this]

/-! ### The analytic core: the generalized graded-module Hilbert–Serre induction

By `numerical_polynomial_of_difference`, to show `H_M` is a numerical polynomial it
suffices to show its first difference `n ↦ H_M(n) - H_M(n-1)` is one. The
first-difference fact is the genuine content of Stacks Prop 10.58.7: it is proved by
induction on the number of variables `d` via the multiplication-by-`X_d`
rank–nullity identity `H_M(n) - H_M(n-1) = H_C(n) - H_K(n-1)`, where `K = ker(·X_d)`
and `C = M/X_d M` are admissible graded `S^{(d-1)}`-modules.
Carrying out that induction faithfully requires generalizing
from `S/I` to arbitrary finitely generated admissible graded modules. We set up that
generalization here: an `AdmissibleGradedModule` datum, the generalized Hilbert
function `hilb`, the induction `isNumericalPolynomialByNaturalArgs_hilb`, and the
specialization to `M = S/I`. -/

/-- An **admissible graded module** over `S = MvPolynomial (Fin d) k`: a module `M`
equipped with an internal `ℕ`-grading `Mgr : ℕ → Submodule k M` (by `k`-submodules),
compatible with multiplication by the variables (which raise degree by `1`), with
finite-dimensional graded pieces, and finitely generated as an `S`-module. This is
exactly the package the Hilbert-function induction on `d` needs; it specializes to
`M = S/I`. (Encoding choice: an `ℕ`-grading suffices because all modules in the
argument are non-negatively graded; the negative pieces are `0`. The universe of `M`
is pinned to that of `k` via `.{u}` so existential statements over
`AdmissibleGradedModule k d` carry no free universe metavariable.) -/
structure AdmissibleGradedModule (k : Type u) [Field k] (d : ℕ) where
  /-- the underlying module -/
  M : Type u
  [addCommGroup : AddCommGroup M]
  [moduleK : Module k M]
  [moduleS : Module (MvPolynomial (Fin d) k) M]
  [tower : IsScalarTower k (MvPolynomial (Fin d) k) M]
  /-- the `ℕ`-grading by `k`-submodules -/
  Mgr : ℕ → Submodule k M
  /-- the grading is internally independent (direct) -/
  iSupIndep : iSupIndep Mgr
  /-- the grading spans `M` -/
  iSup_eq : iSup Mgr = ⊤
  /-- each graded piece is finite-dimensional over `k` -/
  finite : ∀ n, Module.Finite k (Mgr n)
  /-- multiplication by a variable sends `M_n` into `M_{n+1}` -/
  smul_mem :
    ∀ (i : Fin d) (n : ℕ) (x : M),
      x ∈ Mgr n → ((MvPolynomial.X i : MvPolynomial (Fin d) k) • x) ∈ Mgr (n + 1)
  /-- `M` is finitely generated as an `S`-module -/
  fg : Module.Finite (MvPolynomial (Fin d) k) M

attribute [instance] AdmissibleGradedModule.addCommGroup AdmissibleGradedModule.moduleK
  AdmissibleGradedModule.moduleS AdmissibleGradedModule.tower

/-- The **generalized Hilbert function** of an admissible graded module:
`H_M(n) = dim_k(M_n)`, as a `ℤ`-valued function. -/
noncomputable def AdmissibleGradedModule.hilb {d : ℕ} (A : AdmissibleGradedModule k d) (n : ℕ) :
    ℤ :=
  (Module.finrank k (A.Mgr n) : ℤ)

/-- An admissible graded module over `S^{(0)} = k` is finite-dimensional, hence
supported in finitely many degrees, so its Hilbert function is eventually `0`. -/
theorem AdmissibleGradedModule.hilb_eventually_eq_zero (A : AdmissibleGradedModule k 0) :
    ∀ᶠ n in Filter.atTop, A.hilb n = 0 := by
  -- `MvPolynomial (Fin 0) k` is finite over `k`, so via the scalar tower and `A.fg`,
  -- `A.M` is finite-dimensional over `k`.
  have hSfin : Module.Finite k (MvPolynomial (Fin 0) k) :=
    Module.Finite.of_surjective (MvPolynomial.isEmptyAlgEquiv k (Fin 0)).symm.toLinearMap
      (MvPolynomial.isEmptyAlgEquiv k (Fin 0)).symm.surjective
  have hfgS : Module.Finite (MvPolynomial (Fin 0) k) A.M := A.fg
  have hMfin : Module.Finite k A.M := Module.Finite.trans (MvPolynomial (Fin 0) k) A.M
  -- The independent family `A.Mgr` has finite non-⊥ support.
  have hfin : {n | A.Mgr n ≠ ⊥}.Finite := WellFoundedLT.finite_ne_bot_of_iSupIndep A.iSupIndep
  -- Bound the support.
  obtain ⟨N, hN⟩ := hfin.bddAbove
  rw [Filter.eventually_atTop]
  refine ⟨N + 1, fun n hn => ?_⟩
  have hbot : A.Mgr n = ⊥ := by
    by_contra h
    have : n ≤ N := hN h
    omega
  show (Module.finrank k (A.Mgr n) : ℤ) = 0
  rw [hbot]
  simp [finrank_bot]

/-- The degreewise **multiplication-by-`X_{last}`** map `A.Mgr m → A.Mgr (m+1)` for an
admissible graded `S^{(d+1)}`-module `A`. It is `k`-linear; `A.smul_mem` guarantees that
multiplying an element of `A.Mgr m` by the last variable lands in `A.Mgr (m+1)`. The
kernel of this map (in degree `m`) is the degree-`m` piece of `K = ker(·X_last)`, and its
cokernel `A.Mgr (m+1) / range` is the degree-`(m+1)` piece of `C = M/(X_last·M)`. -/
noncomputable def mulXLastDeg {d : ℕ} (A : AdmissibleGradedModule k (d + 1)) (m : ℕ) :
    A.Mgr m →ₗ[k] A.Mgr (m + 1)
    where
  toFun x :=
    ⟨(MvPolynomial.X (Fin.last d) : MvPolynomial (Fin (d + 1)) k) • (x : A.M),
      A.smul_mem (Fin.last d) m x x.property⟩
  map_add' x y := by
    apply Subtype.ext
    change
      (MvPolynomial.X (Fin.last d) : MvPolynomial (Fin (d + 1)) k) • ((x : A.M) + y) =
        (MvPolynomial.X (Fin.last d) : MvPolynomial (Fin (d + 1)) k) • (x : A.M) +
          (MvPolynomial.X (Fin.last d) : MvPolynomial (Fin (d + 1)) k) • (y : A.M)
    rw [smul_add]
  map_smul' c x := by
    apply Subtype.ext
    change
      (MvPolynomial.X (Fin.last d) : MvPolynomial (Fin (d + 1)) k) • (c • (x : A.M)) =
        c • ((MvPolynomial.X (Fin.last d) : MvPolynomial (Fin (d + 1)) k) • (x : A.M))
    rw [smul_comm]

/- The graded kernel as an admissible `S^{(d)}`-module.
For an admissible graded `S^{(d+1)}`-module `A`, the kernel `K = ker(·X_last)` is an
admissible graded `S^{(d)}`-module whose degree-`m` Hilbert value equals the dimension of
the kernel of the degreewise map `mulXLastDeg A m : A.Mgr m → A.Mgr (m+1)`.

Construction: `K = ker(·X_last) ⊆ A.M` is a graded submodule (its homogeneous pieces are
`K_m = ker(mulXLastDeg A m)`, mapped into `A.M`); `X_last` annihilates `K`, so the
`S^{(d+1)}`-action factors through `S^{(d+1)}/(X_last) ≅ S^{(d)}` (`MvPolynomial.finSuccEquiv`
/ rename), making `K` an `S^{(d)}`-module; it is f.g. (submodule of a Noetherian f.g.
module) and finite-dim degreewise (sits inside `A.Mgr`). -/
/-- **Homogeneity of the kernel of a degree-shifting linear map.** If `T : M → M` raises
degree by one (`T (p n) ⊆ p (n+1)`) for an independent spanning grading `p`, then any
`y` with `T y = 0` decomposes into homogeneous pieces each lying in `ker T`. -/
theorem ker_homogeneous {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (p : ℕ → Submodule R M) (T : M →ₗ[R] M) (hindep : iSupIndep p) (htop : iSup p = ⊤)
    (hshift : ∀ (n : ℕ) (x : M), x ∈ p n → T x ∈ p (n + 1)) (y : M) (hy : T y = 0) :
    y ∈ ⨆ n, (p n ⊓ LinearMap.ker T) := by
  classical
  have hymem : y ∈ ⨆ n, p n := htop ▸ Submodule.mem_top
  rw [Submodule.mem_iSup_iff_exists_dfinsupp] at hymem
  obtain ⟨f, hf⟩ := hymem
  set L := DFinsupp.lsum ℕ (fun n => (p n).subtype) with hL
  have hLeq : ∀ (φ : Π₀ n, p n), L φ = φ.sum (fun n b => (b : M)) := by
    intro φ
    simp only [hL, DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply]; rfl
  set g : Π₀ n, p n :=
    f.sum
      (fun i fi =>
        DFinsupp.single (i + 1) (⟨T (fi : M), hshift i fi fi.property⟩ : p (i + 1))) with
    hg
  have hLg : L g = T y := by
    rw [hg, map_dfinsuppSum]
    rw [← hf, hLeq, map_dfinsuppSum]
    have hfun :
      (fun a (b : p a) =>
          L (DFinsupp.single (a + 1) (⟨T (b : M), hshift a b b.property⟩ : p (a + 1)))) =
        (fun a (b : p a) => T (b : M)) := by
      funext a b
      rw [hL, DFinsupp.lsum_single]
      rfl
    rw [hfun]
  have hg0 : g = 0 := by
    apply hindep.dfinsupp_lsum_injective
    rw [← hL, hLg, hy]; simp
  have hfker : ∀ i, T (f i : M) = 0 := by
    intro i
    have hgi : g (i + 1) = 0 := by
      rw [hg0]; rfl
    have hval : ((g (i + 1) : p (i + 1)) : M) = T (f i : M) := by
      rw [hg, DFinsupp.sum_apply]
      let h₀ : (j : ℕ) → p j → p (i + 1) := fun j fj =>
        (DFinsupp.single (j + 1) (⟨T (fj : M), hshift j fj fj.property⟩ : p (j + 1)) :
            Π₀ n, ↥(p n))
          (i + 1)
      have hpush := map_dfinsuppSum (AddSubmonoidClass.subtype (p (i + 1))) f h₀
      show (AddSubmonoidClass.subtype (p (i + 1))) (f.sum h₀) = T (f i : M)
      rw [hpush]
      rw [show
          (f.sum fun j (fj : p j) => (AddSubmonoidClass.subtype (p (i + 1))) (h₀ j fj)) =
            ∑ j ∈ f.support, (AddSubmonoidClass.subtype (p (i + 1))) (h₀ j (f j))
          from rfl]
      rw [Finset.sum_eq_single i]
      · show ((h₀ i (f i) : p (i + 1)) : M) = T (f i : M)
        simp only [h₀]
        rw [DFinsupp.single_apply, dite_eq_left rfl]
      · intro j _ hji
        show ((h₀ j (f j) : p (i + 1)) : M) = 0
        simp only [h₀]
        rw [DFinsupp.single_apply, dite_eq_right (by omega)]
        simp
      · intro hni
        rw [DFinsupp.mem_support_toFun] at hni
        have hfi0 : f i = 0 := by simpa using hni
        show ((h₀ i (f i) : p (i + 1)) : M) = 0
        simp only [h₀]
        rw [DFinsupp.single_apply, dite_eq_left rfl]
        rw [hfi0]
        simp
    rw [← hval, hgi]; simp
  rw [← hf, hLeq]
  refine Submodule.dfinsuppSum_mem _ f _ ?_
  intro i _
  refine Submodule.mem_iSup_of_mem i ?_
  refine Submodule.mem_inf.mpr ⟨(f i).property, ?_⟩
  rw [LinearMap.mem_ker]
  exact hfker i

/-- Independence of a family is preserved under `comap` along an injective linear map. -/
theorem iSupIndep_comap_of_injective {ι R M N : Type*} [Ring R] [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N] (φ : M →ₗ[R] N) (hφ : Function.Injective φ)
    {p : ι → Submodule R N}
    (h : iSupIndep p) : iSupIndep (fun n => Submodule.comap φ (p n)) := by
  rw [iSupIndep_def] at h ⊢
  intro i
  have hle :
    (⨆ (j : ι) (_ : j ≠ i), Submodule.comap φ (p j)) ≤
      Submodule.comap φ (⨆ (j : ι) (_ : j ≠ i), p j) := by
    refine iSup_le fun j => iSup_le fun hj => ?_
    exact Submodule.comap_mono (le_iSup₂ (f := fun j (_ : j ≠ i) => p j) j hj)
  refine Disjoint.mono_right hle ?_
  rw [Submodule.disjoint_def]
  intro x hx1 hx2
  rw [Submodule.mem_comap] at hx1 hx2
  have hd := h i
  rw [Submodule.disjoint_def] at hd
  have := hd (φ x) hx1 hx2
  exact hφ (by simpa using this)

/-- The `k`-algebra map `S^{(d+1)} → S^{(d)}` sending the last variable to `0` and the
remaining variables to themselves. -/
noncomputable def qmap (k : Type*) [Field k] (d : ℕ) :
    MvPolynomial (Fin (d + 1)) k →ₐ[k] MvPolynomial (Fin d) k :=
  MvPolynomial.aeval (Fin.lastCases (0 : MvPolynomial (Fin d) k) MvPolynomial.X)

/-- Setting the last variable to zero is a left inverse of adjoining it: `qmap` undoes
`rename Fin.castSucc`. -/
theorem qmap_rename_castSucc (k : Type*) [Field k] (d : ℕ) (p : MvPolynomial (Fin d) k) :
    qmap k d (MvPolynomial.rename Fin.castSucc p) = p := by
  rw [qmap, MvPolynomial.aeval_rename]
  rw [show
      (Fin.lastCases (0 : MvPolynomial (Fin d) k) MvPolynomial.X) ∘ Fin.castSucc =
        MvPolynomial.X
      by
      funext i; simp [Fin.lastCases_castSucc]]
  rw [MvPolynomial.aeval_X_left]; rfl

/-- The map setting the last variable to zero is surjective. -/
theorem qmap_surjective (k : Type*) [Field k] (d : ℕ) : Function.Surjective (qmap k d) := fun p =>
  ⟨MvPolynomial.rename Fin.castSucc p, qmap_rename_castSucc k d p⟩

/-- The difference `s - rename(castSucc)(qmap s)` lies in the ideal generated by the last
variable; hence it annihilates anything killed by the last variable. -/
theorem sub_rename_qmap_mem_span_X_last (k : Type*) [Field k] (d : ℕ)
    (s : MvPolynomial (Fin (d + 1)) k) :
    s - (MvPolynomial.rename Fin.castSucc) (qmap k d s) ∈
      Ideal.span {(MvPolynomial.X (Fin.last d) : MvPolynomial (Fin (d + 1)) k)} := by
  induction s using MvPolynomial.induction_on with
  | C
    a =>
    simp only [qmap, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.rename_C,
      sub_self]
    exact Submodule.zero_mem _
  | add p q hp
    hq =>
    have heq :
      (p + q) - (MvPolynomial.rename Fin.castSucc) (qmap k d (p + q)) =
        (p - (MvPolynomial.rename Fin.castSucc) (qmap k d p)) +
          (q - (MvPolynomial.rename Fin.castSucc) (qmap k d q)) := by
      simp only [map_add]; ring
    rw [heq]; exact Ideal.add_mem _ hp hq
  | mul_X p j hp =>
    induction j using Fin.lastCases with
    | last =>
      rw [map_mul]
      have hq0 : qmap k d (MvPolynomial.X (Fin.last d) : MvPolynomial (Fin (d + 1)) k) = 0 := by
        simp [qmap, Fin.lastCases_last]
      rw [hq0, mul_zero, map_zero, sub_zero]
      exact Ideal.mul_mem_left _ p (Ideal.mem_span_singleton_self _)
    | cast i =>
      rw [map_mul]
      have hqc :
        qmap k d (MvPolynomial.X (Fin.castSucc i) : MvPolynomial (Fin (d + 1)) k) =
          MvPolynomial.X i := by
        simp [qmap, Fin.lastCases_castSucc]
      rw [hqc, map_mul, MvPolynomial.rename_X]
      rw [show
          p * MvPolynomial.X (Fin.castSucc i) -
              (MvPolynomial.rename Fin.castSucc) (qmap k d p) * MvPolynomial.X (Fin.castSucc i) =
            (p - (MvPolynomial.rename Fin.castSucc) (qmap k d p)) * MvPolynomial.X (Fin.castSucc i)
          by ring]
      exact Ideal.mul_mem_right _ _ hp

/-- The kernel of multiplication by the last variable on an admissible graded module over
`d + 1` variables is again admissible, over `d` variables, with the expected dimensions. -/
theorem exists_kernel_admissible {d : ℕ} (A : AdmissibleGradedModule k (d + 1)) :
    ∃ Kmod : AdmissibleGradedModule k d,
      ∀ m : ℕ, Kmod.hilb m = (Module.finrank k (LinearMap.ker (mulXLastDeg A m)) : ℤ) := by
  classical
  set ren : MvPolynomial (Fin d) k →ₐ[k] MvPolynomial (Fin (d + 1)) k :=
    MvPolynomial.rename Fin.castSucc with hren
  set lXS : A.M →ₗ[MvPolynomial (Fin (d + 1)) k] A.M :=
    LinearMap.lsmul (MvPolynomial (Fin (d + 1)) k) A.M (MvPolynomial.X (Fin.last d)) with hlXS
  set lX : A.M →ₗ[k] A.M := lXS.restrictScalars k with hlX
  set K : Submodule (MvPolynomial (Fin (d + 1)) k) A.M := LinearMap.ker lXS with hK
  -- instances on ↥K
  let smulS₀ : SMul (MvPolynomial (Fin d) k) K := ⟨fun r x => (ren r) • x⟩
  let moduleS₀ : Module (MvPolynomial (Fin d) k) K := Module.compHom (M := K) ren.toRingHom
  let tower₀ : IsScalarTower k (MvPolynomial (Fin d) k) K := by
    refine ⟨fun c r x => ?_⟩
    show (ren (c • r)) • x = c • ((ren r) • x)
    rw [map_smul, smul_assoc]
  -- grading
  set Kgr : ℕ → Submodule k K := fun m =>
    Submodule.comap ((K.subtype).restrictScalars k) (A.Mgr m) with hKgr
  -- the k-linear subtype embedding ↥K → A.M
  set ι : K →ₗ[k] A.M := (K.subtype).restrictScalars k with hι
  have hι_inj : Function.Injective ι := by
    rw [hι]; exact Subtype.coe_injective
  -- key: lX x = X_last • x and membership in K means X_last • x = 0
  have hlX_apply :
    ∀ x : A.M, lX x = (MvPolynomial.X (Fin.last d) : MvPolynomial (Fin (d + 1)) k) • x := by
    intro x; rfl
  refine
    ⟨{  M := K
        Mgr := Kgr
        iSupIndep := ?_
        iSup_eq := ?_
        finite := ?_
        smul_mem := ?_
        fg := ?_ }, ?_⟩
  · -- iSupIndep
    exact iSupIndep_comap_of_injective ι hι_inj A.iSupIndep
  · -- iSup_eq
    -- shift fact for lX
    have hshiftlX : ∀ (n : ℕ) (x : A.M), x ∈ A.Mgr n → lX x ∈ A.Mgr (n + 1) := by
      intro n x hx
      rw [hlX_apply]
      exact A.smul_mem (Fin.last d) n x hx
    -- range ι = ker lX
    have hrange : LinearMap.range ι = LinearMap.ker lX := by
      rw [hι, LinearMap.range_restrictScalars, Submodule.range_subtype, hlX,
        LinearMap.ker_restrictScalars, hK]
    -- reduce via injectivity of map ι
    apply Submodule.map_injective_of_injective hι_inj
    rw [Submodule.map_iSup, Submodule.map_top]
    have hmc : ∀ n, Submodule.map ι (Kgr n) = LinearMap.ker lX ⊓ A.Mgr n := by
      intro n
      rw [hKgr, Submodule.map_comap_eq, hrange]
    rw [iSup_congr hmc]
    -- ⨆ (ker lX ⊓ A.Mgr n) = range ι = ker lX
    rw [hrange]
    apply le_antisymm
    · exact iSup_le fun n => inf_le_left
    · intro w hw
      have hwker : lX w = 0 := hw
      have hmem := ker_homogeneous A.Mgr lX A.iSupIndep A.iSup_eq hshiftlX w hwker
      have hcongr : (⨆ n, (A.Mgr n ⊓ LinearMap.ker lX)) = ⨆ n, (LinearMap.ker lX ⊓ A.Mgr n) :=
        iSup_congr fun n => inf_comm _ _
      rwa [hcongr] at hmem
  · -- finite
    intro n
    have : Module.Finite k (A.Mgr n) := A.finite n
    -- embed Kgr n into A.Mgr n
    let e : Kgr n →ₗ[k] A.Mgr n :=
      LinearMap.codRestrict (A.Mgr n) (ι ∘ₗ (Kgr n).subtype) fun y => y.property
    have he : Function.Injective e := by
      intro a b hab
      have : ι ((Kgr n).subtype a) = ι ((Kgr n).subtype b) := by
        simpa [e, LinearMap.codRestrict] using congrArg (Subtype.val) hab
      exact Subtype.ext (Subtype.ext (congrArg Subtype.val (hι_inj this)))
    exact Module.Finite.of_injective e he
  · -- smul_mem
    intro i n x hx
    show (MvPolynomial.X i • x) ∈ Submodule.comap ((K.subtype).restrictScalars k) (A.Mgr (n + 1))
    rw [Submodule.mem_comap]
    have hxmem : (x : A.M) ∈ A.Mgr n := hx
    have hcoe1 :
      ((K.subtype).restrictScalars k) ((MvPolynomial.X i : MvPolynomial (Fin d) k) • x) =
        ren (MvPolynomial.X i : MvPolynomial (Fin d) k) • (x : A.M) :=
      rfl
    rw [hcoe1, hren, MvPolynomial.rename_X]
    exact A.smul_mem (Fin.castSucc i) n (x : A.M) hxmem
  · -- fg
    -- K is f.g. over R₁ = S^(d+1) (Noetherian)
    have hR1fin : Module.Finite (MvPolynomial (Fin (d + 1)) k) A.M := A.fg
    have hnoeth : IsNoetherian (MvPolynomial (Fin (d + 1)) k) A.M :=
      isNoetherian_of_isNoetherianRing_of_finite (MvPolynomial (Fin (d + 1)) k) A.M
    have hKfin1 : Module.Finite (MvPolynomial (Fin (d + 1)) k) K :=
      Module.Finite.iff_fg.mpr ((isNoetherian_def.mp hnoeth) K)
    -- key semilinearity: s • v = qmap(s) •_R₀ v for v ∈ K
    have hsurj : RingHomSurjective (qmap k d).toRingHom := ⟨qmap_surjective k d⟩
    have hkey : ∀ (s : MvPolynomial (Fin (d + 1)) k) (x : K), ((qmap k d s) • x : K) = s • x := by
      intro s x
      apply Subtype.ext
      show ren (qmap k d s) • (x : A.M) = s • (x : A.M)
      have hxk : (MvPolynomial.X (Fin.last d) : MvPolynomial (Fin (d + 1)) k) • (x : A.M) = 0 := by
        have hx2 : lXS (x : A.M) = 0 := LinearMap.mem_ker.mp x.property
        rwa [hlXS] at hx2
      have hmem := sub_rename_qmap_mem_span_X_last k d s
      rw [Ideal.mem_span_singleton] at hmem
      obtain ⟨h, hh⟩ := hmem
      have : (s - ren (qmap k d s)) • (x : A.M) = 0 := by
        rw [hren] at *
        rw [hh, mul_comm, mul_smul, hxk, smul_zero]
      rw [sub_smul, sub_eq_zero] at this
      exact this.symm
    -- the qmap-semilinear identity map K → K
    let f : K →ₛₗ[(qmap k d).toRingHom] K :=
      { toFun := id
        map_add' := fun a b => rfl
        map_smul' := fun s x => (hkey s x).symm }
    exact Module.Finite.of_surjective f (fun x => ⟨x, rfl⟩)
  · -- hilb
    intro m
    change
      (Module.finrank k (Kgr m) : ℤ) = (Module.finrank k (LinearMap.ker (mulXLastDeg A m)) : ℤ)
    have hfr : Module.finrank k (Kgr m) = Module.finrank k (LinearMap.ker (mulXLastDeg A m)) := by
      apply LinearEquiv.finrank_eq
      -- build equiv Kgr m ≃ₗ[k] ker (mulXLastDeg A m)
      refine
        LinearEquiv.ofLinearMap (?_ : Kgr m →ₗ[k] LinearMap.ker (mulXLastDeg A m))
          (?_ : LinearMap.ker (mulXLastDeg A m) →ₗ[k] Kgr m) ?_ ?_
      · -- forward
        refine
          LinearMap.codRestrict (LinearMap.ker (mulXLastDeg A m))
            ({  toFun := fun y => ⟨ι ((Kgr m).subtype y), y.property⟩
                map_add' := fun a b => by
                  apply Subtype.ext; rfl
                map_smul' := fun c a => by
                  apply Subtype.ext; rfl } :
              Kgr m →ₗ[k] A.Mgr m) ?_
        intro y
        rw [LinearMap.mem_ker]
        apply Subtype.ext
        change
          (MvPolynomial.X (Fin.last d) : MvPolynomial (Fin (d + 1)) k) •
              (ι ((Kgr m).subtype y) : A.M) =
            0
        have hx2 : lXS (ι ((Kgr m).subtype y) : A.M) = 0 :=
          LinearMap.mem_ker.mp ((Kgr m).subtype y).property
        rwa [hlXS] at hx2
      · -- backward
        refine
          { toFun := fun z => ⟨⟨((z : A.Mgr m) : A.M), ?_⟩, ?_⟩
            map_add' := fun a b => by
              apply Subtype.ext; apply Subtype.ext; rfl
            map_smul' := fun c a => by
              apply Subtype.ext; apply Subtype.ext; rfl }
        · -- ((z:A.Mgr m):A.M) ∈ K
          rw [hK, LinearMap.mem_ker, hlXS]
          exact congrArg (Subtype.val) (LinearMap.mem_ker.mp z.property)
        · -- ∈ Kgr m
          show ι _ ∈ A.Mgr m
          exact (z : A.Mgr m).property
      · -- right inverse
        apply LinearMap.ext; intro z
        apply Subtype.ext; apply Subtype.ext; rfl
      · -- left inverse
        apply LinearMap.ext; intro y
        apply Subtype.ext; apply Subtype.ext; rfl
    rw [hfr]

end Stacks.HilbertFunction.PolynomialQuotient
