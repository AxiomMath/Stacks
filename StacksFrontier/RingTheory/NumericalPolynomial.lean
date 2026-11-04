module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

/-!
# Numerical polynomials

A function `f : ℤ → A` taking values in an abelian group `A` is a *numerical polynomial* if there
exist a natural number `r` and elements `a₀, …, aᵣ ∈ A` such that
`f n = ∑_{i = 0}^r (n choose i) • aᵢ` for all `n ≫ 0`.

## Main definitions

* `IsNumericalPolynomial`: the predicate of being a numerical polynomial.

## Main results

* `numerical_polynomial_functorial`: if `φ : A →+ A'` is a homomorphism of abelian groups and `f`
  is a numerical polynomial, then so is `n ↦ φ (f n)`.
* `main_00JZ`: if the backward difference `n ↦ f n - f (n - 1)` is a numerical polynomial, then so
  is `f`.
-/

@[expose] public section


open Filter

variable {A : Type*} [AddCommGroup A]

/-- A function `f : ℤ → A` (with `A` an additive abelian group) is a
*numerical polynomial* if there exist `r : ℕ` and elements
`a : Fin (r + 1) → A` such that
`f n = ∑_{i = 0}^{r} (n choose i) • a i` holds for all sufficiently large
integers `n`. -/
@[stacks 00JX]
def IsNumericalPolynomial (f : ℤ → A) : Prop :=
  ∃ (r : ℕ) (a : Fin (r + 1) → A), ∀ᶠ n in atTop, f n = ∑ i : Fin (r + 1), Ring.choose n i • a i

/-- Being a numerical polynomial only depends on the values of `f` for `n ≫ 0`. -/
theorem IsNumericalPolynomial.congr {f g : ℤ → A} (hf : IsNumericalPolynomial f)
    (hfg : f =ᶠ[atTop] g) : IsNumericalPolynomial g :=
  let ⟨r, a, h⟩ := hf
  ⟨r, a, hfg.symm.trans h⟩

/-- Every constant function is a numerical polynomial. -/
theorem IsNumericalPolynomial.const (c : A) : IsNumericalPolynomial (fun _ : ℤ => c) :=
  ⟨0, fun _ => c, .of_forall fun _ => by simp [Ring.choose]⟩

/-- The zero function is a numerical polynomial. -/
theorem IsNumericalPolynomial.zero : IsNumericalPolynomial (fun _ : ℤ => (0 : A)) :=
  .const 0

/-- For any tuple of coefficients `a : Fin (r + 1) → A`, the function
`n ↦ ∑_{i=0}^{r} (n choose i) • a i` is itself a numerical polynomial. -/
theorem IsNumericalPolynomial.binomial_sum (r : ℕ) (a : Fin (r + 1) → A) :
    IsNumericalPolynomial fun n : ℤ => ∑ i : Fin (r + 1), Ring.choose n i • a i :=
  ⟨r, a, .of_forall fun _ => rfl⟩

end

/-!
## Functoriality
-/

@[expose] public section

open Filter in
/-- `f : ℤ → A` is a numerical polynomial iff there are a degree bound `r` and coefficients
`a : Fin (r+1) → A` such that `f n = ∑ i, Ring.choose n i • a i` for all sufficiently large
integers `n`. -/
theorem isNumericalPolynomial_iff {A : Type*} [AddCommGroup A] (f : ℤ → A) :
    IsNumericalPolynomial f ↔
      ∃ (r : ℕ) (a : Fin (r + 1) → A),
        ∀ᶠ (n : ℤ) in atTop, f n = ∑ i : Fin (r + 1), Ring.choose n (i : ℕ) • a i :=
  Iff.rfl

/-- Numerical polynomials are functorial: if `φ : A →+ A'` is a homomorphism of abelian groups
and `f : ℤ → A` is a numerical polynomial, then `n ↦ φ (f n)` is a numerical polynomial valued in
`A'`. -/
@[stacks 00JY]
theorem numerical_polynomial_functorial
    {A A' : Type*} [AddCommGroup A] [AddCommGroup A']
    (φ : A →+ A') (f : ℤ → A) (hf : IsNumericalPolynomial f) :
    IsNumericalPolynomial (fun n => φ (f n)) := by
  rw [isNumericalPolynomial_iff] at hf ⊢
  obtain ⟨r, a, hN⟩ := hf
  refine ⟨r, fun i => φ (a i), ?_⟩
  filter_upwards [hN] with n hn
  simp only [hn, map_sum, map_zsmul]

end

/-!
## Functions whose backward difference is a numerical polynomial
-/

@[expose] public section
/-- `f : ℤ → A` satisfies `IsNP'` if there are `m : ℕ` and `c : ℕ → A` with
`f n = ∑_{i<m} (n choose i) • c i` for all sufficiently large `n`. -/
def IsNP' {A : Type*} [AddCommGroup A] (f : ℤ → A) : Prop :=
  ∃ (m : ℕ) (c : ℕ → A), ∀ᶠ n in Filter.atTop,
    f n = ∑ i ∈ Finset.range m, Ring.choose n i • c i

/-- `IsNumericalPolynomial` agrees with its `Finset.range`-based reformulation `IsNP'`. -/
theorem isNP'_iff {A : Type*} [AddCommGroup A] (f : ℤ → A) :
    IsNumericalPolynomial f ↔ IsNP' f := by
  rw [isNumericalPolynomial_iff]
  constructor
  · rintro ⟨r, a, ha⟩
    refine ⟨r + 1, fun i => if h : i < r + 1 then a ⟨i, h⟩ else 0, ?_⟩
    filter_upwards [ha] with n hn
    rw [hn, ← Fin.sum_univ_eq_sum_range
      (fun i => Ring.choose n i • (if h : i < r + 1 then a ⟨i, h⟩ else 0)) (r + 1)]
    exact Finset.sum_congr rfl fun i _ => by simp [i.isLt]
  · rintro ⟨m, c, hc⟩
    refine ⟨m, fun i => if (i : ℕ) < m then c (i : ℕ) else 0, ?_⟩
    filter_upwards [hc] with n hn
    rw [hn, Fin.sum_univ_eq_sum_range
      (fun i => Ring.choose n i • (if i < m then c i else 0)) (m + 1), Finset.sum_range_succ]
    simp only [lt_irrefl, ite_false, smul_zero, add_zero]
    exact Finset.sum_congr rfl fun i hi => by simp [Finset.mem_range.mp hi]

/-- Closure of `IsNP'` under eventual equality. -/
theorem IsNP'.congr_eventuallyEq {A : Type*} [AddCommGroup A] {f g : ℤ → A}
    (h : f =ᶠ[Filter.atTop] g) (hg : IsNP' g) : IsNP' f := by
  obtain ⟨m, c, hc⟩ := hg
  exact ⟨m, c, by filter_upwards [h, hc] with n h1 h2 using h1.trans h2⟩

/-- A constant function is numerical (`IsNP'`). -/
theorem IsNP'.const {A : Type*} [AddCommGroup A] (c : A) :
    IsNP' (fun _ : ℤ => c) :=
  ⟨1, fun _ => c, .of_forall fun _ => by simp⟩

/-- Extend a `range`-sum to a larger `range` by padding the coefficients with
zeros. -/
theorem sum_range_pad {A : Type*} [AddCommGroup A] (n : ℤ) (c : ℕ → A)
    (m M : ℕ) (hm : m ≤ M) :
    ∑ i ∈ Finset.range m, Ring.choose n i • c i
      = ∑ i ∈ Finset.range M, Ring.choose n i • (if i < m then c i else 0) := by
  rw [← Finset.sum_subset (Finset.range_mono hm)]
  · exact Finset.sum_congr rfl fun i hi => by simp [Finset.mem_range.mp hi]
  · intro x _ hx
    simp [Nat.not_lt.mpr (not_lt.mp (Finset.mem_range.not.mp hx))]

/-- Closure of `IsNP'` under pointwise addition. -/
theorem IsNP'.add {A : Type*} [AddCommGroup A] {f g : ℤ → A}
    (hf : IsNP' f) (hg : IsNP' g) : IsNP' (fun n => f n + g n) := by
  obtain ⟨mf, cf, hcf⟩ := hf
  obtain ⟨mg, cg, hcg⟩ := hg
  refine ⟨max mf mg,
    fun i => (if i < mf then cf i else 0) + (if i < mg then cg i else 0), ?_⟩
  filter_upwards [hcf, hcg] with n h1 h2
  rw [h1, h2,
    sum_range_pad n cf mf (max mf mg) (le_max_left mf mg),
    sum_range_pad n cg mg (max mf mg) (le_max_right mf mg),
    ← Finset.sum_add_distrib]
  simp only [smul_add]

/-- Shifting the binomial index by one preserves `IsNP'`: the function
`n ↦ ∑_{i<m} (n choose (i+1)) • c i` is numerical. -/
theorem IsNP'.shift {A : Type*} [AddCommGroup A] (m : ℕ) (c : ℕ → A) :
    IsNP' (fun n => ∑ i ∈ Finset.range m, Ring.choose n (i + 1) • c i) := by
  refine ⟨m + 1, fun j => if j = 0 then 0 else c (j - 1), ?_⟩
  filter_upwards with n
  simp [Finset.sum_range_succ']

/-- The Pascal antidifference identity, summed: the backward difference (in the
upper argument) of `n ↦ ∑_{i<m} (n choose (i+1)) • c i` is
`n ↦ ∑_{i<m} (n choose i) • c i`. -/
theorem sum_pascal_diff {A : Type*} [AddCommGroup A] (n : ℤ) (m : ℕ) (c : ℕ → A) :
    (∑ i ∈ Finset.range m, Ring.choose (n + 1) (i + 1) • c i)
      - (∑ i ∈ Finset.range m, Ring.choose n (i + 1) • c i)
      = ∑ i ∈ Finset.range m, Ring.choose n i • c i := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [Ring.choose_succ_succ n i, add_smul]; abel

/-- If `g n = g (n - 1)` for all `n ≥ N`, then `g n = g (N - 1)` for all `n ≥ N - 1`. -/
theorem eventually_const_of_diff_zero {A : Type*} [AddCommGroup A] (g : ℤ → A)
    (N : ℤ) (h : ∀ n ≥ N, g n = g (n - 1)) :
    ∀ n ≥ N - 1, g n = g (N - 1) := by
  intro n hn
  induction n, hn using Int.leInduction with
  | base => rfl
  | succ k hk ih => rw [← ih, h (k + 1) (by omega), add_sub_cancel_right]

/-- Let `A` be an abelian group and `f : ℤ → A`. If the backward difference
`n ↦ f n - f (n - 1)` is a numerical polynomial, then so is `f`. -/
@[stacks 00JZ]
theorem main_00JZ {A : Type*} [AddCommGroup A] (f : ℤ → A)
    (hdiff : IsNumericalPolynomial (fun n => f n - f (n - 1))) :
    IsNumericalPolynomial f := by
  rw [isNP'_iff] at hdiff ⊢
  obtain ⟨m, c, hc⟩ := hdiff
  rw [Filter.eventually_atTop] at hc
  obtain ⟨N, hN⟩ := hc
  set g : ℤ → A := fun n => f n - ∑ i ∈ Finset.range m, Ring.choose (n + 1) (i + 1) • c i
    with hg
  have hdiffg : ∀ n ≥ N, g n = g (n - 1) := by
    intro n hn
    simp only [hg, sub_add_cancel]
    rw [sub_eq_sub_iff_sub_eq_sub]
    exact (hN n hn).trans (sum_pascal_diff n m c).symm
  have hfeq : ∀ n ≥ N - 1, f n
      = g (N - 1) + ∑ i ∈ Finset.range m, Ring.choose (n + 1) (i + 1) • c i := by
    intro n hn
    have := eventually_const_of_diff_zero g N hdiffg n hn
    simp only [hg] at this ⊢
    rw [← this]
    abel
  refine IsNP'.congr_eventuallyEq (g := fun n => (g (N - 1))
    + ((∑ i ∈ Finset.range m, Ring.choose n i • c i)
      + (∑ i ∈ Finset.range m, Ring.choose n (i + 1) • c i))) ?_ ?_
  · exact Filter.eventually_atTop.2 ⟨N - 1, fun n hn => by
      rw [hfeq n hn, eq_add_of_sub_eq (sum_pascal_diff n m c)]⟩
  · have hbase : IsNP' (fun n => ∑ i ∈ Finset.range m, Ring.choose n i • c i) :=
      ⟨m, c, .of_forall fun _ => rfl⟩
    exact (IsNP'.const _).add (hbase.add (IsNP'.shift m c))

end
