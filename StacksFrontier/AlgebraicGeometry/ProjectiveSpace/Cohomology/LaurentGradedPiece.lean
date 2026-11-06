module

public import Mathlib.LinearAlgebra.Basis.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwist
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.LaurentCharts
public import StacksFrontier.RingTheory.HomogeneousLocalization.GradedLocalizedModule

/-!
# The monomial basis of the sections of `𝒪(d)` over a standard open of projective space

Let `R` be a commutative ring, let `P = R[T₀, …, Tₙ]` with its grading by total degree, and let
`s` be a finite set of indices. The sections of `𝒪(d)` over the standard open
`D₊(∏_{i ∈ s} Tᵢ)` of `ℙⁿ_R` are the degree-`d` graded piece of the single localization
`P[1/∏_{i ∈ s} Tᵢ]` ([Stacks, Tag 01M6] together with
`AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeZeroLocalization_twistGrading_eq`). This file
proves that this graded piece is **free on the Laurent monomials** `T₀^{e₀} ⋯ Tₙ^{eₙ}` whose
exponents sum to `d` and are nonnegative outside `s`, which is the index set
`Stacks.ProjectiveSpace.Cohomology.laurentMonomials`.

That identification is what makes the monomial model of
`StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.LaurentCharts` and
`...Cohomology.TopCech` — where `Stacks.ProjectiveSpace.Cohomology.twistChart` is *defined* as
the free module on those exponent vectors — a statement about `ℙⁿ_R` rather than a combinatorial
construction. It is needed for the degrees `q = 0` and `q = n` of [Stacks, Tag 01XT], which
unlike the middle degrees are genuinely graded statements.

## Main definitions

* `Stacks.ProjectiveSpace.Cohomology.chartDenom` — the product `∏_{i ∈ s} Tᵢ` of the variables
  inverted on the chart.
* `Stacks.ProjectiveSpace.Cohomology.numExp` — the exponent vector of the numerator of the
  Laurent monomial `e` written over the denominator `(∏_{i ∈ s} Tᵢ) ^ N`.
* `Stacks.ProjectiveSpace.Cohomology.laurentFrac` — the Laurent monomial `e`, as an element of
  the localization.
* `Stacks.ProjectiveSpace.Cohomology.twistSections` — the degree-`d` graded piece of
  `P[1/∏_{i ∈ s} Tᵢ]`, as an `R`-submodule.

## Main results

* `laurentFrac_eq_mk` — **the Laurent monomial over any sufficiently large denominator**: the
  fraction defining `laurentFrac` does not depend on which power of `∏_{i ∈ s} Tᵢ` clears the
  negative exponents.
* `laurentFrac_mem_twistSections` — a degree-`d` Laurent monomial is a degree-`d` section.
* `twistSectionsBasis` — **the monomial basis**: `twistSections R n d s` is free on
  `laurentMonomials n d s`.
* `twistChartEquivTwistSections` — hence `Stacks.ProjectiveSpace.Cohomology.twistChart`, the free
  `R`-module on those exponent vectors, **is** the degree-`d` graded piece of
  `P[1/∏_{i ∈ s} Tᵢ]`.

## Implementation notes

**Why a basis and not just a linear equivalence.** The spanning and independence statements are
the two halves of the computation and are useful separately: spanning is the surjectivity of the
monomial description of a homogeneous fraction, independence is the statement that a vanishing
combination of Laurent monomials has vanishing coefficients. `twistChartEquivTwistSections` is
their packaging, through `Finsupp.supportedEquivFinsupp`.

**The denominator is not fixed.** `laurentMonomials n d s` is infinite as soon as `s` has two
elements (`T₀^k T₁^{-k}` for all `k`), so no single power of `∏_{i ∈ s} Tᵢ` clears all of them;
each Laurent monomial carries its own. `numExp` and `laurentFrac_eq_mk` are the bookkeeping that
makes this harmless: raising the denominator multiplies the numerator by a power of
`∏_{i ∈ s} Tᵢ`, which on monomials is the translation `numExp s e N ↦ numExp s e (N + k)`.

**`R`-linearity.** `Stacks.GradedLocalization.gradedPiece` is an additive subgroup, not a
submodule, because the ring it is naturally a module over is the degree-zero part of the
localization. Over a polynomial ring the coefficients `R` sit inside the degree-zero part
`𝒜 0`, so each graded piece is an `R`-submodule; `twistSections` is that submodule and
`mem_twistSections` identifies its elements with those of the graded piece.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
-/

@[expose] public noncomputable section

open Finsupp MvPolynomial
open AlgebraicGeometry.ProjectiveSpectrum.Proj (integerGrading)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The grading action of a non-negative ring degree on an integer module degree, as in every
file that needs it. -/
local instance instVAddNatIntLaurentGradedPiece : VAdd ℕ ℤ where
  vadd n z := (n : ℤ) + z

namespace Stacks.ProjectiveSpace.Cohomology

variable (R : Type u) [CommRing R] {n : ℕ}

/-! ### The grading of the polynomial ring, extended to `ℤ` -/

variable {R}

/-- The integer-extended grading of a polynomial ring is multiplicative, so the polynomial ring
acts on it: the degree-`i` part times the degree-`j` part lands in the degree-`i + j` part, a
negative degree being read as the zero submodule. -/
instance instGradedSMulIntegerGradingMvPolynomial (R : Type u) [CommRing R] (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (integerGrading (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) where
  smul_mem := by
    intro i j a b ha hb
    change a * b ∈ integerGrading (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      ((i : ℤ) + j)
    rcases le_or_gt 0 j with hj | hj
    · have hb' : b ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R j.toNat := by
        simpa [integerGrading, hj] using hb
      have ht : (0 : ℤ) ≤ (i : ℤ) + j := by omega
      have heq : ((i : ℤ) + j).toNat = i + j.toNat := by omega
      simpa [integerGrading, ht, heq] using SetLike.mul_mem_graded ha hb'
    · have hb0 : b = 0 := by
        have : b ∈ (⊥ : Submodule ℤ (MvPolynomial (Fin (n + 1)) R)) := by
          simpa [integerGrading, not_le.2 hj] using hb
        simpa using this
      simp [hb0]

/-- Membership in the integer-extended grading in a nonnegative degree is homogeneity of that
degree. -/
theorem mem_integerGrading_iff (R : Type u) [CommRing R] (n : ℕ) {j : ℤ} (hj : 0 ≤ j)
    (x : MvPolynomial (Fin (n + 1)) R) :
    x ∈ integerGrading (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) j ↔
      x.IsHomogeneous j.toNat := by
  simp [integerGrading, hj]

/-- In a negative degree the integer-extended grading is zero. -/
theorem eq_zero_of_mem_integerGrading_neg (R : Type u) [CommRing R] (n : ℕ) {j : ℤ} (hj : j < 0)
    {x : MvPolynomial (Fin (n + 1)) R}
    (hx : x ∈ integerGrading (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) j) : x = 0 := by
  have : x ∈ (⊥ : Submodule ℤ (MvPolynomial (Fin (n + 1)) R)) := by
    simpa [integerGrading, not_le.2 hj] using hx
  simpa using this

/-! ### The denominator of a chart and the exponent bookkeeping -/

variable (R)

/-- The product `∏_{i ∈ s} Tᵢ` of the variables inverted on the chart `s`: the standard open of
`ℙⁿ_R` cut out by the chart is `D₊(∏_{i ∈ s} Tᵢ)`. -/
def chartDenom (n : ℕ) (s : Finset (Fin (n + 1))) : MvPolynomial (Fin (n + 1)) R :=
  ∏ i ∈ s, MvPolynomial.X i

/-- The exponent vector of `(∏_{i ∈ s} Tᵢ) ^ N`. -/
def shiftExp (n : ℕ) (s : Finset (Fin (n + 1))) (N : ℕ) : Fin (n + 1) →₀ ℕ :=
  ∑ i ∈ s, Finsupp.single i N

variable {R}

/-- The exponent of `(∏_{i ∈ s} Tᵢ) ^ N` at an index is `N` inside `s` and `0` outside it. -/
@[simp]
theorem shiftExp_apply (n : ℕ) (s : Finset (Fin (n + 1))) (N : ℕ) (j : Fin (n + 1)) :
    shiftExp n s N j = if j ∈ s then N else 0 := by
  classical
  rw [shiftExp, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq' s j fun _ => N]

/-- Multiplying the powers of `∏_{i ∈ s} Tᵢ` adds the exponent vectors. -/
theorem shiftExp_add (n : ℕ) (s : Finset (Fin (n + 1))) (a b : ℕ) :
    shiftExp n s (a + b) = shiftExp n s a + shiftExp n s b := by
  classical
  refine Finsupp.ext fun j => ?_
  simp only [shiftExp_apply, Finsupp.add_apply]
  split <;> simp

/-- `(∏_{i ∈ s} Tᵢ) ^ N` is the monomial with exponent `N` at each `i ∈ s`. -/
theorem chartDenom_pow (n : ℕ) (s : Finset (Fin (n + 1))) (N : ℕ) :
    (chartDenom R n s) ^ N = MvPolynomial.monomial (shiftExp n s N) (1 : R) := by
  classical
  rw [chartDenom, ← Finset.prod_pow, shiftExp]
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, MvPolynomial.X_pow_eq_monomial,
        MvPolynomial.monomial_mul_monomial, one_mul]

/-- The denominator of the chart `s` is homogeneous of degree `#s`. -/
theorem chartDenom_mem_homogeneousSubmodule (n : ℕ) (s : Finset (Fin (n + 1))) :
    chartDenom R n s ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R s.card := by
  have h := SetLike.prod_mem_graded (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (fun _ : Fin (n + 1) => 1) (fun i => MvPolynomial.X i) (F := s)
    fun i _ => (MvPolynomial.mem_homogeneousSubmodule 1 _).2 (MvPolynomial.isHomogeneous_X R i)
  rw [← Finset.card_eq_sum_ones s] at h
  rw [chartDenom]
  exact h

variable (R)

/-- The submonoid element `(∏_{i ∈ s} Tᵢ) ^ N` of the localizing submonoid. -/
abbrev chartPow (n : ℕ) (s : Finset (Fin (n + 1))) (N : ℕ) :
    Submonoid.powers (chartDenom R n s) :=
  ⟨chartDenom R n s ^ N, ⟨N, rfl⟩⟩

variable {R}

/-- The exponent vector of the numerator of the Laurent monomial `e` written over the denominator
`(∏_{i ∈ s} Tᵢ) ^ N`: the exponents inside `s` are raised by `N`, those outside are unchanged,
and a still-negative entry is truncated to zero. For `e` nonnegative outside `s` and `N` large
enough the truncation does not occur, which is `natCast_numExp_apply`. -/
def numExp {n : ℕ} (s : Finset (Fin (n + 1))) (e : Fin (n + 1) → ℤ) (N : ℕ) :
    Fin (n + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (e i + (if i ∈ s then (N : ℤ) else 0)).toNat

/-- The defining formula for the numerator's exponent vector. -/
@[simp]
theorem numExp_apply {n : ℕ} (s : Finset (Fin (n + 1))) (e : Fin (n + 1) → ℤ) (N : ℕ)
    (i : Fin (n + 1)) : numExp s e N i = (e i + (if i ∈ s then (N : ℤ) else 0)).toNat := rfl

/-- The entries of `numExp` without the truncation, for `e` nonnegative outside `s` and `N`
clearing the negative exponents inside `s`. -/
theorem natCast_numExp_apply {n : ℕ} {s : Finset (Fin (n + 1))} {e : Fin (n + 1) → ℤ} {N : ℕ}
    (hout : ∀ i ∉ s, 0 ≤ e i) (hin : ∀ i ∈ s, 0 ≤ e i + N) (i : Fin (n + 1)) :
    ((numExp s e N i : ℕ) : ℤ) = e i + (if i ∈ s then (N : ℤ) else 0) := by
  classical
  rw [numExp_apply, Int.toNat_of_nonneg]
  by_cases hi : i ∈ s
  · simpa [hi] using hin i hi
  · simpa [hi] using hout i hi

/-- Raising the denominator by `k` translates the numerator's exponent vector by the exponent
vector of `(∏_{i ∈ s} Tᵢ) ^ k`. -/
theorem numExp_add {n : ℕ} {s : Finset (Fin (n + 1))} {e : Fin (n + 1) → ℤ} {N : ℕ}
    (hout : ∀ i ∉ s, 0 ≤ e i) (hin : ∀ i ∈ s, 0 ≤ e i + N) (k : ℕ) :
    numExp s e (N + k) = numExp s e N + shiftExp n s k := by
  classical
  refine Finsupp.ext fun i => ?_
  simp only [numExp_apply, Finsupp.add_apply, shiftExp_apply]
  by_cases hi : i ∈ s
  · have h := hin i hi
    simp only [hi, ite_true]
    omega
  · have h := hout i hi
    simp only [hi, ite_false]
    omega

/-- The total degree of the numerator: the Laurent degree raised by `N · #s`. -/
theorem natCast_degree_numExp {n : ℕ} {s : Finset (Fin (n + 1))} {e : Fin (n + 1) → ℤ} {N : ℕ}
    (hout : ∀ i ∉ s, 0 ≤ e i) (hin : ∀ i ∈ s, 0 ≤ e i + N) :
    (((numExp s e N).degree : ℕ) : ℤ) = (∑ i, e i) + N * s.card := by
  classical
  rw [Finsupp.degree_eq_sum, Nat.cast_sum]
  rw [Finset.sum_congr rfl fun i _ => natCast_numExp_apply hout hin i]
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem Finset.univ s fun _ => (N : ℤ)]
  simp [Finset.univ_inter, Finset.sum_const, mul_comm]

/-- A power of `∏_{i ∈ s} Tᵢ` clearing every negative exponent of `e`. -/
def clearDen {n : ℕ} (s : Finset (Fin (n + 1))) (e : Fin (n + 1) → ℤ) : ℕ :=
  s.sup fun i => (-(e i)).toNat

/-- `Stacks.ProjectiveSpace.Cohomology.clearDen` really does clear the negative exponents inside
`s`. -/
theorem le_add_clearDen {n : ℕ} (s : Finset (Fin (n + 1))) (e : Fin (n + 1) → ℤ) :
    ∀ i ∈ s, 0 ≤ e i + clearDen s e := by
  intro i hi
  have h : (-(e i)).toNat ≤ clearDen s e := Finset.le_sup (f := fun i => (-(e i)).toNat) hi
  have h' : -(e i) ≤ ((-(e i)).toNat : ℤ) := Int.self_le_toNat _
  omega

/-! ### Laurent monomials as elements of the localization -/

variable (R)

/-- The Laurent monomial `T₀^{e₀} ⋯ Tₙ^{eₙ}`, as an element of the localization
`R[T₀, …, Tₙ][1/∏_{i ∈ s} Tᵢ]`: the fraction whose numerator is the monomial with the negative
exponents cleared and whose denominator is the power of `∏_{i ∈ s} Tᵢ` that cleared them. -/
def laurentFrac (n : ℕ) (s : Finset (Fin (n + 1))) (e : Fin (n + 1) → ℤ) :
    LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R) :=
  LocalizedModule.mk (MvPolynomial.monomial (numExp s e (clearDen s e)) (1 : R))
    (chartPow R n s (clearDen s e))

variable {R}

/-- Raising the denominator of the fraction representing a Laurent monomial does not change it. -/
theorem mk_monomial_numExp_add {n : ℕ} {s : Finset (Fin (n + 1))} {e : Fin (n + 1) → ℤ} {N : ℕ}
    (hout : ∀ i ∉ s, 0 ≤ e i) (hin : ∀ i ∈ s, 0 ≤ e i + N) (k : ℕ) :
    LocalizedModule.mk (MvPolynomial.monomial (numExp s e N) (1 : R)) (chartPow R n s N) =
      LocalizedModule.mk (MvPolynomial.monomial (numExp s e (N + k)) (1 : R))
        (chartPow R n s (N + k)) := by
  classical
  refine LocalizedModule.mk_eq.2 ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, smul_eq_mul]
  rw [numExp_add hout hin k, chartDenom_pow, chartDenom_pow, MvPolynomial.monomial_mul_monomial,
    MvPolynomial.monomial_mul_monomial]
  congr 1
  rw [shiftExp_add]
  abel_nf

/-- **The Laurent monomial over any sufficiently large denominator.** For `e` nonnegative outside
`s` and any `N` clearing its negative exponents inside `s`, the Laurent monomial `e` is the
fraction with numerator `numExp s e N` over `(∏_{i ∈ s} Tᵢ) ^ N`. -/
theorem laurentFrac_eq_mk {n : ℕ} {s : Finset (Fin (n + 1))} {e : Fin (n + 1) → ℤ} {N : ℕ}
    (hout : ∀ i ∉ s, 0 ≤ e i) (hin : ∀ i ∈ s, 0 ≤ e i + N) :
    laurentFrac R n s e =
      LocalizedModule.mk (MvPolynomial.monomial (numExp s e N) (1 : R)) (chartPow R n s N) := by
  have h₁ := mk_monomial_numExp_add (R := R) hout (le_add_clearDen s e)
    (max N (clearDen s e) - clearDen s e)
  have h₂ := mk_monomial_numExp_add (R := R) hout hin (max N (clearDen s e) - N)
  rw [Nat.add_sub_cancel' (le_max_right N (clearDen s e))] at h₁
  rw [Nat.add_sub_cancel' (le_max_left N (clearDen s e))] at h₂
  rw [laurentFrac, h₁, h₂]

/-- A scalar multiple of a Laurent monomial is the fraction with the monomial of that coefficient
as numerator. -/
private theorem smul_laurentFrac_eq_mk {n : ℕ} {s : Finset (Fin (n + 1))} {e : Fin (n + 1) → ℤ}
    {N : ℕ} (hout : ∀ i ∉ s, 0 ≤ e i) (hin : ∀ i ∈ s, 0 ≤ e i + N) (c : R) :
    c • laurentFrac R n s e =
      LocalizedModule.mk (MvPolynomial.monomial (numExp s e N) c) (chartPow R n s N) := by
  rw [laurentFrac_eq_mk (R := R) hout hin, LocalizedModule.smul'_mk, MvPolynomial.smul_eq_C_mul,
    MvPolynomial.C_mul_monomial, mul_one]

/-! ### The sections of a twist over a chart, as an `R`-submodule -/

variable (R)

/-- The degree-`d` graded piece of `R[T₀, …, Tₙ][1/∏_{i ∈ s} Tᵢ]`, as an `R`-submodule. By
[Stacks, Tag 01M6] and
`AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeZeroLocalization_twistGrading_eq` this is the
module of sections of `𝒪(d)` over the standard open `D₊(∏_{i ∈ s} Tᵢ)` of `ℙⁿ_R`.

`Stacks.GradedLocalization.gradedPiece` is only an additive subgroup; the coefficients `R` lie in
the degree-zero part of the grading, so the piece is in fact an `R`-submodule. -/
def twistSections (n : ℕ) (d : ℤ) (s : Finset (Fin (n + 1))) :
    Submodule R (LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R)) where
  carrier := Stacks.GradedLocalization.gradedPiece
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (integerGrading (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) (chartDenom R n s) d
  add_mem' ha hb := add_mem ha hb
  zero_mem' := zero_mem _
  smul_mem' := by
    intro c y hy
    obtain ⟨N, x, hx, rfl⟩ := (Stacks.GradedLocalization.mem_gradedPiece_iff
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (integerGrading (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
      (chartDenom_mem_homogeneousSubmodule n s) d _).1 hy
    rw [LocalizedModule.smul'_mk]
    refine Stacks.GradedLocalization.mk_mem_gradedPiece _ _
      (chartDenom_mem_homogeneousSubmodule n s) ?_
    rcases le_or_gt 0 (d + N • (s.card : ℤ)) with hj | hj
    · rw [mem_integerGrading_iff R n hj] at hx ⊢
      rw [MvPolynomial.smul_eq_C_mul]
      exact hx.C_mul c
    · rw [eq_zero_of_mem_integerGrading_neg R n hj hx, smul_zero]
      exact zero_mem _

variable {R}

/-- The elements of `Stacks.ProjectiveSpace.Cohomology.twistSections` are those of the graded
piece it is cut out by. -/
@[simp]
theorem mem_twistSections {n : ℕ} {d : ℤ} {s : Finset (Fin (n + 1))}
    {y : LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R)} :
    y ∈ twistSections R n d s ↔
      y ∈ Stacks.GradedLocalization.gradedPiece
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (integerGrading (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
        (chartDenom R n s) d :=
  Iff.rfl

/-- **A degree-`d` Laurent monomial is a degree-`d` section.** Its numerator is homogeneous of
degree `d + N · #s`, which is the degree the fraction over `(∏_{i ∈ s} Tᵢ) ^ N` must have. -/
theorem laurentFrac_mem_twistSections {n : ℕ} {d : ℤ} {s : Finset (Fin (n + 1))}
    {e : Fin (n + 1) → ℤ} (he : e ∈ laurentMonomials n d (↑s : Set (Fin (n + 1)))) :
    laurentFrac R n s e ∈ twistSections R n d s := by
  obtain ⟨hsum, hout⟩ := he
  have hout' : ∀ i ∉ s, 0 ≤ e i := fun i hi => hout i (by simpa using hi)
  have hin := le_add_clearDen s e
  set N := clearDen s e with hN
  rw [laurentFrac_eq_mk (R := R) hout' hin]
  refine Stacks.GradedLocalization.mk_mem_gradedPiece _ _
    (chartDenom_mem_homogeneousSubmodule n s) ?_
  have hdeg : (((numExp s e N).degree : ℕ) : ℤ) = d + N • (s.card : ℤ) := by
    rw [natCast_degree_numExp hout' hin, hsum, nsmul_eq_mul]
  have hnn : (0 : ℤ) ≤ d + N • (s.card : ℤ) := hdeg ▸ Int.natCast_nonneg _
  rw [mem_integerGrading_iff R n hnn]
  exact MvPolynomial.isHomogeneous_monomial 1 (by omega)

/-! ### The monomial basis -/

/-- The numerator exponent determines the Laurent monomial: the exponent vector is recovered by
subtracting `N` inside `s`. -/
theorem numExp_injective {n : ℕ} {s : Finset (Fin (n + 1))} {N : ℕ}
    {e e' : Fin (n + 1) → ℤ} (hout : ∀ i ∉ s, 0 ≤ e i) (hin : ∀ i ∈ s, 0 ≤ e i + N)
    (hout' : ∀ i ∉ s, 0 ≤ e' i) (hin' : ∀ i ∈ s, 0 ≤ e' i + N)
    (h : numExp s e N = numExp s e' N) : e = e' := by
  funext i
  have h₁ := natCast_numExp_apply hout hin i
  have h₂ := natCast_numExp_apply hout' hin' i
  rw [h] at h₁
  omega

/-- **The degree-`d` Laurent monomials span the degree-`d` sections.** A homogeneous fraction
`x / (∏_{i ∈ s} Tᵢ) ^ N` is the sum over the monomials of `x` of their coefficients times the
Laurent monomials obtained by subtracting `N` from the exponents inside `s`. -/
theorem twistSections_le_span_laurentFrac (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (s : Finset (Fin (n + 1))) :
    twistSections R n d s ≤ Submodule.span R
      (Set.range fun e : laurentMonomials n d (↑s : Set (Fin (n + 1))) =>
        laurentFrac R n s e.1) := by
  classical
  intro y hy
  obtain ⟨N, x, hx, rfl⟩ := (Stacks.GradedLocalization.mem_gradedPiece_iff _ _
    (chartDenom_mem_homogeneousSubmodule n s) d _).1 hy
  rcases lt_or_ge (d + N • (s.card : ℤ)) 0 with hj | hj
  · rw [eq_zero_of_mem_integerGrading_neg R n hj hx, LocalizedModule.zero_mk]
    exact zero_mem _
  -- `x` is homogeneous of degree `D = (d + N · #s).toNat`
  rw [mem_integerGrading_iff R n hj] at hx
  set D := (d + N • (s.card : ℤ)).toNat with hD
  have hDcast : (D : ℤ) = d + N * s.card := by
    rw [hD, Int.toNat_of_nonneg hj]; simp
  -- the Laurent exponent vector attached to a numerator monomial
  set g : (Fin (n + 1) →₀ ℕ) → Fin (n + 1) → ℤ :=
    fun m i => (m i : ℤ) - (if i ∈ s then (N : ℤ) else 0) with hg
  have hmem : ∀ m ∈ x.support, g m ∈ laurentMonomials n d (↑s : Set (Fin (n + 1))) := by
    intro m hm
    have hmdeg : m.degree = D := by
      rw [Finsupp.degree_eq_weight_one]
      exact hx (MvPolynomial.mem_support_iff.1 hm)
    refine ⟨?_, fun i hi => ?_⟩
    · have hsum : (∑ i, ((m i : ℕ) : ℤ)) = (D : ℤ) := by
        rw [← Nat.cast_sum, ← Finsupp.degree_eq_sum, hmdeg]
      rw [hg]
      simp only
      rw [Finset.sum_sub_distrib, hsum,
        Finset.sum_ite_mem Finset.univ s fun _ => (N : ℤ)]
      simp only [Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
      rw [hDcast]
      ring
    · have hi' : i ∉ s := by simpa using hi
      simp [hg, hi']
  have hclear : ∀ m ∈ x.support, ∀ i ∈ s, 0 ≤ g m i + N := by
    intro m _ i hi
    have h : g m i = (m i : ℤ) - N := by simp [hg, hi]
    omega
  have hout : ∀ m ∈ x.support, ∀ i ∉ s, 0 ≤ g m i :=
    fun m hm i hi => (hmem m hm).2 i (by simpa using hi)
  have hnum : ∀ m ∈ x.support, numExp s (g m) N = m := by
    intro m hm
    refine Finsupp.ext fun i => ?_
    have h := natCast_numExp_apply (hout m hm) (hclear m hm) i
    by_cases hi : i ∈ s
    · have hgi : g m i = (m i : ℤ) - N := by simp [hg, hi]
      have hif : (if i ∈ s then (N : ℤ) else 0) = (N : ℤ) := by simp [hi]
      rw [hgi, hif] at h
      omega
    · have hgi : g m i = (m i : ℤ) := by simp [hg, hi]
      have hif : (if i ∈ s then (N : ℤ) else 0) = 0 := by simp [hi]
      rw [hgi, hif] at h
      omega
  -- expand `x` as a sum of monomials
  have hxsum : LocalizedModule.mk x (chartPow R n s N) =
      ∑ m ∈ x.support, x.coeff m • laurentFrac R n s (g m) := by
    conv_lhs => rw [MvPolynomial.as_sum x]
    rw [← LocalizedModule.sum_mk]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [smul_laurentFrac_eq_mk (hout m hm) (hclear m hm), hnum m hm]
  rw [hxsum]
  refine Submodule.sum_mem _ fun m hm => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨⟨g m, hmem m hm⟩, rfl⟩

/-- **The degree-`d` Laurent monomials are linearly independent.** Over a common denominator the
numerators are distinct monomials, and multiplying by the power of `∏_{i ∈ s} Tᵢ` witnessing a
vanishing in the localization keeps them distinct. -/
theorem linearIndependent_laurentFrac (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (s : Finset (Fin (n + 1))) :
    LinearIndependent R fun e : laurentMonomials n d (↑s : Set (Fin (n + 1))) =>
      laurentFrac R n s e.1 := by
  classical
  rw [linearIndependent_iff']
  intro t c hsum e₀ he₀
  set N := t.sup fun e => clearDen s e.1 with hN
  have hin : ∀ e ∈ t, ∀ i ∈ s, 0 ≤ (e : Fin (n + 1) → ℤ) i + N := by
    intro e he i hi
    have h₁ := le_add_clearDen s (e : Fin (n + 1) → ℤ) i hi
    have h₂ : clearDen s (e : Fin (n + 1) → ℤ) ≤ N :=
      Finset.le_sup (f := fun e : laurentMonomials n d (↑s : Set (Fin (n + 1))) =>
        clearDen s e.1) he
    omega
  have hout : ∀ e ∈ t, ∀ i ∉ s, 0 ≤ (e : Fin (n + 1) → ℤ) i :=
    fun e _ i hi => e.2.2 i (by simpa using hi)
  -- the combination, over the common denominator `(∏ i ∈ s, Tᵢ) ^ N`
  have hcomb : LocalizedModule.mk
      (∑ e ∈ t, MvPolynomial.monomial (numExp s (e : Fin (n + 1) → ℤ) N) (c e))
      (chartPow R n s N) = 0 := by
    rw [← LocalizedModule.sum_mk, ← hsum]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [smul_laurentFrac_eq_mk (hout e he) (hin e he)]
  obtain ⟨k, hk⟩ := LocalizedModule.exists_pow_smul_eq_zero_of_mk_eq_zero hcomb
  -- multiply by `(∏ i ∈ s, Tᵢ) ^ k` and read off the coefficient of `e₀`'s monomial
  have hk' : (∑ e ∈ t, MvPolynomial.monomial
      (numExp s (e : Fin (n + 1) → ℤ) N + shiftExp n s k) (c e)) = 0 := by
    have hmul : (∑ e ∈ t, MvPolynomial.monomial
        (numExp s (e : Fin (n + 1) → ℤ) N + shiftExp n s k) (c e)) =
        (chartDenom R n s ^ k) • ∑ e ∈ t, MvPolynomial.monomial
          (numExp s (e : Fin (n + 1) → ℤ) N) (c e) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun e he => ?_
      rw [smul_eq_mul, chartDenom_pow, MvPolynomial.monomial_mul_monomial, one_mul,
        add_comm (shiftExp n s k) (numExp s (e : Fin (n + 1) → ℤ) N)]
    rw [hmul, hk]
  have hsingle : ∀ e ∈ t, e ≠ e₀ →
      (MvPolynomial.monomial (numExp s (e : Fin (n + 1) → ℤ) N + shiftExp n s k) (c e)).coeff
        (numExp s (e₀ : Fin (n + 1) → ℤ) N + shiftExp n s k) = 0 := by
    intro e he hne
    have hne' : ¬ (numExp s (e : Fin (n + 1) → ℤ) N + shiftExp n s k =
        numExp s (e₀ : Fin (n + 1) → ℤ) N + shiftExp n s k) := fun hEq =>
      hne (Subtype.ext (numExp_injective (hout e he) (hin e he) (hout e₀ he₀) (hin e₀ he₀)
        (add_right_cancel hEq)))
    rw [MvPolynomial.coeff_monomial, ite_eq_right hne']
  have hcoeff := congrArg (fun p : MvPolynomial (Fin (n + 1)) R => p.coeff
    (numExp s (e₀ : Fin (n + 1) → ℤ) N + shiftExp n s k)) hk'
  rw [MvPolynomial.coeff_sum, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply,
    Finset.sum_eq_single_of_mem e₀ he₀ hsingle] at hcoeff
  simpa using hcoeff

/-- **The monomial basis of the sections of `𝒪(d)` over a standard open of `ℙⁿ_R`.** The
degree-`d` graded piece of `R[T₀, …, Tₙ][1/∏_{i ∈ s} Tᵢ]` is free on the Laurent monomials of
total degree `d` that are nonnegative outside `s`. -/
def twistSectionsBasis (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (s : Finset (Fin (n + 1))) :
    Module.Basis (laurentMonomials n d (↑s : Set (Fin (n + 1)))) R (twistSections R n d s) :=
  Module.Basis.mk
    (v := fun e => ⟨laurentFrac R n s e.1, laurentFrac_mem_twistSections e.2⟩)
    ((linearIndependent_laurentFrac R n d s).of_comp (twistSections R n d s).subtype)
    (by
      have hgen : ∀ z ∈ Set.range fun e : laurentMonomials n d (↑s : Set (Fin (n + 1))) =>
          laurentFrac R n s e.1, z ∈ twistSections R n d s := by
        rintro z ⟨e, rfl⟩
        exact laurentFrac_mem_twistSections e.2
      have key : Submodule.map (twistSections R n d s).subtype
          (Submodule.span R (Set.range
            fun e : laurentMonomials n d (↑s : Set (Fin (n + 1))) =>
              (⟨laurentFrac R n s e.1,
                laurentFrac_mem_twistSections e.2⟩ : twistSections R n d s))) =
          twistSections R n d s := by
        rw [Submodule.map_span, ← Set.range_comp]
        exact le_antisymm (Submodule.span_le.2 hgen) (twistSections_le_span_laurentFrac R n d s)
      have htop : Submodule.map (twistSections R n d s).subtype
          (Submodule.span R (Set.range
            fun e : laurentMonomials n d (↑s : Set (Fin (n + 1))) =>
              (⟨laurentFrac R n s e.1,
                laurentFrac_mem_twistSections e.2⟩ : twistSections R n d s))) =
          Submodule.map (twistSections R n d s).subtype ⊤ := by
        rw [key, Submodule.map_subtype_top]
      rw [Submodule.map_injective_of_injective
        (twistSections R n d s).injective_subtype htop])

/-- **The monomial chart is the module of sections.** The free `R`-module
`Stacks.ProjectiveSpace.Cohomology.twistChart` on the degree-`d` Laurent monomials that are
nonnegative outside `s` is the degree-`d` graded piece of `R[T₀, …, Tₙ][1/∏_{i ∈ s} Tᵢ]` — by
[Stacks, Tag 01M6] the module of sections of `𝒪(d)` over the standard open
`D₊(∏_{i ∈ s} Tᵢ)` of `ℙⁿ_R`. -/
def twistChartEquivTwistSections (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (s : Finset (Fin (n + 1))) :
    twistChart R n d (↑s : Set (Fin (n + 1))) ≃ₗ[R] twistSections R n d s :=
  (Finsupp.supportedEquivFinsupp (laurentMonomials n d (↑s : Set (Fin (n + 1))))).trans
    (twistSectionsBasis R n d s).repr.symm

end Stacks.ProjectiveSpace.Cohomology

end
