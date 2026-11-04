module

public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.ChernGrading
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.PowerSumPolynomials
public import StacksCore.Tactic.StacksAttribute

/-!
# Power sums of Chern roots: additivity and the tensor formula

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, Stacks 02QL, let `X` be
locally of finite type over `S` and let `P_p` be the universal power-sum polynomial of
Stacks 0F9B, the rank variable `r` being the degree-zero member of the family. For finite locally
free `𝒪_X`-modules [Stacks, Tag 0F9C](https://stacks.math.columbia.edu/tag/0F9C) and
[Stacks, Tag 0F9D](https://stacks.math.columbia.edu/tag/0F9D) are

  `P_p(ℰ) = P_p(ℰ₁) + P_p(ℰ₂)`  for a short exact sequence `0 → ℰ₁ → ℰ → ℰ₂ → 0`,

  `P_p(ℰ₁ ⊗ ℰ₂) = ∑_{p₁ + p₂ = p} C(p, p₁) · P_{p₁}(ℰ₁) · P_{p₂}(ℰ₂)`,

in `A^p(X)`, whence `ch(ℰ) = ch(ℰ₁) + ch(ℰ₂)` and `ch(ℰ₁ ⊗ ℰ₂) = ch(ℰ₁) ch(ℰ₂)` after dividing
by `p!`. This file supplies the **universal algebra** behind the two tags: in an arbitrary
commutative ring, for Chern classes presented as the elementary symmetric functions of a finite
family of roots. For a short exact sequence the roots of `ℰ` are those of `ℰ₁` together with
those of `ℰ₂`; for a tensor product the roots of `ℰ₁ ⊗ ℰ₂` are the sums `x_i + y_j`.

## Main definitions

* `AlgebraicGeometry.esymmOfRoots`, `AlgebraicGeometry.powerSumOfRoots` — the elementary
  symmetric functions and the power sums of a finite family of roots.
* `AlgebraicGeometry.chernClassEval`, `AlgebraicGeometry.chernEval` — evaluation of the universal
  polynomials of Stacks 0F9B at a family of Chern classes, and at a rank together with such a
  family.
* `AlgebraicGeometry.powerSumChernPolynomial` — the universal power sum `P_p` as a
  weighted-homogeneous element of the Chern grading of Stacks 0F9B, the degree-zero member being
  the rank variable.
* `AlgebraicGeometry.powerSumOfChernClasses` — the class `P_p(c_1, …, c_p)` of a rank and a
  family of Chern classes.
* `AlgebraicGeometry.HasChernRoots` — the splitting principle as a property of a rank and a
  family of Chern classes: they are the number of roots and the elementary symmetric functions of
  the roots.

## Main results

* `AlgebraicGeometry.eval₂Hom_esymm_powerSumPolynomial` — substituting the elementary symmetric
  polynomials in any finite number of variables into `P_p` gives the sum of the `p`-th powers.
  This is the evaluation half of Stacks 0F9B with no lower bound on the number of variables.
* `AlgebraicGeometry.powerSumOfChernClasses_eq_powerSumOfRoots` — Chern classes that split have
  `P_p(c_1, …, c_p) = ∑ x_i^p`, in every degree including zero.
* `AlgebraicGeometry.powerSumOfChernClasses_zero`,
  `AlgebraicGeometry.powerSumOfChernClasses_one` — `P_0` is the rank and `P_1` is `c_1`.
* `AlgebraicGeometry.powerSumOfChernClasses_map` — `P_p` commutes with ring homomorphisms.
* `AlgebraicGeometry.powerSumOfRoots_sumElim`,
  `AlgebraicGeometry.powerSumOfChernClasses_add_of_hasChernRoots` — the universal identity behind
  Stacks 0F9C, for roots and for split Chern classes.
* `AlgebraicGeometry.powerSumOfRoots_tensorRoots`,
  `AlgebraicGeometry.powerSumOfChernClasses_tensor_of_hasChernRoots` — the universal identity
  behind Stacks 0F9D, for roots and for split Chern classes.

## Implementation notes

### What is proved

The source proves both lemmas by choosing `π : P ⟶ X` as in Stacks 02UL, using injectivity of
`π^*` to reduce to modules filtered by invertible modules `ℒ_i`, and then computing with
`x_i = c_1(ℒ_i)`. The statements below are that computation, in every degree `p ≥ 0`, for a rank
and a family of Chern classes in an arbitrary commutative ring, with
`AlgebraicGeometry.HasChernRoots` as the hypothesis that they split: for `ℰ` it is
`∑_{i} x_i^p + ∑_j y_j^p`, and for `ℰ₁ ⊗ ℰ₂` it is the binomial theorem applied to
`(x_i + y_j)^p` followed by Fubini, which is where the binomial coefficient `C(p, p₁)` comes from.

### Why the roots of a tensor product are indexed by a product

`AlgebraicGeometry.HasChernRoots` is quantified over an arbitrary finite index type rather than
over `Fin r`, so the concatenated family of Stacks 0F9C is a sum type and the family
`x_i + y_j` of Stacks 0F9D is a product type; no rank arithmetic and no reindexing along
`Fin (r * s)` is needed. The ranks are recorded separately because `P_0` is the rank variable,
not a power sum, and both identities are proved in degree zero as well: they read
`r = r₁ + r₂` and `r₁ · r₂ = r₁ · r₂` there.

### The evaluation half of Stacks 0F9B without a bound on the number of variables

`AlgebraicGeometry.eq_powerSumPolynomial_iff_eval_esymm` characterizes `P_p` by its values on
the elementary symmetric polynomials in `n ≥ p` variables; the bound is what the uniqueness half
needs. `AlgebraicGeometry.eval₂Hom_esymm_powerSumPolynomial` proves the evaluation half with no
bound, by the same induction along Newton's recurrence, which only ever uses
`MvPolynomial.psum_eq_mul_esymm_sub_sum` in positive degree. The bound would be fatal here: a
module appearing in a short exact sequence has no reason to have rank at least `p`.

## References

* [Stacks Project, Tag 0F9C](https://stacks.math.columbia.edu/tag/0F9C)
* [Stacks Project, Tag 0F9D](https://stacks.math.columbia.edu/tag/0F9D)
* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
* [Stacks Project, Tag 02UL](https://stacks.math.columbia.edu/tag/02UL)
* [Stacks Project, Tag 02UJ](https://stacks.math.columbia.edu/tag/02UJ)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry

open MvPolynomial

variable {A : Type*} [CommRing A] {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ### Symmetric functions of a family of Chern roots -/

/-- The `k`-th elementary symmetric function of a finite family of Chern roots. -/
def esymmOfRoots (x : ι → A) (k : ℕ) : A := (Finset.univ.val.map x).esymm k

/-- The `p`-th power sum of a finite family of Chern roots. -/
def powerSumOfRoots (x : ι → A) (p : ℕ) : A := ∑ i, x i ^ p

/-- The degree-zero power sum of a family of roots is the number of roots, which is the rank of
the module they come from. -/
@[simp]
theorem powerSumOfRoots_zero (x : ι → A) : powerSumOfRoots x 0 = (Fintype.card ι : A) := by
  simp [powerSumOfRoots]

/-- The elementary symmetric functions of a family of roots are the values at the roots of the
elementary symmetric polynomials. -/
theorem aeval_esymm_eq_esymmOfRoots (x : ι → A) (k : ℕ) :
    (aeval x) (esymm ι ℤ k) = esymmOfRoots x k :=
  aeval_esymm_eq_multiset_esymm ι ℤ k x

/-- The values at the roots of the power-sum polynomials are the power sums of the roots. -/
theorem aeval_psum_eq_powerSumOfRoots (x : ι → A) (p : ℕ) :
    (aeval x) (psum ι ℤ p) = powerSumOfRoots x p := by
  simp [psum, powerSumOfRoots]

/-! ### The evaluation half of Stacks 0F9B, in any number of variables -/

/-- **The evaluation half of Stacks 0F9B.** Substituting the elementary symmetric polynomials in
`ι` variables into the universal power-sum polynomial `P_p` gives the sum of the `p`-th powers of
the variables, for every positive `p` and every finite `ι`.

`AlgebraicGeometry.eq_powerSumPolynomial_iff_eval_esymm` has the same identity under the
hypothesis `p ≤ #ι`, which its uniqueness half needs; the induction along Newton's recurrence
does not, `MvPolynomial.psum_eq_mul_esymm_sub_sum` asking only for positive degree. -/
theorem eval₂Hom_esymm_powerSumPolynomial (ι : Type*) [Fintype ι] :
    ∀ p : ℕ, 0 < p →
      eval₂Hom (C : ℤ →+* MvPolynomial ι ℤ) (fun i : ℕ+ => esymm ι ℤ (i : ℕ))
          (powerSumPolynomial p : MvPolynomial ℕ+ ℤ) = psum ι ℤ p := by
  classical
  intro p
  induction p using Nat.case_strong_induction_on with
  | hz => intro hk; omega
  | hi k ih =>
      intro _
      rw [coe_powerSumPolynomial_succ, map_add, map_sum]
      simp only [map_mul, eval₂Hom_C, eval₂Hom_X', map_pow]
      rw [psum_eq_mul_esymm_sub_sum ι ℤ (k + 1) (by omega)]
      have hsum : (∑ a ∈ Finset.antidiagonal (k + 1) with a.1 ∈ Set.Ioo 0 (k + 1),
          (-1 : MvPolynomial ι ℤ) ^ a.1 * esymm ι ℤ a.1 * psum ι ℤ a.2) =
          ∑ j ∈ Finset.range k, (-1 : MvPolynomial ι ℤ) ^ (j + 1) *
            esymm ι ℤ (j + 1) * psum ι ℤ (k - j) := by
        rw [Finset.sum_filter, Finset.Nat.sum_antidiagonal_succ]
        simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Set.mem_Ioo,
          lt_irrefl, false_and, ite_false, zero_add]
        rw [Finset.sum_range_succ]
        simp only [lt_irrefl, and_false, ite_false, add_zero]
        exact Finset.sum_congr rfl fun j hj => by simp [Finset.mem_range.mp hj]
      rw [hsum]
      have hs : (∑ j ∈ Finset.range k,
          C (-1 : ℤ) ^ j * esymm ι ℤ ↑(Nat.succPNat j) *
            (eval₂Hom C fun i : ℕ+ => esymm ι ℤ ↑i) ↑(powerSumPolynomial (k - j))) =
          -(∑ j ∈ Finset.range k, (-1 : MvPolynomial ι ℤ) ^ (j + 1) *
            esymm ι ℤ (j + 1) * psum ι ℤ (k - j)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjk : j < k := Finset.mem_range.mp hj
        rw [ih (k - j) (by omega) (by omega), show (Nat.succPNat j : ℕ) = j + 1 by rfl]
        simp only [map_neg, map_one]
        ring
      rw [hs, show (Nat.succPNat k : ℕ) = k + 1 by rfl]
      simp only [map_neg, map_one, map_add, map_natCast]
      push_cast
      ring

/-! ### Evaluating the universal polynomials at Chern classes -/

/-- Evaluation of the universal polynomials of Stacks 0F9B in the Chern-class variables at a
family of Chern classes. -/
def chernClassEval (c : ℕ+ → A) : MvPolynomial ℕ+ ℤ →+* A := eval₂Hom (Int.castRingHom A) c

/-- Evaluation of the universal Chern polynomial ring at a rank and a family of Chern classes:
the rank variable goes to the rank and the variable `c_i` to the `i`-th Chern class. -/
def chernEval (r : ℕ) (c : ℕ+ → A) : ChernPolynomial →+* A :=
  eval₂Hom (Int.castRingHom A) fun v => v.elim (r : A) c

@[simp]
theorem chernEval_X_none (r : ℕ) (c : ℕ+ → A) :
    chernEval r c (MvPolynomial.X none) = (r : A) := by
  simp [chernEval]

@[simp]
theorem chernEval_X_some (r : ℕ) (c : ℕ+ → A) (i : ℕ+) :
    chernEval r c (MvPolynomial.X (some i)) = c i := by
  simp [chernEval]

/-- Evaluating a polynomial that does not involve the rank variable ignores the rank. -/
theorem chernEval_rename_some (r : ℕ) (c : ℕ+ → A) (Q : MvPolynomial ℕ+ ℤ) :
    chernEval r c (MvPolynomial.rename some Q) = chernClassEval c Q := by
  rw [chernEval, chernClassEval, eval₂Hom_rename]
  rfl

/-- Evaluating `P_p` at the elementary symmetric functions of a family of roots gives the `p`-th
power sum of the roots, for every positive `p`. -/
theorem chernClassEval_powerSumPolynomial (x : ι → A) (p : ℕ) (hp : 0 < p) :
    chernClassEval (fun i : ℕ+ => esymmOfRoots x (i : ℕ))
        (powerSumPolynomial p : MvPolynomial ℕ+ ℤ) = powerSumOfRoots x p := by
  calc chernClassEval (fun i : ℕ+ => esymmOfRoots x (i : ℕ))
        (powerSumPolynomial p : MvPolynomial ℕ+ ℤ)
      = eval₂Hom (((aeval x : MvPolynomial ι ℤ →ₐ[ℤ] A).toRingHom).comp C)
          (fun i : ℕ+ => (aeval x : MvPolynomial ι ℤ →ₐ[ℤ] A) (esymm ι ℤ (i : ℕ)))
          (powerSumPolynomial p : MvPolynomial ℕ+ ℤ) :=
        eval₂Hom_congr (Subsingleton.elim _ _)
          (funext fun i => (aeval_esymm_eq_esymmOfRoots x (i : ℕ)).symm) rfl
    _ = (aeval x : MvPolynomial ι ℤ →ₐ[ℤ] A)
          (eval₂Hom C (fun i : ℕ+ => esymm ι ℤ (i : ℕ))
            (powerSumPolynomial p : MvPolynomial ℕ+ ℤ)) :=
        (map_eval₂Hom _ _ _ _).symm
    _ = (aeval x : MvPolynomial ι ℤ →ₐ[ℤ] A) (psum ι ℤ p) := by
        rw [eval₂Hom_esymm_powerSumPolynomial ι p hp]
    _ = powerSumOfRoots x p := aeval_psum_eq_powerSumOfRoots x p

/-! ### The universal power sums in the Chern grading -/

/-- Renaming the Chern-class variables into the universal Chern polynomial ring preserves
weighted homogeneity: the rank variable, which has weight zero, does not occur. -/
theorem isWeightedHomogeneous_rename_some (p : ℕ) :
    MvPolynomial.IsWeightedHomogeneous chernPolynomialWeight
      (MvPolynomial.rename some (powerSumPolynomial p : MvPolynomial ℕ+ ℤ)) p := by
  intro d hd
  obtain ⟨e, rfl, he⟩ := MvPolynomial.coeff_rename_ne_zero some _ d hd
  have hw := isWeightedHomogeneous_powerSumPolynomial p he
  simp only [Finsupp.weight_apply] at hw ⊢
  rw [Finsupp.sum_mapDomain_index (by simp) (by simp [add_mul])]
  simpa [chernPolynomialWeight] using hw

/-- The universal power sum `P_p` as an element of the degree-`p` piece of the Chern grading of
Stacks 0F9B: the rank variable in degree zero, and the power-sum polynomial in the Chern-class
variables in positive degrees. -/
def powerSumChernPolynomial (p : ℕ) : ChernPolynomial.homogeneousSubmodule p :=
  match p with
  | 0 => ⟨degreeZeroPowerSum, degreeZeroPowerSum_mem_homogeneousSubmodule⟩
  | p + 1 => ⟨MvPolynomial.rename some (powerSumPolynomial (p + 1) : MvPolynomial ℕ+ ℤ),
      isWeightedHomogeneous_rename_some (p + 1)⟩

/-- The degree-zero universal power sum is the rank variable. -/
@[simp]
theorem coe_powerSumChernPolynomial_zero :
    (powerSumChernPolynomial 0 : ChernPolynomial) = degreeZeroPowerSum := rfl

/-- In positive degrees the universal power sum is the power-sum polynomial of Stacks 0F9B in the
Chern-class variables. -/
@[simp]
theorem coe_powerSumChernPolynomial_succ (p : ℕ) :
    (powerSumChernPolynomial (p + 1) : ChernPolynomial) =
      MvPolynomial.rename some (powerSumPolynomial (p + 1) : MvPolynomial ℕ+ ℤ) := rfl

/-- The class `P_p(c_1, …, c_p)` of a rank and a family of Chern classes, the degree-zero member
of the family being the rank itself. -/
def powerSumOfChernClasses (r : ℕ) (c : ℕ+ → A) (p : ℕ) : A :=
  chernEval r c (powerSumChernPolynomial p)

/-- **`P_p` commutes with ring homomorphisms.** A ring homomorphism carries the value of `P_p` at
a rank and a family of Chern classes to its value at the rank and the images. -/
theorem powerSumOfChernClasses_map {B : Type*} [CommRing B] (f : A →+* B) (r : ℕ) (c : ℕ+ → A)
    (p : ℕ) :
    f (powerSumOfChernClasses r c p) = powerSumOfChernClasses r (fun i => f (c i)) p := by
  rw [powerSumOfChernClasses, powerSumOfChernClasses, chernEval, chernEval, map_eval₂Hom]
  refine eval₂Hom_congr (Subsingleton.elim _ _) (funext fun v => ?_) rfl
  cases v with
  | none => simp
  | some i => simp

/-- **`P_0` is the rank.** -/
@[simp]
theorem powerSumOfChernClasses_zero (r : ℕ) (c : ℕ+ → A) :
    powerSumOfChernClasses r c 0 = (r : A) := by
  rw [powerSumOfChernClasses, coe_powerSumChernPolynomial_zero]
  exact chernEval_X_none r c

/-- **`P_1` is the first Chern class.** -/
@[simp]
theorem powerSumOfChernClasses_one (r : ℕ) (c : ℕ+ → A) :
    powerSumOfChernClasses r c 1 = c 1 := by
  rw [powerSumOfChernClasses, coe_powerSumChernPolynomial_succ, chernEval_rename_some,
    chernClassEval]
  simp
  rfl

/-! ### The splitting principle as a hypothesis -/

/-- **The splitting principle, as a property of a rank and a family of Chern classes.** The rank
is the number of roots and the `i`-th Chern class is the `i`-th elementary symmetric function of
the roots. This is what Stacks 02UL provides for the pullback of a finite locally free module
along the morphism it produces. -/
structure HasChernRoots (r : ℕ) (c : ℕ+ → A) (x : ι → A) : Prop where
  /-- The rank is the number of roots. -/
  rank : r = Fintype.card ι
  /-- The `i`-th Chern class is the `i`-th elementary symmetric function of the roots. -/
  chernClass : ∀ i : ℕ+, c i = esymmOfRoots x (i : ℕ)

/-- Chern classes that split have `P_p(c_1, …, c_p) = ∑ x_i^p`, in every degree `p ≥ 0`: in
degree zero both sides are the rank. -/
theorem powerSumOfChernClasses_eq_powerSumOfRoots {r : ℕ} {c : ℕ+ → A} {x : ι → A}
    (h : HasChernRoots r c x) (p : ℕ) :
    powerSumOfChernClasses r c p = powerSumOfRoots x p := by
  have hc : c = fun i : ℕ+ => esymmOfRoots x (i : ℕ) := funext h.chernClass
  cases p with
  | zero => simp [powerSumOfChernClasses, degreeZeroPowerSum, h.rank]
  | succ p =>
      rw [powerSumOfChernClasses, coe_powerSumChernPolynomial_succ, chernEval_rename_some, hc]
      exact chernClassEval_powerSumPolynomial x (p + 1) (Nat.succ_pos p)

/-! ### Stacks 0F9C -/

/-- **The universal algebra behind Stacks 0F9C, for roots.** The power sums of a family of roots
obtained by juxtaposing two families are the sums of their power sums, in every degree `p ≥ 0`;
in degree zero this is the additivity of the rank. -/
theorem powerSumOfRoots_sumElim (x : ι → A) (y : κ → A) (p : ℕ) :
    powerSumOfRoots (Sum.elim x y) p = powerSumOfRoots x p + powerSumOfRoots y p := by
  simp [powerSumOfRoots, Fintype.sum_sum_type]

/-- **The universal algebra behind Stacks 0F9C, for split Chern classes.** Let
`0 → ℰ₁ → ℰ → ℰ₂ → 0` be a short exact sequence of finite locally free modules, and suppose the
ranks and Chern classes of `ℰ₁` and `ℰ₂` split into the roots `x` and `y`, those of `ℰ` into the
juxtaposed family. Then

  `P_p(ℰ) = P_p(ℰ₁) + P_p(ℰ₂)`

for every `p ≥ 0`, whence `ch(ℰ) = ch(ℰ₁) + ch(ℰ₂)` after dividing by `p!`. In degree zero this
is `rank ℰ = rank ℰ₁ + rank ℰ₂`. -/
theorem powerSumOfChernClasses_add_of_hasChernRoots {r r₁ r₂ : ℕ} {c c₁ c₂ : ℕ+ → A}
    {x : ι → A} {y : κ → A} (h : HasChernRoots r c (Sum.elim x y))
    (h₁ : HasChernRoots r₁ c₁ x) (h₂ : HasChernRoots r₂ c₂ y) (p : ℕ) :
    powerSumOfChernClasses r c p =
      powerSumOfChernClasses r₁ c₁ p + powerSumOfChernClasses r₂ c₂ p := by
  rw [powerSumOfChernClasses_eq_powerSumOfRoots h, powerSumOfChernClasses_eq_powerSumOfRoots h₁,
    powerSumOfChernClasses_eq_powerSumOfRoots h₂, powerSumOfRoots_sumElim]

/-! ### Stacks 0F9D -/

/-- **The universal algebra behind Stacks 0F9D, for roots.** The power sums of the family of sums
`x_i + y_j` are the binomial convolution of the power sums of `x` and of `y`, in every degree
`p ≥ 0`; in degree zero this is the multiplicativity of the rank. -/
theorem powerSumOfRoots_tensorRoots (x : ι → A) (y : κ → A) (p : ℕ) :
    powerSumOfRoots (fun ij : ι × κ => x ij.1 + y ij.2) p =
      ∑ q ∈ Finset.antidiagonal p,
        (p.choose q.1 : A) * (powerSumOfRoots x q.1 * powerSumOfRoots y q.2) := by
  have hpow : ∀ (i : ι) (j : κ), (x i + y j) ^ p =
      ∑ k ∈ Finset.range (p + 1), (p.choose k : A) * (x i ^ k * y j ^ (p - k)) := by
    intro i j
    rw [add_pow]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hinner : ∀ i : ι, (∑ j : κ, ∑ k ∈ Finset.range (p + 1),
      (p.choose k : A) * (x i ^ k * y j ^ (p - k))) =
      ∑ k ∈ Finset.range (p + 1), ∑ j : κ, (p.choose k : A) * (x i ^ k * y j ^ (p - k)) :=
    fun _ => Finset.sum_comm
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [powerSumOfRoots, Fintype.sum_prod_type, hpow, hinner]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

/-- **The universal algebra behind Stacks 0F9D, for split Chern classes.** Let `ℰ₁` and `ℰ₂` be
finite locally free modules whose ranks and Chern classes split into the roots `x` and `y`, and
suppose those of `ℰ₁ ⊗ ℰ₂` split into the family of sums `x_i + y_j`. Then

  `P_p(ℰ₁ ⊗ ℰ₂) = ∑_{p₁ + p₂ = p} C(p, p₁) · P_{p₁}(ℰ₁) · P_{p₂}(ℰ₂)`

for every `p ≥ 0`, whence `ch(ℰ₁ ⊗ ℰ₂) = ch(ℰ₁) ch(ℰ₂)` after dividing by `p!`, the binomial
coefficients being exactly what `p! = p₁! p₂! C(p, p₁)` turns into the Cauchy product. In degree
zero this is `rank (ℰ₁ ⊗ ℰ₂) = rank ℰ₁ · rank ℰ₂`. -/
theorem powerSumOfChernClasses_tensor_of_hasChernRoots {r r₁ r₂ : ℕ} {c c₁ c₂ : ℕ+ → A}
    {x : ι → A} {y : κ → A}
    (h : HasChernRoots r c (fun ij : ι × κ => x ij.1 + y ij.2))
    (h₁ : HasChernRoots r₁ c₁ x) (h₂ : HasChernRoots r₂ c₂ y) (p : ℕ) :
    powerSumOfChernClasses r c p =
      ∑ q ∈ Finset.antidiagonal p,
        (p.choose q.1 : A) *
          (powerSumOfChernClasses r₁ c₁ q.1 * powerSumOfChernClasses r₂ c₂ q.2) := by
  rw [powerSumOfChernClasses_eq_powerSumOfRoots h, powerSumOfRoots_tensorRoots]
  exact Finset.sum_congr rfl fun q _ => by
    rw [powerSumOfChernClasses_eq_powerSumOfRoots h₁, powerSumOfChernClasses_eq_powerSumOfRoots h₂]

end AlgebraicGeometry

end
