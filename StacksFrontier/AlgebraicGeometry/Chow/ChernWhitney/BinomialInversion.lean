module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.Abel

/-!
# Inverting a binomial transform along a graded endomorphism

Let `G : ℕ → Type*` be a family of abelian groups and `τ i : G i ⟶ G (i + 1)` a family of
additive maps between consecutive members. For a *graded sequence* `e : ∀ j, G j` write

  `B_r(e)_i = ∑_{j ≤ i} binom(r - j, i - j) • τ^{i - j}(e j)  ∈ G i`

for its *binomial transform* at `r`. This file proves that `B` determines its graded sequence
degreewise, and identifies the preimage under the shift of `r`: if the transform of `e` at
`r + 1` agrees with the transform of `e'` at `r` up to degree `r + 1`, then

  `e 0 = e' 0`  and  `e (i + 1) = e' (i + 1) - τ i (e' i)`.

## Why this is here

This is the algebra of [Stacks, Tag 02UH](https://stacks.math.columbia.edu/tag/02UH), the Whitney
relation for a short exact sequence with invertible subsheaf. The source proof twists the
sequence by the inverse of the invertible subsheaf, so that Stacks 02UG makes the Chern classes
of the twisted middle and quotient terms agree, and then reads the twist formula of Stacks 02UD
on both. What comes out is exactly the hypothesis below: two binomial transforms, one at `r + 1`
and one at `r`, that agree. Inverting the transform is the whole remaining content, and it is
pure algebra.

It is stated for a *graded* endomorphism rather than for multiplication by a fixed ring element
because the Chern classes of Stacks 02UH are not available as elements of a ring in this
repository: `Stacks.Chow.nonhomogeneousBivariantGroup` carries no multiplication. They are
available as cap products on Chow groups, which lower the delta-dimension by the degree, and
that is a family of abelian groups with a degree-raising additive endomorphism. The ring case is
a special case, recorded as `Stacks.Chow.descentTower_mulRight`: take `G i = A` constant and
`τ i = (· * t)`, and the transform becomes `∑_{j ≤ i} binom(r - j, i - j) • (e j * t ^ (i - j))`.

## Main definitions

* `Stacks.Chow.descentTower` — the image of `e j` in `G i` under `i - j` applications of `τ`,
  defined by recursion on the *target* degree, so that no transport along `j + (i - j) = i`
  appears.
* `Stacks.Chow.binomialTransform` — the binomial transform `B_r(e)_i`.
* `Stacks.Chow.shiftedDifference` — the sequence `j ↦ e j - τ (e (j - 1))`.

## Main results

* `Stacks.Chow.binomialTransform_shiftedDifference` — the transform of `shiftedDifference τ e`
  at `r + 1` is the transform of `e` at `r`, in degrees up to `r + 1`.
* `Stacks.Chow.eq_of_binomialTransform_eq` — a binomial transform at a fixed `r` determines its
  graded sequence degreewise.
* `Stacks.Chow.eq_shiftedDifference_of_binomialTransform_eq` and
  `Stacks.Chow.eq_sub_of_binomialTransform_eq` — the inversion, in the form Stacks 02UH consumes.

## References

* [Stacks Project, Tag 02UH](https://stacks.math.columbia.edu/tag/02UH)
* [Stacks Project, Tag 02UD](https://stacks.math.columbia.edu/tag/02UD)
* [Stacks Project, Tag 02UG](https://stacks.math.columbia.edu/tag/02UG)
-/

@[expose] public noncomputable section

open Finset

namespace Stacks.Chow

variable {G : ℕ → Type*} [∀ i, AddCommGroup (G i)]

/-! ### The tower of a graded sequence -/

/-- The image of `e j` in `G i` under `i - j` applications of `τ`, for `j ≤ i`, and `0` for
`j > i`.

The recursion is on the *target* degree `i`, with the source degree `j` a parameter, so both
branches of the case split are visibly elements of `G i` and no transport appears. Writing
instead an iterate `G j →+ G (j + (i - j))` would make the type of each summand of a binomial
transform depend on a proof of `j ≤ i`, and the sum could not be formed. -/
def descentTower (τ : ∀ i, G i →+ G (i + 1)) (e : ∀ j, G j) : ∀ i : ℕ, ℕ → G i
  | 0, j => if j = 0 then e 0 else 0
  | i + 1, j => if j = i + 1 then e (i + 1) else τ i (descentTower τ e i j)

/-- On the diagonal the tower is the sequence itself. -/
@[simp]
theorem descentTower_diag (τ : ∀ i, G i →+ G (i + 1)) (e : ∀ j, G j) (i : ℕ) :
    descentTower τ e i i = e i := by
  cases i with
  | zero => simp [descentTower]
  | succ i => simp [descentTower]

/-- Below the diagonal the tower is built by one further application of `τ`. -/
theorem descentTower_succ_of_le (τ : ∀ i, G i →+ G (i + 1)) (e : ∀ j, G j) {i j : ℕ}
    (hj : j ≤ i) :
    descentTower τ e (i + 1) j = τ i (descentTower τ e i j) := by
  have hne : j ≠ i + 1 := by omega
  simp [descentTower, hne]

/-- Two graded sequences that agree in degree `j` have the same tower out of degree `j`. -/
theorem descentTower_congr (τ : ∀ i, G i →+ G (i + 1)) (e e' : ∀ j, G j) (j : ℕ)
    (h : e j = e' j) :
    ∀ i, j ≤ i → descentTower τ e i j = descentTower τ e' i j := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => rw [descentTower_diag, descentTower_diag, h]
  | succ i hi ih => rw [descentTower_succ_of_le τ e hi, descentTower_succ_of_le τ e' hi, ih]

/-! ### The binomial transform and the shifted difference -/

/-- The binomial transform of a graded sequence at `r`, in degree `i`:
`∑_{j ≤ i} binom(r - j, i - j) • τ^{i - j}(e j)`. -/
def binomialTransform (τ : ∀ i, G i →+ G (i + 1)) (r : ℕ) (e : ∀ j, G j) (i : ℕ) : G i :=
  ∑ j ∈ range (i + 1), (r - j).choose (i - j) • descentTower τ e i j

/-- The binomial transform, written out. -/
theorem binomialTransform_eq (τ : ∀ i, G i →+ G (i + 1)) (r : ℕ) (e : ∀ j, G j) (i : ℕ) :
    binomialTransform τ r e i =
      ∑ j ∈ range (i + 1), (r - j).choose (i - j) • descentTower τ e i j :=
  rfl

/-- The sequence `j ↦ e j - τ (e (j - 1))`, with the subtracted term read as zero in degree
zero. -/
def shiftedDifference (τ : ∀ i, G i →+ G (i + 1)) (e : ∀ j, G j) : ∀ j, G j
  | 0 => e 0
  | j + 1 => e (j + 1) - τ j (e j)

/-- The shifted difference in degree zero is the entry `e 0`. -/
@[simp]
theorem shiftedDifference_zero (τ : ∀ i, G i →+ G (i + 1)) (e : ∀ j, G j) :
    shiftedDifference τ e 0 = e 0 :=
  rfl

/-- The shifted difference in degree `j + 1` is the entry `e (j + 1) - τ j (e j)`. -/
@[simp]
theorem shiftedDifference_succ (τ : ∀ i, G i →+ G (i + 1)) (e : ∀ j, G j) (j : ℕ) :
    shiftedDifference τ e (j + 1) = e (j + 1) - τ j (e j) :=
  rfl

/-- The tower of a shifted difference, in positive source degree, is the difference of two
consecutive entries of the tower of the original sequence. -/
theorem descentTower_shiftedDifference_succ (τ : ∀ i, G i →+ G (i + 1)) (e : ∀ j, G j) (j : ℕ) :
    ∀ i, j + 1 ≤ i →
      descentTower τ (shiftedDifference τ e) i (j + 1) =
        descentTower τ e i (j + 1) - descentTower τ e i j := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base =>
      rw [descentTower_diag, descentTower_diag, shiftedDifference_succ,
        descentTower_succ_of_le τ e (le_refl j), descentTower_diag]
  | succ i hi ih =>
      rw [descentTower_succ_of_le τ (shiftedDifference τ e) hi, ih, map_sub,
        descentTower_succ_of_le τ e hi, descentTower_succ_of_le τ e (Nat.le_of_succ_le hi)]

/-- The tower of a shifted difference, in every source degree at most the target degree. -/
theorem descentTower_shiftedDifference (τ : ∀ i, G i →+ G (i + 1)) (e : ∀ j, G j) (i j : ℕ)
    (hj : j ≤ i) :
    descentTower τ (shiftedDifference τ e) i j =
      descentTower τ e i j - (if j = 0 then 0 else descentTower τ e i (j - 1)) := by
  cases j with
  | zero =>
      simp only [↓reduceIte, sub_zero]
      exact descentTower_congr τ (shiftedDifference τ e) e 0 (shiftedDifference_zero τ e) i hj
  | succ j =>
      rw [descentTower_shiftedDifference_succ τ e j i hj]
      simp

/-- The binomial transform in degree `i` is the sum over lower source degrees plus `e i`. -/
private theorem binomialTransform_eq_sum_range_add (τ : ∀ i, G i →+ G (i + 1)) (r : ℕ)
    (e : ∀ j, G j) (i : ℕ) :
    binomialTransform τ r e i =
      ∑ j ∈ range i, (r - j).choose (i - j) • descentTower τ e i j + e i := by
  rw [binomialTransform_eq, Finset.sum_range_succ]
  simp only [Nat.sub_self, Nat.choose_zero_right, one_nsmul, descentTower_diag]

/-- **The shift of the binomial transform.** Passing from `r + 1` to `r` replaces a graded
sequence by its shifted difference, in degrees up to `r + 1`. -/
theorem binomialTransform_shiftedDifference (τ : ∀ i, G i →+ G (i + 1)) (e : ∀ j, G j)
    (r i : ℕ) (hi : i ≤ r + 1) :
    binomialTransform τ (r + 1) (shiftedDifference τ e) i = binomialTransform τ r e i := by
  cases i with
  | zero => simp [binomialTransform_eq]
  | succ i =>
      have hsplit : binomialTransform τ (r + 1) (shiftedDifference τ e) (i + 1) =
          ∑ j ∈ range (i + 1 + 1), ((r + 1 - j).choose (i + 1 - j) •
              descentTower τ e (i + 1) j -
                (r + 1 - j).choose (i + 1 - j) •
                  (if j = 0 then 0 else descentTower τ e (i + 1) (j - 1))) := by
        rw [binomialTransform_eq]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [descentTower_shiftedDifference τ e (i + 1) j
          (Nat.le_of_lt_succ (mem_range.mp hj)), nsmul_sub]
      have hn : (∑ j ∈ range (i + 1 + 1), (r + 1 - j).choose (i + 1 - j) •
            (if j = 0 then 0 else descentTower τ e (i + 1) (j - 1))) =
          ∑ j ∈ range (i + 1), (r - j).choose (i - j) • descentTower τ e (i + 1) j := by
        rw [Finset.sum_range_succ']
        simp only [Nat.add_sub_add_right, Nat.add_eq_zero_iff, one_ne_zero, and_false,
          ↓reduceIte, Nat.add_sub_cancel, smul_zero, add_zero]
      have hc : (∑ j ∈ range (i + 1), (r + 1 - j).choose (i + 1 - j) •
              descentTower τ e (i + 1) j) =
          (∑ j ∈ range (i + 1), (r - j).choose (i + 1 - j) • descentTower τ e (i + 1) j) +
            ∑ j ∈ range (i + 1), (r - j).choose (i - j) • descentTower τ e (i + 1) j := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj' : j ≤ i := Nat.le_of_lt_succ (mem_range.mp hj)
        rw [show r + 1 - j = (r - j) + 1 by omega, show i + 1 - j = (i - j) + 1 by omega,
          Nat.choose_succ_succ', add_nsmul]
        abel
      rw [hsplit, Finset.sum_sub_distrib, hn, binomialTransform_eq_sum_range_add τ r e (i + 1),
        Finset.sum_range_succ]
      simp only [Nat.sub_self, Nat.choose_zero_right, one_nsmul, descentTower_diag]
      rw [hc]
      abel

/-! ### Inverting the transform -/

/-- **A binomial transform determines its graded sequence.** If the transforms of `e` and `e'` at
the same `r` agree in all degrees up to `n`, the two sequences agree in all degrees up to `n`. -/
theorem eq_of_binomialTransform_eq (τ : ∀ i, G i →+ G (i + 1)) (e e' : ∀ j, G j) (r n : ℕ)
    (h : ∀ i ≤ n, binomialTransform τ r e i = binomialTransform τ r e' i) :
    ∀ i ≤ n, e i = e' i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have he := h i hi
    rw [binomialTransform_eq_sum_range_add, binomialTransform_eq_sum_range_add] at he
    have hs : (∑ j ∈ range i, (r - j).choose (i - j) • descentTower τ e i j) =
        ∑ j ∈ range i, (r - j).choose (i - j) • descentTower τ e' i j := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j < i := mem_range.mp hj
      rw [descentTower_congr τ e e' j (ih j hj' ((Nat.le_of_lt hj').trans hi)) i
        (Nat.le_of_lt hj')]
    rw [hs] at he
    exact add_left_cancel he

/-- **The inversion.** If the binomial transform of `e` at `r + 1` agrees with that of `e'` at
`r` in all degrees up to `r + 1`, then `e` is the shifted difference of `e'` in those
degrees. -/
theorem eq_shiftedDifference_of_binomialTransform_eq (τ : ∀ i, G i →+ G (i + 1))
    (e e' : ∀ j, G j) (r : ℕ)
    (h : ∀ i ≤ r + 1, binomialTransform τ (r + 1) e i = binomialTransform τ r e' i) :
    ∀ i ≤ r + 1, e i = shiftedDifference τ e' i := by
  apply eq_of_binomialTransform_eq τ e (shiftedDifference τ e') (r + 1) (r + 1)
  intro i hi
  rw [binomialTransform_shiftedDifference τ e' r i hi]
  exact h i hi

/-- **The inversion, degreewise.** The form Stacks 02UH consumes: in positive degree the
inversion reads `e (i + 1) = e' (i + 1) - τ i (e' i)`. -/
theorem eq_sub_of_binomialTransform_eq (τ : ∀ i, G i →+ G (i + 1)) (e e' : ∀ j, G j) (r i : ℕ)
    (hi : i + 1 ≤ r + 1)
    (h : ∀ m ≤ r + 1, binomialTransform τ (r + 1) e m = binomialTransform τ r e' m) :
    e (i + 1) = e' (i + 1) - τ i (e' i) :=
  eq_shiftedDifference_of_binomialTransform_eq τ e e' r h (i + 1) hi

/-! ### The multiplicative case -/

/-- **Multiplication by a ring element is a graded endomorphism.** With `G i = A` constant and
`τ i = (· * t)`, the tower is multiplication by a power of `t`, so the binomial transform above
is the transform `∑_{j ≤ i} binom(r - j, i - j) • (e j * t ^ (i - j))` of the Stacks 02UH
argument and the inversion above applies to it verbatim. -/
theorem descentTower_mulRight {A : Type*} [Ring A] (t : A) (e : ℕ → A) (i j : ℕ) (hj : j ≤ i) :
    descentTower (fun _ : ℕ => AddMonoidHom.mulRight t) e i j = e j * t ^ (i - j) := by
  induction i, hj using Nat.le_induction with
  | base => simp
  | succ i hi ih =>
      rw [descentTower_succ_of_le _ e hi, ih]
      simp only [AddMonoidHom.mulRight_apply, show i + 1 - j = (i - j) + 1 from by omega,
        pow_succ]
      exact mul_assoc _ _ _

end Stacks.Chow

end
