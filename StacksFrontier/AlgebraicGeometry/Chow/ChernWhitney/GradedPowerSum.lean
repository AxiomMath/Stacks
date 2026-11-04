module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.NewtonPowerSum
public import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.GradedCapRing

/-!
# Power sums in the ring of graded cap families

Let `G : ℤ → Type*` be a family of abelian groups, for instance the Chow groups `A_k(X)` of a
scheme, and let `a` be a graded cap family on `G`
(`StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.GradedCapRing`) whose index-`0` component is
the identity — the shape of a total Chern class `c(ℰ) = 1 + c₁(ℰ) + c₂(ℰ) + ⋯`. This file
constructs the *power sums* of `a`, the classes `P_p` of
[Stacks, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B), and proves the one property of
them that the splitting principle needs: they are **additive** on a product of two total classes,
as soon as the power sums of the first factor commute with the second.

## Newton's identities as one equation

Write `D` for the derivation `Stacks.Chow.gradedDeriv` which multiplies the index-`m` component
by `m`; it is the operator `t·d/dt` on the generating series `∑_m a_m t^m`, and it satisfies the
Leibniz rule for the convolution (`Stacks.Chow.gradedDeriv_mul`). The *logarithmic derivative*
`ν(a) = Stacks.Chow.logDerivFamily a` is defined by, and is the unique solution of,

  `a · ν(a) = D(a)`,

which is exactly Newton's recurrence: the index-`m` component of the left-hand side is
`∑_{i + j = m} a_i ∘ ν_j`, so

  `ν_m = m · a_m - ∑_{j < m} a_{m - j} ∘ ν_j`,

and `P_p = (-1)^{p-1} ν_p` is then the recurrence
`P_p = ∑_{i=1}^{p-1} (-1)^{i-1} a_i P_{p-i} + (-1)^{p-1} p a_p` which defines
`AlgebraicGeometry.powerSumPolynomial`, the universal polynomial of Stacks 0F9B. In the classical
language `ν(a)` is the series `∑_{p ≥ 1} (-1)^{p-1} P_p t^p` and the displayed equation is the
derivative of `log(1 + c₁ + c₂ + ⋯)` — the second characterization of `P_p` in Stacks 0F9B.
Unwinding the recurrence in low degrees gives `P₁ = c₁` (`Stacks.Chow.powerSumFamily_one`) and
`P₂ = c₁² - 2c₂`, the first entries of the list displayed in Stacks 0F9B. Writing the recurrence
as one equation in the ring, rather than degree by degree, is what makes additivity a two-line
computation.

## The canonical `P_p`, and what `powerSumFamily` is

`AlgebraicGeometry.newtonPowerSum` is **the** `P_p` of this development: Newton's recurrence of
Stacks 0F9B read in an arbitrary ring, carrying the faithfulness certificate
`AlgebraicGeometry.newtonPowerSum_eq_powerSumOfChernClasses` that over a commutative ring it is
the evaluation `AlgebraicGeometry.powerSumOfChernClasses` of the universal polynomial. Since
`Stacks.Chow.GradedCapFamily G` is a ring (`Stacks.Chow.instRingGradedCapFamily`), that
recurrence applies here verbatim, and `Stacks.Chow.powerSumFamily` is not a second notion but
the **same one spelled through the logarithmic derivative**: the two agree in every degree,

  `P_p(a) = newtonPowerSum 0 (fun i ↦ a_i) p`,

which is `Stacks.Chow.powerSumFamily_eq_newtonPowerSum`, for `a` with identity index-`0`
component and the family of Chern classes read off as the homogeneous components `a_i` of `a`.
The degree-zero term of the recurrence — the rank variable `r` of Stacks 0F9B — is `0` here,
which is the convention `P₀ = 0` of `AlgebraicGeometry.powerSumPolynomial` and of
`Stacks.Chow.powerSumFamily_zero`; no hypothesis `p ≥ 1` is needed. The spelling is kept because
it is the one in which additivity is two lines: it is a single equation in the ring, not a
recurrence to be unwound.

## Additivity

For `a` and `b` with identity index-`0` components, the Leibniz rule gives

  `(a b) · (ν(a) + ν(b)) = a (ν(a) b) + a (b ν(b)) = (D a) b + a (D b) = D(a b)`

provided `ν(a)` commutes with `b`, the one place commutativity enters; since `a b` is a unit,
uniqueness then gives `ν(a b) = ν(a) + ν(b)`
(`Stacks.Chow.logDerivFamily_mul_of_commute`). For the total Chern classes of a short exact
sequence `c(ℰ) = c(ℰ₁) c(ℰ₂)` is the Whitney sum formula, Stacks 02UI, and the conclusion is
`P_p(ℰ) = P_p(ℰ₁) + P_p(ℰ₂)`, which is
[Stacks, Tag 0F9C](https://stacks.math.columbia.edu/tag/0F9C).

## Main definitions

* `Stacks.Chow.gradedDeriv` — the derivation `a_m ↦ m · a_m`.
* `Stacks.Chow.logDerivFamily` — the logarithmic derivative `ν(a)`.
* `Stacks.Chow.powerSumFamily` — the power sum `P_p(a) = (-1)^{p-1} ν(a)_p`, homogeneous of
  index `p`; the `AlgebraicGeometry.newtonPowerSum` of the homogeneous components of `a`, spelled
  through the logarithmic derivative.

## Main results

* `Stacks.Chow.gradedDeriv_mul` — the Leibniz rule.
* `Stacks.Chow.mul_logDerivFamily` — `a · ν(a) = D(a)`: **Newton's identities**.
* `Stacks.Chow.logDerivFamily_eq_of_mul_eq` — uniqueness of the solution.
* `Stacks.Chow.logDerivFamily_mul_of_commute`, `Stacks.Chow.powerSumFamily_mul_of_commute` —
  additivity of `ν` and of the power sums on a product.
* `Stacks.Chow.commute_logDerivFamily` — `ν(a)` commutes with whatever `a` and `D(a)` commute
  with.
* `Stacks.Chow.powerSumFamily_one` — `P₁ = c₁`.
* `Stacks.Chow.powerSumFamily_eq_newtonPowerSum` — the power sums are Newton's recurrence of
  Stacks 0F9B, `AlgebraicGeometry.newtonPowerSum`, at the homogeneous components of `a` and with
  degree-zero term `0`. This is what makes `Stacks.Chow.powerSumFamily` a spelling of the
  canonical `P_p` and not a second definition of it.
* `Stacks.Chow.homComponent_mul` — the homogeneous components of a product, as a convolution.
* `Stacks.Chow.commute_of_commute_homComponent`,
  `Stacks.Chow.commute_logDerivFamily_of_commute_homComponent` — two families commute, and the
  logarithmic derivative of one commutes with the other, as soon as their homogeneous components
  commute. For Chern classes the hypothesis is the displayed identity of Stacks 02UA.

## References

* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
* [Stacks Project, Tag 0F9C](https://stacks.math.columbia.edu/tag/0F9C)
* [Stacks Project, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI)
-/

@[expose] public noncomputable section

open Finset

namespace Stacks.Chow

universe v

variable {G : ℤ → Type v} [∀ k, AddCommGroup (G k)]

/-! ### Components of sums and multiples -/

/-- The components of a sum of graded cap families. -/
theorem gradedCap_add_apply (a b : GradedCapFamily G) (k : ℤ) (m : ℕ) (x : G k) :
    (a + b) k m x = a k m x + b k m x := by simp

/-- The components of a difference of graded cap families. -/
theorem gradedCap_sub_apply (a b : GradedCapFamily G) (k : ℤ) (m : ℕ) (x : G k) :
    (a - b) k m x = a k m x - b k m x := by simp

/-- The components of a natural multiple of a graded cap family. -/
theorem gradedCap_nsmul_apply (n : ℕ) (a : GradedCapFamily G) (k : ℤ) (m : ℕ) (x : G k) :
    (n • a) k m x = n • a k m x := by simp

/-- The components of an integer multiple of a graded cap family. -/
theorem gradedCap_zsmul_apply (n : ℤ) (a : GradedCapFamily G) (k : ℤ) (m : ℕ) (x : G k) :
    (n • a) k m x = n • a k m x := by simp

/-- An integer multiple of a homogeneous family is homogeneous. -/
theorem isHomogeneous_zsmul {a : GradedCapFamily G} {i : ℕ} (ha : a.IsHomogeneous i) (n : ℤ) :
    (n • a).IsHomogeneous i :=
  ha.zsmul n

/-- A natural multiple of a homogeneous family is homogeneous. -/
theorem isHomogeneous_nsmul {a : GradedCapFamily G} {i : ℕ} (ha : a.IsHomogeneous i) (n : ℕ) :
    (n • a).IsHomogeneous i := by
  rw [← natCast_zsmul]
  exact ha.zsmul n

/-- Two families homogeneous of the same index are equal if their index-`i` components agree. -/
private theorem eq_of_isHomogeneous_of_apply_eq {a b : GradedCapFamily G} {i : ℕ}
    (ha : a.IsHomogeneous i) (hb : b.IsHomogeneous i) (h : ∀ (k : ℤ) (x : G k), a k i x = b k i x) :
    a = b := by
  funext k j
  rcases eq_or_ne j i with rfl | hj
  · exact AddMonoidHom.ext (h k)
  · rw [ha k j hj, hb k j hj]

/-! ### The index derivation -/

/-- The derivation of the ring of graded cap families which multiplies the index-`m` component
by `m`. On generating series `∑_m a_m t^m` it is `t · d/dt`. -/
def gradedDeriv (a : GradedCapFamily G) : GradedCapFamily G := fun k m => m • a k m

/-- The index-`m` component of `gradedDeriv a` is `m` times the index-`m` component of `a`. -/
theorem gradedDeriv_apply (a : GradedCapFamily G) (k : ℤ) (m : ℕ) (x : G k) :
    gradedDeriv a k m x = m • a k m x := by
  simp [gradedDeriv]

/-- The derivation kills the unit. -/
theorem gradedDeriv_one : gradedDeriv (1 : GradedCapFamily G) = 0 := by
  funext k m
  refine AddMonoidHom.ext fun x => ?_
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp [gradedDeriv_apply]
  · rw [gradedDeriv_apply, gradedCap_one_of_ne (by omega)]
    simp

/-- The derivation is additive. -/
theorem gradedDeriv_add (a b : GradedCapFamily G) :
    gradedDeriv (a + b) = gradedDeriv a + gradedDeriv b := by
  funext k m
  refine AddMonoidHom.ext fun x => ?_
  rw [gradedDeriv_apply, gradedCap_add_apply, gradedCap_add_apply, gradedDeriv_apply,
    gradedDeriv_apply, smul_add]

/-- On a homogeneous element of index `i` the derivation is multiplication by `i`. -/
theorem gradedDeriv_of_isHomogeneous {a : GradedCapFamily G} {i : ℕ}
    (ha : a.IsHomogeneous i) : gradedDeriv a = i • a := by
  funext k m
  refine AddMonoidHom.ext fun x => ?_
  rcases eq_or_ne m i with hm | hm
  · subst hm
    rw [gradedDeriv_apply, gradedCap_nsmul_apply]
  · rw [gradedDeriv_apply, gradedCap_nsmul_apply, ha k m hm]
    simp

/-- **The Leibniz rule.** -/
theorem gradedDeriv_mul (a b : GradedCapFamily G) :
    gradedDeriv (a * b) = gradedDeriv a * b + a * gradedDeriv b := by
  funext k m
  refine AddMonoidHom.ext fun x => ?_
  rw [gradedDeriv_apply, gradedCap_mul_apply, gradedCap_add_apply, gradedCap_mul_apply,
    gradedCap_mul_apply, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [convolveTerm_of_le _ _ _ hjm, convolveTerm_of_le _ _ _ hjm, convolveTerm_of_le _ _ _ hjm]
  simp only [capTo_def, gradedDeriv_apply, map_nsmul]
  rw [← add_nsmul]
  congr 1
  omega

/-- The homogeneous components of the derivation. -/
theorem homComponent_gradedDeriv (a : GradedCapFamily G) (i : ℕ) :
    homComponent i (gradedDeriv a) = i • homComponent i a := by
  funext k j
  refine AddMonoidHom.ext fun x => ?_
  rcases eq_or_ne j i with hj | hj
  · subst hj
    rw [homComponent_apply_self, gradedDeriv_apply, gradedCap_nsmul_apply,
      homComponent_apply_self]
  · rw [homComponent_apply_of_ne hj, gradedCap_nsmul_apply, homComponent_apply_of_ne hj]
    simp

/-! ### The logarithmic derivative -/

/-- The components of the logarithmic derivative of `a`, by recursion on the index:
`ν_m = m · a_m - ∑_{j < m} a_{m - j} ∘ ν_j`. This is Newton's recurrence. -/
def logDerivFamilyAux (a : GradedCapFamily G) (k : ℤ) (m : ℕ) : G k →+ G (k - (m : ℤ)) :=
  gradedDeriv a k m -
    ∑ j : Fin m, (gradedDegreeCast G
        (show k - ((j : ℕ) : ℤ) - ((m - (j : ℕ) : ℕ) : ℤ) = k - (m : ℤ) by
          have := j.isLt; omega)).toAddMonoidHom.comp
      ((a (k - ((j : ℕ) : ℤ)) (m - j)).comp (logDerivFamilyAux a k j))
termination_by m
decreasing_by exact j.isLt

/-- **The logarithmic derivative** `ν(a)` of a graded cap family: the solution of
`a · ν(a) = D(a)`, unique when the index-`0` component of `a` is the identity. Its signed
components are the power sums of Stacks 0F9B. -/
def logDerivFamily (a : GradedCapFamily G) : GradedCapFamily G := logDerivFamilyAux a

/-- The defining recursion of `Stacks.Chow.logDerivFamily`. -/
theorem logDerivFamily_apply (a : GradedCapFamily G) (k : ℤ) (m : ℕ) :
    logDerivFamily a k m = gradedDeriv a k m -
      ∑ j : Fin m, (gradedDegreeCast G
          (show k - ((j : ℕ) : ℤ) - ((m - (j : ℕ) : ℕ) : ℤ) = k - (m : ℤ) by
            have := j.isLt; omega)).toAddMonoidHom.comp
        ((a (k - ((j : ℕ) : ℤ)) (m - j)).comp (logDerivFamily a k j)) := by
  rw [logDerivFamily, logDerivFamilyAux]

/-- **Newton's recurrence**, evaluated: `ν_m(x) = m · a_m(x) - ∑_{j < m} a_{m-j}(ν_j(x))`. -/
theorem logDerivFamily_apply_apply (a : GradedCapFamily G) (k : ℤ) (m : ℕ) (x : G k) :
    logDerivFamily a k m x = m • a k m x -
      ∑ j : Fin m, capTo a (m - j)
        (show k - ((j : ℕ) : ℤ) - ((m - (j : ℕ) : ℕ) : ℤ) = k - (m : ℤ) by
          have := j.isLt; omega) (logDerivFamily a k j x) := by
  rw [logDerivFamily_apply, AddMonoidHom.sub_apply, AddMonoidHom.finsetSum_apply,
    gradedDeriv_apply]
  rfl

/-- The index-`0` component of the logarithmic derivative vanishes. -/
theorem logDerivFamily_zero (a : GradedCapFamily G) (k : ℤ) : logDerivFamily a k 0 = 0 := by
  refine AddMonoidHom.ext fun x => ?_
  rw [logDerivFamily_apply_apply]
  simp

/-- The index-`1` component of the logarithmic derivative is the index-`1` component of `a`. -/
theorem logDerivFamily_one_apply (a : GradedCapFamily G) (k : ℤ) (x : G k) :
    logDerivFamily a k 1 x = a k 1 x := by
  rw [logDerivFamily_apply]
  simp only [AddMonoidHom.sub_apply, AddMonoidHom.finsetSum_apply, gradedDeriv_apply]
  simp [logDerivFamily_zero]

/-- **Newton's identities.** If the index-`0` component of `a` is the identity then the
logarithmic derivative solves `a · ν(a) = D(a)`; in components,
`∑_{i + j = m} a_i ∘ ν_j = m · a_m`. -/
theorem mul_logDerivFamily {a : GradedCapFamily G}
    (ha : ∀ k, a k 0 = (1 : GradedCapFamily G) k 0) : a * logDerivFamily a = gradedDeriv a := by
  funext k m
  refine AddMonoidHom.ext fun x => ?_
  rw [gradedCap_mul_apply, Finset.sum_range_succ, convolveTerm_of_le _ _ _ le_rfl,
    capTo_congr_index a (Nat.sub_self m), capTo_def, ha, gradedCap_one_apply_zero,
    gradedDegreeCast_gradedDegreeCast]
  show _ + logDerivFamily a k m x = _
  rw [logDerivFamily_apply_apply,
    ← Fin.sum_univ_eq_sum_range (fun j => convolveTerm a (logDerivFamily a) k m j x) m]
  have hsum : ∑ j : Fin m, convolveTerm a (logDerivFamily a) k m j x =
      ∑ j : Fin m, capTo a (m - j)
        (show k - ((j : ℕ) : ℤ) - ((m - (j : ℕ) : ℕ) : ℤ) = k - (m : ℤ) by
          have := j.isLt; omega) (logDerivFamily a k j x) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [convolveTerm_of_le _ _ _ j.isLt.le]
  rw [hsum, add_sub_cancel, gradedDeriv_apply]

/-- **Uniqueness of the solution of Newton's identities.** -/
theorem logDerivFamily_eq_of_mul_eq {a x : GradedCapFamily G}
    (ha : ∀ k, a k 0 = (1 : GradedCapFamily G) k 0) (h : a * x = gradedDeriv a) :
    x = logDerivFamily a := by
  obtain ⟨u, hu⟩ := isUnit_of_apply_zero ha
  refine (Units.mul_right_inj u).mp ?_
  rw [hu, h, mul_logDerivFamily ha]

/-- The index-`0` component of a product of two families with identity index-`0` components is
again the identity. -/
theorem mul_apply_zero {a b : GradedCapFamily G}
    (ha : ∀ k, a k 0 = (1 : GradedCapFamily G) k 0)
    (hb : ∀ k, b k 0 = (1 : GradedCapFamily G) k 0) (k : ℤ) :
    (a * b) k 0 = (1 : GradedCapFamily G) k 0 := by
  rw [gradedCap_mul_apply_congr (a' := 1) (b' := 1)
      (fun l hl k => by obtain rfl := Nat.le_zero.mp hl; exact ha k)
      (fun l hl k => by obtain rfl := Nat.le_zero.mp hl; exact hb k) k,
    one_mul]

/-- The logarithmic derivative of the unit vanishes. -/
theorem logDerivFamily_one : logDerivFamily (1 : GradedCapFamily G) = 0 :=
  (logDerivFamily_eq_of_mul_eq (fun _ => rfl) (by rw [mul_zero, gradedDeriv_one])).symm

/-- **The logarithmic derivative is additive on a product**, as soon as the logarithmic
derivative of the first factor commutes with the second. This is the only place commutativity
enters the proof of Stacks 0F9C. -/
theorem logDerivFamily_mul_of_commute {a b : GradedCapFamily G}
    (ha : ∀ k, a k 0 = (1 : GradedCapFamily G) k 0)
    (hb : ∀ k, b k 0 = (1 : GradedCapFamily G) k 0)
    (hcomm : Commute (logDerivFamily a) b) :
    logDerivFamily (a * b) = logDerivFamily a + logDerivFamily b := by
  refine (logDerivFamily_eq_of_mul_eq (mul_apply_zero ha hb) ?_).symm
  rw [mul_add, gradedDeriv_mul, mul_assoc, ← hcomm, ← mul_assoc, mul_logDerivFamily ha,
    mul_assoc, mul_logDerivFamily hb]

/-- **The logarithmic derivative commutes with whatever `a` and `D(a)` commute with.** -/
theorem commute_logDerivFamily {a b : GradedCapFamily G}
    (ha : ∀ k, a k 0 = (1 : GradedCapFamily G) k 0) (h₁ : Commute a b)
    (h₂ : Commute (gradedDeriv a) b) : Commute (logDerivFamily a) b := by
  obtain ⟨u, hu⟩ := isUnit_of_apply_zero ha
  have hnu : logDerivFamily a = (↑u⁻¹ : GradedCapFamily G) * gradedDeriv a := by
    refine (logDerivFamily_eq_of_mul_eq ha ?_).symm
    rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]
  rw [hnu]
  refine Commute.mul_left ?_ h₂
  rw [← hu] at h₁
  exact h₁.units_inv_left

/-! ### The power sums -/

/-- **The power sum `P_p`** of a graded cap family: the signed index-`p` component
`(-1)^{p-1} ν(a)_p` of its logarithmic derivative. For `a = c(ℰ)` the total Chern class of a
finite locally free module this is the class `P_p(ℰ)` of Stacks 0F9B, read as an operation
`A_k(X) ⟶ A_{k-p}(X)`.

This is the logarithmic-derivative spelling of the canonical `P_p` of this development,
`AlgebraicGeometry.newtonPowerSum`, Newton's recurrence of Stacks 0F9B in an arbitrary ring: for
`a` with identity index-`0` component the two agree in every degree,
`Stacks.Chow.powerSumFamily_eq_newtonPowerSum`, the degree-zero term of the recurrence being `0`
and the Chern classes being the homogeneous components of `a`. It is kept because additivity on
a product is a two-line consequence of the single ring equation `a · ν(a) = D(a)`, which is what
`Stacks.Chow.powerSumFamily_mul_of_commute` and hence Stacks 0F9C rest on. -/
def powerSumFamily (a : GradedCapFamily G) (p : ℕ) : GradedCapFamily G :=
  ((-1 : ℤ) ^ (p + 1)) • homComponent p (logDerivFamily a)

/-- The power sum of index `p` is homogeneous of index `p`. -/
theorem isHomogeneous_powerSumFamily (a : GradedCapFamily G) (p : ℕ) :
    (powerSumFamily a p).IsHomogeneous p :=
  isHomogeneous_zsmul (isHomogeneous_homComponent p (logDerivFamily a)) _

/-- The index-`p` component of the power sum. -/
theorem powerSumFamily_apply_self (a : GradedCapFamily G) (p : ℕ) (k : ℤ) (x : G k) :
    powerSumFamily a p k p x = ((-1 : ℤ) ^ (p + 1)) • logDerivFamily a k p x := by
  rw [powerSumFamily, gradedCap_zsmul_apply, homComponent_apply_self]

/-- `P₀ = 0`, the convention of `AlgebraicGeometry.powerSumPolynomial`. -/
theorem powerSumFamily_zero (a : GradedCapFamily G) : powerSumFamily a 0 = 0 := by
  refine eq_of_isHomogeneous_of_apply_eq (isHomogeneous_powerSumFamily a 0)
    GradedCapFamily.IsHomogeneous.zero fun k x => ?_
  rw [powerSumFamily_apply_self, logDerivFamily_zero]
  simp

/-- **`P₁ = c₁`.** -/
theorem powerSumFamily_one (a : GradedCapFamily G) :
    powerSumFamily a 1 = homComponent 1 a := by
  refine eq_of_isHomogeneous_of_apply_eq (isHomogeneous_powerSumFamily a 1)
    (isHomogeneous_homComponent 1 a) fun k x => ?_
  rw [powerSumFamily_apply_self, logDerivFamily_one_apply, homComponent_apply_self]
  norm_num

/-- **Additivity of the power sums on a product**, from
`Stacks.Chow.logDerivFamily_mul_of_commute`. -/
theorem powerSumFamily_mul_of_commute {a b : GradedCapFamily G}
    (ha : ∀ k, a k 0 = (1 : GradedCapFamily G) k 0)
    (hb : ∀ k, b k 0 = (1 : GradedCapFamily G) k 0)
    (hcomm : Commute (logDerivFamily a) b) (p : ℕ) :
    powerSumFamily (a * b) p = powerSumFamily a p + powerSumFamily b p := by
  rw [powerSumFamily, powerSumFamily, powerSumFamily,
    logDerivFamily_mul_of_commute ha hb hcomm, map_add, smul_add]

/-! ### The signs of Newton's recursion -/

/-- A power of `-1` in a ring, as an integer multiple: this is how the signs of Newton's
recursion, which are ring elements, meet the integer multiples of the logarithmic derivative. -/
theorem neg_one_pow_mul_eq_zsmul {A : Type*} [Ring A] (n : ℕ) (x : A) :
    (-1 : A) ^ n * x = ((-1 : ℤ) ^ n) • x := by
  rw [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- The last term `(-1)^m (m + 1) a_{m+1}` of Newton's recursion, as an integer multiple of a
natural multiple. -/
theorem neg_one_pow_mul_succ_mul_eq_zsmul {A : Type*} [Ring A] (m : ℕ) (x : A) :
    (-1 : A) ^ m * ((m : A) + 1) * x = ((-1 : ℤ) ^ m) • ((m + 1) • x) := by
  rw [nsmul_eq_mul, zsmul_eq_mul, mul_assoc, Nat.cast_add, Nat.cast_one, Int.cast_pow,
    Int.cast_neg, Int.cast_one]

/-! ### The power sums are Newton's recursion of Stacks 0F9B -/

/-- **The homogeneous components of a product**, as the convolution of the components of the
factors: `(a b)_m = ∑_{i + j = m} a_i b_j`. -/
theorem homComponent_mul (a b : GradedCapFamily G) (m : ℕ) :
    homComponent m (a * b) =
      ∑ j ∈ range (m + 1), homComponent (m - j) a * homComponent j b := by
  have hhom : ∀ i : ℕ,
      (∑ j ∈ range (i + 1), homComponent (i - j) a * homComponent j b).IsHomogeneous i := by
    intro i
    refine GradedCapFamily.IsHomogeneous.sum fun j hj => ?_
    have hji : j ≤ i := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have h := (isHomogeneous_homComponent (i - j) a).mul (isHomogeneous_homComponent j b)
    rwa [Nat.sub_add_cancel hji] at h
  have hmul : a * b = gradedSeries fun i => ∑ j ∈ range (i + 1),
      homComponent (i - j) a * homComponent j b := by
    conv_lhs => rw [← gradedSeries_homComponent a, ← gradedSeries_homComponent b]
    exact mul_gradedSeries (fun i => isHomogeneous_homComponent i a)
      (fun j => isHomogeneous_homComponent j b)
  rw [hmul, homComponent_gradedSeries hhom]

/-- A family whose index-`0` component is the identity has index-`0` homogeneous component `1`;
this is the shape `c(ℰ) = 1 + c₁(ℰ) + ⋯` of a total Chern class. -/
theorem homComponent_zero_of_apply_zero {a : GradedCapFamily G}
    (ha : ∀ k, a k 0 = (1 : GradedCapFamily G) k 0) : homComponent 0 a = 1 := by
  rw [homComponent_congr ha]
  exact GradedCapFamily.IsHomogeneous.one.homComponent_self

/-- The index-`0` homogeneous component of the logarithmic derivative vanishes. -/
theorem homComponent_logDerivFamily_zero (a : GradedCapFamily G) :
    homComponent 0 (logDerivFamily a) = 0 := by
  refine eq_of_isHomogeneous_of_apply_eq (isHomogeneous_homComponent 0 _)
    GradedCapFamily.IsHomogeneous.zero fun k x => ?_
  rw [homComponent_apply_self, logDerivFamily_zero]
  rfl

/-- **Newton's recurrence on homogeneous components**: `ν_{m+1} = (m+1) a_{m+1} - ∑_{i < m+1}
a_{i+1} ν_{m-i}`, the index-`m+1` part of the single equation `a · ν(a) = D(a)` of
`Stacks.Chow.mul_logDerivFamily` with the term `a_0 ν_{m+1} = ν_{m+1}` moved to the left. The
sum is taken over `i < m` because the missing term `a_{m+1} ν_0` vanishes. -/
theorem homComponent_logDerivFamily_succ {a : GradedCapFamily G}
    (ha : ∀ k, a k 0 = (1 : GradedCapFamily G) k 0) (m : ℕ) :
    homComponent (m + 1) (logDerivFamily a) =
      (m + 1) • homComponent (m + 1) a -
        ∑ i ∈ range m, homComponent (i + 1) a * homComponent (m - i) (logDerivFamily a) := by
  have key := congrArg (homComponent (m + 1)) (mul_logDerivFamily ha)
  rw [homComponent_mul, homComponent_gradedDeriv, Finset.sum_range_succ, Nat.sub_self,
    homComponent_zero_of_apply_zero ha, one_mul] at key
  have hre : (∑ j ∈ range (m + 1),
        homComponent (m + 1 - j) a * homComponent j (logDerivFamily a)) =
      ∑ i ∈ range m, homComponent (i + 1) a * homComponent (m - i) (logDerivFamily a) := by
    rw [Finset.sum_range_succ' (fun j => homComponent (m + 1 - j) a *
        homComponent j (logDerivFamily a)) m,
      homComponent_logDerivFamily_zero, mul_zero, add_zero]
    conv_lhs => rw [← Finset.sum_range_reflect (fun i => homComponent (m + 1 - (i + 1)) a *
      homComponent (i + 1) (logDerivFamily a)) m]
    refine Finset.sum_congr rfl fun i hi => ?_
    have him : i < m := mem_range.mp hi
    rw [show m - 1 - i + 1 = m - i by omega, show m + 1 - (m - i) = i + 1 by omega]
  rw [eq_sub_iff_add_eq, add_comm, ← hre]
  exact key

/-- The homogeneous components of the logarithmic derivative are the signed power sums,
`ν_p = (-1)^{p-1} P_p`: the defining relation of `Stacks.Chow.powerSumFamily` read backwards. -/
theorem homComponent_logDerivFamily (a : GradedCapFamily G) (p : ℕ) :
    homComponent p (logDerivFamily a) = ((-1 : ℤ) ^ (p + 1)) • powerSumFamily a p := by
  rw [powerSumFamily, smul_smul, ← pow_add, show p + 1 + (p + 1) = 2 * (p + 1) by ring, pow_mul]
  norm_num

/-- **The power sums are Newton's recursion of Stacks 0F9B.** For a graded cap family `a` whose
index-`0` component is the identity, `Stacks.Chow.powerSumFamily a p` is
`AlgebraicGeometry.newtonPowerSum` — the canonical `P_p`, Newton's recurrence of Stacks 0F9B read
in an arbitrary ring, here the ring `Stacks.Chow.instRingGradedCapFamily` — evaluated at the
degree-zero term `0` and the family of Chern classes `i ↦ a_i`, the homogeneous components of
`a`.

The identity holds in **every** degree, `p = 0` included: the degree-zero term of the recurrence
is the rank variable `r` of Stacks 0F9B, and it is `0` here because
`Stacks.Chow.powerSumFamily_zero` follows the convention `P₀ = 0` of
`AlgebraicGeometry.powerSumPolynomial`. No normalisation factor intervenes: the sign
`(-1)^{p-1}` built into `Stacks.Chow.powerSumFamily` is exactly the one that turns the recurrence
`ν_{m+1} = (m+1) a_{m+1} - ∑_{i < m} a_{i+1} ν_{m-i}` of
`Stacks.Chow.homComponent_logDerivFamily_succ` into the recurrence of
`AlgebraicGeometry.newtonPowerSum_succ`.

Together with `AlgebraicGeometry.newtonPowerSum_eq_powerSumOfChernClasses` this is the
faithfulness certificate for the power sums used in Stacks 0F9C: they are the evaluation of the
universal polynomial `P_p` of Stacks 0F9B wherever that evaluation is defined. -/
theorem powerSumFamily_eq_newtonPowerSum {a : GradedCapFamily G}
    (ha : ∀ k, a k 0 = (1 : GradedCapFamily G) k 0) (p : ℕ) :
    powerSumFamily a p =
      AlgebraicGeometry.newtonPowerSum (0 : GradedCapFamily G)
        (fun i : ℕ+ => homComponent (i : ℕ) a) p := by
  induction p using Nat.case_strong_induction_on with
  | hz => rw [powerSumFamily_zero, AlgebraicGeometry.newtonPowerSum_zero]
  | hi m ih =>
    rw [AlgebraicGeometry.newtonPowerSum_succ]
    simp only [Nat.succPNat_coe]
    have hQ : ∀ j ∈ range m,
        (-1 : GradedCapFamily G) ^ j * homComponent (j + 1) a *
            AlgebraicGeometry.newtonPowerSum (0 : GradedCapFamily G)
              (fun i : ℕ+ => homComponent (i : ℕ) a) (m - j) =
          ((-1 : ℤ) ^ j) • (homComponent (j + 1) a * powerSumFamily a (m - j)) := by
      intro j _
      rw [← ih (m - j) (Nat.sub_le m j), mul_assoc, neg_one_pow_mul_eq_zsmul]
    rw [Finset.sum_congr rfl hQ]
    have hNP : ∀ i ∈ range m,
        ((-1 : ℤ) ^ (m + 1 + 1)) • (homComponent (i + 1) a *
            homComponent (m - i) (logDerivFamily a)) =
          -(((-1 : ℤ) ^ i) • (homComponent (i + 1) a * powerSumFamily a (m - i))) := by
      intro i hi
      have him : i < m := mem_range.mp hi
      have hs : ((-1 : ℤ) ^ (m + 1 + 1) * (-1 : ℤ) ^ (m - i + 1)) = -((-1 : ℤ) ^ i) := by
        rw [← pow_add, show m + 1 + 1 + (m - i + 1) = 2 * (m - i) + i + 3 by omega,
          pow_add, pow_add, pow_mul]
        norm_num
      rw [homComponent_logDerivFamily a (m - i), mul_smul_comm, smul_smul, hs, neg_smul]
    have hlead : ((-1 : ℤ) ^ (m + 1 + 1)) • ((m + 1) • homComponent (m + 1) a)
        = (-1 : GradedCapFamily G) ^ m * ((m : GradedCapFamily G) + 1) *
            homComponent (m + 1) a := by
      rw [neg_one_pow_mul_succ_mul_eq_zsmul,
        show ((-1 : ℤ) ^ (m + 1 + 1)) = (-1 : ℤ) ^ m by rw [pow_succ, pow_succ]; ring]
    rw [powerSumFamily, homComponent_logDerivFamily_succ ha, smul_sub, Finset.smul_sum,
      Finset.sum_congr rfl hNP,
      Finset.sum_neg_distrib (fun i => ((-1 : ℤ) ^ i) •
        (homComponent (i + 1) a * powerSumFamily a (m - i))),
      sub_neg_eq_add, hlead]
    exact add_comm _ _

/-! ### Commuting homogeneous elements -/

/-- The index-`m` component of a product of homogeneous elements of indices `i` and `j`, where
`i + j = m`: the single composite `x_i ∘ y_j`. -/
theorem mul_apply_of_isHomogeneous {x y : GradedCapFamily G} {i j m : ℕ}
    (hy : y.IsHomogeneous j) (hm : i + j = m) (k : ℤ) (z : G k) :
    (x * y) k m z =
      capTo x i (show k - (j : ℤ) - (i : ℤ) = k - (m : ℤ) by subst hm; push_cast; ring)
        (y k j z) := by
  subst hm
  rw [gradedCap_mul_apply, Finset.sum_eq_single j]
  · rw [convolveTerm_of_le _ _ _ (by omega), capTo_congr_index x (show i + j - j = i by omega)]
  · intro l hl hlj
    have hlm : l ≤ i + j := Nat.lt_succ_iff.mp (mem_range.mp hl)
    rw [convolveTerm_of_le _ _ _ hlm, hy k l hlj]
    simp only [AddMonoidHom.zero_apply]
    exact capTo_zero _ _ _
  · intro hmem
    exact absurd (mem_range.mpr (Nat.lt_succ_of_le (Nat.le_add_left j i))) hmem

/-- A product of homogeneous elements of indices `i` and `j` vanishes outside index `i + j`. -/
theorem mul_apply_of_isHomogeneous_of_ne {x y : GradedCapFamily G} {i j : ℕ}
    (hx : x.IsHomogeneous i) (hy : y.IsHomogeneous j) {m : ℕ} (hm : m ≠ i + j) (k : ℤ) :
    (x * y) k m = 0 := by
  refine AddMonoidHom.ext fun z => ?_
  rw [gradedCap_mul_apply, Finset.sum_eq_zero]
  · rfl
  intro l hl
  have hlm : l ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hl)
  rcases eq_or_ne l j with hlj | hlj
  · subst hlj
    rw [convolveTerm_of_le _ _ _ hlm, capTo_of_eq_zero x _ (hx _ _ (by omega))]
  · rw [convolveTerm_of_le _ _ _ hlm, hy k l hlj]
    simp only [AddMonoidHom.zero_apply]
    exact capTo_zero _ _ _

/-- **Two homogeneous elements commute as soon as their one nonzero product component agrees.** -/
theorem commute_of_isHomogeneous {x y : GradedCapFamily G} {i j : ℕ}
    (hx : x.IsHomogeneous i) (hy : y.IsHomogeneous j)
    (h : ∀ (k : ℤ) (z : G k), (x * y) k (i + j) z = (y * x) k (i + j) z) : Commute x y := by
  have hmul : x * y = y * x := by
    funext k m
    rcases eq_or_ne m (i + j) with hm | hm
    · subst hm
      exact AddMonoidHom.ext fun z => h k z
    · rw [mul_apply_of_isHomogeneous_of_ne hx hy hm,
        mul_apply_of_isHomogeneous_of_ne hy hx (by omega) k]
  exact hmul

/-- **Two homogeneous elements commute as soon as their two composites agree**, which for Chern
classes is the displayed identity of Stacks 02UA. -/
theorem commute_of_isHomogeneous_of_capTo {x y : GradedCapFamily G} {i j : ℕ}
    (hx : x.IsHomogeneous i) (hy : y.IsHomogeneous j)
    (h : ∀ (k : ℤ) (z : G k),
      capTo x i (show k - (j : ℤ) - (i : ℤ) = k - ((i + j : ℕ) : ℤ) by push_cast; ring)
          (y k j z) =
        capTo y j (show k - (i : ℤ) - (j : ℤ) = k - ((i + j : ℕ) : ℤ) by push_cast; ring)
          (x k i z)) :
    Commute x y :=
  commute_of_isHomogeneous hx hy fun k z => by
    rw [mul_apply_of_isHomogeneous hy rfl k z,
      mul_apply_of_isHomogeneous hx (show j + i = i + j by omega) k z, h k z]

/-- **A family commutes with another as soon as their homogeneous components commute.** The two
convolutions are the same double sum read in the two orders. -/
theorem commute_of_commute_homComponent {a b : GradedCapFamily G}
    (h : ∀ i j, Commute (homComponent i a) (homComponent j b)) : Commute a b := by
  have hmul : a * b = b * a := by
    rw [← gradedSeries_homComponent a, ← gradedSeries_homComponent b,
      mul_gradedSeries (fun i => isHomogeneous_homComponent i a)
        (fun j => isHomogeneous_homComponent j b),
      mul_gradedSeries (fun j => isHomogeneous_homComponent j b)
        (fun i => isHomogeneous_homComponent i a)]
    congr 1
    funext m
    rw [← Finset.sum_range_reflect
      (fun j => homComponent (m - j) b * homComponent j a) (m + 1)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjm : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
    rw [show m + 1 - 1 - j = m - j by omega, show m - (m - j) = j by omega]
    exact h (m - j) j
  exact hmul

/-- A natural multiple of a commuting family commutes. -/
theorem commute_nsmul_left {a b : GradedCapFamily G} (h : Commute a b) (n : ℕ) :
    Commute (n • a) b := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul]; exact ih.add_left h

/-- **The derivation commutes with whatever the homogeneous components commute with.** -/
theorem commute_gradedDeriv_of_commute_homComponent {a b : GradedCapFamily G}
    (h : ∀ i j, Commute (homComponent i a) (homComponent j b)) : Commute (gradedDeriv a) b :=
  commute_of_commute_homComponent fun i j => by
    rw [homComponent_gradedDeriv]
    exact commute_nsmul_left (h i j) i

/-- **The logarithmic derivative commutes with whatever the homogeneous components commute
with.** -/
theorem commute_logDerivFamily_of_commute_homComponent {a b : GradedCapFamily G}
    (ha : ∀ k, a k 0 = (1 : GradedCapFamily G) k 0)
    (h : ∀ i j, Commute (homComponent i a) (homComponent j b)) :
    Commute (logDerivFamily a) b :=
  commute_logDerivFamily ha (commute_of_commute_homComponent h)
    (commute_gradedDeriv_of_commute_homComponent h)

end Stacks.Chow

end
