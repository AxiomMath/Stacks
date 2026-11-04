module

public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.ChernRootPowerSums

/-!
# Evaluating the universal Chern polynomials at central elements of a ring

The universal power-sum polynomials `P_p` of Stacks 0F9B are integral polynomials in commuting
Chern-class variables, so `AlgebraicGeometry.chernClassEval` evaluates them in a *commutative*
ring. The graded ring `A(X)` of a Weil cohomology theory is not commutative; what is true is that
the Chern classes are central in it. This file supplies the two facts that let the universal
polynomials be evaluated in the centre of an arbitrary ring and the result be recognised inside
`A(X)`:

* a ring map carries such an evaluation to the corresponding evaluation of the images, even
  though a ring map need not send the centre into the centre;
* the evaluation of a weighted-homogeneous polynomial of degree `n` at classes lying in the
  graded pieces `A^i(X)` lies in `A^n(X)`.

The recursion that computes the elementary symmetric functions of a family of Chern roots one
root at a time is here too, since it is what identifies the Chern classes of a sum of classes of
invertible modules with the elementary symmetric functions of their first Chern classes.

## Main results

* `Stacks.WeilCohomology.esymm_cons`: `e_{n+1}(a, x) = e_{n+1}(x) + a · e_n(x)`.
* `Stacks.WeilCohomology.map_chernClassEval`: a ring map commutes with evaluation at central
  elements.
* `Stacks.WeilCohomology.chernClassEval_mem_of_isWeightedHomogeneous`: evaluation of a
  weighted-homogeneous polynomial of degree `n` at graded central elements lands in degree `n`.

## Implementation notes

The grading of the target ring is taken as a bare family of additive subgroups with the unit in
degree zero and multiplication adding degrees, which is the shape
`Stacks.WeilCohomology.ChernSetup` records it in; nothing else about the situation is used, so
the statements are about an arbitrary ring.

## References

* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace Stacks.WeilCohomology

/-! ### The elementary symmetric functions, one root at a time -/

/-- **The elementary symmetric functions of a family of roots, read off one root at a time**:
adjoining a root `a` adds to `e_{n+1}` the term `a · e_n` of the subsets that use it. -/
theorem esymm_cons {R : Type*} [CommSemiring R] (a : R) (s : Multiset R) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Function.comp_def, Multiset.prod_cons, Multiset.sum_map_mul_left]

/-! ### A ring map and an evaluation at central elements -/

/-- The evaluation of `p * X i` is the evaluation of `p` times the value at `i`. -/
private theorem chernClassEval_mul_X {A : Type*} [Ring A] (cA : ℕ+ → Subring.center A)
    (p : MvPolynomial ℕ+ ℤ) (i : ℕ+) :
    (chernClassEval cA (p * MvPolynomial.X i) : A) =
      (chernClassEval cA p : A) * (cA i : A) := by
  rw [map_mul]
  push_cast
  simp [chernClassEval]

/-- **A ring map commutes with the evaluation of a universal Chern polynomial at central
elements.** The evaluation itself has to be performed in the centre, which is commutative; the
ring map need not send the centre of its source into the centre of its target, so the statement
is about the two evaluations and the images of the variables, and is proved by induction on the
polynomial. -/
theorem map_chernClassEval {A B : Type*} [Ring A] [Ring B] (φ : A →+* B)
    (cA : ℕ+ → Subring.center A) (cB : ℕ+ → Subring.center B)
    (h : ∀ i, φ (cA i) = cB i) (Q : MvPolynomial ℕ+ ℤ) :
    φ (chernClassEval cA Q) = (chernClassEval cB Q : B) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [chernClassEval]
  | add p q hp hq => push_cast [map_add, hp, hq]; ring_nf
  | mul_X p i hp =>
      rw [chernClassEval_mul_X, chernClassEval_mul_X, map_mul, hp, h i]

/-! ### An evaluation at graded elements -/

/-- **The evaluation of a weighted-homogeneous polynomial of degree `n` at central classes of the
prescribed degrees lies in degree `n`.** The variable `c_i` has weight `i` and is evaluated at a
class of `A^i(X)`, so every monomial of `Q` is sent to a product of classes whose degrees add up
to the weight of that monomial, which is `n`; the integer coefficient lies in degree zero. -/
theorem chernClassEval_mem_of_isWeightedHomogeneous {A : Type*} [Ring A]
    (grade : ℕ → AddSubgroup A) (hone : (1 : A) ∈ grade 0)
    (hmul : ∀ (i j : ℕ) {a b : A}, a ∈ grade i → b ∈ grade j → a * b ∈ grade (i + j))
    (cA : ℕ+ → Subring.center A) (hc : ∀ i : ℕ+, (cA i : A) ∈ grade (i : ℕ))
    (n : ℕ) (Q : MvPolynomial ℕ+ ℤ)
    (hQ : MvPolynomial.IsWeightedHomogeneous (fun i : ℕ+ => (i : ℕ)) Q n) :
    (chernClassEval cA Q : A) ∈ grade n := by
  classical
  have hpow : ∀ (i : ℕ+) (k : ℕ),
      ((cA i ^ k : Subring.center A) : A) ∈ grade (k * (i : ℕ)) := by
    intro i k
    induction k with
    | zero => simpa using hone
    | succ k ih =>
        have hidx : (k + 1) * (i : ℕ) = k * (i : ℕ) + (i : ℕ) := by ring
        have hsplit : ((cA i ^ (k + 1) : Subring.center A) : A) =
            ((cA i ^ k : Subring.center A) : A) * (cA i : A) := by
          rw [pow_succ]
          push_cast
          rfl
        rw [hidx, hsplit]
        exact hmul _ _ ih (hc i)
  have hprod : ∀ (d : ℕ+ →₀ ℕ) (s : Finset ℕ+),
      ((∏ i ∈ s, cA i ^ d i : Subring.center A) : A) ∈ grade (∑ i ∈ s, d i * (i : ℕ)) := by
    intro d s
    induction s using Finset.induction_on with
    | empty => simpa using hone
    | insert a s ha ih =>
        have hsplit : ((∏ i ∈ insert a s, cA i ^ d i : Subring.center A) : A) =
            ((cA a ^ d a : Subring.center A) : A) *
              ((∏ i ∈ s, cA i ^ d i : Subring.center A) : A) := by
          rw [Finset.prod_insert ha]
          push_cast
          rfl
        rw [Finset.sum_insert ha, hsplit]
        exact hmul _ _ (hpow a (d a)) ih
  have hzint : ∀ z : ℤ, ((z : A)) ∈ grade 0 := fun z => by simpa using zsmul_mem hone z
  rw [MvPolynomial.as_sum Q, map_sum]
  rw [show ((∑ d ∈ Q.support, chernClassEval cA
      (MvPolynomial.monomial d (MvPolynomial.coeff d Q)) : Subring.center A) : A) =
      ∑ d ∈ Q.support, ((chernClassEval cA
        (MvPolynomial.monomial d (MvPolynomial.coeff d Q)) : Subring.center A) : A) from
    map_sum (Subring.center A).subtype _ _]
  refine sum_mem fun d hd => ?_
  have hw : (Finsupp.weight (fun i : ℕ+ => (i : ℕ))) d = n :=
    hQ (MvPolynomial.mem_support_iff.mp hd)
  have hev : ((chernClassEval cA
      (MvPolynomial.monomial d (MvPolynomial.coeff d Q)) : Subring.center A) : A) =
      ((MvPolynomial.coeff d Q : ℤ) : A) *
        ((∏ i ∈ d.support, cA i ^ d i : Subring.center A) : A) := by
    simp [chernClassEval, MvPolynomial.eval₂_monomial, Finsupp.prod]
  have hsum : ∑ i ∈ d.support, d i * (i : ℕ) = n := by
    rw [← hw, Finsupp.weight_apply, Finsupp.sum]
    exact Finset.sum_congr rfl fun i _ => (smul_eq_mul _ _)
  rw [hev]
  simpa using hmul 0 n (hzint (MvPolynomial.coeff d Q)) (hsum ▸ hprod d d.support)

end Stacks.WeilCohomology

end
