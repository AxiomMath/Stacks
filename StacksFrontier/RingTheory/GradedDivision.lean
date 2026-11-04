module

public import Mathlib.Algebra.DirectSum.Ring
public import Mathlib.Algebra.Ring.NonZeroDivisors
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Dividing a map out of a graded ring by a nonzerodivisor

Let `A = ⨁ₙ Aₙ` be a nonnegatively graded commutative ring, let `B` be a commutative ring, let
`π : A ⟶ B` be a ring map and let `t ∈ B` be a nonzerodivisor. Suppose that `π` carries every
homogeneous element of degree `n` into the ideal `(tⁿ)`. Then there is a *unique* ring map
`ψ : A ⟶ B` with `tⁿ ψ(a) = π(a)` for homogeneous `a` of degree `n`, that is, `ψ` divides the
degree-`n` part of `π` by `tⁿ`.

This is the algebraic core of the mapping-in half of the universal property of a relative `Proj`
in the case where the invertible module on the test scheme is trivialized: a graded map
`⨁ₙ Aₙ ⟶ ⨁ₙ L^{⊗n}` with `L = t·B ≅ B` is exactly such a `ψ`. It generalizes
`Stacks.Blowup.reesDivide`, which is the case `A = reesAlgebra I ⊆ R[X]`, from the Rees algebra
of an ideal in a ring to an arbitrary graded ring; the construction there divides inside the
localization `B[1/t]`, which needs `A` to be a subring of a polynomial ring, while the one here
divides degreewise and uses only that `t` is a nonzerodivisor.

## Main results

* `Stacks.GradedDivision.exists_ringHom_pow_mul_eq`: existence of `ψ`, with its characterizing
  property on homogeneous elements.
* `Stacks.GradedDivision.eq_of_pow_mul_eq`: uniqueness of `ψ`, for an internally graded ring.
* `Stacks.GradedDivision.eq_top_of_mem_span_singleton_mul`: if `t` is a nonzerodivisor and
  `t ∈ (t) · J`, then `J` is the unit ideal. This is what turns "the degree-one part of `ψ`
  generates" into the hypothesis of `AlgebraicGeometry.Proj.fromOfGlobalSections`.

## Implementation notes

The existence statement is phrased on `⨁ n : ℕ, A n` with an external grading, because that is
the shape the graded rings of local sections of a relative `Proj` situation have, and because
`DirectSum.liftRingHom` builds a ring map out of such a direct sum from its homogeneous
components. The components of `ψ` are chosen with `Exists.choose`; each ring-hom axiom is then
checked by multiplying through by the relevant power of `t` and cancelling it, which is legitimate
exactly because a power of a nonzerodivisor is a nonzerodivisor.

Uniqueness is stated separately, for an *internally* graded ring `𝒜 : ι → AddSubgroup A`, since
that is the form in which a consumer has its two candidate maps; it does not need `ι = ℕ` and does
not need the divisibility hypothesis. It is stated for an arbitrary family of weights `w` rather
than for the powers of a single `t`, because nothing in the argument relates the weights to each
other.
-/

@[expose] public section

open DirectSum

namespace Stacks.GradedDivision

/-- **A nonzerodivisor cancels from the unit ideal test.** If `t` is a nonzerodivisor and `t` lies
in the product of the principal ideal `(t)` with an ideal `J`, then `J` is the unit ideal.

This is the shape in which surjectivity of the degree-one part of a graded map becomes the
hypothesis of `AlgebraicGeometry.Proj.fromOfGlobalSections`: the image of the irrelevant ideal
contains elements whose multiples by `t` generate `t`. -/
theorem eq_top_of_mem_span_singleton_mul {B : Type*} [CommRing B] {t : B}
    (ht : t ∈ nonZeroDivisors B) {J : Ideal B} (h : t ∈ Ideal.span {t} * J) : J = ⊤ := by
  obtain ⟨y, hyJ, hy⟩ := Submodule.mem_span_singleton_mul.mp h
  have hy1 : y = 1 := by
    refine sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp ht).2 (y - 1) ?_)
    rw [sub_mul, one_mul, mul_comm y t, hy, sub_self]
  exact Ideal.eq_top_of_isUnit_mem _ (hy1 ▸ hyJ) isUnit_one

section Exists

variable {A : ℕ → Type*} [∀ n, AddCommGroup (A n)] [DirectSum.GCommRing A]
  {B : Type*} [CommRing B]

/-- **Division of a map out of a graded ring by a nonzerodivisor.** Let `π : ⨁ₙ Aₙ ⟶ B` be a ring
map and `t ∈ B` a nonzerodivisor such that `tⁿ` divides `π` of every homogeneous element of
degree `n`. Then there is a ring map `ψ` with `tⁿ · ψ(a) = π(a)` for every homogeneous `a` of
degree `n`.

The quotients are chosen degreewise; additivity and multiplicativity of the result follow from
those of `π` by cancelling a power of `t`. -/
theorem exists_ringHom_pow_mul_eq (π : (⨁ n, A n) →+* B) (t : B) (ht : t ∈ nonZeroDivisors B)
    (hdvd : ∀ (n : ℕ) (a : A n), ∃ c : B, π (DirectSum.of A n a) = t ^ n * c) :
    ∃ ψ : (⨁ n, A n) →+* B,
      ∀ (n : ℕ) (a : A n), t ^ n * ψ (DirectSum.of A n a) = π (DirectSum.of A n a) := by
  classical
  have hpow (n : ℕ) : t ^ n ∈ nonZeroDivisors B := pow_mem ht n
  have hcancel {n : ℕ} {x y : B} (h : t ^ n * x = t ^ n * y) : x = y :=
    (mul_cancel_left_mem_nonZeroDivisors (hpow n)).mp h
  -- The degreewise quotient, and its characterizing property.
  let q : ∀ n : ℕ, A n → B := fun n a => (hdvd n a).choose
  have hqspec (n : ℕ) (a : A n) : t ^ n * q n a = π (DirectSum.of A n a) :=
    (hdvd n a).choose_spec.symm
  -- The quotient is unique, so it inherits additivity from `π`.
  let f : ∀ {n : ℕ}, A n →+ B := fun {n} =>
    { toFun := q n
      map_zero' := by
        refine hcancel (n := n) ?_
        rw [hqspec, mul_zero, map_zero, map_zero]
      map_add' := fun a b => by
        refine hcancel (n := n) ?_
        rw [hqspec, mul_add, hqspec, hqspec, ← map_add, ← map_add] }
  refine ⟨DirectSum.liftRingHom ⟨f, ?_, ?_⟩, fun n a => ?_⟩
  · -- `ψ 1 = 1`
    refine hcancel (n := 0) ?_
    show t ^ 0 * q 0 (GradedMonoid.GOne.one : A 0) = t ^ 0 * 1
    rw [hqspec, ← DirectSum.one_def, map_one, pow_zero, one_mul]
  · -- `ψ` is multiplicative on homogeneous elements
    intro i j a b
    refine hcancel (n := i + j) ?_
    show t ^ (i + j) * q (i + j) (GradedMonoid.GMul.mul a b) = t ^ (i + j) * (q i a * q j b)
    rw [hqspec, ← DirectSum.of_mul_of, map_mul, ← hqspec, ← hqspec, pow_add]
    ring
  · rw [DirectSum.liftRingHom_apply, DirectSum.toSemiring_of]
    exact hqspec n a

end Exists

section Unique

variable {A : Type*} [CommRing A] {ι : Type*} [DecidableEq ι] [AddMonoid ι]
  (𝒜 : ι → AddSubgroup A) [GradedRing 𝒜] {B : Type*} [CommRing B]

/-- **Uniqueness of the divided map.** Two ring maps out of an internally graded ring which agree
after multiplication by a family of nonzerodivisors on every homogeneous element are equal,
because a graded ring is additively generated by its homogeneous elements. -/
theorem eq_of_pow_mul_eq (ψ χ : A →+* B) (w : ι → B) (hw : ∀ i, w i ∈ nonZeroDivisors B)
    (h : ∀ (i : ι) (a : A), a ∈ 𝒜 i → w i * ψ a = w i * χ a) : ψ = χ := by
  classical
  refine RingHom.ext fun x => ?_
  rw [← DirectSum.sum_support_decompose 𝒜 x, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (mul_cancel_left_mem_nonZeroDivisors (hw i)).mp (h i _ (DirectSum.decompose 𝒜 x i).2)

end Unique

end Stacks.GradedDivision

end
