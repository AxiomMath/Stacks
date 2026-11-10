module

public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Polynomial.Laurent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# When evaluation of Laurent polynomials at a unit is bijective

Let `f : R →+* Q` be a homomorphism of commutative rings and `x ∈ Qˣ` a unit, and let
`eval₂ f x : R[T;T⁻¹] →+* Q` be the induced homomorphism sending `T` to `x`.  This file gives a
criterion for `eval₂ f x` to be an isomorphism: the elements `f(r) xᵐ` generate `Q` additively,
and there are additive "coefficient" maps `π_n : Q → R` reading off `r` from `f(r) xⁿ` and
killing `f(r) xᵐ` for `m ≠ n`.  This is the shape in which a `ℤ`-graded ring whose degree-zero
part is `R` and whose degree-one part contains a unit is recognised as a ring of Laurent
polynomials.

## Main results

* `LaurentPolynomial.bijective_eval₂_of_coeff`: the criterion.
* `LaurentPolynomial.bijective_eval₂_of_isHomogeneousOf`: **a `ℤ`-graded commutative ring with
  degree-zero part `R` and a unit of degree one is `R[T;T⁻¹]`.**
-/

@[expose] public section

namespace LaurentPolynomial

variable {R Q : Type*} [CommRing R] [CommRing Q] (f : R →+* Q) (x : Qˣ)

/-- **A criterion for `eval₂ f x : R[T;T⁻¹] → Q` to be bijective**: the elements `f(r) xᵐ`
generate `Q` additively, and a family of additive maps `π_n : Q → R` reads off the coefficient of
`xⁿ`. -/
theorem bijective_eval₂_of_coeff (π : ℤ → Q →+ R)
    (hπ : ∀ (n m : ℤ) (r : R), π n (f r * ↑(x ^ m)) = if m = n then r else 0)
    (hgen : ∀ q : Q, q ∈ AddSubmonoid.closure {q' | ∃ (r : R) (m : ℤ), q' = f r * ↑(x ^ m)}) :
    Function.Bijective (eval₂ f x) := by
  classical
  have hcoeff : ∀ (p : R[T;T⁻¹]) (n : ℤ), π n (eval₂ f x p) = p.coeff n := by
    intro p n
    induction p using LaurentPolynomial.induction_on' with
    | add p q hp hq =>
      rw [map_add, map_add, hp, hq, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    | C_mul_T m a =>
      rw [eval₂_C_mul_T, hπ, ← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
        Finsupp.single_apply]
  refine ⟨fun p q hpq => LaurentPolynomial.ext fun n => ?_, fun q => ?_⟩
  · rw [← hcoeff p n, ← hcoeff q n, hpq]
  · induction hgen q using AddSubmonoid.closure_induction with
    | mem q' hq' =>
      obtain ⟨r, m, rfl⟩ := hq'
      exact ⟨C r * T m, eval₂_C_mul_T f x r m⟩
    | zero => exact ⟨0, map_zero _⟩
    | add a b _ _ ha hb =>
      obtain ⟨p, rfl⟩ := ha
      obtain ⟨p', rfl⟩ := hb
      exact ⟨p + p', map_add _ p p'⟩

/-! ### Graded rings -/

section Graded

variable {M : ℤ → Type*} [∀ i, AddCommGroup (M i)] (e : Q ≃+ DirectSum ℤ M)

/-- An element of `Q` is *homogeneous of degree `k`* for the additive identification `e` of `Q`
with a direct sum when it is the image of an element of the `k`th summand. -/
def IsHomogeneousOf (k : ℤ) (q : Q) : Prop := ∃ y : M k, e q = DirectSum.of M k y

variable {e}

/-- An element homogeneous of degree `k` has zero component in every degree `j ≠ k`. -/
theorem IsHomogeneousOf.apply_eq_zero {k j : ℤ} {q : Q} (hq : IsHomogeneousOf e k q)
    (hjk : j ≠ k) : e q j = 0 := by
  obtain ⟨y, hy⟩ := hq
  rw [hy]
  exact DirectSum.of_eq_of_ne k j y hjk

/-- An element `q` homogeneous of degree `k` satisfies `e q = of M k (e q k)`: it is the image of
its own degree-`k` component. -/
theorem IsHomogeneousOf.eq_of {k : ℤ} {q : Q} (hq : IsHomogeneousOf e k q) :
    e q = DirectSum.of M k (e q k) := by
  obtain ⟨y, hy⟩ := hq
  rw [hy, DirectSum.of_eq_same]

/-- **A `ℤ`-graded commutative ring with degree-zero part `R` and a unit of degree one is the ring
of Laurent polynomials over `R`.**

Here `Q` is identified additively with `⨁ₖ Mₖ` by `e`, products of homogeneous elements are
homogeneous of the sum of the degrees, `f : R →+* Q` is an isomorphism onto the degree-zero
summand, and `x` is a unit homogeneous of degree one whose inverse is homogeneous of degree
minus one.  Then `T ↦ x` is an isomorphism `R[T;T⁻¹] ≅ Q`. -/
@[sga "3 VIII 4.7" "partial"]
theorem bijective_eval₂_of_isHomogeneousOf
    (hmul : ∀ (i j : ℤ) (a b : Q), IsHomogeneousOf e i a → IsHomogeneousOf e j b →
      IsHomogeneousOf e (i + j) (a * b))
    (φ : R ≃+ M 0) (hf : ∀ r, e (f r) = DirectSum.of M 0 (φ r))
    (hx : IsHomogeneousOf e 1 (x : Q)) (hxinv : IsHomogeneousOf e (-1) (↑x⁻¹ : Q)) :
    Function.Bijective (eval₂ f x) := by
  classical
  have hf0 : ∀ r, IsHomogeneousOf e 0 (f r) := fun r => ⟨φ r, hf r⟩
  have hpow : ∀ k : ℤ, IsHomogeneousOf e k (↑(x ^ k) : Q) := by
    intro k
    induction k using Int.induction_on with
    | zero => simpa using hf0 1
    | succ k hk =>
      rw [zpow_add_one, Units.val_mul]
      exact hmul _ _ _ _ hk hx
    | pred k hk =>
      rw [zpow_sub_one, Units.val_mul]
      exact hmul _ _ _ _ hk hxinv
  have hdeg0 : ∀ q : Q, IsHomogeneousOf e 0 q → q = f (φ.symm (e q 0)) := fun q hq =>
    e.injective (hq.eq_of.trans (by rw [hf, φ.apply_symm_apply]))
  let π : ℤ → Q →+ R := fun n =>
    φ.symm.toAddMonoidHom.comp ((DFinsupp.evalAddMonoidHom 0).comp
      (e.toAddMonoidHom.comp (AddMonoidHom.mulLeft (↑(x ^ (-n)) : Q))))
  have hπ : ∀ (n : ℤ) (q : Q), π n q = φ.symm (e (↑(x ^ (-n)) * q) 0) := fun _ _ => rfl
  refine bijective_eval₂_of_coeff f x π (fun n m r => ?_) (fun q => ?_)
  · rw [hπ]
    split_ifs with hmn
    · subst hmn
      rw [mul_left_comm, zpow_neg, Units.inv_mul, mul_one, hf, DirectSum.of_eq_same,
        φ.symm_apply_apply]
    · have hh : IsHomogeneousOf e (-n + (0 + m)) (↑(x ^ (-n)) * (f r * ↑(x ^ m))) :=
        hmul _ _ _ _ (hpow _) (hmul _ _ _ _ (hf0 r) (hpow m))
      rw [hh.apply_eq_zero (by omega), map_zero]
  · have hall : ∀ z : DirectSum ℤ M, e.symm z ∈ AddSubmonoid.closure (Set.range
        fun z : Σ k, M k => e.symm (DirectSum.of M z.1 z.2)) := by
      intro z
      induction z using DirectSum.induction_on with
      | zero => rw [map_zero]; exact zero_mem _
      | of k y => exact AddSubmonoid.subset_closure ⟨⟨k, y⟩, rfl⟩
      | add a b ha hb => rw [map_add]; exact add_mem ha hb
    have hq := hall (e q)
    rw [AddEquiv.symm_apply_apply] at hq
    refine AddSubmonoid.closure_mono ?_ hq
    rintro _ ⟨⟨k, y⟩, rfl⟩
    have hy : IsHomogeneousOf e k (e.symm (DirectSum.of M k y)) := ⟨y, e.apply_symm_apply _⟩
    have h0 : IsHomogeneousOf e (-k + k) (↑(x ^ (-k)) * e.symm (DirectSum.of M k y)) :=
      hmul _ _ _ _ (hpow _) hy
    rw [neg_add_cancel] at h0
    refine ⟨φ.symm (e (↑(x ^ (-k)) * e.symm (DirectSum.of M k y)) 0), k, ?_⟩
    change e.symm (DirectSum.of M k y) = _
    rw [← hdeg0 _ h0, mul_comm, ← mul_assoc, zpow_neg, Units.mul_inv, one_mul]

end Graded

end LaurentPolynomial
