module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Multiplicity
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.RingTheory.DividedPowers.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.Polynomial.Basic
public import StacksFrontier.RingTheory.DividedPowers.PolynomialAlgebra
public import StacksFrontier.RingTheory.DividedPowers.Ring
public import StacksFrontier.RingTheory.DividedPowers.PrimeOperation.Coefficients
import all StacksFrontier.RingTheory.DividedPowers.PrimeOperation.Coefficients
public import StacksFrontier.RingTheory.DividedPowers.PrimeOperation.PrimeGamma
import all StacksFrontier.RingTheory.DividedPowers.PrimeOperation.PrimeGamma
public import StacksFrontier.RingTheory.DividedPowers.PrimeOperation.PolynomialLift
import all StacksFrontier.RingTheory.DividedPowers.PrimeOperation.PolynomialLift

/-!
# Divided powers over the integers localized at a prime

Let `p` be a prime and let `A` be a commutative ring in which every integer prime to `p` is
invertible, so that `A` is a `ℤ_(p)`-algebra. Over such a ring a divided power structure on an
ideal `I` is determined by its `p`th operation: the product rule recovers `γₙ` from `γ_{n-1}`
whenever `n` is prime to `p`, and the composition rule recovers `γ_{pm}` from `γₘ ∘ γ_p`, so
an induction on `n` pins every operation down.

Conversely, a map `δ : I → I` satisfying the three identities inherited from the divided
power axioms is the `p`th operation of a unique divided power structure on `I`. Those
identities are the factorial identity `p! · δ(x) = xᵖ`, homogeneity `δ(a • x) = aᵖ • δ(x)`,
and the addition law, whose cross terms carry the coefficients `1/i! · 1/j!` for `i + j = p`
with `i, j ≠ 0`.

## Main results

* `DividedPowers.eq_iff_dpow_prime_eq` — two divided power structures on the same ideal agree
  exactly when their `p`th operations agree.
* `DividedPowers.existsUnique_of_prime_operation` — a proposed `p`th operation satisfying the
  factorial identity, homogeneity and the addition law is the `p`th operation of a unique
  divided power structure.

## Implementation notes

The two assertions of the source are separate declarations, since the uniqueness half needs
none of the polynomial algebra machinery.

## References

* [Stacks Project, Tag 07GS](https://stacks.math.columbia.edu/tag/07GS)
-/

@[expose] public section

open Finset

namespace DividedPowers

private noncomputable def primeDpow {A : Type*} [CommRing A] {I : Ideal A} (p : ℕ)
    (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) (δ : I → I) :
    ℕ → A → A := by
  classical
  exact fun n x => if hx : x ∈ I then primeGamma p hp hA δ n ⟨x, hx⟩ else 0

private lemma primeDpow_apply {A : Type*} [CommRing A] {I : Ideal A} (p : ℕ)
    (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) (δ : I → I)
    (n : ℕ) {x : A} (hx : x ∈ I) :
    primeDpow p hp hA δ n x = primeGamma p hp hA δ n ⟨x, hx⟩ := by
  simp [primeDpow, hx]

private lemma primeDpow_zero {A : Type*} [CommRing A] {I : Ideal A} (p : ℕ)
    (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) (δ : I → I)
    {x : A} (hx : x ∈ I) : primeDpow p hp hA δ 0 x = 1 := by
  rw [primeDpow_apply p hp hA δ 0 hx]
  simp [primeGamma]

private lemma primeDpow_one {A : Type*} [CommRing A] {I : Ideal A} (p : ℕ)
    (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) (δ : I → I)
    {x : A} (hx : x ∈ I) : primeDpow p hp hA δ 1 x = x := by
  rw [primeDpow_apply p hp hA δ 1 hx]
  simp [primeGamma]

private lemma primeDpow_p {A : Type*} [CommRing A] {I : Ideal A} (p : ℕ)
    (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) (δ : I → I)
    {x : A} (hx : x ∈ I) : primeDpow p hp hA δ p x = δ ⟨x, hx⟩ := by
  rw [primeDpow_apply p hp hA δ p hx]
  exact primeGamma_at_prime p hp hA δ ⟨x, hx⟩

private lemma primeDpow_mem {A : Type*} [CommRing A] {I : Ideal A} (p : ℕ)
    (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) (δ : I → I)
    {n : ℕ} (hn : n ≠ 0) {x : A} (hx : x ∈ I) : primeDpow p hp hA δ n x ∈ I := by
  rw [primeDpow_apply p hp hA δ n hx]
  exact primeGamma_mem p hp hA δ n hn ⟨x, hx⟩

private lemma primeDpow_smul {A : Type*} [CommRing A] {I : Ideal A} (p : ℕ)
    (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) (δ : I → I)
    (smul : ∀ (a : A) (x : I), δ (a • x) = a ^ p • δ x) (n : ℕ)
    (a : A) {x : A} (hx : x ∈ I) :
    primeDpow p hp hA δ n (a * x) = a ^ n * primeDpow p hp hA δ n x := by
  let xI : I := ⟨x, hx⟩
  have hcoe : ((a • xI : I) : A) = a * x := by
    rw [Submodule.coe_smul, smul_eq_mul]
  have hax : a * x ∈ I := I.mul_mem_left a hx
  have hsub : (⟨a * x, hax⟩ : I) = a • xI := by
    apply Subtype.ext
    simpa [Submodule.coe_smul, smul_eq_mul]
  rw [primeDpow_apply p hp hA δ n hax, primeDpow_apply p hp hA δ n hx]
  rw [hsub]
  exact primeGamma_smul p hp hA δ smul n a xI

/-- Over a `ℤ_(p)`-algebra, a divided power structure is determined by its `p`th operation. -/
@[stacks 07GS "uniqueness"]
public lemma eq_iff_dpow_prime_eq {A : Type*} [CommRing A] {I : Ideal A} (p : ℕ)
    (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A))
    (γ γ' : _root_.DividedPowers I) :
    γ = γ' ↔ ∀ x : I, γ.dpow p x = γ'.dpow p x := by
  constructor
  · intro h x
    exact congrArg (fun d : _root_.DividedPowers I => d.dpow p (x : A)) h
  · intro hp_eq
    apply _root_.DividedPowers.ext
    intro n x hx
    induction n using Nat.strong_induction_on generalizing x with
    | h n ih =>
        by_cases hn0 : n = 0
        · subst n
          rw [γ.dpow_zero hx, γ'.dpow_zero hx]
        by_cases hn1 : n = 1
        · subst n
          rw [γ.dpow_one hx, γ'.dpow_one hx]
        by_cases hndvd : p ∣ n
        · obtain ⟨m, rfl⟩ := hndvd
          have hm0 : m ≠ 0 := by
            intro hm
            subst m
            exact hn0 rfl
          have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
          have hmn : m < p * m := by
            have hmul : 2 * m ≤ p * m := Nat.mul_le_mul_right m hp.two_le
            omega
          have key (d : _root_.DividedPowers I) :
              (Nat.uniformBell m p : A) * d.dpow (p * m) x =
                d.dpow m (d.dpow p x) := by
            simpa [Nat.mul_comm m p] using (d.dpow_comp (m := m) (n := p) hp.ne_zero hx).symm
          have hrec := ih m hmn (x := γ.dpow p (x : A)) (γ.dpow_mem hp.ne_zero hx)
          rw [hp_eq ⟨x, hx⟩] at hrec
          have hu : IsUnit (Nat.uniformBell m p : A) := hA _ (uniformBell_not_dvd hp)
          refine hu.mul_left_cancel ((key γ).trans (Eq.trans ?_ (key γ').symm))
          rw [hp_eq ⟨x, hx⟩, hrec]
        · have hu : IsUnit (n : A) := hA n hndvd
          have key (d : _root_.DividedPowers I) :
              (n : A) * d.dpow n x = d.dpow (n - 1) x * x := by
            have hmul := d.mul_dpow (m := n - 1) (n := 1) hx
            rw [d.dpow_one hx, Nat.sub_add_cancel (by omega), Nat.choose_symm (by omega)] at hmul
            simpa using hmul.symm
          exact hu.mul_left_cancel
            ((key γ).trans ((congrArg (· * x) (ih (n - 1) (by omega) hx)).trans (key γ').symm))

/-- A map satisfying the factorial, homogeneity, and addition identities for a `p`th divided
power operation extends uniquely to a divided power structure. -/
@[stacks 07GS "existence"]
public lemma existsUnique_of_prime_operation {A : Type*} [CommRing A] (I : Ideal A) (p : ℕ)
    (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) (δ : I → I)
    (factorial_mul : ∀ x : I, (p.factorial : A) * (δ x : A) = (x : A) ^ p)
    (smul : ∀ (a : A) (x : I), δ (a • x) = a ^ p • δ x)
    (add : ∀ x y : I,
      (δ (x + y) : A) = (δ x : A) +
        ∑ ij ∈ (antidiagonal p).filter (fun ij ↦ ij.1 ≠ 0 ∧ ij.2 ≠ 0),
          factorialInverse p hp hA ij.1 * factorialInverse p hp hA ij.2 *
            (x : A) ^ ij.1 * (y : A) ^ ij.2 +
        (δ y : A)) :
    ∃! γ : _root_.DividedPowers I, ∀ x : I, γ.dpow p x = δ x := by
  classical
  have lift := primeGamma_polynomial_lift p hp hA δ factorial_mul smul add
  have hadd (n : ℕ) (x y : A) (hx : x ∈ I) (hy : y ∈ I) :
      primeDpow p hp hA δ n (x + y) =
        ∑ k ∈ antidiagonal n, primeDpow p hp hA δ k.1 x * primeDpow p hp hA δ k.2 y := by
    obtain ⟨J, D, f, hf, v, hv, hD⟩ := lift ![⟨x, hx⟩, ⟨y, hy⟩]
    have he (n : ℕ) (z) (hz : z ∈ J) :
        f (D.dpow n z) = primeDpow p hp hA δ n (f z) := by
      rw [primeDpow_apply p hp hA δ n (hf z hz)]
      exact hD n z hz
    have hv0 : f (v 0) = x := hv 0
    have hv1 : f (v 1) = y := hv 1
    have H := congrArg f (D.dpow_add (n := n) (v 0).property (v 1).property)
    simp only [map_sum, map_mul] at H
    rw [he n _ (J.add_mem (v 0).property (v 1).property), map_add, hv0, hv1] at H
    simpa only [he _ _ (v 0).property, he _ _ (v 1).property, hv0, hv1] using H
  have hcomp (m n : ℕ) (hn : n ≠ 0) (x : A) (hx : x ∈ I) :
      primeDpow p hp hA δ m (primeDpow p hp hA δ n x) =
        (Nat.uniformBell m n : A) * primeDpow p hp hA δ (m * n) x := by
    obtain ⟨J, D, f, hf, v, hv, hD⟩ := lift (fun _ ↦ ⟨x, hx⟩)
    have he (n : ℕ) (z) (hz : z ∈ J) :
        f (D.dpow n z) = primeDpow p hp hA δ n (f z) := by
      rw [primeDpow_apply p hp hA δ n (hf z hz)]
      exact hD n z hz
    have hv0 : f (v 0) = x := hv 0
    have H := congrArg f (D.dpow_comp (m := m) hn (v 0).property)
    simp only [map_mul, map_natCast] at H
    rw [he m _ (D.dpow_mem hn (v 0).property), he n _ (v 0).property,
      he (m * n) _ (v 0).property, hv0] at H
    exact H
  let γ : _root_.DividedPowers I := {
    dpow := primeDpow p hp hA δ
    dpow_null := by intro n x hx; simp [primeDpow, hx]
    dpow_zero := primeDpow_zero p hp hA δ
    dpow_one := primeDpow_one p hp hA δ
    dpow_mem := by intro n x hn hx; exact primeDpow_mem p hp hA δ hn hx
    dpow_add := by intro n x y hx hy; exact hadd n x y hx hy
    dpow_mul := by intro n a x hx; exact primeDpow_smul p hp hA δ smul n a hx
    mul_dpow := by
      intro m n x hx
      simp only [primeDpow_apply p hp hA δ _ hx]
      exact primeGamma_mul_dpow p hp hA δ factorial_mul m n ⟨x, hx⟩
    dpow_comp := by intro m n x hn hx; exact hcomp m n hn x hx }
  have hγ : ∀ x : I, γ.dpow p x = δ x := fun x ↦ primeDpow_p p hp hA δ x.property
  refine ⟨γ, hγ, ?_⟩
  intro γ' hγ'
  exact (eq_iff_dpow_prime_eq p hp hA γ' γ).mpr (fun x ↦ (hγ' x).trans (hγ x).symm)

end DividedPowers
