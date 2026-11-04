module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.IntegralClosure.Algebra.Ideal
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.Tactic.LinearCombination
public import StacksCore.LinearAlgebra.Matrix.CommSemiring
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Lifting idempotents along an integral ring map

Stacks Tag 09XG, Lemma 15.9.9.

Let `A` be a commutative ring, `I ⊆ A` an ideal, and `A → B` an integral ring map
(so `B` is a commutative `A`-algebra and `Algebra.IsIntegral A B` holds). Let `b ∈ B`
be such that its image `b̄ ∈ B / IB` is idempotent, i.e. `b̄ ^ 2 = b̄` in `B / IB`.
Then there exist an integer `d ≥ 1` and a monic polynomial `f ∈ A[X]` such that:

1. `f(b) = 0` in `B` (i.e. `Polynomial.aeval b f = 0`), and
2. `f mod I = X ^ d * (X - 1) ^ d` in `(A / I)[X]`.

Here `X ^ d * (X - 1) ^ d` denotes the polynomial `X ^ d * (X - 1) ^ d` over `A / I`,
where `X` is the indeterminate and `1` is the multiplicative identity of `A / I`.
-/

/-!
## Notation and conventions

* `A` is a commutative ring and `I ⊆ A` is an ideal.
* `A → B` is a ring homomorphism making `B` a commutative `A`-algebra
  (`algebraMap A B`); for `f ∈ A[X]` we write `f(b)` for `Polynomial.aeval b f`.
* `IB` denotes the extension `Ideal.map (algebraMap A B) I` of `I` along `A → B`,
  and the quotient `B / IB` is the corresponding quotient ring.
* `f mod I` denotes the image of `f` under the coefficientwise reduction map
  `A[X] → (A / I)[X]`, namely `Polynomial.map (algebraMap A (A ⧸ I))`.
* A polynomial `f ∈ A[X]` is monic (`Polynomial.Monic`) if its leading coefficient
  is `1`.

"`b` maps to an idempotent in `B / IB`", i.e. `b̄ ^ 2 = b̄`, is equivalent (and we use
this form below) to the membership `b ^ 2 - b ∈ Ideal.map (algebraMap A B) I`.

The only nontrivial cited input is Stacks Tag 00H5, available in Mathlib as
`Polynomial.exists_monic_aeval_eq_zero_forall_mem_of_mem_map`.
-/

open Polynomial

/-- Stacks Tag 09XG, Lemma 15.9.9.

If `A → B` is an integral ring map, `I ⊆ A` is an ideal, and `b ∈ B` maps to an
idempotent in `B / IB` (equivalently, `b ^ 2 - b ∈ IB`), then there exist `d ≥ 1`
and a monic polynomial `f ∈ A[X]` with `f(b) = 0` and `f mod I = X ^ d * (X - 1) ^ d`
in `(A / I)[X]`. -/
@[stacks 09XG]
theorem exists_monic_aeval_eq_zero_map_eq_of_sq_sub_mem_map
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
    (I : Ideal A) (b : B)
    (hb : b ^ 2 - b ∈ Ideal.map (algebraMap A B) I) :
    ∃ d : ℕ, 1 ≤ d ∧ ∃ f : A[X], f.Monic ∧ aeval b f = 0 ∧
      f.map (algebraMap A (A ⧸ I)) =
        (Polynomial.X ^ d * (Polynomial.X - 1) ^ d : (A ⧸ I)[X]) := by
  -- The reduction mod `I` of `X^2 - X`.
  have hx : (Polynomial.X ^ 2 - Polynomial.X : A[X]).map (algebraMap A (A ⧸ I))
      = Polynomial.X ^ 2 - Polynomial.X := by
    rw [Polynomial.map_sub, Polynomial.map_pow, map_X]
  -- Case split on whether `B` is trivial.
  by_cases hB : Subsingleton B
  · -- Trivial `B`: every equation in `B` holds; take `d = 1`, `f = X^2 - X`,
    -- whose reduction mod `I` is `X * (X-1) = X^1 * (X-1)^1`.
    refine ⟨1, le_refl 1, Polynomial.X ^ 2 - Polynomial.X, by monicity!, by subsingleton, ?_⟩
    rw [hx]
    ring
  · -- Nontrivial `B`, hence (via `algebraMap A B`) nontrivial `A`.
    rw [not_subsingleton_iff_nontrivial] at hB
    have : Nontrivial B := hB
    have : Nontrivial A := (algebraMap A B).domain_nontrivial
    -- Apply Stacks Tag 00H5 to `z := b^2 - b ∈ IB` to obtain a
    -- monic `h ∈ A[X]` with `aeval (b^2-b) h = 0` and all non-leading coeffs of `h` in `I`.
    obtain ⟨h, hm, haeval, hc⟩ :=
      Polynomial.exists_monic_aeval_eq_zero_forall_mem_of_mem_map (R := A) (S := B)
        (I := I) (x := b ^ 2 - b) hb
    -- `d := h.natDegree ≥ 1`: otherwise `h = 1`, so `aeval (b^2-b) 1 = 1 = 0` in a
    -- nontrivial ring, a contradiction.
    have hd : 1 ≤ h.natDegree := by
      by_contra hlt
      push Not at hlt
      have hdeg0 : h.natDegree = 0 := Nat.lt_one_iff.mp hlt
      have h1 : h = 1 := hm.natDegree_eq_zero.mp hdeg0
      rw [h1] at haeval
      simp at haeval
    -- Reduction mod `I`: since the lower coefficients of `h` lie in `I` and the
    -- leading coefficient is `1`, `h mod I = X^d` coefficientwise.
    have hmap : h.map (algebraMap A (A ⧸ I)) = Polynomial.X ^ h.natDegree := by
      have key : (algebraMap A (A ⧸ I)) = (Ideal.Quotient.mk I : A →+* A ⧸ I) := rfl
      ext i
      rw [coeff_map, coeff_X_pow, key]
      by_cases hi : i = h.natDegree
      · subst hi; rw [ite_eq_left rfl, hm.coeff_natDegree]; simp
      · rw [ite_eq_right hi, Ideal.Quotient.eq_zero_iff_mem.mpr (hc i hi)]
    -- The witness: `f := h(X^2 - X) = h.comp (X^2 - X)`.
    refine ⟨h.natDegree, hd, h.comp (Polynomial.X ^ 2 - Polynomial.X), ?_, ?_, ?_⟩
    · -- `f` is monic: composition of the monic `h` with the monic `X^2 - X`
      -- (whose degree `2 ≠ 0`).
      apply Monic.comp hm (by monicity!)
      have : (Polynomial.X ^ 2 - Polynomial.X : A[X]).natDegree = 2 := by compute_degree!
      omega
    · -- `f(b) = h(b^2 - b) = h(z) = 0`.
      rw [aeval_comp]
      have : aeval b (Polynomial.X ^ 2 - Polynomial.X : A[X]) = b ^ 2 - b := by simp
      rw [this, haeval]
    · -- `f mod I = (X^2 - X)^d = X^d (X-1)^d`.
      rw [Polynomial.map_comp, hmap, hx, pow_comp, X_comp,
        show (Polynomial.X ^ 2 - Polynomial.X : (A ⧸ I)[X]) = Polynomial.X * (Polynomial.X - 1)
          by ring, mul_pow]

/-!
## Idempotents modulo an ideal
-/

/-- **Definition 3 (Jacobson radical, containment).** The Jacobson radical of
`A` is `(⊥ : Ideal A).jacobson`, the intersection of all maximal ideals. An
ideal `I` is *contained in the Jacobson radical* if `I ≤ (⊥ : Ideal A).jacobson`.
-/
def IsContainedInJacobson {A : Type*} [CommRing A] (I : Ideal A) : Prop :=
  I ≤ (⊥ : Ideal A).jacobson

/-- The map on idempotents induced by the reduction `A → A ⧸ I`, sending `e` to `ē`. -/
@[ega "IV 18.5.16" "special case"]
def idemMap {A : Type*} [CommRing A] (I : Ideal A) :
    {e : A // IsIdempotentElem e} → {e : A ⧸ I // IsIdempotentElem e} :=
  fun e => ⟨Ideal.Quotient.mk I e.val, e.property.map _⟩

/-- The phrase "`A → A/I` induces a bijection on idempotents" means the map
`idemMap I` is a bijection. -/
def InducesBijectionOnIdempotents {A : Type*} [CommRing A] (I : Ideal A) : Prop :=
  Function.Bijective (idemMap I)

/-- The underlying element of `idemMap I e` is the class of `e` in `A ⧸ I`. -/
@[simp]
theorem idemMap_val {A : Type*} [CommRing A] (I : Ideal A)
    (e : {e : A // IsIdempotentElem e}) : (idemMap I e).val = Ideal.Quotient.mk I e.val :=
  rfl

/-- Idempotents that agree modulo an ideal contained in the Jacobson radical are
equal. (Uniqueness of idempotent lifts mod the Jacobson radical.) -/
theorem IsIdempotentElem.eq_of_sub_mem_jacobson {A : Type*} [CommRing A] {e f : A}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (h : e - f ∈ (⊥ : Ideal A).jacobson) : e = f := by
  set x := e - f with hx
  have he' : e * e = e := he
  have hf' : f * f = f := hf
  have hcube : x ^ 3 = x := by
    simp only [hx]
    linear_combination (e + 1 - 3 * f) * he' + (3 * e - f - 1) * hf'
  rw [Ideal.mem_jacobson_bot] at h
  have hu := h (-x)
  have hzero : x * (x * -x + 1) = 0 := by linear_combination -hcube
  obtain ⟨u, hu'⟩ := hu
  have hxu : x * (u : A) = 0 := by rw [hu']; exact hzero
  have hx0 : x = 0 := by
    have : x * (u : A) * (↑u⁻¹ : A) = 0 := by rw [hxu]; ring
    rwa [mul_assoc, Units.mul_inv, mul_one] at this
  exact sub_eq_zero.mp hx0

/-- The map on idempotents is injective when `I` is contained in the Jacobson
radical of `A`. -/
@[stacks 09XF, ega "IV 18.5.16" "partial"]
theorem idemMap_injective {A : Type*} [CommRing A] (I : Ideal A)
    (hI : IsContainedInJacobson I) : Function.Injective (idemMap I) := by
  rintro ⟨e, he⟩ ⟨f, hf⟩ hef
  simp only [idemMap, Subtype.mk.injEq] at hef ⊢
  have hmem : e - f ∈ I := Ideal.Quotient.eq.mp hef
  exact he.eq_of_sub_mem_jacobson hf (hI hmem)
