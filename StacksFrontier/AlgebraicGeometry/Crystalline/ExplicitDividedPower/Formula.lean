module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.RingTheory.DividedPowers.Basic
public import Mathlib.Tactic.Module
public import StacksFrontier.RingTheory.DividedPowers.Criteria

/-!
# The explicit divided power operation on a second-order extension

Let `(A, I, γ)` be a divided power ring, let `M` and `N` be `A`-modules and let
`q : M →ₗ[A] M →ₗ[A] N` be a bilinear map.  A *second-order extension* of `A` by `q` is a
commutative ring `B` which is additively `A × (M × N)`, whose unit map is `a ↦ (a, 0, 0)` and
whose multiplication is
`(a, m, n) * (a', m', n') = (a a', a m' + a' m, a n' + a' n + q m m' + q m' m)`,
together with the ideal `J` of triples whose first coordinate lies in `I`.  On such a `B` the
divided powers of `J` are forced by the formula

`δ_n (a, m, n') = (γ_n a, γ_{n-1} a · m, γ_{n-1} a · n' + γ_{n-2} a · q m m)`

for `n ≥ 2`.  This file defines that operation and proves the identities it satisfies which do
not require comparison with a universal example: the degree-zero and degree-one values, that it
lands in `J`, the factorial identity, and the scalar rule `δ_n (a b) = aⁿ δ_n b`.

The remaining divided power axioms — additivity, the product rule and the composition rule —
each involve two elements of `J` or an iterated application, and are proved by transport from a
universal second-order extension.

## Main definitions

* `Crystalline.secondOrderExtensionDpow` — the explicit second-order divided power operation.

## Main results

* `Crystalline.secondOrderExtensionDpow_formula` — its value in degrees at least two.
* `Crystalline.secondOrderExtensionDpow_zero`, `Crystalline.secondOrderExtensionDpow_one`,
  `Crystalline.secondOrderExtensionDpow_mem`, `Crystalline.secondOrderExtensionDpow_null` —
  the unary axioms.
* `Crystalline.secondOrderExtensionDpow_mul` — the scalar rule.
* `Crystalline.exists_dividedPowers_secondOrderExtension_torsionFree` — over a torsion-free
  ring the factorial criterion already produces the divided power structure.

## Implementation notes

The extension is presented invariantly: instead of fixing a carrier, the statements take an
additive equivalence `e : B ≃+ A × (M × N)` together with hypotheses `halgebra` and `hmul`
pinning down the structure map and the multiplication in those coordinates, and a hypothesis
`hJ` pinning down the ideal.  This lets the results apply to any chosen implementation of the
extension while keeping all three coordinate formulas of the source.

The operation is defined on all of `B` by extending by zero outside `J`, which is the shape
Mathlib's `DividedPowers` structure expects.

## References

* [Stacks Project, Tag 07HI](https://stacks.math.columbia.edu/tag/07HI)
-/

@[expose] public section

namespace Crystalline

universe u v w x

noncomputable section

/-- Multiplying by a scalar from the base acts coordinatewise on a second-order extension. -/
private lemma algebraMap_mul_coords
    {A : Type u} [CommRing A]
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N)
    {B : Type x} [CommRing B] [Algebra A B]
    (e : B ≃+ A × (M × N))
    (halgebra : ∀ a : A, e (algebraMap A B a) = (a, (0, 0)))
    (hmul : ∀ b b' : B,
      e (b * b') =
        ((e b).1 * (e b').1,
          ((e b).1 • (e b').2.1 + (e b').1 • (e b).2.1,
            (e b).1 • (e b').2.2 + (e b').1 • (e b).2.2 +
              q (e b).2.1 (e b').2.1 + q (e b').2.1 (e b).2.1)))
    (a : A) (b : B) :
    e (algebraMap A B a * b) =
      (a * (e b).1, (a • (e b).2.1, a • (e b).2.2)) := by
  rw [hmul, halgebra]
  simp [LinearMap.map_zero]

/-- The coordinates of a power of exponent at least two in a second-order extension. -/
private lemma secondOrder_pow_coords
    {A : Type u} [CommRing A]
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N)
    {B : Type x} [CommRing B]
    (e : B ≃+ A × (M × N))
    (hmul : ∀ b b' : B,
      e (b * b') =
        ((e b).1 * (e b').1,
          ((e b).1 • (e b').2.1 + (e b').1 • (e b).2.1,
            (e b).1 • (e b').2.2 + (e b').1 • (e b).2.2 +
              q (e b).2.1 (e b').2.1 + q (e b').2.1 (e b).2.1)))
    (b : B) (n : ℕ) :
    e (b ^ (n + 2)) =
      (((e b).1) ^ (n + 2),
        ((n + 2 : A) • (((e b).1) ^ (n + 1) • (e b).2.1),
          (n + 2 : A) • (((e b).1) ^ (n + 1) • (e b).2.2) +
            ((n + 2 : A) * (n + 1 : A)) •
              (((e b).1) ^ n • q (e b).2.1 (e b).2.1))) := by
  induction n with
  | zero =>
      simp only [zero_add, zero_add, pow_two, pow_one, pow_zero, one_smul]
      rw [hmul]
      ext <;> simp [two_smul, smul_smul] <;> try module
  | succ n ih =>
      rw [show n + 1 + 2 = (n + 2) + 1 by omega, pow_succ, hmul, ih]
      ext <;> simp [pow_succ, map_smul, smul_add, smul_smul] <;> try module

/-- `n! · γ_{n-1} a = n · a^{n-1}` for an element of a divided power ideal. -/
private lemma factorial_mul_dpow_pred
    {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
    {a : A} (ha : a ∈ I) {n : ℕ} (hn : 0 < n) :
    (n.factorial : A) * γ.dpow (n - 1) a = (n : A) * a ^ (n - 1) := by
  rw [← Nat.mul_factorial_pred (by omega : n ≠ 0), Nat.cast_mul, mul_assoc,
    γ.factorial_mul_dpow_eq_pow ha]

/-- `n! · γ_{n-2} a = n (n-1) · a^{n-2}` for an element of a divided power ideal. -/
private lemma factorial_mul_dpow_pred_pred
    {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
    {a : A} (ha : a ∈ I) {n : ℕ} (hn : 2 ≤ n) :
    (n.factorial : A) * γ.dpow (n - 2) a =
      (n : A) * ((n - 1 : ℕ) : A) * a ^ (n - 2) := by
  have hpred : n - 1 ≠ 0 := by omega
  rw [← Nat.mul_factorial_pred (by omega : n ≠ 0),
    ← Nat.mul_factorial_pred hpred, Nat.cast_mul, Nat.cast_mul,
    Nat.sub_sub,
    mul_assoc, mul_assoc, γ.factorial_mul_dpow_eq_pow ha]
  simp only [show 1 + 1 = 2 by omega, mul_assoc]

/-- `a · γ_{n-1} a = n · γ_n a` for an element of a divided power ideal. -/
private lemma mul_dpow_pred
    {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
    {a : A} (ha : a ∈ I) {n : ℕ} (hn : 0 < n) :
    a * γ.dpow (n - 1) a = (n : A) * γ.dpow n a := by
  have h := γ.mul_dpow (m := 1) (n := n - 1) ha
  simpa [γ.dpow_one ha, Nat.choose_one_right,
    show 1 + (n - 1) = n by omega] using h

/-- Casting a natural-number identity `m + k = n` into a ring. -/
private lemma natCast_add_eq {A : Type u} [CommRing A] {m k n : ℕ} (h : m + k = n) :
    (m : A) + k = n := by
  rw [← h, Nat.cast_add]

/-- `a * a ^ m = a ^ n` when `m + 1 = n`. -/
private lemma mul_pow_eq_of_succ_eq {A : Type u} [CommRing A] (a : A) {m n : ℕ}
    (h : m + 1 = n) : a * a ^ m = a ^ n := by
  rw [← pow_succ', h]

/-- `b · γ_{n-2} b = (n-1) · γ_{n-1} b` for an element of a divided power ideal. -/
private lemma mul_dpow_pred_pred
    {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
    {b : A} (hb : b ∈ I) {n : ℕ} (hn : 2 ≤ n) :
    b * γ.dpow (n - 2) b = ((n - 1 : ℕ) : A) * γ.dpow (n - 1) b := by
  simpa only [show n - 1 - 1 = n - 2 by omega] using
    mul_dpow_pred γ hb (by omega : 0 < n - 1)

/-- The second-order divided power formula, read in the coordinates `A × (M × N)`. -/
public def secondOrderDpow
    {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N) (n : ℕ) (x : A × (M × N)) : A × (M × N) :=
  if _hn : n = 0 then (1, (0, 0)) else if _hn : n = 1 then x else
    (γ.dpow n x.1,
      (γ.dpow (n - 1) x.1 • x.2.1,
        γ.dpow (n - 1) x.1 • x.2.2 +
          γ.dpow (n - 2) x.1 • q x.2.1 x.2.1))

/-- In degree zero the coordinate formula is the unit. -/
private lemma secondOrderDpow_zero
    {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N) (x : A × (M × N)) :
    secondOrderDpow I γ q 0 x = (1, (0, 0)) := by
  simp [secondOrderDpow]

/-- In degree one the coordinate formula is the identity. -/
private lemma secondOrderDpow_one
    {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N) (x : A × (M × N)) :
    secondOrderDpow I γ q 1 x = x := by
  simp [secondOrderDpow]

/-- In degree at least two the coordinate formula is the displayed triple. -/
private lemma secondOrderDpow_of_two_le
    {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N) {n : ℕ} (hn : 2 ≤ n)
    (x : A × (M × N)) :
    secondOrderDpow I γ q n x =
      (γ.dpow n x.1,
        (γ.dpow (n - 1) x.1 • x.2.1,
          γ.dpow (n - 1) x.1 • x.2.2 +
            γ.dpow (n - 2) x.1 • q x.2.1 x.2.1)) := by
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  simp [secondOrderDpow, h0, h1]

/-- The divided power operation of a second-order extension: the explicit second-order
formula on the distinguished ideal `J`, extended by zero elsewhere. -/
public noncomputable def secondOrderExtensionDpow
    {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N)
    {B : Type x} [CommRing B] [Algebra A B]
    (e : B ≃+ A × (M × N)) (J : Ideal B)
    (n : ℕ) (b : B) : B :=
  open Classical in
    if _hb : b ∈ J then e.symm (secondOrderDpow I γ q n (e b)) else 0

/-- On the distinguished ideal the operation is the coordinate formula. -/
private lemma secondOrderExtensionDpow_of_mem
    {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N)
    {B : Type x} [CommRing B] [Algebra A B]
    (e : B ≃+ A × (M × N)) (J : Ideal B) {n : ℕ} {b : B} (hb : b ∈ J) :
    secondOrderExtensionDpow I γ q e J n b = e.symm (secondOrderDpow I γ q n (e b)) := by
  classical
  simp [secondOrderExtensionDpow, hb]

/-- Outside the distinguished ideal the operation vanishes. -/
public lemma secondOrderExtensionDpow_null
    {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N)
    {B : Type x} [CommRing B] [Algebra A B]
    (e : B ≃+ A × (M × N)) (J : Ideal B) {n : ℕ} {b : B}
    (hb : b ∉ J) : secondOrderExtensionDpow I γ q e J n b = 0 := by
  classical
  simp [secondOrderExtensionDpow, hb]

/-- In degree zero the operation takes the value one on the distinguished ideal. -/
public lemma secondOrderExtensionDpow_zero
    {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N)
    {B : Type x} [CommRing B] [Algebra A B]
    (e : B ≃+ A × (M × N)) (halgebra : ∀ a : A, e (algebraMap A B a) = (a, (0, 0)))
    (J : Ideal B) (_hJ : ∀ b : B, b ∈ J ↔ (e b).1 ∈ I)
    {b : B} (hb : b ∈ J) :
    secondOrderExtensionDpow I γ q e J 0 b = 1 := by
  rw [secondOrderExtensionDpow_of_mem I γ q e J hb, secondOrderDpow_zero]
  have h1 : e (1 : B) = (1, (0, 0)) := by
    simpa using (halgebra (1 : A))
  apply e.injective
  simp [h1, e.apply_symm_apply (1, (0, 0))]

/-- In degree one the operation is the identity on the distinguished ideal. -/
public lemma secondOrderExtensionDpow_one
    {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N)
    {B : Type x} [CommRing B] [Algebra A B]
    (e : B ≃+ A × (M × N)) (J : Ideal B)
    {b : B} (hb : b ∈ J) :
    secondOrderExtensionDpow I γ q e J 1 b = b := by
  rw [secondOrderExtensionDpow_of_mem I γ q e J hb, secondOrderDpow_one]
  exact e.symm_apply_apply b

/-- In positive degree the operation maps the distinguished ideal into itself. -/
public lemma secondOrderExtensionDpow_mem
    {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N)
    {B : Type x} [CommRing B] [Algebra A B]
    (e : B ≃+ A × (M × N)) (J : Ideal B)
    (hJ : ∀ b : B, b ∈ J ↔ (e b).1 ∈ I)
    {n : ℕ} (hn : n ≠ 0) {b : B} (hb : b ∈ J) :
    secondOrderExtensionDpow I γ q e J n b ∈ J := by
  rw [secondOrderExtensionDpow_of_mem I γ q e J hb]
  apply (hJ _).2
  have hcoord := e.apply_symm_apply (secondOrderDpow I γ q n (e b))
  rw [hcoord]
  show (secondOrderDpow I γ q n (e b)).1 ∈ I
  by_cases h1 : n = 1
  · subst n
    simp [secondOrderDpow, (hJ b).1 hb]
  · rw [secondOrderDpow_of_two_le I γ q (by omega)]
    exact γ.dpow_mem hn ((hJ b).1 hb)

/-- The value of the operation in degree at least two, in the coordinates `A × (M × N)`. -/
public lemma secondOrderExtensionDpow_formula
    {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N)
    {B : Type x} [CommRing B] [Algebra A B]
    (e : B ≃+ A × (M × N)) (J : Ideal B)
    {n : ℕ} (hn : 2 ≤ n) {b : B} (hb : b ∈ J) :
    secondOrderExtensionDpow I γ q e J n b =
      e.symm (γ.dpow n (e b).1,
        (γ.dpow (n - 1) (e b).1 • (e b).2.1,
          γ.dpow (n - 1) (e b).1 • (e b).2.2 +
            γ.dpow (n - 2) (e b).1 • q (e b).2.1 (e b).2.1)) := by
  rw [secondOrderExtensionDpow_of_mem I γ q e J hb,
    secondOrderDpow_of_two_le I γ q hn]

/-- The factorial identity `n! · δ_n b = bⁿ` in degree at least two. -/
private lemma secondOrderExtensionDpow_factorial
    {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N)
    {B : Type x} [CommRing B] [Algebra A B]
    (e : B ≃+ A × (M × N))
    (halgebra : ∀ a : A, e (algebraMap A B a) = (a, (0, 0)))
    (hmul : ∀ b b' : B,
      e (b * b') =
        ((e b).1 * (e b').1,
          ((e b).1 • (e b').2.1 + (e b').1 • (e b).2.1,
            (e b).1 • (e b').2.2 + (e b').1 • (e b).2.2 +
              q (e b).2.1 (e b').2.1 + q (e b').2.1 (e b).2.1)))
    (J : Ideal B) (hJ : ∀ b : B, b ∈ J ↔ (e b).1 ∈ I)
    {n : ℕ} (hn : 2 ≤ n) {b : B} (hb : b ∈ J) :
    (n.factorial : B) * secondOrderExtensionDpow I γ q e J n b = b ^ n := by
  apply e.injective
  have hcast : (n.factorial : B) = algebraMap A B (n.factorial : A) := by simp
  rw [hcast, algebraMap_mul_coords q e halgebra hmul,
    secondOrderExtensionDpow_formula I γ q e J hn hb]
  simp only [e.apply_symm_apply]
  have hn0 : n - 2 + 2 = n := by omega
  have hn1 : n - 2 + 1 = n - 1 := by omega
  rw [← hn0, secondOrder_pow_coords q e hmul b (n - 2), hn0, hn1]
  have hc0 : ((n - 2 : ℕ) : A) + 2 = (n : A) := by
    exact_mod_cast natCast_add_eq (show n - 2 + 2 = n by omega)
  have hc1 : ((n - 2 : ℕ) : A) + 1 = ((n - 1 : ℕ) : A) := by
    exact_mod_cast natCast_add_eq (show n - 2 + 1 = n - 1 by omega)
  have ha : (e b).1 ∈ I := (hJ b).1 hb
  ext
  · exact γ.factorial_mul_dpow_eq_pow ha
  · simp only [smul_smul]
    rw [factorial_mul_dpow_pred γ ha (by omega : 0 < n)]
    rw [hc0]
  · simp only [smul_add, smul_smul]
    rw [factorial_mul_dpow_pred γ ha (by omega : 0 < n),
      factorial_mul_dpow_pred_pred γ ha hn]
    rw [hc0, hc1]

/-- The operation as a family of maps of the distinguished ideal to itself, which is the shape
the factorial criterion for divided powers expects. -/
private noncomputable def secondOrderExtensionDpowSubtype
    {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N)
    {B : Type x} [CommRing B] [Algebra A B]
    (e : B ≃+ A × (M × N)) (J : Ideal B)
    (hJ : ∀ b : B, b ∈ J ↔ (e b).1 ∈ I) : ℕ → J → J :=
  fun n b => if hn : n = 0 then 0 else
    ⟨secondOrderExtensionDpow I γ q e J n b,
      secondOrderExtensionDpow_mem I γ q e J hJ hn b.property⟩

/-- In positive degree the subtype-valued family agrees with the operation. -/
private lemma secondOrderExtensionDpowSubtype_pos
    {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N)
    {B : Type x} [CommRing B] [Algebra A B]
    (e : B ≃+ A × (M × N)) (J : Ideal B)
    (hJ : ∀ b : B, b ∈ J ↔ (e b).1 ∈ I)
    {n : ℕ} (hn : 0 < n) (b : J) :
    ((secondOrderExtensionDpowSubtype I γ q e J hJ n b : J) : B) =
      secondOrderExtensionDpow I γ q e J n b := by
  simp [secondOrderExtensionDpowSubtype, Nat.ne_of_gt hn]

/-- The factorial identity for the subtype-valued family, in every positive degree. -/
private lemma secondOrderExtensionDpowSubtype_factorial
    {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N)
    {B : Type x} [CommRing B] [Algebra A B]
    (e : B ≃+ A × (M × N))
    (halgebra : ∀ a : A, e (algebraMap A B a) = (a, (0, 0)))
    (hmul : ∀ b b' : B,
      e (b * b') =
        ((e b).1 * (e b').1,
          ((e b).1 • (e b').2.1 + (e b').1 • (e b).2.1,
            (e b).1 • (e b').2.2 + (e b').1 • (e b).2.2 +
              q (e b).2.1 (e b').2.1 + q (e b').2.1 (e b).2.1)))
    (J : Ideal B) (hJ : ∀ b : B, b ∈ J ↔ (e b).1 ∈ I)
    {n : ℕ} (hn : 0 < n) (b : J) :
    (n.factorial : B) *
      (secondOrderExtensionDpowSubtype I γ q e J hJ n b : B) = (b : B) ^ n := by
  rw [secondOrderExtensionDpowSubtype_pos I γ q e J hJ hn b]
  by_cases h1 : n = 1
  · subst n
    rw [secondOrderExtensionDpow_one I γ q e J b.property]
    norm_num
  · exact secondOrderExtensionDpow_factorial I γ q e halgebra hmul J hJ
      (by omega) b.property

/-- Over a torsion-free ring the factorial identity already determines a divided power
structure on the distinguished ideal of a second-order extension, with the explicit
second-order formula in degrees at least two. -/
public theorem exists_dividedPowers_secondOrderExtension_torsionFree
    {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N)
    {B : Type x} [CommRing B] [Algebra A B] [Module.IsTorsionFree ℤ B]
    (e : B ≃+ A × (M × N))
    (halgebra : ∀ a : A, e (algebraMap A B a) = (a, (0, 0)))
    (hmul : ∀ b b' : B,
      e (b * b') =
        ((e b).1 * (e b').1,
          ((e b).1 • (e b').2.1 + (e b').1 • (e b).2.1,
            (e b).1 • (e b').2.2 + (e b').1 • (e b).2.2 +
              q (e b).2.1 (e b').2.1 + q (e b').2.1 (e b).2.1)))
    (J : Ideal B) (hJ : ∀ b : B, b ∈ J ↔ (e b).1 ∈ I) :
    ∃ δ : DividedPowers J,
      ∀ (n : ℕ) (b : B), 2 ≤ n → b ∈ J →
        δ.dpow n b = e.symm
          (γ.dpow n (e b).1,
            (γ.dpow (n - 1) (e b).1 • (e b).2.1,
              γ.dpow (n - 1) (e b).1 • (e b).2.2 +
                γ.dpow (n - 2) (e b).1 • q (e b).2.1 (e b).2.1)) := by
  let γ' := secondOrderExtensionDpowSubtype I γ q e J hJ
  obtain ⟨δ, hδ⟩ :=
    (DividedPowers.exists_dividedPowers_iff_factorial_mul_eq_pow J γ').2 (by
        intro n b hn
        exact secondOrderExtensionDpowSubtype_factorial I γ q e halgebra hmul J hJ hn b)
  refine ⟨δ, ?_⟩
  intro n b hn hb
  calc
    δ.dpow n b = (γ' n ⟨b, hb⟩ : B) := hδ n ⟨b, hb⟩ (by omega)
    _ = secondOrderExtensionDpow I γ q e J n b :=
      secondOrderExtensionDpowSubtype_pos I γ q e J hJ (by omega) ⟨b, hb⟩
    _ = _ := secondOrderExtensionDpow_formula I γ q e J hn hb

/-- Reassembling `a² · a^{n-2}` as `aⁿ`. -/
private lemma secondOrderScalarPow
    {A : Type u} [CommRing A] (a d : A) {n : ℕ} (hn : 2 ≤ n) :
    a ^ 2 * a ^ (n - 2) * d = a ^ n * d := by
  rw [← pow_add, show 2 + (n - 2) = n by omega]

/-- The cross term arising from the scalar rule in the middle coordinate. -/
private lemma secondOrderScalarCross
    {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
    {b : A} (hb : b ∈ I) (a : A) {n : ℕ} (hn : 2 ≤ n) :
    a * a ^ (n - 2) * γ.dpow (n - 2) b * b +
        a ^ (n - 1) * γ.dpow (n - 1) b =
      a ^ (n - 1) * γ.dpow (n - 1) b * (n : A) := by
  have hp : a * a ^ (n - 2) = a ^ (n - 1) := mul_pow_eq_of_succ_eq a (by omega)
  have hd := mul_dpow_pred_pred γ hb hn
  have hc : ((n - 1 : ℕ) : A) + 1 = (n : A) := by
    exact_mod_cast natCast_add_eq (show n - 1 + 1 = n by omega)
  linear_combination γ.dpow (n - 2) b * b * hp + a ^ (n - 1) * hd +
    a ^ (n - 1) * γ.dpow (n - 1) b * hc

/-- The quadratic term arising from the scalar rule in the last coordinate. -/
private lemma secondOrderScalarDouble
    {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
    {b : A} (hb : b ∈ I) (a : A) {n : ℕ} (hn : 2 ≤ n) :
    a ^ (n - 2) * γ.dpow (n - 2) b * b ^ 2 =
      a ^ (n - 2) * γ.dpow n b * (n : A) * ((n - 1 : ℕ) : A) := by
  have hd := mul_dpow_pred_pred γ hb hn
  have hd' := mul_dpow_pred γ hb (by omega : 0 < n)
  linear_combination a ^ (n - 2) * b * hd + a ^ (n - 2) * ((n - 1 : ℕ) : A) * hd'

/-- The scalar rule `δ_n (a b) = aⁿ δ_n b` in degree at least two. -/
public lemma secondOrderExtensionDpow_mul
    {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N)
    {B : Type x} [CommRing B] [Algebra A B]
    (e : B ≃+ A × (M × N))
    (_halgebra : ∀ a : A, e (algebraMap A B a) = (a, (0, 0)))
    (hmul : ∀ b b' : B,
      e (b * b') =
        ((e b).1 * (e b').1,
          ((e b).1 • (e b').2.1 + (e b').1 • (e b).2.1,
            (e b).1 • (e b').2.2 + (e b').1 • (e b).2.2 +
              q (e b).2.1 (e b').2.1 + q (e b').2.1 (e b).2.1)))
    (J : Ideal B) (hJ : ∀ b : B, b ∈ J ↔ (e b).1 ∈ I)
    {n : ℕ} (hn : 2 ≤ n) (a : B) {b : B} (hb : b ∈ J) :
    secondOrderExtensionDpow I γ q e J n (a * b) =
      a ^ n * secondOrderExtensionDpow I γ q e J n b := by
  have hab : a * b ∈ J := J.mul_mem_left a hb
  have hbA : (e b).1 ∈ I := (hJ b).1 hb
  apply e.injective
  rw [secondOrderExtensionDpow_formula I γ q e J hn hab,
    secondOrderExtensionDpow_formula I γ q e J hn hb]
  simp only [e.apply_symm_apply, hmul]
  rw [show n = n - 2 + 2 by omega, secondOrder_pow_coords q e hmul a (n - 2)]
  simp only [show n - 2 + 2 = n by omega, show n - 2 + 1 = n - 1 by omega]
  have hp1 : (e a).1 * (e a).1 ^ (n - 1) = (e a).1 ^ n :=
    mul_pow_eq_of_succ_eq _ (by omega)
  have hcast : ((n - 2 : ℕ) : A) + 2 = (n : A) := by
    exact_mod_cast natCast_add_eq (show n - 2 + 2 = n by omega)
  have hcast' : ((n - 2 : ℕ) : A) + 1 = ((n - 1 : ℕ) : A) := by
    exact_mod_cast natCast_add_eq (show n - 2 + 1 = n - 1 by omega)
  have hγ1 := mul_dpow_pred γ hbA (by omega : 0 < n)
  have hc : (e a).1 ^ (n - 1) * γ.dpow (n - 1) (e b).1 * (e b).1 =
      γ.dpow n (e b).1 * ((n : A) * (e a).1 ^ (n - 1)) := by
    linear_combination (e a).1 ^ (n - 1) * hγ1
  have hcoef : (e a).1 ^ (n - 1) * γ.dpow (n - 1) (e b).1 * (e a).1 =
      (e a).1 ^ n * γ.dpow (n - 1) (e b).1 := by
    linear_combination γ.dpow (n - 1) (e b).1 * hp1
  ext
  · exact γ.dpow_mul hbA
  · simp only [γ.dpow_mul hbA, smul_add, smul_smul]
    simp only [hcast]
    simp only [hc, hcoef]
  · simp only [γ.dpow_mul hbA, smul_add, smul_smul, q.map_add, q.map_smulₛₗ]
    simp only [hcast, hcast']
    simp only [hc, hcoef]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      RingHom.id_apply, smul_add, smul_smul]
    run_tac do
      let goals ← Mathlib.Tactic.Module.matchScalars (← Lean.Elab.Tactic.getMainGoal)
      Lean.Elab.Tactic.setGoals goals
    all_goals try simp only [mul_one]
    all_goals try ring_nf
    all_goals first
    | exact secondOrderScalarCross γ ((hJ b).1 hb) (e a).1 hn
    | exact secondOrderScalarDouble γ ((hJ b).1 hb) (e a).1 hn
    | exact secondOrderScalarPow (e a).1 (γ.dpow (n - 2) (e b).1) hn

end

end Crystalline

end
