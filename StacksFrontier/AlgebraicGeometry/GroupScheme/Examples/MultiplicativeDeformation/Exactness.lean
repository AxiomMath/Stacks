module

public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AbsolutelyIntegrallyClosed.MonogenicPresentation
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.Constant
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.MultiplicativeDeformation.CoordinateRing

/-!
# A deformation of the multiplicative group: exactness on points and flatness

Let `ζ` be an `ℓ`-th root of unity in `A` for which `X ^ ℓ - 1` splits as the product of the
`X - ζ ^ i`, and put `π = ζ - 1`. This file proves that `f : G^{(π)} → G^{(π ^ ℓ)}` is additive
on points, that it is faithfully flat, and that for `ℓ` prime the points `σ_i` exhibit the
constant group scheme of `ℤ/ℓℤ` as its kernel. The additivity of `Φ` on points is a
`q`-analogue of the binomial theorem, proved first.

## Main results

* `AlgebraicGeometry.MultiplicativeDeformation.isogenyOnPoints_add` says that `f` is a morphism
  of group schemes.
* `AlgebraicGeometry.MultiplicativeDeformation.constantPoint_add` says that `i ↦ σ_i` is a
  homomorphism from `ℤ/ℓℤ` to the `A`-points of `G^{(π)}`, and
  `AlgebraicGeometry.MultiplicativeDeformation.isogenyOnPoints_constantPoint` that its image
  lies in the kernel of `f`.
* `AlgebraicGeometry.MultiplicativeDeformation.kernelCoordinateRing_algEquiv_pi` is exactness
  at `G^{(π)}`: for `ℓ` prime the closed immersion of the constant group scheme of `ℤ/ℓℤ` into
  the kernel of `f` determined by the `σ_i` is an isomorphism.
* `AlgebraicGeometry.MultiplicativeDeformation.isogeny_faithfullyFlat` is exactness at
  `G^{(π ^ ℓ)}`.

## Implementation notes

The source fixes the cyclotomic ring `A = ℤ[x]/(x ^ (ℓ - 1) + ⋯ + 1)` and `π = ζ - 1`. That
fixed base is replaced here by the two properties of `ζ` the construction uses: `ζ ^ ℓ = 1` and
the splitting of `X ^ ℓ - 1` into the linear factors `X - ζ ^ i`. Both hold in the source's
`A`; when `ℓ > 1`, the splitting forces `1 + ζ + ⋯ + ζ ^ (ℓ - 1) = 0`, so such an `A` is an
algebra over the cyclotomic ring. Only exactness at `G^{(π)}` needs `ℓ` prime, so primality is
a hypothesis of that statement alone: for composite `ℓ` the differences `σ_i - σ_j` need not be
units and the kernel is not constant.

The kernel of `f` is its fibre over the origin of `G^{(π ^ ℓ)}`, that is the quotient of the
coordinate ring of `G^{(π)}` by the image of the generator, which is `Φ(s)`. The constant group
scheme of `ℤ/ℓℤ` over `Spec A` is affine over the base, with coordinate ring the `A`-algebra
`ZMod ℓ → A` of functions on `ℤ/ℓℤ`; the closed immersion of the source is dual to the
`A`-algebra map sending `s` to `i ↦ σ_i`, and exactness at `G^{(π)}` says that this map is an
isomorphism.

## References

* [Stacks Project, Tag 0GY4](https://stacks.math.columbia.edu/tag/0GY4)
-/

@[expose] public section

open Polynomial TensorProduct CategoryTheory CategoryTheory.Limits
  CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

universe u v

namespace AlgebraicGeometry.MultiplicativeDeformation

variable {A : Type u} [CommRing A]

/-! ### The `q`-falling factorial

The additivity of `Φ` on points is a `q`-analogue of the binomial theorem: writing `q` for `ζ`
and `[k]_q = 1 + q + ⋯ + q ^ (k - 1)`, the polynomial `Φ` is the `q`-falling factorial
`∏_{i < ℓ} (x - [i]_q)`, and its value at a sum `πxy + x + y` expands with `q`-binomial
coefficients. When `X ^ ℓ - 1` splits, all the intermediate coefficients vanish and the
expansion collapses to the two outer terms.
-/

/-- The `q`-binomial coefficient, defined by the Pascal recursion
`c (n + 1) (k + 1) = c n k + q ^ (k + 1) * c n (k + 1)`. -/
private def qChoose (q : A) : ℕ → ℕ → A
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => qChoose q n k + q ^ (k + 1) * qChoose q n (k + 1)

private lemma qChoose_zero (q : A) (n : ℕ) : qChoose q n 0 = 1 := by
  cases n <;> rfl

private lemma qChoose_eq_zero (q : A) {n k : ℕ} (h : n < k) : qChoose q n k = 0 := by
  induction n generalizing k with
  | zero => cases k <;> simp_all [qChoose]
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k => rw [qChoose, ih (by omega), ih (by omega)]; simp

private lemma qChoose_self (q : A) (n : ℕ) : qChoose q n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [qChoose, ih, qChoose_eq_zero q (by omega)]; simp

private lemma qChoose_convolution (q : A) (n : ℕ) (a b : ℕ → A)
    (h : ∀ k, k ≤ n → a k = b (k + 1) + q ^ k * b k) :
    (∑ k ∈ Finset.range (n + 1), qChoose q n k * a k) =
      ∑ k ∈ Finset.range (n + 2), qChoose q (n + 1) k * b k := by
  rw [Finset.sum_congr rfl (fun k hk => congrArg (qChoose q n k * ·)
    (h k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))))]
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [Finset.sum_range_succ' (f := fun k => qChoose q (n + 1) k * b k)]
  simp only [qChoose, one_mul]
  simp_rw [add_mul, Finset.sum_add_distrib]
  have he : (∑ k ∈ Finset.range (n + 1), qChoose q n k * (q ^ k * b k)) =
      (∑ k ∈ Finset.range (n + 1), q ^ (k + 1) * qChoose q n (k + 1) * b (k + 1)) + b 0 := by
    rw [Finset.sum_range_succ' (f := fun k => qChoose q n k * (q ^ k * b k)),
      Finset.sum_range_succ (f := fun k => q ^ (k + 1) * qChoose q n (k + 1) * b (k + 1))]
    simp only [qChoose_eq_zero q (Nat.lt_succ_self n), mul_zero, zero_mul, add_zero,
      qChoose_zero, pow_zero, one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [he]
  ring

/-- Splitting a geometric sum of length `a + b` into its first `a` terms and a shifted tail. -/
private lemma geom_sum_range_add (q : A) (a b : ℕ) :
    (∑ k ∈ Finset.range (a + b), q ^ k) =
      (∑ k ∈ Finset.range a, q ^ k) + q ^ a * ∑ k ∈ Finset.range b, q ^ k := by
  rw [Finset.sum_range_add, Finset.mul_sum]
  simp_rw [pow_add]

/-- The `q`-falling factorial `∏_{i < n} (x - [i]_q)`. -/
private def falling (q : A) (n : ℕ) (x : A) : A :=
  ∏ i ∈ Finset.range n, (x - ∑ j ∈ Finset.range i, q ^ j)

private lemma falling_succ (q x : A) (n : ℕ) :
    falling q (n + 1) x = falling q n x * (x - ∑ j ∈ Finset.range n, q ^ j) :=
  Finset.prod_range_succ _ _

private lemma falling_zero (q x : A) : falling q 0 x = 1 := by simp [falling]

private lemma falling_add (q x y : A) (n : ℕ) :
    falling q n ((q - 1) * x * y + x + y) =
      ∑ k ∈ Finset.range (n + 1), qChoose q n k *
        ((q - 1) * y + 1) ^ k * falling q k x * falling q (n - k) y := by
  let w := (q - 1) * y + 1
  induction n with
  | zero => simp [falling_zero, qChoose]
  | succ n ih =>
    rw [falling_succ, ih, Finset.sum_mul]
    have step (k : ℕ) (hk : k ≤ n) :
        ((q - 1) * x * y + x + y) - (∑ j ∈ Finset.range n, q ^ j) =
          w * (x - ∑ j ∈ Finset.range k, q ^ j) +
            q ^ k * (y - ∑ j ∈ Finset.range (n - k), q ^ j) := by
      have hsum : (∑ j ∈ Finset.range n, q ^ j) =
          (∑ j ∈ Finset.range k, q ^ j) + q ^ k *
            (∑ j ∈ Finset.range (n - k), q ^ j) := by
        simpa [Nat.add_sub_of_le hk] using geom_sum_range_add q k (n - k)
      have hgeom := geom_sum_mul q k
      rw [hsum]
      dsimp [w]
      linear_combination y * hgeom
    have hrec : ∀ k, k ≤ n →
        w ^ k * falling q k x * falling q (n - k) y *
          (((q - 1) * x * y + x + y) - ∑ j ∈ Finset.range n, q ^ j) =
        w ^ (k + 1) * falling q (k + 1) x * falling q (n + 1 - (k + 1)) y +
          q ^ k * (w ^ k * falling q k x * falling q (n + 1 - k) y) := by
      intro k hk
      rw [step k hk, show n + 1 - (k + 1) = n - k by omega,
        show n + 1 - k = (n - k) + 1 by omega, falling_succ, falling_succ, pow_succ]
      ring
    calc
      _ = ∑ k ∈ Finset.range (n + 1), qChoose q n k *
          (w ^ k * falling q k x * falling q (n - k) y *
            (((q - 1) * x * y + x + y) - ∑ j ∈ Finset.range n, q ^ j)) := by
        apply Finset.sum_congr rfl; intro k hk; dsimp [w]; ring
      _ = ∑ k ∈ Finset.range (n + 2), qChoose q (n + 1) k *
          (w ^ k * falling q k x * falling q (n + 1 - k) y) :=
        qChoose_convolution q n _ _ hrec
      _ = _ := by apply Finset.sum_congr rfl; intro k hk; dsimp [w]; ring

private lemma qChoose_map {B : Type*} [CommRing B] (f : A →+* B) (q : A) (n k : ℕ) :
    qChoose (f q) n k = f (qChoose q n k) := by
  induction n generalizing k with
  | zero => cases k <;> simp [qChoose]
  | succ n ih => cases k <;> simp [qChoose, ih]

/-- The product `∏_{i < n} (-q ^ i)`, the constant term of the `q`-falling factorial. -/
private def geometricWeight (q : A) (n : ℕ) : A := ∏ i ∈ Finset.range n, -(q ^ i)

private lemma geometricWeight_succ (q : A) (n : ℕ) :
    geometricWeight q (n + 1) = geometricWeight q n * -(q ^ n) :=
  Finset.prod_range_succ _ _

private lemma geometricWeight_unit {q : A} (hq : IsUnit q) (n : ℕ) :
    IsUnit (geometricWeight q n) := by
  induction n with
  | zero => simp [geometricWeight]
  | succ n ih => rw [geometricWeight_succ]; exact ih.mul (hq.pow n).neg

private lemma prod_geometric_eq_sum (q : A) (n : ℕ) :
    (∏ i ∈ Finset.range n, (X - C (q ^ i))) =
      ∑ k ∈ Finset.range (n + 1),
        qChoose (C q) n k * C (geometricWeight q (n - k)) * X ^ k := by
  induction n with
  | zero => simp [qChoose, geometricWeight]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Finset.sum_mul]
    have hrec : ∀ k, k ≤ n →
        C (geometricWeight q (n - k)) * X ^ k * (X - C (q ^ n)) =
        C (geometricWeight q (n + 1 - (k + 1))) * X ^ (k + 1) +
          (C q) ^ k * (C (geometricWeight q (n + 1 - k)) * X ^ k) := by
      intro k hk
      rw [show n + 1 - (k + 1) = n - k by omega, show n + 1 - k = (n - k) + 1 by omega,
        geometricWeight_succ, map_mul, map_neg, ← map_pow, pow_succ]
      have hp : (C q : A[X]) ^ k * C (q ^ (n - k)) = C (q ^ n) := by
        rw [← C_pow, ← C_mul, ← pow_add, Nat.add_sub_of_le hk]
      simp only [C_pow] at *
      linear_combination (C (geometricWeight q (n - k)) * X ^ k) * hp
    calc
      _ = ∑ k ∈ Finset.range (n + 1), qChoose (C q) n k *
          (C (geometricWeight q (n - k)) * X ^ k * (X - C (q ^ n))) := by
        apply Finset.sum_congr rfl; intro k hk; ring
      _ = ∑ k ∈ Finset.range (n + 2), qChoose (C q) (n + 1) k *
          (C (geometricWeight q (n + 1 - k)) * X ^ k) :=
        qChoose_convolution (C q) n _ _ hrec
      _ = _ := by apply Finset.sum_congr rfl; intro k hk; ring

private lemma prod_geometric_coeff (q : A) (n k : ℕ) (hk : k ≤ n) :
    (∏ i ∈ Finset.range n, (X - C (q ^ i))).coeff k =
      qChoose q n k * geometricWeight q (n - k) := by
  rw [prod_geometric_eq_sum, finsetSum_coeff]
  simp_rw [qChoose_map C, ← C_mul, coeff_C_mul_X_pow]
  simp [Nat.lt_succ_of_le hk]

private lemma qChoose_eq_zero_of_split {q : A} (hq : IsUnit q) (n : ℕ)
    (hsplit : ∏ i ∈ Finset.range n, (X - C (q ^ i)) = X ^ n - 1)
    (k : ℕ) (hk : 0 < k) (hkn : k < n) : qChoose q n k = 0 := by
  have h := congrArg (fun p : A[X] => p.coeff k) hsplit
  rw [prod_geometric_coeff q n k (by omega)] at h
  have hz : (X ^ n - 1 : A[X]).coeff k = 0 := by
    simp [coeff_X_pow, coeff_one, hk.ne', hkn.ne]
  rw [hz] at h
  exact (geometricWeight_unit hq (n - k)).mul_left_eq_zero.mp h

private lemma falling_add_of_split {q : A} (hq : IsUnit q) (n : ℕ) (hn : 0 < n)
    (hsplit : ∏ i ∈ Finset.range n, (X - C (q ^ i)) = X ^ n - 1) (x y : A) :
    falling q n ((q - 1) * x * y + x + y) =
      falling q n y + ((q - 1) * y + 1) ^ n * falling q n x := by
  rw [falling_add, Finset.sum_range_succ]
  have hs : (∑ k ∈ Finset.range n, qChoose q n k *
      ((q - 1) * y + 1) ^ k * falling q k x * falling q (n - k) y) = falling q n y := by
    rw [Finset.sum_eq_single 0]
    · simp [qChoose_zero, falling_zero]
    · intro k hk hk0
      rw [qChoose_eq_zero_of_split hq n hsplit k (by omega) (Finset.mem_range.mp hk)]
      simp
    · simp [hn]
  rw [hs, qChoose_self, Nat.sub_self, falling_zero]
  ring

/-! ### The short exact sequence -/

variable (ℓ : ℕ) [NeZero ℓ] (ζ : A) (hζ : ζ ^ ℓ = 1)
  (hsplit : ∏ i : ZMod ℓ, (X - C (ζ ^ i.val)) = X ^ ℓ - 1)

lemma pow_eq_one_of_split (hlt : 1 < ℓ)
    (hsplit : ∏ i : ZMod ℓ, (X - C (ζ ^ i.val)) = X ^ ℓ - 1) : ζ ^ ℓ = 1 := by
  have h := congrArg (Polynomial.eval ζ) hsplit
  have hzero : (∏ i : ZMod ℓ, (X - C (ζ ^ i.val))).eval ζ = 0 := by
    rw [Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ (1 : ZMod ℓ))
    simp [ZMod.val_one'' (by omega : ℓ ≠ 1)]
  rw [hzero] at h
  apply sub_eq_zero.mp
  simpa only [eval_sub, eval_pow, eval_X, eval_one] using h.symm

private lemma sum_pow_range_eq_zero (hsplit :
    ∏ i : ZMod ℓ, (X - C (ζ ^ i.val)) = X ^ ℓ - 1) (hℓ : 1 < ℓ) :
    (∑ j ∈ Finset.range ℓ, ζ ^ j) = 0 := by
  have hcoef := congrArg (fun p : A[X] => p.coeff (ℓ - 1)) hsplit
  have hcard : 0 < Fintype.card (ZMod ℓ) := by
    rw [ZMod.card]
    exact Nat.zero_lt_of_lt hℓ
  have hprod := Polynomial.prod_X_sub_C_coeff_card_pred Finset.univ
    (fun i : ZMod ℓ => ζ ^ i.val) (by simpa using hcard)
  have hprod' :
      (∏ i : ZMod ℓ, (X - C (ζ ^ i.val))).coeff (ℓ - 1) =
        -(∑ i : ZMod ℓ, ζ ^ i.val) := by
    simpa [ZMod.card] using hprod
  have hright : (X ^ ℓ - 1 : A[X]).coeff (ℓ - 1) = 0 := by
    have hne0 : ℓ - 1 ≠ 0 := by omega
    have hne : ℓ - 1 ≠ ℓ := by omega
    simp [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_one, hne0, hne]
  have hsum : (∑ i : ZMod ℓ, ζ ^ i.val) = 0 := by
    rw [hprod'] at hcoef
    rw [hright] at hcoef
    have h := hcoef
    simp only [neg_eq_zero] at h
    exact h
  calc
    (∑ j ∈ Finset.range ℓ, ζ ^ j) = ∑ j : Fin ℓ, ζ ^ j.val := by
      rw [Fin.sum_univ_eq_sum_range]
    _ = ∑ i : ZMod ℓ, ζ ^ i.val := by
      have heval (j : Fin ℓ) : (ZMod.finEquiv ℓ j).val = j.val := by
        cases ℓ with
        | zero => exact (NeZero.ne 0 rfl).elim
        | succ n => rfl
      exact Fintype.sum_equiv (ZMod.finEquiv ℓ) _ _ (fun j => by simp [heval])
    _ = 0 := hsum

private lemma sigmaPoint_add (hζ : ζ ^ ℓ = 1) (hsplit :
    ∏ i : ZMod ℓ, (X - C (ζ ^ i.val)) = X ^ ℓ - 1)
    (hℓ : 1 < ℓ) (i j : ZMod ℓ) :
    sigmaPoint ℓ ζ (i + j) =
      sigmaPoint ℓ ζ i + ζ ^ i.val * sigmaPoint ℓ ζ j := by
  classical
  let m := i.val
  let n := j.val
  have hi : m < ℓ := i.val_lt
  have hj : n < ℓ := j.val_lt
  have hval : (i + j).val = (m + n) % ℓ := by
    simp [m, n, ZMod.val_add]
  simp only [sigmaPoint]
  rw [hval]
  by_cases hmn : i.val + j.val < ℓ
  · rw [Nat.mod_eq_of_lt hmn, geom_sum_range_add]
  · have hmn' : ℓ ≤ i.val + j.val := Nat.le_of_not_gt hmn
    let r := i.val + j.val - ℓ
    have hmnEq : i.val + j.val = ℓ + r := by dsimp [r]; omega
    have hrlt : r < ℓ := by dsimp [r]; omega
    rw [Nat.mod_eq_sub_mod hmn', Nat.mod_eq_of_lt hrlt]
    have h1 : (∑ k ∈ Finset.range (i.val + j.val), ζ ^ k) =
        (∑ k ∈ Finset.range ℓ, ζ ^ k) +
          ζ ^ ℓ * (∑ k ∈ Finset.range r, ζ ^ k) := by
      rw [hmnEq, geom_sum_range_add]
    have h2 : (∑ k ∈ Finset.range (i.val + j.val), ζ ^ k) =
        (∑ k ∈ Finset.range i.val, ζ ^ k) +
          ζ ^ i.val * (∑ k ∈ Finset.range j.val, ζ ^ k) :=
      geom_sum_range_add ζ _ _
    rw [sum_pow_range_eq_zero (A := A) (ℓ := ℓ) (ζ := ζ) hsplit hℓ] at h1
    simpa [hζ] using h1.symm.trans h2

omit [NeZero ℓ] in
private lemma sum_pow_range_mul_eq_zero
    (hsum : (∑ j ∈ Finset.range ℓ, ζ ^ j) = 0) (q : ℕ) :
    (∑ j ∈ Finset.range (ℓ * q), ζ ^ j) = 0 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, geom_sum_range_add, ih, hsum]
    simp

omit [NeZero ℓ] in
private lemma sum_pow_range_eq_one_of_mod_eq_one (hζ : ζ ^ ℓ = 1)
    (hsum : (∑ j ∈ Finset.range ℓ, ζ ^ j) = 0) {n : ℕ} (hn : n % ℓ = 1) :
    (∑ j ∈ Finset.range n, ζ ^ j) = 1 := by
  have hdecomp : n = ℓ * (n / ℓ) + 1 := by
    have := Nat.mod_add_div n ℓ
    omega
  rw [hdecomp, Finset.sum_range_add,
    sum_pow_range_mul_eq_zero (A := A) (ℓ := ℓ) (ζ := ζ) hsum, zero_add]
  simp [pow_mul, hζ]

private lemma sigmaPoint_mul_geomSum (i m : ℕ) :
    (∑ a ∈ Finset.range i, ζ ^ a) *
      (∑ b ∈ Finset.range m, (ζ ^ i) ^ b) =
        ∑ k ∈ Finset.range (i * m), ζ ^ k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih, Nat.mul_succ, geom_sum_range_add, ← pow_mul,
      mul_comm (ζ ^ (i * m))]

private lemma sigmaPoint_isUnit_of_coprime (hlt : 1 < ℓ) (hζ : ζ ^ ℓ = 1)
    (hsplit : ∏ i : ZMod ℓ, (X - C (ζ ^ i.val)) = X ^ ℓ - 1)
    {i : ZMod ℓ} (hcop : Nat.Coprime i.val ℓ) : IsUnit (sigmaPoint ℓ ζ i) := by
  obtain ⟨m, hm, hmod⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by omega)
  have hprod : sigmaPoint ℓ ζ i * (∑ b ∈ Finset.range m, (ζ ^ i.val) ^ b) = 1 := by
    calc
      _ = ∑ k ∈ Finset.range (i.val * m), ζ ^ k := by
        rw [sigmaPoint]
        exact sigmaPoint_mul_geomSum (A := A) (ζ := ζ) i.val m
      _ = 1 := sum_pow_range_eq_one_of_mod_eq_one (A := A) (ℓ := ℓ) (ζ := ζ)
        hζ (sum_pow_range_eq_zero (A := A) (ℓ := ℓ) (ζ := ζ) hsplit hlt) hmod
  exact IsUnit.of_mul_eq_one _ hprod

private lemma sigmaPoint_sub_isUnit_of_ne (hℓ : ℓ.Prime) (hζ : ζ ^ ℓ = 1)
    (hsplit : ∏ i : ZMod ℓ, (X - C (ζ ^ i.val)) = X ^ ℓ - 1)
    {i j : ZMod ℓ} (hij : i ≠ j) :
    IsUnit (sigmaPoint ℓ ζ i - sigmaPoint ℓ ζ j) := by
  have hlt := hℓ.one_lt
  let k := i - j
  have hk : k ≠ 0 := sub_ne_zero.mpr hij
  have hkcoprime : Nat.Coprime k.val ℓ :=
    (Nat.coprime_of_lt_prime (ZMod.val_pos.mpr hk).ne' k.val_lt hℓ).symm
  have hdiff : sigmaPoint ℓ ζ i - sigmaPoint ℓ ζ j =
      ζ ^ j.val * sigmaPoint ℓ ζ k := by
    rw [← show j + k = i by simp [k], sigmaPoint_add (A := A) (ℓ := ℓ) (ζ := ζ) hζ hsplit hlt j k]
    ring
  rw [hdiff]
  exact ((IsUnit.of_pow_eq_one hζ (NeZero.ne ℓ)).pow j.val).mul
    (sigmaPoint_isUnit_of_coprime (ℓ := ℓ) (ζ := ζ) hlt hζ hsplit hkcoprime)

private noncomputable def polynomialKernelAlgEquiv_pi (hℓ : ℓ.Prime) (hζ : ζ ^ ℓ = 1)
    (hsplit : ∏ i : ZMod ℓ, (X - C (ζ ^ i.val)) = X ^ ℓ - 1) :
    (Polynomial A ⧸ Ideal.span {isogenyPolynomial ℓ ζ}) ≃ₐ[A] (ZMod ℓ → A) := by
  classical
  let I : ZMod ℓ → Ideal A[X] := fun i => Ideal.span {(X - C (sigmaPoint ℓ ζ i))}
  have hcop : Pairwise fun i j => IsCoprime (I i) (I j) := by
    intro i j hij
    change IsCoprime (Ideal.span {(X - C (sigmaPoint ℓ ζ i))})
      (Ideal.span {(X - C (sigmaPoint ℓ ζ j))})
    rw [Ideal.isCoprime_span_singleton_iff]
    have hu := sigmaPoint_sub_isUnit_of_ne (A := A) (ℓ := ℓ) (ζ := ζ)
      hℓ hζ hsplit hij.symm
    let w : A := (hu.unit⁻¹).val
    refine ⟨C w, -C w, ?_⟩
    have hunit : w * (sigmaPoint ℓ ζ j - sigmaPoint ℓ ζ i) = 1 := hu.val_inv_mul
    calc
      C w * (X - C (sigmaPoint ℓ ζ i)) +
          -C w * (X - C (sigmaPoint ℓ ζ j)) =
          C (w * (sigmaPoint ℓ ζ j - sigmaPoint ℓ ζ i)) := by
            simp only [map_sub, map_mul]
            ring
      _ = 1 := by rw [hunit, map_one]
  have hprod : (⨅ i, I i) = Ideal.span {isogenyPolynomial ℓ ζ} := by
    rw [Ideal.iInf_span_singleton]
    · simp [isogenyPolynomial]
    · intro i j hij
      exact (Ideal.isCoprime_span_singleton_iff _ _).mp (hcop hij)
  let ecrt : (Polynomial A ⧸ Ideal.span {isogenyPolynomial ℓ ζ}) ≃+*
      (∀ i : ZMod ℓ, Polynomial A ⧸ (I i)) :=
    (Ideal.quotEquivOfEq hprod.symm).trans (Ideal.quotientInfRingEquivPiQuotient I hcop)
  let e : (∀ i : ZMod ℓ, Polynomial A ⧸ (I i)) ≃ₐ[A] (∀ i : ZMod ℓ, A) :=
    AlgEquiv.piCongrRight fun i => Polynomial.quotientSpanXSubCAlgEquiv (sigmaPoint ℓ ζ i)
  let r : (Polynomial A ⧸ Ideal.span {isogenyPolynomial ℓ ζ}) ≃+* (ZMod ℓ → A) :=
    ecrt.trans e.toRingEquiv
  refine AlgEquiv.ofRingEquiv (f := r) ?_
  intro a
  ext i
  have hcomponent : ecrt (algebraMap A
      (Polynomial A ⧸ Ideal.span {isogenyPolynomial ℓ ζ}) a) i =
        algebraMap A (Polynomial A ⧸ I i) a := by
    have hclass : algebraMap A
        (Polynomial A ⧸ Ideal.span {isogenyPolynomial ℓ ζ}) a =
          Ideal.Quotient.mk (Ideal.span {isogenyPolynomial ℓ ζ}) (C a) := rfl
    rw [hclass]
    simp only [ecrt, RingEquiv.trans_apply, Ideal.quotientInfRingEquivPiQuotient,
      Ideal.quotEquivOfEq_mk]
    change Ideal.quotientInfToPiQuotient I
      (Ideal.Quotient.mk (⨅ j, I j) (C a)) i =
        Ideal.Quotient.mk (I i) (C a)
    exact Ideal.quotientInfToPiQuotient_mk' I (C a) i
  change (Polynomial.quotientSpanXSubCAlgEquiv (sigmaPoint ℓ ζ i))
    (ecrt (algebraMap A
      (Polynomial A ⧸ Ideal.span {isogenyPolynomial ℓ ζ}) a) i) = a
  rw [hcomponent]
  exact (Polynomial.quotientSpanXSubCAlgEquiv (sigmaPoint ℓ ζ i)).commutes a

private lemma isogenyPolynomial_natDegree [Nontrivial A] :
    (isogenyPolynomial ℓ ζ).natDegree = ℓ := by
  rw [isogenyPolynomial, Polynomial.natDegree_prod_of_monic]
  · simp [ZMod.card]
  · exact fun i _ => monic_X_sub_C _

private lemma prod_zmod_eq_prod_range {B : Type*} [CommMonoid B] (f : ℕ → B) :
    (∏ i : ZMod ℓ, f i.val) = ∏ i ∈ Finset.range ℓ, f i := by
  rw [← Fin.prod_univ_eq_prod_range]
  refine (Fintype.prod_equiv (ZMod.finEquiv ℓ) _ _ fun i => ?_).symm
  cases ℓ with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

private lemma aeval_isogenyPolynomial_eq_falling {R : Type v} [CommRing R] [Algebra A R]
    (x : R) : aeval x (isogenyPolynomial ℓ ζ) = falling (algebraMap A R ζ) ℓ x := by
  simp only [isogenyPolynomial, map_prod, map_sub, aeval_X, aeval_C,
    sigmaPoint, map_sum, map_pow]
  exact prod_zmod_eq_prod_range (ℓ := ℓ)
    (fun i => x - ∑ j ∈ Finset.range i, (algebraMap A R ζ) ^ j)

/-- The map `f` is a morphism of group schemes: it is additive on points. -/
@[stacks 0GY4]
theorem isogenyOnPoints_add {R : Type v} [CommRing R] [Algebra A R]
    (x y : DeformedPoint (ζ - 1) R) :
    isogenyOnPoints ℓ ζ hsplit (x + y)
      = isogenyOnPoints ℓ ζ hsplit x + isogenyOnPoints ℓ ζ hsplit y := by
  by_cases hℓ : ℓ = 1
  · subst ℓ
    apply DeformedPoint.ext
    have h0 : ∀ i : ZMod 1, sigmaPoint 1 ζ i = 0 := fun i => by
      rw [show i = 0 from Subsingleton.elim i 0]
      simp [sigmaPoint]
    have hΦ : isogenyPolynomial 1 ζ = X := by
      rw [isogenyPolynomial, Finset.prod_eq_single_of_mem (0 : ZMod 1) (Finset.mem_univ _)
        (fun b _ hb => absurd (Subsingleton.elim b 0) hb)]
      simp [h0]
    simp [coord_isogenyOnPoints, DeformedPoint.coord_add, hΦ]
  have hlt : 1 < ℓ := by have := NeZero.ne ℓ; omega
  have hq : IsUnit (algebraMap A R ζ) :=
    (IsUnit.of_pow_eq_one (pow_eq_one_of_split ℓ ζ hlt hsplit) (NeZero.ne ℓ)).map _
  have hsplitR : ∏ i ∈ Finset.range ℓ, (X - C ((algebraMap A R ζ) ^ i)) = X ^ ℓ - 1 := by
    have hh := congrArg (Polynomial.map (algebraMap A R)) hsplit
    simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      map_pow, Polynomial.map_pow, Polynomial.map_one] at hh
    rw [prod_zmod_eq_prod_range (ℓ := ℓ)
      (fun i => (X : R[X]) - C (algebraMap A R ζ) ^ i)] at hh
    simpa only [C_pow] using hh
  have hadd := falling_add_of_split hq ℓ (by omega) hsplitR x.coord y.coord
  have hpow := congrArg (fun p : A[X] => aeval y.coord p)
    (one_add_mul_pow_eq_isogenyPolynomial ℓ ζ hsplit)
  simp only [map_pow, map_add, map_mul, map_one, aeval_C, aeval_X,
    aeval_isogenyPolynomial_eq_falling] at hpow
  apply DeformedPoint.ext
  simp only [coord_isogenyOnPoints, DeformedPoint.coord_add,
    aeval_isogenyPolynomial_eq_falling, map_sub, map_one, map_pow] at *
  rw [hadd, hpow]
  ring

/-- The points `σ_i` form a homomorphism from `ℤ/ℓℤ` to the `A`-points of `G^{(ζ - 1)}`, as in
`σ_i +_G σ_j = σ_{i + j}`. -/
@[stacks 0GY4]
theorem constantPoint_add
    (hsplit : ∏ k : ZMod ℓ, (X - C (ζ ^ k.val)) = X ^ ℓ - 1)
    (i j : ZMod ℓ) :
    constantPoint ℓ ζ hζ (i + j) = constantPoint ℓ ζ hζ i + constantPoint ℓ ζ hζ j := by
  apply DeformedPoint.ext
  simp only [coord_constantPoint, DeformedPoint.coord_add, Algebra.algebraMap_self,
    RingHom.id_apply]
  by_cases hℓ : 1 < ℓ
  · linear_combination sigmaPoint_add (A := A) (ℓ := ℓ) (ζ := ζ) hζ hsplit hℓ i j -
      sigmaPoint ℓ ζ j * mul_sigmaPoint ℓ ζ i
  · have := NeZero.ne ℓ
    obtain rfl : ℓ = 1 := by omega
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [sigmaPoint]

/-- The composition of `ℤ/ℓℤ → G^{(ζ - 1)}` with `f` is trivial: the points `σ_i` lie in the
kernel of `f`. -/
@[stacks 0GY4]
theorem isogenyOnPoints_constantPoint (i : ZMod ℓ) :
    isogenyOnPoints ℓ ζ hsplit (constantPoint ℓ ζ hζ i) = 0 := by
  apply DeformedPoint.ext
  simp only [coord_isogenyOnPoints, coord_constantPoint, DeformedPoint.coord_zero,
    isogenyPolynomial, map_prod, map_sub, aeval_X, aeval_C]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

private lemma aeval_mk_X_self (p : A[X]) :
    aeval (Ideal.Quotient.mk (Ideal.span {p}) X) p = 0 := by
  have hev : (aeval (Ideal.Quotient.mk (Ideal.span {p}) X) :
      A[X] →ₐ[A] A[X] ⧸ Ideal.span {p}) = Ideal.Quotient.mkₐ A _ := by
    apply Polynomial.algHom_ext
    rw [aeval_X, Ideal.Quotient.mkₐ_eq_mk]
  rw [hev, Ideal.Quotient.mkₐ_eq_mk]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton p))

private lemma one_add_mul_mk_X_pow_eq_one
    (hsplit : ∏ i : ZMod ℓ, (X - C (ζ ^ i.val)) = X ^ ℓ - 1) :
    (algebraMap A (A[X] ⧸ Ideal.span {isogenyPolynomial ℓ ζ}) (ζ - 1) *
      Ideal.Quotient.mk _ X + 1) ^ ℓ = 1 := by
  have h := congrArg (fun p : A[X] =>
      aeval (Ideal.Quotient.mk (Ideal.span {isogenyPolynomial ℓ ζ}) X) p)
    (one_add_mul_pow_eq_isogenyPolynomial ℓ ζ hsplit)
  simp only [map_pow, map_add, map_mul, map_one, aeval_C, aeval_X, aeval_mk_X_self] at h
  simpa using h

private lemma aeval_kernelGenerator_isogenyPolynomial
    (hsplit : ∏ i : ZMod ℓ, (X - C (ζ ^ i.val)) = X ^ ℓ - 1) :
    aeval (Ideal.Quotient.mk
        (Ideal.span {isogeny ℓ ζ hsplit (coordinateGenerator ((ζ - 1) ^ ℓ))})
        (coordinateGenerator (ζ - 1))) (isogenyPolynomial ℓ ζ) = 0 := by
  have hk : Ideal.Quotient.mk
      (Ideal.span {isogeny ℓ ζ hsplit (coordinateGenerator ((ζ - 1) ^ ℓ))})
      (isogeny ℓ ζ hsplit (coordinateGenerator ((ζ - 1) ^ ℓ))) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hev := Polynomial.aeval_algHom_apply
    (Ideal.Quotient.mkₐ A
      (Ideal.span {isogeny ℓ ζ hsplit (coordinateGenerator ((ζ - 1) ^ ℓ))}))
    (coordinateGenerator (ζ - 1)) (isogenyPolynomial ℓ ζ)
  rw [Ideal.Quotient.mkₐ_eq_mk] at hev
  apply hev.trans
  have heval : isogeny ℓ ζ hsplit (coordinateGenerator ((ζ - 1) ^ ℓ)) =
      aeval (coordinateGenerator (ζ - 1)) (isogenyPolynomial ℓ ζ) :=
    localizationMap_X A (ζ - 1) ℓ _ _
  exact (congrArg (Ideal.Quotient.mk
    (Ideal.span {isogeny ℓ ζ hsplit (coordinateGenerator ((ζ - 1) ^ ℓ))}))
      heval.symm).trans hk

private lemma exists_kernelPolynomialQuotientAlgEquiv
    (hsplit : ∏ i : ZMod ℓ, (X - C (ζ ^ i.val)) = X ^ ℓ - 1) :
    ∃ e : kernelCoordinateRing ℓ ζ hsplit ≃ₐ[A]
        (Polynomial A ⧸ Ideal.span {isogenyPolynomial ℓ ζ}),
      e (Ideal.Quotient.mk _ (coordinateGenerator (ζ - 1))) = Ideal.Quotient.mk _ X := by
  classical
  let π : A := ζ - 1
  let φ : A[X] := isogenyPolynomial ℓ ζ
  let Q := Polynomial A ⧸ Ideal.span {φ}
  let q : Q := Ideal.Quotient.mk _ X
  let u : Q := algebraMap A Q π * q + 1
  have hu : IsUnit u :=
    IsUnit.of_pow_eq_one (one_add_mul_mk_X_pow_eq_one ℓ ζ hsplit) (NeZero.ne ℓ)
  let f₀ : coordinateRing π →ₐ[A] Q :=
    IsLocalization.Away.liftAlgHom (C π * X + 1) (by simpa [u] using hu) (f := aeval q)
  have hf₀q : f₀ (coordinateGenerator π) = q := by
    simp [f₀, coordinateGenerator, IsLocalization.Away.liftAlgHom,
      IsLocalization.Away.lift, q]
  have hkill : f₀ (isogeny ℓ ζ hsplit
      (coordinateGenerator (π ^ ℓ))) = 0 := by
    change f₀ (localizationMap A (ζ - 1) ℓ φ _
      (coordinateGenerator ((ζ - 1) ^ ℓ))) = 0
    rw [localizationMap_X, ← Polynomial.aeval_algHom_apply, hf₀q]
    exact aeval_mk_X_self φ
  let f : kernelCoordinateRing ℓ ζ hsplit →ₐ[A] Q :=
    Ideal.Quotient.liftₐ _ f₀ (Ideal.span_le.mpr (by
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact RingHom.mem_ker.mpr hkill))
  let k : kernelCoordinateRing ℓ ζ hsplit :=
    Ideal.Quotient.mk _ (coordinateGenerator π)
  have hkφ : aeval k φ = 0 := aeval_kernelGenerator_isogenyPolynomial ℓ ζ hsplit
  let g₀ : A[X] →ₐ[A] kernelCoordinateRing ℓ ζ hsplit := aeval k
  let g : Q →ₐ[A] kernelCoordinateRing ℓ ζ hsplit :=
    Ideal.Quotient.liftₐ _ g₀ (Ideal.span_le.mpr (by
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact RingHom.mem_ker.mpr hkφ))
  have hf : f k = q := hf₀q
  have hg : g q = k := aeval_X k
  refine ⟨AlgEquiv.ofAlgHom f g ?_ ?_, hf⟩
  · apply Ideal.Quotient.algHom_ext
    apply Polynomial.algHom_ext
    change f (g q) = q
    rw [hg, hf]
  · apply Ideal.Quotient.algHom_ext
    apply IsLocalization.algHom_ext (Submonoid.powers (C π * X + 1))
    apply Polynomial.algHom_ext
    change g (f k) = k
    rw [hf, hg]

private lemma polynomialKernelAlgEquiv_pi_generator
    (hℓ : ℓ.Prime) (hζ : ζ ^ ℓ = 1)
    (hsplit : ∏ i : ZMod ℓ, (X - C (ζ ^ i.val)) = X ^ ℓ - 1) (i : ZMod ℓ) :
    polynomialKernelAlgEquiv_pi ℓ ζ hℓ hζ hsplit (Ideal.Quotient.mk _ X) i =
      sigmaPoint ℓ ζ i := by
  simp only [polynomialKernelAlgEquiv_pi, AlgEquiv.ofRingEquiv_apply,
    RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  change Polynomial.quotientSpanXSubCAlgEquiv _
    (Ideal.quotientInfToPiQuotient (fun i : ZMod ℓ => Ideal.span {X - C (sigmaPoint ℓ ζ i)})
      (Ideal.Quotient.mk _ X) i) = _
  rw [Ideal.quotientInfToPiQuotient_mk', Polynomial.quotientSpanXSubCAlgEquiv_mk,
    Polynomial.eval_X]

/-- Exactness at `G^{(ζ - 1)}`: for `ℓ` prime, the closed immersion of the constant group scheme
of `ℤ/ℓℤ` into the kernel of `f` which sends `i` to `σ_i` is an isomorphism. Dually, the
`A`-algebra map from the coordinate ring of the kernel to the functions on `ℤ/ℓℤ` sending `s`
to `i ↦ σ_i` is an isomorphism. -/
@[stacks 0GY4]
theorem kernelCoordinateRing_algEquiv_pi (hℓ : ℓ.Prime) :
    ∃ e : kernelCoordinateRing ℓ ζ hsplit ≃ₐ[A] (ZMod ℓ → A),
      ∀ i : ZMod ℓ,
        e (Ideal.Quotient.mk _ (coordinateGenerator (ζ - 1))) i = sigmaPoint ℓ ζ i := by
  have hζ := pow_eq_one_of_split ℓ ζ hℓ.one_lt hsplit
  obtain ⟨e, he⟩ := exists_kernelPolynomialQuotientAlgEquiv ℓ ζ hsplit
  refine ⟨e.trans (polynomialKernelAlgEquiv_pi ℓ ζ hℓ hζ hsplit), ?_⟩
  intro i
  rw [AlgEquiv.trans_apply, he]
  exact polynomialKernelAlgEquiv_pi_generator ℓ ζ hℓ hζ hsplit i

/-- Exactness at `G^{((ζ - 1) ^ ℓ)}`: the morphism `f` is faithfully flat. -/
@[stacks 0GY4]
theorem isogeny_faithfullyFlat : (isogeny ℓ ζ hsplit).toRingHom.FaithfullyFlat := by
  classical
  let H := coordinateRing ((ζ - 1) ^ ℓ)
  let G := coordinateRing (ζ - 1)
  let ψ : H →ₐ[A] G := isogeny ℓ ζ hsplit
  let : Algebra H G := ψ.toRingHom.toAlgebra
  by_cases hH : Subsingleton H
  · let : Subsingleton H := hH
    have hG : Subsingleton G := by
      apply subsingleton_of_zero_eq_one
      have h := congrArg ψ (Subsingleton.elim (0 : H) 1)
      simpa [ψ] using h
    let : Subsingleton G := hG
    change Module.FaithfullyFlat H G
    have hflat : Module.Flat H G := by
      rw [Module.Flat.iff_rTensor_injectiveₛ]
      intro P _ _ N
      let : Subsingleton P := Module.subsingleton H P
      let : Subsingleton (N ⊗[H] G) := Module.subsingleton H _
      intro x y _
      exact Subsingleton.elim _ _
    let : Module.Flat H G := hflat
    refine ⟨?_⟩
    intro I hI htop
    exact hI.ne_top (Subsingleton.elim _ _)
  · let : Nontrivial H := not_subsingleton_iff_nontrivial.mp hH
    have hA : Nontrivial A := by
      by_contra hA
      let : Subsingleton A := not_nontrivial_iff_subsingleton.mp hA
      let : Subsingleton A[X] := inferInstance
      let : Subsingleton H := inferInstance
      exact hH inferInstance
    let : Nontrivial A := hA
    let t : H := algebraMap A[X] H X
    let P : H[X] := (isogenyPolynomial ℓ ζ).map (algebraMap A H) - Polynomial.C t
    have hΦmonic : (isogenyPolynomial ℓ ζ).Monic := isogenyPolynomial_monic ℓ ζ
    have hΦdegree : (isogenyPolynomial ℓ ζ).natDegree = ℓ :=
      isogenyPolynomial_natDegree ℓ ζ
    obtain ⟨hP, _⟩ :=
      localization_isAdjoinRootMonic_of_power_eq A (ζ - 1) ℓ
        (isogenyPolynomial ℓ ζ)
        (one_add_mul_pow_eq_isogenyPolynomial ℓ ζ hsplit)
        hΦmonic (by rw [hΦdegree]; exact Nat.pos_of_neZero ℓ)
    have hPdegree : P.natDegree = ℓ := by
      dsimp [P]
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
      · simp [hΦmonic.natDegree_map, hΦdegree]
      · rw [hΦmonic.natDegree_map, hΦdegree]
        simpa [Polynomial.natDegree_C] using Nat.pos_of_neZero ℓ
    have hpos : 0 < P.natDegree := by rw [hPdegree]; exact Nat.pos_of_neZero ℓ
    let : Nonempty (Fin P.natDegree) := ⟨⟨0, hpos⟩⟩
    let : Module.FaithfullyFlat H (Fin P.natDegree →₀ H) := inferInstance
    have hmod : Module.FaithfullyFlat H G :=
      Module.FaithfullyFlat.of_linearEquiv H (Fin P.natDegree →₀ H) hP.basis.repr
    change Module.FaithfullyFlat H G
    exact hmod

end AlgebraicGeometry.MultiplicativeDeformation

end
