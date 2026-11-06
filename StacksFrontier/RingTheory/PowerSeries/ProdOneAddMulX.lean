module

public import Mathlib.RingTheory.PowerSeries.Basic
public import StacksFrontier.RingTheory.MvPolynomial.Symmetric.EsymmAdd
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Data.List.ProdSigma
public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# The coefficients of `∏ (1 + r X)` are the elementary symmetric functions

For a multiset `s` of elements of a commutative semiring, the coefficient of `X^k` in the power
series `∏_{r ∈ s} (1 + r X)` is the `k`-th elementary symmetric function `e_k(s)`. This is the
relation between the total Chern class `c(ℰ) = ∏ (1 + x_i)` of a module filtered by invertible
modules with first Chern classes `x_i` and its Chern classes `c_k(ℰ) = e_k(x_1, …, x_r)`, with the
degree recorded by the power of `X`.

Over a ring `R` which is not commutative, as is the ring of operations on a Chow group in which
Chern classes live, the same holds for elements coming from a commutative ring `A ⟶ R`, which is
how pairwise commuting Chern roots are handled; and the first two coefficients of
`∏_{i,j} (1 + (x_i + y_j) X)`, the total Chern class of a tensor product, are expressed through
those of `∏ (1 + x_i X)` and `∏ (1 + y_j X)`.

## Main results

* `PowerSeries.coeff_prod_one_add_C_mul_X`: `coeff k (∏_{r ∈ s} (1 + C r * X)) = e_k(s)`.
* `PowerSeries.coeff_list_prod_one_add_C_mul_X` and
  `PowerSeries.coeff_list_prod_one_add_C_add_mul_X`: the same over a noncommutative ring, for
  elements coming from a commutative one, and for pairwise sums.
* `PowerSeries.coeff_one_list_prod_one_add_C_add_mul_X` and
  `PowerSeries.coeff_two_list_prod_one_add_C_add_mul_X`: the first two coefficients of
  `∏_{i,j} (1 + (x_i + y_j) X)`, the computation of Stacks 0ESE.
* `PowerSeries.exists_commSubring_of_pairwise_commute`,
  `PowerSeries.coeff_one_list_prod_one_add_C_add_mul_X_of_commute` and
  `PowerSeries.coeff_two_list_prod_one_add_C_add_mul_X_of_commute`: the same for pairwise
  commuting elements of a ring.

## References

* [Stacks Project, Tag 0ESD](https://stacks.math.columbia.edu/tag/0ESD)
* [Stacks Project, Tag 0ESE](https://stacks.math.columbia.edu/tag/0ESE)
-/

@[expose] public section

universe u

namespace PowerSeries

/-- The coefficient of `X^k` in `∏_{r ∈ s} (1 + r X)` is the `k`-th elementary symmetric function
of `s`. -/
theorem coeff_prod_one_add_C_mul_X {R : Type*} [CommSemiring R] (s : Multiset R) (k : ℕ) :
    coeff k (s.map fun r => 1 + C r * X).prod = s.esymm k := by
  induction s using Multiset.induction generalizing k with
  | empty =>
    cases k with
    | zero => simp
    | succ k => simp [coeff_one]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, add_mul, one_mul, mul_assoc, map_add]
    cases k with
    | zero => simp [ih]
    | succ k =>
      rw [coeff_C_mul, coeff_succ_X_mul, ih, ih, Multiset.esymm_cons_succ, add_comm]

section Noncomm

variable {R : Type*} [Ring R] {A : Type*} [CommRing A] (ι : A →+* R)

/-- Over a ring `R`, not necessarily commutative, the coefficient of `X^k` in `∏ (1 + ι(a) X)` for
a list of elements `a` of a commutative ring mapping to `R` is the image of their `k`-th
elementary symmetric function. -/
theorem coeff_list_prod_one_add_C_mul_X (xs : List A) (k : ℕ) :
    coeff k ((xs.map fun x => 1 + C (ι x) * X).prod) = ι ((xs : Multiset A).esymm k) := by
  have h : (xs.map fun x => 1 + C (ι x) * X) =
      (xs.map fun x => 1 + C x * X).map (PowerSeries.map ι) := by
    simp [List.map_map, Function.comp_def]
  rw [h, ← map_list_prod, coeff_map, ← Multiset.prod_coe, ← Multiset.map_coe,
    coeff_prod_one_add_C_mul_X]

/-- The coefficient of `X^k` in `∏_{(a, b)} (1 + (ι(a) + ι(b)) X)`, over the pairs of two lists in
lexicographic order, is the image of the `k`-th elementary symmetric function of the pairwise
sums. -/
theorem coeff_list_prod_one_add_C_add_mul_X (xs ys : List A) (k : ℕ) :
    coeff k ((xs.flatMap fun x => ys.map fun y => 1 + C (ι x + ι y) * X).prod) =
      ι ((((xs : Multiset A) ×ˢ (ys : Multiset A)).map fun p => p.1 + p.2).esymm k) := by
  have h : (xs.flatMap fun x => ys.map fun y => 1 + C (ι x + ι y) * X) =
      ((xs ×ˢ ys).map fun p => p.1 + p.2).map fun z => 1 + C (ι z) * X := by
    induction xs with
    | nil => simp
    | cons a xs ih =>
      rw [List.flatMap_cons, ih, List.product_cons, List.map_append, List.map_append,
        List.map_map, List.map_map, List.map_map]
      congr 1
      simp [Function.comp_def, map_add]
  rw [h, coeff_list_prod_one_add_C_mul_X, Multiset.coe_product, Multiset.map_coe]

/-- **The first coefficient of a product of pairwise sums**, the formal computation behind the
first identity of Stacks 0ESE: for lists `x_1, …, x_r` and `y_1, …, y_s` of elements of a
commutative ring mapping to `R`, the coefficient of `X` in `∏_{i,j} (1 + (x_i + y_j) X)` is
`s` times that of `∏_i (1 + x_i X)` plus `r` times that of `∏_j (1 + y_j X)`. -/
theorem coeff_one_list_prod_one_add_C_add_mul_X (xs ys : List A) :
    coeff 1 ((xs.flatMap fun x => ys.map fun y => 1 + C (ι x + ι y) * X).prod) =
      (ys.length : ℤ) • coeff 1 ((xs.map fun x => 1 + C (ι x) * X).prod) +
        (xs.length : ℤ) • coeff 1 ((ys.map fun y => 1 + C (ι y) * X).prod) := by
  rw [coeff_list_prod_one_add_C_add_mul_X, coeff_list_prod_one_add_C_mul_X,
    coeff_list_prod_one_add_C_mul_X, Multiset.esymm_one_map_add_product]
  simp

/-- **The second coefficient of a product of pairwise sums**, the formal computation behind the
second identity of Stacks 0ESE: with `c_k(x)` the coefficient of `X^k` in `∏_i (1 + x_i X)`, for
`r` elements `x_i` and `s` elements `y_j` of a commutative ring mapping to `R`, the coefficient of
`X^2` in `∏_{i,j} (1 + (x_i + y_j) X)` is
`r c_2(y) + s c_2(x) + C(r,2) c_1(y)² + (r s - 1) c_1(y) c_1(x) + C(s,2) c_1(x)²`. -/
theorem coeff_two_list_prod_one_add_C_add_mul_X (xs ys : List A) :
    coeff 2 ((xs.flatMap fun x => ys.map fun y => 1 + C (ι x + ι y) * X).prod) =
      (xs.length : ℤ) • coeff 2 ((ys.map fun y => 1 + C (ι y) * X).prod) +
        (ys.length : ℤ) • coeff 2 ((xs.map fun x => 1 + C (ι x) * X).prod) +
        (xs.length.choose 2 : ℤ) • coeff 1 ((ys.map fun y => 1 + C (ι y) * X).prod) ^ 2 +
        ((xs.length : ℤ) * ys.length - 1) •
          (coeff 1 ((ys.map fun y => 1 + C (ι y) * X).prod) *
            coeff 1 ((xs.map fun x => 1 + C (ι x) * X).prod)) +
        (ys.length.choose 2 : ℤ) • coeff 1 ((xs.map fun x => 1 + C (ι x) * X).prod) ^ 2 := by
  rw [coeff_list_prod_one_add_C_add_mul_X, coeff_list_prod_one_add_C_mul_X,
    coeff_list_prod_one_add_C_mul_X, coeff_list_prod_one_add_C_mul_X,
    coeff_list_prod_one_add_C_mul_X, Multiset.esymm_two_map_add_product]
  simp only [map_add, map_zsmul, map_nsmul, map_mul, map_pow, Multiset.coe_card,
    natCast_zsmul]
  rw [show ι (Multiset.esymm (xs : Multiset A) 1) * ι (Multiset.esymm (ys : Multiset A) 1) =
      ι (Multiset.esymm (ys : Multiset A) 1) * ι (Multiset.esymm (xs : Multiset A) 1) by
    rw [← map_mul, ← map_mul, mul_comm]]
  abel

end Noncomm

section Commuting

open scoped IsMulCommutative

variable {R : Type u} [Ring R]

/-- A list of pairwise commuting elements of a ring comes from a commutative subring. -/
theorem exists_commSubring_of_pairwise_commute {R : Type u} [Ring R] (xs : List R)
    (hc : ∀ a ∈ xs, ∀ b ∈ xs, Commute a b) :
    ∃ (A : Type u) (_ : CommRing A) (ι : A →+* R) (xs' : List A), xs'.map ι = xs := by
  have := Subring.isMulCommutative_closure (s := {a | a ∈ xs}) fun a ha b hb _ => hc a ha b hb
  refine ⟨Subring.closure {a | a ∈ xs}, inferInstance, (Subring.closure {a | a ∈ xs}).subtype,
    xs.attach.map fun a => ⟨a.1, Subring.subset_closure a.2⟩, ?_⟩
  rw [List.map_map]
  exact List.attach_map_subtype_val xs

/-- Two lists of pairwise commuting elements of a ring come from lists in a commutative ring. -/
private theorem exists_commRing_lift_of_commute (xs ys : List R)
    (hc : ∀ a ∈ xs ++ ys, ∀ b ∈ xs ++ ys, Commute a b) :
    ∃ (A : Type u) (_ : CommRing A) (ι : A →+* R) (xs' ys' : List A),
      xs'.map ι = xs ∧ ys'.map ι = ys := by
  obtain ⟨A, _, ι, zs, hzs⟩ := exists_commSubring_of_pairwise_commute (xs ++ ys) hc
  refine ⟨A, inferInstance, ι, zs.take xs.length, zs.drop xs.length, ?_, ?_⟩
  · rw [List.map_take, hzs, List.take_left]
  · rw [List.map_drop, hzs, List.drop_left]

/-- **The first coefficient of a product of pairwise sums** of pairwise commuting elements of a
ring: the coefficient of `X` in `∏_{i,j} (1 + (x_i + y_j) X)` is
`s c₁(x) + r c₁(y)` for `r` elements `x_i` and `s` elements `y_j`. -/
theorem coeff_one_list_prod_one_add_C_add_mul_X_of_commute (xs ys : List R)
    (hc : ∀ a ∈ xs ++ ys, ∀ b ∈ xs ++ ys, Commute a b) :
    coeff 1 ((xs.flatMap fun x => ys.map fun y => 1 + C (x + y) * X).prod) =
      (ys.length : ℤ) • coeff 1 ((xs.map fun x => 1 + C x * X).prod) +
        (xs.length : ℤ) • coeff 1 ((ys.map fun y => 1 + C y * X).prod) := by
  obtain ⟨A, _, ι, xs', ys', rfl, rfl⟩ := exists_commRing_lift_of_commute xs ys hc
  simp only [List.flatMap_map, List.map_map, List.length_map, Function.comp_def]
  exact coeff_one_list_prod_one_add_C_add_mul_X ι xs' ys'

/-- **The second coefficient of a product of pairwise sums** of pairwise commuting elements of a
ring, the computation of Stacks 0ESE: for `r` elements `x_i` and `s` elements `y_j`, the
coefficient of `X²` in `∏_{i,j} (1 + (x_i + y_j) X)` is
`r c₂(y) + s c₂(x) + C(r,2) c₁(y)² + (r s - 1) c₁(y) c₁(x) + C(s,2) c₁(x)²`. -/
theorem coeff_two_list_prod_one_add_C_add_mul_X_of_commute (xs ys : List R)
    (hc : ∀ a ∈ xs ++ ys, ∀ b ∈ xs ++ ys, Commute a b) :
    coeff 2 ((xs.flatMap fun x => ys.map fun y => 1 + C (x + y) * X).prod) =
      (xs.length : ℤ) • coeff 2 ((ys.map fun y => 1 + C y * X).prod) +
        (ys.length : ℤ) • coeff 2 ((xs.map fun x => 1 + C x * X).prod) +
        (xs.length.choose 2 : ℤ) • coeff 1 ((ys.map fun y => 1 + C y * X).prod) ^ 2 +
        ((xs.length : ℤ) * ys.length - 1) •
          (coeff 1 ((ys.map fun y => 1 + C y * X).prod) *
            coeff 1 ((xs.map fun x => 1 + C x * X).prod)) +
        (ys.length.choose 2 : ℤ) • coeff 1 ((xs.map fun x => 1 + C x * X).prod) ^ 2 := by
  obtain ⟨A, _, ι, xs', ys', rfl, rfl⟩ := exists_commRing_lift_of_commute xs ys hc
  simp only [List.flatMap_map, List.map_map, List.length_map, Function.comp_def]
  exact coeff_two_list_prod_one_add_C_add_mul_X ι xs' ys'

end Commuting

end PowerSeries
