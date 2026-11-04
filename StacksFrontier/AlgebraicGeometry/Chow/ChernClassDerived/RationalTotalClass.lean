module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.TotalClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.RationalChowRing
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.ChernCharacter
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The ring `∏_{p ≥ 0} A^p(X) ⊗ 𝐐`

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `X` be locally of
finite type over `S`. The Chern character of a finite locally free `𝒪_X`-module takes values in
`∏_{p ≥ 0} A^p(X) ⊗ 𝐐`, and Stacks 0FEM asserts that it is a ring map
`K₀(Vect(X)) ⟶ ∏_{p ≥ 0} A^p(X) ⊗ 𝐐`. The ring structure meant there is the Cauchy product

  `(a b)_m = ∑_{i + j = m} a_i b_j`,

with `A^i(X) ⊗ 𝐐 × A^j(X) ⊗ 𝐐 ⟶ A^{i+j}(X) ⊗ 𝐐` the rational extension of the product of
Stacks 0B75. This file constructs it, as `Stacks.Chow.RationalTotalChowClass`, from the ring
`Stacks.Chow.TotalChowClass C sX = ∏_{p ≥ 0} A^p(X)` of total Chow cohomology classes.

The product cannot be obtained by extending scalars: `𝐐 ⊗ ∏_p A^p(X)` is in general a proper
subgroup of `∏_p (A^p(X) ⊗ 𝐐)` (the Chern character itself has unbounded denominators). The
degree-`m` component of `a b` is the degree-`m` component of the product in `𝐐 ⊗ ∏_p A^p(X)` of
the lifts `∑_{p ≤ m} a_p` and `∑_{p ≤ m} b_p`.

## Main definitions

* `Stacks.Chow.TotalChowClass.component`, `Stacks.Chow.TotalChowClass.single`,
  `Stacks.Chow.TotalChowClass.truncate` — the components of a total class, the total class of a
  single homogeneous class, and the truncation below a given degree.
* `Stacks.Chow.RationalTotalChowClass` — `∏_{p ≥ 0} A^p(X) ⊗ 𝐐` with its ring structure, and
  `Stacks.Chow.RationalTotalChowClass.ofFamily`, its identification with the group
  `Stacks.Chow.fullRationalChowCohomology` of families.
* `Stacks.Chow.RationalTotalChowClass.truncatedLift` — the lift `∑_{p ≤ m} a_p ∈ 𝐐 ⊗ ∏_q A^q(X)`
  of a family below degree `m`.
* `Stacks.Chow.RationalTotalChowClass.ofTotalChowClass` — the ring map
  `∏_p A^p(X) ⟶ ∏_p A^p(X) ⊗ 𝐐`.

## Main results

* `Stacks.Chow.TotalChowClass.mul_apply_congr` — `(c d)_m` only depends on the components of
  degree at most `m` of `c` and `d`.
* `Stacks.Chow.RationalTotalChowClass.mul_apply_eq` — the degree-`m` component of a product is
  that of the product of any two lifts of the factors to `𝐐 ⊗ ∏_p A^p(X)` which are correct up to
  degree `m`.

## References

* [Stacks Project, Tag 0FEM](https://stacks.math.columbia.edu/tag/0FEM)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Finset
open scoped TensorProduct

universe u

namespace Stacks.Chow

namespace TotalChowClass

variable {C : ChowSituation.{u}} {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]

/-! ### Components, single classes and truncations -/

/-- The degree-`p` component `c ↦ c_p ∈ A^p(X)` of a total class, as an additive map. -/
def component (p : ℕ) :
    TotalChowClass C sX →+ chowCohomologyComponent C (gysinSystemOfInvertible C) sX p where
  toFun c := c p
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The degree-`p` component map evaluates a total class in degree `p`. -/
theorem component_apply (p : ℕ) (c : TotalChowClass C sX) : component p c = c p :=
  rfl

/-- **The truncation of a total class below degree `m`**: its components of degree at most `m`,
and zero above. -/
def truncate (m : ℕ) : TotalChowClass C sX →+ TotalChowClass C sX where
  toFun c := fun q ↦ if q ≤ m then c q else 0
  map_zero' := ext fun q ↦ by
    change (if q ≤ m then (0 : TotalChowClass C sX) q else 0) = (0 : TotalChowClass C sX) q
    split_ifs <;> rfl
  map_add' c d := ext fun q ↦ by
    change (if q ≤ m then (c + d) q else 0) =
      (if q ≤ m then c q else 0) + (if q ≤ m then d q else 0)
    split_ifs
    · rfl
    · exact (add_zero 0).symm

/-- The components of a truncation. -/
theorem truncate_apply (m : ℕ) (c : TotalChowClass C sX) (q : ℕ) :
    truncate m c q = if q ≤ m then c q else 0 :=
  rfl

/-- The truncation below degree `m` is the sum of the single classes of the components of degree
at most `m`. -/
theorem sum_single_component (m : ℕ) (c : TotalChowClass C sX) :
    ∑ p ∈ range (m + 1), single p (c p) = truncate m c := by
  refine ext fun q ↦ ?_
  rw [sum_apply, truncate_apply]
  split_ifs with hq
  · rw [Finset.sum_eq_single_of_mem q (mem_range.mpr (Nat.lt_succ_of_le hq))
      fun p _ hp ↦ single_apply_of_ne (Ne.symm hp) (c p), single_apply_same]
  · refine Finset.sum_eq_zero fun p hp ↦ single_apply_of_ne (fun h ↦ hq ?_) (c p)
    rw [h]
    exact Nat.lt_succ_iff.mp (mem_range.mp hp)

/-! ### The product only sees the low degrees -/

/-- **The degree-`m` component of a product only involves the components of degree at most `m`
of the factors**: `(c d)_m = ∑_{i + j = m} c_i d_j`. -/
theorem mul_apply_congr {c c' d d' : TotalChowClass C sX} (m : ℕ)
    (hc : ∀ i ≤ m, c i = c' i) (hd : ∀ j ≤ m, d j = d' j) : (c * d) m = (c' * d') m := by
  rw [mul_apply, mul_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [mulTerm]
  split_ifs with hj
  · rw [hc (m - j) (Nat.sub_le m j), hd j hj]
  · rfl

/-- The degree-`m` component of a product is that of the product of the truncations below any
degree at least `m`. -/
theorem mul_apply_truncate (c d : TotalChowClass C sX) {k m : ℕ} (hk : k ≤ m) :
    (truncate m c * truncate m d) k = (c * d) k :=
  mul_apply_congr k (fun i hi ↦ by rw [truncate_apply, ite_eq_left (hi.trans hk)])
    (fun j hj ↦ by rw [truncate_apply, ite_eq_left (hj.trans hk)])

end TotalChowClass

/-! ### The ring `∏_p A^p(X) ⊗ 𝐐` -/

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **`∏_{p ≥ 0} A^p(X) ⊗ 𝐐`**, the target of the Chern character: the families `(a_p)_{p ≥ 0}`
with `a_p ∈ A^p(X) ⊗ 𝐐`, at the Gysin system of the first Chern class of an invertible module. As
a group it is `Stacks.Chow.fullRationalChowCohomology`; it carries the Cauchy product. -/
def RationalTotalChowClass : Type (u + 1) :=
  fullRationalChowCohomology C (gysinSystemOfInvertible C) sX

namespace RationalTotalChowClass

/-- Families are added componentwise. -/
instance : AddCommGroup (RationalTotalChowClass C sX) :=
  inferInstanceAs (AddCommGroup (fullRationalChowCohomology C (gysinSystemOfInvertible C) sX))

/-- Families are scaled componentwise. -/
instance : Module ℚ (RationalTotalChowClass C sX) :=
  inferInstanceAs (Module ℚ (fullRationalChowCohomology C (gysinSystemOfInvertible C) sX))

variable {C sX}

/-- Two families with the same components are equal. -/
@[ext]
theorem ext {a b : RationalTotalChowClass C sX} (h : ∀ p : ℕ, a p = b p) : a = b :=
  funext h

/-- The components of `0` vanish. -/
@[simp]
theorem zero_apply (p : ℕ) : (0 : RationalTotalChowClass C sX) p = 0 :=
  rfl

/-- Families are added componentwise. -/
@[simp]
theorem add_apply (a b : RationalTotalChowClass C sX) (p : ℕ) : (a + b) p = a p + b p :=
  rfl

/-- Families are scaled componentwise. -/
@[simp]
theorem smul_apply (r : ℚ) (a : RationalTotalChowClass C sX) (p : ℕ) : (r • a) p = r • a p :=
  rfl

/-- The identification of `Stacks.Chow.fullRationalChowCohomology`, the group of families
`(a_p)_{p ≥ 0}` with `a_p ∈ A^p(X) ⊗ 𝐐`, with the ring `∏_{p ≥ 0} A^p(X) ⊗ 𝐐`. -/
def ofFamily :
    fullRationalChowCohomology C (gysinSystemOfInvertible C) sX ≃ₗ[ℚ] RationalTotalChowClass C sX :=
  LinearEquiv.refl ℚ _

/-- The identification `Stacks.Chow.RationalTotalChowClass.ofFamily` keeps the components. -/
@[simp]
theorem ofFamily_apply (a : fullRationalChowCohomology C (gysinSystemOfInvertible C) sX)
    (p : ℕ) : ofFamily a p = a p :=
  rfl

/-- The inverse of `Stacks.Chow.RationalTotalChowClass.ofFamily` keeps the components. -/
@[simp]
theorem ofFamily_symm_apply (a : RationalTotalChowClass C sX) (p : ℕ) :
    ofFamily.symm a p = a p :=
  rfl

/-! #### Components and lifts -/

/-- The degree-`p` component `𝐐 ⊗ ∏_q A^q(X) ⟶ A^p(X) ⊗ 𝐐`. -/
def rationalComponent (p : ℕ) :
    ℚ ⊗[ℤ] TotalChowClass C sX →ₗ[ℚ]
      rationalChowCohomologyComponent C (gysinSystemOfInvertible C) sX p :=
  LinearMap.baseChange ℚ (TotalChowClass.component p).toIntLinearMap

/-- The degree-`p` component of `r ⊗ c` is `r ⊗ c_p`. -/
@[simp]
theorem rationalComponent_tmul (p : ℕ) (r : ℚ) (c : TotalChowClass C sX) :
    rationalComponent p (r ⊗ₜ[ℤ] c) = r ⊗ₜ[ℤ] c p :=
  rfl

/-- The class `a ∈ A^p(X) ⊗ 𝐐` as an element of `𝐐 ⊗ ∏_q A^q(X)`. -/
def rationalSingle (p : ℕ) :
    rationalChowCohomologyComponent C (gysinSystemOfInvertible C) sX p →ₗ[ℚ]
      ℚ ⊗[ℤ] TotalChowClass C sX :=
  LinearMap.baseChange ℚ (TotalChowClass.single p).toIntLinearMap

/-- The single class of `r ⊗ x` is `r ⊗` the single class of `x`. -/
@[simp]
theorem rationalSingle_tmul (p : ℕ) (r : ℚ)
    (x : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p) :
    rationalSingle p (r ⊗ₜ[ℤ] x) = r ⊗ₜ[ℤ] TotalChowClass.single p x :=
  rfl

/-- The degree-`p` component of a single class `a ∈ A^p(X) ⊗ 𝐐` is `a`. -/
theorem rationalComponent_rationalSingle_self (p : ℕ)
    (a : rationalChowCohomologyComponent C (gysinSystemOfInvertible C) sX p) :
    rationalComponent p (rationalSingle p a) = a :=
  LinearMap.congr_fun (f := rationalComponent p ∘ₗ rationalSingle p) (g := .id)
    (TensorProduct.AlgebraTensorModule.ext fun r x ↦ by
      rw [LinearMap.comp_apply, rationalSingle_tmul, rationalComponent_tmul,
        TotalChowClass.single_apply_same]; rfl) a

/-- The components of a single class `a ∈ A^p(X) ⊗ 𝐐` in the other degrees vanish. -/
theorem rationalComponent_rationalSingle_of_ne {p q : ℕ} (h : q ≠ p)
    (a : rationalChowCohomologyComponent C (gysinSystemOfInvertible C) sX p) :
    rationalComponent q (rationalSingle p a) = 0 :=
  LinearMap.congr_fun (f := rationalComponent q ∘ₗ rationalSingle p) (g := 0)
    (TensorProduct.AlgebraTensorModule.ext fun r x ↦ by
      rw [LinearMap.comp_apply, rationalSingle_tmul, rationalComponent_tmul,
        TotalChowClass.single_apply_of_ne h]; simp) a

/-- **The truncation below degree `m`** of an element of `𝐐 ⊗ ∏_q A^q(X)`: the sum of its
components of degree at most `m`. -/
def rationalTruncate (m : ℕ) : ℚ ⊗[ℤ] TotalChowClass C sX →ₗ[ℚ] ℚ ⊗[ℤ] TotalChowClass C sX :=
  ∑ p ∈ range (m + 1), rationalSingle p ∘ₗ rationalComponent p

/-- The truncation below degree `m` is the sum of the single classes of the components of
degree at most `m`. -/
theorem rationalTruncate_apply (m : ℕ) (x : ℚ ⊗[ℤ] TotalChowClass C sX) :
    rationalTruncate m x = ∑ p ∈ range (m + 1), rationalSingle p (rationalComponent p x) := by
  rw [rationalTruncate, LinearMap.sum_apply]
  rfl

/-- On a pure tensor the truncation is that of the integral class. -/
theorem rationalTruncate_tmul (m : ℕ) (r : ℚ) (c : TotalChowClass C sX) :
    rationalTruncate m (r ⊗ₜ[ℤ] c) = r ⊗ₜ[ℤ] TotalChowClass.truncate m c := by
  rw [rationalTruncate_apply, ← TotalChowClass.sum_single_component, TensorProduct.tmul_sum]
  rfl

/-- A sum of single classes of degree at most `m` has the summands as components. -/
theorem rationalComponent_sum_rationalSingle (m : ℕ)
    (a : ∀ p : ℕ, rationalChowCohomologyComponent C (gysinSystemOfInvertible C) sX p) {k : ℕ}
    (hk : k ≤ m) :
    rationalComponent k (∑ p ∈ range (m + 1), rationalSingle p (a p)) = a k := by
  rw [map_sum, Finset.sum_eq_single k
      (fun p _ hp ↦ rationalComponent_rationalSingle_of_ne (Ne.symm hp) _)
      (fun h ↦ absurd (mem_range.mpr (Nat.lt_succ_of_le hk)) h),
    rationalComponent_rationalSingle_self]

/-- **The product in `𝐐 ⊗ ∏_q A^q(X)` only sees the low degrees**: the degree-`k` component of
`x y` is that of the product of the truncations of `x` and `y` below any `m ≥ k`. -/
theorem rationalComponent_mul_rationalTruncate (x y : ℚ ⊗[ℤ] TotalChowClass C sX) {k m : ℕ}
    (hk : k ≤ m) :
    rationalComponent k (rationalTruncate m x * rationalTruncate m y) =
      rationalComponent k (x * y) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, zero_mul, zero_mul]
  | add x x' hx hx' => rw [map_add, add_mul, add_mul, map_add, map_add, hx, hx']
  | tmul r c =>
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero, mul_zero, mul_zero]
    | add y y' hy hy' => rw [map_add, mul_add, mul_add, map_add, map_add, hy, hy']
    | tmul r' d =>
      rw [rationalTruncate_tmul, rationalTruncate_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, rationalComponent_tmul, rationalComponent_tmul,
        TotalChowClass.mul_apply_truncate c d hk]

/-- **The lift of a family below degree `m`**: `∑_{p ≤ m} a_p ∈ 𝐐 ⊗ ∏_q A^q(X)`, whose
components of degree at most `m` are those of `a`. -/
def truncatedLift (m : ℕ) : RationalTotalChowClass C sX →ₗ[ℚ] ℚ ⊗[ℤ] TotalChowClass C sX :=
  ∑ p ∈ range (m + 1), rationalSingle p ∘ₗ
    LinearMap.proj (R := ℚ)
      (φ := fun q : ℕ ↦ rationalChowCohomologyComponent C (gysinSystemOfInvertible C) sX q) p

/-- The lift below degree `m` is the sum of the single classes of the components of degree at
most `m`. -/
theorem truncatedLift_apply (m : ℕ) (a : RationalTotalChowClass C sX) :
    truncatedLift m a = ∑ p ∈ range (m + 1), rationalSingle p (a p) := by
  rw [truncatedLift, LinearMap.sum_apply]
  rfl

/-- The components of degree at most `m` of the lift below degree `m` are those of the family. -/
theorem rationalComponent_truncatedLift (m : ℕ) (a : RationalTotalChowClass C sX) {k : ℕ}
    (hk : k ≤ m) : rationalComponent k (truncatedLift m a) = a k := by
  rw [truncatedLift_apply]
  exact rationalComponent_sum_rationalSingle m a hk

/-- An element whose components of degree at most `m` are those of `a` has the lift of `a` below
degree `m` as its truncation. -/
theorem rationalTruncate_eq_truncatedLift {m : ℕ} {a : RationalTotalChowClass C sX}
    {x : ℚ ⊗[ℤ] TotalChowClass C sX} (hx : ∀ k ≤ m, rationalComponent k x = a k) :
    rationalTruncate m x = truncatedLift m a := by
  rw [rationalTruncate_apply, truncatedLift_apply]
  exact Finset.sum_congr rfl fun p hp ↦ by
    rw [hx p (Nat.lt_succ_iff.mp (mem_range.mp hp))]

/-! #### The product -/

/-- **The Cauchy product** `(a b)_m = ∑_{i + j = m} a_i b_j`: the degree-`m` component of the
product of the lifts of `a` and `b` below degree `m`. -/
instance : Mul (RationalTotalChowClass C sX) where
  mul a b m := rationalComponent m (truncatedLift m a * truncatedLift m b)

/-- The unit: the class `1 ∈ A^0(X)`, with rational coefficient `1`, and zero in positive
degrees. -/
instance : One (RationalTotalChowClass C sX) where
  one p := rationalComponent p 1

/-- The degree-`m` component of a product is that of the product of the lifts below degree
`m`. -/
theorem mul_apply (a b : RationalTotalChowClass C sX) (m : ℕ) :
    (a * b) m = rationalComponent m (truncatedLift m a * truncatedLift m b) :=
  rfl

/-- The components of the unit are those of the unit of `𝐐 ⊗ ∏_q A^q(X)`. -/
theorem one_apply (p : ℕ) : (1 : RationalTotalChowClass C sX) p = rationalComponent p 1 :=
  rfl

/-- **The degree-`m` component of a product may be computed on any lifts.** If `x` and `y` in
`𝐐 ⊗ ∏_q A^q(X)` have the components of `a` and `b` in every degree at most `m`, then
`(a b)_m` is the degree-`m` component of `x y`. -/
theorem mul_apply_eq {a b : RationalTotalChowClass C sX} {m : ℕ}
    {x y : ℚ ⊗[ℤ] TotalChowClass C sX} (hx : ∀ k ≤ m, rationalComponent k x = a k)
    (hy : ∀ k ≤ m, rationalComponent k y = b k) :
    (a * b) m = rationalComponent m (x * y) := by
  rw [mul_apply, ← rationalComponent_mul_rationalTruncate x y le_rfl,
    rationalTruncate_eq_truncatedLift hx, rationalTruncate_eq_truncatedLift hy]

/-- The components of degree at most `m` of the product of two lifts below degree `m`. -/
theorem rationalComponent_truncatedLift_mul (a b : RationalTotalChowClass C sX) {k m : ℕ}
    (hk : k ≤ m) :
    rationalComponent k (truncatedLift m a * truncatedLift m b) = (a * b) k :=
  (mul_apply_eq (fun _ hj ↦ rationalComponent_truncatedLift m a (hj.trans hk))
    (fun _ hj ↦ rationalComponent_truncatedLift m b (hj.trans hk))).symm

/-- **The ring `∏_{p ≥ 0} A^p(X) ⊗ 𝐐`**, with the Cauchy product. -/
instance instRing : Ring (RationalTotalChowClass C sX) where
  __ := (inferInstance : AddCommGroup (RationalTotalChowClass C sX))
  mul_assoc a b c := ext fun m ↦ by
    rw [mul_apply_eq (a := a * b) (b := c) (m := m)
        (fun k hk ↦ rationalComponent_truncatedLift_mul a b hk)
        (fun k hk ↦ rationalComponent_truncatedLift m c hk),
      mul_apply_eq (a := a) (b := b * c) (m := m)
        (fun k hk ↦ rationalComponent_truncatedLift m a hk)
        (fun k hk ↦ rationalComponent_truncatedLift_mul b c hk), mul_assoc]
  one_mul a := ext fun m ↦ by
    rw [mul_apply_eq (a := 1) (b := a) (m := m) (x := 1) (fun k _ ↦ (one_apply k).symm)
        (fun k hk ↦ rationalComponent_truncatedLift m a hk), one_mul,
      rationalComponent_truncatedLift m a le_rfl]
  mul_one a := ext fun m ↦ by
    rw [mul_apply_eq (a := a) (b := 1) (m := m) (y := 1)
        (fun k hk ↦ rationalComponent_truncatedLift m a hk) (fun k _ ↦ (one_apply k).symm),
      mul_one, rationalComponent_truncatedLift m a le_rfl]
  zero_mul a := ext fun m ↦ by
    rw [mul_apply, map_zero, zero_mul, map_zero]
    rfl
  mul_zero a := ext fun m ↦ by
    rw [mul_apply, map_zero, mul_zero, map_zero]
    rfl
  left_distrib a b c := ext fun m ↦ by
    rw [mul_apply, map_add, mul_add, map_add]
    rfl
  right_distrib a b c := ext fun m ↦ by
    rw [mul_apply, map_add, add_mul, map_add]
    rfl

/-! #### Integral classes -/

/-- **The ring map `∏_p A^p(X) ⟶ ∏_p A^p(X) ⊗ 𝐐`**, `c ↦ (1 ⊗ c_p)_p`. -/
def ofTotalChowClass : TotalChowClass C sX →+* RationalTotalChowClass C sX where
  toFun c p := (1 : ℚ) ⊗ₜ[ℤ] c p
  map_zero' := ext fun _ ↦ TensorProduct.tmul_zero _ _
  map_add' c d := ext fun _ ↦ TensorProduct.tmul_add _ _ _
  map_one' := rfl
  map_mul' c d := ext fun m ↦ by
    change (1 : ℚ) ⊗ₜ[ℤ] (c * d) m = _
    rw [mul_apply_eq (a := fun p ↦ (1 : ℚ) ⊗ₜ[ℤ] c p) (b := fun p ↦ (1 : ℚ) ⊗ₜ[ℤ] d p)
        (m := m) (x := (1 : ℚ) ⊗ₜ[ℤ] c) (y := (1 : ℚ) ⊗ₜ[ℤ] d) (fun k _ ↦ rfl) (fun k _ ↦ rfl),
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, rationalComponent_tmul]

/-- The components of the image of an integral total class. -/
theorem ofTotalChowClass_apply (c : TotalChowClass C sX) (p : ℕ) :
    ofTotalChowClass c p = (1 : ℚ) ⊗ₜ[ℤ] c p :=
  rfl

end RationalTotalChowClass

end Stacks.Chow

end
