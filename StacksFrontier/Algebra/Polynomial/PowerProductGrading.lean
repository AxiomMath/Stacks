module

public import Mathlib.Algebra.MonoidAlgebra.Support
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Abel
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-!
# Products `∏ (1 - [x])` in a group ring, graded by a multiplicative weight

Let `G` be a commutative group and `ν : G →* ℚ` a positive weight. For a multiset `s` of `G` write
`P(s) = ∏_{x ∈ s} (1 - [x])` in `ℤ[G]`. Provided the elements of weight `1` are of infinite order,
`P(s)` determines the part of `s` of weight `> 1` when all weights are `≥ 1`, and weights `≥ 1` on
one side of `P(X) = P(Y)` force weights `≥ 1` on the other. For a field `K`, two multisets of `Kˣ`
with the same products `∏ (1 - x ^ m)` for all `m ≥ 1` have the same `P`, and combining this with a
symmetry `y ↦ q / y` gives an equality of multisets.

## Main definitions

* `Stacks.PowerProduct.prodOneSub`: the product `P(s) = ∏_{x ∈ s} (1 - [x])` in `ℤ[G]`.
* `Stacks.PowerProduct.deg1`: the part of an element of `ℤ[G]` of weight `1`.
* `Stacks.PowerProduct.evalPow`: the evaluation `ℤ[Kˣ] → K`, `[g] ↦ g ^ m`.

## Main results

* `Stacks.PowerProduct.eq_zero_of_one_sub_single_mul_eq_zero`: `1 - [x]` is a non-zero-divisor
  for `x` of infinite order.
* `Stacks.PowerProduct.deg1_mul`: the part of weight `1` of a product of elements supported in
  weights `≥ 1` is the product of the parts of weight `1`.
* `Stacks.PowerProduct.coeff_prodOneSub_of_le`: if all weights in `s` are `> 1`, the coefficient
  of `P(s)` at an element of minimal weight is minus its multiplicity in `s`.
* `Stacks.PowerProduct.filter_eq_of_prodOneSub_eq`: `P(s)` determines the elements of `s` of
  weight `> 1`.
* `Stacks.PowerProduct.one_le_of_prodOneSub_eq`: if `P(X) = P(Y)` and all weights of `Y` are
  `≥ 1`, then all weights of `X` are `≥ 1`.
* `Stacks.PowerProduct.eq_of_prodOneSub_eq_of_map_div_eq`: two multisets `S`, `T` of `Kˣ` with
  `S` of weights `≥ 1`, `T` symmetric under `y ↦ q / y`, and the same products
  `∏ (1 - x ^ m)` and `∏ (1 - (x / q) ^ m) = ∏ (1 - y ^ (-m))` coincide.
-/

@[expose] public noncomputable section

open MonoidAlgebra

namespace Stacks.PowerProduct

variable {G : Type*} [CommGroup G] [DecidableEq G]

/-- `P(s) = ∏_{x ∈ s} (1 - [x])` in the group ring `ℤ[G]`. -/
def prodOneSub (s : Multiset G) : MonoidAlgebra ℤ G :=
  (s.map fun x => 1 - single x (1 : ℤ)).prod

omit [DecidableEq G] in
/-- `P(∅) = 1`. -/
@[simp] theorem prodOneSub_zero : prodOneSub (0 : Multiset G) = 1 := by simp [prodOneSub]

omit [DecidableEq G] in
/-- `P(x ::ₘ s) = (1 - [x]) P(s)`. -/
@[simp] theorem prodOneSub_cons (x : G) (s : Multiset G) :
    prodOneSub (x ::ₘ s) = (1 - single x (1 : ℤ)) * prodOneSub s := by
  simp [prodOneSub]

omit [DecidableEq G] in
/-- `P(s + t) = P(s) P(t)`. -/
theorem prodOneSub_add (s t : Multiset G) : prodOneSub (s + t) = prodOneSub s * prodOneSub t := by
  simp [prodOneSub]

/-! ### Non-zero-divisors -/

omit [DecidableEq G] in
/-- **`1 - [x]` is a non-zero-divisor for `x` of infinite order**: if `(1 - [x]) f = 0` in
`ℤ[G]`, then `f = 0`. -/
theorem eq_zero_of_one_sub_single_mul_eq_zero (x : G) (hx : ∀ k : ℕ, 0 < k → x ^ k ≠ 1)
    (f : MonoidAlgebra ℤ G) (h : (1 - single x (1 : ℤ)) * f = 0) : f = 0 := by
  have hf : ∀ g, f.coeff g = f.coeff (x⁻¹ * g) := by
    intro g
    have := congrArg (fun y : MonoidAlgebra ℤ G => y.coeff g) h
    simp only [sub_mul, one_mul, coeff_sub, Finsupp.sub_apply, coeff_single_mul_apply,
      coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at this
    exact sub_eq_zero.mp this
  have hk : ∀ (k : ℕ) g, f.coeff g = f.coeff (x⁻¹ ^ k * g) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro g
      rw [ih, hf]
      congr 1
      rw [pow_succ]
      ac_rfl
  apply coeff_injective
  ext g
  by_contra hg
  have hne : ∀ a b : ℕ, a < b → x⁻¹ ^ a * g ≠ x⁻¹ ^ b * g := by
    intro a b hab e
    apply hx (b - a) (by omega)
    have : x⁻¹ ^ b = x⁻¹ ^ a * x⁻¹ ^ (b - a) := by rw [← pow_add]; congr 1; omega
    rw [mul_left_inj, this, left_eq_mul, inv_pow] at e
    exact inv_eq_one.mp e
  have hinj : Function.Injective fun k : ℕ => x⁻¹ ^ k * g := by
    intro a b hab
    by_contra hab'
    rcases lt_or_gt_of_ne hab' with hlt | hlt
    · exact hne a b hlt hab
    · exact hne b a hlt hab.symm
  refine (Set.infinite_of_injective_forall_mem hinj fun k => ?_) (f.coeff.support.finite_toSet)
  rw [Finset.mem_coe, Finsupp.mem_support_iff, ← hk]
  simpa using hg

omit [DecidableEq G] in
/-- If every element of `s` has infinite order and `P(s) f = 0`, then `f = 0`. -/
theorem eq_zero_of_prodOneSub_mul_eq_zero (s : Multiset G)
    (hs : ∀ x ∈ s, ∀ k : ℕ, 0 < k → x ^ k ≠ 1) (f : MonoidAlgebra ℤ G)
    (h : prodOneSub s * f = 0) : f = 0 := by
  induction s using Multiset.induction_on generalizing f with
  | empty => simpa using h
  | cons x s ih =>
    rw [prodOneSub_cons, mul_assoc] at h
    exact ih (fun y hy => hs y (Multiset.mem_cons_of_mem hy)) f
      (eq_zero_of_one_sub_single_mul_eq_zero x (hs x (Multiset.mem_cons_self x s)) _ h)

omit [DecidableEq G] in
/-- If every element of `s` has infinite order, then `P(s) ≠ 0`. -/
theorem prodOneSub_ne_zero (s : Multiset G) (hs : ∀ x ∈ s, ∀ k : ℕ, 0 < k → x ^ k ≠ 1) :
    prodOneSub s ≠ 0 := by
  intro h0
  have := eq_zero_of_prodOneSub_mul_eq_zero s hs 1 (by rw [h0, zero_mul])
  exact one_ne_zero this

omit [DecidableEq G] in
/-- If every element of `s` has infinite order, then `P(s) f = P(s) f'` implies `f = f'`. -/
theorem cancel_prodOneSub {s : Multiset G} (hs : ∀ x ∈ s, ∀ k : ℕ, 0 < k → x ^ k ≠ 1)
    {f f' : MonoidAlgebra ℤ G} (h : prodOneSub s * f = prodOneSub s * f') : f = f' :=
  sub_eq_zero.mp (eq_zero_of_prodOneSub_mul_eq_zero s hs _ (by rw [mul_sub, h, sub_self]))

/-! ### The grading by a weight -/

variable (ν : G →* ℚ)

/-- `f` is supported in weights `≥ 1`. -/
def SuppGe (f : MonoidAlgebra ℤ G) : Prop := ∀ g ∈ f.coeff.support, 1 ≤ ν g

/-- `f` is supported in weights `> 1`. -/
def SuppGt (f : MonoidAlgebra ℤ G) : Prop := ∀ g ∈ f.coeff.support, 1 < ν g

/-- `f` is supported in weight `1`. -/
def SuppEq (f : MonoidAlgebra ℤ G) : Prop := ∀ g ∈ f.coeff.support, ν g = 1

variable {ν}
variable (hν : ∀ g, 0 < ν g)

omit [DecidableEq G] in
/-- A product of elements supported in weights `≥ 1` is supported in weights `≥ 1`. -/
theorem SuppGe.mul {f f' : MonoidAlgebra ℤ G} (hf : SuppGe ν f) (hf' : SuppGe ν f') :
    SuppGe ν (f * f') := by
  classical
  intro g hg
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_mul.mp (support_coeff_mul_subset f f' hg)
  rw [map_mul]
  exact one_le_mul_of_one_le_of_one_le (hf a ha) (hf' b hb)

include hν in
omit [DecidableEq G] in
/-- If `f` is supported in weights `≥ 1` and `f'` in weights `> 1`, then `f * f'` is supported
in weights `> 1`. -/
theorem SuppGe.mul_suppGt {f f' : MonoidAlgebra ℤ G} (hf : SuppGe ν f) (hf' : SuppGt ν f') :
    SuppGt ν (f * f') := by
  classical
  intro g hg
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_mul.mp (support_coeff_mul_subset f f' hg)
  rw [map_mul]
  calc (1 : ℚ) < 1 * ν b := by rw [one_mul]; exact hf' b hb
    _ ≤ ν a * ν b := mul_le_mul_of_nonneg_right (hf a ha) (hν b).le

include hν in
omit [DecidableEq G] in
/-- If `f` is supported in weights `> 1` and `f'` in weights `≥ 1`, then `f * f'` is supported
in weights `> 1`. -/
theorem SuppGt.mul_suppGe {f f' : MonoidAlgebra ℤ G} (hf : SuppGt ν f) (hf' : SuppGe ν f') :
    SuppGt ν (f * f') := by
  classical
  rw [mul_comm]
  exact hf'.mul_suppGt hν hf

omit [DecidableEq G] in
/-- A product of elements supported in weight `1` is supported in weight `1`. -/
theorem SuppEq.mul {f f' : MonoidAlgebra ℤ G} (hf : SuppEq ν f) (hf' : SuppEq ν f') :
    SuppEq ν (f * f') := by
  classical
  intro g hg
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_mul.mp (support_coeff_mul_subset f f' hg)
  rw [map_mul, hf a ha, hf' b hb, one_mul]

/-- The part of weight `1`. -/
def deg1 (ν : G →* ℚ) (f : MonoidAlgebra ℤ G) : MonoidAlgebra ℤ G :=
  ofCoeff (f.coeff.filter fun g => ν g = 1)

/-- The part of weight `≠ 1`. -/
def degNe1 (ν : G →* ℚ) (f : MonoidAlgebra ℤ G) : MonoidAlgebra ℤ G :=
  ofCoeff (f.coeff.filter fun g => ¬ ν g = 1)

omit [DecidableEq G] in
/-- `f` is the sum of its part of weight `1` and its part of weight `≠ 1`. -/
theorem deg1_add_degNe1 (f : MonoidAlgebra ℤ G) : deg1 ν f + degNe1 ν f = f :=
  coeff_injective <| Finsupp.filter_add_filter_not _ _

omit [DecidableEq G] in
/-- Taking the part of weight `1` is additive. -/
theorem deg1_add (f f' : MonoidAlgebra ℤ G) : deg1 ν (f + f') = deg1 ν f + deg1 ν f' :=
  coeff_injective Finsupp.filter_add

omit [DecidableEq G] in
/-- The part of weight `1` of `f` is supported in weight `1`. -/
theorem suppEq_deg1 (f : MonoidAlgebra ℤ G) : SuppEq ν (deg1 ν f) := by
  intro g hg
  rw [deg1, coeff_ofCoeff, Finsupp.support_filter, Finset.mem_filter] at hg
  exact hg.2

omit [DecidableEq G] in
/-- An element supported in weight `1` is its own part of weight `1`. -/
theorem deg1_of_suppEq {f : MonoidAlgebra ℤ G} (hf : SuppEq ν f) : deg1 ν f = f := by
  apply coeff_injective
  rw [deg1, coeff_ofCoeff, Finsupp.filter_eq_self_iff]
  exact fun g hg => hf g (Finsupp.mem_support_iff.mpr hg)

omit [DecidableEq G] in
/-- An element supported in weights `> 1` has zero part of weight `1`. -/
theorem deg1_of_suppGt {f : MonoidAlgebra ℤ G} (hf : SuppGt ν f) : deg1 ν f = 0 := by
  apply coeff_injective
  rw [deg1, coeff_ofCoeff, coeff_zero, Finsupp.filter_eq_zero_iff]
  exact fun g hg => Finsupp.notMem_support_iff.mp fun h0 => (hf g h0).ne' hg

omit [DecidableEq G] in
/-- An element supported in weights `> 1` is supported in weights `≥ 1`. -/
theorem SuppGt.suppGe {f : MonoidAlgebra ℤ G} (hf : SuppGt ν f) : SuppGe ν f :=
  fun g hg => (hf g hg).le

omit [DecidableEq G] in
/-- If `f` is supported in weights `≥ 1`, its part of weight `≠ 1` is supported in
weights `> 1`. -/
theorem SuppGe.degNe1 {f : MonoidAlgebra ℤ G} (hf : SuppGe ν f) :
    SuppGt ν (Stacks.PowerProduct.degNe1 ν f) := by
  intro g hg
  rw [Stacks.PowerProduct.degNe1, coeff_ofCoeff, Finsupp.support_filter, Finset.mem_filter] at hg
  exact lt_of_le_of_ne (hf g hg.1) (Ne.symm hg.2)

omit [DecidableEq G] in
/-- The part of weight `1` of `f` is supported in weights `≥ 1`. -/
theorem SuppGe.deg1 {f : MonoidAlgebra ℤ G} : SuppGe ν (Stacks.PowerProduct.deg1 ν f) := by
  intro g hg
  rw [suppEq_deg1 f g hg]

include hν in
omit [DecidableEq G] in
/-- **The part of weight `1` of a product is the product of the parts of weight `1`**, for
factors supported in weights `≥ 1`. -/
theorem deg1_mul {f f' : MonoidAlgebra ℤ G} (hf : SuppGe ν f) (hf' : SuppGe ν f') :
    deg1 ν (f * f') = deg1 ν f * deg1 ν f' := by
  classical
  conv_lhs => rw [← deg1_add_degNe1 (ν := ν) f, ← deg1_add_degNe1 (ν := ν) f']
  rw [add_mul, mul_add, mul_add, deg1_add, deg1_add, deg1_add,
    deg1_of_suppEq ((suppEq_deg1 f).mul (suppEq_deg1 f')),
    deg1_of_suppGt (SuppGe.deg1.mul_suppGt hν hf'.degNe1),
    deg1_of_suppGt (hf.degNe1.mul_suppGe hν SuppGe.deg1),
    deg1_of_suppGt (hf.degNe1.mul_suppGe hν hf'.degNe1.suppGe), add_zero, add_zero, add_zero]

/-! ### Products of `1 - [x]` -/

/-- The coefficient of `1 ∈ ℤ[G]` at `h` is `1` if `h = 1` and `0` otherwise. -/
theorem coeff_one_apply (h : G) : (1 : MonoidAlgebra ℤ G).coeff h = if h = 1 then 1 else 0 := by
  rw [one_def, coeff_single, Finsupp.single_apply]
  simp only [eq_comm]

omit [DecidableEq G] in
/-- `1 ∈ ℤ[G]` is supported in weight `1`. -/
theorem suppEq_one : SuppEq ν (1 : MonoidAlgebra ℤ G) := by
  classical
  intro g hg
  rw [Finsupp.mem_support_iff, coeff_one_apply] at hg
  split_ifs at hg with h
  · rw [h, map_one]
  · exact absurd rfl hg

omit [DecidableEq G] in
/-- If `ν x ≥ 1`, then `1 - [x]` is supported in weights `≥ 1`. -/
theorem SuppGe.one_sub_single {x : G} (hx : 1 ≤ ν x) :
    SuppGe ν (1 - single x (1 : ℤ)) := by
  classical
  intro g hg
  rw [Finsupp.mem_support_iff, coeff_sub, Finsupp.sub_apply, coeff_one_apply, coeff_single,
    Finsupp.single_apply] at hg
  by_cases h1 : g = 1
  · rw [h1, map_one]
  · by_cases h2 : x = g
    · rw [← h2]; exact hx
    · simp [h1, h2] at hg

omit [DecidableEq G] in
/-- If all elements of `s` have weight `≥ 1`, then `P(s)` is supported in weights `≥ 1`. -/
theorem SuppGe.prodOneSub {s : Multiset G} (hs : ∀ x ∈ s, 1 ≤ ν x) :
    SuppGe ν (prodOneSub s) := by
  classical
  induction s using Multiset.induction_on with
  | empty =>
    rw [prodOneSub_zero]
    intro g hg
    rw [suppEq_one g hg]
  | cons x s ih =>
    rw [prodOneSub_cons]
    exact (SuppGe.one_sub_single (hs x (Multiset.mem_cons_self x s))).mul
      (ih fun y hy => hs y (Multiset.mem_cons_of_mem hy))

omit [DecidableEq G] in
/-- The part of weight `1` of `1 - [x]` is `1 - [x]` if `ν x = 1` and `1` otherwise. -/
theorem deg1_one_sub_single {x : G} :
    deg1 ν (1 - single x (1 : ℤ)) = if ν x = 1 then 1 - single x 1 else 1 := by
  classical
  apply coeff_injective
  ext g
  rw [deg1, coeff_ofCoeff, Finsupp.filter_apply]
  by_cases hx : ν x = 1
  · rw [ite_eq_left hx]
    split_ifs with hg
    · rfl
    · rw [coeff_sub, Finsupp.sub_apply, coeff_one_apply, coeff_single, Finsupp.single_apply]
      have h1 : g ≠ 1 := fun h => hg (by rw [h, map_one])
      have h2 : x ≠ g := fun h => hg (by rw [← h, hx])
      simp [h1, h2]
  · rw [ite_eq_right hx]
    rw [coeff_sub, Finsupp.sub_apply, coeff_one_apply, coeff_single, Finsupp.single_apply]
    by_cases hg : ν g = 1
    · have h2 : x ≠ g := fun h => hx (by rw [h, hg])
      simp [hg, h2]
    · have h1 : g ≠ 1 := fun h => hg (by rw [h, map_one])
      simp [hg, h1]

include hν in
omit [DecidableEq G] in
/-- The part of weight `1` of `P(s)` is `P` of the elements of weight `1`. -/
theorem deg1_prodOneSub {s : Multiset G} (hs : ∀ x ∈ s, 1 ≤ ν x) :
    deg1 ν (prodOneSub s) = prodOneSub (s.filter fun x => ν x = 1) := by
  classical
  induction s using Multiset.induction_on with
  | empty => rw [prodOneSub_zero, deg1_of_suppEq suppEq_one, Multiset.filter_zero, prodOneSub_zero]
  | cons x s ih =>
    have hs' : ∀ y ∈ s, 1 ≤ ν y := fun y hy => hs y (Multiset.mem_cons_of_mem hy)
    rw [prodOneSub_cons, deg1_mul hν (SuppGe.one_sub_single (hs x (Multiset.mem_cons_self x s)))
      (SuppGe.prodOneSub hs'), ih hs', deg1_one_sub_single, Multiset.filter_cons]
    split_ifs with hx
    · rw [Multiset.singleton_add, prodOneSub_cons]
    · rw [zero_add, one_mul]

include hν in
omit [DecidableEq G] in
/-- If all elements of `s` have weight `> 1`, then at an element `h` of weight `≤ 1` the
coefficient of `P(s)` equals that of `1`. -/
theorem coeff_prodOneSub_of_le_one {s : Multiset G} (hs : ∀ y ∈ s, 1 < ν y) {h : G}
    (hh : ν h ≤ 1) : (prodOneSub s).coeff h = (1 : MonoidAlgebra ℤ G).coeff h := by
  classical
  rcases hh.lt_or_eq with hlt | heq
  · have h1 : h ≠ 1 := fun e => by rw [e, map_one] at hlt; exact lt_irrefl _ hlt
    rw [coeff_one_apply, ite_eq_right h1]
    by_contra h0
    exact (not_le.mpr hlt) (SuppGe.prodOneSub (fun y hy => (hs y hy).le) h
      (Finsupp.mem_support_iff.mpr h0))
  · have hd := deg1_prodOneSub hν (s := s) (fun y hy => (hs y hy).le)
    rw [Multiset.filter_eq_nil.mpr (fun y hy => (hs y hy).ne'), prodOneSub_zero] at hd
    have := congrArg (fun f : MonoidAlgebra ℤ G => f.coeff h) hd
    simp only [deg1, coeff_ofCoeff, Finsupp.filter_apply, ite_eq_left heq] at this
    exact this

include hν in
/-- **The coefficient at an element of minimal weight** of `P(s)`, all weights `> 1`, is minus
its multiplicity in `s`. -/
theorem coeff_prodOneSub_of_le {s : Multiset G} (hs : ∀ y ∈ s, 1 < ν y) {g : G}
    (hg : 1 < ν g) (hmin : ∀ y ∈ s, ν g ≤ ν y) : (prodOneSub s).coeff g = -(s.count g : ℤ) := by
  have hg1 : g ≠ 1 := fun e => by rw [e, map_one] at hg; exact lt_irrefl _ hg
  induction s using Multiset.induction_on with
  | empty => rw [prodOneSub_zero, coeff_one_apply, ite_eq_right hg1]; simp
  | cons y s ih =>
    have hs' : ∀ z ∈ s, 1 < ν z := fun z hz => hs z (Multiset.mem_cons_of_mem hz)
    have hy := hs y (Multiset.mem_cons_self y s)
    have hle : ν (y⁻¹ * g) ≤ 1 := by
      rw [map_mul, map_inv, inv_mul_le_one₀ (hν y)]
      exact hmin y (Multiset.mem_cons_self y s)
    rw [prodOneSub_cons, sub_mul, one_mul, coeff_sub, Finsupp.sub_apply, coeff_single_mul_apply,
      one_mul, coeff_prodOneSub_of_le_one hν hs' hle, coeff_one_apply,
      ih hs' (fun z hz => hmin z (Multiset.mem_cons_of_mem hz)), Multiset.count_cons]
    by_cases hyg : y = g
    · subst hyg
      simp only [inv_mul_cancel, ite_true]
      push_cast
      ring
    · have : y⁻¹ * g ≠ 1 := fun e => hyg (by rw [inv_mul_eq_one] at e; exact e)
      simp [this, Ne.symm hyg]

/-- `∑_{x ∈ s} [x]`. -/
def sumSingle (s : Multiset G) : MonoidAlgebra ℤ G := (s.map fun x => single x (1 : ℤ)).sum

omit [CommGroup G] in
/-- The coefficient of `∑_{x ∈ s} [x]` at `z` is the multiplicity of `z` in `s`. -/
theorem coeff_sumSingle (s : Multiset G) (z : G) : (sumSingle s).coeff z = (s.count z : ℤ) := by
  induction s using Multiset.induction_on with
  | empty => simp [sumSingle]
  | cons x s ih =>
    simp only [sumSingle, Multiset.map_cons, Multiset.sum_cons, coeff_add, Finsupp.add_apply,
      coeff_single, Finsupp.single_apply, Multiset.count_cons] at ih ⊢
    rw [ih]
    by_cases hxz : x = z
    · subst hxz; simp [add_comm]
    · simp [hxz, Ne.symm hxz]

include hν in
omit [DecidableEq G] in
/-- **`P(s)` determines the elements of weight `> 1`**, when all weights are `≥ 1` and the
elements of weight `1` have infinite order. -/
theorem filter_eq_of_prodOneSub_eq : ∀ (X Y : Multiset G), (∀ x ∈ X, 1 ≤ ν x) →
    (∀ y ∈ Y, 1 ≤ ν y) → (∀ x ∈ X + Y, ν x = 1 → ∀ k : ℕ, 0 < k → x ^ k ≠ 1) →
    prodOneSub X = prodOneSub Y → X.filter (fun x => 1 < ν x) = Y.filter (fun x => 1 < ν x) := by
  classical
  intro X Y
  induction h : Multiset.card X + Multiset.card Y using Nat.strong_induction_on generalizing X Y
    with
  | _ N ih =>
  intro hX hY h1 hP
  set X1 := X.filter (fun x => ν x = 1)
  set Y1 := Y.filter (fun x => ν x = 1)
  set X2 := X.filter (fun x => 1 < ν x)
  set Y2 := Y.filter (fun x => 1 < ν x)
  have hsplit : ∀ Z : Multiset G, (∀ x ∈ Z, 1 ≤ ν x) →
      Z = Z.filter (fun x => ν x = 1) + Z.filter (fun x => 1 < ν x) := by
    intro Z hZ
    conv_lhs => rw [← Multiset.filter_add_not (fun x => ν x = 1) Z]
    congr 1
    exact Multiset.filter_congr fun x hx => ⟨fun h => lt_of_le_of_ne (hZ x hx) (Ne.symm h),
      fun h e => (ne_of_gt h) e⟩
  have hXs : X = X1 + X2 := hsplit X hX
  have hYs : Y = Y1 + Y2 := hsplit Y hY
  have hA : prodOneSub X1 = prodOneSub Y1 := by
    rw [← deg1_prodOneSub hν hX, ← deg1_prodOneSub hν hY, hP]
  by_cases hemp : X2 + Y2 = 0
  · have hc := congrArg Multiset.card hemp
    rw [Multiset.card_add, Multiset.card_zero] at hc
    rw [Multiset.card_eq_zero.mp (by omega : Multiset.card X2 = 0),
      Multiset.card_eq_zero.mp (by omega : Multiset.card Y2 = 0)]
  obtain ⟨g, hgmem', hgmin'⟩ := (X2 + Y2).toFinset.exists_min_image ν
    (Multiset.toFinset_nonempty.mpr hemp)
  have hgmem : g ∈ X2 + Y2 := Multiset.mem_toFinset.mp hgmem'
  have hgmin : ∀ y ∈ X2 + Y2, ν g ≤ ν y := fun y hy => hgmin' y (Multiset.mem_toFinset.mpr hy)
  have hg2 : 1 < ν g := by
    rcases Multiset.mem_add.mp hgmem with h' | h'
    · exact (Multiset.mem_filter.mp h').2
    · exact (Multiset.mem_filter.mp h').2
  have hX2 : ∀ y ∈ X2, 1 < ν y := fun y hy => (Multiset.mem_filter.mp hy).2
  have hY2 : ∀ y ∈ Y2, 1 < ν y := fun y hy => (Multiset.mem_filter.mp hy).2
  set A := prodOneSub X1
  have hA1 : SuppEq ν A := by
    have := suppEq_deg1 (ν := ν) (prodOneSub X)
    rwa [deg1_prodOneSub hν hX] at this
  have key : ∀ (Z : Multiset G) (hZ : ∀ y ∈ Z, 1 < ν y) (hZmin : ∀ y ∈ Z, ν g ≤ ν y) (h : G),
      (A * sumSingle (Z.filter fun x => ν x = ν g)).coeff h =
        if ν h = ν g then -(A * prodOneSub Z).coeff h else 0 := by
    intro Z hZ hZmin h
    rw [coeff_mul_apply_left, coeff_mul_apply_left]
    split_ifs with hh
    · rw [← Finsupp.sum_neg]
      refine Finsupp.sum_congr fun a ha => ?_
      have hνa : ν a = 1 := hA1 a ha
      have hνh : ν (a⁻¹ * h) = ν g := by rw [map_mul, map_inv, hνa, inv_one, one_mul, hh]
      rw [coeff_sumSingle, Multiset.count_filter_of_pos (p := fun x => ν x = ν g) hνh,
        coeff_prodOneSub_of_le hν hZ (hνh ▸ hg2) (fun y hy => hνh ▸ hZmin y hy)]
      ring
    · refine Finset.sum_eq_zero fun a ha => ?_
      have hνa : ν a = 1 := hA1 a ha
      have hνh : ν (a⁻¹ * h) ≠ ν g := by rw [map_mul, map_inv, hνa, inv_one, one_mul]; exact hh
      change A.coeff a * (sumSingle _).coeff (a⁻¹ * h) = 0
      rw [coeff_sumSingle, Multiset.count_filter_of_neg (p := fun x => ν x = ν g) hνh,
        Nat.cast_zero, mul_zero]
  have hXmin : ∀ y ∈ X2, ν g ≤ ν y := fun y hy => hgmin y (Multiset.mem_add.mpr (Or.inl hy))
  have hYmin : ∀ y ∈ Y2, ν g ≤ ν y := fun y hy => hgmin y (Multiset.mem_add.mpr (Or.inr hy))
  have hEq : A * sumSingle (X2.filter fun x => ν x = ν g) =
      A * sumSingle (Y2.filter fun x => ν x = ν g) := by
    apply coeff_injective
    ext h
    rw [key X2 hX2 hXmin h, key Y2 hY2 hYmin h, ← prodOneSub_add, ← hXs, hA, ← prodOneSub_add,
      ← hYs, hP]
  have hinf1 : ∀ x ∈ X1, ∀ k : ℕ, 0 < k → x ^ k ≠ 1 := fun x hx =>
    h1 x (Multiset.mem_add.mpr (Or.inl (Multiset.mem_of_mem_filter hx)))
      (Multiset.mem_filter.mp hx).2
  have hD := cancel_prodOneSub hinf1 hEq
  have hcount := congrArg (fun f : MonoidAlgebra ℤ G => f.coeff g) hD
  simp only [coeff_sumSingle,
    Multiset.count_filter_of_pos (p := fun x => ν x = ν g) (rfl : ν g = ν g)] at hcount
  have hcnt : X2.count g = Y2.count g := by exact_mod_cast hcount
  have hgX : g ∈ X2 := by
    rcases Multiset.mem_add.mp hgmem with h' | h'
    · exact h'
    · rw [← Multiset.count_pos, hcnt]; exact Multiset.count_pos.mpr h'
  have hgY : g ∈ Y2 := by rw [← Multiset.count_pos, ← hcnt]; exact Multiset.count_pos.mpr hgX
  have hgXX : g ∈ X := Multiset.mem_of_mem_filter hgX
  have hgYY : g ∈ Y := Multiset.mem_of_mem_filter hgY
  have hginf : ∀ k : ℕ, 0 < k → g ^ k ≠ 1 := by
    intro k hk e
    have := congrArg ν e
    rw [map_pow, map_one] at this
    exact (one_lt_pow₀ hg2 hk.ne').ne' this
  have hP' : prodOneSub (X.erase g) = prodOneSub (Y.erase g) := by
    have hX' := Multiset.cons_erase hgXX
    have hY' := Multiset.cons_erase hgYY
    rw [← hX', ← hY', prodOneSub_cons, prodOneSub_cons] at hP
    exact cancel_prodOneSub (s := {g}) (by simpa using hginf) (by simpa [prodOneSub] using hP)
  have hcard : Multiset.card (X.erase g) + Multiset.card (Y.erase g) < N := by
    rw [← h, Multiset.card_erase_of_mem hgXX, Multiset.card_erase_of_mem hgYY,
      Nat.pred_eq_sub_one, Nat.pred_eq_sub_one]
    have := Multiset.card_pos_iff_exists_mem.mpr ⟨g, hgXX⟩
    have := Multiset.card_pos_iff_exists_mem.mpr ⟨g, hgYY⟩
    omega
  have IH := ih _ hcard (X.erase g) (Y.erase g) rfl
    (fun x hx => hX x (Multiset.mem_of_mem_erase hx))
    (fun y hy => hY y (Multiset.mem_of_mem_erase hy))
    (fun x hx => h1 x (by
      rcases Multiset.mem_add.mp hx with h' | h'
      · exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_of_mem_erase h'))
      · exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_of_mem_erase h')))) hP'
  change Multiset.filter (fun x => 1 < ν x) X = Multiset.filter (fun x => 1 < ν x) Y
  rw [← Multiset.cons_erase hgXX, ← Multiset.cons_erase hgYY,
    Multiset.filter_cons_of_pos (p := fun x => 1 < ν x) _ hg2,
    Multiset.filter_cons_of_pos (p := fun x => 1 < ν x) _ hg2, IH]

omit [DecidableEq G] in
/-- `P(s) = [∏ s] · (-1)^{#s} · P(s⁻¹)`: `1 - [x] = -[x] (1 - [x⁻¹])`. -/
theorem prodOneSub_eq_single_mul_map_inv (s : Multiset G) :
    prodOneSub s = single s.prod ((-1 : ℤ) ^ Multiset.card s) * prodOneSub (s.map (·⁻¹)) := by
  induction s using Multiset.induction_on with
  | empty => simp [one_def]
  | cons x s ih =>
    rw [prodOneSub_cons, ih, Multiset.map_cons, prodOneSub_cons, Multiset.prod_cons,
      Multiset.card_cons, ← mul_assoc, ← mul_assoc]
    congr 1
    rw [sub_mul, mul_sub, one_mul, mul_one, single_mul_single, single_mul_single, one_mul,
      mul_one, mul_inv_cancel_comm, pow_succ]
    simp only [mul_neg_one, single_neg]
    abel

include hν in
omit [DecidableEq G] in
/-- The product of a non-empty multiset of elements of weight `< 1` has weight `< 1`. -/
theorem prod_lt_one {s : Multiset G} (hs0 : s ≠ 0) (hs : ∀ x ∈ s, ν x < 1) : ν s.prod < 1 := by
  classical
  induction s using Multiset.induction_on with
  | empty => exact absurd rfl hs0
  | cons x s ih =>
    rw [Multiset.prod_cons, map_mul]
    by_cases h0 : s = 0
    · rw [h0, Multiset.prod_zero, map_one, mul_one]; exact hs x (Multiset.mem_cons_self x s)
    · exact (mul_lt_mul'' (hs x (Multiset.mem_cons_self x s))
        (ih h0 fun y hy => hs y (Multiset.mem_cons_of_mem hy)) (hν x).le (hν _).le).trans_eq
        (one_mul 1)

include hν in
omit [DecidableEq G] in
/-- **Weights `≥ 1` on one side force weights `≥ 1` on the other.** If `P(X) = P(Y)`, all
weights of `Y` are at least `1`, and the elements of `X` of weight `1` have infinite order, then
all weights of `X` are at least `1`. -/
theorem one_le_of_prodOneSub_eq (X Y : Multiset G) (hY : ∀ y ∈ Y, 1 ≤ ν y)
    (hinf : ∀ x ∈ X, ν x = 1 → ∀ k : ℕ, 0 < k → x ^ k ≠ 1) (h : prodOneSub X = prodOneSub Y) :
    ∀ x ∈ X, 1 ≤ ν x := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨x₀, hx₀, hlt₀⟩ := hcon
  set D := X.filter (fun x => ν x < 1)
  set E := X.filter (fun x => ¬ ν x < 1)
  have hD0 : D ≠ 0 := fun h0 => by
    have : x₀ ∈ D := Multiset.mem_filter.mpr ⟨hx₀, hlt₀⟩
    rw [h0] at this; exact Multiset.notMem_zero _ this
  have hDlt : ∀ x ∈ D, ν x < 1 := fun x hx => (Multiset.mem_filter.mp hx).2
  set s' := D.map (·⁻¹) + E
  set c : ℤ := (-1) ^ Multiset.card D
  have hc : c * c = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
  have hX : prodOneSub X = single D.prod c * prodOneSub s' := by
    rw [← Multiset.filter_add_not (fun x => ν x < 1) X, prodOneSub_add,
      prodOneSub_eq_single_mul_map_inv D, prodOneSub_add, mul_assoc]
  have hs' : prodOneSub s' = single D.prod⁻¹ c * prodOneSub Y := by
    rw [← h, hX, ← mul_assoc, single_mul_single, inv_mul_cancel, hc, ← one_def, one_mul]
  have hs'ge : ∀ y ∈ s', 1 ≤ ν y := by
    intro y hy
    rcases Multiset.mem_add.mp hy with hy | hy
    · obtain ⟨d, hd, rfl⟩ := Multiset.mem_map.mp hy
      rw [map_inv]
      exact (one_le_inv₀ (hν d)).mpr (hDlt d hd).le
    · exact not_lt.mp (Multiset.mem_filter.mp hy).2
  have hne : prodOneSub (s'.filter fun x => ν x = 1) ≠ 0 := by
    refine prodOneSub_ne_zero _ fun y hy => ?_
    obtain ⟨hy, hy1⟩ := Multiset.mem_filter.mp hy
    rcases Multiset.mem_add.mp hy with hy' | hy'
    · obtain ⟨d, hd, rfl⟩ := Multiset.mem_map.mp hy'
      rw [map_inv] at hy1
      exact absurd hy1 (ne_of_gt ((one_lt_inv₀ (hν d)).mpr (hDlt d hd)))
    · exact hinf y (Multiset.mem_of_mem_filter hy') hy1
  apply hne
  rw [← deg1_prodOneSub hν hs'ge, hs']
  apply deg1_of_suppGt
  refine SuppGt.mul_suppGe hν ?_ (SuppGe.prodOneSub hY)
  intro g hg
  rw [coeff_single, Finsupp.support_single _ (by
    intro h0; rw [h0, zero_mul] at hc; exact zero_ne_one hc), Finset.mem_singleton] at hg
  rw [hg, map_inv]
  exact (one_lt_inv₀ (hν _)).mpr (prod_lt_one hν hD0 hDlt)

/-! ### From products of numbers to the group ring -/

section Field

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

/-- The evaluation `ℤ[Kˣ] → K`, `[g] ↦ g ^ m`. -/
def evalPow (m : ℕ) : MonoidAlgebra ℤ Kˣ →ₐ[ℤ] K :=
  MonoidAlgebra.lift ℤ K Kˣ ((powMonoidHom m).comp (Units.coeHom K))

omit [CharZero K] [DecidableEq K] in
/-- `evalPow m` sends `P(s)` to `∏_{x ∈ s} (1 - x ^ m)`. -/
theorem evalPow_prodOneSub (m : ℕ) (s : Multiset Kˣ) :
    evalPow m (prodOneSub s) = (s.map fun x : Kˣ => 1 - (x : K) ^ m).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    rw [prodOneSub_cons, map_mul, ih, Multiset.map_cons, Multiset.prod_cons, map_sub, map_one,
      evalPow, MonoidAlgebra.lift_single]
    simp

omit [DecidableEq K] in
/-- **Linear independence of the characters `m ↦ g^m`**: an element of `ℤ[Kˣ]` killed by every
`evalPow m`, `m ≥ 1`, is zero. -/
theorem eq_zero_of_evalPow_eq_zero (f : MonoidAlgebra ℤ Kˣ)
    (h : ∀ m : ℕ, 0 < m → evalPow m f = 0) : f = 0 := by
  have hsum : ∀ m : ℕ, ∑ g ∈ f.coeff.support, ((f.coeff g : K) * g) * (g : K) ^ m = 0 := by
    intro m
    have hm := h (m + 1) (Nat.succ_pos m)
    rw [evalPow, MonoidAlgebra.lift_apply] at hm
    rw [← hm]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply, powMonoidHom_apply,
      zsmul_eq_mul]
    ring
  let χ : f.coeff.support → (Multiplicative ℕ →* K) := fun g => powersHom K (g.1 : K)
  have hχinj : Function.Injective χ := fun g g' e => by
    have := congrArg (fun F : Multiplicative ℕ →* K => F (Multiplicative.ofAdd 1)) e
    simp only [χ, powersHom_apply, toAdd_ofAdd, pow_one] at this
    exact Subtype.ext (Units.ext this)
  have hli : LinearIndependent K fun g : f.coeff.support => (χ g : Multiplicative ℕ → K) :=
    (linearIndependent_monoidHom (Multiplicative ℕ) K).comp χ hχinj
  have hcoef := Fintype.linearIndependent_iff.1 hli (fun g => (f.coeff g.1 : K) * g.1)
    (funext fun m => by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, χ, powersHom_apply]
      rw [← hsum (Multiplicative.toAdd m)]
      exact Finset.sum_coe_sort f.coeff.support
        fun g => (f.coeff g : K) * g * (g : K) ^ (Multiplicative.toAdd m))
  apply coeff_injective
  ext g
  by_contra hg
  have hmem : g ∈ f.coeff.support := Finsupp.mem_support_iff.mpr hg
  have := hcoef ⟨g, hmem⟩
  rw [mul_eq_zero] at this
  rcases this with h0 | h0
  · exact hg (by exact_mod_cast h0)
  · exact g.ne_zero h0

omit [DecidableEq K] in
/-- If `∏_{x ∈ s} (1 - x ^ m) = ∏_{x ∈ t} (1 - x ^ m)` in `K` for all `m ≥ 1`, then
`P(s) = P(t)` in `ℤ[Kˣ]`. -/
theorem prodOneSub_eq_of_prod_eq (s t : Multiset Kˣ)
    (h : ∀ m : ℕ, 0 < m → (s.map fun x : Kˣ => 1 - (x : K) ^ m).prod =
      (t.map fun x : Kˣ => 1 - (x : K) ^ m).prod) : prodOneSub s = prodOneSub t :=
  sub_eq_zero.mp (eq_zero_of_evalPow_eq_zero _ fun m hm => by
    rw [map_sub, evalPow_prodOneSub, evalPow_prodOneSub, h m hm, sub_self])

omit [DecidableEq K] in
/-- If `∏_{x ∈ s} (1 - x ^ m) ≠ 0` for all `m ≥ 1`, then every element of `s` has infinite
order. -/
theorem pow_ne_one_of_prod_ne_zero {s : Multiset Kˣ}
    (hne : ∀ m : ℕ, 0 < m → (s.map fun x : Kˣ => 1 - (x : K) ^ m).prod ≠ 0) :
    ∀ x ∈ s, ∀ k : ℕ, 0 < k → x ^ k ≠ 1 := fun x hx k hk e =>
  hne k hk <| Multiset.prod_eq_zero_iff.mpr <| Multiset.mem_map.mpr
    ⟨x, hx, by rw [← Units.val_pow_eq_pow_val, e, Units.val_one, sub_self]⟩

omit [DecidableEq K] in
/-- **Two families with the same products `∏ (1 - x^m)` and `∏ (1 - (x/q)^m) = ∏ (1 - y^{-m})`
coincide**, for a positive weight `ν` with `ν ≥ 1` on the first family and `ν q > 1`, when the
second family is symmetric under `y ↦ q / y` and its products `∏ (1 - y ^ m)` are non-zero. -/
theorem eq_of_prodOneSub_eq_of_map_div_eq (ν : Kˣ →* ℚ) (hν : ∀ g, 0 < ν g) (q : Kˣ)
    (hq : 1 < ν q) (S T : Multiset Kˣ) (hS : ∀ x ∈ S, 1 ≤ ν x)
    (hsym : T.map (fun y => q * y⁻¹) = T)
    (hne : ∀ m : ℕ, 0 < m → (T.map fun y : Kˣ => 1 - (y : K) ^ m).prod ≠ 0)
    (hG1 : ∀ m : ℕ, 0 < m → (S.map fun x : Kˣ => 1 - (x : K) ^ m).prod =
      (T.map fun y : Kˣ => 1 - (y : K) ^ m).prod)
    (hG2 : ∀ m : ℕ, 0 < m → ((S.map (· * q⁻¹)).map fun x : Kˣ => 1 - (x : K) ^ m).prod =
      ((T.map (·⁻¹)).map fun y : Kˣ => 1 - (y : K) ^ m).prod) : S = T := by
  classical
  have hTinf := pow_ne_one_of_prod_ne_zero hne
  have hSinf := pow_ne_one_of_prod_ne_zero (s := S) (fun m hm => hG1 m hm ▸ hne m hm)
  have hP1 := prodOneSub_eq_of_prod_eq S T hG1
  have hT : ∀ y ∈ T, 1 ≤ ν y := one_le_of_prodOneSub_eq hν T S hS
    (fun y hy _ => hTinf y hy) hP1.symm
  have hgt := filter_eq_of_prodOneSub_eq hν S T hS hT (fun x hx _ => by
    rcases Multiset.mem_add.mp hx with h | h
    · exact hSinf x h
    · exact hTinf x h) hP1
  let ν' : Kˣ →* ℚ := (ν.comp (MulEquiv.inv Kˣ).toMonoidHom)
  have hν'apply : ∀ g, ν' g = (ν g)⁻¹ := fun g => by simp [ν', map_inv]
  have hν' : ∀ g, 0 < ν' g := fun g => by rw [hν'apply]; exact inv_pos.mpr (hν g)
  have hP2 := prodOneSub_eq_of_prod_eq _ _ hG2
  have hTi : ∀ y ∈ T.map (·⁻¹), 1 ≤ ν' y := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hy
    rw [hν'apply, map_inv, inv_inv]
    exact hT z hz
  have hinf2 : ∀ x ∈ S.map (· * q⁻¹) + T.map (·⁻¹), ∀ k : ℕ, 0 < k → x ^ k ≠ 1 := by
    have hne2 : ∀ m : ℕ, 0 < m →
        ((T.map (·⁻¹)).map fun y : Kˣ => 1 - (y : K) ^ m).prod ≠ 0 := by
      intro m hm h0
      rw [Multiset.prod_eq_zero_iff] at h0
      obtain ⟨y, hy, hy0⟩ := Multiset.mem_map.mp h0
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hy
      apply hTinf z hz m hm
      have : ((z⁻¹ ^ m : Kˣ) : K) = 1 := by
        rw [Units.val_pow_eq_pow_val]; exact (sub_eq_zero.mp hy0).symm
      have e : z⁻¹ ^ m = 1 := Units.ext this
      rwa [inv_pow, inv_eq_one] at e
    intro x hx
    rcases Multiset.mem_add.mp hx with h | h
    · exact pow_ne_one_of_prod_ne_zero (fun m hm => hG2 m hm ▸ hne2 m hm) x h
    · exact pow_ne_one_of_prod_ne_zero hne2 x h
  have hSq : ∀ x ∈ S.map (· * q⁻¹), 1 ≤ ν' x := one_le_of_prodOneSub_eq hν' _ _ hTi
    (fun x hx _ => hinf2 x (Multiset.mem_add.mpr (Or.inl hx))) hP2
  have hlt := filter_eq_of_prodOneSub_eq hν' _ _ hSq hTi (fun x hx _ => hinf2 x hx) hP2
  ext z
  by_cases hz : 1 < ν z
  · have := congrArg (Multiset.count z) hgt
    rwa [Multiset.count_filter_of_pos (p := fun x => 1 < ν x) hz,
      Multiset.count_filter_of_pos (p := fun x => 1 < ν x) hz] at this
  · have hz' : ν z < ν q := lt_of_le_of_lt (not_lt.mp hz) hq
    have hzq : 1 < ν' (z * q⁻¹) := by
      rw [hν'apply, map_mul, map_inv, mul_inv, inv_inv]
      rw [← div_eq_inv_mul, one_lt_div (hν z)]
      exact hz'
    have h1 := congrArg (Multiset.count (z * q⁻¹)) hlt
    rw [Multiset.count_filter_of_pos (p := fun x => 1 < ν' x) hzq,
      Multiset.count_filter_of_pos (p := fun x => 1 < ν' x) hzq,
      Multiset.count_map_eq_count' _ _ (mul_left_injective q⁻¹),
      show z * q⁻¹ = (q * z⁻¹)⁻¹ by rw [mul_inv, inv_inv, mul_comm],
      Multiset.count_map_eq_count' _ _ inv_injective] at h1
    rw [h1]
    conv_lhs => rw [← hsym]
    exact Multiset.count_map_eq_count' (fun y => q * y⁻¹) T
      (fun a b hab => by simpa using hab) z

end Field

end Stacks.PowerProduct
