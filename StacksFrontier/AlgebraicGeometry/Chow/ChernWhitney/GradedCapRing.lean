module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.GradedConvolution
public import Mathlib.RingTheory.Binomial
public import Mathlib.Algebra.Group.Commute.Units

/-!
# The ring of graded cap families

Let `G : ℤ → Type*` be a family of abelian groups, for instance the Chow groups `A_k(X)` of a
scheme. A *graded cap family* `a` on `G` (`Stacks.Chow.GradedCapFamily`) assigns to every degree
`k` and every index `i` an additive map `a_k^i : G k ⟶ G (k - i)`; the Chern class cap products
`c_i(ℰ) ∩ -` of a finite locally free module form one. Graded cap families are added pointwise
and multiplied by the convolution

  `(a * b)_k^m = ∑_{i + j = m} a_{k-j}^{i} ∘ b_k^{j}`

of `StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.GradedConvolution`, the coefficientwise
product of the formal series `∑_i a^i` and `∑_j b^j`. This file shows that this is a ring, whose
unit is the identity in index `0` and zero in every positive index, and develops the algebra of
that ring which the Chern classes need:

* an element whose index-`0` component is the identity is a unit — the total Chern class
  `c(ℰ) = 1 + c₁(ℰ) + ⋯` is invertible;
* for `x` homogeneous of index `1` and every `r ∈ ℤ`, the **twist**
  `T_{r,x}(c)`, whose index-`m` component is `∑_{j ≤ m} binom(r - m + j, j) c_{m-j} x^j`,
  satisfies `T_{r+s,x}(c d) = T_{r,x}(c) T_{s,x}(d)` whenever `x` commutes with `d`, and
  `T_{0,x}(1) = 1`. For `ℰ` of rank `r` and `x = c₁(ℒ)` this is the shape of the formula
  `c(ℰ ⊗ ℒ) = T_{r,x}(c(ℰ))` of [Stacks, Tag 02UD], and the two identities are what turn it
  into the formula for a perfect complex in [Stacks, Tag 0FAF].

## Homogeneous components

An element `a` is *homogeneous of index `i`* if `a_k^j = 0` for every `j ≠ i`; its homogeneous
component `homComponent i a` keeps only the index `i`. Every element is the "sum" of its
homogeneous components, the sum being finite in each index: `Stacks.Chow.gradedSeries f` is the
element whose index-`i` component is that of `f i`, and `Stacks.Chow.mul_gradedSeries` multiplies
two such series of homogeneous elements coefficientwise. The proof that the twist is
multiplicative follows the one of `Stacks.Chow.twistSeries_mul` for power series: it is checked
on homogeneous elements, where `T_{r,x}(u) = u (1 + x)^{r - a}` for `u` of index `a`, then on
finite sums by additivity, and in general because the index-`m` component of every quantity
involved only depends on the components of index at most `m`.

## Main definitions

* `Stacks.Chow.instRingGradedCapFamily` — the ring structure.
* `Stacks.Chow.GradedCapFamily.IsHomogeneous`, `Stacks.Chow.homComponent`,
  `Stacks.Chow.gradedSeries` — homogeneous elements, components and series.
* `Stacks.Chow.binomialFamily` — the binomial series `(1 + x)^n`, `n ∈ ℤ`, of an element of
  index `1`.
* `Stacks.Chow.gradedTwist` — the twist `T_{r,x}`.

## Main results

* `Stacks.Chow.isUnit_of_apply_zero` — an element with identity index-`0` component is a unit.
* `Stacks.Chow.gradedTwist_mul` — `T_{r+s,x}(c d) = T_{r,x}(c) T_{s,x}(d)` when `x` commutes
  with `d`.
* `Stacks.Chow.gradedTwist_zero_one` — `T_{0,x}(1) = 1`.
* `Stacks.Chow.gradedTwist_inv_mul`, `Stacks.Chow.gradedTwist_mul_inv` — the twist of an
  inverse at the opposite rank is the inverse of the twist.

## References

* [Stacks Project, Tag 02UD](https://stacks.math.columbia.edu/tag/02UD)
* [Stacks Project, Tag 0FAF](https://stacks.math.columbia.edu/tag/0FAF)
* [Stacks Project, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI)
-/

@[expose] public noncomputable section

open Finset

namespace Stacks.Chow

universe v

variable {G : ℤ → Type v} [∀ k, AddCommGroup (G k)]

/-! ### Transports -/

/-- A transported element is heterogeneously equal to the original. -/
theorem gradedDegreeCast_heq {k l : ℤ} (h : k = l) (x : G k) : gradedDegreeCast G h x ≍ x := by
  subst h; rfl

/-- A transport of the argument of `Stacks.Chow.capTo` is absorbed into its degree condition. -/
theorem capTo_gradedDegreeCast (a : GradedCapFamily G) {k k' n : ℤ} (i : ℕ) (e : k = k')
    (h : k' - (i : ℤ) = n) (x : G k) :
    capTo a i h (gradedDegreeCast G e x) = capTo a i (by rw [e]; exact h) x := by
  subst e; rfl

/-- A family applied to zero gives zero. -/
theorem capTo_zero (a : GradedCapFamily G) {k n : ℤ} (i : ℕ) (h : k - (i : ℤ) = n) :
    capTo a i h (0 : G k) = 0 := by
  simp [capTo_def]

/-- `Stacks.Chow.capTo` is additive in the element. -/
theorem capTo_add (a : GradedCapFamily G) {k n : ℤ} (i : ℕ) (h : k - (i : ℤ) = n) (x y : G k) :
    capTo a i h (x + y) = capTo a i h x + capTo a i h y := by
  simp [capTo_def]

/-- `Stacks.Chow.capTo` of the zero family. -/
theorem capTo_of_eq_zero (a : GradedCapFamily G) {k n : ℤ} {i : ℕ} (h : k - (i : ℤ) = n)
    (ha : a k i = 0) (x : G k) : capTo a i h x = 0 := by
  simp [capTo_def, ha]

/-! ### The unit and the ring axioms -/

/-- The unit graded cap family: the identity in index `0`, zero in every positive index. -/
def gradedCapOne : GradedCapFamily G := fun k i =>
  if h : i = 0 then (gradedDegreeCast G (show k = k - (i : ℤ) by simp [h])).toAddMonoidHom
  else 0

/-- The index-`0` component of the unit is the identity, read in degree `k - 0`. -/
theorem gradedCapOne_apply_zero (k : ℤ) (x : G k) :
    gradedCapOne k 0 x = gradedDegreeCast G (by simp) x := by
  rw [gradedCapOne, dite_eq_left rfl]; rfl

/-- The positive-index components of the unit vanish. -/
theorem gradedCapOne_of_ne {i : ℕ} (hi : i ≠ 0) (k : ℤ) :
    (gradedCapOne : GradedCapFamily G) k i = 0 :=
  dite_eq_right hi

/-- The unit is a right unit for the convolution. -/
theorem convolve_gradedCapOne (a : GradedCapFamily G) : convolve a gradedCapOne = a := by
  funext k m
  refine AddMonoidHom.ext fun x => ?_
  rw [convolve_apply, Finset.sum_eq_single 0]
  · rw [convolveTerm_of_le _ _ _ (Nat.zero_le m), gradedCapOne_apply_zero, capTo_gradedDegreeCast,
      capTo_congr_index a (Nat.sub_zero m)]
    rfl
  · intro j _ hj
    by_cases hjm : j ≤ m
    · rw [convolveTerm_of_le _ _ _ hjm, capTo_def, gradedCapOne_of_ne hj]
      simp
    · exact convolveTerm_of_gt _ _ _ hjm x
  · intro h
    simp at h

/-- The unit is a left unit for the convolution. -/
theorem gradedCapOne_convolve (a : GradedCapFamily G) : convolve gradedCapOne a = a := by
  funext k m
  refine AddMonoidHom.ext fun x => ?_
  rw [convolve_apply, Finset.sum_eq_single m]
  · rw [convolveTerm_of_le _ _ _ le_rfl, capTo_congr_index gradedCapOne (Nat.sub_self m),
      capTo_def, gradedCapOne_apply_zero, gradedDegreeCast_gradedDegreeCast]
    rfl
  · intro j hj hjm
    have hj' : j ≤ m := mem_range_succ_iff.mp hj
    rw [convolveTerm_of_le _ _ _ hj', capTo_def, gradedCapOne_of_ne (by omega)]
    simp
  · intro h
    simp at h

/-- The summands of the convolution are additive in the left factor. -/
theorem convolveTerm_add_left (a a' b : GradedCapFamily G) (k : ℤ) (m j : ℕ) (x : G k) :
    convolveTerm (a + a') b k m j x = convolveTerm a b k m j x + convolveTerm a' b k m j x := by
  by_cases hj : j ≤ m
  · simp only [convolveTerm_of_le _ _ _ hj, capTo_def, Pi.add_apply, AddMonoidHom.add_apply,
      map_add]
  · simp [convolveTerm_of_gt _ _ _ hj]

/-- The summands of the convolution are additive in the right factor. -/
theorem convolveTerm_add_right (a b b' : GradedCapFamily G) (k : ℤ) (m j : ℕ) (x : G k) :
    convolveTerm a (b + b') k m j x = convolveTerm a b k m j x + convolveTerm a b' k m j x := by
  by_cases hj : j ≤ m
  · simp only [convolveTerm_of_le _ _ _ hj, capTo_def, Pi.add_apply, AddMonoidHom.add_apply,
      map_add]
  · simp [convolveTerm_of_gt _ _ _ hj]

/-- The summands of the convolution vanish when the left factor does. -/
theorem convolveTerm_zero_left (b : GradedCapFamily G) (k : ℤ) (m j : ℕ) (x : G k) :
    convolveTerm 0 b k m j x = 0 := by
  by_cases hj : j ≤ m
  · simp [convolveTerm_of_le _ _ _ hj, capTo_def]
  · simp [convolveTerm_of_gt _ _ _ hj]

/-- The summands of the convolution vanish when the right factor does. -/
theorem convolveTerm_zero_right (a : GradedCapFamily G) (k : ℤ) (m j : ℕ) (x : G k) :
    convolveTerm a 0 k m j x = 0 := by
  by_cases hj : j ≤ m
  · simp [convolveTerm_of_le _ _ _ hj, capTo_def]
  · simp [convolveTerm_of_gt _ _ _ hj]

/-- **Graded cap families form a ring**: pointwise addition, the convolution
`(a * b)_k^m = ∑_{i + j = m} a_{k-j}^{i} ∘ b_k^{j}` as multiplication, and the identity in index
`0` as unit. Associativity is `Stacks.Chow.convolve_assoc`. -/
instance instRingGradedCapFamily : Ring (GradedCapFamily G) where
  __ := (inferInstance : AddCommGroup (GradedCapFamily G))
  mul := convolve
  one := gradedCapOne
  mul_assoc a b c := (convolve_assoc a b c).symm
  one_mul := gradedCapOne_convolve
  mul_one := convolve_gradedCapOne
  zero_mul b := by
    funext k m
    refine AddMonoidHom.ext fun x => ?_
    change convolve 0 b k m x = 0
    simp [convolve_apply, convolveTerm_zero_left]
  mul_zero a := by
    funext k m
    refine AddMonoidHom.ext fun x => ?_
    change convolve a 0 k m x = 0
    simp [convolve_apply, convolveTerm_zero_right]
  left_distrib a b c := by
    funext k m
    refine AddMonoidHom.ext fun x => ?_
    change convolve a (b + c) k m x = (convolve a b + convolve a c) k m x
    simp [convolve_apply, convolveTerm_add_right, Finset.sum_add_distrib]
  right_distrib a b c := by
    funext k m
    refine AddMonoidHom.ext fun x => ?_
    change convolve (a + b) c k m x = (convolve a c + convolve b c) k m x
    simp [convolve_apply, convolveTerm_add_left, Finset.sum_add_distrib]

/-- The multiplication of graded cap families is the convolution. -/
theorem gradedCap_mul_def (a b : GradedCapFamily G) : a * b = convolve a b :=
  rfl

/-- The unit of the ring of graded cap families. -/
theorem gradedCap_one_def : (1 : GradedCapFamily G) = gradedCapOne :=
  rfl

/-- The components of a product, as the sum of the summands of the convolution. -/
theorem gradedCap_mul_apply (a b : GradedCapFamily G) (k : ℤ) (m : ℕ) (x : G k) :
    (a * b) k m x = ∑ j ∈ range (m + 1), convolveTerm a b k m j x :=
  convolve_apply a b k m x

/-- Products have equal index-`m` components if their convolution summands agree. -/
private theorem gradedCap_mul_apply_congr_of_convolveTerm {a b a' b' : GradedCapFamily G} {k : ℤ}
    {m : ℕ} (h : ∀ j ≤ m, ∀ x, convolveTerm a b k m j x = convolveTerm a' b' k m j x) :
    (a * b) k m = (a' * b') k m :=
  AddMonoidHom.ext fun x => by
    rw [gradedCap_mul_apply, gradedCap_mul_apply]
    exact Finset.sum_congr rfl fun j hj => h j (mem_range_succ_iff.mp hj) x

/-- The index-`0` component of `1` is the identity, read in degree `k - 0`. -/
theorem gradedCap_one_apply_zero (k : ℤ) (x : G k) :
    (1 : GradedCapFamily G) k 0 x = gradedDegreeCast G (by simp) x :=
  gradedCapOne_apply_zero k x

/-- The positive-index components of `1` vanish. -/
theorem gradedCap_one_of_ne {i : ℕ} (hi : i ≠ 0) (k : ℤ) :
    (1 : GradedCapFamily G) k i = 0 :=
  gradedCapOne_of_ne hi k

/-- The components of a finite sum of graded cap families. -/
theorem gradedCap_sum_apply {ι : Type*} (s : Finset ι) (f : ι → GradedCapFamily G) (k : ℤ)
    (m : ℕ) (x : G k) : (∑ t ∈ s, f t) k m x = ∑ t ∈ s, f t k m x := by
  rw [Finset.sum_apply, Finset.sum_apply, AddMonoidHom.finsetSum_apply]

/-- The index-`m` component of a product only depends on the components of index at most `m` of
the two factors. -/
theorem gradedCap_mul_apply_congr {a a' b b' : GradedCapFamily G} {m : ℕ}
    (ha : ∀ l ≤ m, ∀ k, a k l = a' k l) (hb : ∀ l ≤ m, ∀ k, b k l = b' k l) (k : ℤ) :
    (a * b) k m = (a' * b') k m := by
  refine gradedCap_mul_apply_congr_of_convolveTerm fun j hjm x => ?_
  rw [convolveTerm_of_le _ _ _ hjm, convolveTerm_of_le _ _ _ hjm, capTo_def, capTo_def,
    ha (m - j) (Nat.sub_le m j) (k - (j : ℤ)), hb j hjm k]

/-! ### Formal inversion -/

/-- The components of the right inverse of `a`, by recursion on the index:
`c^m = 1^m - ∑_{j < m} a^{m-j} ∘ c^j`. -/
def gradedRightInvAux (a : GradedCapFamily G) (k : ℤ) (m : ℕ) : G k →+ G (k - (m : ℤ)) :=
  (1 : GradedCapFamily G) k m -
    ∑ j : Fin m, (gradedDegreeCast G
        (show k - ((j : ℕ) : ℤ) - ((m - (j : ℕ) : ℕ) : ℤ) = k - (m : ℤ) by
          have := j.isLt; omega)).toAddMonoidHom.comp
      ((a (k - ((j : ℕ) : ℤ)) (m - j)).comp (gradedRightInvAux a k j))
termination_by m
decreasing_by exact j.isLt

/-- The right inverse of a graded cap family whose index-`0` component is the identity. -/
def gradedRightInv (a : GradedCapFamily G) : GradedCapFamily G :=
  gradedRightInvAux a

/-- The defining recursion of `Stacks.Chow.gradedRightInv`. -/
theorem gradedRightInv_apply (a : GradedCapFamily G) (k : ℤ) (m : ℕ) :
    gradedRightInv a k m = (1 : GradedCapFamily G) k m -
      ∑ j : Fin m, (gradedDegreeCast G
          (show k - ((j : ℕ) : ℤ) - ((m - (j : ℕ) : ℕ) : ℤ) = k - (m : ℤ) by
            have := j.isLt; omega)).toAddMonoidHom.comp
        ((a (k - ((j : ℕ) : ℤ)) (m - j)).comp (gradedRightInv a k j)) := by
  rw [gradedRightInv, gradedRightInvAux]

/-- The index-`0` component of the right inverse is the identity. -/
theorem gradedRightInv_zero (a : GradedCapFamily G) (k : ℤ) :
    gradedRightInv a k 0 = (1 : GradedCapFamily G) k 0 := by
  rw [gradedRightInv_apply]
  simp

/-- If the index-`0` component of `a` is the identity, `Stacks.Chow.gradedRightInv a` is a right
inverse of `a`. -/
theorem mul_gradedRightInv {a : GradedCapFamily G}
    (ha : ∀ k, a k 0 = (1 : GradedCapFamily G) k 0) : a * gradedRightInv a = 1 := by
  funext k m
  refine AddMonoidHom.ext fun x => ?_
  rw [gradedCap_mul_apply, Finset.sum_range_succ, convolveTerm_of_le _ _ _ le_rfl,
    capTo_congr_index a (Nat.sub_self m), capTo_def, ha, gradedCap_one_apply_zero,
    gradedDegreeCast_gradedDegreeCast]
  change _ + gradedRightInv a k m x = _
  rw [gradedRightInv_apply, AddMonoidHom.sub_apply, AddMonoidHom.finsetSum_apply,
    ← Fin.sum_univ_eq_sum_range (fun j => convolveTerm a (gradedRightInv a) k m j x) m]
  have hsum : ∑ j : Fin m, convolveTerm a (gradedRightInv a) k m j x =
      ∑ j : Fin m, ((gradedDegreeCast G
          (show k - ((j : ℕ) : ℤ) - ((m - (j : ℕ) : ℕ) : ℤ) = k - (m : ℤ) by
            have := j.isLt; omega)).toAddMonoidHom.comp
        ((a (k - ((j : ℕ) : ℤ)) (m - j)).comp (gradedRightInv a k j))) x := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [convolveTerm_of_le _ _ _ j.isLt.le]
    rfl
  rw [hsum, add_sub_cancel]

/-- **An element whose index-`0` component is the identity is a unit.** The right inverse is
constructed by recursion on the index; it again has identity index-`0` component, hence has a
right inverse itself, which must then be `a`. -/
theorem isUnit_of_apply_zero {a : GradedCapFamily G}
    (ha : ∀ k, a k 0 = (1 : GradedCapFamily G) k 0) : IsUnit a := by
  have h1 := mul_gradedRightInv ha
  have h2 := mul_gradedRightInv (gradedRightInv_zero a)
  have he : gradedRightInv (gradedRightInv a) = a := by
    calc gradedRightInv (gradedRightInv a)
        = (a * gradedRightInv a) * gradedRightInv (gradedRightInv a) := by rw [h1, one_mul]
      _ = a := by rw [mul_assoc, h2, mul_one]
  rw [he] at h2
  exact ⟨⟨a, gradedRightInv a, h1, h2⟩, rfl⟩

/-! ### Homogeneous elements and series -/

/-- That a graded cap family is *homogeneous of index `i`*: its components of every index other
than `i` vanish. The cap product with the `i`-th Chern class of a module is homogeneous of
index `i`. -/
def GradedCapFamily.IsHomogeneous (i : ℕ) (a : GradedCapFamily G) : Prop :=
  ∀ (k : ℤ) (j : ℕ), j ≠ i → a k j = 0

/-- The homogeneous component of index `i`: the components of index `i` are kept, the others
replaced by zero. -/
def homComponent (i : ℕ) : GradedCapFamily G →+ GradedCapFamily G where
  toFun a k j := if j = i then a k j else 0
  map_zero' := by
    funext k j
    split_ifs <;> rfl
  map_add' a b := by
    funext k j
    by_cases h : j = i <;> simp [h]

/-- The components of a homogeneous component. -/
theorem homComponent_apply (i : ℕ) (a : GradedCapFamily G) (k : ℤ) (j : ℕ) :
    homComponent i a k j = if j = i then a k j else 0 :=
  rfl

/-- A homogeneous component keeps the components of its own index. -/
@[simp]
theorem homComponent_apply_self (i : ℕ) (a : GradedCapFamily G) (k : ℤ) :
    homComponent i a k i = a k i :=
  ite_eq_left rfl

/-- A homogeneous component vanishes away from its index. -/
theorem homComponent_apply_of_ne {i j : ℕ} (h : j ≠ i) (a : GradedCapFamily G) (k : ℤ) :
    homComponent i a k j = 0 :=
  ite_eq_right h

/-- The homogeneous component of index `i` is homogeneous of index `i`. -/
theorem isHomogeneous_homComponent (i : ℕ) (a : GradedCapFamily G) :
    (homComponent i a).IsHomogeneous i :=
  fun k _ hj => homComponent_apply_of_ne hj a k

/-- The homogeneous component of index `i` only depends on the components of index `i`. -/
theorem homComponent_congr {i : ℕ} {a a' : GradedCapFamily G} (h : ∀ k, a k i = a' k i) :
    homComponent i a = homComponent i a' := by
  funext k j
  by_cases hj : j = i
  · subst hj; simp [h k]
  · rw [homComponent_apply_of_ne hj, homComponent_apply_of_ne hj]

namespace GradedCapFamily.IsHomogeneous

variable {a b : GradedCapFamily G} {i : ℕ}

/-- A homogeneous element is its own homogeneous component. -/
theorem homComponent_self (ha : a.IsHomogeneous i) : homComponent i a = a := by
  funext k j
  by_cases hj : j = i
  · subst hj; simp
  · rw [homComponent_apply_of_ne hj, ha k j hj]

/-- The other homogeneous components of a homogeneous element vanish. -/
theorem homComponent_of_ne (ha : a.IsHomogeneous i) {j : ℕ} (hj : j ≠ i) :
    homComponent j a = 0 := by
  funext k l
  by_cases hl : l = j
  · subst hl; rw [homComponent_apply_self, ha k l hj]; rfl
  · rw [homComponent_apply_of_ne hl]; rfl

/-- `0` is homogeneous of every index. -/
theorem zero : (0 : GradedCapFamily G).IsHomogeneous i :=
  fun _ _ _ => rfl

/-- A sum of homogeneous elements of index `i` is homogeneous of index `i`. -/
theorem add (ha : a.IsHomogeneous i) (hb : b.IsHomogeneous i) : (a + b).IsHomogeneous i :=
  fun k j hj => by simp [ha k j hj, hb k j hj]

/-- An integer multiple of a homogeneous element is homogeneous of the same index. -/
theorem zsmul (ha : a.IsHomogeneous i) (n : ℤ) : (n • a).IsHomogeneous i :=
  fun k j hj => by simp [ha k j hj]

/-- A finite sum of homogeneous elements of index `i` is homogeneous of index `i`. -/
theorem sum {ι : Type*} {s : Finset ι} {f : ι → GradedCapFamily G}
    (hf : ∀ t ∈ s, (f t).IsHomogeneous i) : (∑ t ∈ s, f t).IsHomogeneous i := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert t s ht ih =>
    rw [Finset.sum_insert ht]
    exact add (hf t (mem_insert_self t s)) (ih fun t' h => hf t' (mem_insert_of_mem h))

/-- **The product of homogeneous elements is homogeneous**, of the sum of the indices. -/
theorem mul {p q : ℕ} (ha : a.IsHomogeneous p) (hb : b.IsHomogeneous q) :
    (a * b).IsHomogeneous (p + q) := by
  intro k m hm
  refine AddMonoidHom.ext fun x => ?_
  rw [gradedCap_mul_apply]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hjm : j ≤ m := mem_range_succ_iff.mp hj
  rw [convolveTerm_of_le _ _ _ hjm]
  by_cases hjq : j = q
  · subst hjq
    exact capTo_of_eq_zero a _ (ha _ _ (by omega)) _
  · rw [hb k j hjq]
    exact capTo_zero a _ _

/-- `1` is homogeneous of index `0`. -/
theorem one : (1 : GradedCapFamily G).IsHomogeneous 0 :=
  fun k _ hj => gradedCap_one_of_ne hj k

/-- The `n`-th power of an element of index `1` is homogeneous of index `n`. -/
theorem pow (ha : a.IsHomogeneous 1) (n : ℕ) : (a ^ n).IsHomogeneous n := by
  induction n with
  | zero => simpa using one
  | succ n ih => rw [pow_succ]; exact ih.mul ha

end GradedCapFamily.IsHomogeneous

/-- The *series* of a family `f` of graded cap families: the element whose index-`i` component
is the index-`i` component of `f i`. For `f i` homogeneous of index `i` this is the (infinite,
but finite in every index) sum `∑_i f i`. -/
def gradedSeries (f : ℕ → GradedCapFamily G) : GradedCapFamily G :=
  fun k i => f i k i

/-- The components of a series. -/
theorem gradedSeries_apply (f : ℕ → GradedCapFamily G) (k : ℤ) (i : ℕ) :
    gradedSeries f k i = f i k i :=
  rfl

/-- Every graded cap family is the series of its homogeneous components. -/
theorem gradedSeries_homComponent (a : GradedCapFamily G) :
    gradedSeries (fun i => homComponent i a) = a := by
  funext k i
  simp [gradedSeries_apply]

/-- The homogeneous components of a series of homogeneous elements are its terms. -/
theorem homComponent_gradedSeries {f : ℕ → GradedCapFamily G}
    (hf : ∀ i, (f i).IsHomogeneous i) (i : ℕ) : homComponent i (gradedSeries f) = f i := by
  rw [← (hf i).homComponent_self]
  exact homComponent_congr fun k => rfl

/-- The series of a sum of families is the sum of the series. -/
theorem gradedSeries_add (f g : ℕ → GradedCapFamily G) :
    gradedSeries (f + g) = gradedSeries f + gradedSeries g :=
  rfl

/-- **The product of two series of homogeneous elements** is computed coefficientwise:
`(∑_i f_i) (∑_j g_j) = ∑_m ∑_{j ≤ m} f_{m-j} g_j`. -/
theorem mul_gradedSeries {f g : ℕ → GradedCapFamily G} (hg : ∀ j, (g j).IsHomogeneous j) :
    gradedSeries f * gradedSeries g =
      gradedSeries fun m => ∑ j ∈ range (m + 1), f (m - j) * g j := by
  funext k m
  refine AddMonoidHom.ext fun x => ?_
  rw [gradedCap_mul_apply, gradedSeries_apply, gradedCap_sum_apply]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : j ≤ m := mem_range_succ_iff.mp hj
  rw [convolveTerm_of_le _ _ _ hjm, gradedCap_mul_apply, Finset.sum_eq_single j,
    convolveTerm_of_le _ _ _ hjm]
  · rfl
  · intro l hl hlj
    have hlm : l ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hl)
    rw [convolveTerm_of_le _ _ _ hlm, hg j k l hlj]
    exact capTo_zero _ _ _
  · intro h
    exact absurd (mem_range.mpr (Nat.lt_succ_of_le hjm)) h

/-- Multiplying by a homogeneous element on the left shifts the homogeneous components. -/
theorem homComponent_mul_of_isHomogeneous_left {u : GradedCapFamily G} {p : ℕ}
    (hu : u.IsHomogeneous p) (v : GradedCapFamily G) (i : ℕ) :
    homComponent (p + i) (u * v) = u * homComponent i v := by
  funext k m
  by_cases hm : m = p + i
  · subst hm
    rw [homComponent_apply_self]
    refine gradedCap_mul_apply_congr_of_convolveTerm fun j hjm x => ?_
    rw [convolveTerm_of_le _ _ _ hjm, convolveTerm_of_le _ _ _ hjm]
    by_cases hji : j = i
    · subst hji; rw [homComponent_apply_self]
    · rw [capTo_of_eq_zero u _ (hu _ _ (by omega)), capTo_of_eq_zero u _ (hu _ _ (by omega))]
  · rw [homComponent_apply_of_ne hm, (hu.mul (isHomogeneous_homComponent i v)) k m hm]

/-- Multiplying by a homogeneous element on the right shifts the homogeneous components. -/
theorem homComponent_mul_of_isHomogeneous_right (u : GradedCapFamily G) {v : GradedCapFamily G}
    {q : ℕ} (hv : v.IsHomogeneous q) (i : ℕ) :
    homComponent (i + q) (u * v) = homComponent i u * v := by
  funext k m
  by_cases hm : m = i + q
  · subst hm
    rw [homComponent_apply_self]
    refine gradedCap_mul_apply_congr_of_convolveTerm fun j hjm x => ?_
    rw [convolveTerm_of_le _ _ _ hjm, convolveTerm_of_le _ _ _ hjm]
    by_cases hjq : j = q
    · subst hjq
      rw [capTo_congr_index u (show i + j - j = i by omega),
        capTo_congr_index (homComponent i u) (show i + j - j = i by omega), capTo_def, capTo_def,
        homComponent_apply_self]
    · rw [hv k j hjq, AddMonoidHom.zero_apply, capTo_zero, capTo_zero]
  · rw [homComponent_apply_of_ne hm, ((isHomogeneous_homComponent i u).mul hv) k m hm]

/-- An element commuting with an element `x` of index `1` commutes with `x` componentwise. -/
theorem commute_homComponent {x v : GradedCapFamily G} (hx : x.IsHomogeneous 1)
    (h : Commute x v) (i : ℕ) : Commute x (homComponent i v) := by
  have h1 := homComponent_mul_of_isHomogeneous_left hx v i
  have h2 := homComponent_mul_of_isHomogeneous_right v hx i
  rw [h.eq, add_comm] at h1
  exact h1.symm.trans h2

/-- A series of homogeneous elements commutes with every element whose homogeneous components
commute with the terms of the series. -/
theorem commute_gradedSeries {f : ℕ → GradedCapFamily G} (hf : ∀ i, (f i).IsHomogeneous i)
    {v : GradedCapFamily G} (h : ∀ i j, Commute (homComponent i v) (f j)) :
    Commute (gradedSeries f) v := by
  change gradedSeries f * v = v * gradedSeries f
  conv_lhs => rw [← gradedSeries_homComponent v]
  conv_rhs => rw [← gradedSeries_homComponent v]
  rw [mul_gradedSeries (fun i => isHomogeneous_homComponent i v),
    mul_gradedSeries hf]
  congr 1
  funext m
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : j ≤ m := mem_range_succ_iff.mp hj
  rw [show m - (m + 1 - 1 - j) = j by omega, show m + 1 - 1 - j = m - j by omega]
  exact (h (m - j) j).symm.eq

/-! ### The binomial series and the twist -/

/-- The binomial series `(1 + x)^n = ∑_j binom(n, j) x^j` of an element `x`, for `n ∈ ℤ`. For
`x` of index `1` the `j`-th term is homogeneous of index `j`. -/
def binomialFamily (n : ℤ) (x : GradedCapFamily G) : GradedCapFamily G :=
  gradedSeries fun j => Ring.choose n j • x ^ j

variable {x : GradedCapFamily G}

/-- The `j`-th term `binom(n, j) x^j` of the binomial series is homogeneous of index `j`. -/
theorem isHomogeneous_binomialTerm (hx : x.IsHomogeneous 1) (n : ℤ) (j : ℕ) :
    (Ring.choose n j • x ^ j).IsHomogeneous j :=
  (hx.pow j).zsmul _

/-- `(1 + x)^0 = 1`. -/
theorem binomialFamily_zero (x : GradedCapFamily G) : binomialFamily 0 x = 1 := by
  funext k m
  rw [binomialFamily, gradedSeries_apply]
  rcases m with _ | m
  · simp
  · rw [Ring.choose_zero_succ, zero_smul, gradedCap_one_of_ne (Nat.succ_ne_zero m)]
    rfl

/-- `(1 + x)^{n + n'} = (1 + x)^n (1 + x)^{n'}`, by the Chu–Vandermonde identity. -/
theorem binomialFamily_add (hx : x.IsHomogeneous 1) (n n' : ℤ) :
    binomialFamily (n + n') x = binomialFamily n x * binomialFamily n' x := by
  rw [binomialFamily, binomialFamily, binomialFamily,
    mul_gradedSeries (isHomogeneous_binomialTerm hx n')]
  congr 1
  funext m
  have hterm : ∀ j ∈ range (m + 1), (Ring.choose n (m - j) • x ^ (m - j)) *
      (Ring.choose n' j • x ^ j) = (Ring.choose n (m - j) * Ring.choose n' j) • x ^ m := by
    intro j hj
    have hjm : j ≤ m := mem_range_succ_iff.mp hj
    rw [smul_mul_smul_comm, ← pow_add, Nat.sub_add_cancel hjm]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_smul, add_comm n n',
    Ring.add_choose_eq m (Commute.all n' n),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b : ℕ => (Ring.choose n' a * Ring.choose n b : ℤ))]
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- The binomial series of `x` commutes with everything `x` commutes with. -/
theorem commute_binomialFamily (hx : x.IsHomogeneous 1) {v : GradedCapFamily G}
    (h : Commute x v) (n : ℤ) : Commute (binomialFamily n x) v :=
  commute_gradedSeries (isHomogeneous_binomialTerm hx n) fun i j =>
    (((commute_homComponent hx h i).pow_left j).symm.smul_right _)

/-- The twist `T_{r,x}(c)` of a graded cap family `c` by an element `x`: its index-`m`
component is that of

  `∑_{j ≤ m} binom(r - m + j, j) c_{m-j} x^j`,

`c_i` the homogeneous component of `c` of index `i`. For a finite locally free module `ℰ` of
rank `r`, an invertible module `ℒ` and `x = c₁(ℒ)`, Stacks 02UD says that the total Chern class
of `ℰ ⊗ ℒ` is the twist of that of `ℰ`. -/
def gradedTwist (r : ℤ) (x : GradedCapFamily G) : GradedCapFamily G →+ GradedCapFamily G :=
  AddMonoidHom.mk' (fun c => gradedSeries fun m => ∑ j ∈ range (m + 1),
      Ring.choose (r - m + j) j • (homComponent (m - j) c * x ^ j))
    (fun c c' => by
      rw [← gradedSeries_add]
      congr 1
      funext m
      simp only [Pi.add_apply, map_add, add_mul, smul_add, Finset.sum_add_distrib])

/-- The defining formula of the twist. -/
theorem gradedTwist_apply (r : ℤ) (x c : GradedCapFamily G) :
    gradedTwist r x c = gradedSeries fun m => ∑ j ∈ range (m + 1),
      Ring.choose (r - m + j) j • (homComponent (m - j) c * x ^ j) :=
  rfl

/-- The index-`m` component of a twist only depends on the components of index at most `m`. -/
theorem gradedTwist_apply_congr (r : ℤ) (x : GradedCapFamily G) {c c' : GradedCapFamily G}
    {m : ℕ} (h : ∀ l ≤ m, ∀ k, c k l = c' k l) (k : ℤ) :
    gradedTwist r x c k m = gradedTwist r x c' k m := by
  have hsum : (∑ j ∈ range (m + 1), Ring.choose (r - m + j) j • (homComponent (m - j) c * x ^ j)) =
      ∑ j ∈ range (m + 1), Ring.choose (r - m + j) j • (homComponent (m - j) c' * x ^ j) :=
    Finset.sum_congr rfl fun j _ => by
      rw [homComponent_congr fun k => h (m - j) (Nat.sub_le m j) k]
  rw [gradedTwist_apply, gradedTwist_apply, gradedSeries_apply, gradedSeries_apply, hsum]

/-- **The twist of a homogeneous element** `u` of index `a` is `u (1 + x)^{r - a}`. -/
theorem gradedTwist_of_isHomogeneous (hx : x.IsHomogeneous 1) (r : ℤ) {u : GradedCapFamily G}
    {a : ℕ} (hu : u.IsHomogeneous a) : gradedTwist r x u = u * binomialFamily (r - a) x := by
  conv_rhs => rw [← gradedSeries_homComponent u]
  rw [gradedTwist_apply, binomialFamily,
    mul_gradedSeries (isHomogeneous_binomialTerm hx _)]
  congr 1
  funext m
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : j ≤ m := mem_range_succ_iff.mp hj
  rw [mul_smul_comm]
  by_cases ha : m - j = a
  · rw [show r - (m : ℤ) + (j : ℤ) = r - (a : ℤ) by omega]
  · rw [hu.homComponent_of_ne ha, zero_mul, smul_zero, smul_zero]

/-- The twist of a product of two homogeneous elements, the second commuting with `x`. -/
theorem gradedTwist_mul_of_isHomogeneous (hx : x.IsHomogeneous 1) (r s : ℤ)
    {u v : GradedCapFamily G} {a b : ℕ} (hu : u.IsHomogeneous a) (hv : v.IsHomogeneous b)
    (hxv : Commute x v) :
    gradedTwist (r + s) x (u * v) = gradedTwist r x u * gradedTwist s x v := by
  rw [gradedTwist_of_isHomogeneous hx _ (hu.mul hv), gradedTwist_of_isHomogeneous hx _ hu,
    gradedTwist_of_isHomogeneous hx _ hv,
    show r + s - ((a + b : ℕ) : ℤ) = (r - a) + (s - b) by push_cast; ring,
    binomialFamily_add hx]
  simp only [mul_assoc]
  congr 1
  rw [← mul_assoc, ← mul_assoc, (commute_binomialFamily hx hxv (r - a)).eq]

/-- The truncation of `c` below the index `N`: the sum of its homogeneous components of index
less than `N`. -/
def gradedTrunc (N : ℕ) (c : GradedCapFamily G) : GradedCapFamily G :=
  ∑ i ∈ range N, homComponent i c

/-- Below the index `N` the truncation has the components of `c`. -/
theorem gradedTrunc_apply_of_lt {N l : ℕ} (h : l < N) (c : GradedCapFamily G) (k : ℤ) :
    gradedTrunc N c k l = c k l := by
  refine AddMonoidHom.ext fun x => ?_
  rw [gradedTrunc, gradedCap_sum_apply, Finset.sum_eq_single l]
  · rw [homComponent_apply_self]
  · intro i _ hil
    rw [homComponent_apply_of_ne (Ne.symm hil)]
    rfl
  · intro hl
    exact absurd (mem_range.mpr h) hl

/-- **The twist is multiplicative in the family and additive in the rank:**
`T_{r+s,x}(c d) = T_{r,x}(c) T_{s,x}(d)`, for `x` of index `1` commuting with `d`. -/
theorem gradedTwist_mul (hx : x.IsHomogeneous 1) (r s : ℤ) (c : GradedCapFamily G)
    {d : GradedCapFamily G} (hxd : Commute x d) :
    gradedTwist (r + s) x (c * d) = gradedTwist r x c * gradedTwist s x d := by
  funext k m
  have hc : ∀ l ≤ m, ∀ k, c k l = gradedTrunc (m + 1) c k l := fun l hl k =>
    (gradedTrunc_apply_of_lt (Nat.lt_succ_of_le hl) c k).symm
  have hd : ∀ l ≤ m, ∀ k, d k l = gradedTrunc (m + 1) d k l := fun l hl k =>
    (gradedTrunc_apply_of_lt (Nat.lt_succ_of_le hl) d k).symm
  have hfin : gradedTwist (r + s) x (gradedTrunc (m + 1) c * gradedTrunc (m + 1) d) =
      gradedTwist r x (gradedTrunc (m + 1) c) * gradedTwist s x (gradedTrunc (m + 1) d) := by
    simp only [gradedTrunc, Finset.sum_mul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    exact gradedTwist_mul_of_isHomogeneous hx r s (isHomogeneous_homComponent i c)
      (isHomogeneous_homComponent j d) (commute_homComponent hx hxd j)
  calc gradedTwist (r + s) x (c * d) k m
      = gradedTwist (r + s) x (gradedTrunc (m + 1) c * gradedTrunc (m + 1) d) k m :=
        gradedTwist_apply_congr _ _ (fun l hl k => gradedCap_mul_apply_congr
          (fun l' hl' => hc l' (hl'.trans hl)) (fun l' hl' => hd l' (hl'.trans hl)) k) k
    _ = (gradedTwist r x (gradedTrunc (m + 1) c) *
          gradedTwist s x (gradedTrunc (m + 1) d)) k m := by rw [hfin]
    _ = (gradedTwist r x c * gradedTwist s x d) k m :=
        gradedCap_mul_apply_congr
          (fun l hl k => gradedTwist_apply_congr _ _
            (fun l' hl' k' => (hc l' (hl'.trans hl) k').symm) k)
          (fun l hl k => gradedTwist_apply_congr _ _
            (fun l' hl' k' => (hd l' (hl'.trans hl) k').symm) k)
          k

/-- `T_{0,x}(1) = 1`. -/
theorem gradedTwist_zero_one (hx : x.IsHomogeneous 1) : gradedTwist 0 x 1 = 1 := by
  rw [gradedTwist_of_isHomogeneous hx 0 GradedCapFamily.IsHomogeneous.one, Nat.cast_zero,
    sub_zero, binomialFamily_zero, one_mul]

/-- **The twist of an inverse:** `T_{-r,x}(c⁻¹) T_{r,x}(c) = 1` for a unit `c` commuting with
`x`. -/
theorem gradedTwist_inv_mul (hx : x.IsHomogeneous 1) (r : ℤ) (c : (GradedCapFamily G)ˣ)
    (hxc : Commute x c) : gradedTwist (-r) x ↑c⁻¹ * gradedTwist r x c = 1 := by
  rw [← gradedTwist_mul hx _ _ _ hxc, neg_add_cancel, Units.inv_mul, gradedTwist_zero_one hx]

/-- **The twist of an inverse:** `T_{r,x}(c) T_{-r,x}(c⁻¹) = 1` for a unit `c` commuting with
`x`. -/
theorem gradedTwist_mul_inv (hx : x.IsHomogeneous 1) (r : ℤ) (c : (GradedCapFamily G)ˣ)
    (hxc : Commute x c) : gradedTwist r x c * gradedTwist (-r) x ↑c⁻¹ = 1 := by
  rw [← gradedTwist_mul hx _ _ _ hxc.units_inv_right, add_neg_cancel, Units.mul_inv,
    gradedTwist_zero_one hx]

/-- The twist of a unit commuting with `x`, as a unit, with inverse the twist of the inverse at
the opposite rank. -/
def gradedTwistUnit (hx : x.IsHomogeneous 1) (r : ℤ) (c : (GradedCapFamily G)ˣ)
    (hxc : Commute x c) : (GradedCapFamily G)ˣ where
  val := gradedTwist r x c
  inv := gradedTwist (-r) x ↑c⁻¹
  val_inv := gradedTwist_mul_inv hx r c hxc
  inv_val := gradedTwist_inv_mul hx r c hxc

end Stacks.Chow

end
