module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKInvolution

/-!
# The shifted Milnor K-ring `K^M_*(k) ⊕ K^M_*(k) ξ`

Fix a field `k`. `MilnorKShift k` is the ring obtained from `MilnorKRing k` by adjoining a
degree-one element `ξ` subject to

* `ξ r = σ(r) ξ`, where `σ` is the grading involution `milnorKInvolution k`, and
* `ξ ^ 2 = {-1} ξ`.

Concretely an element is a pair `(a, b)`, thought of as `a + b ξ`, and

`(a + b ξ)(c + d ξ) = a c + (a d + b σ(c) + b d {-1}) ξ`.

The grading `milnorKShiftGrading k n` is `K^M_n(k) ⊕ K^M_{n-1}(k) ξ`.

## Main definitions

* `MilnorKShift` — the ring `K^M_*(k) ⊕ K^M_*(k) ξ`.
* `MilnorKShift.main`, `MilnorKShift.shift` — the two coefficients of `a + b ξ`.
* `milnorKShiftGrading` — the subgroup `K^M_n(k) ⊕ K^M_{n-1}(k) ξ`.

## Main results

* `MilnorKShift.instRing` — the ring structure, associativity included.
* `milnorKShiftGrading_mul` — the grading is multiplicative.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
-/

@[expose] public noncomputable section

universe u

variable {k : Type u} [Field k]

/-- The ring `K^M_*(k) ⊕ K^M_*(k) ξ`, where `ξ` has degree one, satisfies `ξ r = σ(r) ξ` for the
grading involution `σ`, and satisfies `ξ ^ 2 = {-1} ξ`. An element is a pair `(a, b)`, read as
`a + b ξ`. -/
def MilnorKShift (k : Type u) [Field k] : Type u := MilnorKRing k × MilnorKRing k

namespace MilnorKShift

/-- The componentwise additive group structure on `K^M_*(k) ⊕ K^M_*(k) ξ`. -/
instance instAddCommGroup : AddCommGroup (MilnorKShift k) :=
  Prod.instAddCommGroup

/-- `mk a b` is the element `a + b ξ`. -/
def mk (a b : MilnorKRing k) : MilnorKShift k := (a, b)

/-- The `ξ`-free coefficient of `a + b ξ`. -/
def main (x : MilnorKShift k) : MilnorKRing k := (x : MilnorKRing k × MilnorKRing k).1

/-- The coefficient of `ξ` in `a + b ξ`. -/
def shift (x : MilnorKShift k) : MilnorKRing k := (x : MilnorKRing k × MilnorKRing k).2

/-- The `ξ`-free coefficient of `a + b ξ` is `a`. -/
@[simp] theorem main_mk (a b : MilnorKRing k) : main (mk a b) = a := rfl
/-- The `ξ`-coefficient of `a + b ξ` is `b`. -/
@[simp] theorem shift_mk (a b : MilnorKRing k) : shift (mk a b) = b := rfl
/-- Every element is `main x + shift x ξ`. -/
@[simp] theorem mk_main_shift (x : MilnorKShift k) : mk (main x) (shift x) = x := rfl

/-- Two elements with the same two coefficients are equal. -/
theorem ext {x y : MilnorKShift k} (h₁ : main x = main y) (h₂ : shift x = shift y) : x = y :=
  Prod.ext h₁ h₂

/-- The `ξ`-free coefficient of `0` is `0`. -/
@[simp] theorem main_zero : main (0 : MilnorKShift k) = 0 := rfl
/-- The `ξ`-coefficient of `0` is `0`. -/
@[simp] theorem shift_zero : shift (0 : MilnorKShift k) = 0 := rfl
/-- The `ξ`-free coefficient is additive. -/
@[simp] theorem main_add (x y : MilnorKShift k) : main (x + y) = main x + main y := rfl
/-- The `ξ`-coefficient is additive. -/
@[simp] theorem shift_add (x y : MilnorKShift k) : shift (x + y) = shift x + shift y := rfl
/-- The `ξ`-free coefficient commutes with negation. -/
@[simp] theorem main_neg (x : MilnorKShift k) : main (-x) = -main x := rfl
/-- The `ξ`-coefficient commutes with negation. -/
@[simp] theorem shift_neg (x : MilnorKShift k) : shift (-x) = -shift x := rfl

/-- The product `(a + b ξ)(c + d ξ) = a c + (a d + b σ(c) + b d {-1}) ξ`. -/
instance instMul : Mul (MilnorKShift k) where
  mul x y := mk (main x * main y)
    (main x * shift y + shift x * milnorKInvolution k (main y) +
      shift x * shift y * milnorKNegOne k)

/-- The unit `1 + 0 ξ`. -/
instance instOne : One (MilnorKShift k) where
  one := mk 1 0

/-- The `ξ`-free coefficient of a product is the product of the `ξ`-free coefficients. -/
@[simp] theorem main_mul (x y : MilnorKShift k) : main (x * y) = main x * main y := rfl

/-- The `ξ`-coefficient of `(a + b ξ)(c + d ξ)` is `a d + b σ(c) + b d {-1}`. -/
@[simp]
theorem shift_mul (x y : MilnorKShift k) :
    shift (x * y) = main x * shift y + shift x * milnorKInvolution k (main y) +
      shift x * shift y * milnorKNegOne k := rfl

/-- The `ξ`-free coefficient of `1` is `1`. -/
@[simp] theorem main_one : main (1 : MilnorKShift k) = 1 := rfl
/-- The `ξ`-coefficient of `1` is `0`. -/
@[simp] theorem shift_one : shift (1 : MilnorKShift k) = 0 := rfl

/-- The `ξ`-coefficient of a triple product `(a + b ξ)(c + d ξ)(e + f ξ)` is the same for both
bracketings. -/
private theorem shift_assoc_aux (a b c d e f : MilnorKRing k) :
    a * c * f +
        (a * d + b * milnorKInvolution k c + b * d * milnorKNegOne k) *
          milnorKInvolution k e +
        (a * d + b * milnorKInvolution k c + b * d * milnorKNegOne k) * f *
          milnorKNegOne k =
      a * (c * f + d * milnorKInvolution k e + d * f * milnorKNegOne k) +
        b * milnorKInvolution k (c * e) +
        b * (c * f + d * milnorKInvolution k e + d * f * milnorKNegOne k) *
          milnorKNegOne k := by
  have hcentre : ∀ q : MilnorKRing k, milnorKNegOne k * q = q * milnorKNegOne k :=
    milnorKNegOne_mul_comm
  have hσ : ∀ x q : MilnorKRing k,
      milnorKInvolution k x * (q * milnorKNegOne k) = x * (q * milnorKNegOne k) := fun x q => by
    rw [← hcentre, milnorKInvolution_mul_milnorKNegOne_mul]
  simp only [map_mul, mul_add, add_mul, mul_assoc, hcentre, hσ]
  abel

/-- The ring structure on `K^M_*(k) ⊕ K^M_*(k) ξ`. -/
instance instRing : Ring (MilnorKShift k) where
  __ := instAddCommGroup
  mul_assoc x y z := ext (by simp only [main_mul, mul_assoc])
    (by simpa only [main_mul, shift_mul] using
      shift_assoc_aux (main x) (shift x) (main y) (shift y) (main z) (shift z))
  one_mul x := ext (by simp) (by simp)
  mul_one x := ext (by simp) (by simp)
  left_distrib x y z := ext
    (by simp only [main_mul, main_add]; noncomm_ring)
    (by simp only [shift_mul, main_add, shift_add, map_add]; noncomm_ring)
  right_distrib x y z := ext
    (by simp only [main_mul, main_add]; noncomm_ring)
    (by simp only [shift_mul, main_add, shift_add]; noncomm_ring)
  zero_mul x := ext (by simp) (by simp)
  mul_zero x := ext (by simp) (by simp)

/-- The inclusion `K^M_*(k) → K^M_*(k) ⊕ K^M_*(k) ξ` as a ring homomorphism. -/
def ofMilnorK (k : Type u) [Field k] : MilnorKRing k →+* MilnorKShift k where
  toFun a := mk a 0
  map_one' := rfl
  map_mul' a b := ext (by simp) (by simp)
  map_zero' := rfl
  map_add' a b := ext (by simp) (by simp)

/-- The `ξ`-free coefficient of the image of `a` is `a`. -/
@[simp] theorem main_ofMilnorK (a : MilnorKRing k) : main (ofMilnorK k a) = a := rfl
/-- The `ξ`-coefficient of the image of `a` is `0`. -/
@[simp] theorem shift_ofMilnorK (a : MilnorKRing k) : shift (ofMilnorK k a) = 0 := rfl

/-- `main`, as an additive homomorphism. -/
def mainHom (k : Type u) [Field k] : MilnorKShift k →+ MilnorKRing k where
  toFun := main
  map_zero' := rfl
  map_add' _ _ := rfl

/-- `shift`, as an additive homomorphism. -/
def shiftHom (k : Type u) [Field k] : MilnorKShift k →+ MilnorKRing k where
  toFun := shift
  map_zero' := rfl
  map_add' _ _ := rfl

/-- `mainHom k` sends `x` to `main x`. -/
@[simp] theorem mainHom_apply (x : MilnorKShift k) : mainHom k x = main x := rfl
/-- `shiftHom k` sends `x` to `shift x`. -/
@[simp] theorem shiftHom_apply (x : MilnorKShift k) : shiftHom k x = shift x := rfl

end MilnorKShift

/-! ### The grading -/

/-- `K^M_{n-1}(k)`, read as the zero subgroup when `n = 0`. -/
def milnorKGradingPred (k : Type u) [Field k] : ℕ → AddSubgroup (MilnorKRing k)
  | 0 => ⊥
  | (n + 1) => milnorKGrading k n

/-- `milnorKGradingPred k 0` is the zero subgroup. -/
@[simp]
theorem milnorKGradingPred_zero : milnorKGradingPred k 0 = ⊥ := rfl

/-- `milnorKGradingPred k (n + 1)` is `K^M_n(k)`. -/
@[simp]
theorem milnorKGradingPred_succ (n : ℕ) :
    milnorKGradingPred k (n + 1) = milnorKGrading k n := rfl

/-- The degree-`n` part `K^M_n(k) ⊕ K^M_{n-1}(k) ξ` of the shifted Milnor K-ring. -/
def milnorKShiftGrading (k : Type u) [Field k] (n : ℕ) : AddSubgroup (MilnorKShift k) :=
  AddSubgroup.comap (MilnorKShift.mainHom k) (milnorKGrading k n) ⊓
    AddSubgroup.comap (MilnorKShift.shiftHom k) (milnorKGradingPred k n)

/-- `a + b ξ` lies in degree `n` if and only if `a ∈ K^M_n(k)` and `b ∈ K^M_{n-1}(k)`. -/
theorem mem_milnorKShiftGrading {n : ℕ} {x : MilnorKShift k} :
    x ∈ milnorKShiftGrading k n ↔
      MilnorKShift.main x ∈ milnorKGrading k n ∧
        MilnorKShift.shift x ∈ milnorKGradingPred k n :=
  Iff.rfl

/-- The unit lies in degree `0`. -/
theorem one_mem_milnorKShiftGrading : (1 : MilnorKShift k) ∈ milnorKShiftGrading k 0 := by
  refine mem_milnorKShiftGrading.2 ⟨?_, ?_⟩
  · simpa only [MilnorKShift.main_one] using
      SetLike.one_mem_graded (A := milnorKGrading k)
  · simp

/-- The grading of the shifted Milnor K-ring is multiplicative: the product of an element of
degree `m` and an element of degree `n` has degree `m + n`. -/
theorem milnorKShiftGrading_mul {m n : ℕ} {x y : MilnorKShift k}
    (hx : x ∈ milnorKShiftGrading k m) (hy : y ∈ milnorKShiftGrading k n) :
    x * y ∈ milnorKShiftGrading k (m + n) := by
  obtain ⟨hx₁, hx₂⟩ := mem_milnorKShiftGrading.1 hx
  obtain ⟨hy₁, hy₂⟩ := mem_milnorKShiftGrading.1 hy
  refine mem_milnorKShiftGrading.2 ⟨?_, ?_⟩
  · simpa only [MilnorKShift.main_mul] using SetLike.mul_mem_graded hx₁ hy₁
  rw [MilnorKShift.shift_mul]
  match m, n with
  | 0, 0 =>
      rw [milnorKGradingPred_zero, AddSubgroup.mem_bot] at hx₂ hy₂
      simp [hx₂, hy₂]
  | 0, n + 1 =>
      rw [milnorKGradingPred_zero, AddSubgroup.mem_bot] at hx₂
      simpa [hx₂] using SetLike.mul_mem_graded hx₁ hy₂
  | m + 1, 0 =>
      rw [milnorKGradingPred_zero, AddSubgroup.mem_bot] at hy₂
      rw [milnorKGradingPred_succ] at hx₂
      simpa [hy₂] using SetLike.mul_mem_graded hx₂ (milnorKInvolution_mem_milnorKGrading 0 hy₁)
  | m + 1, n + 1 =>
      rw [milnorKGradingPred_succ] at hx₂ hy₂
      rw [show m + 1 + (n + 1) = m + n + 1 + 1 by omega, milnorKGradingPred_succ]
      refine add_mem (add_mem ?_ ?_) ?_
      · simpa only [show m + 1 + n = m + n + 1 by omega] using SetLike.mul_mem_graded hx₁ hy₂
      · simpa only [show m + (n + 1) = m + n + 1 by omega] using
          SetLike.mul_mem_graded hx₂ (milnorKInvolution_mem_milnorKGrading (n + 1) hy₁)
      · exact SetLike.mul_mem_graded (SetLike.mul_mem_graded hx₂ hy₂)
          (milnorKNegOne_mem_milnorKGrading (k := k))
