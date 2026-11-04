module

public import Mathlib.RingTheory.Derivation.Basic

/-!
# Correcting the multiplication of a ring by a symmetric pairing

Let `R'` be a commutative ring, `π : R' → L` a derivation into an `R'`-module and
`μ : L × L → R'` a symmetric `R'`-bilinear pairing with `π ∘ μ = 0`. Then
`x ⋆ y := x * y - μ (π x) (π y)` is again a commutative ring structure on the additive group of
`R'`, with the same unit. This is the correction used to turn a solution of the extension problem
on the arrow site into a deformation of a pair: the square of the kernel of the arrow is killed.

## Main definitions

* `Deformation.PairDeformation.MultiplicationCorrection`: the datum `(π, μ)`.
* `Deformation.PairDeformation.CorrectedRing`: the additive group of `R'` with the corrected
  multiplication, as a commutative ring.
* `Deformation.PairDeformation.CorrectedRing.equiv`: the identity of the underlying additive
  groups.
* `Deformation.PairDeformation.CorrectedRing.ringHomTo`: a ring map into `R'` killed by `π` is a
  ring map into the corrected ring.
* `Deformation.PairDeformation.CorrectedRing.ringHomFrom`: a ring map out of `R'` killing the
  image of `μ` is a ring map out of the corrected ring.
* `Deformation.PairDeformation.CorrectedRing.derivation`: `π` is a derivation of the corrected
  ring, for any action of the corrected ring on `L` agreeing with the old one.
* `Deformation.PairDeformation.CorrectedRing.moduleOfPairingSMul`: when the image of `μ` acts by
  zero on `L`, the old action is an action of the corrected ring.

## Main results

* `Deformation.PairDeformation.CorrectedRing.ofCorrected_mul`: the corrected multiplication.
* `Deformation.PairDeformation.CorrectedRing.derivation_ofCorrected_mul`: the Leibniz rule for
  the corrected multiplication, with the old action on `L`.

## Implementation notes

Associativity does not use the symmetry of `μ`: both sides equal
`x y z - z μ(π x, π y) - x μ(π y, π z) - y μ(π x, π z)`, using only bilinearity and
`π ∘ μ = 0`. Symmetry is used for commutativity.

## References

* [Stacks Project, Tag 0D4W](https://stacks.math.columbia.edu/tag/0D4W)
-/

@[expose] public section

namespace Deformation.PairDeformation

variable {R' : Type*} [CommRing R'] {L : Type*} [AddCommGroup L] [Module R' L]

/-- The datum of a multiplication correction: a derivation `π : R' → L` and a symmetric
`R'`-bilinear pairing `μ : L × L → R'` whose values are killed by `π`. -/
structure MultiplicationCorrection (R' : Type*) [CommRing R'] (L : Type*) [AddCommGroup L]
    [Module R' L] where
  /-- The derivation `π`. -/
  derivation : Derivation ℤ R' L
  /-- The pairing `μ`. -/
  pairing : L →ₗ[R'] L →ₗ[R'] R'
  /-- The pairing is symmetric. -/
  pairing_comm : ∀ a b, pairing a b = pairing b a
  /-- The derivation kills the values of the pairing. -/
  derivation_pairing : ∀ a b, derivation (pairing a b) = 0

namespace MultiplicationCorrection

variable (c : MultiplicationCorrection R' L)

/-- The corrected multiplication `x ⋆ y = x y - μ (π x) (π y)`, on `R'` itself. -/
def mul (x y : R') : R' := x * y - c.pairing (c.derivation x) (c.derivation y)

/-- The corrected multiplication, unfolded. -/
theorem mul_def (x y : R') :
    c.mul x y = x * y - c.pairing (c.derivation x) (c.derivation y) := rfl

/-- The corrected multiplication is associative. -/
theorem mul_assoc (x y z : R') : c.mul (c.mul x y) z = c.mul x (c.mul y z) := by
  simp only [mul_def, map_sub, Derivation.leibniz, c.derivation_pairing, sub_zero, map_add,
    LinearMap.add_apply, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- The corrected multiplication is commutative, by the symmetry of `μ`. -/
theorem mul_comm (x y : R') : c.mul x y = c.mul y x := by
  rw [mul_def, mul_def, c.pairing_comm, _root_.mul_comm]

/-- The corrected multiplication distributes over addition on the left. -/
theorem mul_add (x y z : R') : c.mul x (y + z) = c.mul x y + c.mul x z := by
  simp only [mul_def, map_add]
  ring

/-- The corrected multiplication distributes over addition on the right. -/
theorem add_mul (x y z : R') : c.mul (x + y) z = c.mul x z + c.mul y z := by
  simp only [mul_def, map_add, LinearMap.add_apply]
  ring

/-- `0 ⋆ x = 0`. -/
theorem zero_mul (x : R') : c.mul 0 x = 0 := by
  simp [mul_def]

/-- `x ⋆ 0 = 0`. -/
theorem mul_zero (x : R') : c.mul x 0 = 0 := by
  simp [mul_def]

/-- `1 ⋆ x = x`: the unit of `R'` is a unit for the corrected multiplication. -/
theorem one_mul (x : R') : c.mul 1 x = x := by
  simp [mul_def]

/-- `x ⋆ 1 = x`. -/
theorem mul_one (x : R') : c.mul x 1 = x := by
  simp [mul_def]

end MultiplicationCorrection

/-- The additive group of `R'` with the corrected multiplication `x ⋆ y = x y - μ (π x) (π y)`.
It is a commutative ring with the same unit (`CorrectedRing.instCommRing`). -/
def CorrectedRing (_c : MultiplicationCorrection R' L) : Type _ := R'

namespace CorrectedRing

variable (c : MultiplicationCorrection R' L)

/-- An element of `R'`, seen in the corrected ring. -/
def toCorrected (x : R') : CorrectedRing c := x

/-- An element of the corrected ring, seen in `R'`. -/
def ofCorrected (x : CorrectedRing c) : R' := x

/-- `ofCorrected` undoes `toCorrected`. -/
@[simp]
theorem ofCorrected_toCorrected (x : R') : ofCorrected c (toCorrected c x) = x := rfl

/-- `toCorrected` undoes `ofCorrected`. -/
@[simp]
theorem toCorrected_ofCorrected (x : CorrectedRing c) : toCorrected c (ofCorrected c x) = x := rfl

/-- The corrected ring is a commutative ring: the additive structure of `R'`, the corrected
multiplication, and the unit of `R'`. -/
instance instCommRing : CommRing (CorrectedRing c) where
  __ := (inferInstance : AddCommGroup R')
  mul x y := toCorrected c (c.mul (ofCorrected c x) (ofCorrected c y))
  one := toCorrected c 1
  natCast n := toCorrected c (n : R')
  natCast_zero := Nat.cast_zero (R := R')
  natCast_succ n := Nat.cast_succ (R := R') n
  intCast n := toCorrected c (n : R')
  intCast_ofNat n := Int.cast_natCast (R := R') n
  intCast_negSucc n := Int.cast_negSucc (R := R') n
  mul_assoc x y z := c.mul_assoc x y z
  mul_comm x y := c.mul_comm x y
  left_distrib x y z := c.mul_add x y z
  right_distrib x y z := c.add_mul x y z
  zero_mul x := c.zero_mul x
  mul_zero x := c.mul_zero x
  one_mul x := c.one_mul x
  mul_one x := c.mul_one x

/-- The identity of the underlying additive groups of `R'` and of the corrected ring. -/
def equiv : R' ≃+ CorrectedRing c where
  toFun := toCorrected c
  invFun := ofCorrected c
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- `equiv` is `toCorrected`. -/
@[simp]
theorem equiv_apply (x : R') : equiv c x = toCorrected c x := rfl

/-- The inverse of `equiv` is `ofCorrected`. -/
@[simp]
theorem equiv_symm_apply (x : CorrectedRing c) : (equiv c).symm x = ofCorrected c x := rfl

/-- `ofCorrected` is additive. -/
@[simp]
theorem ofCorrected_add (x y : CorrectedRing c) :
    ofCorrected c (x + y) = ofCorrected c x + ofCorrected c y := rfl

/-- `ofCorrected` preserves zero. -/
@[simp]
theorem ofCorrected_zero : ofCorrected c 0 = 0 := rfl

/-- `ofCorrected` preserves negation. -/
@[simp]
theorem ofCorrected_neg (x : CorrectedRing c) : ofCorrected c (-x) = -ofCorrected c x := rfl

/-- `ofCorrected` preserves subtraction. -/
@[simp]
theorem ofCorrected_sub (x y : CorrectedRing c) :
    ofCorrected c (x - y) = ofCorrected c x - ofCorrected c y := rfl

/-- `ofCorrected` preserves the unit. -/
@[simp]
theorem ofCorrected_one : ofCorrected c 1 = 1 := rfl

/-- **The corrected multiplication**: `x ⋆ y = x y - μ (π x) (π y)`. -/
@[simp]
theorem ofCorrected_mul (x y : CorrectedRing c) :
    ofCorrected c (x * y) = ofCorrected c x * ofCorrected c y -
      c.pairing (c.derivation (ofCorrected c x)) (c.derivation (ofCorrected c y)) := rfl

/-- `toCorrected` is additive. -/
@[simp]
theorem toCorrected_add (x y : R') :
    toCorrected c (x + y) = toCorrected c x + toCorrected c y := rfl

/-- `toCorrected` preserves zero. -/
@[simp]
theorem toCorrected_zero : toCorrected c 0 = 0 := rfl

/-- `toCorrected` preserves the unit. -/
@[simp]
theorem toCorrected_one : toCorrected c 1 = 1 := rfl

/-- `toCorrected` is injective. -/
theorem toCorrected_injective : Function.Injective (toCorrected c) := fun _ _ h => h

/-- `ofCorrected` is injective. -/
theorem ofCorrected_injective : Function.Injective (ofCorrected c) := fun _ _ h => h

/-- **`π` is a derivation for the corrected multiplication**, with the old action of `R'` on
`L`: the correction term lies in the kernel of `π`. -/
theorem derivation_ofCorrected_mul (x y : CorrectedRing c) :
    c.derivation (ofCorrected c (x * y)) =
      ofCorrected c x • c.derivation (ofCorrected c y) +
        ofCorrected c y • c.derivation (ofCorrected c x) := by
  rw [ofCorrected_mul, map_sub, c.derivation_pairing, sub_zero, Derivation.leibniz]

/-- **`π` is a derivation of the corrected ring**, for any action of the corrected ring on `L`
which agrees with the old action of `R'`. -/
def derivation [Module (CorrectedRing c) L]
    (h : ∀ (x : CorrectedRing c) (l : L), x • l = ofCorrected c x • l) :
    Derivation ℤ (CorrectedRing c) L :=
  Derivation.mk'
    { toFun := fun x => c.derivation (ofCorrected c x)
      map_add' := fun x y => map_add c.derivation (ofCorrected c x) (ofCorrected c y)
      map_smul' := fun n x => by
        simp only [eq_intCast, Int.cast_id]
        exact map_zsmul c.derivation n (ofCorrected c x) }
    (fun x y => by
      simp only [LinearMap.coe_mk, h]
      exact derivation_ofCorrected_mul c x y)

/-- `derivation c h` is `π` on the underlying elements. -/
@[simp]
theorem derivation_apply [Module (CorrectedRing c) L]
    (h : ∀ (x : CorrectedRing c) (l : L), x • l = ofCorrected c x • l) (x : CorrectedRing c) :
    derivation c h x = c.derivation (ofCorrected c x) := rfl

/-- When the values of `μ` act by zero on `L`, the action of `R'` on `L` is an action of the
corrected ring. -/
@[instance_reducible]
def moduleOfPairingSMul (h : ∀ (a b : L) (l : L), c.pairing a b • l = 0) :
    Module (CorrectedRing c) L where
  smul x l := ofCorrected c x • l
  one_smul l := one_smul R' l
  mul_smul x y l := by
    change ofCorrected c (x * y) • l = ofCorrected c x • ofCorrected c y • l
    rw [ofCorrected_mul, sub_smul, h, sub_zero, mul_smul]
  smul_zero x := smul_zero (ofCorrected c x)
  smul_add x := smul_add (ofCorrected c x)
  add_smul x y := add_smul (ofCorrected c x) (ofCorrected c y)
  zero_smul := zero_smul R'

/-- The action of the corrected ring in `moduleOfPairingSMul` is the action of `R'`. -/
theorem moduleOfPairingSMul_smul (h : ∀ (a b : L) (l : L), c.pairing a b • l = 0)
    (x : CorrectedRing c) (l : L) :
    letI := moduleOfPairingSMul c h
    x • l = ofCorrected c x • l := rfl

/-- **A ring map into `R'` killed by `π` is a ring map into the corrected ring.** -/
def ringHomTo {S : Type*} [Semiring S] (φ : S →+* R') (hφ : ∀ s, c.derivation (φ s) = 0) :
    S →+* CorrectedRing c where
  toFun s := toCorrected c (φ s)
  map_one' := by rw [map_one]; rfl
  map_mul' s t := by
    apply toCorrected_injective c
    change φ (s * t) = φ s * φ t - c.pairing (c.derivation (φ s)) (c.derivation (φ t))
    rw [hφ, hφ, map_zero, sub_zero, map_mul]
  map_zero' := by rw [map_zero]; rfl
  map_add' s t := by rw [map_add]; rfl

/-- `ringHomTo` is `φ` on the underlying elements. -/
@[simp]
theorem ofCorrected_ringHomTo {S : Type*} [Semiring S] (φ : S →+* R')
    (hφ : ∀ s, c.derivation (φ s) = 0) (s : S) :
    ofCorrected c (ringHomTo c φ hφ s) = φ s := rfl

/-- **A ring map out of `R'` killing the values of `μ` is a ring map out of the corrected
ring.** -/
def ringHomFrom {T : Type*} [Ring T] (χ : R' →+* T) (hχ : ∀ a b, χ (c.pairing a b) = 0) :
    CorrectedRing c →+* T where
  toFun x := χ (ofCorrected c x)
  map_one' := map_one χ
  map_mul' x y := by
    rw [ofCorrected_mul, map_sub, hχ, sub_zero, map_mul]
  map_zero' := map_zero χ
  map_add' x y := map_add χ (ofCorrected c x) (ofCorrected c y)

/-- `ringHomFrom` is `χ` on the underlying elements. -/
@[simp]
theorem ringHomFrom_apply {T : Type*} [Ring T] (χ : R' →+* T)
    (hχ : ∀ a b, χ (c.pairing a b) = 0) (x : CorrectedRing c) :
    ringHomFrom c χ hχ x = χ (ofCorrected c x) := rfl

/-- Composing `ringHomTo` with `ringHomFrom` gives the composite of the original maps. -/
theorem ringHomFrom_comp_ringHomTo {S T : Type*} [Semiring S] [Ring T] (φ : S →+* R')
    (hφ : ∀ s, c.derivation (φ s) = 0) (χ : R' →+* T) (hχ : ∀ a b, χ (c.pairing a b) = 0) :
    (ringHomFrom c χ hχ).comp (ringHomTo c φ hφ) = χ.comp φ := rfl

end CorrectedRing

end Deformation.PairDeformation
