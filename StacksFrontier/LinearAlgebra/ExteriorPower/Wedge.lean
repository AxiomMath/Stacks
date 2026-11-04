module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import StacksFrontier.LinearAlgebra.ExteriorPower.Koszul

/-!
# The bigraded wedge product of exterior powers

The exterior powers `⋀[R]^p M` are the graded pieces of `ExteriorAlgebra R M`, so the
multiplication of the exterior algebra restricts to an `R`-bilinear map
`⋀[R]^p M × ⋀[R]^q M → ⋀[R]^(p + q) M`.  This file builds that map,
`exteriorPower.wedgeMul`, and proves the identities that make the exterior powers a graded
`R`-algebra: graded commutativity and associativity.

## Main definitions

* `exteriorPower.wedgeMul`: the wedge product `⋀[R]^p M →ₗ[R] ⋀[R]^q M →ₗ[R] ⋀[R]^(p + q) M`.
* `exteriorPower.degCongr`: the reindexing `⋀[R]^m M ≃ₗ[R] ⋀[R]^n M` along an equality `m = n`
  of degrees.
* `exteriorPower.unitDegZero`: the unit of the exterior algebra as the generator of `⋀[R]^0 M`.

## Main results

* `exteriorPower.mul_comm_of_mem`, `exteriorPower.coe_wedgeMul_comm` and
  `exteriorPower.wedgeMul_comm`: **graded commutativity** `ω ∧ η = (-1)^{p q} η ∧ ω`, in the
  exterior algebra and inside a single exterior power.
* `exteriorPower.coe_wedgeMul_assoc`: the wedge product is **associative**.
* `exteriorPower.wedgeMul_ιMulti`: the wedge of two generators concatenates the two families.
* `exteriorPower.wedgeMul_map`: functoriality of the wedge product in `M`.
* `exteriorPower.wedgeLeft_eq_wedgeMul`: wedging with a vector on the left is the wedge product
  with that vector as an element of `⋀[R]^1 M`.
-/

@[expose] public noncomputable section

namespace exteriorPower

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-! ### Reindexing an exterior power -/

/-- The identification `⋀[R]^m M ≃ₗ[R] ⋀[R]^n M` of exterior powers of equal degrees `m = n`, the
identity on the underlying elements of the exterior algebra. -/
def degCongr {m n : ℕ} (h : m = n) : ⋀[R]^m M ≃ₗ[R] ⋀[R]^n M :=
  LinearEquiv.ofEq _ _ (by rw [h])

/-- `exteriorPower.degCongr` is the identity on the underlying elements of the exterior algebra. -/
@[simp]
theorem coe_degCongr {m n : ℕ} (h : m = n) (x : ⋀[R]^m M) :
    ((degCongr h x : ⋀[R]^n M) : ExteriorAlgebra R M) = (x : ExteriorAlgebra R M) := rfl

/-- The unit `1` of the exterior algebra, as the canonical generator of the zeroth exterior power —
the empty wedge. -/
def unitDegZero (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] :
    ⋀[R]^0 M := ιMulti R 0 Fin.elim0

/-- `exteriorPower.unitDegZero R M` is the unit `1` of the exterior algebra. -/
@[simp]
theorem coe_unitDegZero (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] :
    ((unitDegZero R M : ⋀[R]^0 M) : ExteriorAlgebra R M) = 1 := by
  rw [unitDegZero, ιMulti_apply_coe, ExteriorAlgebra.ιMulti_zero_apply]

/-- A vector sits in the first exterior power. -/
theorem ι_mem_degreeOne (x : M) : ExteriorAlgebra.ι R x ∈ ⋀[R]^1 M := by
  simpa only [pow_one] using LinearMap.mem_range_self (ExteriorAlgebra.ι R) x

/-- A sign scales an element of an exterior power by the same sign in the exterior algebra. -/
@[simp]
theorem coe_neg_one_pow_smul (n m : ℕ) (x : ⋀[R]^m M) :
    (((-1 : R) ^ n • x : ⋀[R]^m M) : ExteriorAlgebra R M) =
      (-1) ^ n * (x : ExteriorAlgebra R M) := by
  rw [SetLike.val_smul, Algebra.smul_def]
  simp

/-! ### The wedge product -/

/-- The wedge product `⋀^p M × ⋀^q M → ⋀^{p+q} M`, as an `R`-bilinear map: the product of the
exterior algebra restricted to its graded pieces. -/
def wedgeMul (p q : ℕ) : ⋀[R]^p M →ₗ[R] ⋀[R]^q M →ₗ[R] ⋀[R]^(p + q) M :=
  LinearMap.mk₂ R
    (fun x y ↦ ⟨(x : ExteriorAlgebra R M) * (y : ExteriorAlgebra R M),
      SetLike.mul_mem_graded x.2 y.2⟩)
    (fun x₁ x₂ y ↦ Subtype.ext (by simpa using add_mul (x₁ : ExteriorAlgebra R M) x₂ y))
    (fun c x y ↦ Subtype.ext (by simp))
    (fun x y₁ y₂ ↦ Subtype.ext (by simpa using mul_add (x : ExteriorAlgebra R M) y₁ y₂))
    (fun c x y ↦ Subtype.ext (by simp))

/-- The wedge product of `x` and `y` is their product in the exterior algebra. -/
@[simp]
theorem wedgeMul_apply_coe (p q : ℕ) (x : ⋀[R]^p M) (y : ⋀[R]^q M) :
    ((wedgeMul p q x y : ⋀[R]^(p + q) M) : ExteriorAlgebra R M) =
      (x : ExteriorAlgebra R M) * (y : ExteriorAlgebra R M) := rfl

/-- The wedge of two generators concatenates the two families of vectors. -/
theorem wedgeMul_ιMulti (p q : ℕ) (u : Fin p → M) (v : Fin q → M) :
    wedgeMul p q (ιMulti R p u) (ιMulti R q v) = ιMulti R (p + q) (Fin.append u v) :=
  Subtype.ext (by
    simp only [wedgeMul_apply_coe, ιMulti_apply_coe, ExteriorAlgebra.ιMulti_mul_ιMulti])

/-- The maps `⋀^n φ` induced by a linear map `φ` are multiplicative for the wedge product. -/
theorem wedgeMul_map {N : Type*} [AddCommGroup N] [Module R N] (p q : ℕ) (φ : M →ₗ[R] N)
    (x : ⋀[R]^p M) (y : ⋀[R]^q M) :
    map (p + q) φ (wedgeMul p q x y) = wedgeMul p q (map p φ x) (map q φ y) :=
  Subtype.ext (by simp only [wedgeMul_apply_coe, coe_map, map_mul])

/-- Wedging with a vector `e` on the left, `⋀^n M → ⋀^{n+1} M`, is the wedge product with `e` as an
element of `⋀^1 M`, reindexed from `⋀^{1+n} M` to `⋀^{n+1} M`. -/
theorem wedgeLeft_eq_wedgeMul (e : M) (n : ℕ) (x : ⋀[R]^n M) :
    wedgeLeft e n x =
      degCongr (Nat.add_comm 1 n) (wedgeMul 1 n ⟨ExteriorAlgebra.ι R e, ι_mem_degreeOne e⟩ x) :=
  Subtype.ext (by rw [coe_wedgeLeft, coe_degCongr, wedgeMul_apply_coe])

/-! ### Graded commutativity -/

/-- Elements of degrees `p` and `q` of the exterior algebra commute up to the sign `(-1)^{p q}`. -/
theorem mul_comm_of_mem {p q : ℕ} {a b : ExteriorAlgebra R M}
    (ha : a ∈ ⋀[R]^p M) (hb : b ∈ ⋀[R]^q M) :
    a * b = (-1) ^ (p * q) * (b * a) := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at ha hb
  induction ha, hb using Submodule.span_induction₂ with
  | mem_mem a b ha hb =>
      obtain ⟨u, rfl⟩ := ha
      obtain ⟨v, rfl⟩ := hb
      rw [ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm, Units.smul_def, zsmul_eq_mul,
        Nat.mul_comm q p]
      simp
  | zero_left => simp
  | zero_right => simp
  | add_left a₁ a₂ b _ _ _ h₁ h₂ => rw [add_mul, h₁, h₂, mul_add, mul_add]
  | add_right a b₁ b₂ _ _ _ h₁ h₂ => rw [mul_add, add_mul, h₁, h₂, mul_add]
  | smul_left c a b _ _ h => rw [smul_mul_assoc, h, mul_smul_comm, mul_smul_comm]
  | smul_right c a b _ _ h => rw [mul_smul_comm, h, smul_mul_assoc, mul_smul_comm]

/-- Graded commutativity of the wedge product in the exterior algebra:
`x ∧ y = (-1)^{p q} y ∧ x`. -/
theorem coe_wedgeMul_comm (p q : ℕ) (x : ⋀[R]^p M) (y : ⋀[R]^q M) :
    ((wedgeMul p q x y : ⋀[R]^(p + q) M) : ExteriorAlgebra R M) =
      (-1) ^ (p * q) * ((wedgeMul q p y x : ⋀[R]^(q + p) M) : ExteriorAlgebra R M) :=
  mul_comm_of_mem x.2 y.2

/-- Graded commutativity of the wedge product, `ω ∧ η = (-1)^{p q} η ∧ ω`, in the exterior power
`⋀^{p+q} M`. -/
theorem wedgeMul_comm (p q : ℕ) (x : ⋀[R]^p M) (y : ⋀[R]^q M) :
    wedgeMul p q x y =
      (-1 : R) ^ (p * q) • degCongr (Nat.add_comm q p) (wedgeMul q p y x) := by
  exact Subtype.ext (by rw [coe_neg_one_pow_smul, coe_degCongr, coe_wedgeMul_comm p q x y])

/-! ### Associativity -/

/-- The wedge product is associative, in the exterior algebra. -/
theorem coe_wedgeMul_assoc (p q r : ℕ) (x : ⋀[R]^p M) (y : ⋀[R]^q M) (z : ⋀[R]^r M) :
    ((wedgeMul (p + q) r (wedgeMul p q x y) z : ⋀[R]^(p + q + r) M) : ExteriorAlgebra R M) =
      ((wedgeMul p (q + r) x (wedgeMul q r y z) : ⋀[R]^(p + (q + r)) M) :
        ExteriorAlgebra R M) :=
  mul_assoc (x : ExteriorAlgebra R M) y z

/-- The wedge product is associative, in the exterior power `⋀^{p+q+r} M`. -/
theorem wedgeMul_assoc (p q r : ℕ) (x : ⋀[R]^p M) (y : ⋀[R]^q M) (z : ⋀[R]^r M) :
    wedgeMul (p + q) r (wedgeMul p q x y) z =
      degCongr (Nat.add_assoc p q r).symm (wedgeMul p (q + r) x (wedgeMul q r y z)) :=
  Subtype.ext (by rw [coe_degCongr, coe_wedgeMul_assoc])

end exteriorPower

end
