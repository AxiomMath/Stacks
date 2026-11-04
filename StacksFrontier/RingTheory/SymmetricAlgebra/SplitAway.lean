module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.AffineTwistSections
public import StacksFrontier.RingTheory.HomogeneousLocalization.BaseAlgebra
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The affine chart of a projective bundle at a split degree-one element

Let `A` be a commutative ring, `M` an `A`-module, `p : M →ₗ[A] A` a linear form and `s : M` an
element with `p s = 1`. Then `p` is a split surjection and `M = K ⊕ A·s` for
`K = LinearMap.ker p`. Grading `S = Sym_A(M)` by its symmetric powers
(`SymmetricAlgebra.grading`), the element `ι s` is homogeneous of degree one, so it has a
standard open `D₊(ι s)` in `Proj(Sym_A(M)) = 𝐏(M̃)`, whose coordinate ring is the degree-zero
homogeneous localization `HomogeneousLocalization.Away (grading A M) (ι A M s)`. This file
identifies that chart with the symmetric algebra of `K`:

`Sym_A(K) ≅ (Sym_A M)_{(ι s)}`,  `k ↦ ι k / ι s`.

## Main definitions

* `SymmetricAlgebra.splitProj`: the projection `M → K`, `m ↦ m - p m · s`.
* `SymmetricAlgebra.setOne`: the retraction `Sym_A(M) →ₐ[A] Sym_A(K)` that writes
  `m = k + p m · s` and sets `s = 1`.
* `SymmetricAlgebra.chartCoord`, `SymmetricAlgebra.chartToAway`: the affine coordinate
  `k ↦ ι k / ι s` and the `A`-algebra map `Sym_A(K) →ₐ[A] (Sym_A M)_{(ι s)}` it generates.
* `SymmetricAlgebra.awayToChart`: the extension of `setOne` over the localization at the powers
  of `ι s`, restricted to the degree-zero part.
* `SymmetricAlgebra.chartEquiv`: the isomorphism `Sym_A(K) ≃ₐ[A] (Sym_A M)_{(ι s)}` given by
  `chartToAway`.
* `SymmetricAlgebra.splitAwayEquiv`: **the chart identification**
  `(Sym_A M)_{(ι s)} ≃ₐ[A] Sym_A(K)`.

## Main results

* `SymmetricAlgebra.splitAwayEquiv_mk`: the chart identification sends the class of
  `a / (ι s)^n` to `setOne a`, and `SymmetricAlgebra.splitAwayEquiv_mk_ι` specialises this to the
  normalisation `ι k / ι s ↦ ι k` that pins the isomorphism down.
* `SymmetricAlgebra.algebraMapInv_comp_setOne`: setting `s = 1` and then killing `K` is the
  evaluation `SymmetricAlgebra.lift p`, and
  `SymmetricAlgebra.algebraMapInv_comp_splitAwayEquiv` reads that off on the chart: the composite
  `(Sym_A M)_{(ι s)} → Sym_A(K) → A` sends the class of `a / (ι s)^n` to
  `SymmetricAlgebra.lift p a`.

## References

* [Stacks Project, Tag 01OA](https://stacks.math.columbia.edu/tag/01OA)
* [Stacks Project, Tag 01MR](https://stacks.math.columbia.edu/tag/01MR)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open HomogeneousLocalization

namespace SymmetricAlgebra

universe u v

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]

/-! ### Degree bookkeeping -/

/-- Every element of `M` is homogeneous of degree one in `Sym_A(M)`. -/
theorem ι_mem_grading_one (m : M) : ι A M m ∈ grading A M 1 :=
  (mem_grading_one_iff A M).mpr (LinearMap.mem_range_self _ m)

/-- An element homogeneous of degree `n` is homogeneous of degree `n • 1`. -/
theorem mem_grading_nsmul {n : ℕ} {x : SymmetricAlgebra A M} (hx : x ∈ grading A M n) :
    x ∈ grading A M (n • 1) := by simpa using hx

/-- Every element of `M` is homogeneous of degree `1 • 1`. -/
theorem ι_mem_grading_smul (m : M) : ι A M m ∈ grading A M (1 • 1) :=
  mem_grading_nsmul (ι_mem_grading_one m)

/-- A scalar is homogeneous of degree `0 • 1`. -/
theorem algebraMap_mem_grading_smul (r : A) :
    algebraMap A (SymmetricAlgebra A M) r ∈ grading A M (0 • 1) := by
  refine mem_grading_nsmul ?_
  show algebraMap A (SymmetricAlgebra A M) r ∈ SymPow.symmetricPower 0 A M
  rw [SymPow.symmetricPower, pow_zero, Submodule.one_eq_range]
  exact ⟨r, rfl⟩

/-- The product of elements of degrees `m • 1` and `n • 1` has degree `(m + n) • 1`. -/
theorem mul_mem_grading_nsmul {m n : ℕ} {x y : SymmetricAlgebra A M}
    (hx : x ∈ grading A M (m • 1)) (hy : y ∈ grading A M (n • 1)) :
    x * y ∈ grading A M ((m + n) • 1) := by
  simp only [smul_eq_mul, mul_one] at hx hy ⊢
  exact SetLike.mul_mem_graded hx hy

/-! ### Arithmetic of fractions on the chart -/

section Fractions

variable (s : M)

/-- Fractions with the same denominator add by adding numerators. -/
theorem mk_add_mk (n : ℕ) (x y : SymmetricAlgebra A M) (hx : x ∈ grading A M (n • 1))
    (hy : y ∈ grading A M (n • 1)) :
    Away.mk (grading A M) (ι_mem_grading_one s) n x hx +
        Away.mk (grading A M) (ι_mem_grading_one s) n y hy =
      Away.mk (grading A M) (ι_mem_grading_one s) n (x + y) (add_mem hx hy) := by
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_add, Away.val_mk,
    Away.val_mk, Away.val_mk, Localization.add_mk_self]

/-- Fractions multiply by multiplying numerators and adding denominator exponents. -/
theorem mk_mul_mk (m n : ℕ) (x y : SymmetricAlgebra A M) (hx : x ∈ grading A M (m • 1))
    (hy : y ∈ grading A M (n • 1)) :
    Away.mk (grading A M) (ι_mem_grading_one s) m x hx *
        Away.mk (grading A M) (ι_mem_grading_one s) n y hy =
      Away.mk (grading A M) (ι_mem_grading_one s) (m + n) (x * y)
        (mul_mem_grading_nsmul hx hy) := by
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mul, Away.val_mk,
    Away.val_mk, Away.val_mk, Localization.mk_mul]
  congr 1
  exact Subtype.ext (pow_add (ι A M s) m n).symm

/-- A scalar is the fraction with that numerator and denominator `(ι s)^0`. -/
theorem algebraMap_eq_mk (r : A) :
    algebraMap A (Away (grading A M) (ι A M s)) r =
      Away.mk (grading A M) (ι_mem_grading_one s) 0
        (algebraMap A (SymmetricAlgebra A M) r) (algebraMap_mem_grading_smul r) := by
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_algebraMap, Away.val_mk,
    IsScalarTower.algebraMap_apply A (SymmetricAlgebra A M)
      (Localization (Submonoid.powers (ι A M s))), ← Localization.mk_one_eq_algebraMap]
  congr 1
  exact Subtype.ext (pow_zero (ι A M s)).symm

/-- A scalar is a degree-one ratio: `r = ι (r · s) / ι s`. -/
theorem algebraMap_eq_mk_ι_smul (r : A) :
    algebraMap A (Away (grading A M) (ι A M s)) r =
      Away.mk (grading A M) (ι_mem_grading_one s) 1 (ι A M (r • s))
        (ι_mem_grading_smul _) := by
  rw [algebraMap_eq_mk, HomogeneousLocalization.ext_iff_val, Away.val_mk, Away.val_mk,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, pow_one, pow_zero, map_smul, Algebra.smul_def]
  ring

end Fractions

/-! ### Setting the split generator to one -/

section SetOne

variable (p : M →ₗ[A] A) (s : M)

/-- The projection of `M` onto `K = ker p` along `s`: `m ↦ m - p m · s`. -/
def splitProj (hps : p s = 1) : M →ₗ[A] LinearMap.ker p :=
  LinearMap.codRestrict _ (LinearMap.id - p.smulRight s) fun m => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
      map_sub, map_smul, hps, smul_eq_mul, mul_one, sub_self]

/-- The projection `splitProj p s hps` sends `m` to `m - p m • s`. -/
@[simp] theorem coe_splitProj (hps : p s = 1) (m : M) :
    (splitProj p s hps m : M) = m - p m • s := rfl

/-- The linear map underlying "write `m = k + p m · s`, then set `s = 1`". -/
def setOneLin (hps : p s = 1) : M →ₗ[A] SymmetricAlgebra A (LinearMap.ker p) :=
  (ι A (LinearMap.ker p)).comp (splitProj p s hps) +
    (Algebra.linearMap A (SymmetricAlgebra A (LinearMap.ker p))).comp p

/-- **Setting the split generator to one**: the retraction `Sym_A(M) →ₐ[A] Sym_A(K)` sending
`ι s` to `1` and `ι k` to `ι k` for `k ∈ K`. -/
def setOne (hps : p s = 1) :
    SymmetricAlgebra A M →ₐ[A] SymmetricAlgebra A (LinearMap.ker p) :=
  SymmetricAlgebra.lift (setOneLin p s hps)

/-- `setOne` sends `ι m` to `ι (m - p m • s) + p m`. -/
@[simp] theorem setOne_ι (hps : p s = 1) (m : M) :
    setOne p s hps (ι A M m) =
      ι A (LinearMap.ker p) (splitProj p s hps m) +
        algebraMap A (SymmetricAlgebra A (LinearMap.ker p)) (p m) :=
  SymmetricAlgebra.lift_ι_apply (setOneLin p s hps) m

/-- `setOne` sends the split generator `ι s` to `1`. -/
@[simp] theorem setOne_ι_self (hps : p s = 1) : setOne p s hps (ι A M s) = 1 := by
  have h0 : splitProj p s hps s = 0 := Subtype.ext (by simp [hps])
  rw [setOne_ι, h0, map_zero, hps, map_one, zero_add]

/-- `setOne` sends `ι k` to `ι k` for `k ∈ ker p`. -/
@[simp] theorem setOne_ι_coe (hps : p s = 1) (k : LinearMap.ker p) :
    setOne p s hps (ι A M (k : M)) = ι A (LinearMap.ker p) k := by
  have hk : p (k : M) = 0 := k.2
  have h0 : splitProj p s hps (k : M) = k := Subtype.ext (by simp [hk])
  rw [setOne_ι, h0, hk, map_zero, add_zero]

end SetOne

/-! ### The two comparison maps -/

section Comparison

variable (p : M →ₗ[A] A) (s : M)

/-- The affine coordinate of the chart: the fraction `ι k / ι s`, for `k ∈ K = ker p`. -/
def chartCoord : LinearMap.ker p →ₗ[A] Away (grading A M) (ι A M s) where
  toFun k :=
    Away.mk (grading A M) (ι_mem_grading_one s) 1 (ι A M (k : M)) (ι_mem_grading_smul _)
  map_add' k₁ k₂ := by
    rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_add, Away.val_mk,
      Away.val_mk, Away.val_mk, Localization.add_mk_self]
    congr 1
    exact (ι A M).map_add (k₁ : M) (k₂ : M)
  map_smul' a k := by
    rw [RingHom.id_apply, Algebra.smul_def, HomogeneousLocalization.ext_iff_val,
      HomogeneousLocalization.val_mul, HomogeneousLocalization.val_algebraMap, Away.val_mk,
      Away.val_mk, IsScalarTower.algebraMap_apply A (SymmetricAlgebra A M)
        (Localization (Submonoid.powers (ι A M s))), ← Localization.mk_one_eq_algebraMap,
      Localization.mk_mul, one_mul]
    congr 1
    rw [show ((a • k : LinearMap.ker p) : M) = a • (k : M) from rfl, map_smul, Algebra.smul_def]

/-- `chartCoord p s k` is the fraction `ι k / ι s`. -/
@[simp] theorem chartCoord_apply (k : LinearMap.ker p) :
    chartCoord p s k =
      Away.mk (grading A M) (ι_mem_grading_one s) 1 (ι A M (k : M)) (ι_mem_grading_smul _) :=
  rfl

/-- The comparison `Sym_A(K) →ₐ[A] (Sym_A M)_{(ι s)}` sending `k` to `ι k / ι s`. -/
def chartToAway : SymmetricAlgebra A (LinearMap.ker p) →ₐ[A] Away (grading A M) (ι A M s) :=
  SymmetricAlgebra.lift (chartCoord p s)

/-- `chartToAway` sends `ι k` to the fraction `ι k / ι s`. -/
@[simp] theorem chartToAway_ι (k : LinearMap.ker p) :
    chartToAway p s (ι A (LinearMap.ker p) k) =
      Away.mk (grading A M) (ι_mem_grading_one s) 1 (ι A M (k : M)) (ι_mem_grading_smul _) :=
  SymmetricAlgebra.lift_ι_apply (chartCoord p s) k

/-- `setOne` sends `ι s` to a unit. -/
theorem isUnit_setOne_ι_self (hps : p s = 1) :
    IsUnit ((setOne p s hps).toRingHom (ι A M s)) := by
  have h : (setOne p s hps).toRingHom (ι A M s) = 1 := setOne_ι_self p s hps
  exact h ▸ isUnit_one

/-- The comparison `(Sym_A M)_{(ι s)} →+* Sym_A(K)`: the extension of `setOne` over the
localization at the powers of `ι s`, restricted along the embedding of the degree-zero
homogeneous localization. -/
def awayToChart (hps : p s = 1) :
    Away (grading A M) (ι A M s) →+* SymmetricAlgebra A (LinearMap.ker p) :=
  (Localization.awayLift (setOne p s hps).toRingHom (ι A M s)
      (isUnit_iff_exists_inv.mpr ⟨1, by rw [mul_one]; exact setOne_ι_self p s hps⟩)).comp
    (algebraMap (Away (grading A M) (ι A M s)) (Localization (Submonoid.powers (ι A M s))))

/-- `awayToChart` sends the class of `a / (ι s)^n` to `setOne a`. -/
theorem awayToChart_mk (hps : p s = 1) (n : ℕ) (a : SymmetricAlgebra A M)
    (ha : a ∈ grading A M (n • 1)) :
    awayToChart p s hps (Away.mk (grading A M) (ι_mem_grading_one s) n a ha) =
      setOne p s hps a := by
  rw [awayToChart, RingHom.comp_apply]
  show Localization.awayLift _ _ _
    (Away.mk (grading A M) (ι_mem_grading_one s) n a ha).val = _
  rw [Away.val_mk, Localization.awayLift_mk (setOne p s hps).toRingHom (ι A M s) a 1
      (by rw [mul_one]; exact setOne_ι_self p s hps) n, one_pow, mul_one]
  rfl

end Comparison

/-! ### The two composites -/

section Composites

variable (p : M →ₗ[A] A) (s : M)

/-- `awayToChart` is a left inverse of `chartToAway`. -/
theorem awayToChart_chartToAway (hps : p s = 1) (x : SymmetricAlgebra A (LinearMap.ker p)) :
    awayToChart p s hps (chartToAway p s x) = x := by
  induction x using SymmetricAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes, algebraMap_eq_mk, awayToChart_mk, AlgHom.commutes]
  | ι k => rw [chartToAway_ι, awayToChart_mk, setOne_ι_coe]
  | mul x y hx hy => rw [map_mul, map_mul, hx, hy]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The splitting `m = (m - p m · s) + p m · s`, read on the chart: `ι m / ι s` is
`ι (m - p m · s) / ι s` plus the scalar `p m`. -/
theorem mk_ι_split (m : M) :
    Away.mk (grading A M) (ι_mem_grading_one s) 1 (ι A M m) (ι_mem_grading_smul m) =
      Away.mk (grading A M) (ι_mem_grading_one s) 1 (ι A M (m - p m • s))
          (ι_mem_grading_smul _) +
        Away.mk (grading A M) (ι_mem_grading_one s) 0
          (algebraMap A (SymmetricAlgebra A M) (p m)) (algebraMap_mem_grading_smul _) := by
  rw [← algebraMap_eq_mk, algebraMap_eq_mk_ι_smul, mk_add_mk]
  congr 1
  rw [← map_add, sub_add_cancel]

/-- The class of `ι m / ι s` is `chartToAway (setOne (ι m))`. -/
theorem mk_ι_eq_chartToAway (hps : p s = 1) (m : M) :
    Away.mk (grading A M) (ι_mem_grading_one s) 1 (ι A M m) (ι_mem_grading_smul m) =
      chartToAway p s (setOne p s hps (ι A M m)) := by
  rw [setOne_ι, map_add, chartToAway_ι, AlgHom.commutes, algebraMap_eq_mk]
  exact mk_ι_split p s m

/-- For `a` in the `n`-th power of the degree-one part of `Sym_A(M)`, the class of
`a / (ι s)^n` is `chartToAway (setOne a)`. -/
theorem mk_eq_chartToAway_setOne' (hps : p s = 1) (n : ℕ) (a : SymmetricAlgebra A M)
    (ha : a ∈ LinearMap.range (ι A M) ^ n) :
    Away.mk (grading A M) (ι_mem_grading_one s) n a (mem_grading_nsmul ha) =
      chartToAway p s (setOne p s hps a) := by
  induction ha using Submodule.pow_induction_on_right' with
  | algebraMap r => rw [AlgHom.commutes, AlgHom.commutes, algebraMap_eq_mk]
  | add x y i hx hy ihx ihy => rw [map_add, map_add, ← ihx, ← ihy, mk_add_mk]
  | mul_mem i x hx ih m hm =>
      obtain ⟨z, rfl⟩ := hm
      rw [map_mul, map_mul, ← ih, ← mk_ι_eq_chartToAway, mk_mul_mk]

/-- For `a` homogeneous of degree `n`, the class of `a / (ι s)^n` is
`chartToAway (setOne a)`. -/
theorem mk_eq_chartToAway_setOne (hps : p s = 1) (n : ℕ) (a : SymmetricAlgebra A M)
    (ha : a ∈ grading A M (n • 1)) :
    Away.mk (grading A M) (ι_mem_grading_one s) n a ha =
      chartToAway p s (setOne p s hps a) :=
  mk_eq_chartToAway_setOne' p s hps n a (by simpa using ha)

/-- The comparison out of `Sym_A(K)` is surjective. -/
theorem chartToAway_surjective (hps : p s = 1) :
    Function.Surjective (chartToAway p s (A := A) (M := M)) := by
  intro z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (grading A M) (ι_mem_grading_one s) z
  exact ⟨setOne p s hps a, (mk_eq_chartToAway_setOne p s hps n a ha).symm⟩

/-- The comparison out of `Sym_A(K)` is injective. -/
theorem chartToAway_injective (hps : p s = 1) :
    Function.Injective (chartToAway p s (A := A) (M := M)) := fun x y h => by
  rw [← awayToChart_chartToAway p s hps x, ← awayToChart_chartToAway p s hps y, h]

/-- **A ring map out of the chart is determined by the degree-one ratios.** Two ring
homomorphisms out of `(Sym_A M)_{(ι s)}` agreeing at every fraction `ι m / ι s`, `m : M`, are
equal. -/
theorem ringHom_ext_mk_ι {B : Type*} [CommRing B] (hps : p s = 1)
    {f g : Away (grading A M) (ι A M s) →+* B}
    (h : ∀ m : M,
      f (Away.mk (grading A M) (ι_mem_grading_one s) 1 (ι A M m) (ι_mem_grading_smul m)) =
        g (Away.mk (grading A M) (ι_mem_grading_one s) 1 (ι A M m) (ι_mem_grading_smul m))) :
    f = g := by
  have key : ∀ x : SymmetricAlgebra A (LinearMap.ker p),
      f (chartToAway p s x) = g (chartToAway p s x) := by
    intro x
    induction x using SymmetricAlgebra.induction with
    | algebraMap r => rw [AlgHom.commutes, algebraMap_eq_mk_ι_smul]; exact h (r • s)
    | ι k => rw [chartToAway_ι]; exact h k
    | mul x y hx hy => simp only [map_mul, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  refine RingHom.ext fun z => ?_
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (grading A M) (ι_mem_grading_one s) z
  rw [mk_eq_chartToAway_setOne p s hps n a ha]
  exact key _

end Composites

/-! ### The chart identification -/

section Equiv

variable (p : M →ₗ[A] A) (s : M)

/-- **The symmetric algebra of `K` is the standard affine chart at `ι s`.** For `p : M →ₗ[A] A`
and `s : M` with `p s = 1`, the comparison `k ↦ ι k / ι s` is an isomorphism of `A`-algebras
from `Sym_A(K)`, `K = ker p`, onto the degree-zero homogeneous localization of `Sym_A(M)` at the
degree-one element `ι s`. -/
@[sga "6 IX 3.3" "special case"]
def chartEquiv (hps : p s = 1) :
    SymmetricAlgebra A (LinearMap.ker p) ≃ₐ[A] Away (grading A M) (ι A M s) :=
  AlgEquiv.ofBijective (chartToAway p s)
    ⟨chartToAway_injective p s hps, chartToAway_surjective p s hps⟩

/-- The underlying map of `chartEquiv` is `chartToAway`. -/
@[simp] theorem chartEquiv_apply (hps : p s = 1) (x : SymmetricAlgebra A (LinearMap.ker p)) :
    chartEquiv p s hps x = chartToAway p s x := rfl

/-- **The standard affine chart of `Proj(Sym_A M)` at a split degree-one element.** The
degree-zero homogeneous localization of `Sym_A(M)` away from `ι s` is the symmetric algebra of
`K = ker p`, normalised by sending the class of `ι k / ι s` to `ι k`
(`SymmetricAlgebra.splitAwayEquiv_mk_ι`). -/
@[sga "6 IX 3.3" "special case"]
def splitAwayEquiv (hps : p s = 1) :
    Away (grading A M) (ι A M s) ≃ₐ[A] SymmetricAlgebra A (LinearMap.ker p) :=
  (chartEquiv p s hps).symm

/-- **The chart identification on a fraction**: the class of `a / (ι s)^n`, for `a` homogeneous
of degree `n`, goes to `setOne a`. -/
@[simp] theorem splitAwayEquiv_mk (hps : p s = 1) (n : ℕ) (a : SymmetricAlgebra A M)
    (ha : a ∈ grading A M (n • 1)) :
    splitAwayEquiv p s hps (Away.mk (grading A M) (ι_mem_grading_one s) n a ha) =
      setOne p s hps a := by
  rw [splitAwayEquiv, AlgEquiv.symm_apply_eq, chartEquiv_apply]
  exact mk_eq_chartToAway_setOne p s hps n a ha

/-- **The normalisation of the chart identification**: the class of `ι k / ι s` goes to `ι k`.
Together with `SymmetricAlgebra.splitAwayEquiv` being an `A`-algebra map this determines it. -/
@[simp] theorem splitAwayEquiv_mk_ι (hps : p s = 1) (k : LinearMap.ker p) :
    splitAwayEquiv p s hps
        (Away.mk (grading A M) (ι_mem_grading_one s) 1 (ι A M (k : M))
          (ι_mem_grading_smul _)) =
      ι A (LinearMap.ker p) k := by
  rw [splitAwayEquiv_mk, setOne_ι_coe]

/-- The chart identification is `SymmetricAlgebra.awayToChart`. -/
theorem splitAwayEquiv_apply (hps : p s = 1) (z : Away (grading A M) (ι A M s)) :
    splitAwayEquiv p s hps z = awayToChart p s hps z := by
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (grading A M) (ι_mem_grading_one s) z
  rw [splitAwayEquiv_mk, awayToChart_mk]

end Equiv

/-! ### Killing the chart coordinates -/

section Origin

variable (p : M →ₗ[A] A) (s : M)

/-- **Setting `s = 1` and then killing `K` is evaluation at `p`.** The composite
`Sym_A(M) → Sym_A(K) → A` of the retraction `setOne` with `SymmetricAlgebra.algebraMapInv` is
the `A`-algebra map induced by the linear form `p` itself. -/
theorem algebraMapInv_comp_setOne (hps : p s = 1) :
    (algebraMapInv (R := A) (M := LinearMap.ker p)).comp (setOne p s hps) =
      SymmetricAlgebra.lift p := by
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => ?_)
  show algebraMapInv (setOne p s hps (ι A M m)) = SymmetricAlgebra.lift p (ι A M m)
  rw [setOne_ι, map_add, algebraMapInv_ι, AlgHom.commutes]
  simp [SymmetricAlgebra.lift_ι_apply]

/-- **The chart identification followed by the origin of `Sym_A(K)` is evaluation at `p`.** The
composite `(Sym_A M)_{(ι s)} → Sym_A(K) → A` sends the class of `a / (ι s)^n` to
`SymmetricAlgebra.lift p a`; this is the `A`-point of the chart at which every affine coordinate
`ι k / ι s` vanishes. -/
theorem algebraMapInv_comp_splitAwayEquiv (hps : p s = 1) (n : ℕ) (a : SymmetricAlgebra A M)
    (ha : a ∈ grading A M (n • 1)) :
    algebraMapInv (splitAwayEquiv p s hps
        (Away.mk (grading A M) (ι_mem_grading_one s) n a ha)) =
      SymmetricAlgebra.lift p a := by
  rw [splitAwayEquiv_mk, ← AlgHom.comp_apply, algebraMapInv_comp_setOne]

end Origin

end SymmetricAlgebra

end
