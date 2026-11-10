module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.KGroupChernCharacter
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapDivisorInduction
public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClassTensor
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.NewtonAdditivity

/-!
# The `n^i`-scaling of total classes, and the Chern classes of an invertible module

Let `X` be locally of finite type over the base of chapter 42 of the Stacks Project. This file
studies the `n^i`-scaling of total Chow cohomology classes and computes the Chern classes and
power sums of an invertible module.

* **The `n^i`-scaling** `Stacks.Chow.TotalChowClass.powScale n` of `∏_{i ≥ 0} A^i(X)`,
  multiplying `A^i(X)` by `n^i`. It is a ring endomorphism
  (`Stacks.Chow.TotalChowClass.powScaleRingHom`): on the degree-`m` component of a product the
  two factors contribute `n^i n^j = n^m`. It commutes with restriction.
* **Stacks 02SP on total classes**: `c₁(ℒ ⊗ 𝒩) = c₁(ℒ) + c₁(𝒩)`
  (`Stacks.Chow.TotalChowClass.firstChernTotal_tensorObj`).
* For an invertible `ℒ`, `c(ℒ) = 1 + c₁(ℒ)` (`Stacks.Chow.totalChern_eq_one_add_firstChernTotal`)
  and `P_p(ℒ) = c₁(ℒ)^p` (`Stacks.Chow.modulePowerSumArbitraryRank_eq_pow`): the Chern roots of a
  module of rank one are its first Chern class.

## References

* [Stacks Project, Tag 0FEN](https://stacks.math.columbia.edu/tag/0FEN)
* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Finset

universe u

namespace Stacks.Chow

/-! ### The `n^i`-scaling of a graded cap family -/

section CapFamily

universe v

variable {G : ℤ → Type v} [∀ k, AddCommGroup (G k)]

/-- The `n^i`-scaling of a graded cap family: the family whose index-`i` component is `n^i` times
that of `a`. -/
def capFamilyPowScale (n : ℤ) (a : GradedCapFamily G) : GradedCapFamily G :=
  fun k i => AddMonoidHom.mk' (fun x => (n ^ i) • a k i x)
    fun x y => by rw [map_add, smul_add]

/-- The index-`i` component of the `n^i`-scaling of `a` is `n^i` times that of `a`. -/
@[simp]
theorem capFamilyPowScale_apply (n : ℤ) (a : GradedCapFamily G) (k : ℤ) (i : ℕ) (x : G k) :
    capFamilyPowScale n a k i x = (n ^ i) • a k i x :=
  rfl

/-- The scaling fixes the unit, which is concentrated in index `0`. -/
theorem capFamilyPowScale_one (n : ℤ) : capFamilyPowScale n (1 : GradedCapFamily G) = 1 := by
  funext k i
  refine AddMonoidHom.ext fun x => ?_
  rcases i with _ | i
  · rw [capFamilyPowScale_apply, pow_zero, one_smul]
  · rw [capFamilyPowScale_apply, gradedCap_one_of_ne (Nat.succ_ne_zero i) k]
    simp

/-- The scaling is multiplicative for the convolution: on the summand indexed by `(m - j, j)` of
the index-`m` component of a product the factors contribute `n^{m-j} n^j = n^m`. -/
theorem capFamilyPowScale_mul (n : ℤ) (a b : GradedCapFamily G) :
    capFamilyPowScale n (a * b) = capFamilyPowScale n a * capFamilyPowScale n b := by
  funext k m
  refine AddMonoidHom.ext fun x => ?_
  rw [capFamilyPowScale_apply, gradedCap_mul_apply, gradedCap_mul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [convolveTerm_of_le a b k hjm,
    convolveTerm_of_le (capFamilyPowScale n a) (capFamilyPowScale n b) k hjm,
    capTo_def, capTo_def, capFamilyPowScale_apply, capFamilyPowScale_apply, map_zsmul,
    map_zsmul, map_zsmul, smul_smul, ← pow_add, show m - j + j = m from by omega]

end CapFamily

namespace TotalChowClass

/-! ### The `n^i`-scaling of total classes -/

section PowScale

variable {C : ChowSituation.{u}} {Y Y' : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
  {sY' : Y' ⟶ C.S} [LocallyOfFiniteType sY']

/-- **The `n^i`-scaling of a total Chow cohomology class**: the class whose degree-`i` component
is `n^i` times that of `c`. -/
def powScale (n : ℤ) (c : TotalChowClass C sY) : TotalChowClass C sY :=
  fun i ↦ (n ^ i) • c i

/-- The degree-`i` component of the `n^i`-scaling of `c` is `n^i` times that of `c`. -/
@[simp]
theorem powScale_apply (n : ℤ) (c : TotalChowClass C sY) (i : ℕ) :
    powScale n c i = (n ^ i) • c i :=
  rfl

/-- The operation of the scaling is the scaling of the operation. -/
theorem op_powScale (n : ℤ) (c : TotalChowClass C sY) {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] : (powScale n c).op g = capFamilyPowScale n (c.op g) := by
  funext k p
  refine AddMonoidHom.ext fun α ↦ ?_
  rw [capFamilyPowScale_apply, op_apply, op_apply, powScale_apply, BivariantClass.idRule_zsmul]

/-- The scaling fixes the unit class. -/
theorem powScale_one (n : ℤ) : powScale n (1 : TotalChowClass C sY) = 1 :=
  ext_op fun g _ ↦ by rw [op_powScale, op_one, capFamilyPowScale_one]

/-- The scaling is multiplicative: `powScale n (c * d) = powScale n c * powScale n d`. -/
theorem powScale_mul (n : ℤ) (c d : TotalChowClass C sY) :
    powScale n (c * d) = powScale n c * powScale n d :=
  ext_op fun g _ ↦ by
    rw [op_powScale, op_mul, op_mul, capFamilyPowScale_mul, op_powScale, op_powScale]

/-- **The `n^i`-scaling as a ring endomorphism** of the total Chow cohomology classes. -/
def powScaleRingHom (n : ℤ) : TotalChowClass C sY →+* TotalChowClass C sY where
  toFun := powScale n
  map_one' := powScale_one n
  map_mul' := powScale_mul n
  map_zero' := by ext p; rw [powScale_apply, zero_apply, smul_zero]
  map_add' c d := by
    ext p
    rw [powScale_apply, add_apply, add_apply, powScale_apply, powScale_apply, smul_add]

/-- The ring endomorphism `powScaleRingHom n` acts as `powScale n`. -/
@[simp]
theorem powScaleRingHom_apply (n : ℤ) (c : TotalChowClass C sY) :
    powScaleRingHom (C := C) (sY := sY) n c = powScale n c :=
  rfl

/-- The scaling commutes with restriction. -/
theorem res_powScale (n : ℤ) (h : Y' ⟶ Y) [LocallyOfFiniteType h] (hs : h ≫ sY = sY')
    (c : TotalChowClass C sY) : res h hs (powScale n c) = powScale n (res h hs c) := by
  subst hs
  ext p
  rw [res_rfl_apply, powScale_apply, powScale_apply, res_rfl_apply, map_zsmul]

/-- The scaling of a class homogeneous of degree `i` is `n^i` times the class. -/
theorem IsHomogeneous.powScale_eq {i : ℕ} {c : TotalChowClass C sY} (hc : c.IsHomogeneous i)
    (n : ℤ) : powScale n c = (n ^ i) • c := by
  refine ext fun p ↦ ?_
  rw [powScale_apply]
  change (n ^ p) • c p = (n ^ i) • c p
  rcases eq_or_ne p i with rfl | hp
  · rfl
  · rw [hc p hp, smul_zero, smul_zero]

end PowScale

/-! ### The first Chern class of a tensor product -/

section FirstChern

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- The index-`1` operation of `c₁(ℒ)` on a test scheme, as the cap with `c₁(g^*ℒ)` followed by a
transport of degrees. -/
theorem op_firstChernTotal_one (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
    {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sY) k) :
    haveI := isInvertible_pullback g L
    (firstChernTotal C sY L).op g k 1 α =
      chowGroupCast C (g ≫ sY) (show k - 1 = k - ((1 : ℕ) : ℤ) by simp)
        ((invCap C (g ≫ sY) ((Scheme.Modules.pullback g).obj L)).capOnChow C (g ≫ sY) (k - 1)
          (chowGroupCast C (g ≫ sY) (by omega) α)) := by
  have := isInvertible_pullback g L
  exact eq_of_heq ((op_firstChernTotal_one_heq C sY L g k α).trans
    (chowGroupCast_heq C (g ≫ sY) _ _).symm)

/-- **Stacks 02SP on total classes**: `c₁(ℒ ⊗ 𝒩) = c₁(ℒ) + c₁(𝒩)`. -/
theorem firstChernTotal_tensorObj (L N : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property N] :
    firstChernTotal C sY (Scheme.Modules.tensorObj L N) =
      firstChernTotal C sY L + firstChernTotal C sY N := by
  refine ext_op fun g _ ↦ ?_
  rw [op_add]
  funext k p
  refine AddMonoidHom.ext fun α ↦ ?_
  rw [gradedCap_add_apply]
  rcases eq_or_ne p 1 with rfl | hp
  · have := isInvertible_pullback g L
    have := isInvertible_pullback g N
    rw [op_firstChernTotal_one, op_firstChernTotal_one, op_firstChernTotal_one, ← map_add,
      invCap_capOnChow_tensorObj,
      invCap_capOnChow_congr C (g ≫ sY) _ _ (pullbackTensorObjIso g L N)]
  · rw [(isHomogeneous_firstChernTotal C sY _).op g k p hp,
      (isHomogeneous_firstChernTotal C sY L).op g k p hp,
      (isHomogeneous_firstChernTotal C sY N).op g k p hp]
    simp

end FirstChern

end TotalChowClass

/-! ### The total Chern class and the power sums of an invertible module -/

section Invertible

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **The total Chern class of an invertible module** is `c(ℒ) = 1 + c₁(ℒ)`. -/
theorem totalChern_eq_one_add_firstChernTotal :
    letI := isFiniteLocallyFreeOfRank_one_of_isInvertible L
    totalChern C sX L 1 = 1 + TotalChowClass.firstChernTotal C sX L := by
  let := isFiniteLocallyFreeOfRank_one_of_isInvertible L
  refine TotalChowClass.ext fun p ↦ ?_
  rw [TotalChowClass.add_apply]
  rcases p with _ | _ | p
  · rw [totalChern_apply_zero, TotalChowClass.firstChernTotal_apply_of_ne C sX L (by omega),
      add_zero]
  · have h : TotalChowClass.firstChernTotal C sX L 1 =
        TotalChowClass.homComponent 1 (totalChern C sX L 1) 1 := by
      rw [← TotalChowClass.firstChernTotal_eq_homComponent_totalChern]
    rw [TotalChowClass.homComponent_apply, ite_eq_left rfl] at h
    rw [TotalChowClass.one_apply_of_ne (by omega), h]
    exact (zero_add _).symm
  · rw [totalChern_apply_of_lt C sX L 1 (by omega), TotalChowClass.one_apply_of_ne (by omega),
      TotalChowClass.firstChernTotal_apply_of_ne C sX L (by omega), add_zero]

/-- The total Chern class of an invertible module, read through the arbitrary-rank total Chern
class, is `1 + c₁(ℒ)`. -/
theorem totalChernClassOfModule_eq_one_add_firstChernTotal :
    letI := isFiniteLocallyFreeOfRank_one_of_isInvertible L
    letI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L :=
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
    totalChernClassOfModule C sX L = 1 + TotalChowClass.firstChernTotal C sX L := by
  let := isFiniteLocallyFreeOfRank_one_of_isInvertible L
  let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
  rw [totalChernClassOfModule_eq_totalChern C sX L 1, totalChern_eq_one_add_firstChernTotal]

/-- **The power sums of an invertible module** are the powers of its first Chern class:
`P_p(ℒ) = c₁(ℒ)^p`, including `P_0(ℒ) = 1`, the rank. -/
theorem modulePowerSumArbitraryRank_eq_pow (p : ℕ) :
    letI := isFiniteLocallyFreeOfRank_one_of_isInvertible L
    letI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L :=
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
    modulePowerSumArbitraryRank C sX L p = TotalChowClass.firstChernTotal C sX L ^ p := by
  let := isFiniteLocallyFreeOfRank_one_of_isInvertible L
  let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
  rw [modulePowerSumArbitraryRank_eq_modulePowerSum C sX L 1 inferInstance]
  unfold modulePowerSum
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · rw [newtonPowerSum_zero, pow_zero, Nat.cast_one, one_smul]
  · refine newtonPowerSum_eq_pow_of_rankOne _ _ _ ?_ (fun i hi ↦ ?_) p hp
    · exact (TotalChowClass.firstChernTotal_eq_homComponent_totalChern C sX L).symm
    · refine TotalChowClass.ext fun q ↦ ?_
      rw [TotalChowClass.homComponent_apply, TotalChowClass.zero_apply]
      split_ifs with hq
      · subst hq
        exact totalChern_apply_of_lt C sX L 1 hi
      · rfl

end Invertible

end Stacks.Chow

end
