module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.FiniteSyntomicMorphisms.UniversalFamily

/-!
# The algebra structure on the universal finite free family

The relations defining the universal coefficient ring `A_d` make the prescribed multiplication on
the free module `B_d` associative, commutative and unital, and make `B_d` an algebra over `A_d`.

## Main definitions

* `AlgebraicGeometry.universalAlgebraStructure`: the commutative `A_d`-algebra structure on the
  universal finite free module `B_d`, whose operations are given coordinatewise by the universal
  multiplication table.

## References

* [Stacks Project, Tag 0FKZ](https://stacks.math.columbia.edu/tag/0FKZ)
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace AlgebraicGeometry

private lemma universalFiniteFreeModule_ext {d : ℕ} [NeZero d]
    {x y : UniversalFiniteFreeModule d} (h : ∀ i, x.coeff i = y.coeff i) : x = y := by
  cases x
  cases y
  congr
  exact funext h

/-- The `m`-th coordinate of the left-bracketed triple product `(x * y) * z` is the sum over
`i, j, k` of `x_i y_j z_k` times `∑ l, c i j l * c l k m`. -/
private lemma universalMultiplication_assoc_coeff_left (d : ℕ) [NeZero d]
    (x y z : UniversalFiniteFreeModule d) (m : Fin d) :
    (universalMultiplication d (universalMultiplication d x y) z).coeff m =
      ∑ i, ∑ j, ∑ k, x.coeff i * y.coeff j * z.coeff k *
        (∑ l, universalStructureConstant d i j l * universalStructureConstant d l k m) := by
  simp only [universalMultiplication, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => enter [2, l]; rw [Finset.sum_comm]; enter [2, k]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [Finset.sum_comm]; enter [2, j]; rw [Finset.sum_comm]
  simp only [mul_comm, mul_left_comm, mul_assoc]

/-- The `m`-th coordinate of the right-bracketed triple product `x * (y * z)` is the sum over
`i, j, k` of `x_i y_j z_k` times `∑ l, c i l m * c j k l`. -/
private lemma universalMultiplication_assoc_coeff_right (d : ℕ) [NeZero d]
    (x y z : UniversalFiniteFreeModule d) (m : Fin d) :
    ∑ i, ∑ j, ∑ k, x.coeff i * y.coeff j * z.coeff k *
        (∑ l, universalStructureConstant d i l m * universalStructureConstant d j k l) =
      (universalMultiplication d x (universalMultiplication d y z)).coeff m := by
  simp only [universalMultiplication, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]; enter [2, j]; rw [Finset.sum_comm]
  simp only [mul_comm, mul_left_comm, mul_assoc]

/-- The universal multiplication on `B_d` is associative, coordinatewise. -/
private lemma universalMultiplication_assoc_coeff (d : ℕ) [NeZero d]
    (x y z : UniversalFiniteFreeModule d) (m : Fin d) :
    (universalMultiplication d (universalMultiplication d x y) z).coeff m =
      (universalMultiplication d x (universalMultiplication d y z)).coeff m := by
  calc
    _ = ∑ i, ∑ j, ∑ k, x.coeff i * y.coeff j * z.coeff k *
          (∑ l, universalStructureConstant d i j l * universalStructureConstant d l k m) :=
        universalMultiplication_assoc_coeff_left d x y z m
    _ = ∑ i, ∑ j, ∑ k, x.coeff i * y.coeff j * z.coeff k *
          (∑ l, universalStructureConstant d i l m * universalStructureConstant d j k l) := by
        simp_rw [universalStructureConstant_assoc]
    _ = _ := universalMultiplication_assoc_coeff_right d x y z m

/-- The defining relations on the universal structure constants equip `B_d`
with its prescribed commutative `A_d`-algebra structure. -/
@[stacks 0FKZ "algebra_axioms"]
noncomputable def universalAlgebraStructure (d : ℕ) [NeZero d] :
    UniversalAlgebraStructure d :=
  letI : Zero (UniversalFiniteFreeModule d) := ⟨⟨fun _ ↦ 0⟩⟩
  letI : Add (UniversalFiniteFreeModule d) := ⟨fun x y ↦ ⟨fun i ↦ x.coeff i + y.coeff i⟩⟩
  letI : Neg (UniversalFiniteFreeModule d) := ⟨fun x ↦ ⟨fun i ↦ -x.coeff i⟩⟩
  letI : One (UniversalFiniteFreeModule d) := ⟨universalUnit d⟩
  letI : Mul (UniversalFiniteFreeModule d) := ⟨universalMultiplication d⟩
  let ring : CommRing (UniversalFiniteFreeModule d) := {
    add_assoc x y z := by exact universalFiniteFreeModule_ext fun _ ↦ add_assoc _ _ _
    zero_add x := by exact universalFiniteFreeModule_ext fun _ ↦ zero_add _
    add_zero x := by exact universalFiniteFreeModule_ext fun _ ↦ add_zero _
    add_comm x y := by exact universalFiniteFreeModule_ext fun _ ↦ add_comm _ _
    mul_assoc x y z := by
      exact universalFiniteFreeModule_ext (universalMultiplication_assoc_coeff d x y z)
    one_mul x := by
      refine universalFiniteFreeModule_ext fun m ↦ ?_
      change (universalMultiplication d (universalUnit d) x).coeff m = x.coeff m
      simp [universalUnit, universalBasisVector, universalMultiplication,
        universalStructureConstant_comm, universalStructureConstant_unit]
    mul_one x := by
      refine universalFiniteFreeModule_ext fun m ↦ ?_
      change (universalMultiplication d x (universalUnit d)).coeff m = x.coeff m
      simp [universalUnit, universalBasisVector, universalMultiplication,
        universalStructureConstant_unit]
    left_distrib x y z := by
      refine universalFiniteFreeModule_ext fun m ↦ ?_
      change (universalMultiplication d x ⟨fun i ↦ y.coeff i + z.coeff i⟩).coeff m =
        (universalMultiplication d x y).coeff m + (universalMultiplication d x z).coeff m
      simp only [universalMultiplication, mul_add, add_mul, Finset.sum_add_distrib]
    right_distrib x y z := by
      refine universalFiniteFreeModule_ext fun m ↦ ?_
      change (universalMultiplication d ⟨fun i ↦ x.coeff i + y.coeff i⟩ z).coeff m =
        (universalMultiplication d x z).coeff m + (universalMultiplication d y z).coeff m
      simp only [universalMultiplication, add_mul, Finset.sum_add_distrib]
    zero_mul x := by
      refine universalFiniteFreeModule_ext fun m ↦ ?_
      change (universalMultiplication d ⟨fun _ ↦ 0⟩ x).coeff m = 0
      simp [universalMultiplication]
    mul_zero x := by
      refine universalFiniteFreeModule_ext fun m ↦ ?_
      change (universalMultiplication d x ⟨fun _ ↦ 0⟩).coeff m = 0
      simp [universalMultiplication]
    mul_comm x y := by
      refine universalFiniteFreeModule_ext fun m ↦ ?_
      change (universalMultiplication d x y).coeff m = (universalMultiplication d y x).coeff m
      simp only [universalMultiplication]
      rw [Finset.sum_comm]
      congr 1
      funext i
      congr 1
      funext j
      rw [universalStructureConstant_comm d j i m]
      ring
    neg_add_cancel x := by exact universalFiniteFreeModule_ext fun _ ↦ neg_add_cancel _
    nsmul := nsmulRec
    nsmul_zero _ := rfl
    nsmul_succ _ _ := rfl
    zsmul := zsmulRec
    zsmul_zero' _ := rfl
    zsmul_succ' _ _ := rfl
    zsmul_neg' _ _ := rfl }
  letI := ring
  let scalarMap :
    FiniteFreeAlgebra.universalRing d →+*
      UniversalFiniteFreeModule d := {
    toFun a := ⟨fun i ↦ if i = 0 then a else 0⟩
    map_zero' := by
      refine universalFiniteFreeModule_ext fun i ↦ ?_
      change (if i = 0 then 0 else 0) = 0
      simp
    map_one' := by
      refine universalFiniteFreeModule_ext fun i ↦ ?_
      change (if i = 0 then 1 else 0) = (universalUnit d).coeff i
      simp [universalUnit, universalBasisVector, eq_comm]
    map_add' a b := by
      refine universalFiniteFreeModule_ext fun i ↦ ?_
      change (if i = 0 then a + b else 0) =
        (if i = 0 then a else 0) + (if i = 0 then b else 0)
      split <;> simp_all
    map_mul' a b := by
      refine universalFiniteFreeModule_ext fun k ↦ ?_
      change (if k = 0 then a * b else 0) =
        (∑ i, ∑ j, (if i = 0 then a else 0) * (if j = 0 then b else 0) *
          universalStructureConstant d i j k)
      symm
      simp [universalStructureConstant_unit, eq_comm] }
  let algebra : Algebra
    (FiniteFreeAlgebra.universalRing d)
      (UniversalFiniteFreeModule d) :=
    scalarMap.toAlgebra
  {
    ring := ring
    algebra := algebra
    zero_coeff _ := rfl
    add_coeff _ _ _ := rfl
    neg_coeff _ _ := rfl
    one_eq := rfl
    mul_eq _ _ := rfl
    algebraMap_coeff _ _ := rfl }

end AlgebraicGeometry
