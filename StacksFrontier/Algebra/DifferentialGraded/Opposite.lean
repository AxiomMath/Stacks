module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DGA.Abelian

/-!
# Opposite differential graded algebras

The opposite `A^opp` of a differential graded algebra `(A, d)` over a commutative ring `R` has
the same underlying graded `R`-module and the same differential; on homogeneous elements its
multiplication reverses the factors and introduces the Koszul sign,
`a ·_opp b = (-1)^{deg a · deg b} (b · a)`. Taking opposites is what turns left differential
graded modules into right ones, which is why the chapter can work with right modules
throughout.

## Main definitions

* `DifferentialGradedAlgebra.Opposite`: the data of an opposite differential graded algebra,
  namely a differential graded algebra together with the identification of its underlying graded
  module with that of `A` and the four formulas this identification satisfies.
* `DifferentialGradedAlgebra.opposite`: the construction of that data.

## Main results

The fields `Opposite.mem_grading_iff`, `Opposite.map_d`, `Opposite.map_one` and
`Opposite.map_mul_of_mem` give the grading, the differential, the unit and the signed
multiplication of the opposite algebra.

## Implementation notes

The construction is stated through `Opposite` rather than by exhibiting a term of
`DifferentialGradedAlgebra R` directly, because the two ring structures live on the same Lean
type: identifying the underlying graded modules by an `R`-linear equivalence avoids silently
identifying the two multiplications. The projection
`(opposite R A).toDifferentialGradedAlgebra` is the coefficient algebra one feeds to
`DifferentialGradedModule`, and the fields supply its defining formulas without unfolding the
construction, which is implicitly reducible so that its dependent projections may be used in
types.

As elsewhere in the chapter the base ring is commutative while the differential graded algebra
need not be, the grading is cohomological, and `Int.negOnePow` expresses the Koszul sign for
arbitrary integer degrees.

## References

* [Stacks Project, Tag 09JG](https://stacks.math.columbia.edu/tag/09JG)
-/

@[expose] public section

namespace DifferentialGradedAlgebra

universe u v w

variable (R : Type u) [CommRing R] (A : DifferentialGradedAlgebra.{u, v} R)

/-- An opposite differential graded algebra for `A`, including the canonical identification of
its underlying graded `R`-module with that of `A`. -/
public structure Opposite where
  /-- The opposite differential graded algebra. -/
  toDifferentialGradedAlgebra : DifferentialGradedAlgebra.{u, v} R
  /-- The identification of its underlying graded module with that of the original algebra. -/
  equiv : toDifferentialGradedAlgebra.A ≃ₗ[R] A.A
  /-- The identification preserves and reflects every homogeneous component. -/
  mem_grading_iff (n : ℤ) (x : toDifferentialGradedAlgebra.A) :
    x ∈ toDifferentialGradedAlgebra.grading n ↔ equiv x ∈ A.grading n
  /-- Under the identification, the differential is unchanged. -/
  map_d (x : toDifferentialGradedAlgebra.A) :
    equiv (toDifferentialGradedAlgebra.d x) = A.d (equiv x)
  /-- Under the identification, the unit is unchanged. -/
  map_one : equiv 1 = 1
  /-- On homogeneous elements, multiplication is reversed with the Koszul sign. -/
  map_mul_of_mem (n m : ℤ) (a b : toDifferentialGradedAlgebra.A)
      (ha : a ∈ toDifferentialGradedAlgebra.grading n)
      (hb : b ∈ toDifferentialGradedAlgebra.grading m) :
    equiv (a * b) = (n * m).negOnePow • (equiv b * equiv a)

attribute [simp] Opposite.mem_grading_iff Opposite.map_d Opposite.map_one

private noncomputable def extendLinear (M : Type w) [AddCommGroup M] [Module R M] :
    (∀ n, A.grading n →ₗ[R] M) →ₗ[R] (A.A →ₗ[R] M) :=
  (LinearMap.lcomp R M (DirectSum.decomposeLinearEquiv A.grading).toLinearMap).comp
    (DFinsupp.lsum R).toLinearMap

private lemma extendLinear_apply (M : Type w) [AddCommGroup M] [Module R M]
    (f : ∀ n, A.grading n →ₗ[R] M) (n : ℤ) (a : A.grading n) :
    extendLinear R A M f a = f n a := by
  show (DFinsupp.lsum R f) (DirectSum.decomposeLinearEquiv A.grading a) = _
  rw [DirectSum.decomposeLinearEquiv_apply_coe]
  exact DFinsupp.lsum_single R f n a

private noncomputable def homogeneousMul (n m : ℤ) :
    A.grading n →ₗ[R] A.grading m →ₗ[R] A.A where
  toFun a :=
    { toFun := fun b => ((n * m).negOnePow : ℤ) • ((b : A.A) * (a : A.A))
      map_add' := by intros; simp [add_mul, smul_add]
      map_smul' := by intros; simp [smul_comm] }
  map_add' := by intros; ext; simp [mul_add, smul_add]
  map_smul' := by intros; ext; simp [smul_comm]

/-- Extend signed reversed multiplication from homogeneous pairs by bilinearity. -/
private noncomputable def oppositeMul : A.A →ₗ[R] A.A →ₗ[R] A.A :=
  extendLinear R A (A.A →ₗ[R] A.A) fun n =>
    (extendLinear R A A.A).comp (LinearMap.pi fun m => homogeneousMul R A n m)

private lemma oppositeMul_of_mem (n m : ℤ) (a b : A.A)
    (ha : a ∈ A.grading n) (hb : b ∈ A.grading m) :
    oppositeMul R A a b = ((n * m).negOnePow : ℤ) • (b * a) := by
  rw [oppositeMul, extendLinear_apply R A _ _ n ⟨a, ha⟩, LinearMap.comp_apply,
    extendLinear_apply R A _ _ m ⟨b, hb⟩]
  rfl

private lemma oppositeMul_mem (n m : ℤ) (a b : A.A)
    (ha : a ∈ A.grading n) (hb : b ∈ A.grading m) :
    oppositeMul R A a b ∈ A.grading (n + m) := by
  rw [oppositeMul_of_mem R A n m a b ha hb]
  exact zsmul_mem (by simpa only [add_comm] using SetLike.mul_mem_graded hb ha) _

private lemma oppositeMul_one (a : A.A) : oppositeMul R A a 1 = a := by
  induction a using DirectSum.Decomposition.inductionOn A.grading with
  | zero => simp
  | homogeneous a =>
    rw [oppositeMul_of_mem R A _ 0 _ _ a.property (SetLike.one_mem_graded A.grading)]
    simp
  | add a b ha hb => simp [ha, hb]

private lemma one_oppositeMul (a : A.A) : oppositeMul R A 1 a = a := by
  induction a using DirectSum.Decomposition.inductionOn A.grading with
  | zero => simp
  | homogeneous a =>
    rw [oppositeMul_of_mem R A 0 _ _ _ (SetLike.one_mem_graded A.grading) a.property]
    simp
  | add a b ha hb => simp [ha, hb]

private lemma oppositeMul_assoc_homogeneous (n m k : ℤ) (a b c : A.A)
    (ha : a ∈ A.grading n) (hb : b ∈ A.grading m) (hc : c ∈ A.grading k) :
    oppositeMul R A (oppositeMul R A a b) c =
      oppositeMul R A a (oppositeMul R A b c) := by
  rw [oppositeMul_of_mem R A (n + m) k _ _ (oppositeMul_mem R A n m a b ha hb) hc,
    oppositeMul_of_mem R A n (m + k) _ _ ha (oppositeMul_mem R A m k b c hb hc),
    oppositeMul_of_mem R A n m a b ha hb, oppositeMul_of_mem R A m k b c hb hc]
  simp only [mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc]
  congr 1
  simp only [← Units.val_mul, ← Int.negOnePow_add]
  congr 2
  ring

private lemma oppositeMul_assoc (a b c : A.A) :
    oppositeMul R A (oppositeMul R A a b) c =
      oppositeMul R A a (oppositeMul R A b c) := by
  induction a using DirectSum.Decomposition.inductionOn A.grading with
  | zero => simp
  | add a a' ha ha' => simp [ha, ha']
  | @homogeneous n a =>
    induction b using DirectSum.Decomposition.inductionOn A.grading with
    | zero => simp
    | add b b' hb hb' => simp [hb, hb']
    | @homogeneous m b =>
      induction c using DirectSum.Decomposition.inductionOn A.grading with
      | zero => simp
      | add c c' hc hc' => simp [hc, hc']
      | @homogeneous k c =>
        exact oppositeMul_assoc_homogeneous R A n m k a b c a.property b.property c.property

private lemma oppositeMul_leibniz (n m : ℤ) (a b : A.A)
    (ha : a ∈ A.grading n) (hb : b ∈ A.grading m) :
    A.d (oppositeMul R A a b) = oppositeMul R A (A.d a) b +
      (n.negOnePow : ℤ) • oppositeMul R A a (A.d b) := by
  rw [oppositeMul_of_mem R A n m a b ha hb,
    oppositeMul_of_mem R A (n + 1) m _ _ (A.d_mem n a ha) hb,
    oppositeMul_of_mem R A n (m + 1) _ _ ha (A.d_mem m b hb),
    map_zsmul, A.leibniz m n b a hb ha]
  simp only [smul_add, smul_smul]
  simp only [← Units.val_mul, ← Int.negOnePow_add]
  rw [add_comm]
  congr 3
  · rw [Int.negOnePow_eq_iff]
    exact ⟨0, by ring⟩
  · rw [Int.negOnePow_eq_iff]
    exact ⟨-n, by ring⟩

@[instance_reducible] private noncomputable def oppositeRing : Ring A.A :=
  { A.ring.toAddCommGroup, A.ring.toAddGroupWithOne with
    mul := fun a b => oppositeMul R A a b
    npow := @npowRec A.A ⟨1⟩ ⟨fun a b => oppositeMul R A a b⟩
    mul_assoc := oppositeMul_assoc R A
    one_mul := one_oppositeMul R A
    mul_one := oppositeMul_one R A
    left_distrib := fun a b c => (oppositeMul R A a).map_add b c
    right_distrib := fun a b c => congrArg (fun f : A.A →ₗ[R] A.A => f c)
      ((oppositeMul R A).map_add a b)
    zero_mul := fun a => congrArg (fun f : A.A →ₗ[R] A.A => f a)
      (oppositeMul R A).map_zero
    mul_zero := fun a => (oppositeMul R A a).map_zero }

@[instance_reducible] private noncomputable def oppositeAlgebra :
    @Algebra R A.A _ (oppositeRing R A).toSemiring := by
  letI : Module R A.A := A.isAlg.toModule
  letI := oppositeRing R A
  exact Algebra.ofModule
    (fun r a b => congrArg (fun f : A.A →ₗ[R] A.A => f b) ((oppositeMul R A).map_smul r a))
    (fun r a b => (oppositeMul R A a).map_smul r b)

private noncomputable def oppositeDGA : DifferentialGradedAlgebra.{u, v} R := by
  letI := oppositeRing R A
  letI := oppositeAlgebra R A
  exact
    { A := A.A
      grading := A.grading
      gradedAlg :=
        { A.gradedAlg.toDecomposition with
          one_mem := A.gradedAlg.one_mem
          mul_mem := fun {n m} {a b} ha hb => oppositeMul_mem R A n m a b ha hb }
      d := A.d
      d_comp_d := A.d_comp_d
      d_mem := A.d_mem
      leibniz := oppositeMul_leibniz R A }

private lemma opposite_exists : Nonempty (Opposite R A) := ⟨{
    toDifferentialGradedAlgebra := oppositeDGA R A
    equiv := LinearEquiv.refl R A.A
    mem_grading_iff _ _ := Iff.rfl
    map_d _ := rfl
    map_one := rfl
    map_mul_of_mem n m a b ha hb := oppositeMul_of_mem R A n m a b ha hb }⟩

/-- The opposite differential graded algebra. Its underlying graded module and differential are
canonically identified with those of `A`, and its multiplication on homogeneous elements is
`a ⋅ᵒᵖᵖ b = (-1)^(deg a * deg b) • (b * a)`. -/
@[stacks 09JG, implicit_reducible]
public noncomputable def opposite : Opposite R A := by
  exact Classical.choice (show Nonempty (Opposite R A) from by exact opposite_exists R A)

end DifferentialGradedAlgebra
