module

public import StacksFrontier.Algebra.DifferentialGraded.GradedCommutative
public import StacksFrontier.Algebra.DifferentialGraded.TensorProductLift

/-!
# Graded commutativity and the tensor product of differential graded algebras

Graded commutativity of the target makes the Koszul anticommutation hypothesis of the universal
property automatic: any two homomorphisms `f : C → E` and `g : D → E` of differential graded
algebras over a commutative ring `R` have Koszul-anticommuting images as soon as the grading of
`E` is graded commutative, so every such pair lifts to `C ⊗_R D → E`.

Graded commutativity is also inherited by the tensor product. For homogeneous pure tensors this
is a sign computation: the Koszul multiplication contributes `(-1)^(q p')` to `(a ⊗ b)(c ⊗ d)`
and `(-1)^(q' p)` to `(c ⊗ d)(a ⊗ b)`, while commuting the factors inside contributes
`(-1)^(p p' + q q')`, and the two sides differ by `(-1)^(2 p q') = 1`. The general case follows
by a double span induction, the degree-`n` part of the tensor product being spanned by the
homogeneous pure tensors of total degree `n`.

## Main results

* `DifferentialGradedAlgebra.anticommutesAlong_of_isGradedCommutative`: a graded-commutative
  target makes any pair of homomorphisms into it Koszul-anticommuting.
* `DifferentialGradedAlgebra.tmul_mul_tmul_comm`: the graded commutation rule for two
  homogeneous pure tensors.
* `DifferentialGradedAlgebra.isGradedCommutative_tensorProduct`: the tensor product of two
  graded-commutative differential graded algebras is graded commutative. This is stated as a
  theorem rather than an instance, so that it is applied explicitly.
* `DifferentialGradedAlgebra.tensorProduct_mul_comm_of_mem`: the elementwise form of the
  previous statement.

## References

* [Stacks Project, Tag 065W](https://stacks.math.columbia.edu/tag/065W)
* [Stacks Project, Tag 061W](https://stacks.math.columbia.edu/tag/061W)
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R]

/-- Two homomorphisms into a graded-commutative differential graded algebra have
Koszul-anticommuting images, so the universal property of the tensor product applies to them. -/
theorem anticommutesAlong_of_isGradedCommutative {C D E : DifferentialGradedAlgebra R}
    (hE : DifferentialGraded.IsGradedCommutative E.grading) (f : C.Hom E) (g : D.Hom E) :
    AnticommutesAlong C D E f g := by
  intro i j a b
  rw [(DifferentialGraded.isGradedCommutative_int_iff E.grading).mp hE
      (f.map_grading i a a.2) (g.map_grading j b b.2),
    Units.smul_def, Int.negOnePow_def, mul_comm j i]

variable (A B : DifferentialGradedAlgebra R)

/-- The sign identity behind graded commutativity of a tensor product: the Koszul sign of the
multiplication, together with the signs of commuting the two pairs of factors, differs from the
Koszul sign of the total degrees by `(-1)^(2 p q') = 1`. -/
theorem negOnePow_tensorProduct_comm (p q p' q' : ℤ) :
    (q * p').negOnePow * (p * p').negOnePow * (q * q').negOnePow =
      ((p + q) * (p' + q')).negOnePow * (q' * p).negOnePow := by
  have key (m k : ℤ) : (m + 2 * k).negOnePow = m.negOnePow := by
    rw [Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]
  rw [← Int.negOnePow_add (q * p') (p * p'), ← Int.negOnePow_add _ (q * q'),
    ← Int.negOnePow_add ((p + q) * (p' + q')) (q' * p),
    show (p + q) * (p' + q') + q' * p = q * p' + p * p' + q * q' + 2 * (p * q') by ring,
    key]

/-- Homogeneous elements of a graded-commutative algebra commute up to the Koszul sign. -/
private theorem mul_eq_negOnePow_smul_mul {X : DifferentialGradedAlgebra R}
    (hX : DifferentialGraded.IsGradedCommutative X.grading) {p p' : ℤ} {x y : X.A}
    (hx : x ∈ X.grading p) (hy : y ∈ X.grading p') :
    x * y = (p * p').negOnePow • (y * x) := by
  simpa only [Units.smul_def] using
    (DifferentialGraded.isGradedCommutative_int_iff X.grading).mp hX hx hy

/-- Two homogeneous pure tensors commute in the tensor product up to the Koszul sign of their
total degrees, provided both factors are graded commutative. -/
theorem tmul_mul_tmul_comm (hA : DifferentialGraded.IsGradedCommutative A.grading)
    (hB : DifferentialGraded.IsGradedCommutative B.grading) (p q p' q' : ℤ)
    (a : A.grading p) (b : B.grading q) (c : A.grading p') (d : B.grading q') :
    ((a : A.A) ᵍ⊗ₜ[R] (b : B.A) : A.grading ᵍ⊗[R] B.grading) *
        ((c : A.A) ᵍ⊗ₜ[R] (d : B.A)) =
      (((p + q) * (p' + q')).negOnePow : ℤ) •
        (((c : A.A) ᵍ⊗ₜ[R] (d : B.A) : A.grading ᵍ⊗[R] B.grading) *
          ((a : A.A) ᵍ⊗ₜ[R] (b : B.A))) := by
  rw [tmul_mul A B p q p' q' a b c d, tmul_mul A B p' q' p q c d a b,
    mul_eq_negOnePow_smul_mul hA a.2 c.2, mul_eq_negOnePow_smul_mul hB b.2 d.2,
    units_smul_tmul_left, units_smul_tmul_right, smul_smul, smul_smul,
    ← Units.smul_def, smul_smul, negOnePow_tensorProduct_comm]

/-- Graded commutativity of the total grading of a tensor product, proved by a double span
induction over the homogeneous pure tensors spanning the two degrees. -/
theorem tensorProduct_mul_comm (hA : DifferentialGraded.IsGradedCommutative A.grading)
    (hB : DifferentialGraded.IsGradedCommutative B.grading) (i j : ℤ)
    (x y : A.grading ᵍ⊗[R] B.grading) (hx : x ∈ tensorProductGrading A B i)
    (hy : y ∈ tensorProductGrading A B j) :
    x * y = ((i * j).negOnePow : ℤ) • (y * x) := by
  obtain ⟨n, hn⟩ : ∃ n : ℤ, ((i * j).negOnePow : ℤ) = n := ⟨_, rfl⟩
  rw [hn]
  induction hx using Submodule.span_induction generalizing y with
  | mem x hx =>
    obtain ⟨p, q, a, b, ha, hb, hpq, rfl⟩ := hx
    subst hpq
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p', q', c, d, hc, hd, hpq', rfl⟩ := hy
      subst hpq'
      subst hn
      exact tmul_mul_tmul_comm A B hA hB p q p' q' ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩
    | zero => simp
    | add y z _ _ ihy ihz => rw [mul_add, add_mul, ihy, ihz, smul_add]
    | smul t y _ ih =>
      rw [Algebra.mul_smul_comm, ih, Algebra.smul_mul_assoc, smul_comm]
  | zero => simp
  | add x z _ _ ihx ihz => rw [add_mul, mul_add, ihx y hy, ihz y hy, smul_add]
  | smul t x _ ih =>
    rw [Algebra.smul_mul_assoc, ih y hy, Algebra.mul_smul_comm, smul_comm]

/-- The tensor product of two graded-commutative differential graded algebras is graded
commutative. This is a theorem rather than an instance, so that it is applied explicitly. -/
theorem isGradedCommutative_tensorProduct
    (hA : DifferentialGraded.IsGradedCommutative A.grading)
    (hB : DifferentialGraded.IsGradedCommutative B.grading) :
    DifferentialGraded.IsGradedCommutative (tensorProduct A B).grading := by
  rw [DifferentialGraded.isGradedCommutative_int_iff]
  intro i j x y hx hy
  exact tensorProduct_mul_comm A B hA hB i j x y hx hy

/-- The elementwise form of graded commutativity of a tensor product: homogeneous elements of
degrees `i` and `j` commute up to the Koszul sign `(-1)^(i·j)`. -/
theorem tensorProduct_mul_comm_of_mem
    (hA : DifferentialGraded.IsGradedCommutative A.grading)
    (hB : DifferentialGraded.IsGradedCommutative B.grading) {i j : ℤ}
    {x y : (tensorProduct A B).A} (hx : x ∈ (tensorProduct A B).grading i)
    (hy : y ∈ (tensorProduct A B).grading j) :
    x * y = ((i * j).negOnePow : ℤ) • (y * x) :=
  (DifferentialGraded.isGradedCommutative_int_iff (tensorProduct A B).grading).mp
    (isGradedCommutative_tensorProduct A B hA hB) hx hy

end DifferentialGradedAlgebra
