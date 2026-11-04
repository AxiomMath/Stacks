module

public import StacksFrontier.Algebra.DifferentialGraded.TensorProductLift

/-!
# The two inclusions of a tensor product of differential graded algebras

Let `A` and `B` be differential graded algebras over a commutative ring `R`. The maps
`a ↦ a ⊗ 1` and `b ↦ 1 ⊗ b` are homomorphisms of differential graded algebras into the tensor
product `A ⊗_R B` of Tag 065W, and their images Koszul-anticommute: for `a` of degree `i` and `b`
of degree `j`,
$$(a \otimes 1)(1 \otimes b) = (-1)^{ij}\,(1 \otimes b)(a \otimes 1).$$
Together with the universal property of `Koszul`'s `tensorLift` this exhibits `A ⊗_R B` as the
coproduct of `A` and `B` among differential graded algebras with Koszul-anticommuting images.

## Main definitions

* `DifferentialGradedAlgebra.tensorInclLeft` and
  `DifferentialGradedAlgebra.tensorInclRight`: the two inclusions, as homomorphisms of
  differential graded algebras.

## Main results

* `DifferentialGradedAlgebra.anticommutesAlong_tensorIncl`: the two inclusions have
  Koszul-anticommuting images.
* `DifferentialGradedAlgebra.tensorIncl_add_swap_of_mem_neg_one`: two elements of degree `-1`
  anticommute on the nose after inclusion, so the sum of the two products vanishes.

## Implementation notes

Compatibility of the left inclusion with the differentials needs the right factor to be a cycle,
which it is because the differential of a differential graded algebra kills the unit; a
decomposition into homogeneous pieces is therefore needed on the left and not on the right. The
anticommutation is read off from Mathlib's `GradedTensorProduct.tmul_coe_mul_coe_tmul`: the sign
appears once on one side and twice on the other, and the square of a sign is one.

## References

* [Stacks Project, Tag 065W](https://stacks.math.columbia.edu/tag/065W)
-/

@[expose] public noncomputable section

namespace DifferentialGradedAlgebra

universe u

open scoped TensorProduct

variable {R : Type u} [CommRing R] (A B : DifferentialGradedAlgebra.{u, u} R)

/-- The differential of a differential graded algebra kills the unit. -/
theorem d_one_eq_zero : A.d 1 = 0 := by
  have h1 : (1 : A.A) ∈ A.grading 0 := SetLike.one_mem_graded A.grading
  have h := A.leibniz 0 0 (1 : A.A) 1 h1 h1
  have h' : A.d 1 = A.d 1 + A.d 1 := by simpa using h
  have hh := congrArg (fun x : A.A => x - A.d 1) h'
  simpa using hh.symm

/-- The pure tensor `a ⊗ 0` vanishes in the graded tensor product `A ⊗_R B`. -/
theorem tmul_zero_right' (a : A.A) :
    ((a ᵍ⊗ₜ[R] (0 : B.A)) : A.grading ᵍ⊗[R] B.grading) = 0 := by
  rw [GradedTensorProduct.tmul, TensorProduct.tmul_zero, map_zero]

/-- The pure tensor `0 ⊗ b` vanishes in the graded tensor product `A ⊗_R B`. -/
theorem tmul_zero_left' (b : B.A) :
    (((0 : A.A) ᵍ⊗ₜ[R] b) : A.grading ᵍ⊗[R] B.grading) = 0 := by
  rw [GradedTensorProduct.tmul, TensorProduct.zero_tmul, map_zero]

/-- The map `a ↦ a ⊗ 1` commutes with the differentials: `d a ⊗ 1 = d (a ⊗ 1)`. -/
theorem includeLeft_map_d (a : A.A) :
    GradedTensorProduct.includeLeft A.grading B.grading (A.d a) =
      (tensorProduct A B).d (GradedTensorProduct.includeLeft A.grading B.grading a) := by
  induction a using DirectSum.Decomposition.inductionOn A.grading with
  | zero =>
      rw [map_zero, map_zero, map_zero]
  | add x y hx hy =>
      rw [map_add, map_add, map_add, map_add, hx, hy]
  | @homogeneous p x =>
      have h := tensorProductDifferential_tmul A B p x (1 : B.A)
      rw [d_one_eq_zero B, tmul_zero_right' A B, smul_zero, add_zero] at h
      exact h.symm

/-- The map `b ↦ 1 ⊗ b` commutes with the differentials: `1 ⊗ d b = d (1 ⊗ b)`. -/
theorem includeRight_map_d (b : B.A) :
    GradedTensorProduct.includeRight A.grading B.grading (B.d b) =
      (tensorProduct A B).d (GradedTensorProduct.includeRight A.grading B.grading b) := by
  have h := tensorProductDifferential_tmul A B 0 ⟨(1 : A.A), SetLike.one_mem_graded A.grading⟩ b
  rw [d_one_eq_zero A, tmul_zero_left' A B, zero_add, Int.negOnePow_zero, Units.val_one,
    one_smul] at h
  exact h.symm

/-- **The inclusion of the left factor** `A → A ⊗_R B`, `a ↦ a ⊗ 1`, as a homomorphism of
differential graded algebras. -/
def tensorInclLeft : A.Hom (tensorProduct A B) where
  toAlgebraHom := GradedTensorProduct.includeLeft A.grading B.grading
  map_grading n a ha := by
    have h := tmul_mem_grading A B n 0 a 1 ha (SetLike.one_mem_graded B.grading)
    rw [show n + 0 = n from by ring] at h
    exact h
  map_d := includeLeft_map_d A B

/-- **The inclusion of the right factor** `B → A ⊗_R B`, `b ↦ 1 ⊗ b`, as a homomorphism of
differential graded algebras. -/
def tensorInclRight : B.Hom (tensorProduct A B) where
  toAlgebraHom := GradedTensorProduct.includeRight A.grading B.grading
  map_grading n b hb := by
    have h := tmul_mem_grading A B 0 n 1 b (SetLike.one_mem_graded A.grading) hb
    rw [show (0 : ℤ) + n = n from by ring] at h
    exact h
  map_d := includeRight_map_d A B

/-- The underlying algebra homomorphism of `tensorInclLeft` is
`GradedTensorProduct.includeLeft`. -/
@[simp] theorem tensorInclLeft_toAlgebraHom :
    (tensorInclLeft A B).toAlgebraHom =
      GradedTensorProduct.includeLeft A.grading B.grading := rfl

/-- The underlying algebra homomorphism of `tensorInclRight` is
`GradedTensorProduct.includeRight`. -/
@[simp] theorem tensorInclRight_toAlgebraHom :
    (tensorInclRight A B).toAlgebraHom =
      GradedTensorProduct.includeRight A.grading B.grading := rfl

/-- **The two inclusions Koszul-anticommute.** -/
theorem anticommutesAlong_tensorIncl :
    AnticommutesAlong A B (tensorProduct A B) (tensorInclLeft A B) (tensorInclRight A B) := by
  intro i j a b
  have hleft : (tensorInclLeft A B).toAlgebraHom (a : A.A) *
      (tensorInclRight A B).toAlgebraHom (b : B.A) =
      (((a : A.A) ᵍ⊗ₜ[R] (b : B.A)) : A.grading ᵍ⊗[R] B.grading) :=
    GradedTensorProduct.tmul_one_mul_one_tmul A.grading B.grading (a : A.A) (b : B.A)
  have hright : (tensorInclRight A B).toAlgebraHom (b : B.A) *
      (tensorInclLeft A B).toAlgebraHom (a : A.A) =
      ((-1 : ℤˣ) ^ (j * i)) •
        ((((1 : A.A) * (a : A.A)) ᵍ⊗ₜ[R] ((b : B.A) * (1 : B.A))) :
          A.grading ᵍ⊗[R] B.grading) :=
    GradedTensorProduct.tmul_coe_mul_coe_tmul A.grading B.grading (1 : A.A) b a (1 : B.A)
  rw [hleft, hright, one_mul, mul_one, smul_smul]
  rw [Int.units_mul_self, one_smul]

/-- Two elements of degree `-1` anticommute on the nose after inclusion into the tensor
product. -/
theorem tensorIncl_add_swap_of_mem_neg_one {a : A.A} {b : B.A}
    (ha : a ∈ A.grading (-1)) (hb : b ∈ B.grading (-1)) :
    (tensorInclLeft A B).toAlgebraHom a * (tensorInclRight A B).toAlgebraHom b +
        (tensorInclRight A B).toAlgebraHom b * (tensorInclLeft A B).toAlgebraHom a = 0 := by
  have h := anticommutesAlong_tensorIncl A B (-1) (-1) ⟨a, ha⟩ ⟨b, hb⟩
  rw [show (-1 : ℤ) * (-1 : ℤ) = 1 from by ring, zpow_one] at h
  have h' : (tensorInclLeft A B).toAlgebraHom a * (tensorInclRight A B).toAlgebraHom b =
      -((tensorInclRight A B).toAlgebraHom b * (tensorInclLeft A B).toAlgebraHom a) := by
    rw [h, Units.smul_def, Units.val_neg, Units.val_one, neg_smul, one_smul]
  rw [h']
  abel

end DifferentialGradedAlgebra
