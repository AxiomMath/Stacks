module

public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleTotalization
public import StacksFrontier.Algebra.DifferentialGraded.Module.Restriction

/-!
# The two inclusions into a graded tensor product of differential graded algebras

For differential graded algebras `C` and `D` over a commutative ring `R`, the two inclusions
`c ↦ c ⊗ 1` and `d ↦ 1 ⊗ d` into the graded tensor product `C ⊗ D` are homomorphisms of
differential graded algebras. Restricting a right differential graded `C ⊗ D`-module along them
gives its underlying right `C`-module and right `D`-module, and the two actions anticommute by the
Koszul sign, which is the defining relation of the graded tensor product.

## Main definitions

* `DifferentialGradedAlgebra.tensorIncludeLeftHom` and
  `DifferentialGradedAlgebra.tensorIncludeRightHom`: the two inclusions, as homomorphisms of
  differential graded algebras.
* `DifferentialGradedModule.tensorRestrictLeft`, `DifferentialGradedModule.tensorRestrictRight`:
  the restrictions of a right `C ⊗ D`-module along them.

## Main results

* `DifferentialGradedAlgebra.includeRight_mul_includeLeft` and
  `DifferentialGradedAlgebra.op_includeLeft_mul_op_includeRight`: the two inclusions commute up to
  the Koszul sign, in the algebra and in its opposite.
* `DifferentialGradedAlgebra.op_includeLeft_smul_op_includeRight_smul`: the same statement for the
  actions on a right `C ⊗ D`-module.

## References

* [Stacks Project, Tag 0FQJ](https://stacks.math.columbia.edu/tag/0FQJ)
-/

@[expose] public section

open scoped TensorProduct

universe u

variable {R : Type u} [CommRing R]

namespace DifferentialGradedAlgebra

variable (C : DifferentialGradedAlgebra R) (D : DifferentialGradedAlgebra R)

/-- The inclusion `c ↦ c ⊗ 1` of `C` into the graded tensor product, as a homomorphism of
differential graded algebras. -/
noncomputable def tensorIncludeLeftHom : C.Hom (tensorProduct C D) where
  toAlgebraHom := GradedTensorProduct.includeLeft C.grading D.grading
  map_grading := by
    intro n a ha
    change (a ᵍ⊗ₜ[R] (1 : D.A)) ∈ (tensorProduct C D).grading n
    convert tmul_mem_grading C D n 0 a 1 ha (SetLike.one_mem_graded D.grading) using 1
    simp
  map_d := by
    intro a
    induction a using DirectSum.Decomposition.inductionOn C.grading with
    | zero => simp
    | add a b ha hb => simp [ha, hb]
    | @homogeneous n a =>
      change (C.d a : C.A) ᵍ⊗ₜ[R] (1 : D.A) =
        (tensorProduct C D).d ((a : C.A) ᵍ⊗ₜ[R] (1 : D.A))
      rw [tensorProductDifferential_tmul C D n a 1]
      simp [d_one D]

/-- The inclusion `d ↦ 1 ⊗ d` of `D` into the graded tensor product, as a homomorphism of
differential graded algebras. -/
noncomputable def tensorIncludeRightHom : D.Hom (tensorProduct C D) where
  toAlgebraHom := (GradedTensorProduct.includeRight C.grading D.grading :
    D.A →ₐ[R] (tensorProduct C D).A)
  map_grading := by
    intro n b hb
    have hb' : (GradedTensorProduct.includeRight C.grading D.grading) b =
        (1 : C.A) ᵍ⊗ₜ[R] (b : D.A) := rfl
    rw [hb']
    simpa only [zero_add] using
      tmul_mem_grading C D 0 n (1 : C.A) b (SetLike.one_mem_graded C.grading) hb
  map_d := by
    intro b
    induction b using DirectSum.Decomposition.inductionOn D.grading with
    | zero => simp
    | add b c hb hc => simp [hb, hc]
    | @homogeneous n b =>
      change (GradedTensorProduct.includeRight C.grading D.grading) (D.d b) =
        (tensorProduct C D).d ((GradedTensorProduct.includeRight C.grading D.grading) b)
      have hdb : (GradedTensorProduct.includeRight C.grading D.grading) (D.d b) =
          (1 : C.A) ᵍ⊗ₜ[R] (D.d b : D.A) := rfl
      have hb : (GradedTensorProduct.includeRight C.grading D.grading) b =
          (1 : C.A) ᵍ⊗ₜ[R] (b : D.A) := rfl
      rw [hdb, hb]
      simpa [d_one C, GradedTensorProduct.tmul] using
        (tensorProductDifferential_tmul C D 0 ⟨1, SetLike.one_mem_graded C.grading⟩ b).symm

/-- A pure tensor, in the opposite algebra, is the product of the two inclusions. -/
theorem op_tmul_eq_includeRight_mul_includeLeft (a : C.A) (b : D.A) :
    MulOpposite.op (a ᵍ⊗ₜ[R] b : (tensorProduct C D).A) =
      MulOpposite.op (GradedTensorProduct.includeRight C.grading D.grading b) *
        MulOpposite.op (GradedTensorProduct.includeLeft C.grading D.grading a) := by
  rw [← MulOpposite.op_mul]
  congr 1
  exact (GradedTensorProduct.tmul_one_mul_one_tmul C.grading D.grading a b).symm

/-- The two inclusions commute up to the Koszul sign. -/
theorem includeRight_mul_includeLeft {m n : ℤ} (a : C.grading m) (b : D.grading n) :
    GradedTensorProduct.includeRight C.grading D.grading (b : D.A) *
        GradedTensorProduct.includeLeft C.grading D.grading (a : C.A) =
      (-1 : ℤˣ) ^ (n * m) •
        (GradedTensorProduct.includeLeft C.grading D.grading (a : C.A) *
          GradedTensorProduct.includeRight C.grading D.grading (b : D.A)) := by
  change ((1 : C.A) ᵍ⊗ₜ[R] (b : D.A)) * ((a : C.A) ᵍ⊗ₜ[R] (1 : D.A)) =
    (-1 : ℤˣ) ^ (n * m) •
      (((a : C.A) ᵍ⊗ₜ[R] (1 : D.A)) * ((1 : C.A) ᵍ⊗ₜ[R] (b : D.A)))
  rw [GradedTensorProduct.tmul_coe_mul_coe_tmul C.grading D.grading
    (1 : C.A) ⟨b, b.property⟩ ⟨a, a.property⟩ (1 : D.A),
    GradedTensorProduct.tmul_one_mul_one_tmul C.grading D.grading]
  simp

/-- In the opposite algebra, the two inclusions commute up to the Koszul sign. -/
theorem op_includeLeft_mul_op_includeRight {m n : ℤ} (a : C.grading m) (b : D.grading n) :
    (MulOpposite.op (GradedTensorProduct.includeLeft C.grading D.grading (a : C.A)) :
        MulOpposite (C.grading ᵍ⊗[R] D.grading)) *
        MulOpposite.op (GradedTensorProduct.includeRight C.grading D.grading (b : D.A)) =
      (-1 : ℤˣ) ^ (m * n) •
        (MulOpposite.op (GradedTensorProduct.includeRight C.grading D.grading (b : D.A)) *
          MulOpposite.op (GradedTensorProduct.includeLeft C.grading D.grading (a : C.A))) := by
  change MulOpposite.op
      (GradedTensorProduct.includeRight C.grading D.grading (b : D.A) *
        GradedTensorProduct.includeLeft C.grading D.grading (a : C.A)) = _
  rw [includeRight_mul_includeLeft C D a b]
  simp [mul_comm]

/-- The two inclusions act on a right module over the graded tensor product in either order, up to
the Koszul sign. -/
theorem op_includeLeft_smul_op_includeRight_smul {X : Type*} [AddCommGroup X] [Module R X]
    [Module (MulOpposite (C.grading ᵍ⊗[R] D.grading)) X]
    [IsScalarTower R (MulOpposite (C.grading ᵍ⊗[R] D.grading)) X]
    {m n : ℤ} (a : C.grading m) (b : D.grading n) (x : X) :
    (MulOpposite.op (GradedTensorProduct.includeLeft C.grading D.grading (a : C.A))) •
      ((MulOpposite.op (GradedTensorProduct.includeRight C.grading D.grading (b : D.A))) • x) =
      (m * n).negOnePow •
        ((MulOpposite.op (GradedTensorProduct.includeRight C.grading D.grading (b : D.A))) •
          ((MulOpposite.op
            (GradedTensorProduct.includeLeft C.grading D.grading (a : C.A))) • x)) := by
  calc
    _ = (MulOpposite.op (GradedTensorProduct.includeLeft C.grading D.grading (a : C.A)) *
        MulOpposite.op
          (GradedTensorProduct.includeRight C.grading D.grading (b : D.A))) • x := by
      rw [mul_smul]
    _ = ((-1 : ℤˣ) ^ (m * n) •
        (MulOpposite.op (GradedTensorProduct.includeRight C.grading D.grading (b : D.A)) *
          MulOpposite.op
            (GradedTensorProduct.includeLeft C.grading D.grading (a : C.A)))) • x := by
      rw [op_includeLeft_mul_op_includeRight C D a b]
    _ = _ := by
      simpa only [mul_smul] using DifferentialGraded.units_negOnePow_smul_assoc (R := R)
        (S := MulOpposite (C.grading ᵍ⊗[R] D.grading)) (X := X) (m * n)
        (MulOpposite.op (GradedTensorProduct.includeRight C.grading D.grading (b : D.A)) *
          MulOpposite.op (GradedTensorProduct.includeLeft C.grading D.grading (a : C.A))) x

end DifferentialGradedAlgebra

namespace DifferentialGradedModule

variable (C : DifferentialGradedAlgebra R) (D : DifferentialGradedAlgebra R)

/-- A right differential graded module over the graded tensor product, regarded as a right
`C`-module along the left inclusion. -/
noncomputable abbrev tensorRestrictLeft
    (N : DifferentialGradedModule (DifferentialGradedAlgebra.tensorProduct C D)) :
    DifferentialGradedModule C :=
  restrictScalars (DifferentialGradedAlgebra.tensorIncludeLeftHom C D) N

/-- A right differential graded module over the graded tensor product, regarded as a right
`D`-module along the right inclusion. -/
noncomputable abbrev tensorRestrictRight
    (N : DifferentialGradedModule (DifferentialGradedAlgebra.tensorProduct C D)) :
    DifferentialGradedModule D :=
  restrictScalars (DifferentialGradedAlgebra.tensorIncludeRightHom C D) N

end DifferentialGradedModule
