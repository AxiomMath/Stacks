module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleComposition
public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroAlgebra
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorBaseChangeSecondVariable
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorCounitDevissage
public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleCohomology

/-! # The map of Stacks 0BZ4 is an isomorphism over the base ring

Let `R` be a commutative ring and let `(B, d)` and `(C, d)` be differential graded `R`-algebras.
Stacks 0BZ4 is the canonical map
`(A ⊗_R B)_B ⊗_B^𝐋 {}_B(B ⊗_R C)_C ⟶ (A ⊗_R B ⊗_R C)_C` of `D(C, d)`, for a third differential
graded `R`-algebra `(A, d)`; it is the hypothesis of Stacks 0BZ5, which the source assumes rather
than proves. This file discharges it unconditionally in the case `A = R`, that is when the first
algebra is the base ring placed in degree zero with zero differential.

The reason is the one the source gives in its proof of Stacks 0BZE: for `A = R` the left-hand
factor `(R ⊗_R B)_B` is the regular right differential graded `B`-module, and the comparison from
the derived to the plain tensor product is invertible at the regular module because the regular
module is orthogonal on the left to the acyclic modules (Stacks 09K1). So no K-flatness of `C` is
needed, which is what Stacks 09S4 would ask for.

## Main definitions

* `DifferentialGraded.unitTensorDown`: the `R`-linear map `R ⊗_R B → B`, `r ⊗ b ↦ r • b`.
* `DifferentialGraded.unitBaseChangeIso`: the identification `B ≅ (R ⊗_R B)_B` of right
  differential graded `B`-modules.

## Main results

* `DifferentialGraded.isIso_derivedTensorBaseChangeComparison_degreeZeroBase`: **the map of
  Stacks 0BZ4 is an isomorphism when the first algebra is the base ring in degree zero**, hence
  the hypothesis of Stacks 0BZ5 holds for that triple with nothing assumed.
* `DifferentialGraded.Bimodule.derivedTensorFunctorCompIsoDegreeZeroBase`: **Stacks 0BZ5** for
  that triple, unconditionally.

## Implementation notes

The graded tensor product of Tag 065W has `R ⊗_R B` for its carrier as a plain tensor product of
`R`-modules, so the identification with `B` is the left unitor `R ⊗_R B ≅ B` of
`TensorProduct.lid`. What has to be checked is that it is a homomorphism of differential graded
modules. The Koszul signs are all trivial here: the first factor sits in degree zero, so the
grading of a pure tensor `r ⊗ b` is the grading of `b`, the signed differential of Tag 065W
reduces to `r ⊗ d b` because `R` carries the zero differential, and the product
`(r ⊗ b)(1 ⊗ c) = r ⊗ bc` is sign-free because `1` has degree zero.

Both differential graded algebras and their modules live in a single universe, which is the
encoding of the differential graded chapter in this tree (Tag 09JJ).

## References

* [Stacks Project, Tag 0BZ4](https://stacks.math.columbia.edu/tag/0BZ4), the canonical map.
* [Stacks Project, Tag 0BZ5](https://stacks.math.columbia.edu/tag/0BZ5), which assumes it is an
  isomorphism, and [Tag 09S4](https://stacks.math.columbia.edu/tag/09S4), which deduces that
  from K-flatness of `C`.
* [Stacks Project, Tag 09K1](https://stacks.math.columbia.edu/tag/09K1) for the left
  orthogonality of the regular module, and
  [Tag 065W](https://stacks.math.columbia.edu/tag/065W) for the graded tensor product.
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGradedModule DifferentialGradedAlgebra
open scoped TensorProduct

universe u

namespace DifferentialGraded

variable {R : Type u} [CommRing R] (B : DifferentialGradedAlgebra.{u, u} R)

/-! ### The unitor `R ⊗_R B ≅ B` -/

/-- The `R`-linear map `R ⊗_R B → B` sending `r ⊗ b` to `r • b`, where the source is the graded
tensor product of Tag 065W of the base ring in degree zero with `B`. -/
def unitTensorDown :
    ((degreeZero R R).grading ᵍ⊗[R] B.grading) →ₗ[R] B.A :=
  (TensorProduct.lid R B.A).toLinearMap ∘ₗ
    (GradedTensorProduct.of R (degreeZero R R).grading B.grading).symm.toLinearMap

/-- The map `unitTensorDown` sends the pure tensor `r ⊗ b` to `r • b`. -/
@[simp] theorem unitTensorDown_tmul (r : R) (b : B.A) :
    unitTensorDown B ((r ᵍ⊗ₜ[R] b : (degreeZero R R).grading ᵍ⊗[R] B.grading)) = r • b := rfl

/-- In `R ⊗_R B`, the pure tensor `r ⊗ b` equals `1 ⊗ (r • b)`. -/
theorem tmul_eq_one_tmul_smul (r : R) (b : B.A) :
    (r ᵍ⊗ₜ[R] b : (degreeZero R R).grading ᵍ⊗[R] B.grading) =
      ((1 : R) ᵍ⊗ₜ[R] (r • b)) := by
  change (GradedTensorProduct.of R _ _) (r ⊗ₜ[R] b) =
    (GradedTensorProduct.of R _ _) ((1 : R) ⊗ₜ[R] (r • b))
  congr 1
  rw [← TensorProduct.smul_tmul, smul_eq_mul, mul_one]

/-- The product of a pure tensor with `1 ⊗ c` is sign-free: the second factor of `1 ⊗ c` meets
the first factor `1` of degree zero. -/
theorem tmul_mul_one_tmul (r : R) (b c : B.A) :
    ((r ᵍ⊗ₜ[R] b : (degreeZero R R).grading ᵍ⊗[R] B.grading) * ((1 : R) ᵍ⊗ₜ[R] c)) =
      (r ᵍ⊗ₜ[R] (b * c)) := by
  calc (r ᵍ⊗ₜ[R] b : (degreeZero R R).grading ᵍ⊗[R] B.grading) * ((1 : R) ᵍ⊗ₜ[R] c)
      = ((r ᵍ⊗ₜ[R] (1 : B.A)) * ((1 : R) ᵍ⊗ₜ[R] b)) * ((1 : R) ᵍ⊗ₜ[R] c) := by
        rw [GradedTensorProduct.tmul_one_mul_one_tmul]
    _ = (r ᵍ⊗ₜ[R] (1 : B.A)) * (((1 : R) ᵍ⊗ₜ[R] b) * ((1 : R) ᵍ⊗ₜ[R] c)) := mul_assoc _ _ _
    _ = (r ᵍ⊗ₜ[R] (1 : B.A)) * ((1 : R) ᵍ⊗ₜ[R] (b * c)) := congrArg (_ * ·)
        (map_mul (GradedTensorProduct.includeRight (degreeZero R R).grading B.grading) b c).symm
    _ = (r ᵍ⊗ₜ[R] (b * c)) :=
        GradedTensorProduct.tmul_one_mul_one_tmul _ _ r (b * c)

/-- The unitor is right `B`-linear. -/
theorem unitTensorDown_mul_one_tmul (a : B.A)
    (x : (degreeZero R R).grading ᵍ⊗[R] B.grading) :
    unitTensorDown B (x * ((1 : R) ᵍ⊗ₜ[R] a)) = unitTensorDown B x * a := by
  induction x using gradedTensor_induction with
  | tmul r b =>
    rw [tmul_mul_one_tmul, unitTensorDown_tmul, unitTensorDown_tmul, smul_mul_assoc]
  | add z w hz hw => rw [add_mul, map_add, map_add, add_mul, hz, hw]

/-- The unitor preserves the grading: the degree-`n` part of `R ⊗_R B` is spanned by the pure
tensors `r ⊗ b` with `b` of degree `n`, the base ring being concentrated in degree zero. -/
theorem unitTensorDown_mem_grading (n : ℤ)
    (x : (degreeZero R R).grading ᵍ⊗[R] B.grading)
    (hx : x ∈ ((degreeZero R R).tensorProduct B).grading n) :
    unitTensorDown B x ∈ B.grading n := by
  have hle : tensorProductGrading (degreeZero R R) B n ≤
      Submodule.comap (unitTensorDown B) (B.grading n) := by
    refine Submodule.span_le.2 ?_
    rintro z ⟨p, q, a, b, ha, hb, hpq, rfl⟩
    have key : unitTensorDown B
        ((a ᵍ⊗ₜ[R] b : (degreeZero R R).grading ᵍ⊗[R] B.grading)) ∈ B.grading n := by
      rcases eq_or_ne p 0 with rfl | hp
      · obtain rfl : q = n := by omega
        rw [unitTensorDown_tmul]
        exact (B.grading _).smul_mem a hb
      · obtain rfl : a = 0 := by
          have ha' : a ∈ degreeZeroGrading R R p := ha
          rw [degreeZeroGrading_eq_bot R R hp] at ha'
          simpa using ha'
        have hz : ((0 : R) ᵍ⊗ₜ[R] b : (degreeZero R R).grading ᵍ⊗[R] B.grading) = 0 := by
          change (GradedTensorProduct.of R _ _) ((0 : R) ⊗ₜ[R] b) = 0
          rw [TensorProduct.zero_tmul, map_zero]
        rw [hz, map_zero]
        exact (B.grading n).zero_mem
    exact key
  exact hle hx

/-- The unitor commutes with the differentials: the signed differential of Tag 065W on `R ⊗_R B`
reduces to `r ⊗ d b`, because the base ring in degree zero carries the zero differential and the
Koszul sign in degree zero is trivial. -/
theorem unitTensorDown_d (x : (degreeZero R R).grading ᵍ⊗[R] B.grading) :
    unitTensorDown B (((degreeZero R R).tensorProduct B).d x) =
      B.d (unitTensorDown B x) := by
  induction x using gradedTensor_induction with
  | tmul r b =>
    have hr : r ∈ (degreeZero R R).grading 0 := by
      change r ∈ degreeZeroGrading R R 0
      rw [degreeZeroGrading_zero R R]
      exact Submodule.mem_top
    have hd : ((degreeZero R R).d (⟨r, hr⟩ : (degreeZero R R).grading 0) : R) = 0 := rfl
    have hz : ((0 : R) ᵍ⊗ₜ[R] b : (degreeZero R R).grading ᵍ⊗[R] B.grading) = 0 := by
      change (GradedTensorProduct.of R _ _) ((0 : R) ⊗ₜ[R] b) = 0
      rw [TensorProduct.zero_tmul, map_zero]
    rw [tensorProductDifferential_tmul (degreeZero R R) B 0 ⟨r, hr⟩ b, hd, hz, zero_add,
      Int.negOnePow_zero, Units.val_one, one_smul, unitTensorDown_tmul, unitTensorDown_tmul,
      map_smul]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- Tensoring on the left with `1` undoes the unitor. -/
theorem one_tmul_unitTensorDown (x : (degreeZero R R).grading ᵍ⊗[R] B.grading) :
    ((1 : R) ᵍ⊗ₜ[R] unitTensorDown B x :
      (degreeZero R R).grading ᵍ⊗[R] B.grading) = x := by
  have hadd : ∀ y z : B.A,
      ((1 : R) ᵍ⊗ₜ[R] (y + z) : (degreeZero R R).grading ᵍ⊗[R] B.grading) =
        ((1 : R) ᵍ⊗ₜ[R] y) + ((1 : R) ᵍ⊗ₜ[R] z) :=
    fun y z =>
      map_add (GradedTensorProduct.includeRight (degreeZero R R).grading B.grading) y z
  induction x using gradedTensor_induction with
  | tmul r b => rw [unitTensorDown_tmul, ← tmul_eq_one_tmul_smul]
  | add z w hz hw => rw [map_add, hadd, hz, hw]

/-! ### The identification of the regular module with `(R ⊗_R B)_B` -/

/-- `b ↦ 1 ⊗ b`, as a homomorphism of right differential graded `B`-modules from the regular
module to `(R ⊗_R B)_B`. -/
def unitBaseChangeHom :
    regularModule B ⟶ baseChangeModule (degreeZero R R) B where
  toFun := (tensorIncludeRightHom (degreeZero R R) B).toAlgebraHom.toLinearMap
  map_smul x a :=
    show (tensorIncludeRightHom (degreeZero R R) B).toAlgebraHom (x * a) =
        (tensorIncludeRightHom (degreeZero R R) B).toAlgebraHom x *
          (tensorIncludeRightHom (degreeZero R R) B).toAlgebraHom a from
      map_mul _ x a
  map_grading n x hx := (tensorIncludeRightHom (degreeZero R R) B).map_grading n x hx
  map_d := by
    ext x
    exact (tensorIncludeRightHom (degreeZero R R) B).map_d x

/-- `r ⊗ b ↦ r • b`, as a homomorphism of right differential graded `B`-modules from
`(R ⊗_R B)_B` to the regular module. -/
def unitBaseChangeInv :
    baseChangeModule (degreeZero R R) B ⟶ regularModule B where
  toFun := unitTensorDown B
  map_smul x a := unitTensorDown_mul_one_tmul B a x
  map_grading := unitTensorDown_mem_grading B
  map_d := by
    ext x
    exact unitTensorDown_d B x

/-- **The regular right differential graded `B`-module is `(R ⊗_R B)_B`**, the base-change module
of Tag 0BZ4 for the base ring in degree zero. -/
def unitBaseChangeIso :
    regularModule B ≅ baseChangeModule (degreeZero R R) B where
  hom := unitBaseChangeHom B
  inv := unitBaseChangeInv B
  hom_inv_id :=
    DifferentialGradedModule.Hom.ext (LinearMap.ext fun b =>
      show unitTensorDown B ((1 : R) ᵍ⊗ₜ[R] b) = b by rw [unitTensorDown_tmul, one_smul])
  inv_hom_id :=
    DifferentialGradedModule.Hom.ext (LinearMap.ext fun x =>
      one_tmul_unitTensorDown B x)

/-! ### Stacks 0BZ4 and Stacks 0BZ5 over the base ring -/

/-- **The canonical map of Stacks 0BZ4 is an isomorphism when the first algebra is the base ring
in degree zero.** For differential graded `R`-algebras `(B, d)` and `(C, d)`, the map
`(R ⊗_R B)_B ⊗_B^𝐋 {}_B(B ⊗_R C)_C ⟶ (R ⊗_R B ⊗_R C)_C` of `D(C, d)` is invertible, with nothing
assumed about `B` or `C`.

By `DifferentialGraded.Bimodule.isIso_derivedTensorBaseChangeComparison_iff` the assertion is
that the comparison of Tag 09LS from the derived to the plain tensor product with
`{}_B(B ⊗_R C)_C` is invertible at the right differential graded `B`-module `(R ⊗_R B)_B`. That
module is the regular module, by `DifferentialGraded.unitBaseChangeIso`, and the regular module
is orthogonal on the left to the acyclic modules by Tag 09K1, where the plain tensor product
already computes the derived one.

This is the hypothesis that Stacks 0BZ5 assumes and that Stacks 09S4 discharges from K-flatness
of `C`; over the base ring no K-flatness is needed. -/
@[stacks 0BZ4 "the canonical map is an isomorphism when the first algebra is the base ring in \
degree zero"]
theorem isIso_derivedTensorBaseChangeComparison_degreeZeroBase
    (C : DifferentialGradedAlgebra.{u, u} R) :
    IsIso (derivedTensorBaseChangeComparison (degreeZero R R) B C) := by
  rw [Bimodule.isIso_derivedTensorBaseChangeComparison_iff]
  exact Bimodule.isIso_derivedTensorFunctorCounit_app_of_iso (baseChangeBimodule B C)
    (unitBaseChangeIso B)
    (Bimodule.isIso_derivedTensorFunctorCounit_app_of_leftOrthogonal
      (baseChangeBimodule B C) _
      (leftOrthogonal_acyclic_toHomotopyCategory_regularModule B))

namespace Bimodule

/-- **Stacks 0BZ5 when the first algebra is the base ring in degree zero**, with nothing assumed.
For a differential graded `R`-algebra `(C, d)`, a differential graded `(R, B)`-bimodule `N` and a
differential graded `(B, C)`-bimodule `N'`, the composite of `- ⊗_R^𝐋 N : D(R) ⥤ D(B, d)` and
`- ⊗_B^𝐋 N' : D(B, d) ⥤ D(C, d)` is the derived tensor functor of the differential graded
`(R, C)`-bimodule `N'' = Ñ ⊗_B Ñ'` of Stacks 0BZ3.

This is `DifferentialGraded.Bimodule.derivedTensorFunctorCompIsoOfBaseChange` with its only
hypothesis — the map of Tag 0BZ4, which Stacks 0BZ5 assumes to be an isomorphism — supplied by
`DifferentialGraded.isIso_derivedTensorBaseChangeComparison_degreeZeroBase`. Here `D(R)` is the
derived category of the base ring viewed as a differential graded algebra concentrated in degree
zero, which is the derived category of `R`-modules by
`DifferentialGradedModule.degreeZeroDerivedEquivalence`. -/
@[stacks 0BZ5 "unconditionally when the first algebra is the base ring in degree zero"]
def derivedTensorFunctorCompIsoDegreeZeroBase
    (C : DifferentialGradedAlgebra.{u, u} R)
    (N : Bimodule (degreeZero R R) B) (N' : Bimodule B C) :
    derivedTensorFunctor N ⋙ derivedTensorFunctor N' ≅
      derivedTensorFunctor (compTensorResolution N N') :=
  derivedTensorFunctorCompIsoOfBaseChange (degreeZero R R) B C
    (isIso_derivedTensorBaseChangeComparison_degreeZeroBase B C) N N'

end Bimodule

end DifferentialGraded

end
