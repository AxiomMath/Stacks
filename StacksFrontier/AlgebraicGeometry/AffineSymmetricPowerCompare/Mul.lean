module

public import StacksFrontier.AlgebraicGeometry.AffineSymmetricPowerCompare.Basic

/-!
# The affine symmetric-power comparison on products with a degree-one generator

**This file identifies `Stacks.SymGraded.tildeSymmetricPowerIso` in degree `n + 1` with
multiplication by a degree-one sheaf generator.** Together with the degree-one normalization of
`StacksFrontier.AlgebraicGeometry.AffineSymmetricPowerCompare.Basic` this fixes the comparison in
every degree, since the degree-`n` piece of a symmetric algebra is generated, locally and up to
scalars, by products of `n` degree-one generators.

## Main results

* `Stacks.SymGraded.symAlgebra_mul_toOpen`: the multiplication of `symAlgebra M` on two global
  sections in the image of `ModuleCat.tilde.toOpen` is the image of their algebraic product.
* `Stacks.SymGraded.tildeSymmetricPowerIso_mul_generator`: the comparison in degree `n + 1`
  carries multiplication by an algebraic degree-one generator to multiplication by the
  corresponding sheaf generator.

## Implementation notes

The statement is heterogeneous because the two sides live in two degrees that are equal in `ℤ`
but not definitionally: the left side is in degree `((n + 1 : ℕ) : ℤ)` and the right side, being
a product of a degree-one and a degree-`n` section, is in degree `1 + (n : ℤ)`. The two
congruence lemmas `Stacks.SymGraded.heq_app_of_degree_eq` and
`Stacks.SymGraded.heq_toOpenₗ_of_degree_eq` discharge that: each substitutes the degree equality
and then compares the two sides as elements of one type. The content of the proof is therefore
entirely `SheafOfModules.GradedAlgebra.IsUniversal.pieceIso_mul` — the canonical comparison of
two symmetric algebras is multiplicative — plus the computation of the multiplication of
`symAlgebra M` on comparison images.

No rewrite is performed on the heterogeneous goal itself. The right-hand side is brought to the
shape `pieceIso` produces by a separate homogeneous equation, and the two are joined with
`HEq.trans`; rewriting under `HEq` across these degrees is what forces the motive to be
ill-typed.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct

universe u

namespace Stacks.SymGraded

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

/-- **A degreewise family of morphisms respects heterogeneous equality across a degree
equality.** -/
theorem heq_app_of_degree_eq
    {P Q : ℤ → SheafOfModules.{u} (Spec R).ringCatSheaf}
    (F : ∀ d : ℤ, P d ⟶ Q d) (U : ((Spec R).Opens)ᵒᵖ) {d e : ℤ} (hde : d = e)
    {x : (P d).val.obj U} {y : (P e).val.obj U} (h : HEq x y) :
    HEq ((F d).val.app U x) ((F e).val.app U y) := by
  subst hde
  exact heq_of_eq (congrArg (ConcreteCategory.hom ((F d).val.app U)) (eq_of_heq h))

/-- **Two global sections of the associated sheaves of two graded pieces of equal degree are
heterogeneously equal as soon as the underlying elements of the symmetric algebra agree.** -/
theorem heq_toOpenₗ_of_degree_eq (U : (Spec R).Opens) {d e : ℤ} (hde : d = e)
    {z : gradedPiece (R := R) M d} {w : gradedPiece (R := R) M e}
    (h : (z : SymmetricAlgebra R M) = (w : SymmetricAlgebra R M)) :
    HEq (AffineBaseChange.toOpenₗ (pieceModule M d) U z)
      (AffineBaseChange.toOpenₗ (pieceModule M e) U w) := by
  subst hde
  exact heq_of_eq (congrArg (AffineBaseChange.toOpenₗ (pieceModule M d) U) (Subtype.ext h))

/-- **The multiplication of `symAlgebra M` on sections in the image of
`ModuleCat.tilde.toOpen`** is the image of the algebraic product. -/
theorem symAlgebra_mul_toOpen (U : ((Spec R).Opens)ᵒᵖ) (i j : ℤ)
    (z : gradedPiece (R := R) M i) (w : gradedPiece (R := R) M j) :
    ((symAlgebra M).mul i j).app U
        (AffineBaseChange.toOpenₗ (pieceModule M i) U.unop z)
        (AffineBaseChange.toOpenₗ (pieceModule M j) U.unop w) =
      AffineBaseChange.toOpenₗ (pieceModule M (i + j)) U.unop (symMulₗ (R := R) M i j z w) := by
  have h := symAlgebra_mul_toTilde M i j U
    ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] z) ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] w)
  rw [AffineBaseChange.toTilde_app, AffineBaseChange.toTildeₗ_tmul, one_smul,
    AffineBaseChange.toTilde_app, AffineBaseChange.toTildeₗ_tmul, one_smul,
    AffineBaseChange.toTilde_app, mulSec_tmul, _root_.one_mul (1 : Γ(Spec R, U.unop)),
    AffineBaseChange.toTildeₗ_tmul, one_smul] at h
  exact h

variable (A : SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥(Spec R)) (tilde M))

/-- **The comparison in degree `n + 1` takes multiplication by an algebraic degree-one generator
to multiplication by the corresponding sheaf generator.** Together with the degree-one
normalization this fixes the canonical comparison in every degree. -/
@[stacks 01I8 "symmetric_power"]
theorem tildeSymmetricPowerIso_mul_generator (n : ℕ) (m : M)
    (x : SymPow.symmetricPower n R M) :
    HEq
      ((((tilde.adjunction (R := R)).homEquiv
        (ModuleCat.of R (SymPow.symmetricPower (n + 1) R M))
        (A.symmetricPower (n + 1)))
        (tildeSymmetricPowerIso M A (n + 1)).hom).hom
          (SymPow.symMulMap n (LinearMap.id : M →ₗ[R] M) (m ⊗ₜ[R] x)))
      ((A.symmetric.mul 1 (n : ℤ)).app (.op (⊤ : Opens (Spec R).carrier))
        (A.symmetricGenerator.val.app (.op (⊤ : Opens (Spec R).carrier))
          ((tilde.toOpen M ⊤).hom m))
        ((tildeSymmetricPowerIso M A n).hom.val.app (.op (⊤ : Opens (Spec R).carrier))
          ((tilde.toOpen (ModuleCat.of R (SymPow.symmetricPower n R M)) ⊤).hom x))) := by
  have hd : ((n + 1 : ℕ) : ℤ) = 1 + (n : ℤ) := by push_cast; ring
  change HEq (((isSymmetricAlgebra M).pieceIso A.symmetric_isSymmetricAlgebra
        ((n + 1 : ℕ) : ℤ)).hom.val.app (op (⊤ : Opens (Spec R).carrier))
      (AffineBaseChange.toOpenₗ (pieceModule M ((n + 1 : ℕ) : ℤ)) ⊤
        (SymPow.symMulMap n (LinearMap.id : M →ₗ[R] M) (m ⊗ₜ[R] x))))
    ((A.symmetric.mul 1 (n : ℤ)).app (op (⊤ : Opens (Spec R).carrier))
      (A.symmetricGenerator.val.app (op (⊤ : Opens (Spec R).carrier))
        ((tilde.toOpen M ⊤).hom m))
      (((isSymmetricAlgebra M).pieceIso A.symmetric_isSymmetricAlgebra (n : ℤ)).hom.val.app
        (op (⊤ : Opens (Spec R).carrier))
        (AffineBaseChange.toOpenₗ (pieceModule M (n : ℤ)) ⊤ x)))
  have hmul := SheafOfModules.GradedAlgebra.IsUniversal.pieceIso_mul
    (isSymmetricAlgebra M) A.symmetric_isSymmetricAlgebra 1 (n : ℤ)
    (op (⊤ : Opens (Spec R).carrier))
    (AffineBaseChange.toOpenₗ (pieceModule M 1) ⊤ (ιG (R := R) M m))
    (AffineBaseChange.toOpenₗ (pieceModule M (n : ℤ)) ⊤ x)
  rw [symAlgebra_mul_toOpen M (op ⊤) 1 (n : ℤ) (ιG (R := R) M m) x] at hmul
  have hrhs : (A.symmetric.mul 1 (n : ℤ)).app (op (⊤ : Opens (Spec R).carrier))
        (A.symmetricGenerator.val.app (op (⊤ : Opens (Spec R).carrier))
          ((tilde.toOpen M ⊤).hom m))
        (((isSymmetricAlgebra M).pieceIso A.symmetric_isSymmetricAlgebra (n : ℤ)).hom.val.app
          (op (⊤ : Opens (Spec R).carrier))
          (AffineBaseChange.toOpenₗ (pieceModule M (n : ℤ)) ⊤ x)) =
      ((isSymmetricAlgebra M).pieceIso A.symmetric_isSymmetricAlgebra
          (1 + (n : ℤ))).hom.val.app (op (⊤ : Opens (Spec R).carrier))
        (AffineBaseChange.toOpenₗ (pieceModule M (1 + (n : ℤ))) ⊤
          (symMulₗ (R := R) M 1 (n : ℤ) (ιG (R := R) M m) x)) :=
    (congrArg (fun z : (A.symmetric.piece 1).val.obj (op (⊤ : Opens (Spec R).carrier)) =>
        (A.symmetric.mul 1 (n : ℤ)).app (op (⊤ : Opens (Spec R).carrier)) z
          (((isSymmetricAlgebra M).pieceIso A.symmetric_isSymmetricAlgebra (n : ℤ)).hom.val.app
            (op (⊤ : Opens (Spec R).carrier))
            (AffineBaseChange.toOpenₗ (pieceModule M (n : ℤ)) ⊤ x)))
      (pieceIso_toOpen_ιG M A ⊤ m).symm).trans hmul.symm
  exact HEq.trans
    (heq_app_of_degree_eq (fun d => ((isSymmetricAlgebra M).pieceIso
        A.symmetric_isSymmetricAlgebra d).hom) (op ⊤) hd
      (heq_toOpenₗ_of_degree_eq M ⊤ hd rfl))
    (heq_of_eq hrhs.symm)

end Stacks.SymGraded
