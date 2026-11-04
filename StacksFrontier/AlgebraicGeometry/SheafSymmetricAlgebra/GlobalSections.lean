module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraGrading
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Affine

/-!
# The graded ring of global sections of the symmetric algebra on an affine base

Let `R` be a commutative ring and `M` an `R`-module. `Stacks.SymGraded.symSheafGradedAlgebra M`
is `Sym(M~)` as the input of the relative `Proj` construction on `Spec R`. **This file identifies
its graded ring of global sections with `Sym_R(M)` itself**, as graded rings.

## Main definitions

* `Stacks.SymGraded.globalPieceEquiv`: the degreewise comparison
  `Sym^n_R(M) ≃ₗ[R] Γ(Sym(M~)ₙ, ⊤)`.
* `Stacks.SymGraded.globalSectionsRingEquiv`: **`Sym_R(M) ≃+* Γ(Sym(M~), ⊤)`.**

## Main results

* `Stacks.SymGraded.globalPieceEquiv_one` and `Stacks.SymGraded.globalPieceEquiv_mul`: the
  degreewise comparison takes the unit to the unit and the graded multiplication of `Sym_R(M)`
  to the multiplication of the sheaf of graded algebras.

## Implementation notes

The degree-`n` piece of `symSheafGradedAlgebra M` is the associated sheaf of `Sym^n_R(M)` **on
the nose** (`Stacks.SymGraded.symSheafGradedAlgebra_piece_natCast`), so the degreewise comparison
is nothing but `AlgebraicGeometry.tilde.toOpen` at the top open, which is an isomorphism by
Mathlib's `AlgebraicGeometry.tilde.isIso_toOpen_top`. No symmetric-power comparison is
interposed and none is needed.

Multiplicativity is likewise direct, with no induction over the symmetric algebra. The
multiplication of `Stacks.SymGraded.symAlgebra` is the base change of the graded multiplication
`Stacks.SymGraded.symMulₗ` of `Sym_R(M)` along `R ⟶ Γ(Spec R, U)`, and
`Stacks.SymGraded.mulSec_tmul` computes it on *pure tensors*; the global section attached to
`x : Sym^n_R(M)` is the comparison image of the pure tensor `1 ⊗ x`, so one rewrite with
`Stacks.SymGraded.symAlgebra_mul_toTilde` and one with `mulSec_tmul` finish it.

**Degrees.** `Stacks.SymGraded.gradedPiece M (n : ℤ)` is `SymPow.symmetricPower n R M` by `rfl`,
and `(↑i + ↑j : ℤ)` reduces to `↑(i + j)` because `Int.add` on two `Int.ofNat` arguments is
`Int.ofNat` of the sum. So no degree transport is needed anywhere below, which is why these
statements are homogeneous equalities and not `HEq`s.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.SheafSymmetricAlgebra
open scoped TensorProduct DirectSum

namespace Stacks.SymGraded

universe u

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

/-! ### The degreewise comparison -/

/-- The global section of the degree-`n` piece of `Sym(M~)` attached to a degree-`n` element of
`Sym_R(M)`: the image of the pure tensor `1 ⊗ x` under the comparison with the associated
sheaf, which is `AlgebraicGeometry.tilde.toOpen` at the top open. -/
theorem pieceCmp_top_one_tmul (n : ℤ) (x : gradedPiece (R := R) M n) :
    PresheafOfModules.Hom.app (pieceCmp M n) (op (⊤ : (Spec R).Opens))
        ((1 : Γ(Spec R, (⊤ : (Spec R).Opens))) ⊗ₜ[R] x) =
      AffineBaseChange.toOpenₗ (pieceModule M n) ⊤ x := by
  rw [AffineBaseChange.toTilde_app, AffineBaseChange.toTildeₗ_tmul, one_smul]

/-- **The unit of `Sym_R(M)` is the unit of `Sym(M~)` on global sections.** -/
theorem toOpenₗ_oneG :
    AffineBaseChange.toOpenₗ (pieceModule M 0) ⊤ (oneG (R := R) M) =
      (symAlgebra M).one.eval (op (⊤ : (Spec R).Opens)) := by
  rw [← pieceCmp_top_one_tmul]
  exact (symAlgebra_one_eval M (op (⊤ : (Spec R).Opens))).symm

/-- **The graded multiplication of `Sym_R(M)` is the multiplication of `Sym(M~)` on global
sections.** -/
theorem toOpenₗ_symMulₗ (i j : ℤ) (x : gradedPiece (R := R) M i)
    (y : gradedPiece (R := R) M j) :
    AffineBaseChange.toOpenₗ (pieceModule M (i + j)) ⊤ (symMulₗ (R := R) M i j x y) =
      ((symAlgebra M).mul i j).app (op (⊤ : (Spec R).Opens))
        (AffineBaseChange.toOpenₗ (pieceModule M i) ⊤ x)
        (AffineBaseChange.toOpenₗ (pieceModule M j) ⊤ y) := by
  have h := symAlgebra_mul_toTilde M i j (op (⊤ : (Spec R).Opens))
    ((1 : Γ(Spec R, (⊤ : (Spec R).Opens))) ⊗ₜ[R] x)
    ((1 : Γ(Spec R, (⊤ : (Spec R).Opens))) ⊗ₜ[R] y)
  rw [mulSec_tmul, one_mul] at h
  rw [← pieceCmp_top_one_tmul, ← pieceCmp_top_one_tmul, ← pieceCmp_top_one_tmul]
  exact h.symm

/-- **The degreewise comparison.** A degree-`n` element of `Sym_R(M)` is a global section of the
degree-`n` piece of `Sym(M~)`, and every global section arises this way exactly once. -/
def globalPieceEquiv (n : ℕ) :
    gradedPiece (R := R) M (n : ℤ) ≃ₗ[R] (symSheafGradedAlgebra M).sectionPieces ⊤ n :=
  LinearEquiv.ofBijective (AffineBaseChange.toOpenₗ (pieceModule M (n : ℤ)) ⊤)
    (ConcreteCategory.bijective_of_isIso (tilde.toOpen (pieceModule M (n : ℤ)) ⊤))

/-- The degreewise comparison is `AlgebraicGeometry.tilde.toOpen` at the top open. -/
theorem globalPieceEquiv_apply (n : ℕ) (x : gradedPiece (R := R) M (n : ℤ)) :
    globalPieceEquiv M n x = AffineBaseChange.toOpenₗ (pieceModule M (n : ℤ)) ⊤ x :=
  rfl

/-- **The comparison takes the unit of `Sym_R(M)` to the unit of `Sym(M~)`.** -/
theorem globalPieceEquiv_one :
    globalPieceEquiv M 0 (oneG (R := R) M) = (symSheafGradedAlgebra M).one ⊤ :=
  toOpenₗ_oneG M

/-- **The comparison takes the graded multiplication of `Sym_R(M)` to the multiplication of
`Sym(M~)`.** -/
theorem globalPieceEquiv_mul (i j : ℕ) (x : gradedPiece (R := R) M (i : ℤ))
    (y : gradedPiece (R := R) M (j : ℤ)) :
    globalPieceEquiv M (i + j) (symMulₗ (R := R) M (i : ℤ) (j : ℤ) x y) =
      ((symSheafGradedAlgebra M).mul (i : ℤ) (j : ℤ)).app ⊤
        (globalPieceEquiv M i x) (globalPieceEquiv M j y) :=
  toOpenₗ_symMulₗ M (i : ℤ) (j : ℤ) x y

/-! ### The graded ring of global sections -/

/-- The degreewise comparison, assembled on the direct sum of the homogeneous pieces. -/
def globalSectionsDirectSumEquiv :
    (⨁ n : ℕ, SymPow.symmetricPower n R M) ≃+ (symSheafGradedAlgebra M).sectionRing ⊤ :=
  DirectSum.congrAddEquiv fun n => (globalPieceEquiv M n).toAddEquiv

/-- The assembled comparison acts on a homogeneous element of degree `n` by
`Stacks.SymGraded.globalPieceEquiv M n`. -/
theorem globalSectionsDirectSumEquiv_of (n : ℕ) (x : SymPow.symmetricPower n R M) :
    globalSectionsDirectSumEquiv M (DirectSum.of _ n x) =
      DirectSum.of _ n (globalPieceEquiv M n x) :=
  DirectSum.map_of (fun n => (globalPieceEquiv M n).toAddEquiv.toAddMonoidHom) n x

/-- **The assembled comparison is multiplicative.** -/
theorem globalSectionsDirectSumEquiv_mul (a b : ⨁ n : ℕ, SymPow.symmetricPower n R M) :
    globalSectionsDirectSumEquiv M (a * b) =
      globalSectionsDirectSumEquiv M a * globalSectionsDirectSumEquiv M b := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of i x =>
      induction b using DirectSum.induction_on with
      | zero => simp
      | of j y =>
          rw [DirectSum.of_mul_of, globalSectionsDirectSumEquiv_of,
            globalSectionsDirectSumEquiv_of, globalSectionsDirectSumEquiv_of,
            DirectSum.of_mul_of]
          exact congrArg (DirectSum.of _ (i + j)) (globalPieceEquiv_mul M i j x y)
      | add y y' hy hy' => simp only [mul_add, map_add, hy, hy']
  | add x x' hx hx' => simp only [add_mul, map_add, hx, hx']

/-- **The graded ring of global sections of `Sym(M~)` is `Sym_R(M)`.** -/
def globalSectionsRingEquiv :
    SymmetricAlgebra R M ≃+* (symSheafGradedAlgebra M).sectionRing ⊤ :=
  (DirectSum.decomposeRingEquiv (fun n : ℕ => SymPow.symmetricPower n R M)).trans
    { globalSectionsDirectSumEquiv M with
      map_mul' := globalSectionsDirectSumEquiv_mul M }

/-- The ring isomorphism is the assembled comparison applied to the decomposition of an element
of `Sym_R(M)` into its homogeneous components. -/
theorem globalSectionsRingEquiv_apply (x : SymmetricAlgebra R M) :
    globalSectionsRingEquiv M x =
      globalSectionsDirectSumEquiv M
        (DirectSum.decompose (fun n : ℕ => SymPow.symmetricPower n R M) x) :=
  rfl

/-- The comparison carries the `n`-th symmetric power into the degree-`n` part of the section
ring. -/
theorem globalSectionsRingEquiv_mem_grading {n : ℕ} {x : SymmetricAlgebra R M}
    (hx : x ∈ SymPow.symmetricPower n R M) :
    globalSectionsRingEquiv M x ∈ (symSheafGradedAlgebra M).grading ⊤ n := by
  rw [globalSectionsRingEquiv_apply,
    DirectSum.decompose_of_mem (fun n : ℕ => SymPow.symmetricPower n R M) hx,
    globalSectionsDirectSumEquiv_of]
  exact SheafGradedAlgebra.of_mem_grading _ _ _

/-- The inverse comparison carries the degree-`n` part of the section ring into the `n`-th
symmetric power. -/
theorem globalSectionsRingEquiv_symm_mem_symmetricPower {n : ℕ}
    {z : (symSheafGradedAlgebra M).sectionRing ⊤}
    (hz : z ∈ (symSheafGradedAlgebra M).grading ⊤ n) :
    (globalSectionsRingEquiv M).symm z ∈ SymPow.symmetricPower n R M := by
  obtain ⟨y, rfl⟩ := hz
  have h : globalSectionsRingEquiv M ((globalPieceEquiv M n).symm y : SymmetricAlgebra R M) =
      DirectSum.of ((symSheafGradedAlgebra M).sectionPieces ⊤) n y := by
    rw [globalSectionsRingEquiv_apply,
      DirectSum.decompose_coe (fun n : ℕ => SymPow.symmetricPower n R M)
        ((globalPieceEquiv M n).symm y)]
    exact (globalSectionsDirectSumEquiv_of M n ((globalPieceEquiv M n).symm y)).trans
      (congrArg (DirectSum.of _ n) ((globalPieceEquiv M n).apply_symm_apply y))
  rw [← h, (globalSectionsRingEquiv M).symm_apply_apply]
  exact ((globalPieceEquiv M n).symm y).2

/-- **The graded ring of global sections of `Sym(M~)` is `Sym_R(M)`, as graded rings.** -/
def gradedGlobalSectionsHom :
    (fun n : ℕ => SymPow.symmetricPower n R M) →+*ᵍ (symSheafGradedAlgebra M).grading ⊤ where
  toRingHom := (globalSectionsRingEquiv M).toRingHom
  map_mem hx := globalSectionsRingEquiv_mem_grading M hx

/-- The inverse of `Stacks.SymGraded.gradedGlobalSectionsHom`. -/
def gradedGlobalSectionsInv :
    (symSheafGradedAlgebra M).grading ⊤ →+*ᵍ (fun n : ℕ => SymPow.symmetricPower n R M) where
  toRingHom := (globalSectionsRingEquiv M).symm.toRingHom
  map_mem hz := globalSectionsRingEquiv_symm_mem_symmetricPower M hz

/-- `Stacks.SymGraded.gradedGlobalSectionsInv` is a right inverse of
`Stacks.SymGraded.gradedGlobalSectionsHom`. -/
theorem gradedGlobalSectionsHom_comp_inv :
    (gradedGlobalSectionsHom M).comp (gradedGlobalSectionsInv M) =
      GradedRingHom.id ((symSheafGradedAlgebra M).grading ⊤) :=
  GradedRingHom.ext fun z => (globalSectionsRingEquiv M).apply_symm_apply z

/-- `Stacks.SymGraded.gradedGlobalSectionsInv` is a left inverse of
`Stacks.SymGraded.gradedGlobalSectionsHom`. -/
theorem gradedGlobalSectionsInv_comp_hom :
    (gradedGlobalSectionsInv M).comp (gradedGlobalSectionsHom M) =
      GradedRingHom.id (fun n : ℕ => SymPow.symmetricPower n R M) :=
  GradedRingHom.ext fun x => (globalSectionsRingEquiv M).symm_apply_apply x

end Stacks.SymGraded

end
