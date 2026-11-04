module

public import StacksFrontier.AlgebraicGeometry.AffineSymmetricAlgebra.PresheafAlgebra

/-!
# The symmetric algebra of an associated sheaf on an affine scheme

Let `R` be a commutative ring and `M` an `R`-module. **This file constructs the sheaf of graded
`𝒪_{Spec R}`-algebras whose degree-`n` homogeneous piece is `Sym^n_R(M)~`**, the associated sheaf
of the `n`-th symmetric power of `M`, with the multiplication induced by that of the symmetric
algebra of `M` and with the degree-one generator induced by `SymmetricAlgebra.ι`.

The pieces are the associated sheaves **on the nose**: `Stacks.SymGraded.symAlgebra_piece_natCast`
is an equality, not an isomorphism, so a statement about `Sym^n_R(M)~` is a statement about the
degree-`n` piece of this algebra with no comparison map interposed.

## Main definitions

* `Stacks.SymGraded.symAlgebra`: the sheaf of graded algebras.
* `Stacks.SymGraded.ιG`: the degree-one inclusion `M ⟶ Sym^1_R(M)`.
* `Stacks.SymGraded.symGen`: its associated sheaf, a degree-one generator
  `M̃ ⟶ (symAlgebra M).piece 1`.

## Main results

* `Stacks.SymGraded.symAlgebra_piece_natCast`: the degree-`n` piece is `Sym^n_R(M)~`.
* `Stacks.SymGraded.symAlgebra_mul_toTilde`: the multiplication on the comparison images of two
  base-changed sections is the comparison image of their product. Together with local
  bijectivity of `Stacks.AffineBaseChange.toTilde` this pins the multiplication down.

## Implementation notes

The construction is `Stacks.GradedAlgebra.ofComparison` applied to the graded algebra of
presheaves `Stacks.SymGraded.presheafAlgebra` along the comparison
`Stacks.AffineBaseChange.toTilde`, which is locally bijective. Nothing is sheafified: the
homogeneous pieces are given, and the only thing extended is the multiplication, which is a
*sectionwise* bilinear family and therefore extends by
`Stacks.BilinearMap.existsUnique_extend` with no map out of a sheafified tensor product.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct

universe u

namespace Stacks.SymGraded

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

/-- The associated sheaf of the degree-`n` graded piece of the symmetric algebra of `M`. -/
abbrev pieceSheaf (n : ℤ) : SheafOfModules.{u} (Spec R).ringCatSheaf :=
  tilde (pieceModule M n)

/-- The comparison from the base-change presheaf of the degree-`n` graded piece to its
associated sheaf. -/
abbrev pieceCmp (n : ℤ) : piecePresheaf M n ⟶ (pieceSheaf M n).val :=
  AffineBaseChange.toTilde (pieceModule M n)

/-- **The symmetric algebra of `M̃` on `Spec R`**, as a sheaf of graded `𝒪_{Spec R}`-algebras
whose degree-`n` piece is the associated sheaf of the `n`-th symmetric power of `M`. -/
def symAlgebra : SheafOfModules.GradedAlgebra.{u, u} (Spec R).ringCatSheaf :=
  (presheafAlgebra M).ofComparison (pieceSheaf M) (pieceCmp M)

/-- The degree-`n` piece of `symAlgebra M` is `pieceSheaf M n`. -/
theorem symAlgebra_piece (n : ℤ) : (symAlgebra M).piece n = pieceSheaf M n := rfl

/-- **The degree-`n` piece is the associated sheaf of the `n`-th symmetric power**, on the
nose. -/
theorem symAlgebra_piece_natCast (n : ℕ) :
    (symAlgebra M).piece (n : ℤ) = tilde (ModuleCat.of R (SymPow.symmetricPower n R M)) := rfl

/-- The multiplication of `symAlgebra M` on the comparison images of two base-changed local
sections. -/
theorem symAlgebra_mul_toTilde (i j : ℤ) (U : ((Spec R).Opens)ᵒᵖ)
    (x : (piecePresheaf M i).obj U) (y : (piecePresheaf M j).obj U) :
    ((symAlgebra M).mul i j).app U
        (PresheafOfModules.Hom.app (pieceCmp M i) U x)
        (PresheafOfModules.Hom.app (pieceCmp M j) U y) =
      PresheafOfModules.Hom.app (pieceCmp M (i + j)) U (mulSec M U i j x y) :=
  (presheafAlgebra M).ofComparison_mul_comparison (pieceSheaf M) (pieceCmp M) i j U x y

/-- The unit of `symAlgebra M` on `U` is the comparison image of `1 ⊗ oneG M`. -/
theorem symAlgebra_one_eval (U : ((Spec R).Opens)ᵒᵖ) :
    (symAlgebra M).one.eval U =
      PresheafOfModules.Hom.app (pieceCmp M 0) U
        ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] oneG (R := R) M) :=
  rfl

/-! ### Negative degrees -/

/-- The graded piece of the symmetric algebra of `M` in a negative degree is `⊥`. -/
theorem gradedPiece_eq_bot_of_neg {n : ℤ} (hn : n < 0) : gradedPiece (R := R) M n = ⊥ := by
  match n with
  | .ofNat k => exact absurd hn (not_lt.mpr (Int.natCast_nonneg k))
  | .negSucc k => rfl

/-- Every local section of the base-change presheaf of a negative-degree piece vanishes. -/
theorem piecePresheaf_eq_zero_of_neg {n : ℤ} (hn : n < 0) (U : ((Spec R).Opens)ᵒᵖ)
    (t : (piecePresheaf M n).obj U) : t = 0 := by
  have hbot := gradedPiece_eq_bot_of_neg M hn
  induction t using TensorProduct.induction_on with
  | zero => rfl
  | tmul a z =>
      have hz : z = 0 := Subtype.ext (Submodule.mem_bot R |>.mp (hbot ▸ z.2))
      rw [hz]
      exact TensorProduct.tmul_zero _ a
  | add t t' ht ht' =>
      rw [ht, ht']
      exact add_zero 0

/-- **The symmetric algebra is concentrated in nonnegative degrees**: every local section of a
negative-degree piece vanishes. -/
theorem symAlgebra_piece_eq_zero_of_neg {n : ℤ} (hn : n < 0) (U : ((Spec R).Opens)ᵒᵖ)
    (x : ((symAlgebra M).piece n).val.obj U) : x = 0 := by
  refine Stacks.eq_of_isSeparated ((symAlgebra M).piece n)
    (Stacks.cmpSieve_mem (pieceCmp M n) x) ?_
  rintro Y f ⟨t, ht⟩
  have ht' : PresheafOfModules.Hom.app (pieceCmp M n) (op Y) t =
    ((symAlgebra M).piece n).val.map f.op x := ht
  rw [← ht', piecePresheaf_eq_zero_of_neg M hn (op Y) t]
  rw [show PresheafOfModules.Hom.app (pieceCmp M n) (op Y) 0 = 0 from
    map_zero (AffineBaseChange.toTildeₗ (pieceModule M n) (op Y).unop)]
  exact (map_zero ((((symAlgebra M).piece n).val.map f.op).hom)).symm

/-! ### The degree-one generator -/

/-- The degree-one generator at the level of base-change presheaves. -/
abbrev genPresheaf : AffineBaseChange.presheaf M ⟶ piecePresheaf M 1 :=
  AffineBaseChange.presheafMap (ModuleCat.ofHom (ιG (R := R) M))

/-- **The degree-one generator of `symAlgebra M`**: the associated sheaf of the degree-one
inclusion `M ⟶ Sym^1_R(M)`. -/
def symGen : (tilde M : SheafOfModules.{u} (Spec R).ringCatSheaf) ⟶ (symAlgebra M).piece 1 :=
  tilde.map (ModuleCat.ofHom (ιG (R := R) M))

/-- `symGen M` sends the comparison image of a base-changed section to the comparison image of
its image under `genPresheaf M`. -/
theorem symGen_toTilde (U : ((Spec R).Opens)ᵒᵖ) (x : Γ(Spec R, U.unop) ⊗[R] M) :
    (symGen M).val.app U
        (PresheafOfModules.Hom.app (AffineBaseChange.toTilde M) U x) =
      PresheafOfModules.Hom.app (pieceCmp M 1) U
        (PresheafOfModules.Hom.app (genPresheaf M) U x) :=
  AffineBaseChange.toTilde_map_app (ModuleCat.ofHom (ιG (R := R) M)) U x

/-- **The degree-one generator has pairwise commuting image**: the images under `symGen M`
of any two local sections of `M̃` commute in `symAlgebra M`. -/
theorem pairwiseCommutes_symGen :
    SheafOfModules.GradedAlgebra.PairwiseCommutes (symGen M) :=
  (presheafAlgebra M).pairwiseCommutes_cmpGen (pieceSheaf M) (pieceCmp M) (genPresheaf M)
    (AffineBaseChange.toTilde M) (symGen M) (symGen_toTilde M)
    fun X _ _ => mulSec_comm_one M X _ _

end Stacks.SymGraded
