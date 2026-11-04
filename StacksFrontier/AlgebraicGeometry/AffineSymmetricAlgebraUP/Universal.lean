module

public import StacksFrontier.AlgebraicGeometry.AffineSymmetricAlgebraUP.Lift

/-!
# The universal property of the symmetric algebra of an associated sheaf on an affine scheme

Let `R` be a commutative ring and `M` an `R`-module. **This file proves that
`Stacks.SymGraded.symAlgebra M` with its degree-one generator `Stacks.SymGraded.symGen M` is
the symmetric algebra of `M̃` on `Spec R`** in the sense of
`SheafOfModules.GradedAlgebra.IsSymmetricAlgebra`: every degree-one generator of a sheaf of
graded `𝒪_{Spec R}`-algebras whose image commutes pairwise is obtained from `symGen M` by a
unique unital homomorphism.

## Main results

* `Stacks.SymGraded.existsUnique_desc_symAlgebra`: **the universal property**.
* `Stacks.SymGraded.isSymmetricAlgebra`: `symAlgebra M` is a symmetric algebra of `M̃`.
* `Stacks.SymGraded.unitalHom_ext_of_symGen`: **two unital homomorphisms out of `symAlgebra M`
  agreeing on the degree-one generator are equal.** This is the uniqueness half, and it is the
  half with mathematical content: the degree-`n` piece is generated, locally and up to scalars,
  by products of `n` degree-one generators.

## Implementation notes

The existence half is `Stacks.GradedAlgebra.existsUnique_descCmp` applied to the degreewise
morphism `Stacks.SymGraded.descHom`; all its content is in
`StacksFrontier.AlgebraicGeometry.AffineSymmetricAlgebraUP.Lift`.

The uniqueness half runs through three reductions. Both homomorphisms are determined on the
comparison images of local sections of the base-change presheaf, because the comparison is
locally surjective and the target is separated (`Stacks.hom_eq_of_app_eq`); on a pure tensor
`a ⊗ z` they are `a` times their value on `1 ⊗ z`, so the question is a semilinear one about
`z`, and `SymPow.ext_of_prod_ι` reduces it to the products of `n` degree-one generators. On such
a product the comparison image is an ordered product of comparison images of degree-one sections
(`Stacks.SymGraded.pieceCmp_prod_ι`), which any unital homomorphism carries to the corresponding
ordered product in the target (`Stacks.GradedAlgebra.app_homogeneousProd`) — and that is
determined by the degree-one component.

Negative degrees are handled separately and trivially: every local section of a negative-degree
piece vanishes, by `Stacks.SymGraded.symAlgebra_piece_eq_zero_of_neg`.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite PresheafOfModules
open scoped TensorProduct

universe u

namespace Stacks.SymGraded

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

/-! ### The comparison on pure tensors -/

/-- A pure tensor `a ⊗ₜ z` is the scalar multiple `a • (1 ⊗ₜ z)`. -/
theorem tmul_eq_smul_one_tmul (n : ℤ) (U : ((Spec R).Opens)ᵒᵖ) (a : Γ(Spec R, U.unop))
    (z : gradedPiece (R := R) M n) :
    (a • ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] z) :
      Γ(Spec R, U.unop) ⊗[R] gradedPiece (R := R) M n) = a ⊗ₜ[R] z := by
  rw [TensorProduct.smul_tmul' a (1 : Γ(Spec R, U.unop)) z, smul_eq_mul, mul_one]

/-- For `r : R`, the tensor `1 ⊗ₜ (r • z)` equals `algebraMap R _ r ⊗ₜ z`. -/
theorem one_tmul_smul (n : ℤ) (U : ((Spec R).Opens)ᵒᵖ) (r : R)
    (z : gradedPiece (R := R) M n) :
    ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] (r • z) :
      Γ(Spec R, U.unop) ⊗[R] gradedPiece (R := R) M n) =
      algebraMap R Γ(Spec R, U.unop) r ⊗ₜ[R] z := by
  rw [← TensorProduct.smul_tmul r (1 : Γ(Spec R, U.unop)) z]
  exact congrArg (fun c : Γ(Spec R, U.unop) => c ⊗ₜ[R] z)
    ((Algebra.smul_def r (1 : Γ(Spec R, U.unop))).trans (mul_one _))

/-- The comparison image of a product of degree-one generators, read through the degree-one
generator of `symAlgebra M`. -/
theorem pieceCmp_one_tmul_ιG (U : ((Spec R).Opens)ᵒᵖ) (m : M) :
    PresheafOfModules.Hom.app (pieceCmp M 1) U
        ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] ιG (R := R) M m) =
      (symGen M).val.app U (AffineBaseChange.toTildeₗ M U.unop
        ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] m)) := by
  refine ((symGen_toTilde M U ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] m)).trans
    (congrArg (PresheafOfModules.Hom.app (pieceCmp M 1) U) ?_)).symm
  exact (AffineBaseChange.presheafMap_app (ModuleCat.ofHom (ιG (R := R) M)) U
      ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] m)).trans
    (AffineBaseChange.presheafMapₗ_tmul (ModuleCat.ofHom (ιG (R := R) M)) U.unop 1 m)

/-! ### The graded algebra of presheaves, re-spelled -/

/-- The base change of the symmetric algebra of `M`, as a graded algebra of presheaves of
modules over `(Spec R).presheaf`. -/
def presheafAlgebraP : Stacks.GradedAlgebra (symPieceVal M) := presheafAlgebra M

/-! ### Ordered products of degree-one generators -/

/-- **The ordered product of `n` degree-one generators, in the base-change presheaf.** -/
theorem homogeneousProd_presheafAlgebra (U : ((Spec R).Opens)ᵒᵖ) (n : ℕ) (s : Fin n → M) :
    (presheafAlgebraP M).homogeneousProd U n
        (fun i => (1 : Γ(Spec R, U.unop)) ⊗ₜ[R] ιG (R := R) M (s i)) =
      (1 : Γ(Spec R, U.unop)) ⊗ₜ[R]
        (⟨∏ i : Fin n, SymmetricAlgebra.ι R M (s i), SymmetricAlgebra.prod_ι_mem R s⟩ :
          SymPow.symmetricPower n R M) := by
  induction n with
  | zero =>
      refine congrArg (fun w : gradedPiece (R := R) M 0 =>
        (1 : Γ(Spec R, U.unop)) ⊗ₜ[R] w) (Subtype.ext ?_)
      simp
  | succ n ih =>
      show ((presheafAlgebraP M).mul (n : ℤ) 1).app U
        ((presheafAlgebraP M).homogeneousProd U n
          (fun i => (1 : Γ(Spec R, U.unop)) ⊗ₜ[R] ιG (R := R) M (s i.castSucc)))
        ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] ιG (R := R) M (s (Fin.last n))) = _
      rw [ih fun i => s i.castSucc]
      refine Eq.trans (mulSec_tmul M U (n : ℤ) 1 1 1 _ _) ?_
      rw [_root_.one_mul (1 : Γ(Spec R, U.unop))]
      refine congrArg (fun w : gradedPiece (R := R) M ((n : ℤ) + 1) =>
        (1 : Γ(Spec R, U.unop)) ⊗ₜ[R] w) (Subtype.ext ?_)
      exact (Fin.prod_univ_castSucc (fun i => SymmetricAlgebra.ι R M (s i))).symm

/-- **The comparison image of a product of `n` degree-one generators** is the ordered product,
in `symAlgebra M`, of the comparison images of the degree-one generators. -/
theorem pieceCmp_prod_ι (U : ((Spec R).Opens)ᵒᵖ) (n : ℕ) (s : Fin n → M) :
    PresheafOfModules.Hom.app (pieceCmp M (n : ℤ)) U
        ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R]
          (⟨∏ i : Fin n, SymmetricAlgebra.ι R M (s i), SymmetricAlgebra.prod_ι_mem R s⟩ :
            SymPow.symmetricPower n R M)) =
      (presheafOf (symAlgebra M)).homogeneousProd U n
        (fun i => PresheafOfModules.Hom.app (pieceCmp M 1) U
          ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] ιG (R := R) M (s i))) := by
  refine Eq.trans (congrArg (PresheafOfModules.Hom.app (pieceCmp M (n : ℤ)) U)
    (homogeneousProd_presheafAlgebra M U n s).symm) ?_
  exact Stacks.GradedAlgebra.app_homogeneousProd (presheafAlgebraP M)
    (presheafOf (symAlgebra M)) (pieceCmp M)
    (fun i j X x y => (symAlgebra_mul_toTilde M i j X x y).symm)
    (fun X => (symAlgebra_one_eval M X).symm) U n _

/-! ### Uniqueness -/

variable (B : SheafOfModules.GradedAlgebra.{u, u} (Spec R).ringCatSheaf)

/-- A unital homomorphism out of `symAlgebra M`, precomposed with the comparison: a morphism out
of the base-change presheaf of the `n`-th symmetric power. -/
def compCmp (g : SheafOfModules.GradedAlgebra.UnitalHom (symAlgebra M) B) (n : ℤ) :
    symPieceVal M n ⟶ pieceVal B n :=
  pieceCmp M n ≫ (g.app n).val

/-- On sections, `compCmp M B g n` is the comparison `pieceCmp M n` followed by `g`. -/
theorem compCmp_app (g : SheafOfModules.GradedAlgebra.UnitalHom (symAlgebra M) B) (n : ℤ)
    (U : ((Spec R).Opens)ᵒᵖ) (t : Γ(Spec R, U.unop) ⊗[R] gradedPiece (R := R) M n) :
    PresheafOfModules.Hom.app (compCmp M B g n) U t =
      (g.app n).val.app U (PresheafOfModules.Hom.app (pieceCmp M n) U t) := rfl

/-- The value of `compCmp M B g n` on `a ⊗ₜ z` is `a` times its value on `1 ⊗ₜ z`. -/
theorem compCmp_tmul (g : SheafOfModules.GradedAlgebra.UnitalHom (symAlgebra M) B) (n : ℤ)
    (U : ((Spec R).Opens)ᵒᵖ) (a : Γ(Spec R, U.unop)) (z : gradedPiece (R := R) M n) :
    PresheafOfModules.Hom.app (compCmp M B g n) U (a ⊗ₜ[R] z) =
      (a : secRing R U) • PresheafOfModules.Hom.app (compCmp M B g n) U
        ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] z) := by
  refine Eq.trans (congrArg (PresheafOfModules.Hom.app (compCmp M B g n) U)
    (tmul_eq_smul_one_tmul M n U a z).symm) ?_
  exact map_smul (ConcreteCategory.hom ((compCmp M B g n).app U)) (a : secRing R U) _

/-- A unital homomorphism out of `symAlgebra M`, read on the comparison image of `1 ⊗ z` as a
semilinear map out of the `n`-th symmetric power. -/
def uniqSemilin (g : SheafOfModules.GradedAlgebra.UnitalHom (symAlgebra M) B) (k : ℕ)
    (U : ((Spec R).Opens)ᵒᵖ) :
    SymPow.symmetricPower k R M →ₛₗ[specStruct R U] (pieceVal B (k : ℤ)).obj U where
  toFun z := PresheafOfModules.Hom.app (compCmp M B g (k : ℤ)) U
    ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] z)
  map_add' z z' := by
    refine Eq.trans (congrArg (PresheafOfModules.Hom.app (compCmp M B g (k : ℤ)) U)
      (TensorProduct.tmul_add (1 : Γ(Spec R, U.unop)) z z')) ?_
    exact map_add (ConcreteCategory.hom ((compCmp M B g (k : ℤ)).app U)) _ _
  map_smul' r z := by
    refine Eq.trans (congrArg (PresheafOfModules.Hom.app (compCmp M B g (k : ℤ)) U)
      (one_tmul_smul M (k : ℤ) U r z)) ?_
    exact compCmp_tmul M B g (k : ℤ) U (algebraMap R Γ(Spec R, U.unop) r) z

/-- **A unital homomorphism out of `symAlgebra M` on a product of degree-one generators** is the
ordered product of the images of the generators under its degree-one component. -/
theorem compCmp_prod_ι (g : SheafOfModules.GradedAlgebra.UnitalHom (symAlgebra M) B)
    (U : ((Spec R).Opens)ᵒᵖ) (k : ℕ) (s : Fin k → M) :
    PresheafOfModules.Hom.app (compCmp M B g (k : ℤ)) U
        ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R]
          (⟨∏ i : Fin k, SymmetricAlgebra.ι R M (s i), SymmetricAlgebra.prod_ι_mem R s⟩ :
            SymPow.symmetricPower k R M)) =
      (presheafOf B).homogeneousProd U k fun i =>
        (symGen M ≫ g.app 1).val.app U (AffineBaseChange.toTildeₗ M U.unop
          ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] s i)) := by
  refine Eq.trans (congrArg ((g.app (k : ℤ)).val.app U) (pieceCmp_prod_ι M U k s)) ?_
  refine Eq.trans (Stacks.GradedAlgebra.app_homogeneousProd (presheafOf (symAlgebra M))
    (presheafOf B) (fun n => (g.app n).val) (fun i j X x y => g.map_mul i j X x y)
    (fun X => g.map_one X) U k _) ?_
  exact congrArg ((presheafOf B).homogeneousProd U k) (funext fun i =>
    congrArg ((g.app 1).val.app U) (pieceCmp_one_tmul_ιG M U (s i)))

/-- **Two unital homomorphisms out of `symAlgebra M` agreeing on the degree-one generator are
equal.** -/
theorem unitalHom_ext_of_symGen
    {g g' : SheafOfModules.GradedAlgebra.UnitalHom (symAlgebra M) B}
    (h : symGen M ≫ g.app 1 = symGen M ≫ g'.app 1) : g = g' := by
  refine SheafOfModules.GradedAlgebra.UnitalHom.ext fun n => SheafOfModules.hom_ext ?_
  refine Stacks.hom_eq_of_app_eq (T := (pieceSheaf M n).val)
    (B.piece n).isSheaf.isSeparated (pieceCmp M n) fun U t => ?_
  match n with
  | .negSucc k =>
      rw [symAlgebra_piece_eq_zero_of_neg M (Int.negSucc_lt_zero k) U
        (PresheafOfModules.Hom.app (pieceCmp M (Int.negSucc k)) U t)]
      erw [map_zero, map_zero]
  | .ofNat k =>
      have key : uniqSemilin M B g k U = uniqSemilin M B g' k U := by
        refine SymPow.ext_of_prod_ι fun s => ?_
        refine (compCmp_prod_ι M B g U k s).trans (Eq.trans ?_ (compCmp_prod_ι M B g' U k s).symm)
        exact congrArg
          (fun q : (tilde M : SheafOfModules.{u} (Spec R).ringCatSheaf) ⟶ B.piece 1 =>
            (presheafOf B).homogeneousProd U k fun i => q.val.app U
              (AffineBaseChange.toTildeₗ M U.unop ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] s i))) h
      show PresheafOfModules.Hom.app (compCmp M B g (Int.ofNat k)) U t =
        PresheafOfModules.Hom.app (compCmp M B g' (Int.ofNat k)) U t
      induction t using TensorProduct.induction_on with
      | zero => erw [map_zero, map_zero]
      | tmul a z =>
          rw [compCmp_tmul M B g (Int.ofNat k) U a z, compCmp_tmul M B g' (Int.ofNat k) U a z]
          exact congrArg (fun y : (pieceVal B (Int.ofNat k)).obj U => (a : secRing R U) • y)
            (DFunLike.congr_fun key z)
      | add t t' ht ht' => erw [map_add, map_add, ht, ht']

/-! ### Existence, and the universal property -/

variable (κ : (tilde M : SheafOfModules.{u} (Spec R).ringCatSheaf) ⟶ B.piece 1)
  (hc : Stacks.GradedAlgebra.GenCommutes (presheafOf B) (genBC M B κ))

/-- A pure tensor of the base-change presheaf of `M`, as a scalar multiple of `1 ⊗ m`. -/
theorem bcTmul_eq_smul (U : ((Spec R).Opens)ᵒᵖ) (a : Γ(Spec R, U.unop)) (m : M) :
    (a • ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] m) : Γ(Spec R, U.unop) ⊗[R] M) = a ⊗ₜ[R] m := by
  rw [TensorProduct.smul_tmul' a (1 : Γ(Spec R, U.unop)) m, smul_eq_mul, mul_one]

/-- `descHom` in degree one recovers the given degree-one generator. -/
theorem descHom_genPresheaf (U : ((Spec R).Opens)ᵒᵖ) (x : Γ(Spec R, U.unop) ⊗[R] M) :
    PresheafOfModules.Hom.app (descHom M B κ hc 1) U
        (PresheafOfModules.Hom.app (genPresheaf M) U x) =
      κ.val.app U (PresheafOfModules.Hom.app (AffineBaseChange.toTilde M) U x) := by
  induction x using TensorProduct.induction_on with
  | zero => erw [map_zero, map_zero]; rfl
  | tmul a m =>
      rw [AffineBaseChange.presheafMap_app, AffineBaseChange.presheafMapₗ_tmul, descHom_tmul,
        show ((ConcreteCategory.hom (ModuleCat.ofHom (ιG (R := R) M)) m :
            gradedPiece (R := R) M 1) : SymmetricAlgebra R M) =
          SymmetricAlgebra.ι R M m from rfl,
        theta_ι, (presheafOf B).proj_incl]
      refine Eq.trans (map_smul (ConcreteCategory.hom ((genBC M B κ).app U))
        (a : secRing R U) ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] m)).symm ?_
      exact congrArg (PresheafOfModules.Hom.app (genBC M B κ) U) (bcTmul_eq_smul M U a m)
  | add x y hx hy => erw [map_add, map_add, hx, hy, map_add, map_add]; rfl

/-- **The universal property of `Stacks.SymGraded.symAlgebra`.** -/
theorem existsUnique_desc_symAlgebra (hκ : SheafOfModules.GradedAlgebra.PairwiseCommutes κ) :
    ∃! g : SheafOfModules.GradedAlgebra.UnitalHom (symAlgebra M) B,
      symGen M ≫ g.app 1 = κ := by
  obtain ⟨h, hh, -⟩ := Stacks.GradedAlgebra.existsUnique_descCmp (presheafAlgebra M)
    (pieceSheaf M) (pieceCmp M)
    (fun n => descHom M B κ (genCommutes_genBC M B κ hκ) n)
    (fun i j X x y => descHom_mul M B κ (genCommutes_genBC M B κ hκ) i j X x y)
    (fun X => descHom_one M B κ (genCommutes_genBC M B κ hκ) X)
  have hkey : symGen M ≫ h.app 1 = κ := by
    refine SheafOfModules.hom_ext (Stacks.hom_eq_of_app_eq (T := (tilde M).val)
      (B.piece 1).isSheaf.isSeparated (AffineBaseChange.toTilde M) fun U x => ?_)
    show (h.app 1).val.app U ((symGen M).val.app U
      (PresheafOfModules.Hom.app (AffineBaseChange.toTilde M) U x)) = _
    rw [symGen_toTilde M U x, hh 1 U (PresheafOfModules.Hom.app (genPresheaf M) U x)]
    exact descHom_genPresheaf M B κ (genCommutes_genBC M B κ hκ) U x
  exact ⟨h, hkey, fun g hg => unitalHom_ext_of_symGen M B (hg.trans hkey.symm)⟩

/-- **`Stacks.SymGraded.symAlgebra M` is the symmetric algebra of `M̃` on `Spec R`.** -/
theorem isSymmetricAlgebra :
    SheafOfModules.GradedAlgebra.IsSymmetricAlgebra (symAlgebra M) (symGen M) :=
  ⟨pairwiseCommutes_symGen M, fun B κ hκ => existsUnique_desc_symAlgebra M B κ hκ⟩

end Stacks.SymGraded
