module

public import StacksFrontier.AlgebraicGeometry.AffineSymmetricAlgebraUP.Universal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricAlgebras

/-!
# Symmetric powers of an associated sheaf on an affine scheme

Let `R` be a commutative ring and `M` an `R`-module. **This file identifies the associated sheaf
of the `n`-th symmetric power of `M` with the `n`-th symmetric power of `M̃` on `Spec R`**, and
pins the identification down in degree zero and degree one.

The symmetric power of `M̃` is the degree-`n` homogeneous piece of *the* symmetric algebra of
`M̃`, which is taken as a hypothesis `A : SheafOfModules.TensorExteriorSymmetricAlgebras …` in
the idiom of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricAlgebras`: quantifying over
bundles is strictly stronger than fixing a chosen one, since any two are canonically
isomorphic.

## Main definitions

* `Stacks.SymGraded.tildeSymmetricPowerIso`: the affine symmetric-power comparison
  `Sym^n_R(M)~ ≅ Symⁿ(M̃)`.

## Main results

* `Stacks.SymGraded.tildeSymmetricPowerIso_unit`: in degree zero the comparison takes the
  algebraic unit to the multiplicative unit of the symmetric algebra sheaf.
* `Stacks.SymGraded.tildeSymmetricPowerIso_generator`: in degree one it takes an algebraic
  degree-one generator to the corresponding sheaf generator.

## Implementation notes

`Stacks.SymGraded.symAlgebra_piece_natCast` says that the degree-`n` piece of
`Stacks.SymGraded.symAlgebra M` **is** `Sym^n_R(M)~` — an equality, not an isomorphism — so the
comparison is nothing but the canonical comparison
`SheafOfModules.GradedAlgebra.IsSymmetricAlgebra.pieceIso` between two symmetric algebras of
`M̃`, the one built in
`StacksFrontier.AlgebraicGeometry.AffineSymmetricAlgebra.Basic` and the one carried by `A`. No
bridging isomorphism is interposed and none is needed: the base spelling
`Sheaf.toRingCat (Opens.grothendieckTopology ↥(Spec R)) (Spec R).sheaf = (Spec R).ringCatSheaf`
also holds by `rfl`.

The statements are phrased through the transpose
`ModuleCat.tilde.adjunction.homEquiv`, which is likewise definitional:
`((tilde.adjunction.homEquiv N G) f).hom x` is `(f.val.app (op ⊤)).hom ((tilde.toOpen N ⊤).hom x)`.
Each proof therefore reduces by `change` to a statement about the section of the comparison
over `⊤`, where the universal property applies.

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
  (A : SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥(Spec R)) (tilde M))

/-- **The affine symmetric-power comparison.** The associated sheaf of the `n`-th symmetric
power of `M` is the `n`-th symmetric power of `M̃`. -/
@[stacks 01I8 "symmetric_power"]
def tildeSymmetricPowerIso (n : ℕ) :
    (tilde (ModuleCat.of R (SymPow.symmetricPower n R M)) :
        SheafOfModules.{u} (Spec R).ringCatSheaf) ≅ A.symmetricPower n :=
  (isSymmetricAlgebra M).pieceIso A.symmetric_isSymmetricAlgebra (n : ℤ)

/-- The forward map of `tildeSymmetricPowerIso M A n` is that of the canonical comparison
`SheafOfModules.GradedAlgebra.IsSymmetricAlgebra.pieceIso` in degree `n`. -/
theorem tildeSymmetricPowerIso_hom (n : ℕ) :
    (tildeSymmetricPowerIso M A n).hom =
      ((isSymmetricAlgebra M).pieceIso A.symmetric_isSymmetricAlgebra (n : ℤ)).hom :=
  rfl

/-! ### The degree-one generator on global sections -/

/-- The degree-one generator of `Stacks.SymGraded.symAlgebra M`, read on a section of `M̃` in
the image of `ModuleCat.tilde.toOpen`. -/
theorem symGen_toOpen (U : (Spec R).Opens) (m : M) :
    (symGen M).val.app (op U) ((tilde.toOpen M U).hom m) =
      AffineBaseChange.toOpenₗ (pieceModule M 1) U (ιG (R := R) M m) := by
  have h := pieceCmp_one_tmul_ιG M (op U) m
  rw [AffineBaseChange.toTilde_app, AffineBaseChange.toTildeₗ_tmul, one_smul,
    AffineBaseChange.toTildeₗ_tmul, one_smul] at h
  exact h.symm

/-- On sections over an open `U`, the degree-one comparison `pieceIso` takes the algebraic
generator of `m : M` to the image of `m` under the generator `A.symmetricGenerator`. -/
theorem pieceIso_toOpen_ιG (U : (Spec R).Opens) (m : M) :
    ((isSymmetricAlgebra M).pieceIso A.symmetric_isSymmetricAlgebra 1).hom.val.app (op U)
        (AffineBaseChange.toOpenₗ (pieceModule M 1) U (ιG (R := R) M m)) =
      A.symmetricGenerator.val.app (op U) ((tilde.toOpen M U).hom m) := by
  rw [← symGen_toOpen M U m]
  exact congrArg (fun h : (tilde M : SheafOfModules.{u} (Spec R).ringCatSheaf) ⟶
        A.symmetric.piece 1 =>
      h.val.app (op U) ((tilde.toOpen M U).hom m))
    (SheafOfModules.GradedAlgebra.IsUniversal.pieceIso_generator
      (isSymmetricAlgebra M) A.symmetric_isSymmetricAlgebra)

/-! ### The tagged statements in degrees zero and one -/

/-- The transpose of the comparison, evaluated at `x`, is its section over `⊤` at the image of `x`
under `tilde.toOpen`. -/
private theorem homEquiv_tildeSymmetricPowerIso_hom (n : ℕ) (x : SymPow.symmetricPower n R M) :
    (((tilde.adjunction (R := R)).homEquiv
      (ModuleCat.of R (SymPow.symmetricPower n R M)) (A.symmetricPower n))
      (tildeSymmetricPowerIso M A n).hom).hom x =
      (tildeSymmetricPowerIso M A n).hom.val.app (op (⊤ : Opens (Spec R).carrier))
        ((tilde.toOpen (ModuleCat.of R (SymPow.symmetricPower n R M)) ⊤).hom x) :=
  rfl

/-- **In degree zero the comparison takes the algebraic unit to the unit of the symmetric
algebra sheaf.** -/
@[stacks 01I8 "symmetric_power"]
theorem tildeSymmetricPowerIso_unit :
    let x : SymPow.symmetricPower 0 R M := ⟨1, one_mem_gradedPiece (R := R) M⟩
    (((tilde.adjunction (R := R)).homEquiv
      (ModuleCat.of R (SymPow.symmetricPower 0 R M))
      (A.symmetricPower 0))
      (tildeSymmetricPowerIso M A 0).hom).hom x =
        A.symmetric.one.eval (.op (⊤ : Opens (Spec R).carrier)) := by
  intro x
  have h1 : (tilde.toOpen (ModuleCat.of R (SymPow.symmetricPower 0 R M)) ⊤).hom x =
      (symAlgebra M).one.eval (.op (⊤ : Opens (Spec R).carrier)) := by
    rw [symAlgebra_one_eval, AffineBaseChange.toTilde_app, AffineBaseChange.toTildeₗ_tmul,
      one_smul]
    rfl
  rw [homEquiv_tildeSymmetricPowerIso_hom, h1]
  exact SheafOfModules.GradedAlgebra.IsUniversal.pieceIso_one
    (isSymmetricAlgebra M) A.symmetric_isSymmetricAlgebra (op ⊤)

/-- **In degree one the comparison takes an algebraic generator to the corresponding generator
of the symmetric algebra sheaf.** -/
@[stacks 01I8 "symmetric_power"]
theorem tildeSymmetricPowerIso_generator (m : M) :
    let x : SymPow.symmetricPower 1 R M :=
      ⟨SymmetricAlgebra.ι R M m, ι_mem_gradedPiece_one (R := R) M m⟩
    (((tilde.adjunction (R := R)).homEquiv
      (ModuleCat.of R (SymPow.symmetricPower 1 R M))
      (A.symmetricPower 1))
      (tildeSymmetricPowerIso M A 1).hom).hom x =
        (A.symmetricGenerator.val.app (.op (⊤ : Opens (Spec R).carrier)))
          ((tilde.toOpen M ⊤).hom m) := by
  intro x
  rw [homEquiv_tildeSymmetricPowerIso_hom]
  exact pieceIso_toOpen_ιG M A ⊤ m

end Stacks.SymGraded
