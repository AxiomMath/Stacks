module

public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Bridge
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Transport
public import StacksFrontier.AlgebraicGeometry.AffineSymmetricAlgebra.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Assembled

/-!
# The symmetric algebra of a quasi-coherent module on an affine base, as relative Proj data

Let `R` be a commutative ring and `M` an `R`-module. `Stacks.SymGraded.symAlgebra M` is the sheaf
of graded `𝒪_{Spec R}`-algebras whose degree-`n` homogeneous piece is `Sym^n_R(M)~`. **This file
turns it into sheaf-level graded algebra data in the sense of Situation 01NN and takes its
relative homogeneous spectrum**, which is the projective bundle `P(M~)` over `Spec R`, with its
projection and its affine Proj charts.

Three things have to be supplied beyond what the construction of `symAlgebra` records.

* **Commutativity in every pair of degrees.** What the construction records is
  `Stacks.SymGraded.pairwiseCommutes_symGen`, commutation of two degree-*one* generators, which
  is the half of the universal property cutting the symmetric algebra out of the tensor algebra.
  Situation 01NN needs the multiplication itself to be commutative, in every pair of degrees.
  That is proved here from commutativity of `SymmetricAlgebra R M`, carried through the
  base-change presheaves by `Stacks.SymGraded.mulSec_comm` and then through the comparison by
  `Stacks.GradedAlgebra.heq_ofComparison_mul_comm`.
* **Vanishing in negative degrees.** This is
  `Stacks.SymGraded.symAlgebra_piece_eq_zero_of_neg`, restated as a zero object.
* **Quasi-coherence of every piece.** Each piece *is* an associated sheaf, so this is Mathlib's
  instance for `AlgebraicGeometry.tilde`.

## Main definitions

* `Stacks.SymGraded.symSheafGradedAlgebra`: **`Sym(M~)` as the input of relative Proj.**
* `Stacks.SymGraded.projectiveBundle`: **`P(M~) = Proj_{Spec R}(Sym(M~))`**, with its projection
  to `Spec R` and its affine Proj charts.
* `Stacks.SymGraded.projectiveBundleToBase`: that projection.

## Main results

* `Stacks.SymGraded.symMulₗ_comm` and `Stacks.SymGraded.mulSec_comm`: commutativity of the graded
  multiplication of the symmetric algebra, and of its base change, as heterogeneous equalities.
* `Stacks.SymGraded.isCommutative_symAlgebra`: commutativity of `symAlgebra M`.
* `Stacks.SymGraded.symSheafGradedAlgebra_piece`: the degree-`n` piece of the data is
  `Sym^n_R(M)~`, on the nose.
* `Stacks.SymGraded.projectiveBundle_isPullback`: each chart of the bundle is the inverse image
  of its affine open — the defining property of the charts, inherited from Tag 01NQ.

## Implementation notes

**Degrees are `ℤ` and `i + j` is not `j + i`.** Every commutativity statement here is a
heterogeneous equality: the two sides are sections of the pieces of degrees `i + j` and `j + i`,
which are equal integers but not definitionally equal terms. The three levels are bridged by the
three transport lemmas of the existing development: `Stacks.SymGraded.heq_gradedPiece_of_eq` at
the level of submodules of `SymmetricAlgebra R M`, `Stacks.SymGraded.heq_tensor_of_eq` at the
level of base changes of those submodules, and `Stacks.heq_of_isSeparated` at the level of
sheaves.

**The site index.** `Stacks.GradedAlgebra.heq_ofComparison_mul_comm` is stated at `op X` for an
open `X`, because the sieve-restriction argument it runs produces `(op X).unop` where a statement
quantified over `(Opens)ᵒᵖ` would need `X` itself, and the two are equal only by a reduction that
`rewrite` does not perform. Applying it at `U.unop` for `U` in the opposite category is accepted
by `exact`, which is how `isCommutative_symAlgebra` is proved.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)

## Not done here

**No tag is claimed, and in particular not 01OB.** Tag 01OB is the projective bundle of a
quasi-coherent module on an arbitrary scheme. What is built here is the projective bundle of an
*associated sheaf on an affine scheme*, which is the special case `S = Spec R`, `E = M~`. The
general case needs the symmetric algebra of a quasi-coherent module on an arbitrary scheme; the
two declarations it is missing are named in the `Not done here` section of
`StacksFrontier/AlgebraicGeometry/SheafSymmetricAlgebra/Qcoh.lean`, which also extends what is
built here from an associated sheaf to an arbitrary quasi-coherent module on the affine base.

Tag 01NQ is not claimed either: the relative homogeneous spectrum is
`Stacks.AlgebraicGeometry.RelativeProj.relativeProj`, which already carries that tag; this
file only supplies its input.

The twists of the bundle are not built. `Stacks.AlgebraicGeometry.RelativeProj` has no
twist construction over `SheafGradedAlgebra` data, so `projectiveBundleTwist` of Tag 01OB and
its invertibility are untouched.

This bundle **is** identified with a `Proj` of a polynomial ring when `M` is free, by
`Stacks.SymGraded.projectiveBundleIsoProjectiveSpaceOverRing` of
`StacksFrontier/AlgebraicGeometry/SheafSymmetricAlgebra/ProjComparison.lean`, which goes through
`Stacks.SymGraded.globalSectionsRingEquiv` of
`StacksFrontier/AlgebraicGeometry/SheafSymmetricAlgebra/GlobalSections.lean` — the graded ring of
global sections of `Sym(M~)` is `Sym_R(M)`. Nothing is proved about the bundle's functoriality
in `M`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.SheafSymmetricAlgebra
open scoped TensorProduct

namespace Stacks.SymGraded

universe u

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

/-! ### Commutativity of the graded multiplication -/

/-- Two homogeneous elements of `SymmetricAlgebra R M` whose degrees are equal and whose
underlying elements are equal are heterogeneously equal. -/
public theorem heq_gradedPiece_of_eq {i j : ℤ} (h : i = j) {x : gradedPiece (R := R) M i}
    {y : gradedPiece (R := R) M j}
    (hxy : (x : SymmetricAlgebra R M) = (y : SymmetricAlgebra R M)) : HEq x y := by
  subst h
  exact heq_of_eq (Subtype.ext hxy)

/-- The underlying elements of `x * y` and `y * x` in `SymmetricAlgebra R M` agree. -/
private theorem coe_symMulₗ_comm (i j : ℤ) (x : gradedPiece (R := R) M i)
    (y : gradedPiece (R := R) M j) :
    ((symMulₗ (R := R) M i j x y : gradedPiece (R := R) M (i + j)) : SymmetricAlgebra R M) =
      (symMulₗ (R := R) M j i y x : gradedPiece (R := R) M (j + i)) := by
  simp only [symMulₗ_coe, mul_comm]

/-- **The graded multiplication of the symmetric algebra is commutative**, in every pair of
degrees. -/
public theorem symMulₗ_comm (i j : ℤ) (x : gradedPiece (R := R) M i)
    (y : gradedPiece (R := R) M j) :
    HEq (symMulₗ (R := R) M i j x y) (symMulₗ (R := R) M j i y x) :=
  heq_gradedPiece_of_eq M (add_comm i j)
    (coe_symMulₗ_comm M i j x y)

/-- **The base change of the graded multiplication is commutative.** -/
public theorem mulSec_comm (U : ((Spec R).Opens)ᵒᵖ) (i j : ℤ)
    (x : Γ(Spec R, U.unop) ⊗[R] gradedPiece (R := R) M i)
    (y : Γ(Spec R, U.unop) ⊗[R] gradedPiece (R := R) M j) :
    HEq (mulSec M U i j x y) (mulSec M U j i y x) := by
  refine heq_tensor_of_eq (congrArg (gradedPiece (R := R) M) (add_comm i j)) ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x₀ =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b y₀ =>
          rw [mulSec_tmul, mulSec_tmul, tensorCongr_tmul, mul_comm a b]
          exact congrArg (fun z : gradedPiece (R := R) M (j + i) => (b * a) ⊗ₜ[R] z)
            (Subtype.ext (coe_symMulₗ_comm M i j x₀ y₀))
      | add y y' hy hy' =>
          simp [hy, hy']
  | add x x' hx hx' =>
      simp [hx, hx']

/-- **The multiplication of `symAlgebra M` is commutative.** -/
public theorem isCommutative_symAlgebra : IsCommutative (symAlgebra M) := fun i j U a b =>
  (presheafAlgebra M).heq_ofComparison_mul_comm (pieceSheaf M) (pieceCmp M)
    (fun i j X x y => mulSec_comm M X i j x y) i j U.unop a b

/-- **`symAlgebra M` is concentrated in nonnegative degrees.** -/
public theorem vanishesInNegativeDegrees_symAlgebra :
    VanishesInNegativeDegrees (symAlgebra M) := fun _ hn U x =>
  symAlgebra_piece_eq_zero_of_neg M hn U x

/-- Every homogeneous piece of `symAlgebra M` is quasi-coherent: it is an associated sheaf. -/
public instance isQuasicoherent_symAlgebra_piece (n : ℤ) :
    (((symAlgebra M).piece n : (Spec R).Modules)).IsQuasicoherent :=
  inferInstanceAs ((tilde (pieceModule M n)).IsQuasicoherent)

/-! ### The symmetric algebra as relative Proj data -/

/-- **`Sym(M~)` as sheaf-level graded algebra data on `Spec R`**, the input of the relative Proj
construction: a commutative, nonnegatively graded, quasi-coherent graded `𝒪_{Spec R}`-algebra. -/
public def symSheafGradedAlgebra : SheafGradedAlgebra (Spec R) :=
  toSheafGradedAlgebra (symAlgebra M) (isCommutative_symAlgebra M)
    (vanishesInNegativeDegrees_symAlgebra M) (isQuasicoherent_symAlgebra_piece M)

/-- **The degree-`n` piece of the data is the associated sheaf of the `n`-th symmetric power**,
on the nose. -/
public theorem symSheafGradedAlgebra_piece (n : ℤ) :
    (symSheafGradedAlgebra M).piece n = pieceSheaf M n := rfl

/-- The degree-`n` piece, for `n` a natural number, is `Sym^n_R(M)~`. -/
public theorem symSheafGradedAlgebra_piece_natCast (n : ℕ) :
    (symSheafGradedAlgebra M).piece (n : ℤ) =
      tilde (ModuleCat.of R (SymPow.symmetricPower n R M)) := rfl

/-- The multiplication of the data is the multiplication of `symAlgebra M`. -/
public theorem symSheafGradedAlgebra_mul_app (i j : ℤ) (U : (Spec R).Opens) :
    ((symSheafGradedAlgebra M).mul i j).app U = ((symAlgebra M).mul i j).app (op U) := rfl

/-! ### The projective bundle over an affine base -/

/-- **The projective bundle `P(M~) = Proj_{Spec R}(Sym(M~))`**, together with its projection to
`Spec R` and its affine Proj charts.

This is `Stacks.AlgebraicGeometry.RelativeProj.relativeProj`, Tag 01NQ, applied to the
symmetric algebra. -/
public def projectiveBundle :
    Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData (symSheafGradedAlgebra M) :=
  Stacks.AlgebraicGeometry.RelativeProj.relativeProj (symSheafGradedAlgebra M)

/-- The projection of the projective bundle to its base. -/
public def projectiveBundleToBase : (projectiveBundle M).scheme ⟶ Spec R :=
  (projectiveBundle M).toBase

/-- **Each chart of the projective bundle is the inverse image of its affine open.** -/
public theorem projectiveBundle_isPullback (U : (Spec R).Opens) (hU : IsAffineOpen U) :
    IsPullback ((projectiveBundle M).chart U hU)
      (Stacks.AlgebraicGeometry.RelativeProj.projInclusionToOpen
        (symSheafGradedAlgebra M) U hU)
      (projectiveBundleToBase M) U.ι :=
  (projectiveBundle M).chart_isPullback U hU

/-- **The charts of the projective bundle are compatible with restriction of sections.** -/
public theorem projectiveBundle_chart_transition (U V : (Spec R).Opens) (h : U ≤ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    Stacks.AlgebraicGeometry.RelativeProj.projInclusionMap
        (symSheafGradedAlgebra M) U V h hU hV ≫ (projectiveBundle M).chart V hV =
      (projectiveBundle M).chart U hU :=
  (projectiveBundle M).chart_transition U V h hU hV

end Stacks.SymGraded

end
