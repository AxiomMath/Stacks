module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Scheme
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Bridge
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Site
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Transport
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Assembled
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The symmetric algebra of a module on an arbitrary scheme

Let `X` be a scheme and `E` an `𝒪_X`-module. The degreewise sheafification of the sectionwise
symmetric algebra of `E` is `AlgebraicGeometry.Scheme.Modules.symmetricAlgebra X E`. This file
proves that it is commutative and concentrated in nonnegative degrees, and exhibits the
projective bundle `P(E) = Proj_X(Sym(E))` as the relative homogeneous spectrum of that algebra
given quasi-coherence of its homogeneous pieces.

Quasi-coherence of all the pieces is equivalent to quasi-coherence of `E`: the degree-one piece
is isomorphic to `E`, and conversely `Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent`
proves it for every quasi-coherent `E`.

## Main definitions

* `Stacks.SymGraded.IsQuasicoherentPieces`: quasi-coherence of all the homogeneous pieces.
* `Stacks.SymGraded.schemeSheafGradedAlgebra`: that algebra as a quasi-coherent graded
  `𝒪_X`-algebra, given quasi-coherence of the pieces.
* `Stacks.SymGraded.schemeProjectiveBundle`: `P(E) = Proj_X(Sym(E))` on an arbitrary scheme,
  with its projection and its affine Proj charts, given the same.

## Main results

* `Stacks.SymGraded.isCommutative_symmetricAlgebra`: the multiplication is commutative in every
  pair of degrees.
* `Stacks.SymGraded.pairwiseCommutes_symmetricAlgebraGen`: the degree-one local sections in the
  image of the generator commute pairwise.
* `Stacks.SymGraded.vanishesInNegativeDegrees_symmetricAlgebra`: every local section of a
  negative-degree piece vanishes.
* `Stacks.SymGraded.isQuasicoherentPieces_of_restrict_affineOpens`: the quasi-coherence
  hypothesis is affine-local.
* `Stacks.SymGraded.symmetricAlgebra_piece`: the degree-`n` piece is the sheafification of
  `U ↦ Sym^n_{Γ(X, U)}(Γ(E, U))`.
* `Stacks.SymGraded.symmetricAlgebra_one_eval` and `Stacks.SymGraded.symmetricAlgebra_mul_unit`:
  the unit and the multiplication on unit-images of sectionwise sections are the unit-images of
  the sectionwise unit and product.
* `Stacks.SymGraded.schemeProjectiveBundle_isPullback` and
  `Stacks.SymGraded.schemeProjectiveBundle_chart_transition`: the charts are the inverse images
  of the affine opens and are compatible with restriction of homogeneous sections.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.SheafSymmetricAlgebra

namespace Stacks.SymGraded

universe u

variable {X : Scheme.{u}} (E : X.Modules)

/-! ### The sheafified sectionwise symmetric algebra

`Sym(E)` is `AlgebraicGeometry.Scheme.Modules.symmetricAlgebra X E`; the identities below read its
unit, multiplication and pieces off the sectionwise algebra it sheafifies. -/

/-- **The unit of `Sym(E)` is the unit-image of the sectionwise unit.** -/
theorem symmetricAlgebra_one_eval (U : (Opens X.carrier)ᵒᵖ) :
    (Scheme.Modules.symmetricAlgebra X E).one.eval U =
      PresheafOfModules.Hom.app
        (PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj) (siteGradedPiece E.val 0)) U
        ((sitePresheafAlgebra E.val).one.eval U) :=
  rfl

/-- **The multiplication of `Sym(E)` on the unit-images of two sectionwise homogeneous local
sections is the unit-image of their sectionwise product.** -/
theorem symmetricAlgebra_mul_unit (i j : ℤ) (U : (Opens X.carrier)ᵒᵖ)
    (x : (siteGradedPiece E.val i).obj U) (y : (siteGradedPiece E.val j).obj U) :
    ((Scheme.Modules.symmetricAlgebra X E).mul i j).app U
        (PresheafOfModules.Hom.app
          (PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj) (siteGradedPiece E.val i)) U x)
        (PresheafOfModules.Hom.app
          (PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj) (siteGradedPiece E.val j)) U y) =
      PresheafOfModules.Hom.app
        (PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj) (siteGradedPiece E.val (i + j))) U
        ((siteMul E.val i j).app U x y) :=
  (sitePresheafAlgebra E.val).sheafify_mul_unit (𝟙 X.ringCatSheaf.obj) i j U x y

/-- **The degree-`n` piece is the sheafification of `U ↦ Sym^n_{Γ(X, U)}(Γ(E, U))`.** -/
theorem symmetricAlgebra_piece (n : ℤ) :
    (Scheme.Modules.symmetricAlgebra X E).piece n =
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
        (siteGradedPiece E.val n) := rfl

/-- **The multiplication of `Sym(E)` is commutative**, in every pair of degrees. -/
theorem isCommutative_symmetricAlgebra :
    IsCommutative (Scheme.Modules.symmetricAlgebra X E) := fun i j U a b =>
  (sitePresheafAlgebra E.val).heq_sheafify_mul_comm (𝟙 X.ringCatSheaf.obj)
    (fun i j Y x y => siteMul_comm E.val i j Y x y) i j U.unop a b

/-- **`Sym(E)` is concentrated in nonnegative degrees**: every local section of a negative-degree
piece vanishes. -/
theorem vanishesInNegativeDegrees_symmetricAlgebra :
    VanishesInNegativeDegrees (Scheme.Modules.symmetricAlgebra X E) := by
  intro n hn U x
  refine Stacks.eq_of_isSeparated ((Scheme.Modules.symmetricAlgebra X E).piece n)
    (Stacks.liftSieve_mem (𝟙 X.ringCatSheaf.obj) (siteGradedPiece E.val n) x) ?_
  rintro Y f ⟨t, ht⟩
  have ht' : PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit
      (𝟙 X.ringCatSheaf.obj) (siteGradedPiece E.val n)) (op Y) t =
    ((Scheme.Modules.symmetricAlgebra X E).piece n).val.map f.op x := ht
  rw [← ht', siteGradedPiece_eq_zero_of_neg E.val hn (op Y) t]
  simp only [map_zero]
  rfl

/-! ### The degree-one generator

The generator `E ⟶ Sym(E)₁` is `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraGen X E`. -/

/-- **The degree-one local sections in the image of the generator commute pairwise**, which is
the half of the universal property of the symmetric algebra that cuts it out of the tensor
algebra. -/
theorem pairwiseCommutes_symmetricAlgebraGen :
    SheafOfModules.GradedAlgebra.PairwiseCommutes
      (Scheme.Modules.symmetricAlgebraGen X E) := fun U _ _ =>
  (sitePresheafAlgebra E.val).pairwiseCommutes_sheafifyGen (𝟙 X.ringCatSheaf.obj)
    (siteGen E.val) (genCommutes_siteGen E.val) U _ _

/-! ### The projective bundle, given quasi-coherence -/

/-- **Quasi-coherence of every homogeneous piece of `Sym(E)`.** -/
def IsQuasicoherentPieces : Prop :=
  ∀ n : ℤ, (((Scheme.Modules.symmetricAlgebra X E).piece n : X.Modules)).IsQuasicoherent

/-- **The hypothesis is affine-local.** It suffices that the restriction of every homogeneous
piece to every affine open is quasi-coherent. -/
theorem isQuasicoherentPieces_of_restrict_affineOpens
    (h : ∀ (n : ℤ) (V : X.affineOpens),
      ((Scheme.Modules.restrictFunctor (V : X.Opens).ι).obj
        ((Scheme.Modules.symmetricAlgebra X E).piece n : X.Modules)).IsQuasicoherent) :
    IsQuasicoherentPieces E := fun n =>
  Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_restrict_affineOpens _ (h n)

variable (hqc : IsQuasicoherentPieces E)

/-- **`Sym(E)` as sheaf-level graded algebra data on an arbitrary scheme**: a commutative,
nonnegatively graded, quasi-coherent graded `𝒪_X`-algebra. -/
def schemeSheafGradedAlgebra : SheafGradedAlgebra X :=
  toSheafGradedAlgebra (Scheme.Modules.symmetricAlgebra X E) (isCommutative_symmetricAlgebra E)
    (vanishesInNegativeDegrees_symmetricAlgebra E) hqc

/-- The degree-`n` piece of the data is the degree-`n` piece of `Sym(E)`. -/
theorem schemeSheafGradedAlgebra_piece (n : ℤ) :
    (schemeSheafGradedAlgebra E hqc).piece n =
      (Scheme.Modules.symmetricAlgebra X E).piece n := rfl

/-- The multiplication of the data is the multiplication of `Sym(E)`. -/
theorem schemeSheafGradedAlgebra_mul_app (i j : ℤ) (U : X.Opens) :
    ((schemeSheafGradedAlgebra E hqc).mul i j).app U =
      ((Scheme.Modules.symmetricAlgebra X E).mul i j).app (op U) := rfl

/-- **The projective bundle `P(E) = Proj_X(Sym(E))`** of a module on an arbitrary scheme,
together with its projection to `X` and its affine Proj charts: the relative Proj
`Stacks.AlgebraicGeometry.RelativeProj.relativeProj` of the sheafified sectionwise symmetric
algebra of `E`. -/
@[ega "II 8.3.1" "special case"]
def schemeProjectiveBundle :
    Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData
      (schemeSheafGradedAlgebra E hqc) :=
  Stacks.AlgebraicGeometry.RelativeProj.relativeProj (schemeSheafGradedAlgebra E hqc)

/-- The projection of the projective bundle to its base. -/
def schemeProjectiveBundleToBase : (schemeProjectiveBundle E hqc).scheme ⟶ X :=
  (schemeProjectiveBundle E hqc).toBase

/-- **Each chart of the projective bundle is the inverse image of its affine open.** -/
theorem schemeProjectiveBundle_isPullback (U : X.Opens) (hU : IsAffineOpen U) :
    IsPullback ((schemeProjectiveBundle E hqc).chart U hU)
      (Stacks.AlgebraicGeometry.RelativeProj.projInclusionToOpen
        (schemeSheafGradedAlgebra E hqc) U hU)
      (schemeProjectiveBundleToBase E hqc) U.ι :=
  (schemeProjectiveBundle E hqc).chart_isPullback U hU

/-- **The charts are compatible with restriction of homogeneous sections.** -/
theorem schemeProjectiveBundle_chart_transition (U V : X.Opens) (h : U ≤ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    Stacks.AlgebraicGeometry.RelativeProj.projInclusionMap
        (schemeSheafGradedAlgebra E hqc) U V h hU hV ≫
      (schemeProjectiveBundle E hqc).chart V hV =
      (schemeProjectiveBundle E hqc).chart U hU :=
  (schemeProjectiveBundle E hqc).chart_transition U V h hU hV

end Stacks.SymGraded

end
