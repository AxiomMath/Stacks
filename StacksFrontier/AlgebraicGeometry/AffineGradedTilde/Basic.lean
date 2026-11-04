module

public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.PullbackSpecGradedAlgebra
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Bridge
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Transport
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Assembled

/-!
# A nonnegatively graded algebra on an affine scheme, as relative `Proj` data

Let `R` be a commutative ring and `A = ⨁_{n ≥ 0} 𝒜 n` a commutative graded `R`-algebra.
`Stacks.SpecGraded.specGradedAlgebra` attaches to a `ℤ`-graded `R`-algebra the sheaf of graded
`𝒪_{Spec R}`-algebras whose degree-`n` piece is `(𝒢 n)~`. **This file applies it to the grading of
`A` extended by zero to negative degrees
(`Stacks.AlgebraicGeometry.GradedProperCohomology.intExtend`) and packages the result as the
input of the relative `Proj` construction (Situation 01NN)**: a commutative, nonnegatively
graded, quasi-coherent graded `𝒪_{Spec R}`-algebra.

## Main definitions

* `Stacks.AffineGradedTilde.sheafGradedAlgebra`: `⨁ (𝒜 n)~` as relative `Proj` data.

## Main results

* `Stacks.AffineGradedTilde.isCommutative_specGradedAlgebra` and
  `Stacks.AffineGradedTilde.vanishesInNegativeDegrees_specGradedAlgebra`: the hypotheses of
  Situation 01NN.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.SheafSymmetricAlgebra
open Stacks.AlgebraicGeometry.GradedProperCohomology (intExtend intExtend_neg)
open Stacks.SpecGraded (specGradedAlgebra)
open scoped TensorProduct

universe u

namespace Stacks.AffineGradedTilde

variable {R : CommRingCat.{u}} {A : Type u} [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [_root_.GradedAlgebra 𝒜]

/-- The multiplication of `⨁ (𝒜 n)~` is commutative. -/
theorem isCommutative_specGradedAlgebra : IsCommutative (specGradedAlgebra (intExtend 𝒜)) :=
  fun i j U a b => SpecGraded.specGradedAlgebra_mul_comm (intExtend 𝒜) i j U a b

/-- `⨁ (𝒜 n)~` is concentrated in nonnegative degrees. -/
theorem vanishesInNegativeDegrees_specGradedAlgebra :
    VanishesInNegativeDegrees (specGradedAlgebra (intExtend 𝒜)) :=
  fun n hn U x => by
    have hz := SpecGraded.isZero_specGradedAlgebra_piece (intExtend 𝒜) (intExtend_neg 𝒜 hn)
    exact congrArg (fun φ : (specGradedAlgebra (intExtend 𝒜)).piece n ⟶
        (specGradedAlgebra (intExtend 𝒜)).piece n => φ.val.app U x) (hz.eq_of_src (𝟙 _) 0)

/-- **The graded algebra `A` as relative `Proj` data on `Spec R`**: the commutative,
nonnegatively graded, quasi-coherent graded `𝒪_{Spec R}`-algebra `⨁ (𝒜 n)~`. -/
def sheafGradedAlgebra : SheafGradedAlgebra (Spec R) :=
  toSheafGradedAlgebra (specGradedAlgebra (intExtend 𝒜)) (isCommutative_specGradedAlgebra 𝒜)
    (vanishesInNegativeDegrees_specGradedAlgebra 𝒜)
    (SpecGraded.isQuasicoherent_specGradedAlgebra_piece (intExtend 𝒜))

/-- On an open `U`, the multiplication `(𝒜 i)~ ⊗ (𝒜 j)~ → (𝒜 (i + j))~` of
`sheafGradedAlgebra 𝒜` is that of `specGradedAlgebra (intExtend 𝒜)`. -/
theorem sheafGradedAlgebra_mul_app (i j : ℤ) (U : (Spec R).Opens) :
    ((sheafGradedAlgebra 𝒜).mul i j).app U =
      ((specGradedAlgebra (intExtend 𝒜)).mul i j).app (op U) := rfl

end Stacks.AffineGradedTilde

end
