module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitStageTriple
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitTwoGeneratorSquare
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorNoetherianCorners
public import StacksFrontier.AlgebraicGeometry.ProjAmple.Basic

/-!
# The ordinary triple an object of the fibre product of Tag 0EXD descends to, at Example 0EVH

Let `A` be a ring with `p = 0` in `A` for a prime `p`, and `f₁, f₂ ∈ A`. Every object of the
categorical fibre product of [Stacks, Tag 0EXD] at the almost blowup square of
[Stacks, Example 0EVH], the target of `AlgebraicGeometry.twoGeneratorFrobeniusColimitComparison`,
is isomorphic to the object attached to a triple of ordinary finite locally free modules
(replacing the triple `(ℱ, 𝒢, φ)` of `colim_F`-modules). No Noetherian hypothesis is needed, in
contrast with the reduction of [Stacks, Tag 0B8W].

## Main results

* `AlgebraicGeometry.exists_twoGeneratorFrobeniusColimitStageTriple_iso`: every object of the
  categorical fibre product of [Stacks, Tag 0EXD] at the square of [Stacks, Example 0EVH] is
  isomorphic to the object attached to a triple of ordinary finite locally free modules.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
* [Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius Stacks.AlmostBlowUp

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable (A : Type u) [CommRing A] (f₁ f₂ : A) (p : ℕ) [Fact p.Prime] (hpA : (p : A) = 0)

include hpA

/-- Every object `T` of the categorical fibre product of [Stacks, Tag 0EXD] at the square of
[Stacks, Example 0EVH], the target of `AlgebraicGeometry.twoGeneratorFrobeniusColimitComparison`,
is isomorphic to the object attached to a finite locally free module `Ec` on the centre
`Z = Spec (A/(f₁,f₂))`, a finite locally free module `Em` on the modification
`X' = Proj (A[T₀,T₁]/(f₂T₀-f₁T₁))`, and an isomorphism `psi` of the `j`-fold Frobenius pullbacks
of their restrictions to the exceptional line `E = 𝐏¹_Z`. -/
theorem exists_twoGeneratorFrobeniusColimitStageTriple_iso
    (T : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      CategoricalPullback
        (frobeniusColimitVectorBundlesPullback p (exceptionalToCenter A f₁ f₂)
          (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
          (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA))
        (frobeniusColimitVectorBundlesPullback p (exceptionalToModification A f₁ f₂)
          (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
          (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA))) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    ∃ (n j : ℕ) (Ec : (Spec (.of (centerRing A f₁ f₂))).Vect)
      (Em : (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).Vect)
      (psi : (frobeniusPullbackIter (AlgebraicGeometry.Proj (exceptionalGrading A f₁ f₂)) p
            (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA) j).obj
            ((Scheme.Vect.pullback (exceptionalToCenter A f₁ f₂)).obj Ec) ≅
          (frobeniusPullbackIter (AlgebraicGeometry.Proj (exceptionalGrading A f₁ f₂)) p
            (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA) j).obj
            ((Scheme.Vect.pullback (exceptionalToModification A f₁ f₂)).obj Em)),
      Nonempty (T ≅ frobeniusColimitStageTriple p (exceptionalToCenter A f₁ f₂)
        (exceptionalToModification A f₁ f₂)
        (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)
        (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)
        (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA) n j Ec Em psi) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  have hMc : CompactSpace (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)) :=
    compactSpace_proj_modificationGrading A f₁ f₂
  have hEc : CompactSpace (AlgebraicGeometry.Proj (exceptionalGrading A f₁ f₂)) :=
    Stacks.ProjAmple.compactSpace_proj_polyGrading (centerRing A f₁ f₂) 1
  exact exists_frobeniusColimitStageTriple_iso p (exceptionalToCenter A f₁ f₂)
    (exceptionalToModification A f₁ f₂)
    (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)
    (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)
    (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA) T

end AlgebraicGeometry

end
