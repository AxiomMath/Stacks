module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitTwoGeneratorSquare
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectCatPullbackLoc
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorCoefficientCube

/-!
# Restricting the fibre product of Tag 0EXD along a change of coefficient algebra

Let `p` be a prime, `A` a ring in which `p` vanishes, `f₁, f₂ ∈ A`, and `B` an `A`-algebra in
which `p` vanishes.  The two-generator square of [Stacks, Example 0EVH] over `B`, at the images of
`f₁, f₂`, maps to the one over `A` by the coefficient morphisms of
`StacksFrontier/AlgebraicGeometry/Blowup/TwoGeneratorCoefficientBaseChange.lean`, and an `A`-algebra
map `φ : B →ₐ[A] B'` gives a morphism from the square over `B'` to the one over `B` by
`StacksFrontier/AlgebraicGeometry/Blowup/TwoGeneratorCoefficientCube.lean`.  This file instantiates
at those two cubes the general restriction functor
`AlgebraicGeometry.frobeniusColimitVectorBundlesCatPullbackLoc` on the categorical fibre products
and the comparison `AlgebraicGeometry.frobeniusColimitVectorBundlesCatPullbackLocIso` of the
comparison functor of [Stacks, Tag 0EXD] with it.

The case of interest is a localisation `B = A_g`: the square over `A_g` is the restriction of the
square over `A` to the basic open `D(g)`, and the restriction functor is how the local hypothesis
of the Zariski glueing in the essential surjectivity half of [Stacks, Tag 0EXD] is stated.

## Main definitions

* `AlgebraicGeometry.twoGeneratorFrobeniusColimitLoc`: restriction along `A → B`.
* `AlgebraicGeometry.twoGeneratorFrobeniusColimitLocIso`: the comparison functor commutes with it.
* `AlgebraicGeometry.twoGeneratorFrobeniusColimitLocOfHom` and
  `AlgebraicGeometry.twoGeneratorFrobeniusColimitLocOfHomIso`: the same along an `A`-algebra map
  `B →ₐ[A] B'`.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Example 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius Stacks.AlmostBlowUp Stacks.ProjectiveCohomology

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable (A : Type u) [CommRing A] (f₁ f₂ : A) (p : ℕ) [Fact p.Prime] (hpA : (p : A) = 0)
  (B : Type u) [CommRing B] [Algebra A B] (hpB : (p : B) = 0)

omit [Fact p.Prime] in
include hpA in
/-- A natural number vanishing in `A` vanishes in every `A`-algebra. -/
theorem natCast_eq_zero_of_algebra (B : Type u) [CommRing B] [Algebra A B] :
    (p : B) = 0 := by
  rw [← map_natCast (algebraMap A B) p, hpA, map_zero]

/-- **Restriction of the categorical fibre product of [Stacks, Tag 0EXD] along `A → B`**: the
module on the centre and the module on the modification are restricted along the coefficient
morphisms of the corners, and the structural isomorphism is conjugated by the two square
comparisons at the exceptional corner. -/
noncomputable def twoGeneratorFrobeniusColimitLoc :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    letI := (twoGeneratorSquare B (algebraMap A B f₁) (algebraMap A B f₂)).modificationGraded
    CategoricalPullback
        (frobeniusColimitVectorBundlesPullback p (exceptionalToCenter A f₁ f₂)
          (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
          (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA))
        (frobeniusColimitVectorBundlesPullback p (exceptionalToModification A f₁ f₂)
          (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
          (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)) ⥤
      CategoricalPullback
        (frobeniusColimitVectorBundlesPullback p
          (exceptionalToCenter B (algebraMap A B f₁) (algebraMap A B f₂))
          (isInCharacteristic_twoGeneratorExceptional B _ _ p hpB)
          (isInCharacteristic_twoGeneratorCenter B _ _ p hpB))
        (frobeniusColimitVectorBundlesPullback p
          (exceptionalToModification B (algebraMap A B f₁) (algebraMap A B f₂))
          (isInCharacteristic_twoGeneratorExceptional B _ _ p hpB)
          (isInCharacteristic_twoGeneratorModification B _ _ p hpB)) :=
  letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
  letI := (twoGeneratorSquare B (algebraMap A B f₁) (algebraMap A B f₂)).modificationGraded
  frobeniusColimitVectorBundlesCatPullbackLoc p (exceptionalToModification A f₁ f₂)
    (exceptionalToCenter A f₁ f₂)
    (exceptionalToModification B (algebraMap A B f₁) (algebraMap A B f₂))
    (exceptionalToCenter B (algebraMap A B f₁) (algebraMap A B f₂))
    (modificationCoeffProjMap A B f₁ f₂) (Spec.map (CommRingCat.ofHom (centerCoeffHom A B f₁ f₂)))
    (projModelMap 1 (centerCoeffHom A B f₁ f₂))
    (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)
    (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)
    (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
    (isInCharacteristic_twoGeneratorModification B _ _ p hpB)
    (isInCharacteristic_twoGeneratorCenter B _ _ p hpB)
    (isInCharacteristic_twoGeneratorExceptional B _ _ p hpB)
    (exceptionalToModification_comp_modificationCoeffProjMap A B f₁ f₂)
    (isPullback_exceptionalToCenter_coeff A B f₁ f₂).w

/-- **The comparison functor of [Stacks, Tag 0EXD] commutes with restriction along `A → B`**:
`Loc (G M) ≅ G_B (ι^* M)`. -/
noncomputable def twoGeneratorFrobeniusColimitLocIso
    (M : frobeniusColimitVectorBundles (Spec (.of A)) p (isInCharacteristic_spec A p hpA)) :
    (twoGeneratorFrobeniusColimitLoc A f₁ f₂ p hpA B hpB).obj
        ((twoGeneratorFrobeniusColimitComparison A f₁ f₂ p hpA).obj M) ≅
      (twoGeneratorFrobeniusColimitComparison B (algebraMap A B f₁) (algebraMap A B f₂) p hpB).obj
        ((frobeniusColimitVectorBundlesPullback p (Spec.map (CommRingCat.ofHom (algebraMap A B)))
          (isInCharacteristic_spec B p hpB) (isInCharacteristic_spec A p hpA)).obj M) :=
  letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
  letI := (twoGeneratorSquare B (algebraMap A B f₁) (algebraMap A B f₂)).modificationGraded
  frobeniusColimitVectorBundlesCatPullbackLocIso p (modificationToBase A f₁ f₂)
    (centerToBase A f₁ f₂) (exceptionalToModification A f₁ f₂) (exceptionalToCenter A f₁ f₂)
    (modificationToBase B (algebraMap A B f₁) (algebraMap A B f₂))
    (centerToBase B (algebraMap A B f₁) (algebraMap A B f₂))
    (exceptionalToModification B (algebraMap A B f₁) (algebraMap A B f₂))
    (exceptionalToCenter B (algebraMap A B f₁) (algebraMap A B f₂))
    (Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (modificationCoeffProjMap A B f₁ f₂) (Spec.map (CommRingCat.ofHom (centerCoeffHom A B f₁ f₂)))
    (projModelMap 1 (centerCoeffHom A B f₁ f₂))
    (isInCharacteristic_spec A p hpA)
    (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)
    (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)
    (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
    (isInCharacteristic_spec B p hpB)
    (isInCharacteristic_twoGeneratorModification B _ _ p hpB)
    (isInCharacteristic_twoGeneratorCenter B _ _ p hpB)
    (isInCharacteristic_twoGeneratorExceptional B _ _ p hpB)
    (exceptionalToModification_comp_modificationCoeffProjMap A B f₁ f₂)
    (isPullback_exceptionalToCenter_coeff A B f₁ f₂).w
    (twoGenerator_isPullback A f₁ f₂).w
    (twoGenerator_isPullback B (algebraMap A B f₁) (algebraMap A B f₂)).w
    (isPullback_modificationToBase_coeff A B f₁ f₂).w
    (isPullback_centerToBase_coeff A B f₁ f₂).w M

section OfHom

variable {B} {B' : Type u} [CommRing B'] [Algebra A B'] (hpB' : (p : B') = 0) (φ : B →ₐ[A] B')

/-- **Restriction of the categorical fibre product of [Stacks, Tag 0EXD] along an `A`-algebra map
`φ : B →ₐ[A] B'`**, through the cube of
`StacksFrontier/AlgebraicGeometry/Blowup/TwoGeneratorCoefficientCube.lean`. -/
noncomputable def twoGeneratorFrobeniusColimitLocOfHom :
    letI := (twoGeneratorSquare B (algebraMap A B f₁) (algebraMap A B f₂)).modificationGraded
    letI := (twoGeneratorSquare B' (algebraMap A B' f₁) (algebraMap A B' f₂)).modificationGraded
    CategoricalPullback
        (frobeniusColimitVectorBundlesPullback p
          (exceptionalToCenter B (algebraMap A B f₁) (algebraMap A B f₂))
          (isInCharacteristic_twoGeneratorExceptional B _ _ p hpB)
          (isInCharacteristic_twoGeneratorCenter B _ _ p hpB))
        (frobeniusColimitVectorBundlesPullback p
          (exceptionalToModification B (algebraMap A B f₁) (algebraMap A B f₂))
          (isInCharacteristic_twoGeneratorExceptional B _ _ p hpB)
          (isInCharacteristic_twoGeneratorModification B _ _ p hpB)) ⥤
      CategoricalPullback
        (frobeniusColimitVectorBundlesPullback p
          (exceptionalToCenter B' (algebraMap A B' f₁) (algebraMap A B' f₂))
          (isInCharacteristic_twoGeneratorExceptional B' _ _ p hpB')
          (isInCharacteristic_twoGeneratorCenter B' _ _ p hpB'))
        (frobeniusColimitVectorBundlesPullback p
          (exceptionalToModification B' (algebraMap A B' f₁) (algebraMap A B' f₂))
          (isInCharacteristic_twoGeneratorExceptional B' _ _ p hpB')
          (isInCharacteristic_twoGeneratorModification B' _ _ p hpB')) :=
  letI := (twoGeneratorSquare B (algebraMap A B f₁) (algebraMap A B f₂)).modificationGraded
  letI := (twoGeneratorSquare B' (algebraMap A B' f₁) (algebraMap A B' f₂)).modificationGraded
  frobeniusColimitVectorBundlesCatPullbackLoc p
    (exceptionalToModification B (algebraMap A B f₁) (algebraMap A B f₂))
    (exceptionalToCenter B (algebraMap A B f₁) (algebraMap A B f₂))
    (exceptionalToModification B' (algebraMap A B' f₁) (algebraMap A B' f₂))
    (exceptionalToCenter B' (algebraMap A B' f₁) (algebraMap A B' f₂))
    (coeffCubeModification A f₁ f₂ φ) (coeffCubeCenter A f₁ f₂ φ)
    (coeffCubeExceptional A f₁ f₂ φ)
    (isInCharacteristic_twoGeneratorModification B _ _ p hpB)
    (isInCharacteristic_twoGeneratorCenter B _ _ p hpB)
    (isInCharacteristic_twoGeneratorExceptional B _ _ p hpB)
    (isInCharacteristic_twoGeneratorModification B' _ _ p hpB')
    (isInCharacteristic_twoGeneratorCenter B' _ _ p hpB')
    (isInCharacteristic_twoGeneratorExceptional B' _ _ p hpB')
    (coeffCube_sq A f₁ f₂ φ) (coeffCube_se A f₁ f₂ φ)

/-- **The comparison functor of [Stacks, Tag 0EXD] commutes with restriction along an `A`-algebra
map `φ : B →ₐ[A] B'`.** -/
noncomputable def twoGeneratorFrobeniusColimitLocOfHomIso
    (M : frobeniusColimitVectorBundles (Spec (.of B)) p (isInCharacteristic_spec B p hpB)) :
    (twoGeneratorFrobeniusColimitLocOfHom A f₁ f₂ p hpB hpB' φ).obj
        ((twoGeneratorFrobeniusColimitComparison B (algebraMap A B f₁) (algebraMap A B f₂)
          p hpB).obj M) ≅
      (twoGeneratorFrobeniusColimitComparison B' (algebraMap A B' f₁) (algebraMap A B' f₂)
          p hpB').obj
        ((frobeniusColimitVectorBundlesPullback p (coeffCubeBase A φ)
          (isInCharacteristic_spec B' p hpB') (isInCharacteristic_spec B p hpB)).obj M) :=
  letI := (twoGeneratorSquare B (algebraMap A B f₁) (algebraMap A B f₂)).modificationGraded
  letI := (twoGeneratorSquare B' (algebraMap A B' f₁) (algebraMap A B' f₂)).modificationGraded
  frobeniusColimitVectorBundlesCatPullbackLocIso p
    (modificationToBase B (algebraMap A B f₁) (algebraMap A B f₂))
    (centerToBase B (algebraMap A B f₁) (algebraMap A B f₂))
    (exceptionalToModification B (algebraMap A B f₁) (algebraMap A B f₂))
    (exceptionalToCenter B (algebraMap A B f₁) (algebraMap A B f₂))
    (modificationToBase B' (algebraMap A B' f₁) (algebraMap A B' f₂))
    (centerToBase B' (algebraMap A B' f₁) (algebraMap A B' f₂))
    (exceptionalToModification B' (algebraMap A B' f₁) (algebraMap A B' f₂))
    (exceptionalToCenter B' (algebraMap A B' f₁) (algebraMap A B' f₂))
    (coeffCubeBase A φ) (coeffCubeModification A f₁ f₂ φ) (coeffCubeCenter A f₁ f₂ φ)
    (coeffCubeExceptional A f₁ f₂ φ)
    (isInCharacteristic_spec B p hpB)
    (isInCharacteristic_twoGeneratorModification B _ _ p hpB)
    (isInCharacteristic_twoGeneratorCenter B _ _ p hpB)
    (isInCharacteristic_twoGeneratorExceptional B _ _ p hpB)
    (isInCharacteristic_spec B' p hpB')
    (isInCharacteristic_twoGeneratorModification B' _ _ p hpB')
    (isInCharacteristic_twoGeneratorCenter B' _ _ p hpB')
    (isInCharacteristic_twoGeneratorExceptional B' _ _ p hpB')
    (coeffCube_sq A f₁ f₂ φ) (coeffCube_se A f₁ f₂ φ)
    (twoGenerator_isPullback B (algebraMap A B f₁) (algebraMap A B f₂)).w
    (twoGenerator_isPullback B' (algebraMap A B' f₁) (algebraMap A B' f₂)).w
    (coeffCube_sb A f₁ f₂ φ) (coeffCube_sz A f₁ f₂ φ) M

end OfHom

end AlgebraicGeometry

end
