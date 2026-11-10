module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback
public import StacksFrontier.AlgebraicGeometry.PicardUFD.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurve
import StacksFrontier.AlgebraicGeometry.Divisors.NormalSheaf

/-!
# The Picard group of a contracted exceptional curve

Let `E ⊆ X` be an exceptional curve of the first kind, presented as an effective Cartier divisor
`D` together with an isomorphism `e : 𝐏¹_k ≅ E` carrying the normal sheaf to `𝒪(-1)`. Stacks
0C5L asserts a short exact sequence

`0 ⟶ Pic(X') ⟶ Pic(X) ⟶ ℤ ⟶ 0`

for the contraction `b : X ⟶ X'` of `E`, the first map being pullback along `b` and the second
the degree on `E`, split by `n ↦ 𝒪_X(-nE)`.

This file proves the right-hand half of that sequence, which does not involve the contraction:
restriction to `E` carries `𝒪_X(-nE)` to `𝒪(n)` on `𝐏¹_k`, so the degree of `𝒪_X(-nE)` on `E` is
`n`, the degree map is surjective and `n ↦ 𝒪_X(-nE)` is injective.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.exceptionalRestrictionHom` — restriction of Picard
  classes to the exceptional curve, read on `𝐏¹_k` through `e`.
* `AlgebraicGeometry.Scheme.IdealSheafData.negativeExceptionalMultipleHom` — the splitting
  `n ↦ [𝒪_X(-nE)]`.
* `AlgebraicGeometry.Scheme.IdealSheafData.exceptionalDegreeHom` — the degree on the exceptional
  curve, computed through an identification `ℤ ≃+ Pic(𝐏¹_k)`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.exceptionalRestrictionHom_negativeExceptionalMultiple`
  — `𝒪_X(-nE)` restricts to `𝒪(n)` on the exceptional curve.
* `AlgebraicGeometry.Scheme.IdealSheafData.exceptionalDegreeHom_negativeExceptionalMultiple` —
  the degree of `𝒪_X(-nE)` on `E` is `n`, so the degree map is split by `n ↦ 𝒪_X(-nE)`.
* `AlgebraicGeometry.Scheme.IdealSheafData.exceptionalDegreeHom_picardClass` — `𝒪_X(E)` has
  degree `-1` on `E`.
* `AlgebraicGeometry.Scheme.IdealSheafData.exceptionalDegreeHom_surjective` — the degree map is
  surjective.
* `AlgebraicGeometry.Scheme.IdealSheafData.negativeExceptionalMultipleHom_injective` — the
  splitting is injective, so `ℤ` is a direct summand of `Pic(X)`.

## Implementation notes

The Picard group used is `Stacks.Picard.ofScheme`, which carries both the pullback homomorphism
`Stacks.Picard.schemePullbackClassHom` and the Picard class `Stacks.Divisors.picardClass` of an
effective Cartier divisor. `Stacks.PicardUFD.twistPicardHom` lands in the different group
`AlgebraicGeometry.Scheme.picardGroup`, so the twist class is written as
`Stacks.SheafOfModules.picardClass` of `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf`.
The identification `ℤ ≃+ Pic(𝐏¹_k)` defining the degree is a parameter of the degree map.

The splitting is the `ℤ`-multiple homomorphism
`zmultiplesHom _ (Stacks.Divisors.negativeTwistPicardClass D)`; that it agrees with the divisor
`nE` for `n : ℕ` is `negativeExceptionalMultipleHom_natCast`.

## References

* [Stacks Project, Tag 0C5L](https://stacks.math.columbia.edu/tag/0C5L)
* [Stacks Project, Tag 0C5G](https://stacks.math.columbia.edu/tag/0C5G)
* [Stacks Project, Tag 0BXJ](https://stacks.math.columbia.edu/tag/0BXJ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open Stacks.RingedSpace (structureIsSheaf pullbackFunctor modulePullback_isInvertible_of)
open Stacks.SheafOfModules (IsInvertible)

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace AlgebraicGeometry

namespace Scheme.IdealSheafData

variable {X : Scheme.{u}} (D : X.IdealSheafData) (k : Type u) [Field k]
  [Stacks.Divisors.IsEffectiveCartierDivisor D] (e : projectiveLineProj k ≅ D.subscheme)

/-! ### The restriction of `𝒪_X(E)` to the exceptional curve -/

/-- The pullback of `𝒪_X(D)` to the closed subscheme `D` is invertible. -/
public theorem isInvertible_pullback_invertibleSheaf :
    IsInvertible D.subscheme.presheaf (structureIsSheaf D.subscheme.toRingedSpace)
      ((pullbackFunctor D.subschemeι.toLRSHom.toShHom).obj
        (Stacks.Divisors.invertibleSheaf' D)) :=
  modulePullback_isInvertible_of _ _ (Stacks.Divisors.isInvertible_invertibleSheaf_picard D)

/-- The twist `𝒪(m)` on the projective line is invertible. -/
public theorem isInvertible_twistingSheaf_projectiveLine (m : ℤ) :
    IsInvertible (projectiveLineProj k).presheaf
      (structureIsSheaf (projectiveLineProj k).toRingedSpace)
      (ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) m) :=
  Stacks.PicardUFD.isInvertible_twistingSheaf k 1 m

/-- For an exceptional curve of the first kind, the pullback of `𝒪_X(D)` to `𝐏¹_k` along `e.hom`
and the closed immersion is the twist `𝒪(-1)`: on `D` it is the normal sheaf, and `e` carries the
normal sheaf to `𝒪(-1)`. -/
public def pullbackInvertibleSheafIsoTwist (hE : D.IsExceptionalCurveOfFirstKind k e) :
    (pullbackFunctor e.hom.toLRSHom.toShHom).obj
        ((pullbackFunctor D.subschemeι.toLRSHom.toShHom).obj
          (Stacks.Divisors.invertibleSheaf' D)) ≅
      ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) (-1) :=
  ((pullbackFunctor e.hom.toLRSHom.toShHom).mapIso
    (Stacks.Divisors.normalSheafIsoInvertibleSheaf D)).symm ≪≫ hE.2.some

/-- For an exceptional curve of the first kind, the class of `𝒪_X(E)` restricted to the
exceptional curve and read on `𝐏¹_k` through `e` is the class of `𝒪(-1)`. -/
public theorem exceptionalRestriction_picardClass (hE : D.IsExceptionalCurveOfFirstKind k e) :
    Stacks.Picard.schemePullbackClass e.hom
        (Stacks.Picard.schemePullbackClass D.subschemeι (Stacks.Divisors.picardClass D)) =
      Stacks.SheafOfModules.picardClass (projectiveLineProj k).presheaf
        (structureIsSheaf (projectiveLineProj k).toRingedSpace)
        (ProjectiveSpectrum.Proj.twistingSheaf
          (MvPolynomial.homogeneousSubmodule (Fin 2) k) (-1))
        (isInvertible_twistingSheaf_projectiveLine k (-1)) :=
  (congrArg (Stacks.Picard.schemePullbackClass e.hom)
      (Stacks.Picard.pullbackClass_classOf D.subschemeι.toLRSHom.toShHom _
        (Stacks.Divisors.isInvertible_invertibleSheaf_picard D))).trans
    ((Stacks.Picard.pullbackClass_classOf e.hom.toLRSHom.toShHom _
        (isInvertible_pullback_invertibleSheaf D)).trans
      ((Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2
        ⟨pullbackInvertibleSheafIsoTwist D k e hE⟩))

/-! ### The two outer maps of the sequence of Tag 0C5L -/

/-- Restriction of Picard classes to the exceptional curve, read on `𝐏¹_k` through the
isomorphism `e`. -/
public abbrev exceptionalRestrictionHom :
    Stacks.Picard.ofScheme X →+ Stacks.Picard.ofScheme (projectiveLineProj k) :=
  (Stacks.Picard.schemePullbackClassHom e.hom).comp
    (Stacks.Picard.schemePullbackClassHom D.subschemeι)

/-- The homomorphism `n ↦ [𝒪_X(-nE)]`, sending `n` to the `n`-th multiple of the class of the
ideal sheaf `𝒪_X(-E)`. -/
public abbrev negativeExceptionalMultipleHom : ℤ →+ Stacks.Picard.ofScheme X :=
  zmultiplesHom _ (Stacks.Divisors.negativeTwistPicardClass D)

/-- For `n : ℕ`, `negativeExceptionalMultipleHom D n` is the class `[𝒪_X(-nE)]` of the divisor
`nE`. -/
public theorem negativeExceptionalMultipleHom_natCast (n : ℕ) :
    negativeExceptionalMultipleHom D (n : ℤ) =
      Stacks.Divisors.negativeTwistPicardClass (D ^ n) := by
  rw [Stacks.Divisors.negativeTwistPicardClass_eq_neg, Stacks.Divisors.picardClass_pow,
    zmultiplesHom_apply, Stacks.Divisors.negativeTwistPicardClass_eq_neg, zsmul_neg, neg_inj]

/-- The restriction of `𝒪_X(-nE)` to the exceptional curve is `𝒪(n)`, written as the `(-n)`-th
multiple of the class of `𝒪(-1)` in `Pic(𝐏¹_k)`. -/
@[stacks 0C5L "the splitting map n ↦ O_X(-nE), stated through Pic(P¹_k) rather than Z: the \
restriction of O_X(-nE) to the exceptional curve is O(n)"]
public theorem exceptionalRestrictionHom_negativeExceptionalMultiple
    (hE : D.IsExceptionalCurveOfFirstKind k e) (n : ℤ) :
    exceptionalRestrictionHom D k e (negativeExceptionalMultipleHom D n) =
      (-n) • Stacks.SheafOfModules.picardClass (projectiveLineProj k).presheaf
        (structureIsSheaf (projectiveLineProj k).toRingedSpace)
        (ProjectiveSpectrum.Proj.twistingSheaf
          (MvPolynomial.homogeneousSubmodule (Fin 2) k) (-1))
        (isInvertible_twistingSheaf_projectiveLine k (-1)) := by
  rw [zmultiplesHom_apply, Stacks.Divisors.negativeTwistPicardClass_eq_neg,
    zsmul_neg, map_neg, map_zsmul, neg_zsmul]
  exact congrArg (fun y => -(n • y)) (exceptionalRestriction_picardClass D k e hE)

/-! ### The degree on the exceptional curve -/

variable (φ : ℤ ≃+ Stacks.Picard.ofScheme (projectiveLineProj k))

/-- The degree of a Picard class on the exceptional curve: restrict to `E`, read the result on
`𝐏¹_k` through `e`, and convert to an integer through an identification `φ : ℤ ≃+ Pic(𝐏¹_k)`. -/
public abbrev exceptionalDegreeHom : Stacks.Picard.ofScheme X →+ ℤ :=
  (φ.symm : Stacks.Picard.ofScheme (projectiveLineProj k) →+ ℤ).comp
    (exceptionalRestrictionHom D k e)

/-- If `φ : ℤ ≃+ Pic(𝐏¹_k)` carries `-1` to the class of `𝒪(-1)`, then the degree of `𝒪_X(-nE)`
on the exceptional curve is `n`. -/
@[stacks 0C5L "the splitting: the degree of O_X(-nE) on the exceptional curve is n. The \
identification Z ≃+ Pic(P¹_k) of Tag 0BXJ is an explicit hypothesis, the library having only \
the injectivity half of that tag"]
public theorem exceptionalDegreeHom_negativeExceptionalMultiple
    (hE : D.IsExceptionalCurveOfFirstKind k e)
    (hφ : φ (-1) = Stacks.SheafOfModules.picardClass (projectiveLineProj k).presheaf
      (structureIsSheaf (projectiveLineProj k).toRingedSpace)
      (ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) (-1))
      (isInvertible_twistingSheaf_projectiveLine k (-1)))
    (n : ℤ) :
    exceptionalDegreeHom D k e φ (negativeExceptionalMultipleHom D n) = n := by
  have h : exceptionalRestrictionHom D k e (negativeExceptionalMultipleHom D n) =
      φ ((-n) • (-1 : ℤ)) := by
    rw [map_zsmul, hφ]
    exact exceptionalRestrictionHom_negativeExceptionalMultiple D k e hE n
  change φ.symm (exceptionalRestrictionHom D k e (negativeExceptionalMultipleHom D n)) = n
  rw [h, φ.symm_apply_apply]
  simp

/-- If `φ : ℤ ≃+ Pic(𝐏¹_k)` carries `-1` to the class of `𝒪(-1)`, then the degree of `𝒪_X(E)` on
the exceptional curve is `-1`. -/
@[stacks 0C5L "the normalization of the degree map: O_X(E) has degree -1 on the exceptional \
curve. The identification Z ≃+ Pic(P¹_k) of Tag 0BXJ is an explicit hypothesis, the library \
having only the injectivity half of that tag"]
public theorem exceptionalDegreeHom_picardClass
    (hE : D.IsExceptionalCurveOfFirstKind k e)
    (hφ : φ (-1) = Stacks.SheafOfModules.picardClass (projectiveLineProj k).presheaf
      (structureIsSheaf (projectiveLineProj k).toRingedSpace)
      (ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) (-1))
      (isInvertible_twistingSheaf_projectiveLine k (-1))) :
    exceptionalDegreeHom D k e φ (Stacks.Divisors.picardClass D) = -1 := by
  have h := exceptionalDegreeHom_negativeExceptionalMultiple D k e φ hE hφ 1
  rw [zmultiplesHom_apply, one_zsmul,
    Stacks.Divisors.negativeTwistPicardClass_eq_neg, map_neg] at h
  omega

/-- If `φ : ℤ ≃+ Pic(𝐏¹_k)` carries `-1` to the class of `𝒪(-1)`, then the degree map on the
exceptional curve is surjective onto `ℤ`. -/
@[stacks 0C5L "right exactness: the degree map Pic(X) ⟶ Z on the exceptional curve is \
surjective, witnessed by the splitting n ↦ O_X(-nE). The identification Z ≃+ Pic(P¹_k) of Tag \
0BXJ is an explicit hypothesis, the library having only the injectivity half of that tag"]
public theorem exceptionalDegreeHom_surjective
    (hE : D.IsExceptionalCurveOfFirstKind k e)
    (hφ : φ (-1) = Stacks.SheafOfModules.picardClass (projectiveLineProj k).presheaf
      (structureIsSheaf (projectiveLineProj k).toRingedSpace)
      (ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) (-1))
      (isInvertible_twistingSheaf_projectiveLine k (-1))) :
    Function.Surjective (exceptionalDegreeHom D k e φ) :=
  Function.LeftInverse.surjective
    (exceptionalDegreeHom_negativeExceptionalMultiple D k e φ hE hφ)

/-- If `φ : ℤ ≃+ Pic(𝐏¹_k)` carries `-1` to the class of `𝒪(-1)`, then `n ↦ [𝒪_X(-nE)]` is
injective, so `ℤ` is a direct summand of `Pic(X)`. -/
@[stacks 0C5L "the splitting n ↦ O_X(-nE) is injective, so Z is a direct summand of Pic(X). The \
identification Z ≃+ Pic(P¹_k) of Tag 0BXJ is an explicit hypothesis, the library having only \
the injectivity half of that tag"]
public theorem negativeExceptionalMultipleHom_injective
    (hE : D.IsExceptionalCurveOfFirstKind k e)
    (hφ : φ (-1) = Stacks.SheafOfModules.picardClass (projectiveLineProj k).presheaf
      (structureIsSheaf (projectiveLineProj k).toRingedSpace)
      (ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) (-1))
      (isInvertible_twistingSheaf_projectiveLine k (-1))) :
    Function.Injective (negativeExceptionalMultipleHom D) :=
  Function.LeftInverse.injective
    (exceptionalDegreeHom_negativeExceptionalMultiple D k e φ hE hφ)

end Scheme.IdealSheafData

end AlgebraicGeometry

end
