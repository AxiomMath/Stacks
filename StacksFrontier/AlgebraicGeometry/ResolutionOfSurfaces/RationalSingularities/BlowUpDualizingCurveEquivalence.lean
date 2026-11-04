module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpDualizingSequence
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalTwistCohomology
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.FibreDimension
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineBaseVanishing
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpDualizingSupplement
public import StacksFrontier.AlgebraicGeometry.Duality.ExceptionalDualizingSheafIdentificationSupplement
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpDualizingSequenceSupplement

/-!
# The curve vanishing that clause (2) of Tag 0B64 consumes is its own conclusion

In Situation [Stacks, Tag 0B4W] let `X` be the blowup of `Spec(A)` in the maximal ideal, let
`i : E ⟶ X` be its exceptional divisor and let `ω_X` be a dualizing module on `X`. Clause (2) of
[Stacks, Tag 0B64] is the vanishing `H¹(X, ω_X(n)) = 0` for `n ≥ 0`, and
`AlgebraicGeometry.BlowUpDualizing.isZero_firstCohomology_dualizingTwist_of_restrictionVanishing`
of `…/RationalSingularities/BlowUpDualizingSequence.lean` proves it from the single datum

`hcurve : H¹(E, (ω_X|_E)(n)) = 0 for every n ≥ 0`.

This file proves the converse implication, degree by degree: `H¹(X, ω_X(n)) = 0` implies
`H¹(E, (ω_X|_E)(n)) = 0`. The two families of vanishings are therefore equivalent: `hcurve` is
the conclusion of the clause restated on `E`.

## Main results

* `AlgebraicGeometry.BlowUpDualizing.isZero_cohomology_two_le_of_isQuasicoherent`:
  `Hⁱ(X, ℱ) = 0` for `i ≥ 2` and `ℱ` quasi-coherent, from the fibre dimension of the
  modification ([Stacks, Tag 0E7D] over the affine base).
* `AlgebraicGeometry.BlowUpDualizing.isZero_firstCohomology_curveTwist_of_schemeTwist`:
  **the converse of clause (2)**, `H¹(X, ω_X(n)) = 0 ⟹ H¹(E, (ω_X|_E)(n)) = 0`.
* `AlgebraicGeometry.BlowUpDualizing.isZero_firstCohomology_curveTwist_iff_schemeTwist`: the two
  families are equivalent.

## The argument

The restriction sequence of `…/RationalSingularities/BlowUpDualizingSequence.lean`, twisted `n`
times, is

`0 ⟶ ω_X(n + 1) ⟶ ω_X(n) ⟶ i_*((ω_X|_E)(n)) ⟶ 0`

and the relevant stretch of its long exact cohomology sequence is

`H¹(X, ω_X(n)) ⟶ H¹(X, i_*((ω_X|_E)(n))) ⟶ H²(X, ω_X(n + 1))`.

The right-hand term vanishes for every quasi-coherent module: the fibres of the modification
have dimension at most one
(`AlgebraicGeometry.RationalSingularitySituation.topologicalKrullDim_fiber_le_natCast_one`) and
the base is affine, so [Stacks, Tag 0E7D] kills cohomology in degrees at least two. Given the
left-hand term, `AlgebraicGeometry.BlowUpDualizing.isZero_deltaFunctor_right` of
`…/RationalSingularities/ExceptionalTwistCohomology.lean` makes the middle term vanish; and the
middle term is `H¹(E, (ω_X|_E)(n))` because cohomology does not change along the closed
immersion `i` ([Stacks, Tag 089W], `…HyperplaneTwistSequence.cohomologyHyperplaneIso`).

## References

* [Stacks Project, Tag 0B64](https://stacks.math.columbia.edu/tag/0B64)
* [Stacks Project, Tag 0B4W](https://stacks.math.columbia.edu/tag/0B4W)
* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 0EGK](https://stacks.math.columbia.edu/tag/0EGK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Ample Stacks.RelativeVeryAmple
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence
open Stacks.Cohomology.FormalFunctions (cohomologyDeltaFunctor cohomologyDeltaFunctor_functor)
open Stacks.AlgebraicGeometry.TopDegreeBaseChange
  (isZero_rightDerivedPlus_of_forall_fiber_dim_le_of_affineBase)

attribute [local instance 2000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.BlowUpDualizing

variable (S : RationalSingularitySituation.{u})

/-- **`Hⁱ(X, ℱ) = 0` for `i ≥ 2` and `ℱ` quasi-coherent on the blowup.** The fibres of the
modification have dimension at most one and the base is affine, so this is [Stacks, Tag 0E7D]
over an affine base. -/
theorem isZero_cohomology_two_le_of_isQuasicoherent
    (F : (blowUpScheme S.A).Modules) (hF : F.IsQuasicoherent) (n : ℕ) (hn : 2 ≤ n) :
    IsZero (((cohomologyDeltaFunctor (blowUpScheme S.A)).functor n).obj F) := by
  let : IsProper (blowUpToBase (centre S.A)) := isProper_blowUpToBase (centre S.A)
  exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ n F).2
    (isZero_rightDerivedPlus_of_forall_fiber_dim_le_of_affineBase (blowUpToBase (centre S.A)) 1
      (fun y => (rationalSingularitySituationBlowUp S).topologicalKrullDim_fiber_le_natCast_one y)
      (n : ℤ) (by exact_mod_cast hn) F hF)

/-- **The converse of clause (2) of [Stacks, Tag 0B64]**: in Situation [Stacks, Tag 0B4W] at the
blowup of `Spec(A)` in the maximal ideal, the vanishing `H¹(X, ω_X(n)) = 0` implies the curve
vanishing `H¹(E, (ω_X|_E)(n)) = 0` that
`AlgebraicGeometry.BlowUpDualizing.isZero_firstCohomology_dualizingTwist_of_restrictionVanishing`
consumes, in the same degree.

The `n`-th twist of the restriction sequence has
`H¹(X, ω_X(n)) ⟶ H¹(X, i_*((ω_X|_E)(n))) ⟶ H²(X, ω_X(n + 1))` as a stretch of its long exact
cohomology sequence, the right-hand term vanishes by
`AlgebraicGeometry.BlowUpDualizing.isZero_cohomology_two_le_of_isQuasicoherent`, and cohomology
does not change along the closed immersion `i`. -/
theorem isZero_firstCohomology_curveTwist_of_schemeTwist
    (ωX : (blowUpScheme S.A).Modules)
    (hωX : letI : IsLocallyNoetherian (blowUpScheme S.A) := isLocallyNoetherian_blowUpScheme S.A
      Stacks.Duality.IsDualizingModule ωX)
    (n : ℕ)
    (hvanish : IsZero (((cohomologyDeltaFunctor (blowUpScheme S.A)).functor 1).obj
      (schemeTwist S.A ωX (n : ℤ)))) :
    IsZero (((cohomologyDeltaFunctor (exceptionalCurve S.A)).functor 1).obj
      (curveTwist S.A ((Scheme.Modules.pullback (exceptionalImmersion S.A)).obj ωX) (n : ℤ))) := by
  let : IsLocallyNoetherian (blowUpScheme S.A) := isLocallyNoetherian_blowUpScheme S.A
  let : ωX.IsCoherent := hωX.1
  obtain ⟨f, g, w, hS⟩ := exists_shortExact_schemeTwist_dualizing S.A ωX hωX
  have hSm := shortExact_twistedSequence (exceptionalImmersion S.A) (twistNegOne S.A) ωX
    ((Scheme.Modules.pullback (exceptionalImmersion S.A)).obj ωX) f g w hS (-(n : ℤ))
  have hX := isZero_deltaFunctor_right (cohomologyDeltaFunctor (blowUpScheme S.A)) hSm 1
    hvanish (isZero_cohomology_two_le_of_isQuasicoherent S _
      (Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing.isQuasicoherent_tensorPowTwist
        ωX (twistNegOne S.A) (-(n : ℤ) - 1)) 2 le_rfl)
  have hres := IsZero.of_iso hX
    (cohomologyHyperplaneIso (exceptionalImmersion S.A) (twistNegOne S.A)
      ((Scheme.Modules.pullback (exceptionalImmersion S.A)).obj ωX) (-(n : ℤ))
      (isQuasicoherent_curveTwist_pullback S.A ωX hωX.1 (n : ℤ)) 1).symm
  rw [ModuleCat.isZero_iff_subsingleton] at hres ⊢
  exact hres

/-- **The curve vanishing that clause (2) of [Stacks, Tag 0B64] consumes is equivalent to the
conclusion of that clause.** In Situation [Stacks, Tag 0B4W] at the blowup of `Spec(A)` in the
maximal ideal, for `ω_X` a dualizing module on `X`,

`(∀ n ≥ 0, H¹(E, (ω_X|_E)(n)) = 0) ↔ (∀ n ≥ 0, H¹(X, ω_X(n)) = 0)`.

The forward implication is
`AlgebraicGeometry.BlowUpDualizing.isZero_firstCohomology_dualizingTwist_of_restrictionVanishing`
and the backward one is
`AlgebraicGeometry.BlowUpDualizing.isZero_firstCohomology_curveTwist_of_schemeTwist`. -/
theorem isZero_firstCohomology_curveTwist_iff_schemeTwist
    (ωX : (blowUpScheme S.A).Modules)
    (hωX : letI : IsLocallyNoetherian (blowUpScheme S.A) := isLocallyNoetherian_blowUpScheme S.A
      Stacks.Duality.IsDualizingModule ωX) :
    (∀ n : ℕ, IsZero (((cohomologyDeltaFunctor (exceptionalCurve S.A)).functor 1).obj
        (curveTwist S.A ((Scheme.Modules.pullback (exceptionalImmersion S.A)).obj ωX)
          (n : ℤ)))) ↔
      ∀ n : ℕ, IsZero (((cohomologyDeltaFunctor (blowUpScheme S.A)).functor 1).obj
        (schemeTwist S.A ωX (n : ℤ))) :=
  ⟨fun h n => isZero_firstCohomology_dualizingTwist_of_restrictionVanishing S.A ωX hωX h n,
    fun h n => isZero_firstCohomology_curveTwist_of_schemeTwist S ωX hωX n (h n)⟩

end AlgebraicGeometry.BlowUpDualizing

end
