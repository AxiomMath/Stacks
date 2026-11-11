module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpDualizingSequence
public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.Twist
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.AssociatedPointsCompat
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Twist
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionAssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeExactSequenceTwist
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeSequence
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleAssociatedPoint
public import StacksFrontier.AlgebraicGeometry.IdealSheafSequence.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.StalkMono
public import StacksFrontier.AlgebraicGeometry.Modules.TensorInvertible
public import StacksFrontier.AlgebraicGeometry.Modules.TensorStalkNaturality
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpDualizing
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpEventualVanishing
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalCurveSections
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedDualizingModule
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpDualizingSupplement

/-!
# Further results on `BlowUpDualizingSequence`

Results about the objects of the module `BlowUpDualizingSequence` (in
`StacksDraft.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities`)
that need imports beyond those of that module.

## Main results

* `AlgebraicGeometry.BlowUpDualizing.isZero_firstCohomology_dualizingTwist_of_normalized`:
  `H¹(X, ω_X(n)) = 0` for `n ≥ 0` on the blowup `X` of a rational singularity, given the vanishing
  of `H¹(E, (ω_X|_E)(n))` on the exceptional curve `E`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Stacks.Ample
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence
open Stacks.Cohomology.FormalFunctions (cohomologyDeltaFunctor cohomologyDeltaFunctor_functor)

universe u

namespace AlgebraicGeometry.BlowUpDualizing

attribute [local instance] AlgebraicGeometry.schemeModulesMonoidal
  AlgebraicGeometry.schemeModulesSymmetric

attribute [local instance 10000] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- **Clause (2) of [Stacks, Tag 0B64], given its restriction to the exceptional curve.** In
Situation [Stacks, Tag 0B4W] let `X` be the blowup of `Spec(A)` in the maximal ideal, let `E` be
its exceptional curve and let `ω_X` be a dualizing module of `X` normalized relative to a dualizing
module `ω_A` of `A`, in the sense of
`AlgebraicGeometry.RationalSingularitySituation.NormalizedDualizingModule`. If
`H¹(E, (ω_X|_E)(n)) = 0` for every `n ≥ 0`, then `H¹(X, ω_X(n)) = 0` for every `n ≥ 0`.

No `@[stacks 0B64]` attribute is attached: the hypothesis `hcurve` on `E` is not part of the
source's statement. -/
theorem isZero_firstCohomology_dualizingTwist_of_normalized (S : RationalSingularitySituation.{u})
    (ωA : ModuleCat.{u} S.A) (ωX : (blowUpScheme S.A).Modules)
    (N : letI : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
        isLocallyNoetherian_blowUpScheme S.A
      (rationalSingularitySituationBlowUp S).NormalizedDualizingModule ωA ωX)
    (hcurve : ∀ n : ℕ, IsZero (((cohomologyDeltaFunctor (exceptionalCurve S.A)).functor 1).obj
      (curveTwist S.A ((Scheme.Modules.pullback (exceptionalImmersion S.A)).obj ωX) (n : ℤ))))
    (n : ℕ) :
    IsZero (((cohomologyDeltaFunctor (blowUpScheme S.A)).functor 1).obj
      (schemeTwist S.A ωX n)) := by
  let : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
    isLocallyNoetherian_blowUpScheme S.A
  exact isZero_firstCohomology_dualizingTwist_of_restrictionVanishing S.A ωX N.isDualizing
    hcurve n

end AlgebraicGeometry.BlowUpDualizing

end
