module

public import StacksFrontier.AlgebraicGeometry.Duality.ExceptionalDualizingSheafIdentification
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointLocallySmall
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalDualizingNormalized
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalDualizingSheafNormalized
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointPredicateSupplement
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointSheafHomSupplement
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafDualitySupplement
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedDualizingExistenceSupplement

/-!
# Vanishing for twists of a normalized dualizing module on the blowup

In Situation [Stacks, Tag 0B4W] let `X` be the blowup of `Spec(A)` in the maximal ideal. This file
shows that a quasi-coherent `𝒪_X`-module placed in degree zero is bounded below as an object of
`D_QCoh(𝒪_X)`, and that `H¹(X, ω_X(n)) = 0` for every `n ≥ 0` when `ω_X` is a dualizing module on
`X` normalized relative to a dualizing module `ω_A` for `A`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open StacksDraft.DerivedModel (modelHomologyFunctorIso modelSingleFunctorIso)
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence
open Stacks.Cohomology.FormalFunctions (cohomologyDeltaFunctor cohomologyDeltaFunctor_functor)

universe u

namespace AlgebraicGeometry.BlowUpDualizing

variable (S : RationalSingularitySituation.{u})

/-- **A quasi-coherent module in degree zero is bounded below**, as an object of
`D_QCoh(𝒪_X)`: its cohomology vanishes in every negative degree, the single complex being
concentrated in degree zero. This is the hypothesis that [Stacks, Tag 0A9X] asks of the object it
is read at. -/
theorem isBoundedBelowQuasiCoherent_singleQuasiCoherent (ωX : (blowUpScheme S.A).Modules)
    (hq : ωX.IsQuasicoherent) :
    Stacks.Duality.isBoundedBelowQuasiCoherentAtModel (blowUpScheme S.A)
      (Stacks.Duality.singleQuasiCoherent ωX hq 0) := by
  refine ⟨0, fun m hm => ?_⟩
  change IsZero ((DerivedCategory.homologyFunctor (blowUpScheme S.A).Modules m).obj
    ((DerivedCategory.singleFunctor (blowUpScheme S.A).Modules 0).obj ωX))
  exact DerivedCategory.isZero_of_isGE _ 0 m hm

/-- **Clause (2) of [Stacks, Tag 0B64], without the non-regularity hypothesis.** In Situation
[Stacks, Tag 0B4W] let `X` be the blowup of `Spec(A)` in the maximal ideal, let `ω_A` be a
dualizing module for `A` and let `ω_X` be a dualizing module on `X` normalized relative to `ω_A`
in the sense of [Stacks, Remark 0B4R]. Then `H¹(X, ω_X(n)) = 0` for every `n ≥ 0`.

The source assumes in addition that `A` is not regular; the argument does not use it. The proof
descends from the vanishing for large `n` along the restriction sequences to the exceptional
curve `E`, where the vanishing needed is clause (1) of the same tag read through duality for the
dualizing module `ω_E` of `E`. -/
theorem isZero_firstCohomology_dualizingTwist_of_isDualizingRingModule
    (ωA : ModuleCat.{u} S.A) (hωA : Stacks.Duality.IsDualizingRingModule S.A ωA)
    (ωX : (blowUpScheme S.A).Modules)
    (N : letI : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
        isLocallyNoetherian_blowUpScheme S.A
      (rationalSingularitySituationBlowUp S).DualizingNormalization ωA ωX)
    (n : ℕ) :
    IsZero (((cohomologyDeltaFunctor (blowUpScheme S.A)).functor 1).obj
      (schemeTwist S.A ωX n)) :=
  isZero_firstCohomology_dualizingTwist_of_dualizingNormalization S ωA ωX N
    (nonempty_exceptionalDualizingModule_iso_dualizingSheafOverField S ωA hωA ωX N).some n

end AlgebraicGeometry.BlowUpDualizing

end
