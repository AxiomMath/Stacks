module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpExceptionalDualizing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleDualEvaluation
public import StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierAdjunctionModule
public import StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierDualizingModule
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpDualizing
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalTwistGlobalGeneration
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingTwistSupplement
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointSheafHomSupplement
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpDualizingSupplement

/-!
# The dualizing module of the exceptional curve of a blowup

Results about `AlgebraicGeometry.BlowUpDualizing.exceptionalDualizingModule`, the module
`ω_E = H¹(a(ω_X))` on the exceptional curve `E` of the blowup `X` of `Spec(A)` in the maximal ideal
of a local ring `A`, that need imports beyond those of the file defining it.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Ample Stacks.RelativeVeryAmple
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence
open Stacks.Cohomology.FormalFunctions (cohomologyDeltaFunctor cohomologyDeltaFunctor_functor)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.BlowUpDualizing

variable (A : Type u) [CommRing A] [IsLocalRing A]

section Noetherian

variable [IsNoetherianRing A]

/-- **`ω_E` is a dualizing module on `E`.** If `ω_X`, placed in some degree `n`, is a dualizing
complex on the blowup `X`, then the module `ω_E = H¹(a(ω_X))` on the exceptional divisor
`i : E ⟶ X` is dualizing. This is [Stacks, Tag 0AA3] — `i^!` of a dualizing complex is dualizing —
at the closed immersion `i`. -/
theorem isDualizingModule_exceptionalDualizingModule (ωX : (blowUpScheme A).Modules)
    [ωX.IsQuasicoherent] (n : ℤ)
    (hωX : letI : IsLocallyNoetherian (blowUpScheme A) := isLocallyNoetherian_blowUpScheme A
      Stacks.Duality.IsDualizingComplex
        ((DerivedCategory.singleFunctor (blowUpScheme A).Modules n).obj ωX)) :
    letI : IsLocallyNoetherian (exceptionalCurve A) := isLocallyNoetherian_exceptionalCurve A
    Stacks.Duality.IsDualizingModule (exceptionalDualizingModule A ωX) := by
  have : IsLocallyNoetherian (blowUpScheme A) := isLocallyNoetherian_blowUpScheme A
  exact Stacks.Divisors.isDualizingModule_homologyOne_derivedSheafHomExactSupport
    (exceptionalIdeal (centre A)) ωX n hωX

end Noetherian

/-! ### Modules on `E` isomorphic to the dualizing sheaf of `E` over `κ` -/

section OverResidueField

variable (S : RationalSingularitySituation.{u})

/-- **Duality for a module on the exceptional curve isomorphic to the dualizing sheaf of `E` over
`κ`.** A module on `E` isomorphic to `Stacks.Duality.dualizingSheafOverField` of the structure
morphism `E ⟶ Spec(κ)` satisfies
`AlgebraicGeometry.CohenMacaulayCurveSituation.DualityVanishing`. -/
theorem dualityVanishing_of_iso_dualizingSheafOverField (ωE : (exceptionalCurve S.A).Modules)
    (e : ωE ≅ Stacks.Duality.dualizingSheafOverField
      (X := (cohenMacaulayCurveSituationExceptionalDivisor S).X)
      (cohenMacaulayCurveSituationExceptionalDivisor S).f) :
    (cohenMacaulayCurveSituationExceptionalDivisor S).DualityVanishing ωE := by
  intro M _ hM
  refine IsZero.of_iso
    ((cohenMacaulayCurveSituationExceptionalDivisor S).dualityVanishing_dualizingSheafOverField
      M hM) ?_
  exact AlgebraicGeometry.cohomologyOverFieldIso
    (cohenMacaulayCurveSituationExceptionalDivisor S).k
    (cohenMacaulayCurveSituationExceptionalDivisor S).f
    (Stacks.SheafOfModules.TensorPower.tensorSheafMapIso _ _ e (Iso.refl M)) 1

/-- **`H¹(X, ω_X(n)) = 0` for every `n ≥ 0`, with the single input that `ω_E = H¹(a(ω_X))` is the
dualizing sheaf of `E` over `κ`.**

This is the conclusion of clause (2) of [Stacks, Tag 0B64], with the hypothesis `e`, a single
isomorphism of modules on `E`, in place of the `n`-indexed curve vanishing carried by
`AlgebraicGeometry.BlowUpDualizing.isZero_firstCohomology_dualizingTwist_of_normalized`. -/
theorem isZero_firstCohomology_dualizingTwist_of_exceptionalDualizingIso
    (ωX : (blowUpScheme S.A).Modules)
    (hωX : letI : IsLocallyNoetherian (blowUpScheme S.A) := isLocallyNoetherian_blowUpScheme S.A
      Stacks.Duality.IsDualizingModule ωX)
    (e : exceptionalDualizingModule S.A ωX ≅ Stacks.Duality.dualizingSheafOverField
      (X := (cohenMacaulayCurveSituationExceptionalDivisor S).X)
      (cohenMacaulayCurveSituationExceptionalDivisor S).f)
    (n : ℕ) :
    IsZero (((cohomologyDeltaFunctor (blowUpScheme S.A)).functor 1).obj
      (schemeTwist S.A ωX n)) := by
  have : IsLocallyNoetherian (blowUpScheme S.A) := isLocallyNoetherian_blowUpScheme S.A
  have : IsLocallyNoetherian (exceptionalCurve S.A) := isLocallyNoetherian_exceptionalCurve S.A
  obtain ⟨m, hm⟩ := hωX.2
  have : ωX.IsQuasicoherent :=
    (((Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae (blowUpScheme S.A) ωX).out 1 2
      rfl rfl).mp hωX.1).1
  exact isZero_firstCohomology_dualizingTwist_of_dualityVanishing S ωX
    (exceptionalDualizingModule S.A ωX) hωX
    (isDualizingModule_exceptionalDualizingModule S.A ωX m hm)
    (nonempty_exceptionalDualizingModule_iso_curveTwist S.A ωX).some
    (dualityVanishing_of_iso_dualizingSheafOverField S _ e) n

end OverResidueField

end AlgebraicGeometry.BlowUpDualizing

end
