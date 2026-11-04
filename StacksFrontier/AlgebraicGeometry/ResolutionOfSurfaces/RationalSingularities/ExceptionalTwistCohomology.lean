module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.IdealPowerCohomologySequence
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpEventualVanishing
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalCurveSections
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalTwistSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleVanishingAboveTheDimension
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalIdealPowersExtra

/-!
# Cohomology of the nonnegative twists on the exceptional curve

In Situation [Stacks, Tag 0B4W] let `X` be the blowup of `Spec(A)` in the maximal ideal, let
`i : E ⟶ X` be its exceptional divisor and let `𝒪_E(n)` be the `n`-th twist on `E`. This file
proves clause (4) of [Stacks, Tag 0B63]: `H¹(E, 𝒪_E(n)) = 0` for every `n ≥ 0`.

## Main results

* `AlgebraicGeometry.BlowUpDualizing.isZero_firstCohomology_curveTwistSheaf`: **clause (4) of
  [Stacks, Tag 0B63]**, `H¹(E, 𝒪_E(n)) = 0` for `n ≥ 0`.
* `AlgebraicGeometry.BlowUpDualizing.isZero_secondCohomology_exceptionalIdealPow`:
  `H²(X, ℐⁿ) = 0` for every `n ≥ 0`, which is what clause (4) is read off.
* `AlgebraicGeometry.BlowUpDualizing.exists_isZero_secondCohomology_twistSheaf`:
  `H²(X, 𝒪_X(n)) = 0` for `n` large, [Stacks, Tag 02O1] in degree two at the structure sheaf.
* `AlgebraicGeometry.BlowUpDualizing.isZero_firstCohomology_exceptionalIdealPow`:
  [Stacks, Tag 0B4Y] in the indexing and the spelling used here.

## The argument

The source takes clause (4) from the exact sequences `0 ⟶ ℐⁿ⁺¹ ⟶ ℐⁿ ⟶ i_*𝒪_E(n) ⟶ 0`
(`AlgebraicGeometry.BlowUpDualizing.exceptionalTwistedSequence`) and their long exact cohomology
sequences. The relevant stretch is

`H¹(X, ℐⁿ) ⟶ H¹(X, i_*𝒪_E(n)) ⟶ H²(X, ℐⁿ⁺¹)`,

whose outer terms vanish: the first is [Stacks, Tag 0B4Y] and the second is proved here. The
middle term is `H¹(E, 𝒪_E(n))` because cohomology does not change along a closed immersion
([Stacks, Tag 01EX], `Stacks.Cohomology.ClosedImmersion.cohomologyObjIsoPushforward`); the
restriction of scalars along `i^♯` that comparison carries changes neither the carrier of a
module nor its being a zero object.

**Where `H²(X, ℐⁿ) = 0` comes from.** Descending induction on `n`. The same sequence gives
`H²(X, ℐⁿ⁺¹) ⟶ H²(X, ℐⁿ) ⟶ H²(X, i_*𝒪_E(n))`, and the third term vanishes with no hypothesis on
`X`: the exceptional curve is a Noetherian space of dimension one by clause (1) of
[Stacks, Tag 0B63], so [Stacks, Tag 02UZ] applies to it, and
`Stacks.CohomologyVanishing.isZero_rightDerived_pushforward_of_noetherianSpace_of_dim_le`
transports that to the direct image. So `H²(X, ℐⁿ⁺¹) = 0` forces `H²(X, ℐⁿ) = 0`, and the
induction starts from the eventual vanishing of [Stacks, Tag 02O1] — applied, exactly as
`AlgebraicGeometry.BlowUpDualizing.exists_isZero_firstCohomology_schemeTwist` applies it in
degree one, to the structure sheaf, which is coherent because `X` is locally Noetherian. Neither
[Stacks, Tag 0E7D] nor the fibre dimensions are needed.

## References

* [Stacks Project, Tag 0B63](https://stacks.math.columbia.edu/tag/0B63)
* [Stacks Project, Tag 0B4W](https://stacks.math.columbia.edu/tag/0B4W)
* [Stacks Project, Tag 0B4Y](https://stacks.math.columbia.edu/tag/0B4Y)
* [Stacks Project, Tag 02O1](https://stacks.math.columbia.edu/tag/02O1)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Ample Stacks.RelativeVeryAmple
open Stacks.Cohomology.FormalFunctions (cohomologyDeltaFunctor)
open Stacks.AlgebraicGeometry.AmpleTwistAcyclicity
  (exists_isZero_rightDerivedPlus_pushforward_tensorPowModule)
open Stacks.AlgebraicGeometry.TopDegreeBaseChange
  (isZero_cohomology_of_isZero_rightDerivedPlus_pushforward)
open Stacks.Divisors (idealSheafOfModules)

attribute [local instance 2000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.BlowUpDualizing

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-! ### `𝒪_X ⊗ 𝒪_X(n)` is `𝒪_X(n)` -/

/-- `𝒪_X ⊗ 𝒪_X(n) ≅ 𝒪_X(n)`, the left unit constraint of the tensor product of
`𝒪_X`-modules. -/
def unitSchemeTwistIso (n : ℤ) :
    schemeTwist A (unitModule (blowUpScheme A)) n ≅ twistSheaf A n :=
  Stacks.Divisors.tensorUnitIso (twistSheaf A n)

/-- A functor sends an object isomorphic to one with vanishing image to one with vanishing
image. -/
private theorem isZero_obj_of_iso {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {X Y : C}
    (e : X ≅ Y) (h : IsZero (F.obj Y)) : IsZero (F.obj X) :=
  h.of_iso (F.mapIso e)

/-! ### Eventual vanishing of `H²(X, ℐⁿ)` -/

/-- **`H²(X, 𝒪_X(n)) = 0` for all large `n`.** This is [Stacks, Tag 02O1] at the proper morphism
`X ⟶ Spec(A)`, the coherent structure sheaf and the relatively ample invertible module `𝒪_X(1)`,
followed by the affine-base comparison [Stacks, Tag 01XK] read in the direction that reflects a
zero object — exactly the argument of
`AlgebraicGeometry.BlowUpDualizing.exists_isZero_firstCohomology_schemeTwist`, in degree two and
at the structure sheaf instead of a dualizing module. -/
theorem exists_isZero_secondCohomology_twistSheaf [IsNoetherianRing A] :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      IsZero (((cohomologyDeltaFunctor (blowUpScheme A)).functor 2).obj
        (twistSheaf A (n : ℤ))) := by
  have : IsLocallyNoetherian (blowUpScheme A) := isLocallyNoetherian_blowUpScheme A
  have : (unitModule (blowUpScheme A)).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.structureSheaf_isCoherent (blowUpScheme A)
  obtain ⟨n₀, hn₀⟩ := exists_isZero_rightDerivedPlus_pushforward_tensorPowModule
    (blowUpToBase (centre A)) (unitModule (blowUpScheme A)) (blowUpTwist (centre A) 1)
    (isRelativelyAmple_blowUpTwist (centre A) (isFiniteType_centre A))
  refine ⟨n₀, fun n hn => ?_⟩
  have : (schemeTwist A (unitModule (blowUpScheme A)) (n : ℤ)).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing.isQuasicoherent_tensorPowTwist
      (unitModule (blowUpScheme A)) (twistNegOne A) (-(n : ℤ))
  have hpush : IsZero (((Scheme.Modules.pushforward (blowUpToBase (centre A))).rightDerivedPlus
      ((2 : ℕ) : ℤ)).obj (schemeTwist A (unitModule (blowUpScheme A)) (n : ℤ))) :=
    IsZero.of_iso (hn₀ n 2 hn (by omega))
      (((Scheme.Modules.pushforward (blowUpToBase (centre A))).rightDerivedPlus
        ((2 : ℕ) : ℤ)).mapIso (schemeTwistNatIso A (unitModule (blowUpScheme A)) n))
  have hzero : IsZero (((cohomologyDeltaFunctor (blowUpScheme A)).functor 2).obj
      (schemeTwist A (unitModule (blowUpScheme A)) (n : ℤ))) :=
    (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff
        (Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpScheme A)) 2 _).mpr
      (isZero_cohomology_of_isZero_rightDerivedPlus_pushforward (blowUpToBase (centre A))
        ((2 : ℕ) : ℤ) (schemeTwist A (unitModule (blowUpScheme A)) (n : ℤ)) hpush)
  exact isZero_obj_of_iso _ (unitSchemeTwistIso A (n : ℤ)).symm hzero

/-- **`H²(X, ℐⁿ) = 0` for all large `n`**, read off the previous statement through part (3) of
[Stacks, Tag 02OS] in degree `n`. -/
theorem exists_isZero_secondCohomology_exceptionalIdealPow [IsNoetherianRing A] :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      IsZero (((cohomologyDeltaFunctor (blowUpScheme A)).functor 2).obj
        (idealSheafOfModules (exceptionalIdeal (centre A) ^ n))) := by
  obtain ⟨n₀, hn₀⟩ := exists_isZero_secondCohomology_twistSheaf A
  exact ⟨n₀, fun n hn =>
    isZero_obj_of_iso _ (exceptionalIdealPowIsoTwistSheaf A n) (hn₀ n hn)⟩

/-! ### A vanishing lemma for the right-hand term -/

/-- **Vanishing of `Fⁿ` in the middle and of `Fⁿ⁺¹` on the left forces `Fⁿ` on the right.** The
connecting morphism out of `Fⁿ(X₃)` is a monomorphism because the map into `Fⁿ(X₃)` is zero, and
it lands in a zero object. This is the companion of
`CategoryTheory.ShortComplex.Exact.isZero_X₂`, for the third term instead of the
second. -/
theorem isZero_deltaFunctor_right {C D : Type*} [Category C] [Category D] [Abelian C]
    [Abelian D] (F : CategoryTheory.DeltaFunctor C D) {S : ShortComplex C} (hS : S.ShortExact)
    (n : ℕ) (h₂ : IsZero ((F.functor n).obj S.X₂))
    (h₁ : IsZero ((F.functor (n + 1)).obj S.X₁)) :
    IsZero ((F.functor n).obj S.X₃) := by
  have := F.mono_δ_of_map_g_eq_zero hS n (h₂.eq_of_src _ _)
  exact IsZero.of_mono (F.δ hS n) h₁

/-! ### The situation at the blowup -/

section Situation

variable (S : RationalSingularitySituation.{u})

/-- **[Stacks, Tag 0B4Y]: `H¹(X, ℐⁿ) = 0`**, in the `Functor.rightDerived` indexing and at the
spelling `exceptionalIdeal (centre S.A)` of the ideal sheaf of the exceptional divisor. This is
`RationalSingularitySituation.isZero_firstCohomology_exceptionalIdealPow_unconditional` at
Situation [Stacks, Tag 0B4W] realized at the blowup of the maximal ideal. -/
theorem isZero_firstCohomology_exceptionalIdealPow (n : ℕ) :
    IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections
        (blowUpScheme S.A)).rightDerived 1).obj
      (idealSheafOfModules (exceptionalIdeal (centre S.A) ^ n))) := by
  have h : IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections
      (rationalSingularitySituationBlowUp S).X).rightDerivedPlus 1).obj
      (idealSheafOfModules ((rationalSingularitySituationBlowUp S).exceptionalIdeal ^ n))) :=
    RationalSingularitySituation.isZero_firstCohomology_exceptionalIdealPow_unconditional
      (rationalSingularitySituationBlowUp S) n
  rw [rationalSingularitySituationBlowUp_exceptionalIdeal] at h
  exact (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff _
    (m := (1 : ℤ)) (n := 1) rfl _).1 h

/-- The exceptional curve has Noetherian underlying space: it is proper over the residue field,
hence quasi-compact, and locally Noetherian. -/
theorem noetherianSpace_exceptionalCurve : NoetherianSpace (exceptionalCurve S.A) := by
  have : IsProper (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)) :=
    isProper_exceptionalDivisorToCentre_residuePoint S.A
  have : CompactSpace (exceptionalCurve S.A) :=
    QuasiCompact.compactSpace_of_compactSpace
      (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
  have : IsLocallyNoetherian (exceptionalCurve S.A) := isLocallyNoetherian_exceptionalCurve S.A
  have : IsNoetherian (exceptionalCurve S.A) := { }
  exact IsNoetherian.noetherianSpace

/-- The exceptional curve has dimension at most one, by clause (1) of [Stacks, Tag 0B63]. -/
theorem topologicalKrullDim_exceptionalCurve_le :
    topologicalKrullDim (exceptionalCurve S.A) ≤ (1 : WithBot ℕ∞) :=
  le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two)

/-- **`H²(X, i_*𝒢) = 0` for every `𝒪_E`-module `𝒢`.** Cohomology does not change along the closed
immersion `i` and the exceptional curve is a Noetherian space of dimension one, so this is
[Stacks, Tag 02UZ] on `E`. No hypothesis on `X`. -/
theorem isZero_secondCohomology_pushforward (G : (exceptionalCurve S.A).Modules) :
    IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections
        (blowUpScheme S.A)).rightDerived 2).obj
      ((Scheme.Modules.pushforward (exceptionalImmersion S.A)).obj G)) :=
  have := noetherianSpace_exceptionalCurve S
  Stacks.CohomologyVanishing.isZero_rightDerived_pushforward_of_noetherianSpace_of_dim_le
    (exceptionalImmersion S.A) (d := 1) (topologicalKrullDim_exceptionalCurve_le S) (by omega) G

/-- **`H²(X, ℐⁿ) = 0` for every `n ≥ 0`.** Descending induction from the eventual vanishing of
[Stacks, Tag 02O1]: the restriction sequence `0 ⟶ ℐⁿ⁺¹ ⟶ ℐⁿ ⟶ i_*𝒪_E(n) ⟶ 0` has
`H²(X, i_*𝒪_E(n)) = 0` because the exceptional curve is one-dimensional, so `H²(X, ℐⁿ⁺¹) = 0`
forces `H²(X, ℐⁿ) = 0`. -/
theorem isZero_secondCohomology_exceptionalIdealPow (n : ℕ) :
    IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections
        (blowUpScheme S.A)).rightDerived 2).obj
      (idealSheafOfModules (exceptionalIdeal (centre S.A) ^ n))) := by
  obtain ⟨n₀, hn₀⟩ := exists_isZero_secondCohomology_exceptionalIdealPow S.A
  have hstep : ∀ m : ℕ, IsZero (((cohomologyDeltaFunctor (blowUpScheme S.A)).functor 2).obj
      (idealSheafOfModules (exceptionalIdeal (centre S.A) ^ (m + 1)))) →
      IsZero (((cohomologyDeltaFunctor (blowUpScheme S.A)).functor 2).obj
        (idealSheafOfModules (exceptionalIdeal (centre S.A) ^ m))) := by
    intro m hm
    have h₁ : IsZero (((cohomologyDeltaFunctor (blowUpScheme S.A)).functor 2).obj
        (exceptionalTwistedSequence S.A m).X₁) := by
      rw [pow_succ'] at hm
      exact isZero_obj_of_iso _ (exceptionalTwistedSequenceIsoOne S.A m) hm
    have h₃ : IsZero (((cohomologyDeltaFunctor (blowUpScheme S.A)).functor 2).obj
        (exceptionalTwistedSequence S.A m).X₃) :=
      isZero_obj_of_iso _ (exceptionalTwistedSequenceIsoThree S.A m)
        (isZero_secondCohomology_pushforward S (curveTwistSheaf S.A (m : ℤ)))
    exact ((cohomologyDeltaFunctor (blowUpScheme S.A)).exact_map
      (shortExact_exceptionalTwistedSequence S.A m) 2).isZero_X₂
      (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)
  have key : ∀ k m : ℕ, n₀ ≤ m + k →
      IsZero (((cohomologyDeltaFunctor (blowUpScheme S.A)).functor 2).obj
        (idealSheafOfModules (exceptionalIdeal (centre S.A) ^ m))) := by
    intro k
    induction k with
    | zero => exact fun m hm => hn₀ m (by simpa using hm)
    | succ k ih => exact fun m hm => hstep m (ih (m + 1) (by omega))
  exact key n₀ n (by omega)

/-! ### Clause (4) -/

/-- **`H¹(E, 𝒪_E(n)) = 0` for every `n ≥ 0`.**

From the restriction sequence `0 ⟶ ℐⁿ⁺¹ ⟶ ℐⁿ ⟶ i_*𝒪_E(n) ⟶ 0` and its long exact cohomology
sequence: `H¹(X, ℐⁿ) = 0` is [Stacks, Tag 0B4Y] and `H²(X, ℐⁿ⁺¹) = 0` is
`isZero_secondCohomology_exceptionalIdealPow`, so the term between them vanishes; and
`H¹(X, i_*𝒪_E(n))` is `H¹(E, 𝒪_E(n))` because cohomology does not change along a closed
immersion ([Stacks, Tag 01EX]). -/
@[stacks 0B63 "clause (4): H^1(E, O_E(n)) = 0 for n >= 0"]
theorem isZero_firstCohomology_curveTwistSheaf (n : ℕ) :
    IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections
        (exceptionalCurve S.A)).rightDerived 1).obj (curveTwistSheaf S.A (n : ℤ))) := by
  have hX : IsZero (((cohomologyDeltaFunctor (blowUpScheme S.A)).functor 1).obj
      (exceptionalTwistedSequence S.A n).X₃) := by
    refine isZero_deltaFunctor_right (cohomologyDeltaFunctor (blowUpScheme S.A))
      (shortExact_exceptionalTwistedSequence S.A n) 1
      (isZero_firstCohomology_exceptionalIdealPow S n) ?_
    have h2 : IsZero (((cohomologyDeltaFunctor (blowUpScheme S.A)).functor 2).obj
        (idealSheafOfModules
          (exceptionalIdeal (centre S.A) * exceptionalIdeal (centre S.A) ^ n))) := by
      rw [← pow_succ']
      exact isZero_secondCohomology_exceptionalIdealPow S (n + 1)
    exact isZero_obj_of_iso _ (exceptionalTwistedSequenceIsoOne S.A n) h2
  have hpush : IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections
      (blowUpScheme S.A)).rightDerived 1).obj
      ((Scheme.Modules.pushforward (exceptionalImmersion S.A)).obj
        (curveTwistSheaf S.A (n : ℤ)))) :=
    isZero_obj_of_iso _ (exceptionalTwistedSequenceIsoThree S.A n).symm hX
  have hres := IsZero.of_iso hpush
    (Stacks.Cohomology.ClosedImmersion.cohomologyObjIsoPushforward (exceptionalImmersion S.A)
      (curveTwistSheaf S.A (n : ℤ)) 1).symm
  rw [ModuleCat.isZero_iff_subsingleton] at hres ⊢
  exact hres

end Situation

end AlgebraicGeometry.BlowUpDualizing

end
