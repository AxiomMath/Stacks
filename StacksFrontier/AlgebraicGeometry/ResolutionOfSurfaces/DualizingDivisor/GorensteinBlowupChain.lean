module

public import StacksFrontier.AlgebraicGeometry.Duality.CohenMacaulaySchemeOfDualizingModule
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModule
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.FirstLocalCohomologyFiniteness
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ImpliedProperties.LocalDomain
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.RationalDoublePointResolutionTag
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.LipmanEquivalence
public import StacksFrontier.RingTheory.Dualizing.Gorenstein
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift

/-!
# A regular blowup chain over a Gorenstein rational surface singularity

Let `A` be a Noetherian local normal Nagata domain of dimension two which has a resolution of
singularities, defines a rational singularity and has a dualizing module `ω_A ≅ A`. Then the
hypotheses of [Stacks, Tag 0BGE] hold for `A`, and so `Spec(A)` has a resolution by a finite
sequence of blowups in singular closed points, all of whose stages are normal with finitely many
singular points, each a rational double point in the sense of [Stacks, Tag 0BGC].

This is the resolution `Y ⟶ Spec(A)` on which the proof of the second sentence of
[Stacks, Tag 0EA2] computes the dualizing module ("a repeated application of
[Stacks, Tag 0B64]").

## Main results

* `AlgebraicGeometry.isGorensteinLocalRing_of_iso_dualizingModule`: a Noetherian local ring with a
  dualizing module isomorphic to the ring is Gorenstein.
* `AlgebraicGeometry.isNormalDomain_adicCompletion_of_isResolution`: the completion of a
  Noetherian local normal domain of dimension two having a resolution is a normal domain
  (part (3) of [Stacks, Tag 0BGI], with the integral closure of `A` equal to `A`).
* `AlgebraicGeometry.exists_singularPointBlowupChain_isRegular_of_iso_dualizingModule`: the
  blowup chain of [Stacks, Tag 0BGE] for such an `A`.
-/

@[expose] public section

open CategoryTheory IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- **A Noetherian local ring with a dualizing module isomorphic to the ring is Gorenstein.**
The dualizing module placed in some degree `n` is a dualizing complex; replacing it by `A` and
shifting by `n` gives `A` in degree zero. -/
theorem isGorensteinLocalRing_of_iso_dualizingModule (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (ωA : ModuleCat.{u} A)
    (hωA : Stacks.Duality.IsDualizingRingModule A ωA) (e : ωA ≅ ModuleCat.of A A) :
    Dualizing.IsGorensteinLocalRing A := by
  obtain ⟨-, n, hn⟩ := hωA
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  have e' : ModuleCat.of A ωA ≅ ModuleCat.of A A := e
  have h1 : Dualizing.IsDualizingComplex
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) n).obj (ModuleCat.of A A)) :=
    Stacks.Duality.ringIsDualizingComplex_of_iso
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) n).mapIso e') hn
  change Dualizing.IsDualizingComplex
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))
  exact Stacks.Duality.ringIsDualizingComplex_of_iso
    (((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso n 0 n (by simp)).app _)
    (Dualizing.isDualizingComplex_shift _ h1 n)

/-- **The completion of a two-dimensional normal local domain with a resolution is normal.**
This is part (3) of [Stacks, Tag 0BGI] for the resolution, read through the identification of
`A` with its integral closure in its fraction field (`A` being integrally closed): completing `A`
at its maximal ideal and completing the integral closure at the extended ideal give isomorphic
rings (`Stacks.LocalCohomology.adicCompletionRingEquivCongr`), and a local normal ring is a
domain. -/
theorem isNormalDomain_adicCompletion_of_isResolution (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (hf : IsResolution f) :
    IsNormalDomain (AdicCompletion (maximalIdeal A) A) := by
  have hN := isNormalRing_adicCompletion_integralClosure_of_regular_alteration A X f
    (isAlteration_of_isResolution hf) hf.2
  have hbij : Function.Bijective
      (algebraMap A ↥(integralClosure A (FractionRing A))) := by
    refine ⟨fun x y hxy => IsFractionRing.injective A (FractionRing A) ?_, fun b => ?_⟩
    · simpa using congrArg Subtype.val hxy
    · obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp b.2
      exact ⟨a, Subtype.ext ha⟩
  let e : A ≃+* ↥(integralClosure A (FractionRing A)) := RingEquiv.ofBijective _ hbij
  have hN' : IsNormalRing (AdicCompletion (maximalIdeal A) A) :=
    IsNormalRing.congr
      (Stacks.LocalCohomology.adicCompletionRingEquivCongr e (maximalIdeal A)).symm hN
  obtain ⟨hd, hi⟩ := hN'.of_isLocalRing
  exact ⟨hd, hi⟩

/-- **The blowup chain of [Stacks, Tag 0BGE] over a Gorenstein rational surface singularity.**
Let `A` be a Noetherian local normal Nagata domain of dimension two defining a rational
singularity, with a resolution `X ⟶ Spec(A)` and a dualizing module `ω_A ≅ A`. Then there is a
finite sequence of blowups in singular closed points `Y ⟶ ⋯ ⟶ Spec(A)` with `Y` regular, each
stage normal with finitely many singular points, each a rational double point
([Stacks, Tag 0BGC]): the completion of `A` is normal by part (3) of [Stacks, Tag 0BGI] and `A`
is Gorenstein, which are the remaining hypotheses of [Stacks, Tag 0BGE]. -/
theorem exists_singularPointBlowupChain_isRegular_of_iso_dualizingModule (A : Type u)
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A]
    (hnagata : IsNagataRing A) (hdim : ringKrullDim A = 2)
    (hrational : DefinesRationalSingularity A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (hf : IsResolution f) (ωA : ModuleCat.{u} A)
    (hωA : Stacks.Duality.IsDualizingRingModule A ωA) (e : ωA ≅ ModuleCat.of A A) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of A)),
      SingularPointBlowupChain (fun W => IsNormal W ∧ (singularLocus W).Finite ∧
          ∀ w ∈ singularLocus W, ∃ S : RationalDoublePointSituation.{u},
            Nonempty (S.A ≃+* W.presheaf.stalk w))
        (Spec (.of A)) Y g ∧ IsRegular Y :=
  exists_singularPointBlowupChain_isRegular_of_definesRationalSingularity A hnagata hdim
    hrational (isNormalDomain_adicCompletion_of_isResolution A f hf)
    (isGorensteinLocalRing_of_iso_dualizingModule A ωA hωA e)

end AlgebraicGeometry

end
