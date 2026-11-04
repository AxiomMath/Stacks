module

public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzCone.ConeDepthAssembly
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzCone.NilpotentSection
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzCone.FiniteSheaves
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.ImprovingFormalModulesDepthTwoCarrier
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.CanonicalExtensionCdOneDepthThree
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.SpecialFibreSerreCriterion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.AnnihilatedComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedConeDepthDimension

/-!
# Algebraization of formal modules along the zero scheme of an ample section

Let `k` be a field, `P` a proper scheme over `k`, `𝓛` an ample invertible `𝒪_P`-module, `s` a
global section of `𝓛`, `Q = Z(s)` its zero scheme and `𝓘` the ideal of `Q`. An object `(𝓕ₙ)` of
`Coh(P, 𝓘)` such that for all `q ∈ Q` and all primes `𝔭 ∉ V(𝓘_q^∧)` of `𝒪_{P,q}^∧`

`depth((𝓕_q^∧)_𝔭) + dim(𝒪_{P,q}^∧/𝔭) + dim({q}‾) > 2`

is the completion of a coherent `𝒪_P`-module.

## Main results

* `Stacks.Algebraization.isCompletionOfCoherent_of_two_lt_depth_add_dim`: an object of
  `Coh(P, 𝓘)` satisfying the depth-plus-dimension bound above is the completion of a coherent
  `𝒪_P`-module.

## References

* [Stacks Project, Tag 0EL5](https://stacks.math.columbia.edu/tag/0EL5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.GradedSections (sectionRing)
open Stacks.AmpleFiniteAvoidance (grading)
open Stacks.SectionRingProjMorphism (projHomOfIsAmple)

universe u

namespace Stacks.Algebraization

section Monoidal

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable (k : Type u) [Field k] {P : Scheme.{u}} (fP : P ⟶ Spec (.of k)) [IsProper fP]
  (L : P.Modules) [Stacks.Ample.IsInvertibleModule P L] (hL : Stacks.Ample.IsAmple P L)
  (s : Γ(L, ⊤))

include hL in
/-- Let `k` be a field, `P` a proper scheme over `k`, `𝓛` an ample invertible `𝒪_P`-module,
`s ∈ Γ(P, 𝓛)` and `𝓘` the ideal of the zero scheme `Q = Z(s)`. Let `(𝓕ₙ)` be an object of
`Coh(P, 𝓘)` such that for all `q ∈ Q` and all primes `𝔭` of `𝒪_{P,q}^∧` not containing `𝓘_q^∧`,
`depth((𝓕_q^∧)_𝔭) + dim(𝒪_{P,q}^∧/𝔭) + dim({q}‾) > 2`.
Then `(𝓕ₙ)` is the completion of a coherent `𝒪_P`-module. -/
@[stacks 0EL5]
theorem isCompletionOfCoherent_of_two_lt_depth_add_dim
    (F : Stacks.Coherent.CoherentAdicSystems (zeroScheme P L s))
    (hdepth : ∀ q ∈ (zeroScheme P L s).support,
      ∀ p : PrimeSpectrum (completedLocalRing (zeroScheme P L s) q),
        ¬ completedLocalIdeal (zeroScheme P L s) q ≤ p.asIdeal →
        (2 : EInt) < enatToEInt (completedStalkDepth (zeroScheme P L s) F q p) +
          krullDimToEInt (ringKrullDim (completedLocalRing (zeroScheme P L s) q ⧸ p.asIdeal)) +
          krullDimToEInt (dimClosureAt P q)) :
    haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian fP
    IsCompletionOfCoherent (zeroScheme P L s) F := by
  classical
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian fP
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace fP
  have : IsNoetherian P := ⟨⟩
  have : IsIso (projHomOfIsAmple L hL) :=
    Stacks.SectionRingProjIso.isIso_projHomOfIsAmple_of_isProper L hL fP
  have : IsNoetherianRing (sectionRing L) :=
    Stacks.LefschetzCone.isNoetherianRing_sectionRing fP L hL
  have hdual := hasDualizingComplexOnAffineCover_of_locallyOfFiniteType k fP
  have hT := stableUnderSpecialization_zeroSchemeClosureDimLE L s 1
  have hT' := stableUnderSpecialization_zeroSchemeClosureDimLE L s 0
  have hTY := zeroSchemeClosureDimLE_subset_support L s 1
  have himm := mem_zeroSchemeClosureDimLE_one_of_isImmediateSpecialization fP L s
  obtain ⟨hdep, -, H, e, σ, -, -, -, hσ⟩ := exists_proIso_coherentAdicSystem_canonicalImprovedSystem
    hdual F hT hT' hTY (zeroSchemeClosureDimLE_mono L s zero_le_one) 1
    (exists_affineOpen_cohomologicalDimension_zeroScheme_le_one fP L hL s)
    (zeroScheme_hypothesis_b fP L hL s F hdepth) (zeroScheme_hypothesis_c L s F hdepth)
    (zeroScheme_hypothesis_d fP L hL s F hdepth) himm
  suffices hH : IsCompletionOfCoherent (zeroScheme P L s) H by
    obtain ⟨G, ⟨eG⟩⟩ := hH
    obtain ⟨G', ⟨eG'⟩⟩ := essImage_of_essImage_of_isKernelCokernelAnnihilatedByPower P _ σ hσ
      ⟨G, ⟨(ObjectProperty.fullyFaithfulι _).preimageIso eG⟩⟩
    exact ⟨G', ⟨(ObjectProperty.ι _).mapIso eG'⟩⟩
  have hfg : (Ideal.span ({Stacks.LefschetzCone.sectionElt L s} : Set (sectionRing L))).FG :=
    ⟨{Stacks.LefschetzCone.sectionElt L s}, by simp⟩
  rcases Stacks.LefschetzCone.cohomologicalDimension_span_singleton_le_zero_or_eq_one
      (Stacks.LefschetzCone.sectionElt L s) hfg with h0 | h1
  · exact Stacks.LefschetzCone.isCompletionOfCoherent_of_isNilpotent L hL s
      (Stacks.LefschetzCone.isNilpotent_of_cohomologicalDimension_le_zero (grading L)
        (Stacks.LefschetzCone.sectionElt_mem L s) hfg h0) H
  have hfinite : ∀ G : P.Modules, G.IsCoherent →
      Module.Finite _ (Stacks.TwistedSections.twistModule G L) := fun G _ ↦
    Stacks.AlgebraicGeometry.ProperAmpleCohomology.moduleFinite_twistModule_of_isCoherent
      fP _ L hL
  have hfinH := fun n : ℕ ↦
    hfinite _ (Stacks.LefschetzCone.isCoherent_obj L s H (op n))
  set F'' := canonicalImprovedSystem hdual F hT hT' hTY himm
  have hcoh : ∀ n, (F''.obj n).IsCoherent :=
    isCoherent_canonicalImprovedSystem_obj hdual F hT hT' hTY himm
  have hfin := fun n ↦ hfinite _ (hcoh n)
  have : ∀ n, ((F'' ⋙ Stacks.LefschetzCone.coneFunctor L s).obj n).IsCoherent := fun n ↦
    Stacks.LefschetzCone.isCoherent_coneFunctor_obj L s _ (hfin n)
  let : Algebra k (sectionRing L) := (Stacks.LefschetzCone.sectionRingStructureMap fP L).toAlgebra
  have : Algebra.FiniteType k (sectionRing L) :=
    Stacks.AlgebraicGeometry.ProperAmpleCohomology.ringHomFiniteType_sectionRing fP L hL
  obtain ⟨K, hK⟩ := exists_isDualizingComplex_of_finiteType_field k (sectionRing L)
  refine Stacks.LefschetzCone.isCompletionOfCoherent_of_canonicallyExtends L hL s H hfinH ?_
  refine canonicallyExtends_of_cd_one_of_proIso_depthThree (Stacks.LefschetzCone.coneSituation L s)
    _ ⟨K, hK⟩ h1 (F'' ⋙ Stacks.LefschetzCone.coneFunctor L s)
    (Stacks.LefschetzCone.coneSystemProIso L hL s H hfinH F'' e) fun n y z hyz ↦ ?_
  have := _root_.isQuasicoherent_of_isCoherent (F''.obj (op n))
  exact Stacks.LefschetzCone.three_le_depthOfStalkOnOpen_coneFunctor_add_distanceToZ L hL s fP
    (F''.obj (op n)) (hfin (op n)) (hdep (op n)) y z hyz

end Monoidal

end Stacks.Algebraization

end
