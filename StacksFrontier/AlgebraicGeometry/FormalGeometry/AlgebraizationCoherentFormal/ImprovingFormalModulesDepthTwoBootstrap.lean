module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.ImprovingFormalModulesDepthTwoCompletion
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapFromCompletedStalks
public import StacksFrontier.RingTheory.LocalCohomology.EssentiallyConstantBootstrap
public import StacksFrontier.RingTheory.Module.FiniteFromAdicReduction
public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic

/-!
# The bootstrap situation over the completion of an affine open

Keep the notation of `ImprovingFormalModulesDepthTwoCompletion.lean`: `U` is an affine open of
`X` with ring `A₀ = Γ(X, U)` and ideal `I₀ = ℐ(U)`, `A` is the `I₀`-adic completion of `A₀`,
`(𝒢ₙ)` is an object of `Coh(X, ℐ)` and `M_A` is the completion of `M_𝒢 = lim Γ(U, 𝒢ₙ)`.

The fourth paragraph of the proof of [Stacks, Tag 0EJF] observes that `A, I₀A, T'_A, M_A`,
`s = 1` and `d` satisfy assumptions (1), (3), (4) and (6) of Situation [Stacks, Tag 0EFU] when
`A₀` has a dualizing complex, `cd(A₀, I₀) ≤ d`, and the completed stalks of `(𝒢ₙ)` satisfy
conditions (c) and (d) of [Stacks, Tag 0EJF] at the points of `U ∩ T'`. This file builds that
situation and applies Theorem [Stacks, Tag 0EIE] to it in degree one, which gives the essential
constancy of `{H¹_{T'_A}(M_A/(I₀A)ⁿM_A)}`.

## Main definitions

* `Stacks.Algebraization.depthTwoBootstrapSituation`: the bootstrap situation.

## Main results

* `Stacks.Algebraization.isEssentiallyConstantPro_completedFormalSectionsTower`: the essential
  constancy of `{H¹_{T'_A}(M_A/(I₀A)ⁿM_A)}`.

## References

* [Stacks Project, Tag 0EJF](https://stacks.math.columbia.edu/tag/0EJF)
* [Stacks Project, Tag 0EFU](https://stacks.math.columbia.edu/tag/0EFU)
* [Stacks Project, Tag 0EIE](https://stacks.math.columbia.edu/tag/0EIE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Algebraization

variable {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData} {U : X.Opens}
  (hU : IsAffineOpen U)

omit [AlgebraicGeometry.IsNoetherian X] in
/-- The primes of the completion lying over `U ∩ T'`, for `T' ⊆ Y`, are the primes of the
completion whose contraction to `Γ(X, U)` lies over `T'`. -/
theorem completedAffineLocus_eq_preimage_primesIn {T' : Set X} (hT'Y : T' ⊆ I.support) :
    letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    completedAffineLocus hU T' = PrimeSpectrum.comap
      (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))) ⁻¹' primesIn hU T' := by
  ext q
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  exact (PrimeSpectrum.mem_zeroLocus _ _).1 (primesIn_subset_zeroLocus hU hT'Y h) ha

/-- The completion `M_A` of the formal sections of an object of `Coh(X, ℐ)` over an affine open
is a finite module over the completed ring. -/
theorem finite_completedFormalSections (G : Stacks.Coherent.CoherentAdicSystems I) :
    Module.Finite (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)) (completedFormalSections U hU G) := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : (G.obj.obj (op 0)).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  have : (G.obj.obj (op 0)).IsFiniteType :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).2
  have h0 : Module.Finite Γ(X, U) ((G.obj ⋙ sectionsOver U).obj (op 0)) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections (G.obj.obj (op 0)) hU
  refine Module.Finite.adicCompletion_of_finite_quotient_smul_top
    (Ideal.fg_of_isNoetherianRing _) _ ?_
  have e := (Submodule.quotEquivOfEq _ _ (by rw [zero_add, pow_one])).trans (levelEquiv G hU 0)
  exact Module.Finite.equiv e.symm

/-- The levels `M_𝒢/I₀^{n+1}M_𝒢 ≅ Γ(U, 𝒢ₙ)` are compatible with the transition maps. -/
theorem levelEquiv_transitionMap (G : Stacks.Coherent.CoherentAdicSystems I) {m n : ℕ}
    (h : m ≤ n) (z : formalSectionsOver G U ⧸ (I.ideal ⟨U, hU⟩ ^ (n + 1) •
      (⊤ : Submodule Γ(X, U) (formalSectionsOver G U)))) :
    (G.obj.map (homOfLE h).op).app U (levelEquiv G hU n z) =
      levelEquiv G hU m (AdicCompletion.transitionMap _ _ (Nat.succ_le_succ h) z) := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ z
  show (G.obj.map (homOfLE h).op).app U (limit.π (G.obj ⋙ sectionsOver U) (op n) x) =
    limit.π (G.obj ⋙ sectionsOver U) (op m) x
  rw [← limit.w (G.obj ⋙ sectionsOver U) (homOfLE h).op]
  rfl

variable {T' : Set X} (hT' : StableUnderSpecialization T') (hT'Y : T' ⊆ I.support)
  (G : Stacks.Coherent.CoherentAdicSystems I) (d : ℤ)

/-- **The bootstrap situation of the proof of [Stacks, Tag 0EJF]** over the completion `A` of
`Γ(X, U)`: the ideal `I₀A`, the module `M_A`, the locus `T'_A` of primes over `U ∩ T'`, `s = 1`
and the bound `d`. Assumption (1) comes from a dualizing complex on `Γ(X, U)`, assumption (3)
from `cd(Γ(X, U), I₀) ≤ d`, and assumptions (4) and (6) from conditions (c) and (d) of
[Stacks, Tag 0EJF] on the completed stalks of `(𝒢ₙ)` at the points of `U ∩ T'`. -/
public def depthTwoBootstrapSituation
    (hdualU : letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
      letI := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
      ∃ ω : DerivedCategory (ModuleCat.{u} Γ(X, U)), Dualizing.IsDualizingComplex ω)
    (hcd : letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
      Stacks.LocalCohomology.cohomologicalDimension Γ(X, U) (I.ideal ⟨U, hU⟩)
        (Ideal.fg_of_isNoetherianRing _) ≤ d)
    (hc : ∀ x : U, x.1 ∈ T' → ∀ p : PrimeSpectrum (completedLocalRing I x.1),
      ¬ completedLocalIdeal I x.1 ≤ p.asIdeal →
      adicClosedFibreThrough I x.1 p ≠ {completedMaximalIdeal I x.1} →
      1 ≤ completedStalkDepth I G x.1 p ∨
        enatToEInt (completedStalkDepth I G x.1 p) +
            krullDimToEInt (ringKrullDim (completedLocalRing I x.1 ⧸ p.asIdeal)) >
          ((1 + d : ℤ) : EInt))
    (hd : ∀ x : U, x.1 ∈ T' → ∀ p : PrimeSpectrum (completedLocalRing I x.1),
      p.asIdeal ≠ completedMaximalIdeal I x.1 →
      adicClosedFibreThrough I x.1 p = {completedMaximalIdeal I x.1} →
      ((1 : ℕ) : ℕ∞) < completedStalkDepth I G x.1 p) :
    BootstrapSituation.{u, u, u} :=
  letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI := finite_completedFormalSections hU G
  have he : ∀ a ∈ ((I.ideal ⟨U, hU⟩).map
      (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))) ^ 0,
      ∀ x ∈ LinearMap.ker (LinearMap.id : completedFormalSections U hU G →ₗ[AdicCompletion
          (I.ideal ⟨U, hU⟩) Γ(X, U)] completedFormalSections U hU G),
        a • x = 0 := fun a _ x hx => by
    rw [LinearMap.mem_ker, LinearMap.id_apply] at hx
    rw [hx, smul_zero]
  { A := AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)
    I := (I.ideal ⟨U, hU⟩).map (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))
    M := completedFormalSections U hU G
    T := PrimeSpectrum.comap (algebraMap Γ(X, U) (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))) ⁻¹'
      primesIn hU T'
    subset_adicLocus := fun q hq => by
      rw [← completedAffineLocus_eq_preimage_primesIn hU hT'Y] at hq
      exact hq.1
    stableUnderSpecialization :=
      (stableUnderSpecialization_primesIn hU hT').preimage (PrimeSpectrum.continuous_comap _)
    s := 1
    d := d
    dualizing := by
      obtain ⟨K, hK⟩ := hdualU
      exact ⟨_, Dualizing.isDualizingComplex_adicCompletion (I.ideal ⟨U, hU⟩) K hK⟩
    cohomologicalDimension_le :=
      (Stacks.LocalCohomology.cohomologicalDimension_map_le _ _ _).trans hcd
    depth_or_depth_add_dimension := by
      rw [← completedAffineLocus_eq_preimage_primesIn hU hT'Y]
      exact depth_or_depth_add_dimension_of_completedStalkDepth hU G (levelEquiv G hU)
        (fun h z => levelEquiv_transitionMap hU G h z) LinearMap.id Function.surjective_id 0 he
        hdualU T' d hc
    completedLocalDepth := by
      rw [← completedAffineLocus_eq_preimage_primesIn hU hT'Y]
      exact completedLocalDepth_of_completedStalkDepth hU G (levelEquiv G hU)
        (fun h z => levelEquiv_transitionMap hU G h z) LinearMap.id Function.surjective_id 0 he
        T' 1 hd }

include hT' hT'Y in
/-- **Essential constancy of `{H¹_{T'_A}(M_A/(I₀A)ⁿM_A)}`**, by Theorem [Stacks, Tag 0EIE] in
degree `1 = s` for `depthTwoBootstrapSituation`. -/
public theorem isEssentiallyConstantPro_completedFormalSectionsTower
    (hdualU : letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
      letI := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
      ∃ ω : DerivedCategory (ModuleCat.{u} Γ(X, U)), Dualizing.IsDualizingComplex ω)
    (hcd : letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
      Stacks.LocalCohomology.cohomologicalDimension Γ(X, U) (I.ideal ⟨U, hU⟩)
        (Ideal.fg_of_isNoetherianRing _) ≤ d)
    (hc : ∀ x : U, x.1 ∈ T' → ∀ p : PrimeSpectrum (completedLocalRing I x.1),
      ¬ completedLocalIdeal I x.1 ≤ p.asIdeal →
      adicClosedFibreThrough I x.1 p ≠ {completedMaximalIdeal I x.1} →
      1 ≤ completedStalkDepth I G x.1 p ∨
        enatToEInt (completedStalkDepth I G x.1 p) +
            krullDimToEInt (ringKrullDim (completedLocalRing I x.1 ⧸ p.asIdeal)) >
          ((1 + d : ℤ) : EInt))
    (hd : ∀ x : U, x.1 ∈ T' → ∀ p : PrimeSpectrum (completedLocalRing I x.1),
      p.asIdeal ≠ completedMaximalIdeal I x.1 →
      adicClosedFibreThrough I x.1 p = {completedMaximalIdeal I x.1} →
      ((1 : ℕ) : ℕ∞) < completedStalkDepth I G x.1 p) :
    letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    CategoryTheory.EssentiallyConstantPro.IsEssentiallyConstantPro
      (completedFormalSectionsTower hU G ⋙
        Stacks.LocalCohomology.localCohomologyWithSupportInModuleFunctor.{u, u}
          (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U))
          ((PrimeSpectrum.comap (algebraMap Γ(X, U)
            (AdicCompletion (I.ideal ⟨U, hU⟩) Γ(X, U)))) ⁻¹' primesIn hU T') 1) := by
  obtain ⟨⟨j, σ, h⟩, -⟩ := Stacks.LocalCohomology.Bootstrap.essentiallyConstant_and_consequences
    (depthTwoBootstrapSituation hU hT' hT'Y G d hdualU hcd hc hd) 1 le_rfl
  exact ⟨_, j, σ, h⟩

end Stacks.Algebraization

end
