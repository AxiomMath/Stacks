module

public import StacksFrontier.AlgebraicGeometry.AffinePushforwardStalk.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.AlgebraDictionary
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.FlatDimensionTransfer
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeMapSectionsInjectivity
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.CanonicalDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.AffineFiber
public import StacksFrontier.RingTheory.Flat.DevissageLocalizeAwayProjective

/-!
# Spreading out the free map of a dévissage stage over a neighbourhood of the base point

Let `(Z, Y, i, π, 𝒢, α)` be a stage of a complete dévissage of `ℱ/X/S` over `s`, so that
`α : 𝒪_Y^{⊕ r} ⟶ π_* 𝒢` is an isomorphism over the residue field of the generic point `ξ` of the
fibre `Y_s`. If `π_* 𝒢` is flat over `S` at `ξ`, Stacks 05IA (1) ⟹ (2) produces an element
`a ∈ Γ(S, 𝒪_S)` not vanishing at `s` such that the map of global sections of `α`, localized at
`a`, is universally injective over `Γ(S, 𝒪_S)`. This is the step of the proof of Stacks 05UF, in
the case `d₁ > d`, which replaces `S` by a standard open neighbourhood of `s` over which `α` is
`S`-universally injective.

## Main results

* `AlgebraicGeometry.DevissageStage.exists_universallyInjective_away`: the element `a` above.

## Implementation notes

All schemes of a stage are affine, and the statement is read on the rings of global sections
`R = Γ(S, ⊤)`, `A = Γ(Y, ⊤)` and `N = Γ(π_* 𝒢, ⊤)`. The point `s` corresponds to the prime
`r` of `R` read off `S ≅ Spec R`, and `ξ` to the prime `rA` of `A`
(`AlgebraicGeometry.asIdeal_isoSpec_hom_fiberι_eq_map`). The generic-fibre condition of the stage
becomes bijectivity of the map of sections over the residue field of `rA`
(`AlgebraicGeometry.DevissageStage.fiber_bijective_sectionsAlpha`), and the flatness at `ξ`
becomes flatness over `R` of the localization of `N` at `rA`. The ring form of Stacks
05IA, `Module.exists_universallyInjective_localizedModule_away_of_flat_localizedModule`, then
applies to the map of sections precomposed with the identification
`A^{⊕ r} ≅ Γ(𝒪_Y^{⊕ r}, ⊤)`.

## References

* [Stacks Project, Tag 05IA](https://stacks.math.columbia.edu/tag/05IA)
* [Stacks Project, Tag 05UF](https://stacks.math.columbia.edu/tag/05UF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Universal injectivity of a localized map survives precomposing the map with a linear
equivalence: the localization of the equivalence is surjective. -/
theorem injective_rTensor_localizedModuleMap_of_comp_linearEquiv {R A M M' N : Type u}
    [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module A M] [Module R M]
    [IsScalarTower R A M] [AddCommGroup M'] [Module A M'] [Module R M'] [IsScalarTower R A M']
    [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
    (φ : M →ₗ[A] N) (e : M' ≃ₗ[A] M) (T : Submonoid R) (Q : Type u) [AddCommGroup Q]
    [Module R Q]
    (h : Function.Injective (((LocalizedModule.map T
      ((φ ∘ₗ e.toLinearMap).restrictScalars R)).restrictScalars R).rTensor Q)) :
    Function.Injective (((LocalizedModule.map T (φ.restrictScalars R)).restrictScalars R).rTensor
      Q) := by
  have hcomp : ((LocalizedModule.map T ((φ ∘ₗ e.toLinearMap).restrictScalars R)).restrictScalars
      R) = ((LocalizedModule.map T (φ.restrictScalars R)).restrictScalars R) ∘ₗ
        ((LocalizedModule.map T (e.toLinearMap.restrictScalars R)).restrictScalars R) := by
    refine LinearMap.ext fun x ↦ ?_
    induction x using LocalizedModule.induction_on with
    | _ m t => simp [LocalizedModule.map_mk]
  have hsurj : Function.Surjective
      ((LocalizedModule.map T (e.toLinearMap.restrictScalars R)).restrictScalars R) := by
    intro x
    induction x using LocalizedModule.induction_on with
    | _ m t => exact ⟨LocalizedModule.mk (e.symm m) t, by simp [LocalizedModule.map_mk]⟩
  rw [hcomp, LinearMap.rTensor_comp] at h
  exact Function.Injective.of_comp_right h (LinearMap.rTensor_surjective Q hsurj)

/-- Bijectivity of a map after tensoring survives pre- and postcomposing the map with linear
equivalences. -/
private theorem bijective_rTensor_of_eq_comp {R M M' N N' : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N'] (φ : M →ₗ[R] N) (u : N' ≃ₗ[R] N) (ψ : M' →ₗ[R] N')
    (v : M ≃ₗ[R] M') (h : φ = u.toLinearMap ∘ₗ ψ ∘ₗ v.toLinearMap) (K : Type*)
    [AddCommGroup K] [Module R K] (hψ : Function.Bijective (ψ.rTensor K)) :
    Function.Bijective (φ.rTensor K) := by
  subst h
  rw [LinearMap.rTensor_comp, LinearMap.rTensor_comp]
  exact (LinearEquiv.bijective (LinearEquiv.rTensor K u)).comp
    (hψ.comp (LinearEquiv.bijective (LinearEquiv.rTensor K v)))

namespace DevissageStage

/-- **Stacks Project, Tag 05IA (1) ⟹ (2), on a stage of a complete dévissage.** If the direct
image `π_* 𝒢` of a stage is flat over the base at the generic point of the fibre of `Y` over `s`,
then there is a function `a` on `S` not vanishing at `s` such that the map of global sections of
the free map `α` of the stage, localized at `a`, is universally injective over `Γ(S, ⊤)`. -/
theorem exists_universallyInjective_away
    {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] {F : X.Modules}
    [F.IsQuasicoherent] [F.IsFiniteType] {s : S} (stage : DevissageStage f F s)
    (hf : FinitePresentation f) [F.IsFinitePresentation]
    (hflat : IsFlatOverAt stage.oneStep.g.toLRSHom.toShHom
      ((Scheme.Modules.pushforward stage.oneStep.π).obj stage.oneStep.G)
      (stage.oneStep.g.fiberι s stage.genericPoint)) :
    letI : Algebra Γ(S, ⊤) Γ(stage.oneStep.Y, ⊤) := stage.oneStep.g.appTop.hom.toAlgebra
    letI : Module Γ(S, ⊤)
        Γ(Scheme.Modules.free stage.oneStep.Y (ULift.{u} (Fin stage.rank)), ⊤) :=
      Module.compHom _ stage.oneStep.g.appTop.hom
    letI : Module Γ(S, ⊤)
        Γ((Scheme.Modules.pushforward stage.oneStep.π).obj stage.oneStep.G, ⊤) :=
      Module.compHom _ stage.oneStep.g.appTop.hom
    haveI : IsScalarTower Γ(S, ⊤) Γ(stage.oneStep.Y, ⊤)
        Γ(Scheme.Modules.free stage.oneStep.Y (ULift.{u} (Fin stage.rank)), ⊤) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    haveI : IsScalarTower Γ(S, ⊤) Γ(stage.oneStep.Y, ⊤)
        Γ((Scheme.Modules.pushforward stage.oneStep.π).obj stage.oneStep.G, ⊤) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    ∃ a : Γ(S, ⊤), s ∈ S.basicOpen a ∧ ∀ (Q : Type u) [AddCommGroup Q] [Module Γ(S, ⊤) Q],
      Function.Injective (((LocalizedModule.map (Submonoid.powers a)
        ((schemeAppLinearMap (G := Scheme.Modules.free stage.oneStep.Y
          (ULift.{u} (Fin stage.rank))) stage.alpha ⊤).restrictScalars Γ(S, ⊤))).restrictScalars
            Γ(S, ⊤)).rTensor Q) := by
  have hY : IsAffine stage.oneStep.Y := stage.oneStep.affine_Y
  have hS : IsAffine S := stage.oneStep.affine_S
  let : Algebra Γ(S, ⊤) Γ(stage.oneStep.Y, ⊤) := stage.oneStep.g.appTop.hom.toAlgebra
  let : Module Γ(S, ⊤)
      Γ(Scheme.Modules.free stage.oneStep.Y (ULift.{u} (Fin stage.rank)), ⊤) :=
    Module.compHom _ stage.oneStep.g.appTop.hom
  let : Module Γ(S, ⊤)
      Γ((Scheme.Modules.pushforward stage.oneStep.π).obj stage.oneStep.G, ⊤) :=
    Module.compHom _ stage.oneStep.g.appTop.hom
  have : IsScalarTower Γ(S, ⊤) Γ(stage.oneStep.Y, ⊤)
      Γ(Scheme.Modules.free stage.oneStep.Y (ULift.{u} (Fin stage.rank)), ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower Γ(S, ⊤) Γ(stage.oneStep.Y, ⊤)
      Γ((Scheme.Modules.pushforward stage.oneStep.π).obj stage.oneStep.G, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : LocallyOfFinitePresentation f := hf.1
  have hsm : Algebra.Smooth Γ(S, ⊤) Γ(stage.oneStep.Y, ⊤) :=
    stage.oneStep.algebraSmooth_g_appTop
  have hgi : GeometricallyIrreducible
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) Γ(stage.oneStep.Y, ⊤)))) :=
    stage.oneStep.geometricallyIrreducible_specMap_algebraMap
  have : GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) Γ(stage.oneStep.Y, ⊤)))) :=
    geometricallyIntegral_of_smooth_of_geometricallyIrreducible Γ(S, ⊤) Γ(stage.oneStep.Y, ⊤)
  have hNfp := stage.oneStep.isFinitePresentation_pushforward
  have : IsFinite stage.oneStep.π := stage.oneStep.finite
  have : stage.oneStep.G.IsQuasicoherent := stage.oneStep.quasi_coherent_G
  have : ((Scheme.Modules.pushforward stage.oneStep.π).obj stage.oneStep.G).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom _ _
  have : Module.FinitePresentation Γ(stage.oneStep.Y, ⊤)
      Γ((Scheme.Modules.pushforward stage.oneStep.π).obj stage.oneStep.G, ⊤) :=
    Stacks.AlgebraicGeometry.ModuleLimits.finitePresentation_sectionsTop _
  -- the primes of `s` and of the generic point `ξ` of the fibre
  let r : Ideal Γ(S, ⊤) := (S.isoSpec.hom s).asIdeal
  let z : stage.oneStep.Y := stage.oneStep.g.fiberι s stage.genericPoint
  let q : Ideal Γ(stage.oneStep.Y, ⊤) := (stage.oneStep.Y.isoSpec.hom z).asIdeal
  have hgz : stage.oneStep.g z = s := by
    have h : z ∈ stage.oneStep.g ⁻¹' {s} :=
      (stage.oneStep.g.range_fiberι s) ▸ Set.mem_range_self stage.genericPoint
    simpa using h
  have hqr : q.under Γ(S, ⊤) = r := by
    have h := comap_algebraMap_isoSpec_hom stage.oneStep.g rfl z
    rw [hgz] at h
    exact congrArg PrimeSpectrum.asIdeal h
  -- the free map, on the free module `Fin r → A`
  let e : (Fin stage.rank → Γ(stage.oneStep.Y, ⊤)) ≃ₗ[Γ(stage.oneStep.Y, ⊤)]
      Γ(Scheme.Modules.free stage.oneStep.Y (ULift.{u} (Fin stage.rank)), ⊤) :=
    (Finsupp.linearEquivFunOnFinite Γ(stage.oneStep.Y, ⊤) Γ(stage.oneStep.Y, ⊤)
        (Fin stage.rank)).symm ≪≫ₗ
      Finsupp.domLCongr (Equiv.ulift.{u, 0} (α := Fin stage.rank)).symm ≪≫ₗ
      (freeSectionsEquiv stage.oneStep.Y (ULift.{u} (Fin stage.rank))).symm
  let a' : (Fin stage.rank → Γ(stage.oneStep.Y, ⊤)) →ₗ[Γ(stage.oneStep.Y, ⊤)]
      Γ((Scheme.Modules.pushforward stage.oneStep.π).obj stage.oneStep.G, ⊤) :=
    schemeAppLinearMap (G := Scheme.Modules.free stage.oneStep.Y (ULift.{u} (Fin stage.rank)))
      stage.alpha ⊤ ∘ₗ e.toLinearMap
  -- the generic-fibre condition
  have halpha :
      let := Ideal.isPrime_map_of_geometricallyIntegral Γ(S, ⊤) Γ(stage.oneStep.Y, ⊤) r
      Function.Bijective
        (a'.rTensor (Ideal.map (algebraMap Γ(S, ⊤) Γ(stage.oneStep.Y, ⊤)) r).ResidueField) := by
    let : Module Γ(stage.oneStep.Y, ⊤) Γ(stage.oneStep.G, ⊤) :=
      Module.compHom Γ(stage.oneStep.G, ⊤) stage.oneStep.π.appTop.hom
    have hb := stage.fiber_bijective_sectionsAlpha r rfl
    rw [LinearMap.baseChange_eq_ltensor] at hb
    have hb' := (LinearMap.lTensor_bij_iff_rTensor_bij _ _).1 hb
    have heq : a' = (OneStepDevissage.pushforwardSectionsEquiv stage.oneStep.π
        stage.oneStep.G).symm.toLinearMap ∘ₗ stage.sectionsAlpha ∘ₗ
          (Finsupp.linearEquivFunOnFinite Γ(stage.oneStep.Y, ⊤) Γ(stage.oneStep.Y, ⊤)
            (Fin stage.rank)).symm.toLinearMap := by
      refine LinearMap.ext fun x ↦ ?_
      simp only [a', e, LinearMap.comp_apply, LinearEquiv.coe_coe, DevissageStage.sectionsAlpha,
        LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
      rfl
    exact bijective_rTensor_of_eq_comp _ _ _ _ heq _ hb'
  -- flatness at `ξ`
  have hflatq : Module.Flat Γ(S, ⊤)
      (LocalizedModule q.primeCompl
        Γ((Scheme.Modules.pushforward stage.oneStep.π).obj stage.oneStep.G, ⊤)) := by
    have hUV : (⊤ : stage.oneStep.Y.Opens) ≤ stage.oneStep.g ⁻¹ᵁ (⊤ : S.Opens) :=
      fun _ _ ↦ trivial
    have hkey := flat_localizedModule_sections_of_isFlatOverAt stage.oneStep.g
      ((Scheme.Modules.pushforward stage.oneStep.π).obj stage.oneStep.G) (isAffineOpen_top S)
      (isAffineOpen_top stage.oneStep.Y) hUV (Set.mem_univ z) hflat
    rwa [Stacks.AffineAlgebraEquivalence.appLE_top_top stage.oneStep.g hUV,
      primeIdealOf_top] at hkey
  obtain ⟨a, ha, hinj⟩ :=
    Module.exists_universallyInjective_localizedModule_away_of_flat_localizedModule
      Γ(S, ⊤) Γ(stage.oneStep.Y, ⊤) r q hqr _ stage.rank a' halpha hflatq
  refine ⟨a, ?_, fun Q _ _ ↦ injective_rTensor_localizedModuleMap_of_comp_linearEquiv
    (schemeAppLinearMap (G := Scheme.Modules.free stage.oneStep.Y (ULift.{u} (Fin stage.rank)))
      stage.alpha ⊤) e _ Q (hinj Q)⟩
  rwa [← Scheme.map_PrimeSpectrum_basicOpen_of_affine]

end DevissageStage

end AlgebraicGeometry

end
