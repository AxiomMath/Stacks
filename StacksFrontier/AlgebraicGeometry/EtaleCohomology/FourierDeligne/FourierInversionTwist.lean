module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.RelativeAffineLineTopLisse

/-!
# `F' = H²(Φ(Φ F))` is `ν⁻¹ F` twisted by a sheaf pulled back from `Spec k`

Let `pr : P ⟶ W` be the base change of the affine line `𝔸¹_k ⟶ Spec k` along `πW : W ⟶ Spec k`
and `M` étale-locally free of finite rank on `W`. The projection formula and proper base change
give `Hⁱ(R pr_!(pr⁻¹ M)) ≅ πW⁻¹ Hⁱ(R f_! Λ) ⊗ M`, `f : 𝔸¹_k ⟶ Spec k`. For the Fourier transform
`Φ` on `𝔸¹_k`, Fourier inversion `Φ(Φ(F[0])) ≅ R pr_!(pr⁻¹ ν⁻¹ F)` (`ν = -1`) then gives

`H²(Φ(Φ(F[0]))) ≅ 𝔸f⁻¹ H²(R f_! Λ) ⊗ ν⁻¹ F`.

This is the identification of the monodromy of `F'` with the monodromy of `ν⁻¹ F` twisted by the
rank-one sheaf `H²(R f_! Λ)` on `Spec k`, used for the level dichotomy of `F'` in Laumon's proof
of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH). The isomorphisms are those of the proof
of `isFiniteTypeLocallyConstant_homology_derivedLowerShriek_inverseImage_affineLine`.

## Main results

* `Stacks.EtaleCohomology.nonempty_homology_derivedLowerShriek_inverseImage_affineLine_iso`.
* `Stacks.EtaleCohomology.nonempty_homology_fourierTransform_comp_iso_tensor`.

## Implementation notes

`Rf_!` and the Fourier transform live in the standard model `HasDerivedCategory.standard`, and so
do the statements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
  Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  HasDerivedCategory.standard etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [CommRing Λ] [Finite Λ] (k : Type u) [Field k] [Fintype k]

local notation "𝔸f" => affineLineStructureMap k

omit [Fintype k] in
attribute [local instance] etaleModuleInverseImageSheafPullbackMonoidal
  hasSheafify_etaleModules_fourierKernel in
/-- **`Hⁱ(R pr_!(pr⁻¹ M)) ≅ πW⁻¹ Hⁱ(R f_! Λ) ⊗ M`** on the affine line `pr : P ⟶ W` over a
`k`-scheme `W`, for `M` étale-locally free of finite rank on `W` (projection formula and proper
base change). -/
theorem nonempty_homology_derivedLowerShriek_inverseImage_affineLine_iso
    (j : CompactificationOf (Over.mk 𝔸f)) {W P : Scheme.{u}}
    (πW : W ⟶ Spec (.of k)) {T : P ⟶ Spec (.of (Polynomial k))} {pr : P ⟶ W}
    (sq : IsPullback T pr 𝔸f πW) (M : EtaleModules.{u, 0} Λ W)
    (hM : IsLocallyFreeEtaleModule Λ M) (i : ℤ) :
    Nonempty ((DerivedCategory.Plus.homologyFunctor _ i).obj
        ((derivedLowerShriek.{u, 0} pr (j.baseChange sq) Λ).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((etaleModuleInverseImage.{u, 0} Λ pr).obj M))) ≅
      (etaleModuleInverseImage.{u, 0} Λ πW).obj ((DerivedCategory.Plus.homologyFunctor _ i).obj
        ((derivedLowerShriek.{u, 0} 𝔸f j Λ).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            (𝟙_ (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))))))) ⊗ M) := by
  have : IsNoetherianRing Λ := inferInstance
  have : LocallyOfFiniteType 𝔸f := locallyOfFiniteType_specPolynomial k
  have : LocallyOfFiniteType pr :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq inferInstance
  have : IsSeparated pr := MorphismProperty.of_isPullback (P := @IsSeparated) sq inferInstance
  have : QuasiCompact pr := MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  let H := DerivedCategory.Plus.homologyFunctor (EtaleModules.{u, 0} Λ W) i
  let S := DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ P) 0
  let I := fun {X Y : Scheme.{u}} (a : X ⟶ Y) => etaleModuleInverseImage.{u, 0} Λ a
  -- `Hⁱ(R pr_! Λ_P)` is pulled back from `Spec k`
  let K₀ := (DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ
    (Spec (.of (Polynomial k)))) 0).obj (𝟙_ (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))))
  have := isIso_derivedLowerShriekBaseChange_app Λ sq j K₀ (isTorsionPlus_of_finite Λ _ K₀)
  let eU : (etaleModuleDerivedInverseImagePlus.{u, 0} Λ T).obj K₀ ≅ S.obj (𝟙_ _) :=
    (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle (I T) 0).app _ ≪≫
      S.mapIso (Functor.Monoidal.εIso (etaleModuleInverseImage.{u, 0} Λ T)).symm
  let e₀ : H.obj ((derivedLowerShriek.{u, 0} pr (j.baseChange sq) Λ).obj (S.obj (𝟙_ _))) ≅
      (I πW).obj ((DerivedCategory.Plus.homologyFunctor _ i).obj
        ((derivedLowerShriek.{u, 0} 𝔸f j Λ).obj K₀)) :=
    H.mapIso ((derivedLowerShriek.{u, 0} pr (j.baseChange sq) Λ).mapIso eU.symm ≪≫
      (asIso ((derivedLowerShriekBaseChange.{u, 0} Λ sq j).app K₀)).symm) ≪≫
      (etaleModuleInverseImageHomologyIso Λ πW _ i).symm
  -- the projection formula
  have hf := additive_preservesFiniteLimits_preservesFiniteColimits_tensorRight_inverseImage
    pr M hM
  have hg :=
    additive_preservesFiniteLimits_preservesFiniteColimits_tensorRight_of_isLocallyConstantWith M hM
  have := hf.1; have := hf.2.1; have := hf.2.2
  have := hg.1; have := hg.2.1; have := hg.2.2
  let eP := (derivedLowerShriekProjectionIso pr (j.baseChange sq) M hM).app (S.obj (𝟙_ _))
  let eL : S.obj ((I pr).obj M) ≅
      (MonoidalCategory.tensorRight ((I pr).obj M)).mapDerivedCategoryPlus.obj (S.obj (𝟙_ _)) :=
    S.mapIso (λ_ _).symm ≪≫
      ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
        (MonoidalCategory.tensorRight ((I pr).obj M)) 0).app _).symm
  let eH : H.obj ((MonoidalCategory.tensorRight M).mapDerivedCategoryPlus.obj
        ((derivedLowerShriek.{u, 0} pr (j.baseChange sq) Λ).obj (S.obj (𝟙_ _)))) ≅
      H.obj ((derivedLowerShriek.{u, 0} pr (j.baseChange sq) Λ).obj (S.obj (𝟙_ _))) ⊗ M :=
    H.mapIso ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso
        (MonoidalCategory.tensorRight M)).app _) ≪≫
      (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
        (MonoidalCategory.tensorRight M) i).app _
  let e : H.obj ((derivedLowerShriek.{u, 0} pr (j.baseChange sq) Λ).obj (S.obj ((I pr).obj M))) ≅
      H.obj ((derivedLowerShriek.{u, 0} pr (j.baseChange sq) Λ).obj (S.obj (𝟙_ _))) ⊗ M :=
    H.mapIso ((derivedLowerShriek.{u, 0} pr (j.baseChange sq) Λ).mapIso eL ≪≫ eP) ≪≫ eH
  exact ⟨e ≪≫ whiskerRightIso e₀ M⟩

variable (ψ : AddChar k Λ) (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj (cover k (Polynomial k) Polynomial.X))

/-- **`Hⁱ(Φ(Φ(F[0]))) ≅ 𝔸f⁻¹ Hⁱ(R f_! Λ) ⊗ ν⁻¹ F`** for `F` étale-locally free of finite rank on
`𝔸¹_k`: Fourier inversion `Φ(Φ(F[0])) ≅ R pr_!(pr⁻¹(ν⁻¹ F))` on the antidiagonal, then the
projection formula and proper base change. For `i = 2` this is `F'`. -/
theorem nonempty_homology_fourierTransform_comp_iso_tensor (hψ : ∑ a : k, ψ a = 0)
    (hq : IsUnit (Fintype.card k : Λ)) (j : CompactificationOf (Over.mk 𝔸f))
    (jQ : CompactificationOf (Over.mk (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f)))
    (F : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) (hF : IsLocallyFreeEtaleModule Λ F)
    (i : ℤ) :
    Nonempty ((DerivedCategory.Plus.homologyFunctor _ i).obj
        ((fourierTransform k Λ ψ B p₀ j).obj ((fourierTransform k Λ ψ B p₀ j).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) ≅
      (etaleModuleInverseImage.{u, 0} Λ 𝔸f).obj ((DerivedCategory.Plus.homologyFunctor _ i).obj
        ((derivedLowerShriek.{u, 0} 𝔸f j Λ).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            (𝟙_ (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))))))) ⊗
        (etaleModuleInverseImage.{u, 0} Λ (affineLineNeg k)).obj F) := by
  have : IsNoetherianRing Λ := inferInstance
  have hFf := finite_globalSections_inverseImage_of_isConstructible Λ
    (isConstructibleEtaleModule_of_isLocallyFreeEtaleModule Λ hF)
  obtain ⟨e₁⟩ := nonempty_fourierTransform_comp_iso k Λ ψ B p₀ hψ hq j jQ F hFf
  obtain ⟨e₂⟩ := nonempty_fourierAntidiagonalTransform_iso k Λ j jQ F
  obtain ⟨h⟩ := nonempty_homology_derivedLowerShriek_inverseImage_affineLine_iso Λ k j
    𝔸f (isPullback_fourierAntidiagonal k) _
    (isLocallyFreeEtaleModule_inverseImage Λ (affineLineNeg k) hF) i
  exact ⟨(DerivedCategory.Plus.homologyFunctor _ i).mapIso (e₁ ≪≫ e₂) ≪≫ h⟩

end Stacks.EtaleCohomology

end
