module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ConstructibleLocallyFreeTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ConstructibilityUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompactSupportFiniteness

/-!
# The Fourier transform of a constructible sheaf

Let `k` be a finite field, `Λ` a finite commutative ring, `ψ` an additive character of `k` with
values in `Λ` and `Φ(K) = R pr₂!(pr₁⁻¹ K ⊗ μ⁻¹ L_ψ)` the Fourier transform on `D⁺(𝔸¹_k, Λ)`. For a
constructible sheaf `A` of `Λ`-modules on `𝔸¹_k`:

* the integrand `pr₁⁻¹ A ⊗ μ⁻¹ L_ψ` is constructible ([Stacks, Tag 095G] and the tensor product
  with the locally free kernel, `isConstructibleEtaleModule_tensor_of_isLocallyFreeEtaleModule`);
* every cohomology sheaf `Hⁱ(Φ(A[0]))` is constructible ([Stacks, Tag 0GL0]);
* every cohomology sheaf `Hⁱ(Φ(A[0]))` has finite geometric stalks ([Stacks, Tag 0GKR] on the
  geometric fibres, `finite_globalSections_inverseImage_homology_fourierTransform`).

Constructible sheaves have finite geometric stalks
(`finite_globalSections_inverseImage_of_isConstructible`), so the class of constructible sheaves
is stable under `A ↦ Hⁱ(Φ(A[0]))` and supplies the finiteness hypotheses of the single-level
argument for the irreducibility of the Fourier transform in Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `finite_globalSections_inverseImage_of_isConstructible`.
* `isConstructibleEtaleModule_fourierIntegrand`.
* `isConstructibleEtaleModule_homology_fourierTransform`.
* `finite_globalSections_inverseImage_homology_fourierTransform_of_isConstructible`.

## Implementation notes

The Fourier transform lives in the standard model `HasDerivedCategory.standard`, and so do the
statements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  HasDerivedCategory.standard etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

section Sheaf

variable (Λ : Type) [CommRing Λ] [Finite Λ]

/-- **A constructible sheaf has finite geometric stalks**: its inverse image to the spectrum of
an algebraically closed field is constructible ([Stacks, Tag 095G]), and the global sections of a
constructible sheaf there are a finite module. -/
theorem finite_globalSections_inverseImage_of_isConstructible {X : Scheme.{u}}
    {A : EtaleModules.{u, 0} Λ X} (hA : IsConstructibleEtaleModule Λ A) (Ω : Type u) [Field Ω]
    [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ X) :
    Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
      ((etaleModuleInverseImage.{u, 0} Λ w).obj A)) := by
  have : IsNoetherianRing Λ := inferInstance
  have := module_finite_etaleModuleGlobalSections_of_isConstructibleEtaleModule Λ Ω _
    (isConstructibleEtaleModule_etaleModuleInverseImage Λ w A hA)
  exact Module.finite_of_finite Λ

end Sheaf

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
  (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj (cover k (Polynomial k) Polynomial.X))

local notation "𝔸f" => affineLineStructureMap k

/-- The second projection of `𝔸¹_k ×_k 𝔸¹_k` is locally of finite type. -/
private theorem locallyOfFiniteType_pullback_snd_affineLineStructureMap (K : Type u) [Field K] :
    LocallyOfFiniteType (pullback.snd (affineLineStructureMap K) (affineLineStructureMap K)) := by
  have : LocallyOfFiniteType (affineLineStructureMap K) := locallyOfFiniteType_specPolynomial K
  exact MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
    (IsPullback.of_hasPullback (affineLineStructureMap K) (affineLineStructureMap K)) inferInstance

omit [Fintype k] in
/-- The affine plane `𝔸¹_k ×_k 𝔸¹_k` is Noetherian: it is of finite type over the Noetherian
scheme `𝔸¹_k`. -/
theorem isNoetherian_pullback_affineLineStructureMap :
    AlgebraicGeometry.IsNoetherian (pullback 𝔸f 𝔸f) := by
  have := locallyOfFiniteType_pullback_snd_affineLineStructureMap k
  have : IsLocallyNoetherian (pullback 𝔸f 𝔸f) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd 𝔸f 𝔸f)
  have : CompactSpace ↥(pullback 𝔸f 𝔸f) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd 𝔸f 𝔸f)
  exact ⟨⟩

/-- **The integrand `pr₁⁻¹ A ⊗ μ⁻¹ L_ψ` of the Fourier transform of a constructible sheaf is
constructible**: `pr₁⁻¹ A` is constructible ([Stacks, Tag 095G]) and `μ⁻¹ L_ψ` is étale-locally
free of rank one. -/
theorem isConstructibleEtaleModule_fourierIntegrand
    (A : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) (hA : IsConstructibleEtaleModule Λ A) :
    IsConstructibleEtaleModule Λ ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst 𝔸f 𝔸f)).obj A ⊗
      (etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj
        (affineLineArtinSchreierSheaf k Λ ψ B p₀)) :=
  have : IsNoetherianRing Λ := inferInstance
  have := isNoetherian_pullback_affineLineStructureMap k
  isConstructibleEtaleModule_tensor_of_isLocallyFreeEtaleModule Λ
    (isConstructibleEtaleModule_etaleModuleInverseImage Λ _ A hA)
    (isLocallyFreeEtaleModule_fourierKernel k Λ ψ B p₀)

/-- **The cohomology sheaves of the Fourier transform of a constructible sheaf have finite
geometric stalks.** -/
theorem finite_globalSections_inverseImage_homology_fourierTransform_of_isConstructible
    (j : CompactificationOf (Over.mk 𝔸f)) (A : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k))))
    (hA : IsConstructibleEtaleModule Λ A) (i : ℤ) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (w : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))) :
    Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
      ((etaleModuleInverseImage.{u, 0} Λ w).obj ((DerivedCategory.Plus.homologyFunctor _ i).obj
        ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj A))))) :=
  finite_globalSections_inverseImage_homology_fourierTransform k Λ ψ B p₀ j A
    (isConstructibleEtaleModule_fourierIntegrand k Λ ψ B p₀ A hA) i Ω w

/-- **The cohomology sheaves of the Fourier transform of a constructible sheaf are
constructible** ([Stacks, Tag 0GL0] for `R pr₂!` of the constructible integrand). -/
theorem isConstructibleEtaleModule_homology_fourierTransform (j : CompactificationOf (Over.mk 𝔸f))
    (A : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) (hA : IsConstructibleEtaleModule Λ A)
    (i : ℤ) :
    IsConstructibleEtaleModule Λ ((DerivedCategory.Plus.homologyFunctor _ i).obj
      ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj A))) := by
  have : IsNoetherianRing Λ := inferInstance
  let pr₁ := pullback.fst 𝔸f 𝔸f
  let pr₂ := pullback.snd 𝔸f 𝔸f
  let 𝓛 := (etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj
    (affineLineArtinSchreierSheaf k Λ ψ B p₀)
  have h𝓛e := isExactTensorRight_fourierKernel k Λ ψ B p₀
  let G := (etaleModuleInverseImage.{u, 0} Λ pr₁).obj A ⊗ 𝓛
  let jP := j.baseChange (IsPullback.of_hasPullback 𝔸f 𝔸f)
  have := h𝓛e.1
  have := h𝓛e.2.1
  have := h𝓛e.2.2
  let eT : (fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj A) ≅
      (derivedLowerShriek.{u, 0} pr₂ jP Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G) :=
    (derivedLowerShriek.{u, 0} pr₂ jP Λ).mapIso
      ((etaleModuleDerivedTensorRight Λ 𝓛 h𝓛e).mapIso
          ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
            (etaleModuleInverseImage.{u, 0} Λ pr₁) 0).app A) ≪≫
        (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
          (MonoidalCategory.tensorRight 𝓛) 0).app _)
  have : LocallyOfFiniteType pr₂ := locallyOfFiniteType_pullback_snd_affineLineStructureMap k
  have : IsSeparated pr₂ := MorphismProperty.of_isPullback (P := @IsSeparated)
    (IsPullback.of_hasPullback 𝔸f 𝔸f) inferInstance
  have : QuasiCompact pr₂ := MorphismProperty.of_isPullback (P := @QuasiCompact)
    (IsPullback.of_hasPullback 𝔸f 𝔸f) inferInstance
  have : LocallyOfFinitePresentation pr₂ :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 ‹_›
  let B' := BigEtaleSite.ofSet ({(pullback 𝔸f 𝔸f : Scheme.{u}), Spec (.of (Polynomial k))} :
    Set Scheme.{u})
  have hX : B'.Contains (pullback 𝔸f 𝔸f) := BigEtaleSite.contains_ofSet _ (by simp)
  have hY : B'.Contains (Spec (.of (Polynomial k))) := BigEtaleSite.contains_ofSet _ (by simp)
  have : CompactSpace (B'.obj _ hY).obj :=
    inferInstanceAs (CompactSpace (Spec (.of (Polynomial k))))
  have : QuasiSeparatedSpace (B'.obj _ hY).obj :=
    inferInstanceAs (QuasiSeparatedSpace (Spec (.of (Polynomial k))))
  have hG : IsBigSiteConstructibleEtaleModule B' (B'.obj _ hX) Λ G :=
    (isConstructibleEtaleModule_iff_isConstructibleModuleSheaf Λ B' hX G).1
      (isConstructibleEtaleModule_fourierIntegrand k Λ ψ B p₀ A hA)
  have h := (isConstructibleEtaleModule_homology_derivedLowerShriek_of_isConstructible B'
    (X := B'.obj _ hX) (Y := B'.obj _ hY) pr₂ jP Λ).1
    ((DerivedCategory.Plus.singleFunctor _ 0).obj G)
    (fun q => ⟨isConstructibleEtaleModule_homology_singleFunctor hG q,
      isTorsionEtaleModule_of_finite Λ _ _⟩) i
  exact (IsConstructibleEtaleModule Λ).prop_of_iso
    ((DerivedCategory.Plus.homologyFunctor _ i).mapIso eT.symm)
    ((isConstructibleEtaleModule_iff_isConstructibleModuleSheaf Λ B' hY _).2 h)

end Stacks.EtaleCohomology

end
