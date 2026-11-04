module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierSubsheafDichotomyMonodromy
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.SubsheafLevelDichotomyTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierInversionTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTwistNoConstantQuotientProof

/-!
# The level dichotomy for `H¹(Φ F)`, from the subsheaf dichotomy of `ν⁻¹ F`

Let `k` be a finite field, `Λ` a finite commutative ring in which `q = #k` is invertible, `ψ` an
additive character of `k` with values in `Λ` and `∑ ψ = 0`, and `Φ` the Fourier transform on
`D⁺(𝔸¹_k, Λ)`. Let `F` be étale-locally free of finite rank on `𝔸¹_k`, `G = H¹(Φ(F[0]))` and
`0 ⟶ A ⟶ G ⟶ Q ⟶ 0` short exact with `A` constructible, `A` and `Q` locally constant with
finite values on a nonempty open `V`, and `Q` without sections supported off `V`.

* If `F' = H²(Φ(Φ(F[0])))` satisfies the subsheaf level dichotomy at `ℓ, N, c₀`
  (`Stacks.EtaleCohomology.SubsheafLevelDichotomy`), then `ℓ^N • 𝟙 A = 0` or `ℓ^{c₀} • 𝟙 Q = 0`
  (`Stacks.EtaleCohomology.fourier_subsheaf_level_dichotomy_of_subsheafLevelDichotomy`). This is
  `Stacks.EtaleCohomology.fourier_subsheaf_level_dichotomy_of_monodromy` with its monodromy
  hypothesis on `F'` replaced by the sheaf-level dichotomy it is used for, and with the input
  `Stacks.EtaleCohomology.FourierTwistNoConstantQuotientInput` discharged
  (`Stacks.EtaleCohomology.fourierTwistNoConstantQuotientInput`).
* `F' ≅ 𝔸f⁻¹ T ⊗ ν⁻¹ F` with `T = H²(R f_! Λ)` on `Spec k`
  (`Stacks.EtaleCohomology.nonempty_homology_fourierTransform_comp_iso_tensor`). When `T` is
  étale-locally free and invertible with étale-locally free inverse, the subsheaf dichotomy of
  `F'` follows from that of `ν⁻¹ F` (`Stacks.EtaleCohomology.SubsheafLevelDichotomy.tensor`), so
  the conclusion holds under the subsheaf dichotomy of `ν⁻¹ F`
  (`Stacks.EtaleCohomology.fourier_subsheaf_level_dichotomy_of_twist`).

This is step (d) of the single-level argument for the irreducibility of the Fourier transform in
Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), with the rank-one twist
of Fourier inversion removed.

## Main results

* `Stacks.EtaleCohomology.fourier_subsheaf_level_dichotomy_of_subsheafLevelDichotomy`.
* `Stacks.EtaleCohomology.fourier_subsheaf_level_dichotomy_of_twist`.

## Implementation notes

The Fourier transform lives in the standard model `HasDerivedCategory.standard`, and so do the
statements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
  (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj (cover k (Polynomial k) Polynomial.X))

local notation "𝔸f" => affineLineStructureMap k

/-- **The level dichotomy (S6, step (d)), from the subsheaf dichotomy of `F'`**: for `F`
étale-locally free of finite rank on `𝔸¹_k`, a short exact sequence `0 ⟶ A ⟶ H¹(Φ(F[0])) ⟶ Q ⟶ 0`
with `A` constructible, `A`, `Q` locally constant with finite values on a nonempty open `V` and
`Q` without sections supported off `V`, if `F' = H²(Φ(Φ(F[0])))` satisfies the subsheaf level
dichotomy at `ℓ, N, c₀`, then either `ℓ^N` kills `A` or `ℓ^{c₀}` kills `Q`. -/
theorem fourier_subsheaf_level_dichotomy_of_subsheafLevelDichotomy (hψ : ∑ a : k, ψ a = 0)
    (hq : IsUnit (Fintype.card k : Λ)) (j : CompactificationOf (Over.mk 𝔸f))
    (jQ : CompactificationOf (Over.mk (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f)))
    (F : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) (hF : IsLocallyFreeEtaleModule Λ F)
    {A Q : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))}
    (α : A ⟶ (DerivedCategory.Plus.homologyFunctor _ 1).obj
      ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))
    (β : (DerivedCategory.Plus.homologyFunctor _ 1).obj
      ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ⟶ Q)
    (w : α ≫ β = 0) (hS : (ShortComplex.mk α β w).ShortExact)
    (hAc : IsConstructibleEtaleModule Λ A)
    {V : Scheme.{u}} (jV : V ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion jV] [Nonempty V]
    (hA : Stacks.ConstantSheaf.IsLocallyConstantWith Λ V.smallEtaleTopology
      (fun E => Module.Finite Λ E) ((etaleModuleInverseImage.{u, 0} Λ jV).obj A))
    (hQ : Stacks.ConstantSheaf.IsLocallyConstantWith Λ V.smallEtaleTopology
      (fun E => Module.Finite Λ E) ((etaleModuleInverseImage.{u, 0} Λ jV).obj Q))
    (hQm : Mono ((etaleModuleInverseImageAdj.{u, 0} Λ jV).unit.app Q)) (ℓ N c₀ : ℕ)
    (hdich : SubsheafLevelDichotomy ((DerivedCategory.Plus.homologyFunctor _ 2).obj
      ((fourierTransform k Λ ψ B p₀ j).obj ((fourierTransform k Λ ψ B p₀ j).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) ℓ N c₀) :
    ℓ ^ N • 𝟙 A = 0 ∨ ℓ ^ c₀ • 𝟙 Q = 0 := by
  have : Mono α := hS.mono_f
  have : Epi β := hS.epi_g
  let Φ := fourierTransform k Λ ψ B p₀ j
  let := fourierTransformCommShift k Λ ψ B p₀ j
  have := isTriangulated_fourierTransform k Λ ψ B p₀ j
  let S := DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) 0
  let H₁ := DerivedCategory.Plus.homologyFunctor
    (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) 1
  let a := H₁.map (Φ.map (S.map α))
  let b := H₁.map (Φ.map (S.map β))
  have hab : a ≫ b = 0 := by simp only [a, b, ← Functor.map_comp, w, Functor.map_zero]
  by_cases h : ℓ ^ N • a = 0
  · exact Or.inl (nsmul_id_eq_zero_of_nsmul_homology_one_fourierTransform_map_of_twist k Λ ψ B p₀
      fourierTwistNoConstantQuotientInput hψ hq j jQ F hF α (ℓ ^ N) h jV hA)
  right
  have hFf := finite_globalSections_inverseImage_of_isConstructible Λ
    (isConstructibleEtaleModule_of_isLocallyFreeEtaleModule Λ hF)
  obtain ⟨⟨m₀, hm₀⟩, -⟩ := exists_mono_epi_fourierTransform_homology_one k Λ ψ B p₀ hψ hq j jQ F
    hF hFf
  -- the image `K` of `H¹(Φ α)` inside `F'`
  let κ := image.ι a ≫ m₀
  have hκ : ℓ ^ N • κ ≠ 0 := fun h0 => h <| by
    rw [← image.fac a, ← Preadditive.comp_nsmul, show ℓ ^ N • image.ι a = 0 by
      rwa [← cancel_mono m₀, zero_comp, Preadditive.nsmul_comp], comp_zero]
  -- `K` is constructible, hence locally constant on a nonempty open `U`
  have hGc := isConstructibleEtaleModule_homology_fourierTransform k Λ ψ B p₀ j F
    (isConstructibleEtaleModule_of_isLocallyFreeEtaleModule Λ hF) 1
  have hGc₁ := isConstructibleEtaleModule_homology_fourierTransform k Λ ψ B p₀ j _ hGc 1
  have hKc : IsConstructibleEtaleModule Λ (image a) :=
    (IsConstructibleEtaleModule Λ).prop_of_iso (Abelian.imageIsoImage a)
      (isConstructibleEtaleModule_kernel_of_isConstructible Λ _ hGc₁
        (isConstructibleEtaleModule_cokernel_of_isConstructible Λ a
          (isConstructibleEtaleModule_homology_fourierTransform k Λ ψ B p₀ j _ hAc 1) hGc₁))
  obtain ⟨U, hU, hKU, -⟩ :=
    exists_opens_isFiniteTypeLocallyConstant_of_isConstructibleEtaleModule Λ hKc hKc
  have : Nonempty U := hU.to_subtype
  obtain ⟨r, hr⟩ := hdich κ inferInstance U hU.to_subtype hKU hκ
  let L := etaleModuleInverseImage.{u, 0} Λ U.ι
  have : L.Additive := Functor.additive_of_preserves_binary_products _
  -- `ℓ^{c₀} H¹(Φ β)` vanishes on `U`
  have hιb : image.ι a ≫ b = 0 := by
    rw [← cancel_epi (factorThruImage a), image.fac_assoc, hab, comp_zero]
  have hc : L.map (ℓ ^ c₀ • b) = 0 := by
    have h₁ : L.map (ℓ ^ c₀ • 𝟙 _) ≫ L.map m₀ = L.map m₀ ≫ r ≫ L.map κ := by
      rw [hr]
      simp only [Functor.map_nsmul, CategoryTheory.Functor.map_id, Preadditive.nsmul_comp,
        Preadditive.comp_nsmul, Category.id_comp]
      exact congrArg (fun f => ℓ ^ c₀ • f) (Category.comp_id (L.map m₀)).symm
    have h₂ : L.map (ℓ ^ c₀ • 𝟙 _) = L.map m₀ ≫ r ≫ L.map (image.ι a) := by
      rw [← cancel_mono (L.map m₀), h₁]
      simp only [κ, Functor.map_comp, Category.assoc]
    rw [← Category.id_comp b, ← Preadditive.nsmul_comp, Functor.map_comp, h₂]
    simp only [Category.assoc, ← Functor.map_comp, hιb, Functor.map_zero, comp_zero]
  have hI : IsPunctualEtaleModule Λ (image (ℓ ^ c₀ • b)) := by
    refine ⟨U.toScheme, U.ι, inferInstance, inferInstance, ?_⟩
    have hp : L.map (factorThruImage (ℓ ^ c₀ • b)) = 0 := by
      rwa [← cancel_mono (L.map (image.ι (ℓ ^ c₀ • b))), zero_comp, ← Functor.map_comp,
        image.fac]
    exact IsZero.of_epi_eq_zero _ hp
  exact nsmul_id_eq_zero_of_nsmul_homology_one_fourierTransform_map_eq_comp k Λ ψ B p₀
    fourierTwistNoConstantQuotientInput hψ hq
    j jQ F hF β jV hQ hQm (ℓ ^ c₀) (factorThruImage (ℓ ^ c₀ • b)) (image.ι (ℓ ^ c₀ • b))
    (image.fac _).symm hI

section Twist

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory isMonoidal_W_etaleModules
  etaleModuleInverseImageSheafPullbackMonoidal hasSheafify_etaleModules_fourierKernel

/-- **The level dichotomy (S6, step (d)), from the subsheaf dichotomy of `ν⁻¹ F`**: as
`Stacks.EtaleCohomology.fourier_subsheaf_level_dichotomy_of_subsheafLevelDichotomy`, when
`T = H²(R f_! Λ)` on `Spec k` (`f : 𝔸¹_k ⟶ Spec k`) is étale-locally free with an étale-locally
free inverse `T'`, and `ν⁻¹ F` (`ν = -1`) satisfies the subsheaf level dichotomy at `ℓ, N, c₀`. -/
theorem fourier_subsheaf_level_dichotomy_of_twist (hψ : ∑ a : k, ψ a = 0)
    (hq : IsUnit (Fintype.card k : Λ)) (j : CompactificationOf (Over.mk 𝔸f))
    (jQ : CompactificationOf (Over.mk (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f)))
    (F : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) (hF : IsLocallyFreeEtaleModule Λ F)
    {A Q : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))}
    (α : A ⟶ (DerivedCategory.Plus.homologyFunctor _ 1).obj
      ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))
    (β : (DerivedCategory.Plus.homologyFunctor _ 1).obj
      ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ⟶ Q)
    (w : α ≫ β = 0) (hS : (ShortComplex.mk α β w).ShortExact)
    (hAc : IsConstructibleEtaleModule Λ A)
    {V : Scheme.{u}} (jV : V ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion jV] [Nonempty V]
    (hA : Stacks.ConstantSheaf.IsLocallyConstantWith Λ V.smallEtaleTopology
      (fun E => Module.Finite Λ E) ((etaleModuleInverseImage.{u, 0} Λ jV).obj A))
    (hQ : Stacks.ConstantSheaf.IsLocallyConstantWith Λ V.smallEtaleTopology
      (fun E => Module.Finite Λ E) ((etaleModuleInverseImage.{u, 0} Λ jV).obj Q))
    (hQm : Mono ((etaleModuleInverseImageAdj.{u, 0} Λ jV).unit.app Q)) (ℓ N c₀ : ℕ)
    (T' : EtaleModules.{u, 0} Λ (Spec (.of k)))
    (hT : IsLocallyFreeEtaleModule Λ ((DerivedCategory.Plus.homologyFunctor _ 2).obj
      ((derivedLowerShriek.{u, 0} 𝔸f j Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
        (𝟙_ (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))))))))
    (hT' : IsLocallyFreeEtaleModule Λ T')
    (e : (DerivedCategory.Plus.homologyFunctor _ 2).obj
      ((derivedLowerShriek.{u, 0} 𝔸f j Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
        (𝟙_ (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k))))))) ⊗ T' ≅
      𝟙_ (EtaleModules.{u, 0} Λ (Spec (.of k))))
    (e' : T' ⊗ (DerivedCategory.Plus.homologyFunctor _ 2).obj
      ((derivedLowerShriek.{u, 0} 𝔸f j Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
        (𝟙_ (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k))))))) ≅
      𝟙_ (EtaleModules.{u, 0} Λ (Spec (.of k))))
    (hdich : SubsheafLevelDichotomy ((etaleModuleInverseImage.{u, 0} Λ (affineLineNeg k)).obj F)
      ℓ N c₀) :
    ℓ ^ N • 𝟙 A = 0 ∨ ℓ ^ c₀ • 𝟙 Q = 0 := by
  obtain ⟨eF⟩ := nonempty_homology_fourierTransform_comp_iso_tensor Λ k ψ B p₀ hψ hq j jQ F hF 2
  obtain ⟨e₁⟩ := nonempty_inverseImage_tensor_iso_tensorUnit Λ 𝔸f e
  obtain ⟨e₁'⟩ := nonempty_inverseImage_tensor_iso_tensorUnit Λ 𝔸f e'
  have h₁ := hdich.tensor (isLocallyConstantWith_inverseImage Λ _ 𝔸f hT)
    (isLocallyConstantWith_inverseImage Λ _ 𝔸f hT') e₁ e₁'
  exact fourier_subsheaf_level_dichotomy_of_subsheafLevelDichotomy k Λ ψ B p₀ hψ hq j jQ F hF α β
    w hS hAc jV hA hQ hQm ℓ N c₀ (h₁.of_iso ((β_ _ _) ≪≫ eF.symm))

end Twist

end Stacks.EtaleCohomology

end
