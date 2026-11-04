module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierSubsheafDichotomyTwist
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LevelDichotomyInverseImage
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SectionNormalRange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LocallyFreeDual

/-!
# The level dichotomy for `H¹(Φ F)`, from the monodromy of `F`

Let `k` be a finite field, `Λ` a finite commutative ring in which `q = #k` is invertible, `ψ` an
additive character of `k` with values in `Λ` and `∑ ψ = 0`, `Φ` the Fourier transform on
`D⁺(𝔸¹_k, Λ)` and `F` étale-locally free of finite rank on `𝔸¹_k`. Suppose that `T = H²(R f_! Λ)`
on `Spec k` (`f : 𝔸¹_k ⟶ Spec k`) is étale-locally free with an étale-locally free inverse, and
that the monodromy modules of `F` (Tag 0DV5) satisfy the level dichotomy at `ℓ, N, c₀` at every
geometric point. Then for a short exact sequence `0 ⟶ A ⟶ H¹(Φ(F[0])) ⟶ Q ⟶ 0` with `A`
constructible, `A`, `Q` locally constant with finite values on a nonempty open `V` and `Q` without
sections supported off `V`, either `ℓ^N` kills `A` or `ℓ^{c₀}` kills `Q`.

## Main results

* `Stacks.EtaleCohomology.fourier_subsheaf_level_dichotomy_of_twist_monodromy`: the level
  dichotomy for the subsheaves of `H¹(Φ(F[0]))`, from the level dichotomy of the monodromy
  modules of `F`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits
  Sheaf.monoidalCategory isMonoidal_W_etaleModules

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
  (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj (cover k (Polynomial k) Polynomial.X))

local notation "𝔸f" => affineLineStructureMap k

/-- **The level dichotomy, from the monodromy of `F`**: as
`Stacks.EtaleCohomology.fourier_subsheaf_level_dichotomy_of_twist`, with the subsheaf dichotomy of
`ν⁻¹ F` replaced by the level dichotomy of the monodromy modules of `F` at every geometric
point. -/
theorem fourier_subsheaf_level_dichotomy_of_twist_monodromy (hψ : ∑ a : k, ψ a = 0)
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
    (hdich : ∀ x : GeometricPoint (Spec (.of (Polynomial k))), ContinuousModuleLevelDichotomy
      ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B
        (B.obj _ (schemeSizeBelow_spec_polynomial k B)) x Λ).functor.obj
        ⟨F, isFiniteTypeLocallyConstant_of_isLocallyConstantWith F hF⟩) ℓ N c₀) :
    ℓ ^ N • 𝟙 A = 0 ∨ ℓ ^ c₀ • 𝟙 Q = 0 := by
  let XB := B.obj _ (schemeSizeBelow_spec_polynomial k B)
  let ν : XB ⟶ XB := ObjectProperty.homMk (affineLineNeg k)
  have hν : ∀ y : GeometricPoint XB.1, Function.Surjective (etaleFundamentalGroupMap ν.hom y) :=
    fun y ↦ surjective_etaleFundamentalGroupMap_of_section (affineLineNeg k) (affineLineNeg k)
      (affineLineNeg_comp_affineLineNeg k) y
  have hF' := isFiniteTypeLocallyConstant_etaleModuleInverseImage_of_hom (affineLineNeg k) Λ F
    (isFiniteTypeLocallyConstant_of_isLocallyConstantWith F hF)
  have : IsNormal (Spec (.of (Polynomial k))) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed (Polynomial k))
  have hs := subsheafLevelDichotomy_of_monodromy B (schemeSizeBelow_spec_polynomial k B) hF' ℓ N c₀
    (continuousModuleLevelDichotomy_inverseImage B ν hν _ hF' hdich)
  exact fourier_subsheaf_level_dichotomy_of_twist k Λ ψ B p₀ hψ hq j jQ F hF α β w hS hAc jV hA hQ
    hQm ℓ N c₀ T' hT hT' e e' hs

end Stacks.EtaleCohomology

end
