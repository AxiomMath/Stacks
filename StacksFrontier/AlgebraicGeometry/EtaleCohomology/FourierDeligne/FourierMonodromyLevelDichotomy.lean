module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierSubsheafDichotomyMonodromyTwist
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.AffineLineTopDirectImageRankOne
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.MonodromySubmoduleShortExact
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTransformConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LevelDichotomyBasePoint

/-!
# The level dichotomy for the stable submodules of the monodromy of `H¹(Φ F)`

Let `k` be a finite field, `Λ` a finite commutative ring in which `q = #k` is invertible, `ψ` an
additive character of `k` with values in `Λ` and `∑ ψ = 0`, `Φ` the Fourier transform on
`D⁺(𝔸¹_k, Λ)` and `F` étale-locally free of finite rank on `𝔸¹_k` whose monodromy at one
geometric point satisfies the level dichotomy at `ℓ, N, c₀` (Tag 0DV5). Then:

* for every short exact sequence `0 ⟶ A ⟶ H¹(Φ(F[0])) ⟶ Q ⟶ 0` with `A`, `Q` locally constant
  with finite values on a nonempty open `V` and `Q` without sections supported off `V`, either
  `ℓ^N` kills `A` or `ℓ^{c₀}` kills `Q`
  (`Stacks.EtaleCohomology.fourier_subsheaf_level_dichotomy_of_basePoint`): this is
  `Stacks.EtaleCohomology.fourier_subsheaf_level_dichotomy_of_twist_monodromy` with the
  invertibility of `H²(R f_! Λ)` on `Spec k`
  (`Stacks.EtaleCohomology.exists_invertible_homology_two_derivedLowerShriek_tensorUnit`), the
  constructibility of `A` (a subsheaf of the constructible `H¹(Φ(F[0]))`, Stacks 09BH (3)) and the
  independence of the base point discharged;
* if `H¹(Φ(F[0]))` is lisse on a connected open `V` with a geometric point `v̄`, every
  `π₁(V, v̄)`-stable submodule `W` of its monodromy module `M` at `v̄` is killed by `ℓ^N` or
  contains `ℓ^{c₀} M` (`Stacks.EtaleCohomology.fourier_monodromy_level_dichotomy`), through the
  short exact sequence attached to `W`
  (`Stacks.EtaleCohomology.exists_shortExact_of_monodromy_submodule`).

This is step (d) of the single-level argument for the irreducibility of the Fourier transform in
Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), in the form consumed by
the comparison with the representation `τ`.

## Main results

* `Stacks.EtaleCohomology.fourier_subsheaf_level_dichotomy_of_basePoint`.
* `Stacks.EtaleCohomology.fourier_monodromy_level_dichotomy`.

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
  Sheaf.monoidalCategory isMonoidal_W_etaleModules

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
  (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj (cover k (Polynomial k) Polynomial.X))

local notation "𝔸f" => affineLineStructureMap k

/-- **The level dichotomy (S6, step (d)), from the monodromy of `F` at one geometric point**:
`Stacks.EtaleCohomology.fourier_subsheaf_level_dichotomy_of_twist_monodromy` with the invertibility
of `H²(R f_! Λ)`, the constructibility of `A` and the dichotomy at the other geometric points
discharged. -/
theorem fourier_subsheaf_level_dichotomy_of_basePoint (hψ : ∑ a : k, ψ a = 0)
    (hq : IsUnit (Fintype.card k : Λ)) (j : CompactificationOf (Over.mk 𝔸f))
    (jQ : CompactificationOf (Over.mk (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f)))
    (F : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) (hF : IsLocallyFreeEtaleModule Λ F)
    {A Q : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))}
    (α : A ⟶ (DerivedCategory.Plus.homologyFunctor _ 1).obj
      ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))
    (β : (DerivedCategory.Plus.homologyFunctor _ 1).obj
      ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ⟶ Q)
    (w : α ≫ β = 0) (hS : (ShortComplex.mk α β w).ShortExact)
    {V : Scheme.{u}} (jV : V ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion jV] [Nonempty V]
    (hA : Stacks.ConstantSheaf.IsLocallyConstantWith Λ V.smallEtaleTopology
      (fun E => Module.Finite Λ E) ((etaleModuleInverseImage.{u, 0} Λ jV).obj A))
    (hQ : Stacks.ConstantSheaf.IsLocallyConstantWith Λ V.smallEtaleTopology
      (fun E => Module.Finite Λ E) ((etaleModuleInverseImage.{u, 0} Λ jV).obj Q))
    (hQm : Mono ((etaleModuleInverseImageAdj.{u, 0} Λ jV).unit.app Q)) (ℓ N c₀ : ℕ)
    (x₀ : GeometricPoint (Spec (.of (Polynomial k))))
    (hdich : ContinuousModuleLevelDichotomy
      ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B
        (B.obj _ (schemeSizeBelow_spec_polynomial k B)) x₀ Λ).functor.obj
        ⟨F, isFiniteTypeLocallyConstant_of_isLocallyConstantWith F hF⟩) ℓ N c₀) :
    ℓ ^ N • 𝟙 A = 0 ∨ ℓ ^ c₀ • 𝟙 Q = 0 := by
  have : IsNoetherianRing Λ := inferInstance
  obtain ⟨hT, T', hT', ⟨e⟩, ⟨e'⟩⟩ :=
    exists_invertible_homology_two_derivedLowerShriek_tensorUnit k Λ hq j
  have : ConnectedSpace (B.obj _ (schemeSizeBelow_spec_polynomial k B)).1 :=
    inferInstanceAs (ConnectedSpace (Spec (.of (Polynomial k))))
  have : Mono α := hS.mono_f
  have hAc : IsConstructibleEtaleModule Λ A :=
    isConstructibleEtaleModule_of_mono_small α
      (isConstructibleEtaleModule_homology_fourierTransform k Λ ψ B p₀ j F
        (isConstructibleEtaleModule_of_isFiniteTypeLocallyConstant Λ
          (isFiniteTypeLocallyConstant_of_isLocallyConstantWith F hF)) 1)
  have hd : ∀ x : GeometricPoint (Spec (.of (Polynomial k))), ContinuousModuleLevelDichotomy
      ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B
        (B.obj _ (schemeSizeBelow_spec_polynomial k B)) x Λ).functor.obj
        ⟨F, isFiniteTypeLocallyConstant_of_isLocallyConstantWith F hF⟩) ℓ N c₀ := fun x =>
    continuousModuleLevelDichotomy_of_basePoint B (B.obj _ (schemeSizeBelow_spec_polynomial k B))
      x₀ x (isFiniteTypeLocallyConstant_of_isLocallyConstantWith F hF) hdich
  exact fourier_subsheaf_level_dichotomy_of_twist_monodromy k Λ ψ B p₀ hψ hq j jQ F hF α β w hS
    hAc jV hA hQ hQm ℓ N c₀ T' hT hT' e e' hd

/-- **The level dichotomy for the stable submodules of the monodromy of `H¹(Φ F)`.** If
`H¹(Φ(F[0]))` is locally constant of finite type on a connected open `V` with a geometric point
`v̄`, and the monodromy of `F` at one geometric point satisfies the level dichotomy at `ℓ, N, c₀`,
then every `π₁(V, v̄)`-stable submodule `W` of the monodromy module `M` of `H¹(Φ(F[0]))|_V` at `v̄`
is killed by `ℓ^N` or contains `ℓ^{c₀} M`. -/
theorem fourier_monodromy_level_dichotomy (hψ : ∑ a : k, ψ a = 0)
    (hq : IsUnit (Fintype.card k : Λ)) (j : CompactificationOf (Over.mk 𝔸f))
    (jQ : CompactificationOf (Over.mk (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f)))
    (F : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) (hF : IsLocallyFreeEtaleModule Λ F)
    (VB : B.Scheme) [ConnectedSpace VB.1] (jV : VB.1 ⟶ Spec (.of (Polynomial k)))
    [IsOpenImmersion jV] (v : GeometricPoint VB.1)
    (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ VB.1.smallEtaleTopology
      ((etaleModuleInverseImage.{u, 0} Λ jV).obj
        ((DerivedCategory.Plus.homologyFunctor _ 1).obj
          ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))))
    (ℓ N c₀ : ℕ) (x₀ : GeometricPoint (Spec (.of (Polynomial k))))
    (hdich : ContinuousModuleLevelDichotomy
      ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B
        (B.obj _ (schemeSizeBelow_spec_polynomial k B)) x₀ Λ).functor.obj
        ⟨F, isFiniteTypeLocallyConstant_of_isLocallyConstantWith F hF⟩) ℓ N c₀)
    (W : Submodule Λ ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B VB v
      Λ).functor.obj ⟨_, hG⟩).obj.obj.obj.V)
    (hW : ∀ h, ∀ x ∈ W, (((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B VB v
      Λ).functor.obj ⟨_, hG⟩).obj.obj.obj.ρ h).hom x ∈ W) :
    (∀ x ∈ W, ℓ ^ N • x = 0) ∨ (∀ x, ℓ ^ c₀ • x ∈ W) := by
  obtain ⟨A, Q, α, β, w, hS, hA, hQ, hQm, h₁, h₂⟩ :=
    exists_shortExact_of_monodromy_submodule B VB jV v _ hG W hW
  have : Nonempty VB.1 := ⟨v.hom.base (IsLocalRing.closedPoint v.residueField)⟩
  rcases fourier_subsheaf_level_dichotomy_of_basePoint k Λ ψ B p₀ hψ hq j jQ F hF α β w hS jV hA
    hQ hQm ℓ N c₀ x₀ hdich with h | h
  · exact Or.inl (nsmul_eq_zero_of_nsmul_finiteTypeContinuousModuleOfStableι
      ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B VB v Λ).functor.obj ⟨_, hG⟩)
      W hW _ (h₁ _ h))
  · exact Or.inr (nsmul_mem_of_nsmul_finiteTypeContinuousModuleQuotientπ
      ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B VB v Λ).functor.obj ⟨_, hG⟩)
      W hW _ (h₂ _ h))

end Stacks.EtaleCohomology

end
