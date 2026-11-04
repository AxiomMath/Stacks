module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierSubsheafAnnihilator
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTransformFirstCohomologyKernel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierGenericCoinvariantCurveHalf

/-!
# Mechanism (b) for a subsheaf of `H¹(Φ F)`, `F` lisse

Let `k` be a finite field, `Λ` a finite commutative ring in which `q = #k` is invertible, `ψ` an
additive character of `k` with values in `Λ` and `∑ ψ = 0`, and `Φ` the Fourier transform on
`D⁺(𝔸¹_k, Λ)`. Let `F` be étale-locally free of finite rank on `𝔸¹_k`, `G = H¹(Φ(F[0]))`,
`C = H²(Φ(F[0]))` and `α : A ⟶ G` a monomorphism such that `A` is locally constant with finite
values on a nonempty open `V`. If `n ∈ ℕ` kills `H¹(Φ(α))`, then `n` kills `A`, provided
`F' = H²(Φ(Φ(F[0])))` and `H⁰(Φ(C[0]))` are locally constant of finite type.

The hypotheses of `Stacks.EtaleCohomology.nsmul_id_eq_zero_of_isPunctual_of_isLocallyConstantWith`
are discharged as follows:

* `G` has finite geometric stalks, `G` being constructible (Tag 0GL0 for the Fourier transform of
  the locally free `F`);
* `H⁰(Φ(G[0])) = 0` (`Stacks.EtaleCohomology.isZero_homology_zero_fourierTransform_homology_one`);
* `H²(Φ(A[0]))` is punctual: this is the generic vanishing of geometric coinvariants (L2),
  `Stacks.EtaleCohomology.FourierGenericCoinvariantVanishingInput`, which follows from
  `Stacks.EtaleCohomology.FourierTwistNoConstantQuotientInput`
  (`Stacks.EtaleCohomology.fourierGenericCoinvariantVanishingInput_of_twist`);
* `H¹(Φ(G[0]))` and `H²(Φ(G[0]))` are locally constant: they are the kernel and the cokernel of
  a map `F' ⟶ H⁰(Φ(C[0]))`
  (`Stacks.EtaleCohomology.isFiniteTypeLocallyConstant_homology_fourierTransform_homology_one`).

This is the mechanism (b) (`ℓᵉ K(S) = 0 ⇒ ℓᵉ S = 0`) of the single-level argument for the
irreducibility of the Fourier transform in Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.isPunctualEtaleModule_homology_two_fourierTransform_of_twist`
* `Stacks.EtaleCohomology.nsmul_id_eq_zero_of_nsmul_homology_one_fourierTransform_homology_one_map`

## Implementation notes

The Fourier transform lives in the standard model `HasDerivedCategory.standard`, and so do the
statements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
  (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj (cover k (Polynomial k) Polynomial.X))

local notation "𝔸f" => affineLineStructureMap k

/-- **(L2) `H²(Φ(H[0]))` is punctual** for a sheaf `H` on `𝔸¹_k` which is locally constant with
finite values on a nonempty open, given the generic absence of constant simple quotients of the
twisted sheaves `FourierTwistNoConstantQuotientInput`. -/
theorem isPunctualEtaleModule_homology_two_fourierTransform_of_twist
    (hT : FourierTwistNoConstantQuotientInput.{u}) (hψ : ∑ a : k, ψ a = 0)
    (hq : IsUnit (Fintype.card k : Λ)) (j : CompactificationOf (Over.mk 𝔸f))
    (H : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) {V : Scheme.{u}}
    (jV : V ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion jV] [Nonempty V]
    (hH : Stacks.ConstantSheaf.IsLocallyConstantWith Λ V.smallEtaleTopology
      (fun E => Module.Finite Λ E) ((etaleModuleInverseImage.{u, 0} Λ jV).obj H)) :
    IsPunctualEtaleModule Λ ((DerivedCategory.Plus.homologyFunctor _ 2).obj
      ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj H))) :=
  fourierGenericCoinvariantVanishingInput_of_twist hT k Λ ψ B p₀ hψ hq j H jV hH

/-- **Mechanism (b) for a subsheaf of `G = H¹(Φ(F[0]))`**: for `F` étale-locally free of finite
rank, `α : A ⟶ G` a monomorphism with `A` locally constant with finite values on a nonempty open,
`F' = H²(Φ(Φ(F[0])))` and `H⁰(Φ(C[0]))` (`C = H²(Φ(F[0]))`) locally constant of finite type,
`n • H¹(Φ(α)) = 0` implies `n • 𝟙 A = 0`. -/
theorem nsmul_id_eq_zero_of_nsmul_homology_one_fourierTransform_homology_one_map
    (hT : FourierTwistNoConstantQuotientInput.{u}) (hψ : ∑ a : k, ψ a = 0)
    (hq : IsUnit (Fintype.card k : Λ)) (j : CompactificationOf (Over.mk 𝔸f))
    (jQ : CompactificationOf (Over.mk (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f)))
    (F : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) (hF : IsLocallyFreeEtaleModule Λ F)
    (hF' : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ
      (Spec (.of (Polynomial k))).smallEtaleTopology
      ((DerivedCategory.Plus.homologyFunctor _ 2).obj
        ((fourierTransform k Λ ψ B p₀ j).obj ((fourierTransform k Λ ψ B p₀ j).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))))
    (hC : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ
      (Spec (.of (Polynomial k))).smallEtaleTopology
      ((DerivedCategory.Plus.homologyFunctor _ 0).obj
        ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((DerivedCategory.Plus.homologyFunctor _ 2).obj
            ((fourierTransform k Λ ψ B p₀ j).obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))))))
    {A : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))}
    (α : A ⟶ (DerivedCategory.Plus.homologyFunctor _ 1).obj
      ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))
    [Mono α] (n : ℕ)
    (hu : n • (DerivedCategory.Plus.homologyFunctor _ 1).map
      ((fourierTransform k Λ ψ B p₀ j).map ((DerivedCategory.Plus.singleFunctor _ 0).map α)) = 0)
    {V : Scheme.{u}} (jV : V ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion jV] [Nonempty V]
    (hA : Stacks.ConstantSheaf.IsLocallyConstantWith Λ V.smallEtaleTopology
      (fun E => Module.Finite Λ E) ((etaleModuleInverseImage.{u, 0} Λ jV).obj A)) :
    n • 𝟙 A = 0 := by
  have : IsNoetherianRing Λ := inferInstance
  have hFc := isConstructibleEtaleModule_of_isLocallyFreeEtaleModule Λ hF
  have hGf := finite_globalSections_inverseImage_of_isConstructible Λ
    (isConstructibleEtaleModule_homology_fourierTransform k Λ ψ B p₀ j F hFc 1)
  have hG0 := isZero_homology_zero_fourierTransform_homology_one k Λ ψ B p₀ hψ hq j jQ F hF
    (finite_globalSections_inverseImage_of_isConstructible Λ hFc)
  obtain ⟨hL₁, hL₂⟩ := isFiniteTypeLocallyConstant_homology_fourierTransform_homology_one k Λ ψ
    B p₀ hψ hq j jQ F hF hF' hC
  exact nsmul_id_eq_zero_of_isPunctual_of_isLocallyConstantWith k Λ ψ B p₀ hψ hq j jQ α n hGf
    hG0 hu (isPunctualEtaleModule_homology_two_fourierTransform_of_twist k Λ ψ B p₀ hT hψ hq j A
      jV hA) (ModuleCat.isFG Λ) (ModuleCat.isFG Λ) hL₁ hL₂

end Stacks.EtaleCohomology

end
