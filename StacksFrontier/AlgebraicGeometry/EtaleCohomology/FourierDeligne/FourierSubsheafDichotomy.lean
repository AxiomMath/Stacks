module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierSubsheafQuotientAnnihilator
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTransformFirstCohomologySequence

/-!
# The level dichotomy for a short exact sequence of quotients of `H¹(Φ F)`

Let `k` be a finite field, `Λ` a finite commutative ring in which `q = #k` is invertible, `ψ` an
additive character of `k` with values in `Λ` and `∑ ψ = 0`, and `Φ` the Fourier transform on
`D⁺(𝔸¹_k, Λ)`. Let `F` be étale-locally free of finite rank on `𝔸¹_k`, `G = H¹(Φ(F[0]))`,
`F' = H²(Φ(Φ(F[0])))`, and `0 ⟶ A ⟶ G ⟶ Q ⟶ 0` short exact with `A` and `Q` locally constant with
finite values on a nonempty open `V`, and `Q` without sections supported off `V`.

Suppose the *dichotomy for `F'`* at the exponents `N, c₀`: every subsheaf `κ : K ↪ F'` with
`ℓ^N • κ ≠ 0` contains `ℓ^{c₀} F'` on a nonempty open. Then

`ℓ^N • 𝟙 A = 0` or `ℓ^{c₀} • 𝟙 Q = 0`.

This is step (d) of the single-level argument for the irreducibility of the Fourier transform in
Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH):

* if `ℓ^N • H¹(Φ α) = 0`, mechanism (b) gives `ℓ^N • 𝟙 A = 0`;
* otherwise the image `K` of `H¹(Φ α)` in `H¹(Φ G) ⊆ F'` has `ℓ^N • K ≠ 0`, so on a nonempty open
  `U`, `ℓ^{c₀} H¹(Φ G) ⊆ ℓ^{c₀} F' ⊆ K`, which `H¹(Φ β)` kills: the image of
  `ℓ^{c₀} H¹(Φ β)` vanishes on `U`, and mechanism (c) gives `ℓ^{c₀} • 𝟙 Q = 0`.

The only named input is `Stacks.EtaleCohomology.FourierTwistNoConstantQuotientInput`; the
dichotomy for `F'` is the statement about the monodromy of `F'` which the absolute irreducibility
supplies.

## Main results

* `Stacks.EtaleCohomology.fourier_subsheaf_level_dichotomy`.

## Implementation notes

The Fourier transform lives in the standard model `HasDerivedCategory.standard`, and so do the
statements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
  (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj (cover k (Polynomial k) Polynomial.X))

local notation "𝔸f" => affineLineStructureMap k

/-- **The level dichotomy (S6, step (d))**: for `F` étale-locally free of finite rank on `𝔸¹_k`,
a short exact sequence `0 ⟶ A ⟶ H¹(Φ(F[0])) ⟶ Q ⟶ 0` with `A`, `Q` locally constant with finite
values on a nonempty open `V` and `Q` without sections supported off `V`, and the dichotomy for
the subsheaves of `F' = H²(Φ(Φ(F[0])))` at exponents `N, c₀`, either `ℓ^N` kills `A` or `ℓ^{c₀}`
kills `Q`. -/
theorem fourier_subsheaf_level_dichotomy
    (hT : FourierTwistNoConstantQuotientInput.{u}) (hψ : ∑ a : k, ψ a = 0)
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
    (hdich : ∀ {K : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))}
      (κ : K ⟶ (DerivedCategory.Plus.homologyFunctor _ 2).obj
        ((fourierTransform k Λ ψ B p₀ j).obj ((fourierTransform k Λ ψ B p₀ j).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))), Mono κ → ℓ ^ N • κ ≠ 0 →
      ∃ (U : Scheme.{u}) (jU : U ⟶ Spec (.of (Polynomial k))), IsOpenImmersion jU ∧ Nonempty U ∧
        ∃ r : (etaleModuleInverseImage.{u, 0} Λ jU).obj
            ((DerivedCategory.Plus.homologyFunctor _ 2).obj
              ((fourierTransform k Λ ψ B p₀ j).obj ((fourierTransform k Λ ψ B p₀ j).obj
                ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) ⟶
            (etaleModuleInverseImage.{u, 0} Λ jU).obj K,
          r ≫ (etaleModuleInverseImage.{u, 0} Λ jU).map κ = ℓ ^ c₀ • 𝟙 _) :
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
  have hab : a ≫ b = 0 := by
    simp only [a, b, ← Functor.map_comp, w, Functor.map_zero]
  by_cases h : ℓ ^ N • a = 0
  · exact Or.inl (nsmul_id_eq_zero_of_nsmul_homology_one_fourierTransform_map_of_twist k Λ ψ B p₀
      hT hψ hq j jQ F hF α (ℓ ^ N) h jV hA)
  right
  obtain ⟨⟨m₀, hm₀⟩, -⟩ := exists_mono_epi_fourierTransform_homology_one k Λ ψ B p₀ hψ hq j jQ F
    hF (finite_globalSections_inverseImage_of_isConstructible Λ
      (isConstructibleEtaleModule_of_isLocallyFreeEtaleModule Λ hF))
  -- the image `K` of `H¹(Φ α)` inside `F'`
  let κ := image.ι a ≫ m₀
  have hκ : ℓ ^ N • κ ≠ 0 := fun h0 => h <| by
    have h1 : ℓ ^ N • image.ι a = 0 := by
      rwa [← cancel_mono m₀, zero_comp, Preadditive.nsmul_comp]
    rw [← image.fac a, ← Preadditive.comp_nsmul, h1, comp_zero]
  obtain ⟨U, jU, hjU, hU, r, hr⟩ := hdich κ inferInstance hκ
  let L := etaleModuleInverseImage.{u, 0} Λ jU
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
    refine ⟨U, jU, hjU, hU, IsZero.of_epi_eq_zero (L.map (factorThruImage (ℓ ^ c₀ • b))) ?_⟩
    rwa [← cancel_mono (L.map (image.ι (ℓ ^ c₀ • b))), zero_comp, ← Functor.map_comp,
      image.fac]
  exact nsmul_id_eq_zero_of_nsmul_homology_one_fourierTransform_map_eq_comp k Λ ψ B p₀ hT hψ hq
    j jQ F hF β jV hQ hQm (ℓ ^ c₀) (factorThruImage (ℓ ^ c₀ • b)) (image.ι (ℓ ^ c₀ • b))
    (image.fac _).symm hI

end Stacks.EtaleCohomology

end
