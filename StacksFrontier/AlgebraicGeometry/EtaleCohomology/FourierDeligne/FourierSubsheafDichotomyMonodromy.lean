module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierSubsheafDichotomy
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LisseSubsheafMonodromyDichotomy
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ConstructibleKernelCokernel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.RelativeAffineLineTopLisse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTransformConstructible

/-!
# The level dichotomy for `H¹(Φ F)`, from the monodromy of `F' = H²(Φ(Φ F))`

Let `k` be a finite field, `Λ` a finite commutative ring in which `q = #k` is invertible, `ψ` an
additive character of `k` with values in `Λ` and `∑ ψ = 0`, and `Φ` the Fourier transform on
`D⁺(𝔸¹_k, Λ)`. Let `F` be étale-locally free of finite rank on `𝔸¹_k`, `G = H¹(Φ(F[0]))`,
`F' = H²(Φ(Φ(F[0])))` (locally constant of finite type), and `0 ⟶ A ⟶ G ⟶ Q ⟶ 0` short exact
with `A` constructible, `A` and `Q` locally constant with finite values on a nonempty open `V`,
and `Q` without sections supported off `V`.

Suppose that at every geometric point the monodromy module of `F'` (Tag 0DV5) satisfies the level
dichotomy at the exponents `N, c₀` of `ℓ`: every `π₁`-stable submodule `W` with `ℓ^N W ≠ 0`
contains `ℓ^{c₀}` times the module. Then `ℓ^N • 𝟙 A = 0` or `ℓ^{c₀} • 𝟙 Q = 0`.

This is `Stacks.EtaleCohomology.fourier_subsheaf_level_dichotomy` with its sheaf-level dichotomy
hypothesis discharged: the image `K` of `H¹(Φ A) ⟶ H¹(Φ G) ⊆ F'` is constructible, hence locally
constant on a nonempty open `U`, and there
`Stacks.EtaleCohomology.exists_inverseImage_comp_eq_nsmul_of_monodromy` gives `ℓ^{c₀} F'|_U ⊆ K|_U`
from the monodromy. It is step (d) of the single-level argument for the irreducibility of the
Fourier transform in Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).
The only named input is `Stacks.EtaleCohomology.FourierTwistNoConstantQuotientInput`.

## Main results

* `Stacks.EtaleCohomology.fourier_subsheaf_level_dichotomy_of_monodromy`.

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

/-- **The level dichotomy (S6, step (d)), from the monodromy of `F'`**: for `F` étale-locally
free of finite rank on `𝔸¹_k`, a short exact sequence `0 ⟶ A ⟶ H¹(Φ(F[0])) ⟶ Q ⟶ 0` with `A`
constructible, `A`, `Q` locally constant with finite values on a nonempty open `V` and `Q` without
sections supported off `V`, if the monodromy module of `F' = H²(Φ(Φ(F[0])))` satisfies the level
dichotomy at `ℓ, N, c₀` at every geometric point, then either `ℓ^N` kills `A` or `ℓ^{c₀}` kills
`Q`. -/
theorem fourier_subsheaf_level_dichotomy_of_monodromy
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
    (hAc : IsConstructibleEtaleModule Λ A)
    {V : Scheme.{u}} (jV : V ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion jV] [Nonempty V]
    (hA : Stacks.ConstantSheaf.IsLocallyConstantWith Λ V.smallEtaleTopology
      (fun E => Module.Finite Λ E) ((etaleModuleInverseImage.{u, 0} Λ jV).obj A))
    (hQ : Stacks.ConstantSheaf.IsLocallyConstantWith Λ V.smallEtaleTopology
      (fun E => Module.Finite Λ E) ((etaleModuleInverseImage.{u, 0} Λ jV).obj Q))
    (hQm : Mono ((etaleModuleInverseImageAdj.{u, 0} Λ jV).unit.app Q)) (ℓ N c₀ : ℕ)
    (hdich : ∀ x : GeometricPoint (Spec (.of (Polynomial k))), ContinuousModuleLevelDichotomy
      ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B
        (B.obj _ (schemeSizeBelow_spec_polynomial k B)) x Λ).functor.obj
        ⟨_, isFiniteTypeLocallyConstant_homology_two_fourierTransform_comp Λ k ψ B p₀ hψ hq j jQ
          F hF 2⟩) ℓ N c₀) :
    ℓ ^ N • 𝟙 A = 0 ∨ ℓ ^ c₀ • 𝟙 Q = 0 := by
  have : Mono α := hS.mono_f
  have : Epi β := hS.epi_g
  have : IsNoetherianRing Λ := inferInstance
  let Φ := fourierTransform k Λ ψ B p₀ j
  let := fourierTransformCommShift k Λ ψ B p₀ j
  have := isTriangulated_fourierTransform k Λ ψ B p₀ j
  have : Φ.Additive := inferInstance
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
  have hFc := isConstructibleEtaleModule_of_isLocallyFreeEtaleModule Λ hF
  have hFf := finite_globalSections_inverseImage_of_isConstructible Λ hFc
  obtain ⟨⟨m₀, hm₀⟩, -⟩ := exists_mono_epi_fourierTransform_homology_one k Λ ψ B p₀ hψ hq j jQ F
    hF hFf
  -- the image `K` of `H¹(Φ α)` inside `F'`
  let κ := image.ι a ≫ m₀
  have hκ : ℓ ^ N • κ ≠ 0 := by
    intro h0
    apply h
    have h1 : ℓ ^ N • image.ι a = 0 := by
      rwa [← cancel_mono m₀, zero_comp, Preadditive.nsmul_comp]
    rw [← image.fac a, ← Preadditive.comp_nsmul, h1, comp_zero]
  -- `K` is constructible, hence locally constant on a nonempty open `U`
  have hH := fun G (hG : IsConstructibleEtaleModule Λ G) =>
    isConstructibleEtaleModule_homology_fourierTransform k Λ ψ B p₀ j G hG 1
  have hGc := hH F hFc
  have hKc : IsConstructibleEtaleModule Λ (image a) := by
    refine (IsConstructibleEtaleModule Λ).prop_of_iso (Abelian.imageIsoImage a) ?_
    exact isConstructibleEtaleModule_kernel_of_isConstructible Λ _ (hH _ hGc)
      (isConstructibleEtaleModule_cokernel_of_isConstructible Λ a (hH _ hAc) (hH _ hGc))
  obtain ⟨U, hU, hKU, -⟩ :=
    exists_opens_isFiniteTypeLocallyConstant_of_isConstructibleEtaleModule Λ hKc hKc
  have : Nonempty U := hU.to_subtype
  have : IsIntegral (Spec (.of (Polynomial k))) := inferInstance
  have : IsNormal (Spec (.of (Polynomial k))) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed (Polynomial k))
  obtain ⟨r, hr⟩ := exists_inverseImage_comp_eq_nsmul_of_monodromy B
    (schemeSizeBelow_spec_polynomial k B) κ
    (isFiniteTypeLocallyConstant_homology_two_fourierTransform_comp Λ k ψ B p₀ hψ hq j jQ F hF 2)
    U hKU ℓ N c₀ hdich hκ
  let jU := U.ι
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
    refine ⟨U.toScheme, jU, inferInstance, inferInstance, ?_⟩
    have hp : L.map (factorThruImage (ℓ ^ c₀ • b)) = 0 := by
      rwa [← cancel_mono (L.map (image.ι (ℓ ^ c₀ • b))), zero_comp, ← Functor.map_comp,
        image.fac]
    exact IsZero.of_epi_eq_zero _ hp
  exact nsmul_id_eq_zero_of_nsmul_homology_one_fourierTransform_map_eq_comp k Λ ψ B p₀ hT hψ hq
    j jQ F hF β jV hQ hQm (ℓ ^ c₀) (factorThruImage (ℓ ^ c₀ • b)) (image.ι (ℓ ^ c₀ • b))
    (image.fac _).symm hI

end Stacks.EtaleCohomology

end
