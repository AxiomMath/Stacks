module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierInversionExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTransformAmplitude
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.PunctualLisseExtVanishing

/-!
# Mechanism (b): an annihilator of `H¹(Φ(α))` annihilates the subsheaf

Let `k` be a finite field, `Λ` a finite commutative ring in which `q = #k` is invertible, `ψ` an
additive character of `k` with values in `Λ` and `∑ ψ = 0`, and `Φ` the Fourier transform on
`D⁺(𝔸¹_k, Λ)`. Let `α : A ⟶ G` be a monomorphism of sheaves on `𝔸¹_k`, `G` with finite geometric
stalks and `H⁰(Φ(G[0])) = 0` (so also `H⁰(Φ(A[0])) = 0`, `H⁰ ∘ Φ` being left exact). If `n ∈ ℕ`
kills `H¹(Φ(α))`, and

* `Hom(H²(Φ(A[0]))[-2], H¹(Φ(G[0]))[-1]) = 0`, `Hom(H²(Φ(A[0])), H²(Φ(G[0]))) = 0` — for instance
  `H²(Φ(A[0]))` punctual and `H¹(Φ(G[0]))`, `H²(Φ(G[0]))` locally constant (step (L3)),

then `n` kills `A`: `n • Φ(α)` is a morphism between objects with cohomology in degrees `1, 2`
which vanishes on `H¹`, hence is zero
(`Stacks.DerivedCategoryPlus.eq_zero_of_homology_one_map_eq_zero`), and Fourier inversion (E1)
detects it.

This is the mechanism (b) (`ℓᵉ K(S) = 0 ⇒ ℓᵉ S = 0`) of the single-level argument for the
irreducibility of the Fourier transform in Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.mono_homology_zero_fourierTransform_map_of_mono`.
* `Stacks.EtaleCohomology.nsmul_id_eq_zero_of_nsmul_homology_one_fourierTransform_map_eq_zero`.
* `Stacks.EtaleCohomology.nsmul_id_eq_zero_of_isPunctual_of_isLocallyConstantWith`.

## Implementation notes

The Fourier transform lives in the standard model `HasDerivedCategory.standard`, and so do the
statements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
  Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
  (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj (cover k (Polynomial k) Polynomial.X))

local notation "𝔸f" => affineLineStructureMap k

/-- **`H⁰ ∘ Φ` is left exact**: it carries a monomorphism of sheaves to a monomorphism, the
preceding term of the long exact sequence being `H⁻¹(Φ(-)) = 0`. -/
theorem mono_homology_zero_fourierTransform_map_of_mono (j : CompactificationOf (Over.mk 𝔸f))
    {A G : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))} (α : A ⟶ G) [Mono α] :
    Mono ((DerivedCategory.Plus.homologyFunctor _ 0).map
      ((fourierTransform k Λ ψ B p₀ j).map ((DerivedCategory.Plus.singleFunctor _ 0).map α))) := by
  let := fourierTransformCommShift k Λ ψ B p₀ j
  have := isTriangulated_fourierTransform k Λ ψ B p₀ j
  let S := ShortComplex.mk α (cokernel.π α) (cokernel.condition α)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (S.exact_of_g_is_cokernel (cokernelIsCokernel α)) inferInstance inferInstance
  have hT := (fourierTransform k Λ ψ B p₀ j).map_distinguished _
    (Stacks.DerivedIndexing.singleTrianglePlus_distinguished hS)
  exact ((DerivedCategory.Plus.homologyFunctor _ 0).homologySequence_mono_shift_map_mor₁_iff _ hT
    (-1) 0 (by omega)).2
    ((isZero_homology_fourierTransform_of_neg k Λ ψ B p₀ j (cokernel α) (-1) (by omega)).eq_of_src
      _ _)

/-- **Mechanism (b)**: for a monomorphism `α : A ⟶ G`, `G` with finite geometric stalks and
`H⁰(Φ(G[0])) = 0`, if `n • H¹(Φ(α)) = 0`, `Hom(H²(Φ(A[0]))[-2], H¹(Φ(G[0]))[-1]) = 0` and
`Hom(H²(Φ(A[0])), H²(Φ(G[0]))) = 0`, then `n • 𝟙 A = 0`. -/
theorem nsmul_id_eq_zero_of_nsmul_homology_one_fourierTransform_map_eq_zero
    (hψ : ∑ a : k, ψ a = 0) (hq : IsUnit (Fintype.card k : Λ))
    (j : CompactificationOf (Over.mk 𝔸f))
    (jQ : CompactificationOf (Over.mk (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f)))
    {A G : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))} (α : A ⟶ G) [Mono α] (n : ℕ)
    (hGf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))),
      Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
        ((etaleModuleInverseImage.{u, 0} Λ w).obj G)))
    (hG0 : IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G))))
    (hu : n • (DerivedCategory.Plus.homologyFunctor _ 1).map
      ((fourierTransform k Λ ψ B p₀ j).map ((DerivedCategory.Plus.singleFunctor _ 0).map α)) = 0)
    (h₁ : ∀ g : (DerivedCategory.Plus.singleFunctor _ 2).obj
        ((DerivedCategory.Plus.homologyFunctor _ 2).obj
          ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj A))) ⟶
      (DerivedCategory.Plus.singleFunctor _ 1).obj ((DerivedCategory.Plus.homologyFunctor _ 1).obj
        ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G))),
      g = 0)
    (h₂ : ∀ g : (DerivedCategory.Plus.homologyFunctor _ 2).obj
        ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj A)) ⟶
      (DerivedCategory.Plus.homologyFunctor _ 2).obj
        ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G)),
      g = 0) :
    n • 𝟙 A = 0 := by
  let Φ := fourierTransform k Λ ψ B p₀ j
  let := fourierTransformCommShift k Λ ψ B p₀ j
  have := isTriangulated_fourierTransform k Λ ψ B p₀ j
  have : Φ.Additive := inferInstance
  let S := DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) 0
  have hA0 : IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj (Φ.obj (S.obj A))) := by
    have := mono_homology_zero_fourierTransform_map_of_mono k Λ ψ B p₀ j α
    exact hG0.of_mono ((DerivedCategory.Plus.homologyFunctor _ 0).map (Φ.map (S.map α)))
  have hGE : ∀ (X : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))),
      IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj (Φ.obj (S.obj X))) →
        (Φ.obj (S.obj X)).IsGE 1 := fun X hX =>
    (DerivedCategory.Plus.isGE_iff _ 1).2 fun i hi => by
      obtain h | rfl := (show i ≤ 0 by omega).lt_or_eq
      · exact isZero_homology_fourierTransform_of_neg k Λ ψ B p₀ j X i h
      · exact hX
  have hLE : ∀ (X : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))),
      (Φ.obj (S.obj X)).IsLE 2 := fun X =>
    (DerivedCategory.Plus.isLE_iff _ 2).2 fun i hi =>
      isZero_homology_fourierTransform_of_two_lt k Λ ψ B p₀ j X i (by omega)
  have := hGE A hA0
  have := hGE G hG0
  have := hLE A
  have := hLE G
  refine eq_zero_of_fourierTransform_map_comp_mono_eq_zero k Λ ψ B p₀ hψ hq j jQ α (n • 𝟙 A) hGf ?_
  rw [Preadditive.nsmul_comp, Category.id_comp, Functor.map_nsmul, Functor.map_nsmul]
  exact Stacks.DerivedCategoryPlus.eq_zero_of_homology_one_map_eq_zero _
    (by rwa [Functor.map_nsmul]) h₁ h₂

/-- **Mechanism (b), punctual form**: for a monomorphism `α : A ⟶ G`, `G` with finite geometric
stalks and `H⁰(Φ(G[0])) = 0`, `H²(Φ(A[0]))` punctual and `H¹(Φ(G[0]))`, `H²(Φ(G[0]))` locally
constant, `n • H¹(Φ(α)) = 0` implies `n • 𝟙 A = 0`. -/
theorem nsmul_id_eq_zero_of_isPunctual_of_isLocallyConstantWith
    (hψ : ∑ a : k, ψ a = 0) (hq : IsUnit (Fintype.card k : Λ))
    (j : CompactificationOf (Over.mk 𝔸f))
    (jQ : CompactificationOf (Over.mk (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f)))
    {A G : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))} (α : A ⟶ G) [Mono α] (n : ℕ)
    (hGf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))),
      Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
        ((etaleModuleInverseImage.{u, 0} Λ w).obj G)))
    (hG0 : IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G))))
    (hu : n • (DerivedCategory.Plus.homologyFunctor _ 1).map
      ((fourierTransform k Λ ψ B p₀ j).map ((DerivedCategory.Plus.singleFunctor _ 0).map α)) = 0)
    (hP : IsPunctualEtaleModule Λ ((DerivedCategory.Plus.homologyFunctor _ 2).obj
      ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj A))))
    (Q₁ Q₂ : ModuleCat.{u + 1} Λ → Prop)
    (hL₁ : Stacks.ConstantSheaf.IsLocallyConstantWith Λ
      (Spec (.of (Polynomial k))).smallEtaleTopology Q₁
      ((DerivedCategory.Plus.homologyFunctor _ 1).obj
        ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G))))
    (hL₂ : Stacks.ConstantSheaf.IsLocallyConstantWith Λ
      (Spec (.of (Polynomial k))).smallEtaleTopology Q₂
      ((DerivedCategory.Plus.homologyFunctor _ 2).obj
        ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))) :
    n • 𝟙 A = 0 := by
  have : IsIntegral (Spec (.of (Polynomial k))) := inferInstance
  have : IsNormal (Spec (.of (Polynomial k))) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed (Polynomial k))
  exact nsmul_id_eq_zero_of_nsmul_homology_one_fourierTransform_map_eq_zero k Λ ψ B p₀ hψ hq j jQ
    α n hGf hG0 hu
    (singleFunctor_hom_eq_zero_of_isPunctual_of_isLocallyConstantWith Λ hP Q₁ hL₁ 2 1 (by omega))
    (IsPunctualEtaleModule.eq_zero_of_isLocallyConstantWith hP Q₂ hL₂)

end Stacks.EtaleCohomology

end
