module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierOffAntidiagonalVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ProjectionFormulaProp

/-!
# The composite of two Fourier transforms is supported on the antidiagonal

Let `k` be a finite field, `Λ` a finite commutative ring in which `q = #k` is invertible, `ψ` an
additive character of `k` with values in `Λ` and `∑ ψ = 0`, `L = L_ψ(x)` and
`Φ(K) = R pr₂!(pr₁⁻¹ K ⊗ μ⁻¹ L)` the Fourier transform on `D⁺(𝔸¹_k, Λ)`,
`μ(x, t) = xt`. For a sheaf `F` on `𝔸¹_k` with finite geometric stalks,

`Φ(Φ(F)) ≅ R(q₃|_{Q_Δ})_!((q₁|_{Q_Δ})⁻¹ F)`,

`Q_Δ = {x + u = 0} ⊆ Q = 𝔸¹_x ×_k 𝔸¹_t ×_k 𝔸¹_u`, `q₁ = x`, `q₃ = u`: the integral transform of
the composite has kernel `q₁₂⁻¹ μ⁻¹ L ⊗ q₂₃⁻¹ μ⁻¹ L ≅ s⁻¹ L`, `s = t(x + u)`
(`Stacks.EtaleCohomology.integralTransformCompIso`, Tags 0F7L, 0F7J and the projection formula),
which has no cohomology off `Q_Δ`
(`Stacks.EtaleCohomology.isZero_derivedLowerShriek_fourierOffAntidiagonal`) and is trivial on it,
so the open-closed triangle (Tag 0GKP) collapses
(`Stacks.EtaleCohomology.nonempty_derivedLowerShriek_tensor_iso_closed_of_isZero_open`). `Q_Δ` is a
line bundle over `𝔸¹_u` with fibre coordinate `t`; on it `x = -u`, so the right-hand side is
`[-1]^* F ⊗ RΓ_c(𝔸¹_t, Λ)`: this is Fourier inversion, in the objectwise form used for the
irreducibility of the Fourier transform of an irreducible lisse sheaf.

## Main results

* `Stacks.EtaleCohomology.nonempty_fourierTransform_comp_iso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
  Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  HasDerivedCategory.standard

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
  (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj (cover k (Polynomial k) Polynomial.X))

local notation "𝔸f" => affineLineStructureMap k

/-- The exactness of `- ⊗ μ⁻¹ L_ψ`, for the Fourier kernel. -/
theorem isExactTensorRight_fourierKernel :
    IsExactTensorRight Λ ((etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj
      (affineLineArtinSchreierSheaf k Λ ψ B p₀)) :=
  isExactTensorRight_of_isLocallyFreeEtaleModule (isLocallyFreeEtaleModule_fourierKernel k Λ ψ B p₀)

/-- **The Fourier transform** `Φ(K) = R pr₂!(pr₁⁻¹ K ⊗ μ⁻¹ L_ψ)` on `D⁺(𝔸¹_k, Λ)`, through a
compactification `j` of `𝔸¹_k` over `Spec k`. -/
abbrev fourierTransform (j : CompactificationOf (Over.mk 𝔸f)) :
    DerivedCategory.Plus (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) ⥤
      DerivedCategory.Plus (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) :=
  integralTransform Λ 𝔸f 𝔸f j ((etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj
    (affineLineArtinSchreierSheaf k Λ ψ B p₀)) (isExactTensorRight_fourierKernel k Λ ψ B p₀)

/-- `- ⊗ A ≅ - ⊗ B` on `D⁺` for `A ≅ B`, both with `- ⊗ A`, `- ⊗ B` exact. -/
def etaleModuleDerivedTensorRightIsoOfIso {X : Scheme.{u}} {A B' : EtaleModules.{u, 0} Λ X}
    (e : A ≅ B') (hA : IsExactTensorRight Λ A) (hB : IsExactTensorRight Λ B') :
    etaleModuleDerivedTensorRight Λ A hA ≅ etaleModuleDerivedTensorRight Λ B' hB :=
  haveI := hA.1; haveI := hA.2.1; haveI := hA.2.2
  haveI := hB.1; haveI := hB.2.1; haveI := hB.2.2
  Stacks.DerivedFunctor.mapDerivedCategoryPlusNatIso ((tensoringRight _).mapIso e)

include ψ in
/-- **`Φ(Φ(F)) ≅ R(q₃|_{Q_Δ})_!((q₁|_{Q_Δ})⁻¹ F)`** for a sheaf `F` on `𝔸¹_k` with finite geometric
stalks, `Q_Δ = {x + u = 0}`: the kernel of the composite transform is `s⁻¹ L_ψ`, `s = t(x + u)`,
which has no compactly supported cohomology off `Q_Δ` and is trivial on `Q_Δ`. -/
theorem nonempty_fourierTransform_comp_iso (hψ : ∑ a : k, ψ a = 0)
    (hq : IsUnit (Fintype.card k : Λ)) (j : CompactificationOf (Over.mk 𝔸f))
    (jQ : CompactificationOf (Over.mk (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f)))
    (F : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k))))
    (hF : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))),
      Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
        ((etaleModuleInverseImage.{u, 0} Λ w).obj F))) :
    Nonempty ((fourierTransform k Λ ψ B p₀ j ⋙ fourierTransform k Λ ψ B p₀ j).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≅
      (derivedLowerShriek.{u, 0}
          (fourierAntidiagonalι k ≫ tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f)
          (jQ.restrictClosed (fourierAntidiagonalι k)) Λ).obj
        ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ
          (fourierAntidiagonalι k ≫ tripleProduct₁₂ 𝔸f 𝔸f 𝔸f ≫ pullback.fst 𝔸f 𝔸f)).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  let L := affineLineArtinSchreierSheaf k Λ ψ B p₀
  let 𝓛 := (etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj L
  let K := (DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ
    (Spec (.of (Polynomial k)))) 0).obj F
  let q₁₂ := tripleProduct₁₂ 𝔸f 𝔸f 𝔸f
  let q₂₃ := tripleProduct₂₃ 𝔸f 𝔸f 𝔸f
  let q₃ := tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f
  have h𝓛 := isLocallyFreeEtaleModule_fourierKernel k Λ ψ B p₀
  have h₁' : IsExactTensorRight Λ ((etaleModuleInverseImage.{u, 0} Λ q₁₂).obj 𝓛) :=
    isExactTensorRight_of_isLocallyFreeEtaleModule (isLocallyFreeEtaleModule_inverseImage Λ _ h𝓛)
  have h₂' : IsExactTensorRight Λ ((etaleModuleInverseImage.{u, 0} Λ q₂₃).obj 𝓛) :=
    isExactTensorRight_of_isLocallyFreeEtaleModule (isLocallyFreeEtaleModule_inverseImage Λ _ h𝓛)
  have h𝓜 :
      IsExactTensorRight Λ ((etaleModuleInverseImage.{u, 0} Λ (fourierTripleKernelMap k)).obj L) :=
    isExactTensorRight_of_isLocallyFreeEtaleModule (isLocallyFreeEtaleModule_inverseImage Λ _
      (isLocallyFreeEtaleModule_affineLineArtinSchreierSheaf k Λ ψ B p₀))
  -- compactness of the products
  have : LocallyOfFiniteType 𝔸f := locallyOfFiniteType_specPolynomial k
  have : CompactSpace ↥(tripleProduct 𝔸f 𝔸f 𝔸f) :=
    QuasiCompact.compactSpace_of_compactSpace (fourierTripleCoords k)
  have : QuasiSeparatedSpace ↥(tripleProduct 𝔸f 𝔸f 𝔸f) :=
    quasiSeparatedSpace_of_quasiSeparated (fourierTripleCoords k)
  have : CompactSpace ↥(pullback 𝔸f 𝔸f) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd 𝔸f 𝔸f)
  have : QuasiSeparatedSpace ↥(pullback 𝔸f 𝔸f) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd 𝔸f 𝔸f)
  have : QuasiCompact q₃ := quasiCompact_of_compactSpace q₃
  -- the composite transform and its kernel
  let e₁ := (integralTransformCompIso Λ 𝔸f 𝔸f 𝔸f j j 𝓛 (isExactTensorRight_fourierKernel k Λ ψ B p₀)
    𝓛 (isExactTensorRight_fourierKernel k Λ ψ B p₀) h₁' h₂' jQ
    (derivedLowerShriekProjectionFormula Λ) h𝓛).app K
  let eM := (nonempty_fourierTripleKernel_tensor_iso k Λ ψ B p₀).some
  let e₂ := (derivedLowerShriek.{u, 0} q₃ jQ Λ).mapIso
    ((etaleModuleDerivedTensorRightIsoOfIso Λ eM (h₁'.tensor Λ h₂') h𝓜).app
      ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ
        (tripleProduct₁₂ 𝔸f 𝔸f 𝔸f ≫ pullback.fst 𝔸f 𝔸f)).obj K))
  obtain ⟨e₃⟩ := nonempty_derivedLowerShriek_tensor_iso_closed_of_isZero_open Λ
    (tripleProduct₁₂ 𝔸f 𝔸f 𝔸f ≫ pullback.fst 𝔸f 𝔸f) jQ (fourierOffAntidiagonalι k)
    (fourierAntidiagonalι k) (range_fourierOffAntidiagonalι k) _ h𝓜
    (nonempty_fourierAntidiagonal_kernel_iso_tensorUnit k Λ ψ B p₀).some K
    (isZero_derivedLowerShriek_fourierOffAntidiagonal k Λ ψ B p₀ hψ hq jQ h𝓜 F hF)
  exact ⟨e₁ ≪≫ e₂ ≪≫ e₃⟩

end Stacks.EtaleCohomology

end
