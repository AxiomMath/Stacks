module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.AffineLineFourierKernel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierLevelSheafTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierKernelUnit

/-!
# The Fourier kernel is invertible

The Artin–Schreier sheaf `L = L_ψ(X)` on `𝔸¹_k` has the inverse `L_ψ(-X)`:
`L_ψ(X) ⊗ L_ψ(-X) ≅ L_ψ(X - X)` (`Stacks.ArtinSchreier.artinSchreierLevelSheafTensorIso`), and
`L_ψ(0)` is the constant sheaf `Λ`, the unit of the tensor product, `0` being `0^q - 0`
(`Stacks.ArtinSchreier.nonempty_artinSchreierLevelSheaf_iso_constantSheaf_of_sub_eq`). Inverse
image being monoidal, the Fourier kernel `μ⁻¹ L` on `𝔸¹ ×_k 𝔸¹` and all its inverse images are
invertible, with étale-locally free inverses.

This is what lets the twist by the Fourier kernel be undone in the vanishing of `H⁰` of the Fourier
transform of a sheaf without punctual sections, in Laumon's argument for
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.nonempty_inverseImage_tensor_iso_tensorUnit`.
* `Stacks.EtaleCohomology.exists_affineLineArtinSchreierSheaf_inverse`.
* `Stacks.EtaleCohomology.exists_fourierKernel_inverse`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  etaleModuleInverseImageSheafPullbackMonoidal hasSheafify_etaleModules_fourierKernel

variable (Λ : Type) [CommRing Λ]

/-- **Inverse image preserves inverse pairs**: `A ⊗ B ≅ 𝟙` gives `f⁻¹ A ⊗ f⁻¹ B ≅ 𝟙`. -/
theorem nonempty_inverseImage_tensor_iso_tensorUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : EtaleModules.{u, 0} Λ Y} (e : A ⊗ B ≅ 𝟙_ (EtaleModules.{u, 0} Λ Y)) :
    Nonempty ((etaleModuleInverseImage.{u, 0} Λ f).obj A ⊗
      (etaleModuleInverseImage.{u, 0} Λ f).obj B ≅ 𝟙_ (EtaleModules.{u, 0} Λ X)) :=
  ⟨Functor.Monoidal.μIso (etaleModuleInverseImage.{u, 0} Λ f) A B ≪≫
    (etaleModuleInverseImage.{u, 0} Λ f).mapIso e ≪≫
    (Functor.Monoidal.εIso (etaleModuleInverseImage.{u, 0} Λ f)).symm⟩

variable (k : Type u) [Field k] [Fintype k] [Finite Λ] (ψ : AddChar k Λ) (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj (cover k (Polynomial k) Polynomial.X))

/-- **`L_ψ(X)` is invertible**, with an étale-locally free inverse. -/
theorem exists_affineLineArtinSchreierSheaf_inverse :
    ∃ L' : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k))), IsLocallyFreeEtaleModule Λ L' ∧
      Nonempty (affineLineArtinSchreierSheaf k Λ ψ B p₀ ⊗ L' ≅
        𝟙_ (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k))))) ∧
      Nonempty (L' ⊗ affineLineArtinSchreierSheaf k Λ ψ B p₀ ≅
        𝟙_ (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k))))) := by
  let A := Polynomial k
  let hX := schemeSizeBelow_spec_polynomial k B
  let x := affineLineOrigin k
  obtain ⟨p'⟩ := nonempty_finiteEtaleFiber_cover k (-Polynomial.X : A) x
  obtain ⟨p₁₂⟩ := nonempty_finiteEtaleFiber_cover k (Polynomial.X + -Polynomial.X : A) x
  obtain ⟨p₂₁⟩ := nonempty_finiteEtaleFiber_cover k (-Polynomial.X + Polynomial.X : A) x
  let L' := artinSchreierLevelSheaf k A (-Polynomial.X) Λ ψ B hX x p'
  obtain ⟨c₁₂⟩ := nonempty_artinSchreierLevelSheaf_iso_constantSheaf_of_sub_eq k A
    (Polynomial.X + -Polynomial.X) Λ ψ B hX 0 (by simp) x p₁₂
  obtain ⟨c₂₁⟩ := nonempty_artinSchreierLevelSheaf_iso_constantSheaf_of_sub_eq k A
    (-Polynomial.X + Polynomial.X) Λ ψ B hX 0 (by simp) x p₂₁
  refine ⟨L',
    isLocallyFreeEtaleModule_artinSchreierLevelSheaf k (A := A) (-Polynomial.X) Λ ψ B hX x p',
    ⟨artinSchreierLevelSheafTensorIso k A Polynomial.X (-Polynomial.X) Λ ψ B hX x p₀ p' p₁₂ ≪≫
      c₁₂ ≪≫ (etaleModuleTensorUnitIso Λ _).symm⟩,
    ⟨artinSchreierLevelSheafTensorIso k A (-Polynomial.X) Polynomial.X Λ ψ B hX x p' p₀ p₂₁ ≪≫
      c₂₁ ≪≫ (etaleModuleTensorUnitIso Λ _).symm⟩⟩

/-- **The Fourier kernel `μ⁻¹ L_ψ` on `𝔸¹ ×_k 𝔸¹` is invertible**, with an étale-locally free
inverse. -/
theorem exists_fourierKernel_inverse :
    ∃ L' : EtaleModules.{u, 0} Λ (pullback (affineLineStructureMap k) (affineLineStructureMap k)),
      IsLocallyFreeEtaleModule Λ L' ∧
      Nonempty ((etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj
          (affineLineArtinSchreierSheaf k Λ ψ B p₀) ⊗ L' ≅ 𝟙_ (EtaleModules.{u, 0} Λ
            (pullback (affineLineStructureMap k) (affineLineStructureMap k)))) ∧
      Nonempty (L' ⊗ (etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj
          (affineLineArtinSchreierSheaf k Λ ψ B p₀) ≅ 𝟙_ (EtaleModules.{u, 0} Λ
            (pullback (affineLineStructureMap k) (affineLineStructureMap k)))) := by
  obtain ⟨L', hL', ⟨e₁⟩, ⟨e₂⟩⟩ := exists_affineLineArtinSchreierSheaf_inverse Λ k ψ B p₀
  exact ⟨(etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj L',
    isLocallyFreeEtaleModule_inverseImage Λ _ hL',
    nonempty_inverseImage_tensor_iso_tensorUnit Λ _ e₁,
    nonempty_inverseImage_tensor_iso_tensorUnit Λ _ e₂⟩

end Stacks.EtaleCohomology

end
