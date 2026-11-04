module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTransformFirstCohomologySequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTransformConstructible
public import StacksFrontier.Algebra.Homology.DerivedCategory.PlusTwoDegreeTriangleKernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerre.FiniteTypeLocallyConstant

/-!
# `H¹(Φ G)` and `H²(Φ G)` are the kernel and the cokernel of `F' ⟶ H⁰(Φ C)`

Let `k` be a finite field, `Λ` a finite commutative ring in which `q = #k` is invertible, `ψ` an
additive character of `k` with values in `Λ` and `∑ ψ = 0`, and `Φ` the Fourier transform on
`D⁺(𝔸¹_k, Λ)`. For `F` étale-locally free of finite rank on `𝔸¹_k`, let `G = H¹(Φ(F[0]))`,
`C = H²(Φ(F[0]))` and `F' = H²(Φ(Φ(F[0])))`. Applying `Φ` to the truncation triangle
`G[-1] ⟶ Φ(F[0]) ⟶ C[-2] ⟶` gives the exact sequence

`0 ⟶ H¹(Φ(G[0])) ⟶ F' ⟶ H⁰(Φ(C[0])) ⟶ H²(Φ(G[0])) ⟶ 0`

(`Stacks.DerivedCategoryPlus.exists_kernel_cokernel_iso_homology_map_singleFunctor_of_distTriang`).
Hence, when `F'` and `H⁰(Φ(C[0]))` are locally constant of finite type, so are `H¹(Φ(G[0]))` and
`H²(Φ(G[0]))` (Tag 093S: kernels and cokernels of maps of such sheaves).

This is the local constancy of `H¹ΦG` and `H²ΦG` in step (a) of the single-level argument for
the irreducibility of the Fourier transform in Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.exists_kernel_cokernel_iso_fourierTransform_homology_one`.
* `Stacks.EtaleCohomology.isFiniteTypeLocallyConstant_homology_fourierTransform_homology_one`.

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

/-- **`0 ⟶ H¹(Φ(G[0])) ⟶ F' ⟶ H⁰(Φ(C[0])) ⟶ H²(Φ(G[0])) ⟶ 0` is exact**, for `F` étale-locally
free of finite rank, `G = H¹(Φ(F[0]))`, `C = H²(Φ(F[0]))` and `F' = H²(Φ(Φ(F[0])))`: there is
`u : F' ⟶ H⁰(Φ(C[0]))` with `H¹(Φ(G[0])) ≅ ker u` and `H²(Φ(G[0])) ≅ coker u`. -/
theorem exists_kernel_cokernel_iso_fourierTransform_homology_one (hψ : ∑ a : k, ψ a = 0)
    (hq : IsUnit (Fintype.card k : Λ)) (j : CompactificationOf (Over.mk 𝔸f))
    (jQ : CompactificationOf (Over.mk (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f)))
    (F : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) (hF : IsLocallyFreeEtaleModule Λ F) :
    ∃ u : (DerivedCategory.Plus.homologyFunctor _ 2).obj
        ((fourierTransform k Λ ψ B p₀ j).obj ((fourierTransform k Λ ψ B p₀ j).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) ⟶
        (DerivedCategory.Plus.homologyFunctor _ 0).obj
          ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((DerivedCategory.Plus.homologyFunctor _ 2).obj
              ((fourierTransform k Λ ψ B p₀ j).obj
                ((DerivedCategory.Plus.singleFunctor _ 0).obj F))))),
      Nonempty ((DerivedCategory.Plus.homologyFunctor _ 1).obj
          ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((DerivedCategory.Plus.homologyFunctor _ 1).obj
              ((fourierTransform k Λ ψ B p₀ j).obj
                ((DerivedCategory.Plus.singleFunctor _ 0).obj F))))) ≅ kernel u) ∧
        Nonempty ((DerivedCategory.Plus.homologyFunctor _ 2).obj
          ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((DerivedCategory.Plus.homologyFunctor _ 1).obj
              ((fourierTransform k Λ ψ B p₀ j).obj
                ((DerivedCategory.Plus.singleFunctor _ 0).obj F))))) ≅ cokernel u) := by
  have : IsNoetherianRing Λ := inferInstance
  have hFf := finite_globalSections_inverseImage_of_isConstructible Λ
    (isConstructibleEtaleModule_of_isLocallyFreeEtaleModule Λ hF)
  let Φ := fourierTransform k Λ ψ B p₀ j
  let S := DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) 0
  let Y := Φ.obj (S.obj F)
  have : Y.IsGE 1 := (DerivedCategory.Plus.isGE_iff _ 1).2 fun i hi => by
    obtain h | rfl : i < 0 ∨ i = 0 := by omega
    · exact isZero_homology_fourierTransform_of_neg k Λ ψ B p₀ j F i h
    · exact isZero_homology_zero_fourierTransform_of_isLocallyFreeEtaleModule k Λ ψ B p₀ j F hF
  have : Y.IsLE (1 + 1) := (DerivedCategory.Plus.isLE_iff _ (1 + 1)).2 fun i hi =>
    isZero_homology_fourierTransform_of_two_lt k Λ ψ B p₀ j F i (by omega)
  obtain ⟨M, N, f, g, h, hT, ⟨eM⟩, ⟨eN⟩⟩ :=
    Stacks.DerivedCategoryPlus.exists_distTriang_singleFunctor_of_isGE_of_isLE Y 1
  have hY := isZero_homology_fourierTransform_comp k Λ ψ B p₀ hψ hq j jQ F hFf 3 (by decide)
  rw [Functor.comp_obj] at hY
  have hN := isZero_homology_fourierTransform_of_neg k Λ ψ B p₀ j N (-1) (by decide)
  obtain ⟨u, ⟨eK⟩, ⟨eC⟩⟩ :=
    @Stacks.DerivedCategoryPlus.exists_kernel_cokernel_iso_homology_map_singleFunctor_of_distTriang
      (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) _ _ _ Φ
      (fourierTransformCommShift k Λ ψ B p₀ j) (isTriangulated_fourierTransform k Λ ψ B p₀ j)
      M N Y f g h hT hN hY
  let iG : ∀ n : ℤ, (DerivedCategory.Plus.homologyFunctor _ n).obj
      (Φ.obj (S.obj ((DerivedCategory.Plus.homologyFunctor _ 1).obj Y))) ≅
      (DerivedCategory.Plus.homologyFunctor _ n).obj (Φ.obj (S.obj M)) := fun n =>
    (DerivedCategory.Plus.homologyFunctor _ n).mapIso (Φ.mapIso (S.mapIso eM.symm))
  let iC : (DerivedCategory.Plus.homologyFunctor _ 0).obj (Φ.obj (S.obj N)) ≅
      (DerivedCategory.Plus.homologyFunctor _ 0).obj
        (Φ.obj (S.obj ((DerivedCategory.Plus.homologyFunctor _ (1 + 1)).obj Y))) :=
    (DerivedCategory.Plus.homologyFunctor _ 0).mapIso (Φ.mapIso (S.mapIso eN))
  exact ⟨u ≫ iC.hom, ⟨iG 1 ≪≫ eK ≪≫ (kernelCompMono u iC.hom).symm⟩,
    ⟨iG 2 ≪≫ eC ≪≫ (cokernelCompIsIso u iC.hom).symm⟩⟩

/-- **`H¹(Φ(G[0]))` and `H²(Φ(G[0]))` are locally constant of finite type** when
`F' = H²(Φ(Φ(F[0])))` and `H⁰(Φ(C[0]))` are, for `F` étale-locally free of finite rank,
`G = H¹(Φ(F[0]))` and `C = H²(Φ(F[0]))`: they are the kernel and the cokernel of a map
`F' ⟶ H⁰(Φ(C[0]))` (Tag 093S). -/
theorem isFiniteTypeLocallyConstant_homology_fourierTransform_homology_one
    (hψ : ∑ a : k, ψ a = 0) (hq : IsUnit (Fintype.card k : Λ))
    (j : CompactificationOf (Over.mk 𝔸f))
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
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F))))))) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ
        (Spec (.of (Polynomial k))).smallEtaleTopology
        ((DerivedCategory.Plus.homologyFunctor _ 1).obj
          ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((DerivedCategory.Plus.homologyFunctor _ 1).obj
              ((fourierTransform k Λ ψ B p₀ j).obj
                ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))))) ∧
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ
        (Spec (.of (Polynomial k))).smallEtaleTopology
        ((DerivedCategory.Plus.homologyFunctor _ 2).obj
          ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((DerivedCategory.Plus.homologyFunctor _ 1).obj
              ((fourierTransform k Λ ψ B p₀ j).obj
                ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))))) := by
  have : IsNoetherianRing Λ := inferInstance
  obtain ⟨u, ⟨eK⟩, ⟨eC⟩⟩ :=
    exists_kernel_cokernel_iso_fourierTransform_homology_one k Λ ψ B p₀ hψ hq j jQ F hF
  exact ⟨Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ _ eK.symm
      (Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_kernel.{u, u + 1, 0, 0}
        (Spec (.of (Polynomial k))).smallEtaleTopology Λ u hF' hC),
    Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ _ eC.symm
      (Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_cokernel.{u, u + 1, 0, 0}
        (Spec (.of (Polynomial k))).smallEtaleTopology Λ u hF' hC)⟩

end Stacks.EtaleCohomology

end
