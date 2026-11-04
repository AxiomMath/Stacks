module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierNoPunctualSubsheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTransformDegreeZero
public import StacksFrontier.Algebra.Homology.DerivedCategory.PlusTwoDegreeTriangle

/-!
# The Fourier transform of `G = H¹(Φ(F[0]))` has no `H⁰`

Let `k` be a finite field, `Λ` a finite commutative ring in which `q = #k` is invertible, `ψ` an
additive character of `k` with values in `Λ` and `∑ ψ = 0`, and `Φ` the Fourier transform on
`D⁺(𝔸¹_k, Λ)`. For `F` étale-locally free of finite rank on `𝔸¹_k` with finite geometric stalks,
`Φ(F[0])` has cohomology in degrees `1` and `2` only (`H⁰ = 0` and the amplitude `[0, 2]`), so it
is an extension `G[-1] ⟶ Φ(F[0]) ⟶ C[-2]` with `G = H¹(Φ(F[0]))` and `C = H²(Φ(F[0]))`. Applying
`Φ`, and using that `Φ(Φ(F[0]))` lives in degree `2` (Fourier inversion) and `Φ(C[0])` in degrees
`≥ 0`,

`H⁰(Φ(G[0])) = 0`.

Consequently `G` has no punctual subsheaf as soon as it has finite geometric stalks
(`Stacks.EtaleCohomology.isZero_of_mono_of_isZero_homology_zero_fourierTransform`).

This is the step (a) of the single-level argument for the irreducibility of the Fourier
transform in Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.isZero_homology_zero_fourierTransform_homology_one`.
* `Stacks.EtaleCohomology.isZero_of_mono_homology_one_fourierTransform`.

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

/-- **(a) `H⁰(Φ(G[0])) = 0` for `G = H¹(Φ(F[0]))`**, `F` étale-locally free of finite rank with
finite geometric stalks: from the truncation triangle `G[-1] ⟶ Φ(F[0]) ⟶ C[-2]`, the long exact
cohomology sequence of its image under `Φ`, Fourier inversion (`H¹(ΦΦ(F[0])) = 0`) and
`H⁻²(Φ(C[0])) = 0`. -/
theorem isZero_homology_zero_fourierTransform_homology_one (hψ : ∑ a : k, ψ a = 0)
    (hq : IsUnit (Fintype.card k : Λ)) (j : CompactificationOf (Over.mk 𝔸f))
    (jQ : CompactificationOf (Over.mk (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f)))
    (F : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) (hF : IsLocallyFreeEtaleModule Λ F)
    (hFf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))),
      Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
        ((etaleModuleInverseImage.{u, 0} Λ w).obj F))) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((DerivedCategory.Plus.homologyFunctor _ 1).obj
          ((fourierTransform k Λ ψ B p₀ j).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))))) := by
  let Y := (fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
  have : Y.IsGE 1 := (DerivedCategory.Plus.isGE_iff _ 1).2 fun i hi => by
    rcases lt_or_eq_of_le (show i ≤ 0 by omega) with h | rfl
    · exact isZero_homology_fourierTransform_of_neg k Λ ψ B p₀ j F i h
    · exact isZero_homology_zero_fourierTransform_of_isLocallyFreeEtaleModule k Λ ψ B p₀ j F hF
  have : Y.IsLE (1 + 1) := (DerivedCategory.Plus.isLE_iff _ (1 + 1)).2 fun i hi =>
    isZero_homology_fourierTransform_of_two_lt k Λ ψ B p₀ j F i (by omega)
  obtain ⟨M, N, f, g, h, hT, ⟨eM⟩, -⟩ :=
    Stacks.DerivedCategoryPlus.exists_distTriang_singleFunctor_of_isGE_of_isLE Y 1
  have hY := isZero_homology_fourierTransform_comp k Λ ψ B p₀ hψ hq j jQ F hFf 1 (by decide)
  rw [Functor.comp_obj] at hY
  have hN := isZero_homology_fourierTransform_of_neg k Λ ψ B p₀ j N (-2) (by decide)
  have h0 := @Stacks.DerivedCategoryPlus.isZero_homology_zero_map_singleFunctor_of_distTriang
    (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) _ _ _
    (fourierTransform k Λ ψ B p₀ j) (fourierTransformCommShift k Λ ψ B p₀ j)
    (isTriangulated_fourierTransform k Λ ψ B p₀ j) M N Y f g h hT hY hN
  exact h0.of_iso ((DerivedCategory.Plus.homologyFunctor _ 0).mapIso
    ((fourierTransform k Λ ψ B p₀ j).mapIso
      ((DerivedCategory.Plus.singleFunctor _ 0).mapIso eM.symm)))

/-- **(a) `G = H¹(Φ(F[0]))` has no nonzero punctual subsheaf**, for `F` étale-locally free of
finite rank with finite geometric stalks and `G` with finite geometric stalks. -/
theorem isZero_of_mono_homology_one_fourierTransform (hψ : ∑ a : k, ψ a = 0)
    (hq : IsUnit (Fintype.card k : Λ)) (j : CompactificationOf (Over.mk 𝔸f))
    (jQ : CompactificationOf (Over.mk (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f)))
    (F : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) (hF : IsLocallyFreeEtaleModule Λ F)
    (hFf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))),
      Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
        ((etaleModuleInverseImage.{u, 0} Λ w).obj F)))
    (hGf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))),
      Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
        ((etaleModuleInverseImage.{u, 0} Λ w).obj ((DerivedCategory.Plus.homologyFunctor _ 1).obj
          ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F))))))
    {P : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))}
    (ι : P ⟶ (DerivedCategory.Plus.homologyFunctor _ 1).obj
      ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))
    [Mono ι] (hP : IsPunctualEtaleModule Λ P) : IsZero P :=
  isZero_of_mono_of_isZero_homology_zero_fourierTransform k Λ ψ B p₀ hψ hq j jQ ι hP hGf
    (isZero_homology_zero_fourierTransform_homology_one k Λ ψ B p₀ hψ hq j jQ F hF hFf)

end Stacks.EtaleCohomology

end
