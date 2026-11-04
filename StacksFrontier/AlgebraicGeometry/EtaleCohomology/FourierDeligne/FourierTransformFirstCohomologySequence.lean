module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTransformFirstCohomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.PlusTwoDegreeTriangleSequence

/-!
# `H¹(Φ G)` embeds in `F'` and `H²(Φ G)` is a quotient of `H⁰(Φ C)`

Let `k` be a finite field, `Λ` a finite commutative ring in which `q = #k` is invertible, `ψ` an
additive character of `k` with values in `Λ` and `∑ ψ = 0`, and `Φ` the Fourier transform on
`D⁺(𝔸¹_k, Λ)`. For `F` étale-locally free of finite rank on `𝔸¹_k` with finite geometric stalks,
let `G = H¹(Φ(F[0]))`, `C = H²(Φ(F[0]))` and `F' = H²(Φ(Φ(F[0])))`. Applying `Φ` to the
truncation triangle `G[-1] ⟶ Φ(F[0]) ⟶ C[-2]`, the long exact cohomology sequence, Fourier
inversion (`ΦΦ(F[0])` lives in degree `2`) and the amplitude of `Φ` give

`0 → H¹(Φ(G[0])) → F'` and `H⁰(Φ(C[0])) → H²(Φ(G[0])) → 0`.

This is the rest of the step (a) of the single-level argument for the irreducibility of the
Fourier transform in Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.exists_mono_epi_fourierTransform_homology_one`.

## Implementation notes

The Fourier transform lives in the standard model `HasDerivedCategory.standard`, and so does the
statement.
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

/-- **(a) `0 → H¹(Φ(G[0])) → H²(ΦΦ(F[0]))` and `H⁰(Φ(C[0])) → H²(Φ(G[0])) → 0`**, for `F`
étale-locally free of finite rank with finite geometric stalks, `G = H¹(Φ(F[0]))` and
`C = H²(Φ(F[0]))`. -/
theorem exists_mono_epi_fourierTransform_homology_one (hψ : ∑ a : k, ψ a = 0)
    (hq : IsUnit (Fintype.card k : Λ)) (j : CompactificationOf (Over.mk 𝔸f))
    (jQ : CompactificationOf (Over.mk (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f)))
    (F : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) (hF : IsLocallyFreeEtaleModule Λ F)
    (hFf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))),
      Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
        ((etaleModuleInverseImage.{u, 0} Λ w).obj F))) :
    (∃ m : (DerivedCategory.Plus.homologyFunctor _ 1).obj
        ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((DerivedCategory.Plus.homologyFunctor _ 1).obj
            ((fourierTransform k Λ ψ B p₀ j).obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F))))) ⟶
        (DerivedCategory.Plus.homologyFunctor _ 2).obj
          ((fourierTransform k Λ ψ B p₀ j).obj ((fourierTransform k Λ ψ B p₀ j).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F))), Mono m) ∧
      ∃ p : (DerivedCategory.Plus.homologyFunctor _ 0).obj
          ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((DerivedCategory.Plus.homologyFunctor _ 2).obj
              ((fourierTransform k Λ ψ B p₀ j).obj
                ((DerivedCategory.Plus.singleFunctor _ 0).obj F))))) ⟶
        (DerivedCategory.Plus.homologyFunctor _ 2).obj
          ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((DerivedCategory.Plus.homologyFunctor _ 1).obj
              ((fourierTransform k Λ ψ B p₀ j).obj
                ((DerivedCategory.Plus.singleFunctor _ 0).obj F))))), Epi p := by
  let Φ := fourierTransform k Λ ψ B p₀ j
  let S := DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) 0
  let Y := Φ.obj (S.obj F)
  have : Y.IsGE 1 := (DerivedCategory.Plus.isGE_iff _ 1).2 fun i hi => by
    rcases lt_or_eq_of_le (show i ≤ 0 by omega) with h | rfl
    · exact isZero_homology_fourierTransform_of_neg k Λ ψ B p₀ j F i h
    · exact isZero_homology_zero_fourierTransform_of_isLocallyFreeEtaleModule k Λ ψ B p₀ j F hF
  have : Y.IsLE (1 + 1) := (DerivedCategory.Plus.isLE_iff _ (1 + 1)).2 fun i hi =>
    isZero_homology_fourierTransform_of_two_lt k Λ ψ B p₀ j F i (by omega)
  obtain ⟨M, N, f, g, h, hT, ⟨eM⟩, ⟨eN⟩⟩ :=
    Stacks.DerivedCategoryPlus.exists_distTriang_singleFunctor_of_isGE_of_isLE Y 1
  have hY := isZero_homology_fourierTransform_comp k Λ ψ B p₀ hψ hq j jQ F hFf 3 (by decide)
  rw [Functor.comp_obj] at hY
  have hN := isZero_homology_fourierTransform_of_neg k Λ ψ B p₀ j N (-1) (by decide)
  obtain ⟨⟨m, hm⟩, ⟨p, hp⟩⟩ :=
    @Stacks.DerivedCategoryPlus.exists_mono_epi_homology_map_singleFunctor_of_distTriang
      (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) _ _ _ Φ
      (fourierTransformCommShift k Λ ψ B p₀ j) (isTriangulated_fourierTransform k Λ ψ B p₀ j)
      M N Y f g h hT hN hY
  let iG : ∀ n : ℤ, (DerivedCategory.Plus.homologyFunctor _ n).obj
      (Φ.obj (S.obj ((DerivedCategory.Plus.homologyFunctor _ 1).obj Y))) ≅
      (DerivedCategory.Plus.homologyFunctor _ n).obj (Φ.obj (S.obj M)) := fun n =>
    (DerivedCategory.Plus.homologyFunctor _ n).mapIso (Φ.mapIso (S.mapIso eM.symm))
  let iC : (DerivedCategory.Plus.homologyFunctor _ 0).obj
      (Φ.obj (S.obj ((DerivedCategory.Plus.homologyFunctor _ (1 + 1)).obj Y))) ≅
      (DerivedCategory.Plus.homologyFunctor _ 0).obj (Φ.obj (S.obj N)) :=
    (DerivedCategory.Plus.homologyFunctor _ 0).mapIso (Φ.mapIso (S.mapIso eN.symm))
  exact ⟨⟨(iG 1).hom ≫ m, mono_comp' (IsIso.mono_of_iso (iG 1).hom) hm⟩,
    ⟨iC.hom ≫ p ≫ (iG 2).inv,
      epi_comp' (IsIso.epi_of_iso iC.hom) (epi_comp' hp (IsIso.epi_of_iso (iG 2).inv))⟩⟩

end Stacks.EtaleCohomology

end
