module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierNoPunctualSubsheaf
public import StacksFrontier.Algebra.Homology.DerivedCategory.PlusTwoDegreeTriangle

/-!
# The Fourier transform of a punctual sheaf is a sheaf without punctual subsheaves

Let `k` be a finite field, `Λ` a finite commutative ring in which `q = #k` is invertible, `ψ` an
additive character of `k` with values in `Λ` and `∑ ψ = 0`, and `Φ` the Fourier transform on
`D⁺(𝔸¹_k, Λ)`. For a punctual sheaf `C` on `𝔸¹_k`, `Φ(C[0])` has cohomology in degree `0` only
(`Stacks.EtaleCohomology.isZero_homology_fourierTransform_of_isZero_inverseImage`), so it is
`D[0]` for `D = H⁰(Φ(C[0]))`. If `C` has finite geometric stalks, `Φ(D[0]) ≅ Φ(Φ(C[0]))` lives in
degree `2` (Fourier inversion), so `H⁰(Φ(D[0])) = 0`, and `D` has no punctual subsheaf as soon as
it has finite geometric stalks
(`Stacks.EtaleCohomology.isZero_of_mono_of_isZero_homology_zero_fourierTransform`).

This is used in the step (b) of the single-level argument for the irreducibility of the Fourier
transform in Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), for
`C = H²(Φ(F[0]))`: the cokernel of `H¹(Φ G) ↪ F'` embeds in `D` and so receives no nonzero map
from a punctual sheaf.

## Main results

* `Stacks.EtaleCohomology.nonempty_fourierTransform_singleFunctor_iso_of_isPunctual`.
* `Stacks.EtaleCohomology.isZero_homology_zero_fourierTransform_homology_zero_of_isPunctual`.
* `Stacks.EtaleCohomology.isZero_of_mono_homology_zero_fourierTransform_of_isPunctual`.

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

/-- **`Φ(C[0]) ≅ H⁰(Φ(C[0]))[0]` for a punctual sheaf `C`**: its cohomology lives in degree `0`. -/
theorem nonempty_fourierTransform_singleFunctor_iso_of_isPunctual
    (j : CompactificationOf (Over.mk 𝔸f)) {C : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))}
    (hC : IsPunctualEtaleModule Λ C) :
    Nonempty ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj C) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj ((DerivedCategory.Plus.homologyFunctor _ 0).obj
        ((fourierTransform k Λ ψ B p₀ j).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj C)))) := by
  obtain ⟨U, jU, h₁, h₂, h₃⟩ := hC
  have := h₁
  have := h₂
  let Y := (fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj C)
  have : Y.IsGE 0 := (DerivedCategory.Plus.isGE_iff _ 0).2 fun i hi =>
    isZero_homology_fourierTransform_of_neg k Λ ψ B p₀ j C i hi
  have : Y.IsLE 0 := (DerivedCategory.Plus.isLE_iff _ 0).2 fun i hi =>
    isZero_homology_fourierTransform_of_isZero_inverseImage k Λ ψ B p₀ j C jU h₃ i (by omega)
  obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.Plus.exists_iso_singleFunctor_obj_of_isGE_of_isLE Y 0
  exact ⟨e ≪≫ (DerivedCategory.Plus.singleFunctor _ 0).mapIso
    ((Stacks.DerivedCategoryPlus.homologySingleFunctorIso 0 M).symm ≪≫
      (DerivedCategory.Plus.homologyFunctor _ 0).mapIso e.symm)⟩

/-- **`H⁰(Φ(D[0])) = 0` for `D = H⁰(Φ(C[0]))`**, `C` punctual with finite geometric stalks:
`Φ(D[0]) ≅ Φ(Φ(C[0]))` lives in degree `2`. -/
theorem isZero_homology_zero_fourierTransform_homology_zero_of_isPunctual (hψ : ∑ a : k, ψ a = 0)
    (hq : IsUnit (Fintype.card k : Λ)) (j : CompactificationOf (Over.mk 𝔸f))
    (jQ : CompactificationOf (Over.mk (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f)))
    {C : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))} (hC : IsPunctualEtaleModule Λ C)
    (hCf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))),
      Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
        ((etaleModuleInverseImage.{u, 0} Λ w).obj C))) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((DerivedCategory.Plus.homologyFunctor _ 0).obj
          ((fourierTransform k Λ ψ B p₀ j).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj C)))))) := by
  obtain ⟨e⟩ := nonempty_fourierTransform_singleFunctor_iso_of_isPunctual k Λ ψ B p₀ j hC
  have h := isZero_homology_fourierTransform_comp k Λ ψ B p₀ hψ hq j jQ C hCf 0 (by decide)
  rw [Functor.comp_obj] at h
  exact h.of_iso ((DerivedCategory.Plus.homologyFunctor _ 0).mapIso
    ((fourierTransform k Λ ψ B p₀ j).mapIso e.symm))

/-- **`H⁰(Φ(C[0]))` has no nonzero punctual subsheaf**, for `C` punctual with finite geometric
stalks and `H⁰(Φ(C[0]))` with finite geometric stalks. -/
theorem isZero_of_mono_homology_zero_fourierTransform_of_isPunctual (hψ : ∑ a : k, ψ a = 0)
    (hq : IsUnit (Fintype.card k : Λ)) (j : CompactificationOf (Over.mk 𝔸f))
    (jQ : CompactificationOf (Over.mk (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f)))
    {C : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))} (hC : IsPunctualEtaleModule Λ C)
    (hCf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))),
      Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
        ((etaleModuleInverseImage.{u, 0} Λ w).obj C)))
    (hDf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))),
      Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
        ((etaleModuleInverseImage.{u, 0} Λ w).obj ((DerivedCategory.Plus.homologyFunctor _ 0).obj
          ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj C))))))
    {P : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))}
    (ι : P ⟶ (DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj C)))
    [Mono ι] (hP : IsPunctualEtaleModule Λ P) : IsZero P :=
  isZero_of_mono_of_isZero_homology_zero_fourierTransform k Λ ψ B p₀ hψ hq j jQ ι hP hDf
    (isZero_homology_zero_fourierTransform_homology_zero_of_isPunctual k Λ ψ B p₀ hψ hq j jQ hC hCf)

end Stacks.EtaleCohomology

end
