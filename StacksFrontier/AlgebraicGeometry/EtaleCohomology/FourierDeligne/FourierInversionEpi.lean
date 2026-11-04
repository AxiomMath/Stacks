module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierInversionExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.PlusSingleTriangleFactor

/-!
# Killing a quotient through the Fourier transform

Let `k` be a finite field, `Λ` a finite commutative ring in which `#k` is invertible, `ψ` an
additive character of `k` with values in `Λ` and `∑ ψ = 0`, and `Φ` the Fourier transform on
`D⁺(𝔸¹_k, Λ)`. For an epimorphism `β : A ⟶ Q` of sheaves on `𝔸¹_k`, `A` with finite geometric
stalks, and `φ : Q ⟶ Q`, if `Φ((β ≫ φ)[0])` factors through an object `Z` with `H²(Φ(Z)) = 0`,
then `φ = 0`: `H²(Φ(Φ(-[0])))` is faithful on sheaves with finite geometric stalks
(`Stacks.EtaleCohomology.eq_zero_of_homology_two_fourierTransform_comp_map_eq_zero`).

This is the formal lemma (E2) of the single-level argument for the irreducibility of the Fourier
transform in Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), applied
with `φ = ℓᵉ • 𝟙 Q`.

## Main results

* `Stacks.EtaleCohomology.eq_zero_of_fourierTransform_map_epi_comp_factors` (E2).

## Implementation notes

The Fourier transform lives in the standard model `HasDerivedCategory.standard`, and so does the
statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  HasDerivedCategory.standard

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
  (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj (cover k (Polynomial k) Polynomial.X))

local notation "𝔸f" => affineLineStructureMap k

/-- **(E2) If `Φ((β ≫ φ)[0])` factors through `Z` with `H²(Φ(Z)) = 0`, for an epimorphism
`β : A ⟶ Q` and `φ : Q ⟶ Q`, then `φ = 0`**, for `A` with finite geometric stalks; for instance
`ℓᵉ • Φ(β)` factoring through such a `Z` forces `ℓᵉ • 𝟙 Q = 0`. -/
theorem eq_zero_of_fourierTransform_map_epi_comp_factors
    (hψ : ∑ a : k, ψ a = 0) (hq : IsUnit (Fintype.card k : Λ))
    (j : CompactificationOf (Over.mk 𝔸f))
    (jQ : CompactificationOf (Over.mk (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f)))
    {A Q : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))} (β : A ⟶ Q) [Epi β] (φ : Q ⟶ Q)
    (hA : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))),
      Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
        ((etaleModuleInverseImage.{u, 0} Λ w).obj A)))
    {Z : DerivedCategory.Plus (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k))))}
    (a : (fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj A) ⟶ Z)
    (b : Z ⟶ (fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj Q))
    (hab : (fourierTransform k Λ ψ B p₀ j).map ((DerivedCategory.Plus.singleFunctor _ 0).map
      (β ≫ φ)) = a ≫ b)
    (hZ : IsZero ((DerivedCategory.Plus.homologyFunctor _ 2).obj
      ((fourierTransform k Λ ψ B p₀ j).obj Z))) : φ = 0 :=
  @Stacks.DerivedCategoryPlus.eq_zero_of_map_singleFunctor_map_epi_comp_factors
    (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) _ _ _
    (fourierTransform k Λ ψ B p₀ j) (fourierTransform k Λ ψ B p₀ j)
    (fourierTransformCommShift k Λ ψ B p₀ j) (fourierTransformCommShift k Λ ψ B p₀ j)
    (isTriangulated_fourierTransform k Λ ψ B p₀ j) (isTriangulated_fourierTransform k Λ ψ B p₀ j)
    (fun A ↦ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (w : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))),
      Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
        ((etaleModuleInverseImage.{u, 0} Λ w).obj A)))
    (fun ι _ hB ↦ finite_globalSections_inverseImage_of_mono Λ ι hB)
    (fun π _ hA ↦ finite_globalSections_inverseImage_of_epi Λ π hA) 2
    (fun X hX i hi ↦ isZero_homology_fourierTransform_comp k Λ ψ B p₀ hψ hq j jQ X hX i hi)
    (fun X hX hz ↦
      isZero_of_isZero_homology_two_fourierTransform_comp k Λ ψ B p₀ hψ hq j jQ X hX hz)
    _ _ β _ φ hA _ a b hab hZ

end Stacks.EtaleCohomology

end
