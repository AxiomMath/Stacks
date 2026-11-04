module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Dimension
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.AffineSpaceSmooth

/-!
# A proper smooth curve has no clopen subset inside an affine open

Let `Y` be proper and smooth of relative dimension one over a field `K` and let `o : V ⟶ Y` be an
open immersion from an affine scheme. Then no nonempty clopen subset of `Y` lies in the image of
`o`. Such a subset `Z` would be an open subscheme of `Y`, hence of dimension one, and also a
closed subscheme of the affine `V`, hence affine; being proper and affine over `K` it would be
integral over `K`, hence of dimension zero.

Equivalently, every connected component of `Y` meets the complement of `V`.

## Main results

* `AlgebraicGeometry.eq_empty_of_isClopen_of_subset_range_of_isAffine`: no nonempty clopen subset
  of `Y` lies in the image of an open immersion from an affine scheme.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **No nonempty clopen subset of a proper smooth curve lies in an affine open.** -/
theorem eq_empty_of_isClopen_of_subset_range_of_isAffine {K : Type u} [Field K] {Y V : Scheme.{u}}
    (g : Y ⟶ Spec (.of K)) [IsProper g] [SmoothOfRelativeDimension 1 g] (o : V ⟶ Y)
    [IsOpenImmersion o] [IsAffine V] (Z : Set Y) (hZ : IsClopen Z)
    (hZV : Z ⊆ Set.range o) : Z = ∅ := by
  by_contra hne
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.2 hne
  let W : Y.Opens := ⟨Z, hZ.isOpen⟩
  have : Nonempty W := ⟨⟨z, hz⟩⟩
  have : SmoothOfRelativeDimension 1 (W.ι ≫ g) := SmoothOfRelativeDimension.etale_comp 1 W.ι g
  have h1 : topologicalKrullDim W = ((1 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 (W.ι ≫ g)
  have : IsClosedImmersion W.ι := IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]; exact hZ.isClosed)
  have hWV : Set.range W.ι ⊆ Set.range o := by rwa [Scheme.Opens.range_ι]
  let l : (W : Scheme.{u}) ⟶ V := IsOpenImmersion.lift o W.ι hWV
  have hl : l ≫ o = W.ι := IsOpenImmersion.lift_fac o W.ι hWV
  have : IsOpenImmersion (l ≫ o) := by rw [hl]; infer_instance
  have : IsOpenImmersion l := IsOpenImmersion.of_comp l o
  have hrange : Set.range l = o ⁻¹' Z := by
    ext v
    constructor
    · rintro ⟨w, rfl⟩
      show o (l w) ∈ Z
      rw [← Scheme.Hom.comp_apply, hl]
      exact w.2
    · intro hv
      obtain ⟨w, hw⟩ : o v ∈ Set.range W.ι := by rwa [Scheme.Opens.range_ι]
      refine ⟨w, o.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, hl, hw]
  have : IsClosedImmersion l := IsClosedImmersion.of_isPreimmersion _ (by
    rw [hrange]; exact hZ.isClosed.preimage o.continuous)
  have : IsAffine (W : Scheme.{u}) := isAffine_of_isAffineHom l
  have : IsIntegralHom (W.ι ≫ g) := by
    rw [IsIntegralHom.iff_universallyClosed_and_isAffineHom]
    exact ⟨inferInstance, inferInstance⟩
  have h0 := topologicalKrullDim_le_of_isIntegralHom (W.ι ≫ g)
  have hK : topologicalKrullDim (Spec (.of K)) = 0 := by
    show topologicalKrullDim (PrimeSpectrum K) = 0
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]
  rw [h1, hK] at h0
  exact absurd h0 (by decide)

end AlgebraicGeometry

end
