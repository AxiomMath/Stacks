module

public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.GoodSections
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Restricting a smooth closed subscheme to an open

`AlgebraicGeometry.GoodNeighbourhood.SubschemeSmoothAt` is local on the ambient scheme: if the
closed subscheme cut out by `I` is smooth of relative dimension `n` at `φ y'` for an open immersion
`φ : Y' ⟶ Y` (for instance an isomorphism), then the closed subscheme cut out by the inverse image
of `I` is smooth of relative dimension `n` at `y'` over the same base. This is how the conditions
on the fibre through the point are carried from the variety to the fibres of the incidence family
and of its partial intersections.

## Main results

* `AlgebraicGeometry.GoodNeighbourhood.SubschemeSmoothAt.comap_of_isOpenImmersion`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GoodNeighbourhood

/-- **Smoothness of a closed subscheme restricts along an open immersion of the ambient
scheme.** -/
theorem SubschemeSmoothAt.comap_of_isOpenImmersion {Y' Y S : Scheme.{u}} (φ : Y' ⟶ Y)
    [IsOpenImmersion φ] (q : Y ⟶ S) {I : Y.IdealSheafData} {n : ℕ} (y' : Y')
    (h : SubschemeSmoothAt q I n (φ y')) : SubschemeSmoothAt (φ ≫ q) (I.comap φ) n y' := by
  obtain ⟨y, hy, U, hyU, hsm⟩ := h
  let ρ : (I.comap φ).subscheme ⟶ I.subscheme := (I.comapIso φ).hom ≫ pullback.snd _ _
  have hρ : ρ ≫ I.subschemeι = (I.comap φ).subschemeι ≫ φ := by
    simp only [ρ, Category.assoc, ← pullback.condition,
      Scheme.IdealSheafData.comapIso_hom_fst_assoc]
  obtain ⟨y'', hy''⟩ : y' ∈ Set.range (I.comap φ).subschemeι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap]
    change φ y' ∈ (I.support : Set Y)
    rw [← Scheme.IdealSheafData.range_subschemeι, ← hy]
    exact ⟨y, rfl⟩
  have hρy : ρ y'' = y := by
    apply I.subschemeι.isClosedEmbedding.injective
    change (ρ ≫ I.subschemeι) y'' = I.subschemeι y
    rw [hρ, Scheme.Hom.comp_apply, hy'', hy]
  refine ⟨y'', hy'', ρ ⁻¹ᵁ U, show ρ y'' ∈ U from hρy ▸ hyU, ?_⟩
  have heq : (ρ ⁻¹ᵁ U).ι ≫ (I.comap φ).subschemeι ≫ φ ≫ q =
      (ρ ∣_ U) ≫ U.ι ≫ I.subschemeι ≫ q := by
    rw [← reassoc_of% hρ, ← reassoc_of% (morphismRestrict_ι ρ U)]
  rw [heq]
  simpa only [zero_add] using
    (inferInstance : SmoothOfRelativeDimension (0 + n) ((ρ ∣_ U) ≫ U.ι ≫ I.subschemeι ≫ q))

end AlgebraicGeometry.GoodNeighbourhood

end
