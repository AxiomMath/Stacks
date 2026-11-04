module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Contraction.CompletedStalkFormalNeighborhood
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveThickeningSurjective
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties

/-!
# The local ring at the image point of a contracted exceptional curve

In the setting of [Stacks, Tag 0C2L] — a proper morphism `f : X ⟶ Y` onto a Noetherian scheme with
`f_* 𝒪_X = 𝒪_Y`, carrying an exceptional curve of the first kind `E ⊆ X` to a closed point `y`,
with the fibre over `y` contained in `E` — the completion of `𝒪_{Y, y}` is the ring
`A = lim H⁰(Eₙ, 𝒪_{Eₙ})` of [Stacks, Tag 0C2K]
(`AlgebraicGeometry.Scheme.IdealSheafData.exists_ringEquiv_adicCompletion_formalNeighborhoodRing`).
This file draws the consequences used in the proof of [Stacks, Tag 0C2L]: `𝒪_{Y, y}` is regular
when `A` is, by [Stacks, Tag 07NY], it has the dimension of `A`, by [Stacks, Tag 07NV], and the
maximal ideal of `𝒪_{Y, y}` generates the first step `I₁` of the filtration of `A`.

## Main results

* `isRegularLocalRing_stalk_of_steinSetup`: `𝒪_{Y, y}` is regular if `A` is.
* `ringKrullDim_stalk_eq_of_steinSetup`: `dim 𝒪_{Y, y} = dim A`.
* `formalNeighborhoodFiltration_one_eq_map_maximalIdeal_of_steinSetup`: `I₁ = 𝔪_y A`.

## References

* [Stacks Project, Tag 0C2L](https://stacks.math.columbia.edu/tag/0C2L)
* [Stacks Project, Tag 07NY](https://stacks.math.columbia.edu/tag/07NY)
* [Stacks Project, Tag 07NV](https://stacks.math.columbia.edu/tag/07NV)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}} [IsNoetherian X] {D : X.IdealSheafData} {k : Type u} [Field k]

/-- **The local ring at the image point is regular if the formal neighbourhood is**: its
completion is the ring `A` of compatible functions on the thickenings of the curve, and a
Noetherian local ring is regular if its completion is ([Stacks, Tag 07NY]). -/
public theorem isRegularLocalRing_stalk_of_steinSetup
    (e : projectiveLineProj k ≅ D.subscheme) (f : X ⟶ Y) (y : Y)
    (hsetup : D.IsSteinContractionSetup f y)
    (hmaps : ∀ x ∈ (D.support : Set X), f.base x = y)
    (hfib : f.base ⁻¹' {y} ⊆ (D.support : Set X))
    (hA : IsRegularLocalRing D.formalNeighborhoodRing) :
    IsRegularLocalRing (Y.presheaf.stalk y) := by
  have := hsetup.isNoetherian
  obtain ⟨ψ, -⟩ := exists_ringEquiv_adicCompletion_formalNeighborhoodRing e f y hsetup hmaps hfib
  have := hA
  exact isRegularLocalRing_iff_adicCompletion_maximalIdeal.2
    (IsRegularLocalRing.of_ringEquiv ψ.symm)

/-- **The local ring at the image point has the dimension of the formal neighbourhood**: its
completion is the ring `A`, and a Noetherian local ring has the dimension of its completion
([Stacks, Tag 07NV]). -/
public theorem ringKrullDim_stalk_eq_of_steinSetup
    (e : projectiveLineProj k ≅ D.subscheme) (f : X ⟶ Y) (y : Y)
    (hsetup : D.IsSteinContractionSetup f y)
    (hmaps : ∀ x ∈ (D.support : Set X), f.base x = y)
    (hfib : f.base ⁻¹' {y} ⊆ (D.support : Set X)) :
    ringKrullDim (Y.presheaf.stalk y) = ringKrullDim D.formalNeighborhoodRing := by
  have := hsetup.isNoetherian
  obtain ⟨ψ, -⟩ := exists_ringEquiv_adicCompletion_formalNeighborhoodRing e f y hsetup hmaps hfib
  exact ringKrullDim_adicCompletion_maximalIdeal.trans (ringKrullDim_eq_of_ringEquiv ψ)

/-- **The maximal ideal of `𝒪_{Y, y}` generates the first step of the filtration of `A`**:
`I₁ = 𝔪_y A`. The isomorphism `𝒪_{Y, y}^∧ ≅ A` carries the maximal ideal `𝔪_y 𝒪_{Y, y}^∧` of the
completion onto `𝔪_y A`, which is therefore maximal; it lies in `I₁` because germs vanishing at `y`
vanish on the reduced curve, and `I₁` is a proper ideal because `A / I₁` is a field. -/
public theorem formalNeighborhoodFiltration_one_eq_map_maximalIdeal_of_steinSetup
    {e : projectiveLineProj k ≅ D.subscheme} (hE : D.IsExceptionalCurveOfFirstKind k e)
    (f : X ⟶ Y) (y : Y) (hsetup : D.IsSteinContractionSetup f y)
    (hmaps : ∀ x ∈ (D.support : Set X), f.base x = y)
    (hfib : f.base ⁻¹' {y} ⊆ (D.support : Set X)) :
    D.formalNeighborhoodFiltration 1 =
      Ideal.map (D.stalkToFormalNeighborhood f y hmaps)
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) := by
  have := hsetup.isNoetherian
  have := isReduced_subscheme_of_projectiveLineProj_iso k e
  obtain ⟨ψ, hψ⟩ := exists_ringEquiv_adicCompletion_formalNeighborhoodRing e f y hsetup hmaps hfib
  have hcomp : D.stalkToFormalNeighborhood f y hmaps = ψ.toRingHom.comp
      (algebraMap (Y.presheaf.stalk y)
        (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))) :=
    RingHom.ext fun a ↦ (hψ a).symm
  have hJ : (Ideal.map (D.stalkToFormalNeighborhood f y hmaps)
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))).IsMaximal := by
    rw [hcomp, ← Ideal.map_map, ← AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.map_isMaximal_of_equiv ψ
  have hI : (D.formalNeighborhoodFiltration 1).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ hE.isField_quotient_formalNeighborhoodFiltration_one
  refine (hJ.eq_of_le hI.ne_top ?_).symm
  rw [Ideal.map_le_iff_le_comap]
  exact fun a ha ↦ stalkToFormalNeighborhood_mem_filtration_one D f y hmaps ha

end AlgebraicGeometry.Scheme.IdealSheafData

end
