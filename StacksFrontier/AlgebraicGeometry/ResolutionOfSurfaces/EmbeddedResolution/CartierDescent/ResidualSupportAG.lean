module

public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceBlowup
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.BlowupTransport
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.ResidualSupport
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The residual ideal sheaf on `AlgebraicGeometry.blowUp`, with regular local rings

Let `A` be a two-dimensional regular local ring and let `L` be an ideal with `𝔪 ^ n ≤ L ≤ 𝔪`. On
the blowup `AlgebraicGeometry.blowUp (centre A)` of `Spec A` at its closed point, the inverse image
of `L` factors as a positive power of the exceptional divisor times an ideal sheaf supported at
finitely many closed points whose local rings are regular of Krull dimension two. This is the
support half of [Stacks, Tag 0AGT]; regularity of the local rings is [Stacks, Tag 0AGR].

## Main results

* `Stacks.ResolutionOfSurfaces.CartierDescent.isRegularLocalRing_stalk_blowUp_centre`: every
  local ring of the blowup of a regular local surface at its closed point is regular.
* `Stacks.ResolutionOfSurfaces.CartierDescent.exists_residual_support`: the support half of
  [Stacks, Tag 0AGT] on `AlgebraicGeometry.blowUp`.

## References

* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
* [Stacks Project, Tag 0AGR](https://stacks.math.columbia.edu/tag/0AGR)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.ResolutionOfSurfaces.CartierDescent

/-- Every local ring of the blowup of a two-dimensional regular local ring at its closed point is
regular. -/
@[ega "IV 19.4.11" "(iii), special case", ega "IV 19.4.4" "special case"]
public theorem isRegularLocalRing_stalk_blowUp_centre (A : Type u) [CommRing A]
    [IsRegularLocalRing A] (hdim : ringKrullDim A = 2)
    (z : AlgebraicGeometry.blowUp (centre A)) :
    IsRegularLocalRing ((AlgebraicGeometry.blowUp (centre A)).presheaf.stalk z) := by
  have hreg : AlgebraicGeometry.IsRegular (AlgebraicGeometry.blowUp (centre A)) :=
    AlgebraicGeometry.isRegular_blowUp_maximalIdeal A hdim
  have hpair : IsLocallyNoetherian (AlgebraicGeometry.blowUp (centre A)) ∧
      ∀ w : AlgebraicGeometry.blowUp (centre A),
        IsRegularLocalRing ((AlgebraicGeometry.blowUp (centre A)).presheaf.stalk w) :=
    ((AlgebraicGeometry.isRegular_tfae (AlgebraicGeometry.blowUp (centre A))).out 1 2
      (by simp) (by simp)).mp hreg
  exact hpair.2 z

/-- The support half of [Stacks, Tag 0AGT] on `AlgebraicGeometry.blowUp`. Let `A` be a regular
local ring of dimension two with `𝔪 = (x, y)`, and let `L` be an ideal with `𝔪 ^ n ≤ L ≤ 𝔪`.
Suppose that the colength bound `hcol` holds for every factorisation on `Stacks.Blowup.blowUp`.
On the blowup of `Spec A` at its closed point the inverse image of `L` is a
positive power `d` of the exceptional divisor times an ideal sheaf `J'` whose support is contained
in a finite set of closed points, at each of which the local ring is regular of dimension two. -/
public theorem exists_residual_support (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (hdim : ringKrullDim A = 2) {x y : A}
    (hspan : Ideal.span ({x, y} : Set A) = IsLocalRing.maximalIdeal A)
    (L : Ideal A) (n : ℕ) (hmn : IsLocalRing.maximalIdeal A ^ n ≤ L)
    (hLm : L ≤ IsLocalRing.maximalIdeal A)
    (hcol : ∀ (d : ℕ), 0 < d →
      ∀ J'₀ : (Stacks.Blowup.blowUp (centre A)).IdealSheafData,
      Stacks.Blowup.exceptionalIdeal (centre A) ^ d * J'₀ =
          (idealSheafOf A L).comap (Stacks.Blowup.blowUpToBase (centre A)) →
      ¬ ((idealSheafOf A L).comap (Stacks.Blowup.blowUpToBase (centre A)) ≤
          Stacks.Blowup.exceptionalIdeal (centre A) ^ (d + 1)) →
      ∀ T₀ : Finset (Stacks.Blowup.blowUp (centre A)),
      ((J'₀.support : Set (Stacks.Blowup.blowUp (centre A))) ⊆ (T₀ : Set _)) →
      ∑ w ∈ T₀, Module.length ((Stacks.Blowup.blowUp (centre A)).presheaf.stalk w)
          ((Stacks.Blowup.blowUp (centre A)).presheaf.stalk w ⧸
            AlgebraicGeometry.IdealSheafData.stalk J'₀ w) <
        Module.length A (A ⧸ L)) :
    ∃ (d : ℕ) (T : Finset (AlgebraicGeometry.blowUp (centre A)))
      (J' : (AlgebraicGeometry.blowUp (centre A)).IdealSheafData),
      0 < d ∧
      AlgebraicGeometry.exceptionalIdeal (centre A) ^ d * J' =
        (idealSheafOf A L).comap (AlgebraicGeometry.blowUpToBase (centre A)) ∧
      ((J'.support : Set (AlgebraicGeometry.blowUp (centre A))) ⊆ (T : Set _)) ∧
      (∀ z ∈ T, IsClosed ({z} : Set (AlgebraicGeometry.blowUp (centre A)))) ∧
      (∀ z ∈ T, IsRegularLocalRing
        ((AlgebraicGeometry.blowUp (centre A)).presheaf.stalk z)) ∧
      (∀ z ∈ T, ringKrullDim ((AlgebraicGeometry.blowUp (centre A)).presheaf.stalk z) = 2) ∧
      ∑ z ∈ T, Module.length ((AlgebraicGeometry.blowUp (centre A)).presheaf.stalk z)
          ((AlgebraicGeometry.blowUp (centre A)).presheaf.stalk z ⧸
            AlgebraicGeometry.IdealSheafData.stalk J' z) <
        Module.length A (A ⧸ L) := by
  classical
  obtain ⟨d, T₀, J'₀, hdpos, hfac, hmax, hsupp, hclosed, hdim2⟩ :=
    exists_residual_isEffectiveCartier_support A hdim hspan L n hmn hLm
  set e := Stacks.Blowup.blowUpIso (centre A) with he
  set J' : (AlgebraicGeometry.blowUp (centre A)).IdealSheafData := J'₀.comap e.inv with hJ'def
  have hJ'eq : J'.comap e.hom = J'₀ := by
    rw [hJ'def, ← Scheme.IdealSheafData.comap_comp, e.hom_inv_id,
      Scheme.IdealSheafData.comap_id]
  have hbij : Function.Bijective e.hom.base := by
    simpa only [Scheme.coe_homeoOfIso] using (Scheme.homeoOfIso e).bijective
  refine ⟨d, T₀.image e.hom.base, J', hdpos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine eq_of_comap_blowUpIso_hom_eq (centre A) ?_
    rw [comap_blowUpIso_hom_mul, comap_blowUpIso_hom_exceptionalIdeal_pow, hJ'eq,
      comap_blowUpIso_hom_comap_blowUpToBase]
    exact hfac
  · intro z hz
    obtain ⟨w, rfl⟩ := hbij.2 z
    have hw : w ∈ (J'₀.support : Set (Stacks.Blowup.blowUp (centre A))) := by
      rwa [← hJ'eq, support_comap_blowUpIso_hom]
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨w, hsupp hw, rfl⟩)
  · intro z hz
    obtain ⟨w, hwT, rfl⟩ := Finset.mem_image.1 hz
    have := (Scheme.homeoOfIso e).isClosedMap _ (hclosed w hwT)
    simpa only [Set.image_singleton, Scheme.coe_homeoOfIso] using this
  · exact fun z _ => isRegularLocalRing_stalk_blowUp_centre A hdim z
  · intro z hz
    obtain ⟨w, hwT, rfl⟩ := Finset.mem_image.1 hz
    exact (ringKrullDim_stalk_eq (centre A) w).symm.trans (hdim2 w hwT)
  · rw [Finset.sum_image fun w _ w' _ h => hbij.1 h]
    refine lt_of_eq_of_lt (Finset.sum_congr rfl fun w _ => ?_)
      (hcol d hdpos J'₀ hfac hmax T₀ hsupp)
    exact (length_stalk_quotient_comap_blowUpIso_hom (centre A) J' w).symm.trans
      (by rw [hJ'eq])

end Stacks.ResolutionOfSurfaces.CartierDescent

end
