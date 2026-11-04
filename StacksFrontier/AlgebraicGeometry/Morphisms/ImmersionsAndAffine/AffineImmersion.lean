module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.OpenCoverCriterion

/-!
# Affineness of an immersion from an affine open and a closed boundary

Let `j : Y ⟶ X` be an immersion of schemes and let `U ⊆ X` be an open subset with complement
`Z = X \ U`. If the inclusion `U ⟶ X` is affine, the restriction `j ∣_ U` is affine, and the
part `j(Y) ∩ Z` of the image of `j` lying outside `U` is closed, then `j` is affine. In
particular the source of such an immersion into an affine scheme is affine.

## Main results

* `AlgebraicGeometry.isAffineHom_of_isAffineHom_restrict_of_isClosed`: affineness of the
  immersion.
* `AlgebraicGeometry.isAffine_of_isAffineHom_restrict_of_isClosed`: affineness of its source
  when the target is affine.

## Implementation notes

Affineness is checked on an affine open covering of `X` by
`AlgebraicGeometry.isAffineHom_iff_forall_exists_isAffineOpen`, splitting the points of `X` into
three cases. Over `U` an affine open contained in `U` works, because affineness of `j ∣_ U` and of
`U ⟶ X` makes the inverse image of such an affine open affine. At a point of the closure of the
image outside `U` an affine open inside the coborder of the image works, since `j` factors as a
closed immersion into the coborder followed by an open immersion. At a remaining point an affine
open missing `j(Y) ∩ Z` works, because the inverse image of such an affine open agrees with the
inverse image of its intersection with `U`.

## References

* [Stacks Project, Tag 0C3A](https://stacks.math.columbia.edu/tag/0C3A)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- If the inclusion of an open `U ⊆ X` and the restriction of `f : Y ⟶ X` over `U` are both
affine, then the inverse image under `f` of an affine open contained in `U` is affine. -/
private lemma isAffineOpen_preimage_of_le {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens)
    [IsAffineHom U.ι] [IsAffineHom (f ∣_ U)] {V : X.Opens} (hV : IsAffineOpen V)
    (hVU : V ≤ U) : IsAffineOpen (f ⁻¹ᵁ V) := by
  have himage : IsAffineOpen ((f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ V))) :=
    ((hV.preimage U.ι).preimage (f ∣_ U)).image_of_isOpenImmersion _
  have himageV : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    simp [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hVU]
  simpa only [image_morphismRestrict_preimage, himageV] using himage

/-- **Stacks Project, Tag 0C3A, affineness of the immersion.** An immersion `j : Y ⟶ X` is
affine as soon as there is an open `U ⊆ X` with affine inclusion over which `j` restricts to an
affine morphism and whose complement meets the image of `j` in a closed set. -/
@[stacks 0C3A "immersion is affine"]
theorem isAffineHom_of_isAffineHom_restrict_of_isClosed {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsImmersion j] (U : X.Opens) [IsAffineHom U.ι] [IsAffineHom (j ∣_ U)]
    (hZ : IsClosed (Set.range (j : Y → X) ∩ (U : Set X)ᶜ)) : IsAffineHom j := by
  rw [isAffineHom_iff_forall_exists_isAffineOpen]
  intro x
  by_cases hxU : x ∈ U
  · obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.isOpen
    exact ⟨V, hxV, hV, isAffineOpen_preimage_of_le j U hV hVU⟩
  by_cases hxrange : x ∈ Set.range (j : Y → X)
  · obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (subset_coborder hxrange) j.coborderRange.isOpen
    have hVW' : (⟨V, hV⟩ : X.affineOpens) ≤ j.coborderRange.ι.opensRange := by
      intro y hy
      rw [Scheme.Opens.opensRange_ι]
      exact hVW hy
    refine ⟨V, hxV, hV, ?_⟩
    rw [← j.liftCoborder_ι, Scheme.Hom.comp_preimage]
    exact (hV.preimage_of_isOpenImmersion j.coborderRange.ι hVW').preimage j.liftCoborder
  · have hxT : x ∉ Set.range (j : Y → X) ∩ (U : Set X)ᶜ := fun hx => hxrange hx.1
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVT⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxT hZ.isOpen_compl
    have hW : IsAffineOpen (V ⊓ U) := by
      simpa [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]
        using (hV.preimage U.ι).image_of_isOpenImmersion U.ι
    have hEq : j ⁻¹ᵁ V = j ⁻¹ᵁ (V ⊓ U) := by
      refine le_antisymm (fun y hy => ⟨hy, ?_⟩) (fun _ hy => hy.1)
      by_contra hyU
      exact hVT hy ⟨⟨y, rfl⟩, hyU⟩
    exact ⟨V, hxV, hV, hEq ▸ isAffineOpen_preimage_of_le j U hW inf_le_right⟩

/-- **Stacks Project, Tag 0C3A, affineness of the source.** In the situation of
`AlgebraicGeometry.isAffineHom_of_isAffineHom_restrict_of_isClosed` with an affine target, the
source of the immersion is affine. -/
@[stacks 0C3A "source is affine"]
theorem isAffine_of_isAffineHom_restrict_of_isClosed {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsImmersion j] [IsAffine X] (U : X.Opens) [IsAffineHom U.ι] [IsAffineHom (j ∣_ U)]
    (hZ : IsClosed (Set.range (j : Y → X) ∩ (U : Set X)ᶜ)) : IsAffine Y :=
  have := isAffineHom_of_isAffineHom_restrict_of_isClosed j U hZ
  isAffine_of_isAffineHom j

end AlgebraicGeometry
