module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# The part of a scheme-theoretic image lying over an open of the target

The scheme-theoretic image of a quasi-compact morphism `h : Z ⟶ X` is the closed subscheme of
`X` cut out by `AlgebraicGeometry.Scheme.Hom.ker h`, and its underlying set is the closure of
the image of `h`. If the image of `h` is *closed in* an open `O ⊆ X` — the typical case being
`h = w ≫ O.ι` for a closed immersion `w` into `O` — then the part of the scheme-theoretic
image lying over `O` is exactly the image of `h`.

## Main results

* `AlgebraicGeometry.range_imageι_eq_closure_range`: the underlying set of the
  scheme-theoretic image of a quasi-compact morphism is the closure of its image.
* `AlgebraicGeometry.range_toImage_eq_preimage`: the part of the scheme-theoretic image over
  an open `O` in which the image of `h` is closed is exactly the image of `h`.
* `AlgebraicGeometry.range_toImage_comp_isOpenImmersion` and
  `AlgebraicGeometry.range_toImage_comp_opens_ι`: the special case of a closed immersion
  followed by an open immersion.

## References

* [Stacks Project, Tag 01R8](https://stacks.math.columbia.edu/tag/01R8)
* [Stacks Project, Tag 01RG](https://stacks.math.columbia.edu/tag/01RG)
* [Stacks Project, Tag 0DBF](https://stacks.math.columbia.edu/tag/0DBF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {Z X : Scheme.{u}} (h : Z ⟶ X)

/-- The inclusion of the scheme-theoretic image of a morphism is injective on points. -/
theorem imageι_injective : Function.Injective h.imageι :=
  fun _ _ hab => Subtype.ext hab

/-- The underlying set of the scheme-theoretic image of a quasi-compact morphism is the
closure of the image of that morphism. -/
theorem range_imageι_eq_closure_range [QuasiCompact h] :
    Set.range h.imageι = closure (Set.range h) := by
  rw [Scheme.Hom.imageι, Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker]

/-- A point of the scheme-theoretic image lies in the image of
`AlgebraicGeometry.Scheme.Hom.toImage` precisely when the point of the target below it lies in
the image of the morphism. -/
theorem mem_range_toImage_iff (x : h.image) :
    x ∈ Set.range h.toImage ↔ h.imageι x ∈ Set.range h := by
  refine ⟨?_, ?_⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, by rw [← Scheme.Hom.comp_apply, h.toImage_imageι]⟩
  · rintro ⟨z, hz⟩
    refine ⟨z, imageι_injective h ?_⟩
    rw [← Scheme.Hom.comp_apply, h.toImage_imageι, hz]

/-- The part of the scheme-theoretic image of a quasi-compact morphism lying over an open `O` of
the target in which the image is closed is exactly that image. The hypothesis is
`closure (Set.range h) ∩ O = Set.range h`, which for `Set.range h ⊆ O` says precisely that
`Set.range h` is closed in the subspace `O`. -/
theorem range_toImage_eq_preimage [QuasiCompact h] {O : Set X}
    (hO : closure (Set.range h) ∩ O = Set.range h) :
    Set.range h.toImage = h.imageι ⁻¹' O := by
  ext x
  rw [mem_range_toImage_iff, Set.mem_preimage, ← hO]
  refine ⟨fun hx => hx.2, fun hx => ⟨?_, hx⟩⟩
  rw [← range_imageι_eq_closure_range h]
  exact Set.mem_range_self x

/-- For a closed immersion `w` followed by an open immersion `j`, the part of the
scheme-theoretic image of `w ≫ j` lying over the image of `j` is exactly the image of `w ≫ j`. -/
theorem range_toImage_comp_isOpenImmersion {W Y : Scheme.{u}} (w : W ⟶ Y) (j : Y ⟶ X)
    [IsClosedImmersion w] [IsOpenImmersion j] [QuasiCompact (w ≫ j)] :
    Set.range (w ≫ j).toImage = (w ≫ j).imageι ⁻¹' Set.range j := by
  refine range_toImage_eq_preimage _ ?_
  have hrange : Set.range (w ≫ j) = j '' Set.range w := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  have hclosed : IsClosed (Set.range w) := w.isClosedEmbedding.isClosed_range
  refine Set.eq_of_subset_of_subset ?_
    (Set.subset_inter subset_closure (hrange ▸ Set.image_subset_range _ _))
  rintro x ⟨hxc, y, rfl⟩
  rw [hrange]
  refine ⟨y, ?_, rfl⟩
  have hy : y ∈ j ⁻¹' closure (Set.range (w ≫ j)) := hxc
  rwa [j.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage j.continuous,
    hrange, Set.preimage_image_eq _ j.isOpenEmbedding.injective, hclosed.closure_eq] at hy

/-- The case of `AlgebraicGeometry.range_toImage_comp_isOpenImmersion` in which the open
immersion is the inclusion of an open subscheme. -/
theorem range_toImage_comp_opens_ι {W : Scheme.{u}} (O : X.Opens) (w : W ⟶ O.toScheme)
    [IsClosedImmersion w] [QuasiCompact (w ≫ O.ι)] :
    Set.range (w ≫ O.ι).toImage = (w ≫ O.ι).imageι ⁻¹' (O : Set X) := by
  rw [range_toImage_comp_isOpenImmersion, Scheme.Opens.range_ι]

end AlgebraicGeometry

end
