module

public import StacksFrontier.AlgebraicGeometry.RegularImmersion.OpenIndependence
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularIdealSheaf.RegularToQuasiRegular
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.RegularOpenIndependence

/-!
# Reading regularity of a closed immersion on the ambient scheme

`Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion` and
`Stacks.AlgebraicGeometry.RegularIdealSheaf.IsQuasiRegularImmersion` are conditions on the defining
ideal of the canonical closed factor `i.liftCoborder` of an immersion, which lives on the open
subscheme `i.coborderRange`. When the immersion is a closed immersion, these conditions follow from
the corresponding conditions on its defining ideal on the target.

## Main results

* `Stacks.AlgebraicGeometry.isRegularImmersion_of_isRegularIdealSheaf`: a closed immersion whose
  defining ideal on the target is a regular ideal sheaf is a regular immersion.
* `Stacks.AlgebraicGeometry.isQuasiRegularImmersion_of_isQuasiRegularIdealSheaf`: the same with
  quasi-regularity on both sides.

## References

* [Stacks Project, Lemma 31.20.3 (Tag 063G)](https://stacks.math.columbia.edu/tag/063G)
* [Stacks Project, Definition 31.21.1 (Tag 063J)](https://stacks.math.columbia.edu/tag/063J)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace Stacks.AlgebraicGeometry

universe u

/-- The factorization of a closed immersion through its coborder range is a closed immersion. -/
private theorem closedImmersion_liftCoborder_comp_ι {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] : IsClosedImmersion (i.liftCoborder ≫ i.coborderRange.ι) := by
  rw [i.liftCoborder_ι]; infer_instance

/-- A closed immersion whose defining ideal on the target is a regular ideal sheaf is a regular
immersion. -/
theorem isRegularImmersion_of_isRegularIdealSheaf {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i]
    (h : IsRegularIdealSheaf X.toRingedSpace (definingIdealOfHom i)) :
    IsRegularImmersion i := by
  rw [← i.liftCoborder_ι] at h
  have := closedImmersion_liftCoborder_comp_ι i
  exact (isRegularIdealSheaf_comp_open_iff i.liftCoborder i.coborderRange.ι).mp h

/-- A closed immersion whose defining ideal on the target is a quasi-regular ideal sheaf is a
quasi-regular immersion. -/
theorem isQuasiRegularImmersion_of_isQuasiRegularIdealSheaf {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i]
    (h : IsQuasiRegularIdealSheaf X.toRingedSpace (definingIdealOfHom i)) :
    IsQuasiRegularImmersion i := by
  rw [← i.liftCoborder_ι] at h
  have := closedImmersion_liftCoborder_comp_ι i
  refine (RegularIdealSheaf.isQuasiRegularIdealSheaf_iff_exists_affine_generators
    i.coborderRange.toScheme _).mpr fun x hx => ?_
  rw [definingIdealQuotient_support_eq_range] at hx
  obtain ⟨z, rfl⟩ := hx
  have hz : i.coborderRange.ι (i.liftCoborder z) ∈
      idealQuotientSupport X.toRingedSpace
        (definingIdealOfHom (i.liftCoborder ≫ i.coborderRange.ι)) := by
    rw [definingIdealQuotient_support_eq_range]
    exact ⟨z, rfl⟩
  obtain ⟨U, hxU, r, s, hgen, hs⟩ :=
    (RegularIdealSheaf.isQuasiRegularIdealSheaf_iff_exists_affine_generators X _).mp h _ hz
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (show i.liftCoborder z ∈ i.coborderRange.ι ⁻¹ᵁ U.1 from hxU)
  refine ⟨⟨V, hV⟩, hxV, r, fun k => i.coborderRange.ι.appLE U.1 V hVU (s k), ?_, ?_⟩
  · have hg := isGeneratedByOn_mono _ hVU _
      (isGeneratedByOn_restriction i.coborderRange.ι _ U.1 s hgen)
    rwa [definingIdealOfHom_comp_open] at hg
  · have hflat := Koszul.isQuasiRegular_map_of_flat
      (i.coborderRange.ι.appLE U.1 V hVU).hom
      (i.coborderRange.ι.flat_appLE U.2 hV hVU) hs
    simpa only [List.map_ofFn, Function.comp_def] using hflat

end Stacks.AlgebraicGeometry

end
