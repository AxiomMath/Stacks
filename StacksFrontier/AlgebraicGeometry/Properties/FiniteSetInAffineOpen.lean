module

public import StacksFrontier.AlgebraicGeometry.QuasiAffineNonvanishing.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite sets of points inside an affine open

A finite set of points of a scheme `X` lies in a single affine open of `X` when `X` admits an
immersion into an affine scheme, and in particular when `X` is quasi-affine.

## Main results

* `AlgebraicGeometry.isAffineOpen_preimage_of_isImmersion`: for an immersion `i : X ⟶ Y`, the
  preimage of an affine open of `Y` that is contained in `i.coborderRange` is an affine open
  of `X`.
* `AlgebraicGeometry.exists_isAffineOpen_of_isImmersion_of_isAffine`: a scheme admitting an
  immersion into an affine scheme has every finite set of points inside an affine open.
* `AlgebraicGeometry.exists_isAffineOpen_of_isQuasiAffine`: a quasi-affine scheme has every
  finite set of points inside an affine open.

## References

* [Stacks Project, Tag 01ZY](https://stacks.math.columbia.edu/tag/01ZY)
* [Stacks Project, Tag 00DS](https://stacks.math.columbia.edu/tag/00DS)
* [Stacks Project, Tag 01P6](https://stacks.math.columbia.edu/tag/01P6)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Let `i : X ⟶ Y` be an immersion and let `W` be an affine open of `Y` contained in
`i.coborderRange`, the largest open of `Y` in which the image of `X` is closed. Then `i ⁻¹ᵁ W`
is an affine open of `X`. -/
@[ega "II 1.2.2" "more general"]
theorem isAffineOpen_preimage_of_isImmersion {X Y : Scheme.{u}} (i : X ⟶ Y) [IsImmersion i]
    {W : Y.Opens} (hW : IsAffineOpen W) (hWle : W ≤ i.coborderRange) :
    IsAffineOpen (i ⁻¹ᵁ W) := by
  have hW' : IsAffineOpen (i.coborderRange.ι ⁻¹ᵁ W) := by
    rwa [← i.coborderRange.ι.isAffineOpen_iff_of_isOpenImmersion,
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hWle]
  have h := IsAffineHom.isAffine_preimage (f := i.liftCoborder) _ hW'
  rwa [← Scheme.Hom.comp_preimage, i.liftCoborder_ι] at h

/-- A scheme `X` with an immersion `i : X ⟶ Y` into an affine scheme `Y` (that is, isomorphic to
a locally closed subscheme of an affine scheme) has every finite set of its points inside a
single affine open. -/
@[stacks 01ZY "case (2)"]
theorem exists_isAffineOpen_of_isImmersion_of_isAffine {X Y : Scheme.{u}} [IsAffine Y]
    (i : X ⟶ Y) [IsImmersion i] {E : Set X} (hE : E.Finite) :
    ∃ U : X.Opens, IsAffineOpen U ∧ E ⊆ (U : Set X) := by
  obtain ⟨r, hr₁, hr₂⟩ := Y.exists_basicOpen_subset_of_finite_of_isQuasiAffine
    (hE.image i.base) i.coborderRange
    (fun _ ⟨e, _, he⟩ => he ▸ subset_coborder (Set.mem_range_self e))
  exact ⟨i ⁻¹ᵁ Y.basicOpen r,
    isAffineOpen_preimage_of_isImmersion i ((isAffineOpen_top Y).basicOpen r) hr₂,
    fun e he => hr₁ ⟨e, he, rfl⟩⟩

/-- A quasi-affine scheme has every finite set of its points inside a single affine open. -/
@[stacks 01ZY "case (1)"]
theorem exists_isAffineOpen_of_isQuasiAffine (X : Scheme.{u}) [X.IsQuasiAffine] {E : Set X}
    (hE : E.Finite) : ∃ U : X.Opens, IsAffineOpen U ∧ E ⊆ (U : Set X) :=
  exists_isAffineOpen_of_isImmersion_of_isAffine X.toSpecΓ hE

end AlgebraicGeometry

end
