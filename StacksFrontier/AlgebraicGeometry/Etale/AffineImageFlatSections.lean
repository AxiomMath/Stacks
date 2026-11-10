module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.RingTheory.RingHom.Flat
public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineCoverVanishing.PreimageUniformBound

/-!
# Sections of an étale morphism over affine opens, and affine images

An étale morphism of schemes is flat, so the ring map `Γ(Y, U) ⟶ Γ(X, V)` it induces between
sections over affine opens `V ≤ f⁻¹U` is a flat ring map.  Étale morphisms are also open, and
every point of the source has an affine open neighbourhood whose image is an affine open of the
target: shrink to an affine `V'` lying over an affine open `U` of `Y`, pick an affine open
`U' ⊆ f(V')`, and replace `V'` by `V' ∩ f⁻¹U'`, which is affine because it is `U' ×_U V'` and
whose image is exactly `U'`.

Together these say that the sections of the structure sheaf of an object of the small étale site
are flat over the sections of `𝒪_Y` on the image, on a family of opens which covers.

## Main results

* `AlgebraicGeometry.Etale.flat_appLE` and `AlgebraicGeometry.Etale.flat_appLE_top`: the sections
  map of an étale morphism between affine opens is a flat ring map.
* `AlgebraicGeometry.Etale.moduleFlat_of_algebraMap_eq`: the same, read as flatness of a module
  for any algebra structure realizing that ring map.
* `AlgebraicGeometry.Etale.faithfullyFlat_appLE_top`: if moreover the affine open of the target is
  contained in the image, that sections map is faithfully flat.
* `AlgebraicGeometry.Etale.exists_isAffineOpen_image_isAffineOpen`: every point of the source of
  an étale morphism lies in an affine open whose image is an affine open of the target.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Étale ring maps are flat.** For an étale morphism of schemes, the ring map on sections
between an affine open of the target and an affine open of the source lying over it is flat. -/
theorem flat_appLE [Etale f] {U : Y.Opens} (hU : IsAffineOpen U) {V : X.Opens}
    (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U) : (f.appLE U V e).hom.Flat :=
  Flat.flat_appLE f hU hV e

/-- For an étale morphism out of an affine scheme, the ring map from the sections over an affine
open of the target containing the image to the global sections of the source is flat. -/
theorem flat_appLE_top [Etale f] [IsAffine X] {U : Y.Opens} (hU : IsAffineOpen U)
    (e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ U) : (f.appLE U ⊤ e).hom.Flat :=
  flat_appLE f hU (isAffineOpen_top X) e

/-- The global sections of an affine open of the source of an étale morphism form a flat module
over the sections of the target on an affine open lying under it, for any algebra structure whose
structure map is the sections map of the morphism. -/
theorem moduleFlat_of_algebraMap_eq [Etale f] {U : Y.Opens} (hU : IsAffineOpen U) {V : X.Opens}
    (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U) [Algebra Γ(Y, U) Γ(X, V)]
    (h : algebraMap Γ(Y, U) Γ(X, V) = (f.appLE U V e).hom) : Module.Flat Γ(Y, U) Γ(X, V) := by
  rw [← RingHom.flat_algebraMap_iff, h]
  exact flat_appLE f hU hV e

/-- **Étale sections maps onto an affine open in the image are faithfully flat.** For an étale
morphism out of an affine scheme whose image contains an affine open `U` of the target, the ring
map from the sections over `U` to the global sections of the source is faithfully flat: it is flat
because `f` is étale, and `Spec` of it is surjective because every point of `U` is hit by `f`. -/
theorem faithfullyFlat_appLE_top [Etale f] [IsAffine X] {U : Y.Opens} (hU : IsAffineOpen U)
    (e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ U) (hsurj : (U : Set Y) ⊆ Set.range f.base) :
    (f.appLE U ⊤ e).hom.FaithfullyFlat := by
  have : IsAffine (⊤ : X.Opens).toScheme := isAffineOpen_top X
  have : IsAffine U.toScheme := hU
  have hs : Surjective (f.resLE U ⊤ e) := ⟨fun u ↦ by
    obtain ⟨x, hx⟩ := hsurj u.2
    exact ⟨⟨x, trivial⟩, Subtype.ext <| by rw [Scheme.Hom.coe_resLE_apply]; exact hx⟩⟩
  exact (RingHom.FaithfullyFlat.respectsIso.arrow_mk_iso_iff (arrowResLEAppIso f U ⊤ e)).mp
    ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine _).mp ⟨inferInstance, hs⟩)

/-- **Every point of the source of an étale morphism has an affine open neighbourhood with
affine image.** Étale morphisms are open, and the open `V' ∩ f⁻¹U'` cut out of an affine open
`V'` by an affine open `U' ⊆ f(V')` is affine with image exactly `U'`. -/
theorem exists_isAffineOpen_image_isAffineOpen [Etale f] (x : X) :
    ∃ (V : X.Opens) (U : Y.Opens), x ∈ V ∧ IsAffineOpen V ∧ IsAffineOpen U ∧
      f.base '' (V : Set X) = (U : Set Y) := by
  obtain ⟨U₀, hU₀, hxU₀, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := f.base x) (U := (⊤ : Y.Opens)) trivial
  obtain ⟨V', hV', hxV', hV'U₀⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := f ⁻¹ᵁ U₀) hxU₀
  have hWopen : IsOpen (f.base '' (V' : Set X)) := f.isOpenMap _ V'.2
  have hxW : f.base x ∈ (⟨f.base '' (V' : Set X), hWopen⟩ : Y.Opens) := ⟨x, hxV', rfl⟩
  obtain ⟨U', hU', hxU', hU'W⟩ := exists_isAffineOpen_mem_and_subset
    (X := Y) (x := f.base x) (U := (⟨f.base '' (V' : Set X), hWopen⟩ : Y.Opens)) hxW
  have hWU₀ : f.base '' (V' : Set X) ⊆ (U₀ : Set Y) := Set.image_subset_iff.mpr hV'U₀
  refine ⟨V' ⊓ f ⁻¹ᵁ U', U', ⟨hxV', hxU'⟩,
    isAffineOpen_inf_preimage_of_le_preimage f hV' hU₀ hU' hV'U₀ (hU'W.trans hWU₀), hU', ?_⟩
  change f.base '' ((V' : Set X) ∩ f.base ⁻¹' (U' : Set Y)) = (U' : Set Y)
  rw [Set.image_inter_preimage]
  exact Set.inter_eq_right.mpr hU'W

end AlgebraicGeometry.Etale

end
